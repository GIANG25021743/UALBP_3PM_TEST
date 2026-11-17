"""
SAT-based solver for SALB3PM using SAT-UNSAT search with Inaugural formulation (SAT-SU-I).
Uses Maplesat solver (corresponds to Cadical-SU-I.py with different SAT solver).

This solver implements the SAT-UNSAT search strategy to find the optimal power peak value.
It uses the inaugural objective formulation with unary encoding.

Search Strategy: SAT-UNSAT (SU)
- Iteratively finds SAT solutions and adds constraints to ban them
- Each iteration finds a solution with strictly lower power peak
- Continues until UNSAT, proving optimality
- More iterations than binary search but may find optimal value faster in practice

Objective Formulation: Inaugural (I)
- Uses unary encoding with E[1..ub] variables
- Minimizes the maximum power peak (Eq. 8)
- Simpler encoding but requires more variables than enhanced formulation

Constraints implemented (all from paper):
- Eq. (2): Each task assigned to exactly one workstation
- Eq. (3): Workload capacity constraint
- Eq. (4)-(5): Precedence and start time constraints
- Eq. (6): Impossible start times
- Eq. (7): Non-overlap constraint
- Eq. (8): Power peak constraint (objective with unary encoding)

Note: This file is identical to Cadical-SU-I.py except it uses the Maplesat solver
      instead of Cadical195 for solving SAT instances.
"""

from pysat.card import CardEnc
from pysat.formula import *
from pysat.pb import *
from pysat.solvers import *
import re
import time
import os
import argparse
from sat_csv import write_result
import pysat.card as card
from math import ceil,floor
from math import log2,ceil

# Encoding types for cardinality and pseudo-Boolean constraints
card_encoding = card.EncType.cardnetwrk
PB_encoding = EncType.best

# Variable pool for managing Boolean variables
vpool = IDPool(start_from=1)

# Boolean variable definitions:
# X(j,k): task j assigned to the in gate of workstation k (Eq. 2)
# O(j,k): task j assigned to the out gate of workstation k (Eq. 2)
# S(j,t): task j starts at time t (Eq. 4)
# A(j,t): auxiliary variable indicating if time t is active for task j (used in Eq. 7 and Eq. 8)
# E(j): unary encoding variable for objective (power peak) - inaugural formulation
X = lambda j, k: vpool.id('X{0}@{1}'.format(j, k))
O = lambda j, k: vpool.id('O{0}@{1}'.format(j, k))
S = lambda j, t: vpool.id('S{0}@{1}'.format(j, t))
A = lambda j, t: vpool.id('A{0}@{1}'.format(j, t))
E = lambda j: vpool.id('E{0}'.format(j))

pos_A = {}  # Track positive A[j,t] variables (active time slots)

def parse_3pm_file(input_file):
    """
    Parse the .3pm input file format.
    
    Format:
    - Line 1: n m c (number of tasks, workstations, cycle time)
    - Lines 2 to n+1: t_i w_i (processing time and power for each task)
    - Remaining lines: i,j (precedence relations, terminated by -1,-1)
    """
    with open(input_file, 'r') as file:
        lines = file.readlines()

    # Skip comments and parse the first meaningful line
    line_index = 0
    while lines[line_index].startswith('c'):
        line_index += 1

    n, m, c = map(int, lines[line_index].strip().split())
    T, W = [0], [0]
    precedence_relations = []

    # Parse task information
    for i in range(1, n + 1):
        t, w = map(int, lines[line_index + i].strip().split())
        T.append(t)
        W.append(w)

    # Parse precedence relations
    for line in lines[line_index + n + 1:]:
        i, j = map(int, line.strip().split(','))
        if i == -1 and j == -1:
            break
        precedence_relations.append((i, j))

    return n, m, c, T, W, precedence_relations

def parse_str(S_str, key_char='S'):
    """Parse variable name to extract task index and time/workstation index."""
    j, t = S_str.lstrip(key_char).split('@', 1)
    return int(j), int(t)

def get_cnf_insatance(n, m, c, T, W, precedence_relations, vpool, ub,
                      precedence_constraint=True):
    """
    Generate CNF instance for SAT-STR (Structure-based method).
    
    This function encodes all constraints from the paper into SAT clauses.
    Unlike SAT-BS and SAT-SU, it does not include objective encoding (no E variables).
    The power peak is computed directly from the solution.
    
    Constraints:
    - Eq. (2): Task assignment to exactly one in/out gate
    - Eq. (3): Workload capacity constraint
    - Eq. (4)-(6): Precedence and start time constraints
    - Eq. (6): Invalid start times
    - Eq. (7): Non-overlap constraint
    - Eq. (9): In-gate/out-gate ordering constraint
    - Note: Eq. (8) is handled by evaluating power peak from solutions
    
    Args:
        n: number of tasks
        m: number of workstations
        c: cycle time
        T: processing times
        W: power consumption values
        precedence_relations: list of (i,j) precedence pairs
        vpool: variable pool
    
    Returns:
        cnf: CNF formula with all constraints
    """
    cnf = CNF()

    '''Eq. (3): Tasks assigned to the same workstation have the sum of their processing times bounded by c'''
    for k in range(1, m + 1):
        lits = []
        weight = []
        for j in range(1, n + 1):
            lits.extend([X(j, k), O(j, k)])
            weight.extend([T[j], T[j]])
        cnf.extend(
            PBEnc.leq(
                lits=lits,
                weights=weight, bound=c, vpool=vpool, encoding=PB_encoding
            )
        )
    '''Tasks assigned  to the same workstation have the sum of their processing times bounded by c'''

    for j in range(1, n + 1):
        # Eq. (2): Each task is assigned to exactly one in/out gate
        cnf.extend(
            card.CardEnc.equals(lits=[gate_var for k in range(1, m + 1)
                                      for gate_var in (X(j, k), O(j, k))],
                                bound=1, encoding=card_encoding,
                                vpool=vpool))  # (1)(2)
        # Eq. (4)-(5): Each task has exactly one start time
        cnf.extend(card.CardEnc.equals(lits=[S(j, t) for t in range(0, c - T[j] + 1)], bound=1,
                                        encoding=card_encoding, vpool=vpool))  # (4)(5)
        for k in range(1, m + 1):
            # Eq. (7): Non-overlap constraint for tasks on same workstation
            for i in range(1, j):
                for i_gate in (X(i, k), O(i, k)):
                    for j_gate in (X(j, k), O(j, k)):
                        cnf.extend([[-i_gate, -j_gate, -A(i, t), -A(j, t)]
                                    for t in range(0, c)])  # (7)

        # Eq. (5): Start time constraints - link S[j,t] with A[j,t']
        for t in range(0, c - T[j] + 1):
            for t_prime in range(c):
                if t_prime >= t and t_prime - t < T[j]:
                    if A(j, t_prime) not in pos_A:
                        cnf.append([-S(j, t), A(j, t_prime)])
                else:
                    cnf.append([-S(j, t), -A(j, t_prime)])

        # Eq. (6): Impossible start times
        cnf.extend([[-S(j, t)] for t in range(c - T[j] + 1, c)])  # (6)

    if precedence_constraint:
        # Eq. (4): A successor at an in gate must have its predecessor
        # at an in gate on the same or an earlier workstation.
        # A successor at an out gate has the reversed workstation order:
        # its predecessor may be at an out gate on a later workstation,
        # or at any in gate.
        for i, j in precedence_relations:
            for k in range(1, m + 1):
                cnf.append(
                    [-X(j, k)] + [X(i, h) for h in range(1, k + 1)]
                )
                cnf.append(
                    [-O(j, k)]
                    + [O(i, h) for h in range(k + 1, m + 1)]
                    + [X(i, h) for h in range(1, m + 1)]
                )

                # Eq. (6): Temporal precedence when both tasks use
                # the same workstation, regardless of their gate.
                for t in range(0, c - T[j] + 1):
                    start_before_j = [
                        S(i, tau) for tau in range(0, t - T[i] + 1)
                    ]
                    for i_gate in (X(i, k), O(i, k)):
                        for j_gate in (X(j, k), O(j, k)):
                            cnf.append(
                                [-S(j, t), -i_gate, -j_gate]
                                + start_before_j
                            )

        # Eq. (9): A task at an in gate must start before a task at
        # the out gate of the same workstation.
        for k in range(1, m + 1):
            for i in range(1, n + 1):
                for j in range(1, n + 1):
                    if i == j:
                        continue
                    for t in range(c):
                        starts_before_j = [
                            S(i, gamma)
                            for gamma in range(max(0, t - T[i] + 1))
                        ]
                        cnf.append(
                            [-S(j, t), -X(i, k), -O(j, k)]
                            + starts_before_j
                        )

    # Inaugural objective: unary encoding with E[1..ub] variables
    # Monotonicity: E[i] → E[i-1]
    for i in range(2, ub + 1):
        cnf.append([-E(i), E(i - 1)])

    # Eq. (8): Power peak constraint with unary encoding
    # At any time t, sum of power ≤ value represented by E variables
    for t in range(c):
        lits = [A(j, t) for j in range(1, 1 + n)] + [-E(x) for x in range(1, ub + 1)]
        weights = [W[j] for j in range(1, 1 + n)] + [1] * ub
        cnf.extend(PBEnc.leq(lits=lits, weights=weights, bound=ub, vpool=vpool, encoding=PB_encoding))

    return cnf
def trans(x:int):
    """Convert variable ID to variable name string."""
    if x>0:
        return vpool.obj(x)
    else:
        return f"-{vpool.obj(-x)}"

def custom_sort(record):
    """Custom sorting for variable names with natural number ordering."""
    name = record
    parts = re.split(r'([0-9]*\.[0-9]+|[0-9]+)', name)
    converted_parts = []
    for part in parts:
        if part.isdigit():
            converted_parts.append(int(part))
        elif re.match(r'[0-9]*\.[0-9]+', part):
            converted_parts.append(float(part))
        elif part:
            converted_parts.append(part)
    if type(converted_parts[0]) == int:
        return tuple([str(converted_parts[0])]+converted_parts[1:])
    return tuple(converted_parts)

def get_var_list(model, n, key_char='S'):
    """Extract variables of a specific type from the model."""
    S_list = []
    for m in model:
        if m is None:
            continue
        if m.find(key_char)!=-1 and m.find("-")==-1:
            S_list.append(m)
    return S_list

def get_specific_var_list(model, n, key_char):
    """Extract and sort variables to create a task-indexed list."""
    S_list = get_var_list(list(map(trans, model)), n, key_char)
    S_list.sort(key=custom_sort)
    S_model = [-1]
    for id, s in enumerate(S_list):
        j, t = parse_str(s, key_char)
        assert(j == id+1)
        S_model.append(t)
    return S_model

def get_workstation_model(model, n, m):
    """Extract each task's workstation from its positive X or O variable."""
    model_set = set(model)
    workstation_model = [-1]
    for j in range(1, n + 1):
        workstation = None
        for k in range(1, m + 1):
            if X(j, k) in model_set or O(j, k) in model_set:
                workstation = k
                break
        if workstation is None:
            raise ValueError(f"No workstation assignment found for task {j}")
        workstation_model.append(workstation)
    return workstation_model

def get_maxW(n, T, W, s_model, x_model):
    """
    Calculate the maximum power peak from a SAT model.
    
    Args:
        n: number of tasks
        T: processing times
        W: power consumption values
        s_model: list of start times for each task
        x_model: list of workstation assignments for each task
    
    Returns:
        tuple: (max_power_peak, time_of_max_peak, list_of_tasks_at_that_time)
    """
    maxW = 0
    ret = None
    book_m = [[0] * c for _ in range(m + 1)]
    for i in range(1, n + 1):
        for j in range(s_model[i], s_model[i] + T[i]):
            assert book_m[x_model[i]][j] == 0
            book_m[x_model[i]][j] = i
    for t in range(0, c):
        task_list = []
        w = 0
        for s in range(1, m + 1):
            task = book_m[s][t]
            if task==0:
                continue
            task_list.append(task)
            w += W[task]
        if w > maxW:
            maxW = w
            ret = (maxW, t, task_list)

    return ret

def get_longTask_constraints(n, m, c, T, W, precedence_relations):
    """
    Generate reduction constraints for long tasks.
    
    For long tasks, certain time slots are always active, reducing the number of A[j,t] variables.
    This is part of the reduction rules to minimize variable count.
    """
    LongTask_cnf = CNF()
    for i in range(1, n + 1):
        # Determine the range of time slots that are always active for task i
        l = c - T[i]
        r = T[i] - 1
        if l > r:
            continue

        # For tasks that span more than half the cycle time, mark active slots
        for t in range(l, r + 1):
            pos_A[A(i, t)] = 1
            LongTask_cnf.append([A(i, t)])

    return LongTask_cnf

if __name__ == '__main__':
    """
    Main entry point for SAT-SU-I solver using Maplesat.
    
    Usage: python Maplesat-SU-I.py <input_file>
    
    This solver uses SAT-UNSAT search with the inaugural objective formulation
    to find the optimal power peak value for SALB3PM.
    Uses Maplesat solver instead of Cadical195.
    """
    parser = argparse.ArgumentParser(description="Solving SALB3PM with Maplesat.")
    parser.add_argument("input_file", type=str, help="Path to the .3pm document")
    parser.add_argument('--precedence_constraint', action='store_true', default=True,
                        help='Enable the precedence constraints')
    parser.add_argument('--no-precedence_constraint', action='store_false', dest='precedence_constraint',
                        help='Disable the precedence constraints')
    parser.add_argument('--long_task_constraint', action='store_true', default=True,
                        help='Enable the long-task constraints')
    parser.add_argument('--no-long_task_constraint', action='store_false', dest='long_task_constraint',
                        help='Disable the long-task constraints')
    args = parser.parse_args()

    input_file = args.input_file
    start_time = time.time()
    n, m, c, T, W, precedence_relations = parse_3pm_file(input_file)
    cnf = CNF()

    if args.long_task_constraint:
        print("c long task constraints enabled!")
        cnf_longTask = get_longTask_constraints(n, m, c, T, W, precedence_relations)
        cnf.extend(cnf_longTask)

    if args.precedence_constraint:
        print("c precedence constraints enabled!")

    # Compute bounds
    lb = min(W[1:])
    ub = sum(sorted(W[1:], reverse=True)[:min(m, len(W) - 1)])
    cnf.extend(get_cnf_insatance(
        n, m, c, T, W, precedence_relations, vpool, ub,
        precedence_constraint=args.precedence_constraint
    ))

    solve_start_time = time.time()
    print(f"$$$ Transformation time: {solve_start_time - start_time}")

    ff = 1
    MinW = float('inf')
    ub_cnf = CNF()
    print(f"@@@ nb_var {cnf.nv} nb_cons {len(cnf.clauses)}")

    E_lits = [E(x) for x in range(1, ub + 1)]

    # SAT-UNSAT search: iteratively find solutions and ban them
    while ff:
        solver = Solver(name='Maplesat', bootstrap_with=cnf.clauses+ub_cnf.clauses)
        solver.solve()
        if not solver.get_status():
            # UNSAT: found optimal solution
            break
        model = solver.get_model()
        s_model = get_specific_var_list(model, n, key_char='S')
        x_model = get_workstation_model(model, n, m)
        focus_on = get_maxW(n, T, W, s_model, x_model)
        MinW = focus_on[0]
        print(f"new W : {MinW} | {time.time() - solve_start_time:.4f}")
        write_result(input_file, "Maplesat-SU-I", n, m, c, cnf.nv,
                     len(cnf.clauses), MinW,
                     time.time() - solve_start_time,
                     "initial" if ub_cnf.nv == 0 else "improved")
        # Add constraint to ban this solution: sum of E[x] ≤ MinW-1 (unary encoding)
        ub_cnf = card.CardEnc.atmost(lits=E_lits, bound=MinW-1, vpool=vpool, encoding=card.EncType.cardnetwrk)

    end_time = time.time()
    write_result(input_file, "Maplesat-SU-I", n, m, c, cnf.nv,
                 len(cnf.clauses), MinW if MinW != float('inf') else "",
                 end_time - solve_start_time,
                 "optimal" if MinW != float('inf') else "infeasible")
    print(f"### Benchmark {os.path.basename(input_file)} OPT {MinW} TotTime {end_time - start_time} RealTime {end_time - solve_start_time}")