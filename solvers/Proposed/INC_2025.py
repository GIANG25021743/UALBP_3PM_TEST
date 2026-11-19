"""
SAT-based solver for SALB3PM using Structure-based method (SAT-STR).

This solver implements the structure-based search strategy to find the optimal power peak value.
Unlike SAT-BS (binary search) and SAT-SU (SAT-UNSAT search), it uses a direct approach
by iteratively finding solutions and banning specific time slots.

Search Strategy: Structure-based (STR)
- Iteratively finds SAT solutions
- Bans specific time slots from the optimal solution to find better ones
- Uses clause learning to eliminate suboptimal solutions
- Does not require objective encoding variables (E variables)
- Simpler but may require more iterations than other methods

Constraints implemented (all from paper):
- Eq. (2): Each task assigned to exactly one in/out gate
- Eq. (3): Workload capacity constraint
- Eq. (4)-(6): Precedence and start time constraints for in/out gates
- Eq. (6): Impossible start times
- Eq. (7): Non-overlap constraint
- Eq. (9): In-gate tasks start before out-gate tasks on the same workstation
- Note: Does not use Eq. (8) objective encoding, directly evaluates power peak from solutions
"""

from pysat.formula import *
from pysat.pb import *
from pysat.solvers import *
import re
import time
import os
import csv
import argparse
import pysat.card as card
from math import ceil,floor

# Encoding types for cardinality and pseudo-Boolean constraints
card_encoding = card.EncType.cardnetwrk
PB_encoding = EncType.best

# Variable pool for managing Boolean variables
vpool = IDPool(start_from=1)

# Boolean variable definitions:
# X(j,k): task j assigned to the in gate of workstation k (Eq. 2)
# O(j,k): task j assigned to the out gate of workstation k (Eq. 2)
# S(j,t): task j starts at time t (Eq. 4)
# A(j,t): auxiliary variable indicating if time t is active for task j (used in Eq. 7)
X = lambda j, k: vpool.id('X{0}@{1}'.format(j, k))
O = lambda j, k: vpool.id('O{0}@{1}'.format(j, k))
R = lambda j, k: vpool.id('R{0}@{1}'.format(j, k))
S = lambda j, t: vpool.id('S{0}@{1}'.format(j, t))
Q = lambda j, t: vpool.id('T{0}@{1}'.format(j, t))
A = lambda j, t: vpool.id('A{0}@{1}'.format(j, t))

# Dictionary for tracking positive A[j,t] variables (long-task reduction)
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

def get_cnf_insatance(n, m, c, T, W, precedence_relations, vpool,
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
        cnf.append([-X(j, 1), R(j, 1)]) #cse 1-a
        cnf.append([X(j, 1), -R(j, 1)]) #cse 1-b
        for k in range(2, 2*m):
            cnf.append([-R(j, k - 1), R(j, k)]) #cse 2-a
            if k < m + 1:
                cnf.append([-X(j, k), R(j, k)]) #cse 3-a
                cnf.append([-X(j, k), -R(j, k - 1)]) #cse 4-a
                cnf.append([-R(j, k), R(j, k - 1), X(j, k)])  # cse 5-a
            if k >= m + 1:
                cnf.append([-O(j, 2 * m - k + 1), R(j, k)]) #cse 3-b
                cnf.append([-O(j, 2 * m - k + 1), -R(j, k - 1)]) #cse 4-b
                cnf.append([-R(j, k), R(j, k - 1), O(j, 2 * m - k + 1)])  # cse 5-b
            cnf.append([-O(j, 1), -R(j, 2 * m - 1)]) #cse 5-c
            cnf.append([O(j, 1), R(j, 2 * m - 1)]) #cse 5-d
            
        # Eq. (4)-(5): Each task has exactly one start time
        cnf.append([-Q(j, 0), S(j, 0)]) #cse 7-a
        cnf.append([Q(j, 0), -S(j, 0)]) #cse 7-b
        lastime = c - T[j]
        for t in range(1, lastime):
            cnf.append([Q(j, t), -Q(j, t - 1)]) #cse 8
            cnf.append([-S(j, t), Q(j, t)]) #cse 9
            cnf.append([-Q(j, t - 1), -S(j, t)]) #cse 10
            cnf.append([-Q(j, t), Q(j, t - 1), S(j, t)]) #cse 11

        cnf.append([-S(j, lastime), -Q(j, lastime - 1)]) #cse 11-a
        cnf.append([Q(j, lastime - 1), S(j, lastime)]) #cse 11-b
    
        for t in range(lastime + 1, c):
            cnf.append([-S(j, t)])
            
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
            for k in range(2, 2*m + 1):
                if k <= m:
                    cnf.append([-X(i, k), -R(j, k - 1)])  # cse 6-a
                if k >= m + 1:
                    cnf.append([-O(i, 2 * m - k + 1), -R(j, k - 1)])  # cse 6-b
                
            for k in range(1, m + 1):
                # Eq. (6): Temporal precedence when both tasks use
                # the same workstation, regardless of their gate.
                left = T[i] - 1
                right = c - T[j]
                cnf.append([-X(i, k), -X(j, k), -Q(j, left)])
                cnf.append([-O(i, k), -O(j, k), -Q(j, left)])
                cnf.append([-X(i, k), -O(j, k), -Q(j, left)])
                for t in range(left + 1, right):
                    t_i = t - T[i] + 1
                    cnf.append([-X(i, k), -X(j, k), -S(i, t_i), -Q(j, t)])
                    cnf.append([-O(i, k), -O(j, k), -S(i, t_i), -Q(j, t)])
                    cnf.append([-X(i, k), -O(j, k), -S(i, t_i), -Q(j, t)])
                
                for t in range(right, c):
                    cnf.append([-X(i, k), -X(j, k), -S(i, t - T[i] + 1)])
                    cnf.append([-O(i, k), -O(j, k), -S(i, t - T[i] + 1)])
                    cnf.append([-X(i, k), -O(j, k), -S(i, t - T[i] + 1)])

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

def write_csv_result(input_file, n, m, c, variables, clauses, best_value,
                     solve_time, status):
    """Update the single CSV row identified by the instance dimensions."""
    result_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "result")
    )
    os.makedirs(result_dir, exist_ok=True)

    result_file = os.path.join(result_dir, "2025_results.csv")
    fieldnames = [
        "Inputfile", "n", "m", "c", "variables", "clauses",
        "besvalue", "time", "status"
    ]
    records = {}

    if os.path.exists(result_file):
        with open(result_file, "r", newline="", encoding="utf-8") as file:
            for record in csv.DictReader(file):
                try:
                    key = (int(record["n"]), int(record["m"]), int(record["c"]))
                except (KeyError, TypeError, ValueError):
                    continue
                records[key] = {
                    field: record.get(field, "") for field in fieldnames
                }

    records[(n, m, c)] = {
        "Inputfile": os.path.basename(input_file),
        "n": n,
        "m": m,
        "c": c,
        "variables": variables,
        "clauses": clauses,
        "besvalue": best_value,
        "time": solve_time,
        "status": status,
    }

    with open(result_file, "w", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(records.values())

if __name__ == '__main__':
    """
    Main entry point for SAT-STR solver.
    
    Usage: python Cadical-STR.py <input_file>
    
    This solver uses structure-based search to find the optimal power peak value for SALB3PM.
    """
    parser = argparse.ArgumentParser(description="Solving SALB3PM with Cadical.")
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

    if args.precedence_constraint:
        print("c precedence constraints enabled!")

    if args.long_task_constraint:
        print("c long task constraints enabled!")
        cnf_longTask = get_longTask_constraints(n, m, c, T, W, precedence_relations)
        cnf.extend(cnf_longTask)

    cnf.extend(get_cnf_insatance(
        n, m, c, T, W, precedence_relations, vpool,
        precedence_constraint=args.precedence_constraint
    ))
    solve_start_time = time.time()
    print(f"$$$ Transformation time: {solve_start_time - start_time}")

    ff = 1
    MinW = float('inf')
    solver = Solver(name='Cadical195', bootstrap_with=cnf.clauses)

    print(f"@@@ nb_var {cnf.nv} nb_cons {len(cnf.clauses)}")
    U = lambda j: vpool.id('U{0}'.format(j))

    sol = 0
    # Structure-based search: iteratively find solutions and ban time slots
    while ff:
        sol += 1
        solver.solve()
        if not solver.get_status():
            status = "optimal" if MinW != float('inf') else "infeasible"
            write_csv_result(
                input_file=input_file,
                n=n,
                m=m,
                c=c,
                variables=cnf.nv,
                clauses=len(cnf.clauses),
                best_value=int(MinW) if MinW != float('inf') else "",
                solve_time=time.time() - solve_start_time,
                status=status,
            )
            break
        model = solver.get_model()
        s_model = get_specific_var_list(model, n, key_char='S')
        x_model = get_workstation_model(model, n, m)
        focus_on = get_maxW(n, T, W, s_model, x_model)
        if MinW > focus_on[0]:
            status = "initial" if MinW == float('inf') else "improved"
            MinW = focus_on[0]
            print(f"new W : {MinW} | {time.time() - solve_start_time:.4f}")
        on_time = focus_on[1]

        # Ban the time slots at which the max power peak occurs
        if sol < 1:
            for t in range(c):
                solver.add_clause([-A(task, t) for task in focus_on[2]])
            
        if sol == 1:
            for i in range(max(W), MinW):
                solver.add_clause([-U(i), U(i + 1)])

            for t in range(c):
                lits, weights = [], []
                for j in range(1, n + 1):
                    lits.append(A(j, t))    
                    weights.append(W[j])
                for j in range(max(W), MinW):
                    lits.append(U(j))
                    weights.append(1)
                pb_constraint = PBEnc.leq(
                        lits=lits, weights=weights, bound=MinW,
                        vpool=vpool, encoding=PB_encoding
                )
                for clause in pb_constraint.clauses:
                    solver.add_clause(clause)
            
        if sol >1:
            solver.add_clause([U(MinW - 1)])

        write_csv_result(
            input_file=input_file,
            n=n,
            m=m,
            c=c,
            variables=cnf.nv,
            clauses=len(cnf.clauses),
            best_value=int(MinW),
            solve_time=time.time() - solve_start_time,
            status=status,
        )
    end_time = time.time()
    print(f"### Benchmark {os.path.basename(input_file)} OPT {MinW} TotTime {end_time - start_time} RealTime {end_time - solve_start_time}")