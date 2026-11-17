import time
import sys
import os
import csv
from ortools.sat.python import cp_model
import argparse
from google.protobuf import text_format
import numpy as np
from math import ceil,floor,log2

# Time limit for solving (7200 seconds as per experimental setup)
CUTOFF = 7200

def status_to_string(status):
    """Convert CP-SAT solver status to human-readable string."""
    if status == cp_model.OPTIMAL:
        return "OPTIMAL"
    elif status == cp_model.FEASIBLE:
        return "FEASIBLE"
    elif status == cp_model.INFEASIBLE:
        return "INFEASIBLE"
    elif status == cp_model.MODEL_INVALID:
        return "MODEL_INVALID"
    elif status == cp_model.UNKNOWN:
        return "UNKNOWN"
    else:
        return "UNDEFINED"

# Global variables for constraint reduction
X = {}  # X[j,k]: task j assigned to in gate ofworkstation k (Eq. 2)
O = {}  # O[j,k]: task j assigned to out gate of workstation k (Eq. 2)
S = {}  # S[j,t]: task j starts at time t (Eq. 4)
neg_X = {}  # Dictionary to track negated X variables for reduction rules
neg_XS_pair = {}  # Dictionary to track negated X-S pairs for reduction rules
W_max = None  # Maximum power peak (objective variable)

def get_initial_model(n, m, c, W):
    """
    Initialize the CP-SAT model with variables.
    
    Parameters:
    - n: number of tasks
    - m: number of workstations
    - c: cycle time
    - W: list of power consumption for each task
    
    Returns:
    - model: initialized CP-SAT model
    
    Variables:
    - X[j,k]: Boolean, task j assigned to workstation k
    - S[j,t]: Boolean, task j starts at time t (0 ≤ t < c)
    - W_max: Integer, maximum power peak (objective, Eq. 8)
    """
    global W_max
    model = cp_model.CpModel()
    for j in range(1, n + 1):
        for k in range(1, m + 1):
            X[j, k] = model.NewBoolVar(f'X{j}@{k}')
            O[j, k] = model.NewBoolVar(f'O{j}@{k}')
    for j in range(1, n + 1):
        for t in range(c):
            S[j, t] = model.NewBoolVar(f'S{j}@{t}')
    W_max = model.NewIntVar(0, sum(W), "W_max")
    model.Minimize(W_max)
    return model

def get_CP_SAT_model(model, n, m, c, T, W, precedence_relations):
    """
    Add all SALB3PM constraints to the CP-SAT model.
    
    Constraints implemented:
    - Eq. (2): Each task assigned to exactly one workstation
    - Eq. (3): Workload capacity constraint
    - Eq. (4): Precedence constraint (workstation ordering)
    - Eq. (5): Each task has exactly one start time
    - Eq. (6): Precedence constraint (temporal ordering)
    - Eq. (7): Non-overlap constraint for tasks on same workstation
    - Eq. (8): Power peak constraint (objective)
    """
    # Constraint (2): Each task assigned to exactly one workstation
    for j in range(1, n + 1):
        model.Add(sum(X[j, k] for k in range(1, m + 1)) + sum(O[j, k] for k in range(1, m + 1)) == 1)

    # Constraint (3): Workload capacity - sum of processing times on each workstation ≤ c
    for k in range(1, m + 1):
        model.Add(sum(X[j, k] * T[j] for j in range(1, n + 1)) + sum(O[j, k] * T[j] for j in range(1, n + 1)) <= c)

    # Constraint (4): Precedence constraint - if task j on workstation k, 
    # then task i must be on workstation ≤ k
    for i, j in precedence_relations:
        for k in range(1, m + 1):
            model.Add(X[j, k] <= sum(X[i, h] for h in range(1, k + 1)))
            model.Add(O[j, k] <= sum(O[i, h] for h in range(k + 1, m + 1)) + sum(X[i, h] for h in range(1, m + 1)))

    # Constraint (5): Each task has exactly one start time
    for j in range(1, n + 1):
        model.Add(sum(S[j, t] for t in range(c - T[j] + 1)) == 1)

    # Constraint (6): Precedence constraint (temporal) - if i→j, then start time of j 
    # must be after start time of i + T[i], considering workstation assignments
    for i, j in precedence_relations:
        for k in range(1, m + 1):
            for t in range(c - T[j] + 1):
                gamma_max = max(0, t - T[i] + 1)
                model.Add(S[j, t] <= sum(S[i, gamma] for gamma in range(gamma_max)) + 2
                          - X[i, k] - O[i, k]
                          - X[j, k] - O[j, k])

    # Constraint (7): Non-overlap constraint - tasks on same workstation cannot overlap
    for i in range(1, n + 1):
        for j in range(1, i):
            for k in range(1, m + 1):
                for t in range(c):
                    gama_start_i = max(0, t - T[i] + 1)
                    gama_start_j = max(0, t - T[j] + 1)
                    model.Add((X[i, k] + O[i, k]) + (X[j, k] + O[j, k])
                              + sum(S[i, gama] for gama in range(gama_start_i, t + 1)) +
                              sum(S[j, gama] for gama in range(gama_start_j, t + 1)) <= 3)

    # Constraint (8): Power peak constraint - at any time t, sum of power ≤ W_max
    for t in range(c):
        expr = sum(W[j] * S[j, gama] for j in range(1, n + 1) for gama in range(max(0, t - T[j] + 1), t + 1))
        model.Add(expr <= W_max)

    # Constraint (9): Task i at in gate start before task j at out gate of same workstation k
    for k in range(1, m + 1):
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i != j:
                    for t in range(c):
                        gama_start_i = max(0, t - T[i] + 1)
                        model.Add(S[j, t] <= sum(S[i, gama] for gama in range(gama_start_i)) + 2
                                  - X[i, k] - O[j, k])
    return model

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

def get_single_machine_time(ealiest_st_time, T):
    """
    Calculate the makespan for tasks on a single machine (no parallel workstations).
    Used for computing lower bounds on task completion times.
    """
    C_max = 0
    st_T_pair = sorted(list(zip(ealiest_st_time, T)))
    for r, t in st_T_pair:
        C_max = max(C_max, r) + t
    return C_max

def write_csv_result(input_file, n, m, c, model, solver, status):
    result_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "result")
    )
    os.makedirs(result_dir, exist_ok=True)

    result_file = os.path.join(result_dir, "cpsat_results.csv")
    file_exists = os.path.exists(result_file)
    status_text = status_to_string(status)

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        best_value = int(solver.ObjectiveValue())
    else:
        best_value = ""

    row = {
        "Inputfile": os.path.basename(input_file),
        "n": n,
        "m": m,
        "c": c,
        "variables": len(model.Proto().variables),
        "clauses": len(model.Proto().constraints),
        "besvalue": best_value,
        "time": solver.WallTime(),
        "status": status_text,
    }

    with open(result_file, "a", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=row.keys())
        if not file_exists:
            writer.writeheader()
        writer.writerow(row)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="python this.py <path/to/3pm>")
    parser.add_argument("input_path", help="path/to/3pm")
    args = parser.parse_args()
    input_file = args.input_path

    start_time = time.time()

    # Parse input file to get problem parameters
    n, m, c, T, W, precedence_relations = parse_3pm_file(input_file)

    # Build the CP-SAT model
    model = get_initial_model(n, m, c, W)
    get_CP_SAT_model(model, n, m, c, T, W, precedence_relations)
    trans_end_time = time.time()
    print(f"$$$ Done modeling at {trans_end_time-start_time} seconds")
    
    # Create solver and solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = CUTOFF
    solver.parameters.num_search_workers = 1
    status = solver.Solve(model)
    end_time = time.time()
    write_csv_result(
        input_file=input_file,
        n=n,
        m=m,
        c=c,
        model=model,
        solver=solver,
        status=status,
    )

    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        print("Solution is feasible.")
        print("\n---------------------")
        print(f"@@@ {status_to_string(status)}")
        print(f">>> Benchmark {os.path.basename(args.input_path)} OPT {int(solver.ObjectiveValue())}"
              f" TimeTot {end_time - start_time} TimeReal {end_time - trans_end_time} TimeTrans {trans_end_time - start_time}"
              f" Status {status_to_string(status)}")
    else:
        print(f">>> Benchmark {os.path.basename(args.input_path)} OPT {int(solver.ObjectiveValue())}"
              f" TimeTot {end_time - start_time} TimeReal {end_time - trans_end_time} TimeTrans {trans_end_time - start_time}"
              f" Status {status_to_string(status)}")