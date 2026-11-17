import argparse
import csv
import os
import time

import cplex
from cplex import SparsePair


TIME_LIMIT = 7200


def write_csv_result(input_path, solver_name, n, m, c, model, status, objective, elapsed):
    result_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "result"))
    os.makedirs(result_dir, exist_ok=True)
    result_path = os.path.join(result_dir, "ilp_results.csv")
    row = {
        "Inputfile": os.path.basename(input_path),
        "solver": solver_name,
        "n": n,
        "m": m,
        "c": c,
        "variables": model.variables.get_num(),
        "constraints": model.linear_constraints.get_num(),
        "bestvalue": objective,
        "time": elapsed,
        "status": status,
    }
    file_exists = os.path.exists(result_path) and os.path.getsize(result_path) > 0
    with open(result_path, "a", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=row.keys())
        if not file_exists:
            writer.writeheader()
        writer.writerow(row)


def parse_3pm_file(input_file):
    with open(input_file, "r", encoding="utf-8") as file:
        lines = [line.strip() for line in file if line.strip()]

    line_index = 0
    while lines[line_index].startswith("c"):
        line_index += 1

    n, m, c = map(int, lines[line_index].split())
    task_time = [0]
    power = [0]
    for offset in range(1, n + 1):
        processing_time, task_power = map(int, lines[line_index + offset].split())
        task_time.append(processing_time)
        power.append(task_power)

    precedence = []
    for line in lines[line_index + n + 1:]:
        i, j = map(int, line.split(","))
        if (i, j) == (-1, -1):
            break
        precedence.append((i, j))
    return n, m, c, task_time, power, precedence


def add_constraint(model, coefficients, sense, rhs, name):
    variables, values = zip(*((variable, coefficient)
                              for variable, coefficient in coefficients.items()
                              if coefficient))
    model.linear_constraints.add(
        lin_expr=[SparsePair(list(variables), list(values))],
        senses=[sense],
        rhs=[rhs],
        names=[name],
    )


def build_model(n, m, c, task_time, power, precedence):
    model = cplex.Cplex()
    model.objective.set_sense(model.objective.sense.minimize)

    x = {(j, k): f"X{j}@{k}" for j in range(1, n + 1) for k in range(1, m + 1)}
    out = {(j, k): f"O{j}@{k}" for j in range(1, n + 1) for k in range(1, m + 1)}
    start = {(j, t): f"S{j}@{t}" for j in range(1, n + 1) for t in range(c)}
    w_max = "W_max"
    binary_names = list(x.values()) + list(out.values()) + list(start.values())
    model.variables.add(names=binary_names, types=[model.variables.type.binary] * len(binary_names))
    model.variables.add(
        names=[w_max],
        lb=[0],
        ub=[sum(power)],
        obj=[1],
        types=[model.variables.type.integer],
    )

    for j in range(1, n + 1):
        coefficients = {}
        for k in range(1, m + 1):
            coefficients[x[j, k]] = 1
            coefficients[out[j, k]] = 1
        add_constraint(model, coefficients, "E", 1, f"assignment_{j}")

    for k in range(1, m + 1):
        coefficients = {}
        for j in range(1, n + 1):
            coefficients[x[j, k]] = task_time[j]
            coefficients[out[j, k]] = task_time[j]
        add_constraint(model, coefficients, "L", c, f"capacity_{k}")

    for j in range(1, n + 1):
        add_constraint(
            model,
            {start[j, t]: 1 for t in range(c - task_time[j] + 1)},
            "E",
            1,
            f"start_{j}",
        )

    for i, j in precedence:
        for k in range(1, m + 1):
            coefficients = {x[j, k]: 1}
            for h in range(1, k + 1):
                coefficients[x[i, h]] = coefficients.get(x[i, h], 0) - 1
            add_constraint(model, coefficients, "L", 0, f"precedence_in_{i}_{j}_{k}")

            coefficients = {out[j, k]: 1}
            for h in range(k + 1, m + 1):
                coefficients[out[i, h]] = coefficients.get(out[i, h], 0) - 1
            for h in range(1, m + 1):
                coefficients[x[i, h]] = coefficients.get(x[i, h], 0) - 1
            add_constraint(model, coefficients, "L", 0, f"precedence_out_{i}_{j}_{k}")

            for t in range(c - task_time[j] + 1):
                coefficients = {start[j, t]: 1}
                for gamma in range(max(0, t - task_time[i] + 1)):
                    coefficients[start[i, gamma]] = coefficients.get(start[i, gamma], 0) - 1
                for variable in (x[i, k], out[i, k], x[j, k], out[j, k]):
                    coefficients[variable] = coefficients.get(variable, 0) + 1
                add_constraint(
                    model, coefficients, "L", 2,
                    f"temporal_{i}_{j}_{k}_{t}",
                )

    for i in range(1, n + 1):
        for j in range(1, i):
            for k in range(1, m + 1):
                for t in range(c):
                    coefficients = {
                        x[i, k]: 1, out[i, k]: 1,
                        x[j, k]: 1, out[j, k]: 1,
                    }
                    for gamma in range(max(0, t - task_time[i] + 1), t + 1):
                        coefficients[start[i, gamma]] = coefficients.get(start[i, gamma], 0) + 1
                    for gamma in range(max(0, t - task_time[j] + 1), t + 1):
                        coefficients[start[j, gamma]] = coefficients.get(start[j, gamma], 0) + 1
                    add_constraint(model, coefficients, "L", 3, f"overlap_{i}_{j}_{k}_{t}")

    for t in range(c):
        coefficients = {w_max: -1}
        for j in range(1, n + 1):
            for gamma in range(max(0, t - task_time[j] + 1), t + 1):
                coefficients[start[j, gamma]] = power[j]
        add_constraint(model, coefficients, "L", 0, f"power_{t}")

    for k in range(1, m + 1):
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for t in range(c):
                    coefficients = {start[j, t]: 1, x[i, k]: 1, out[j, k]: 1}
                    for gamma in range(max(0, t - task_time[i] + 1)):
                        coefficients[start[i, gamma]] = coefficients.get(start[i, gamma], 0) - 1
                    add_constraint(model, coefficients, "L", 2, f"gate_order_{i}_{j}_{k}_{t}")
    return model


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve UALBP from a .3pm instance with CPLEX")
    parser.add_argument("input_path", help="path to .3pm")
    args = parser.parse_args()

    start_time = time.time()
    n, m, c, task_time, power, precedence = parse_3pm_file(args.input_path)
    model = build_model(n, m, c, task_time, power, precedence)
    model.parameters.threads.set(1)
    model.parameters.clocktype.set(1)
    model.parameters.timelimit.set(TIME_LIMIT)
    model.set_log_stream(None)
    model.set_error_stream(None)
    model.set_warning_stream(None)
    model.solve()
    end_time = time.time()

    status = model.solution.status[model.solution.get_status()]
    if model.solution.is_primal_feasible():
        objective = int(model.solution.get_objective_value())
        print("Solution is feasible.")
        print("\n---------------------")
        print(f"@@@ {status}")
        print(f">>> Benchmark {os.path.basename(args.input_path)} OPT {objective}"
              f" TimeTot {end_time - start_time}")
    else:
        objective = ""
        print("Solution is infeasible.")
    write_csv_result(
        args.input_path, "CPLEX", n, m, c, model, status, objective,
        end_time - start_time
    )
