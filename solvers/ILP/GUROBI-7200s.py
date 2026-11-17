import argparse
import csv
import os
import time

import gurobipy as gp
from gurobipy import GRB


TIME_LIMIT = 7200


def write_csv_result(input_path, n, m, c, model, status, objective, elapsed):
    result_dir = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "result"))
    os.makedirs(result_dir, exist_ok=True)
    result_path = os.path.join(result_dir, "ilp_results.csv")
    row = {
        "Inputfile": os.path.basename(input_path),
        "solver": "GUROBI",
        "n": n,
        "m": m,
        "c": c,
        "variables": model.NumVars,
        "constraints": model.NumConstrs,
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


def load_env_file():
    """Load local license settings without overwriting existing environment values."""
    env_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env")
    if not os.path.isfile(env_path):
        return
    with open(env_path, "r", encoding="utf-8") as file:
        for line in file:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, value = line.split("=", 1)
            key = key.strip()
            value = value.strip().strip("\"'")
            if key:
                os.environ.setdefault(key, value)


def create_wls_environment():
    """Create a Gurobi environment using the WLS credentials from the environment."""
    load_env_file()
    required = ("WLSACCESSID", "WLSSECRET", "LICENSEID")
    missing = [name for name in required if not os.environ.get(name)]
    if missing:
        raise RuntimeError(
            "Missing Gurobi WLS setting(s): {}. Set them in the environment "
            "or solvers/ILP/.env.".format(", ".join(missing))
        )

    try:
        env = gp.Env(empty=True)
        env.setParam("WLSAccessID", os.environ["WLSACCESSID"])
        env.setParam("WLSSecret", os.environ["WLSSECRET"])
        env.setParam("LicenseID", int(os.environ["LICENSEID"]))
        env.start()
        return env
    except (ValueError, gp.GurobiError) as error:
        raise RuntimeError(
            "Could not initialize the Gurobi WLS license. "
            "Check WLSACCESSID, WLSSECRET, LICENSEID and network access."
        ) from error


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


def build_model(n, m, c, task_time, power, precedence, env):
    model = gp.Model("UALBP", env=env)
    x = {(j, k): model.addVar(vtype=GRB.BINARY, name=f"X{j}@{k}")
         for j in range(1, n + 1) for k in range(1, m + 1)}
    out = {(j, k): model.addVar(vtype=GRB.BINARY, name=f"O{j}@{k}")
           for j in range(1, n + 1) for k in range(1, m + 1)}
    start = {(j, t): model.addVar(vtype=GRB.BINARY, name=f"S{j}@{t}")
             for j in range(1, n + 1) for t in range(c)}
    w_max = model.addVar(lb=0, ub=sum(power), vtype=GRB.INTEGER, name="W_max")
    model.setObjective(w_max, GRB.MINIMIZE)

    for j in range(1, n + 1):
        model.addConstr(
            gp.quicksum(x[j, k] + out[j, k] for k in range(1, m + 1)) == 1,
            name=f"assignment_{j}",
        )

    for k in range(1, m + 1):
        model.addConstr(
            gp.quicksum(task_time[j] * (x[j, k] + out[j, k]) for j in range(1, n + 1)) <= c,
            name=f"capacity_{k}",
        )

    for j in range(1, n + 1):
        model.addConstr(
            gp.quicksum(start[j, t] for t in range(c - task_time[j] + 1)) == 1,
            name=f"start_{j}",
        )

    for i, j in precedence:
        for k in range(1, m + 1):
            model.addConstr(
                x[j, k] <= gp.quicksum(x[i, h] for h in range(1, k + 1)),
                name=f"precedence_in_{i}_{j}_{k}",
            )
            model.addConstr(
                out[j, k] <= gp.quicksum(out[i, h] for h in range(k + 1, m + 1))
                + gp.quicksum(x[i, h] for h in range(1, m + 1)),
                name=f"precedence_out_{i}_{j}_{k}",
            )
            for t in range(c - task_time[j] + 1):
                model.addConstr(
                    start[j, t] <= gp.quicksum(
                        start[i, gamma] for gamma in range(max(0, t - task_time[i] + 1))
                    ) + 2 - x[i, k] - out[i, k] - x[j, k] - out[j, k],
                    name=f"temporal_{i}_{j}_{k}_{t}",
                )

    for i in range(1, n + 1):
        for j in range(1, i):
            for k in range(1, m + 1):
                for t in range(c):
                    model.addConstr(
                        x[i, k] + out[i, k] + x[j, k] + out[j, k]
                        + gp.quicksum(
                            start[i, gamma]
                            for gamma in range(max(0, t - task_time[i] + 1), t + 1)
                        )
                        + gp.quicksum(
                            start[j, gamma]
                            for gamma in range(max(0, t - task_time[j] + 1), t + 1)
                        ) <= 3,
                        name=f"overlap_{i}_{j}_{k}_{t}",
                    )

    for t in range(c):
        model.addConstr(
            gp.quicksum(
                power[j] * start[j, gamma]
                for j in range(1, n + 1)
                for gamma in range(max(0, t - task_time[j] + 1), t + 1)
            ) <= w_max,
            name=f"power_{t}",
        )

    for k in range(1, m + 1):
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for t in range(c):
                    model.addConstr(
                        start[j, t] <= gp.quicksum(
                            start[i, gamma] for gamma in range(max(0, t - task_time[i] + 1))
                        ) + 2 - x[i, k] - out[j, k],
                        name=f"gate_order_{i}_{j}_{k}_{t}",
                    )
    model.update()
    return model


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve UALBP from a .3pm instance with Gurobi")
    parser.add_argument("input_path", help="path to .3pm")
    args = parser.parse_args()

    env = None
    model = None
    try:
        start_time = time.time()
        env = create_wls_environment()
        n, m, c, task_time, power, precedence = parse_3pm_file(args.input_path)
        model = build_model(n, m, c, task_time, power, precedence, env)
        model.Params.Threads = 1
        model.Params.TimeLimit = TIME_LIMIT
        model.Params.OutputFlag = 1
        model.optimize()
        end_time = time.time()

        if model.SolCount > 0:
            status = {
                GRB.OPTIMAL: "OPTIMAL",
                GRB.TIME_LIMIT: "TIME_LIMIT",
            }.get(model.Status, str(model.Status))
            objective = int(model.ObjVal)
            print("Solution is feasible.")
            print("\n---------------------")
            print(f"@@@ {status}")
            print(f">>> Benchmark {os.path.basename(args.input_path)} OPT {objective}"
                  f" TimeTot {end_time - start_time}")
        else:
            status = str(model.Status)
            objective = ""
            print("Solution is infeasible or no incumbent was found.")
        write_csv_result(
            args.input_path, n, m, c, model, status, objective,
            end_time - start_time
        )
    except (RuntimeError, gp.GurobiError) as error:
        parser.error(str(error))
    finally:
        if model is not None:
            model.dispose()
        if env is not None:
            env.dispose()
