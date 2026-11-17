import csv
import os


FIELDNAMES = [
    "Inputfile", "n", "m", "c", "variables", "clauses",
    "besvalue", "time", "status"
]


def write_result(input_file, solver_name, n, m, c, variables, clauses,
                 best_value, solve_time, status):
    result_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "result")
    )
    os.makedirs(result_dir, exist_ok=True)

    result_file = os.path.join(result_dir, f"{solver_name}_results.csv")
    records = {}
    if os.path.exists(result_file):
        with open(result_file, "r", newline="", encoding="utf-8") as file:
            for record in csv.DictReader(file):
                try:
                    key = (int(record["n"]), int(record["m"]), int(record["c"]))
                except (KeyError, TypeError, ValueError):
                    continue
                records[key] = record

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
        writer = csv.DictWriter(file, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(records.values())
