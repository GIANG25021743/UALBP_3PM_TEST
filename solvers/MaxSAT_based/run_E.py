import argparse
import csv
import os
import subprocess
import sys
import time

from pysat.examples.rc2 import RC2
from pysat.formula import WCNF


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RESULT_DIR = os.path.abspath(os.path.join(SCRIPT_DIR, "..", "..", "result"))
WCNF_PATH = os.path.join(SCRIPT_DIR, "enhanced.wcnf")
ENCODER_PATH = os.path.join(SCRIPT_DIR, "MSAT-E.py")


def write_result(result_path, record):
    os.makedirs(os.path.dirname(result_path), exist_ok=True)
    fieldnames = list(record)
    write_header = not os.path.exists(result_path) or os.path.getsize(result_path) == 0
    with open(result_path, "a", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=fieldnames)
        if write_header:
            writer.writeheader()
        writer.writerow(record)


def main():
    parser = argparse.ArgumentParser(description="Encode and solve an instance with MSAT-E and RC2")
    parser.add_argument("input_path", help="path to a .3pm instance")
    parser.add_argument(
        "result_name",
        nargs="?",
        default="MSAT-E_rc2_results.csv",
        help="CSV filename under result/ (default: MSAT-E_rc2_results.csv)",
    )
    args = parser.parse_args()

    input_path = os.path.abspath(args.input_path)
    if not os.path.isfile(input_path):
        parser.error("instance file not found: {}".format(input_path))

    result_name = os.path.basename(args.result_name)
    if not result_name:
        parser.error("result name must not be empty")
    result_path = os.path.join(RESULT_DIR, result_name)
    encode_started = time.perf_counter()
    encoder = subprocess.run(
        [sys.executable, ENCODER_PATH, input_path, WCNF_PATH],
        capture_output=True,
        text=True,
        check=False,
    )
    if encoder.returncode != 0:
        raise RuntimeError("MSAT-E encoding failed:\n{}".format(encoder.stderr.strip()))

    solve_started = time.perf_counter()
    formula = WCNF(from_file=WCNF_PATH)
    with RC2(formula) as solver:
        model = solver.compute()
        cost = solver.cost if model is not None else ""
    solve_time = time.perf_counter() - solve_started
    record = {
        "input_file": os.path.basename(input_path),
        "wcnf_file": os.path.basename(WCNF_PATH),
        "status": "optimal" if model is not None else "unsatisfiable",
        "cost": cost,
        "model_size": len(model) if model is not None else 0,
        "encoding_time_seconds": round(solve_started - encode_started, 6),
        "solve_time_seconds": round(solve_time, 6),
        "encoder_output": encoder.stdout.strip(),
    }
    write_result(result_path, record)
    print("RC2 result written to {}".format(result_path))
    print("status={} cost={} solve_time_seconds={}".format(
        record["status"], record["cost"], record["solve_time_seconds"]
    ))


if __name__ == "__main__":
    main()
