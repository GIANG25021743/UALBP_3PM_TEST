#!/bin/bash
# =============================================================================
# Run ILP solvers on a single SALB3PM instance
#
# Usage: bash scripts/run_ilp.sh <path_to_3pm_file> [solver]
#
# solver options: gurobi, cplex, both (default)
# Results are appended to result/ilp_results.csv.
# =============================================================================

set -e

INSTANCE="$1"
SOLVER="${2:-both}"
PYTHON="${PYTHON:-python3}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SOLVER_DIR="$SCRIPT_DIR/../solvers/ILP"

if [ -z "$INSTANCE" ]; then
    echo "Usage: bash scripts/run_ilp.sh <path_to_3pm_file> [solver]"
    echo "Solver options: gurobi, cplex, both (default)"
    exit 1
fi

if [ ! -f "$INSTANCE" ]; then
    echo "Error: Instance file '$INSTANCE' not found."
    exit 1
fi

run_solver() {
    local solver_script="$1"
    local solver_name="$2"
    echo "========================================"
    echo "Running $solver_name on $(basename "$INSTANCE")"
    echo "========================================"
    "$PYTHON" "$SOLVER_DIR/$solver_script" "$INSTANCE"
}

case "$SOLVER" in
    gurobi|g)
        run_solver "GUROBI-7200s.py" "Gurobi"
        ;;
    cplex|c)
        run_solver "CPLEX-7200s.py" "CPLEX"
        ;;
    both)
        run_solver "GUROBI-7200s.py" "Gurobi"
        echo ""
        run_solver "CPLEX-7200s.py" "CPLEX"
        ;;
    *)
        echo "Unknown solver: $SOLVER"
        echo "Available: gurobi, cplex, both"
        exit 1
        ;;
esac

echo ""
echo "Results are written to result/ilp_results.csv"
