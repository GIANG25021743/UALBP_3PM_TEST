#!/bin/bash
# =============================================================================
# Run MaxSAT-based encoders and RC2 on a single SALB3PM instance
#
# Usage: bash scripts/run_maxsat.sh <path_to_3pm_file> [formulation] [result_csv]
#
# formulation options: enhanced, inaugural, both (default)
# =============================================================================

set -e

INSTANCE="$1"
FORMULATION="${2:-both}"
RESULT_NAME="$3"
PYTHON="${PYTHON:-python3}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SOLVER_DIR="$SCRIPT_DIR/../solvers/MaxSAT_based"

if [ -z "$INSTANCE" ]; then
    echo "Usage: bash scripts/run_maxsat.sh <path_to_3pm_file> [formulation] [result_csv]"
    echo ""
    echo "Formulation options: enhanced, inaugural, both (default)"
    exit 1
fi

if [ ! -f "$INSTANCE" ]; then
    echo "Error: Instance file '$INSTANCE' not found."
    exit 1
fi

run_solver() {
    local solver_script="$1"
    if [ -n "$RESULT_NAME" ]; then
        "$PYTHON" "$SOLVER_DIR/$solver_script" "$INSTANCE" "$RESULT_NAME"
    else
        "$PYTHON" "$SOLVER_DIR/$solver_script" "$INSTANCE"
    fi
}

case "$FORMULATION" in
    enhanced|e)
        echo "Running Enhanced formulation with RC2..."
        run_solver "run_E.py"
        ;;
    inaugural|i)
        echo "Running Inaugural formulation with RC2..."
        run_solver "run_I.py"
        ;;
    both)
        echo ""
        echo "Running Enhanced formulation with RC2..."
        run_solver "run_E.py"
        echo ""
        echo "Running Inaugural formulation with RC2..."
        run_solver "run_I.py"
        ;;
    *)
        echo "Unknown formulation: $FORMULATION"
        echo "Available: enhanced, inaugural, both"
        exit 1
        ;;
esac

echo ""
echo "WCNF files: $SOLVER_DIR/enhanced.wcnf and $SOLVER_DIR/inaugural.wcnf"
echo "Results are written under the repository result/ directory."
