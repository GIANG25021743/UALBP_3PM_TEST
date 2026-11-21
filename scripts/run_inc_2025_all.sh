#!/bin/bash
# =============================================================================
# Run INC_2025 on every .3pm instance under benchmarks/
#
# Usage: bash scripts/run_inc_2025_all.sh
# =============================================================================

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
BENCHMARK_DIR="$ROOT_DIR/benchmarks"
SOLVER="$ROOT_DIR/solvers/Proposed/INC_2025.py"
PYTHON="${PYTHON:-python3}"

if [ ! -d "$BENCHMARK_DIR" ]; then
    echo "Error: Benchmark directory '$BENCHMARK_DIR' not found." >&2
    exit 1
fi

if [ ! -f "$SOLVER" ]; then
    echo "Error: Solver '$SOLVER' not found." >&2
    exit 1
fi

mapfile -d '' INSTANCES < <(find "$BENCHMARK_DIR" -type f -name '*.3pm' -print0 | sort -z)

if [ "${#INSTANCES[@]}" -eq 0 ]; then
    echo "Error: No .3pm files found under '$BENCHMARK_DIR'." >&2
    exit 1
fi

echo "Found ${#INSTANCES[@]} benchmark(s)."

for INSTANCE in "${INSTANCES[@]}"; do
    echo ""
    echo "========================================"
    echo "Running INC_2025 on $(basename "$INSTANCE")"
    echo "========================================"
    "$PYTHON" "$SOLVER" "$INSTANCE"
done

echo ""
echo "Completed ${#INSTANCES[@]} benchmark(s)."
