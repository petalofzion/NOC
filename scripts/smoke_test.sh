#!/usr/bin/env bash
set -e

echo "Running NOC Smoke Test..."
echo "Target: NOC.Dev.Checks"

# Build the specific module. 
# If this passes, imports work and symbols exist.
lake build NOC.Dev.Checks

echo "✅ Smoke Test Passed! Core library wiring is intact."
