#!/usr/bin/env python3
import sys
import re
import json

def parse_log(stream):
    errors = []
    # Regex for Lean 4 error format:
    # error: file/path.lean:line:col: message
    error_pattern = re.compile(r'^error: ([^:]+):(\d+):(\d+): (.+)')
    
    for line in stream:
        line = line.strip()
        match = error_pattern.match(line)
        if match:
            errors.append({
                "file": match.group(1),
                "line": int(match.group(2)),
                "col": int(match.group(3)),
                "message": match.group(4)
            })
    
    return errors

if __name__ == "__main__":
    errors = parse_log(sys.stdin)
    print(json.dumps(errors, indent=2))
