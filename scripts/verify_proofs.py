#!/usr/bin/env python3
import os
import re
import sys

def scan_lean_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    defs = []
    current_decl = None
    has_sorry = False
    
    # Regex to catch declarations. Very basic heuristic.
    # Matches: theorem foo, lemma bar, def baz
    decl_pattern = re.compile(r'^\s*(theorem|lemma|def|instance|structure|class)\s+([^\s{:(]+)')
    
    for i, line in enumerate(lines):
        # Check for declaration start
        match = decl_pattern.match(line)
        if match:
            # If we were tracking a previous declaration, save it
            if current_decl:
                defs.append((current_decl, has_sorry))
            
            kind = match.group(1)
            name = match.group(2)
            current_decl = f"{kind} {name}"
            has_sorry = False
        
        # Check for 'sorry' (ignoring comments is hard with regex, but we try basic '--')
        # This is a heuristic: if 'sorry' appears and not after '--'
        if 'sorry' in line:
            code_part = line.split('--')[0]
            if 'sorry' in code_part:
                has_sorry = True

    # Save last one
    if current_decl:
        defs.append((current_decl, has_sorry))
        
    return defs

def main():
    root_dir = "NOC"
    if len(sys.argv) > 1:
        root_dir = sys.argv[1]

    total_proved = 0
    total_sorry = 0

    print(f"Scanning {root_dir} for proofs...\n")

    for dirpath, dirnames, filenames in os.walk(root_dir):
        for filename in filenames:
            if filename.endswith(".lean"):
                path = os.path.join(dirpath, filename)
                results = scan_lean_file(path)
                
                # Filter out boring ones if you want, or print all
                file_has_sorry = any(r[1] for r in results)
                
                if file_has_sorry:
                    print(f"📄 {path}")
                    for decl, is_sorry in results:
                        if is_sorry:
                            print(f"  ❌ {decl} (HAS SORRY)")
                            total_sorry += 1
                        else:
                            # print(f"  ✅ {decl}") # Uncomment to see passed ones
                            total_proved += 1
                    print("")
                else:
                    # Fully proved file
                    count = len(results)
                    total_proved += count
                    # print(f"✅ {path} ({count} decls)")

    print("-" * 40)
    print(f"Summary:")
    print(f"  ✅ Proved/Defined: {total_proved}")
    print(f"  ❌ Incomplete:     {total_sorry}")
    
    if total_sorry > 0:
        print("\n(Run with --all to see proved theorems too, currently hiding them to focus on incomplete ones)")

if __name__ == "__main__":
    main()
