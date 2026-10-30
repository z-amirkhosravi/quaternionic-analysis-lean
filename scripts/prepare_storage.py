#!/usr/bin/env python3
"""Keep downloaded runtimes on native Linux storage, with stable project links."""

import hashlib
import os
from pathlib import Path

root = Path(__file__).resolve().parents[1]
key = hashlib.sha256(str(root).encode()).hexdigest()[:16]
runtime = Path(os.environ.get("MATH_RESEARCH_RUNTIME_DIR",
                             str(Path.home() / ".local/share/math-research-lean" / key)))
runtime = runtime.expanduser().absolute()
(root / ".lake").mkdir(exist_ok=True)
for relative, name in [(".elan", "elan"), (".lake/packages", "packages"), (".cache", "cache")]:
    link = root / relative
    if link.is_symlink():
        if not link.is_dir():
            raise SystemExit(f"Broken runtime link: {link}; restore its target before setup")
        print(f"Using {link} -> {link.resolve()}")
        continue
    if link.is_dir():
        print(f"Using existing local runtime directory: {link}")
        continue
    if link.exists():
        raise SystemExit(f"Runtime location is not a directory: {link}")
    target = runtime / name
    target.mkdir(parents=True, exist_ok=True)
    link.symlink_to(target, target_is_directory=True)
    print(f"Created {link} -> {target}")
