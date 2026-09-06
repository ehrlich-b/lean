#!/usr/bin/env python3
"""Check the curated publication boundary; this is not a proof verifier."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def check(root):
    files = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-z']).decode().split('\0')
    files = [name for name in files if name]
    errors = []
    root_files = {'README.md', 'LICENSE', 'NOTICE', 'AGENTS.md', '.gitignore',
                  'LeanFactory.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}
    prefixes = ('LeanFactory/', 'docs/', 'verification/', 'scripts/', 'tests/', '.github/')
    for name in files:
        p = root / name
        if name not in root_files and not name.startswith(prefixes):
            errors.append(f'unapproved publication path: {name}')
        if p.is_symlink() or not p.is_file():
            errors.append(f'non-regular publication file: {name}')
            continue
        data = p.read_bytes()
        if b'\x00' in data:
            errors.append(f'binary publication file: {name}')
        # Report paths only; never echo a possible credential.
        patterns = [rb'gh[pousr]_[A-Za-z0-9]{30,}', rb'sk-[A-Za-z0-9_-]{30,}',
                    rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----',
                    rb'/Users' + rb'/[^/\s]+/', rb'/home/' + rb'ehrli/', rb'192\.168\.\d+\.\d+']
        if any(re.search(pattern, data) for pattern in patterns):
            errors.append(f'private-context or credential pattern: {name}')
    lean = {name for name in files if name.endswith('.lean') and
            (name == 'LeanFactory.lean' or name.startswith('LeanFactory/'))}
    seen = set()
    pending = ['LeanFactory.lean']
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        if name not in lean:
            errors.append(f'missing tracked import: {name}')
            continue
        seen.add(name)
        source = (root / name).read_text()
        for mod in re.findall(r'^import (LeanFactory(?:\.[A-Za-z0-9_]+)*)\s*$', source, re.M):
            pending.append(mod.replace('.', '/') + '.lean')
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b|fail "Implement', source):
            errors.append(f'forbidden proof placeholder or axiom token: {name}')
    for name in sorted(lean - seen):
        errors.append(f'unexported Lean module: {name}')
    manifest = json.loads((root / 'docs/source-manifest.json').read_text())
    expected = lean | {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}
    if set(manifest) != expected:
        errors.append('source manifest does not cover exactly every Lean module and dependency pin')
    for name in expected:
        if manifest.get(name) != hashlib.sha256((root / name).read_bytes()).hexdigest():
            errors.append(f'source digest mismatch: {name}')
    return errors


if __name__ == '__main__':
    failures = check(Path.cwd())
    print('\n'.join(failures) if failures else 'Publication boundary and complete import coverage: PASS')
    sys.exit(bool(failures))
