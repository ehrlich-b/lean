import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
import json
import hashlib

spec = importlib.util.spec_from_file_location('public', Path(__file__).parents[1] / 'scripts/check_public.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class PublicationTests(unittest.TestCase):
    def fixture(self, root):
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        (root / 'docs').mkdir()
        for name, content in {'LeanFactory.lean': '', 'lakefile.toml': '',
                              'lake-manifest.json': '{}', 'lean-toolchain': 'pin'}.items():
            (root / name).write_text(content)
        self.refresh(root)

    def refresh(self, root):
        names = ['LeanFactory.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
        names += [str(p.relative_to(root)) for p in (root / 'LeanFactory').rglob('*.lean')]
        (root / 'docs/source-manifest.json').write_text(json.dumps({
            n: hashlib.sha256((root / n).read_bytes()).hexdigest() for n in names}))
        subprocess.run(['git', '-C', str(root), 'add', '.'], check=True)

    def test_orphan_cannot_hide_outside_root_build(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d); self.fixture(r)
            (r/'LeanFactory').mkdir(); (r/'LeanFactory/Hidden.lean').write_text('')
            self.refresh(r)
            self.assertTrue(any('unexported' in e for e in module.check(r)))
            (r/'LeanFactory.lean').write_text('import LeanFactory.Hidden\n');self.refresh(r)
            self.assertEqual(module.check(r), [])

    def test_stale_receipt_and_missing_import_fail(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);self.fixture(r)
            (r/'LeanFactory.lean').write_text('import LeanFactory.Missing\n')
            errors=module.check(r)
            self.assertTrue(any('digest mismatch' in e for e in errors))
            self.assertTrue(any('missing tracked import' in e for e in errors))

    def test_private_paths_and_symlinks_fail(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d);self.fixture(r)
            (r/'docs/note.md').write_text('/home/' + 'ehrli/' + 'private')
            (r/'docs/link').symlink_to('note.md');self.refresh(r)
            errors=module.check(r)
            self.assertTrue(any('private-context' in e for e in errors))
            self.assertTrue(any('non-regular' in e for e in errors))

if __name__ == '__main__': unittest.main()
