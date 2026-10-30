#!/usr/bin/env python3
"""Integration controls: real Lean proofs, placeholders, and additional axioms."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class VerificationControls(unittest.TestCase):
    def check_source(self, source, should_pass, expected_text, extra_args=()):
        # Never modify a real module or the root imports. An orphan module must
        # still be built and audited, including declarations in another namespace.
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="Control",
                                         dir=ROOT / "MathResearch", delete=False) as handle:
            handle.write("module\n\npublic section\n\n" + source)
            canary = Path(handle.name)
        try:
            result = subprocess.run([sys.executable, str(ROOT / "scripts/verify.py"), *extra_args],
                                    cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            self.assertEqual(result.returncode == 0, should_pass, result.stdout)
            self.assertIn(expected_text, result.stdout)
            record_path = Path(result.stdout.rsplit("Evidence: ", 1)[1].strip())
            record = json.loads(record_path.read_text())
            self.assertEqual(record["status"], "passed" if should_pass else "failed")
            self.assertIn(str(canary.relative_to(ROOT)), record["source_sha256"])
            print(f"Control evidence: {record_path}", flush=True)
        finally:
            canary.unlink()

    def test_valid_orphan_and_explicit_assumption(self):
        self.check_source(
            "namespace VerificationControl\n"
            "theorem valid : True := True.intro\n"
            "theorem conditional (unprovedPremise : False) : False := unprovedPremise\n"
            "end VerificationControl\n",
            True, '"declaration":"VerificationControl.conditional"', ('--clean-local',))

    def test_transitive_private_sorry_with_warning_suppressed(self):
        self.check_source(
            "set_option warningAsError false\n"
            "namespace VerificationControl\n"
            "private theorem unfinished : False := by sorry\n"
            "theorem dependent : False := unfinished\n"
            "end VerificationControl\n",
            False, "sorryAx")

    def test_unused_extra_axiom(self):
        self.check_source("axiom VerificationControl.unproved : False\n",
                          False, '"unexpected_axioms":["VerificationControl.unproved"]')

    def test_unused_private_axiom(self):
        self.check_source("private axiom VerificationControl.unproved : False\n",
                          False, "VerificationControl.unproved")

    def test_invalid_proof(self):
        self.check_source("theorem VerificationControl.invalid : False := True.intro\n",
                          False, "Type mismatch")


if __name__ == "__main__":
    unittest.main(verbosity=2)
