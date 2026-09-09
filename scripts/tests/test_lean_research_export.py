from __future__ import annotations

import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal"
sys.path.insert(0, str(ROOT / "scripts"))

import lean_research_export as exporter  # noqa: E402


def protocol_output(**updates) -> str:
    """Empty protocol envelope for subprocess tests, not mathematical test data."""
    payload = {
        "schema_version": 1,
        "toolchain": exporter.TOOLCHAIN,
        "modules": ["Init"],
        "declarations": [],
        "status": "ok",
        "error": None,
    }
    payload.update(updates)
    return exporter.EXPORT_SENTINEL + json.dumps(payload) + "\n"


class DriverTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory(prefix="hgt-export-driver-test-")
        self.addCleanup(self.directory.cleanup)
        self.formal = Path(self.directory.name)
        (self.formal / "lean-toolchain").write_text(exporter.TOOLCHAIN + "\n")

    def process(self, stdout=None, stderr="", returncode=0):
        process = mock.Mock(pid=987654321, returncode=returncode)
        process.communicate.return_value = (protocol_output() if stdout is None else stdout, stderr)
        return process

    def test_single_foreground_scratch_call_and_cleanup(self) -> None:
        seen = {}
        process = self.process(stdout="compiler diagnostic\n" + protocol_output())

        def launch(command, **kwargs):
            seen.update(command=command, kwargs=kwargs)
            scratch = Path(command[-1])
            seen["scratch"] = scratch
            seen["source"] = scratch.read_text(encoding="utf-8")
            self.assertNotIn(self.formal, scratch.parents)
            return process

        with mock.patch.object(exporter.subprocess, "Popen", side_effect=launch) as popen:
            result = exporter.export_module(self.formal, "Init", timeout_seconds=7)
        self.assertEqual(result["status"], "ok", result)
        self.assertEqual(result["toolchain"], exporter.TOOLCHAIN)
        self.assertEqual(result["diagnostics"], "compiler diagnostic")
        popen.assert_called_once()
        self.assertEqual(seen["command"][:3], ["lake", "env", "lean"])
        self.assertEqual(len(seen["command"]), 4)
        self.assertEqual(seen["kwargs"]["cwd"], self.formal.resolve())
        self.assertTrue(seen["source"].startswith("import «Init»\n"))
        self.assertNotIn("import GaloisForLFunctions", seen["source"])
        self.assertIn('#export_research_corpus ["Init"]', seen["source"])
        self.assertFalse(seen["scratch"].exists())
        process.communicate.assert_called_once_with(timeout=7)

    def test_rejects_root_umbrella_and_import_injection_before_starting_lean(self) -> None:
        with mock.patch.object(exporter.subprocess, "Popen") as popen:
            for module in ("GaloisForLFunctions", "", "../Init", "Init/Prelude", "Init\\Prelude",
                           "Init\nimport GaloisForLFunctions", "Init..Prelude", "«Init»", "Init\0"):
                with self.subTest(module=module):
                    result = exporter.export_module(self.formal, module)
                    self.assertEqual(result["status"], "error")
                    self.assertTrue(result["error"])
            popen.assert_not_called()

    def test_module_components_are_quoted_including_unicode_and_keywords(self) -> None:
        self.assertEqual(exporter._quoted_module("Corpus.α.import"), "«Corpus».«α».«import»")

    def test_invalid_deadlines_and_wrong_toolchain_do_not_launch(self) -> None:
        with mock.patch.object(exporter.subprocess, "Popen") as popen:
            for timeout in (0, -1, float("inf"), float("nan"), "60", None, True):
                with self.subTest(timeout=timeout):
                    result = exporter.export_module(self.formal, "Init", timeout_seconds=timeout)
                    self.assertEqual(result["status"], "error")
            (self.formal / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
            result = exporter.export_module(self.formal, "Init")
            self.assertIn("requires", result["error"])
            popen.assert_not_called()

    def test_missing_executable_or_project_is_unavailable(self) -> None:
        with mock.patch.object(exporter.subprocess, "Popen", side_effect=FileNotFoundError("lake")):
            result = exporter.export_module(self.formal, "Init")
        self.assertEqual(result["status"], "unavailable")
        self.assertEqual(result["declarations"], [])
        self.assertIsNone(result["toolchain"])
        self.assertEqual(exporter.export_module(self.formal / "missing", "Init")["status"], "unavailable")

    def test_nonzero_exit_never_accepts_a_payload(self) -> None:
        process = self.process(stderr="object file does not exist", returncode=1)
        with mock.patch.object(exporter.subprocess, "Popen", return_value=process):
            result = exporter.export_module(self.formal, "Init")
        self.assertEqual(result["status"], "error")
        self.assertIn("object file does not exist", result["error"])
        self.assertIsNone(result["toolchain"])

    def test_rejects_missing_duplicate_corrupt_or_mismatched_payload(self) -> None:
        for stdout in ("", protocol_output() * 2, exporter.EXPORT_SENTINEL + "{",
                       protocol_output(schema_version=99), protocol_output(modules=["Lean"]),
                       protocol_output(declarations={}), protocol_output(status="proved")):
            with self.subTest(stdout=stdout):
                with mock.patch.object(exporter.subprocess, "Popen", return_value=self.process(stdout)):
                    result = exporter.export_module(self.formal, "Init")
                self.assertEqual(result["status"], "error")
                self.assertEqual(result["declarations"], [])

    def test_actual_compiler_toolchain_mismatch_is_reported(self) -> None:
        process = self.process(protocol_output(toolchain="leanprover/lean4:v4.99.0"))
        with mock.patch.object(exporter.subprocess, "Popen", return_value=process):
            result = exporter.export_module(self.formal, "Init")
        self.assertEqual(result["status"], "error")
        self.assertEqual(result["toolchain"], "leanprover/lean4:v4.99.0")

    @unittest.skipUnless(os.name == "posix", "POSIX process-group cleanup")
    def test_timeout_and_cancellation_kill_only_owned_group_and_reap(self) -> None:
        for exception in (subprocess.TimeoutExpired("lean", 1), KeyboardInterrupt()):
            with self.subTest(exception=type(exception).__name__):
                process = self.process()
                process.communicate.side_effect = [exception, ("", "stopped")]
                scratch_paths = []

                def launch(command, **kwargs):
                    self.assertTrue(kwargs["start_new_session"])
                    scratch_paths.append(Path(command[-1]))
                    return process

                with mock.patch.object(exporter.subprocess, "Popen", side_effect=launch), \
                     mock.patch.object(exporter.os, "killpg") as killpg:
                    if isinstance(exception, KeyboardInterrupt):
                        with self.assertRaises(KeyboardInterrupt):
                            exporter.export_module(self.formal, "Init", timeout_seconds=1)
                    else:
                        result = exporter.export_module(self.formal, "Init", timeout_seconds=1)
                        self.assertEqual(result["status"], "timeout")
                        self.assertIn("stopped", result["error"])
                    killpg.assert_called_once_with(process.pid, exporter.signal.SIGKILL)
                self.assertEqual(process.communicate.call_count, 2)
                self.assertFalse(scratch_paths[0].exists())

    def test_batch_uses_one_process_and_deduplicates_modules(self) -> None:
        process = self.process(protocol_output(modules=["Init", "Init.Data.Nat.Basic"]))
        sources = []

        def launch(command, **kwargs):
            sources.append(Path(command[-1]).read_text())
            return process

        with mock.patch.object(exporter.subprocess, "Popen", side_effect=launch) as popen:
            result = exporter.export_modules(self.formal, ["Init", "Init.Data.Nat.Basic", "Init"])
        self.assertEqual(result["status"], "ok", result)
        popen.assert_called_once()
        self.assertEqual(result["modules"], ["Init", "Init.Data.Nat.Basic"])
        self.assertEqual(set(result["snapshots"]), set(result["modules"]))
        self.assertIn('import «Init».«Data».«Nat».«Basic»', sources[0])
        self.assertEqual(sources[0].count("import «Init»\n"), 1)
        self.assertIn('#export_research_corpus ["Init", "Init.Data.Nat.Basic"]', sources[0])
        self.assertEqual(result["compiler_snapshot_status"], "compiled_snapshot")

    def test_batch_rejects_invalid_requests_and_root_before_launch(self) -> None:
        with mock.patch.object(exporter.subprocess, "Popen") as popen:
            for modules in ([], "Init", ["Init", "GaloisForLFunctions"], ["Init", None]):
                with self.subTest(modules=modules):
                    self.assertEqual(exporter.export_modules(self.formal, modules)["status"], "error")
            self.assertEqual(exporter.export_modules(self.formal, ["Init"],
                             source_paths={"Lean": self.formal / "Lean.lean"})["status"], "error")
            popen.assert_not_called()

    def test_invalid_compiler_artifact_metadata_returns_error(self) -> None:
        for reports in (None, {}, [{"module": "Lean"}],
                        [{"module": "Init", "artifact_path": 12}],
                        [{"module": "Init", "direct_imports": "Init.Prelude"}]):
            with self.subTest(reports=reports):
                with mock.patch.object(exporter.subprocess, "Popen", return_value=self.process(
                        protocol_output(module_artifacts=reports))):
                    result = exporter.export_module(self.formal, "Init")
                self.assertEqual(result["status"], "error")


class SnapshotTests(unittest.TestCase):
    """Filesystem provenance fixtures; fake artifact bytes are never sent to Lean."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="hgt-corpus-snapshot-test-")
        self.addCleanup(temporary.cleanup)
        self.formal = Path(temporary.name).resolve()
        (self.formal / "lean-toolchain").write_text(exporter.TOOLCHAIN)

    def module(self, name="Corpus.A", *, package=None, src_dir="", build_dir=".lake/build",
               source_time=100, artifact_time=200):
        root = self.formal if package is None else self.formal / ".lake/packages" / package
        relative = Path(*name.split("."))
        source = root / src_dir / relative.with_suffix(".lean")
        artifact = root / build_dir / "lib/lean" / relative.with_suffix(".olean")
        source.parent.mkdir(parents=True, exist_ok=True)
        artifact.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("def fixture : Nat := 0\n")
        artifact.write_bytes(b"opaque artifact bytes for filesystem tests only")
        os.utime(source, ns=(source_time * 10**9, source_time * 10**9))
        os.utime(artifact, ns=(artifact_time * 10**9, artifact_time * 10**9))
        return source, artifact

    def setup_imports(self, module, imports):
        path = self.formal / ".lake/build/ir" / Path(*module.split(".")).with_suffix(".setup.json")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"name": module, "importArts": imports}))
        return path

    def test_newer_artifact_and_matching_trace_source_hash_do_not_certify_current(self) -> None:
        source, artifact = self.module()
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        artifact.with_suffix(".trace").write_text(json.dumps({
            "inputs": [[str(source), source_hash]], "depHash": "unverified-build-graph"}))
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(result["artifact_path"], str(artifact))
        self.assertEqual(result["artifact_hash"], hashlib.sha256(artifact.read_bytes()).hexdigest())
        self.assertEqual(result["source_hash"], source_hash)
        self.assertEqual(result["artifact_mtime_ns"], 200 * 10**9)
        self.assertEqual(result["freshness"], "unavailable")
        self.assertFalse(result["provenance_verified"])
        self.assertTrue(result["snapshot_stable"])
        self.assertEqual(result["trace"]["status"], "input_hashes_unverified")
        self.assertEqual(result["compiler_snapshot_status"], "compiled_snapshot")

    def test_source_newer_than_artifact_is_stale(self) -> None:
        source, _ = self.module(source_time=300)
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(result["freshness"], "stale")
        self.assertIn("source_newer_than_artifact", [e["reason"] for e in result["evidence"]])

    def test_old_timestamp_on_edited_source_does_not_create_current_status(self) -> None:
        source, _ = self.module()
        before = hashlib.sha256(source.read_bytes()).hexdigest()
        source.write_text("def fixture : Nat := 1\n")
        os.utime(source, ns=(100 * 10**9, 100 * 10**9))
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertNotEqual(result["source_hash"], before)
        self.assertEqual(result["freshness"], "unavailable")

    def test_missing_artifact_and_missing_source_are_explicit(self) -> None:
        source, artifact = self.module()
        artifact.unlink()
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertIsNone(result["artifact_hash"])
        self.assertEqual(result["compiler_snapshot_status"], "unavailable")
        self.assertEqual(result["freshness"], "unavailable")
        source, _ = self.module()
        source.unlink()
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertIsNone(result["source_hash"])
        self.assertEqual(result["freshness"], "unavailable")

    def test_standalone_validator_rejects_unsupported_project_toolchain(self) -> None:
        source, _ = self.module()
        (self.formal / "lean-toolchain").write_text("leanprover/lean4:v4.31.0")
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertIsNone(result["artifact_path"])
        self.assertEqual(result["freshness"], "unavailable")
        self.assertEqual(result["compiler_snapshot_status"], "unavailable")
        self.assertIn("unsupported_toolchain", [entry["reason"] for entry in result["evidence"]])

    def test_timeout_preserves_preexport_stale_status(self) -> None:
        source, _ = self.module(source_time=300)
        process = mock.Mock()
        process.communicate.side_effect = [subprocess.TimeoutExpired("lean", 1)]
        with mock.patch.object(exporter.subprocess, "Popen", return_value=process), \
             mock.patch.object(exporter, "_stop_process", return_value=("", "")):
            result = exporter.export_module(self.formal, "Corpus.A", source_path=source)
        self.assertEqual(result["status"], "timeout")
        self.assertEqual(result["freshness"], "stale")

    def test_package_source_and_custom_build_directory_resolution(self) -> None:
        source, artifact = self.module("Pkg.A", package="pkg", src_dir="Lean4", build_dir=".lake/build/default")
        (self.formal / ".lake/packages/pkg/lakefile.toml").write_text(
            'name = "pkg"\nbuildDir = ".lake/build/default"\n[[lean_lib]]\nname = "Pkg"\nsrcDir = "Lean4"\n')
        result = exporter.validate_compiled_snapshot(self.formal, "Pkg.A", None)
        self.assertEqual(result["artifact_path"], str(artifact))
        self.assertEqual(result["source_path"], str(source))

    def test_ambiguous_artifacts_are_not_arbitrarily_selected(self) -> None:
        source, _ = self.module()
        self.module(package="shadow")
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertIsNone(result["artifact_path"])
        self.assertEqual(result["freshness"], "unavailable")
        self.assertEqual(len(result["evidence"][0]["candidates"]), 2)

    def test_transitive_import_source_and_artifact_staleness(self) -> None:
        source, _ = self.module(artifact_time=400)
        _, b_art = self.module("Corpus.B", artifact_time=300)
        _, c_art = self.module("Corpus.C", source_time=350, artifact_time=300)
        self.setup_imports("Corpus.A", {"Corpus.B": [str(b_art)], "Corpus.C": [str(c_art)]})
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(result["freshness"], "stale")
        self.assertEqual(result["transitive_status"], "checked_for_staleness")
        self.assertEqual(len(result["dependencies"]), 2)
        c = next(row for row in result["dependencies"] if row["module"] == "Corpus.C")
        self.assertIn("dependency_source_newer_than_artifact", c["reasons"])
        os.utime(c_art, ns=(500 * 10**9, 500 * 10**9))
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        c = next(row for row in result["dependencies"] if row["module"] == "Corpus.C")
        self.assertIn("import_artifact_newer_than_parent", c["reasons"])

    def test_missing_import_artifacts_and_invalid_setup_are_explicit(self) -> None:
        source, _ = self.module()
        setup = self.setup_imports("Corpus.A", {"Corpus.Absent": [str(self.formal / "absent.olean")]})
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(result["freshness"], "stale")
        self.assertEqual(result["transitive_status"], "partial")
        setup.write_text("{not valid JSON")
        result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(result["transitive_status"], "partial")
        self.assertNotEqual(result["freshness"], "current")

    def test_source_change_during_validation_detected_despite_preserved_mtime_and_size(self) -> None:
        source, artifact = self.module()
        fingerprint = exporter._fingerprint

        def racing_read(path, **kwargs):
            info = fingerprint(path, **kwargs)
            if path == artifact:
                source.write_text("def fixture : Nat := 1\n")
                os.utime(source, ns=(100 * 10**9, 100 * 10**9))
            return info

        with mock.patch.object(exporter, "_fingerprint", side_effect=racing_read):
            result = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(result["freshness"], "stale")
        self.assertFalse(result["snapshot_stable"])
        self.assertIn(str(source), result["evidence"][-1]["paths"])

    def test_source_and_artifact_change_while_compiler_runs(self) -> None:
        for change_artifact in (False, True):
            with self.subTest(change_artifact=change_artifact):
                source, artifact = self.module()
                source_hash = hashlib.sha256(source.read_bytes()).hexdigest()

                def communicate(**kwargs):
                    path = artifact if change_artifact else source
                    before = path.stat()
                    data = path.read_bytes()
                    path.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
                    os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
                    return protocol_output(modules=["Corpus.A"], module_artifacts=[{
                        "module": "Corpus.A", "source_path": str(source), "artifact_path": str(artifact),
                        "direct_imports": []}]), ""

                process = mock.Mock(returncode=0)
                process.communicate.side_effect = communicate
                with mock.patch.object(exporter.subprocess, "Popen", return_value=process):
                    result = exporter.export_module(self.formal, "Corpus.A", source_path=source)
                self.assertEqual(result["status"], "ok", result)
                self.assertEqual(result["snapshot"]["freshness"], "stale")
                self.assertEqual(result["compiler_snapshot_status"], "compiled_snapshot")
                self.assertFalse(result["snapshot"]["snapshot_stable"])
                self.assertEqual(result["snapshot"]["source_hash"], source_hash)
                if change_artifact:
                    self.assertIsNone(result["snapshot"]["artifact_hash"])
                    self.assertIsNone(result["snapshot"]["artifact_set_hash"])

    def test_private_olean_changes_invalidate_artifact_set_identity(self) -> None:
        source, artifact = self.module()
        private = Path(f"{artifact}.private")
        private.write_bytes(b"body one")
        before = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        private.write_bytes(b"body two")
        after = exporter.validate_compiled_snapshot(self.formal, "Corpus.A", source)
        self.assertEqual(before["artifact_hash"], after["artifact_hash"])
        self.assertNotEqual(before["artifact_set_hash"], after["artifact_set_hash"])

    def test_wrong_requested_source_does_not_receive_compiler_artifact_freshness(self) -> None:
        source, artifact = self.module()
        wrong_source = self.formal / "Wrong.lean"
        wrong_source.write_text("def other := 2\n")
        process = mock.Mock(returncode=0)
        process.communicate.return_value = (protocol_output(modules=["Corpus.A"], module_artifacts=[{
            "module": "Corpus.A", "artifact_path": str(artifact), "source_path": str(source)}]), "")
        with mock.patch.object(exporter.subprocess, "Popen", return_value=process):
            result = exporter.export_module(self.formal, "Corpus.A", source_path=wrong_source)
        self.assertFalse(result["snapshot"]["source_path_matches_compiler"])
        self.assertIsNone(result["snapshot"]["source_hash"])
        self.assertEqual(result["snapshot"]["source_path"], str(source))
        self.assertNotEqual(result["snapshot"]["freshness"], "current")


def compile_scratch(source: str, sentinel: str) -> dict:
    """Compile test-only Lean commands, using cached imports and no output olean."""
    with tempfile.TemporaryDirectory(prefix="hgt-corpus-compiler-test-") as directory:
        scratch = Path(directory) / "CorpusTest.lean"
        scratch.write_text(source, encoding="utf-8")
        process = subprocess.Popen(
            ["lake", "env", "lean", str(scratch)], cwd=FORMAL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            start_new_session=(os.name == "posix"),
        )
        try:
            stdout, stderr = process.communicate(timeout=60)
        except BaseException:
            exporter._stop_process(process)
            raise
        if process.returncode:
            raise AssertionError(f"Lean scratch failed:\n{stdout}\n{stderr}")
        payloads = [line[len(sentinel):] for line in stdout.splitlines() if line.startswith(sentinel)]
        if len(payloads) != 1:
            raise AssertionError(f"Expected compiler payload:\n{stdout}\n{stderr}")
        return json.loads(payloads[0])


@unittest.skipUnless(shutil.which("lake"), "Lean/Lake unavailable; integration never installs them")
class CompilerIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cached = FORMAL / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Logic/Nonempty.olean"
        if not cached.is_file():
            raise unittest.SkipTest("Mathlib.Logic.Nonempty olean unavailable; no builds allowed")
        cls.mathlib = exporter.export_module(FORMAL, "Mathlib.Logic.Nonempty")
        if cls.mathlib["status"] != "ok":
            raise AssertionError(cls.mathlib)
        cls.rows = {row["name"]: row for row in cls.mathlib["declarations"]}

    def test_explicit_data_unnamed_hypotheses_and_instance_binders_survive(self) -> None:
        row = self.rows["Nonempty.map"]
        self.assertEqual(row["kind"], "theorem")
        self.assertEqual([binder["binder_info"] for binder in row["binders"]],
                         ["implicit", "implicit", "explicit", "explicit"])
        self.assertEqual(row["binders"][2]["name"], "f")
        self.assertIn("α → β", row["binders"][2]["type"])
        self.assertIn("Nonempty", row["binders"][3]["type"])
        instance = self.rows["Nonempty.elim_to_inhabited"]["binders"]
        self.assertEqual([binder["binder_info"] for binder in instance],
                         ["implicit", "instance_implicit", "implicit", "explicit"])
        self.assertEqual(instance[1]["name"], "h")
        self.assertIn("α", instance[1]["type"])

    def test_direct_type_and_proof_dependencies_and_transitive_axioms(self) -> None:
        row = self.rows["Nonempty.imp"]
        self.assertIn("Nonempty", row["type_dependencies"])
        self.assertNotIn("Nonempty.forall", row["type_dependencies"])
        self.assertIn("Nonempty.forall", row["proof_dependencies"])
        self.assertEqual(row["proof_dependencies_status"], "available")
        choice = self.rows["Nonempty.some"]
        self.assertIn("Classical.choice", choice["proof_dependencies"])
        self.assertEqual(choice["axioms"], ["Classical.choice"])
        self.assertEqual(choice["axioms_status"], "available")

    def test_exact_module_ownership_including_private_generated_declarations(self) -> None:
        self.assertNotIn("Classical.choice", self.rows)
        self.assertTrue(all(row["module"] == "Mathlib.Logic.Nonempty" for row in self.rows.values()))
        generated = [name for name in self.rows if name.startswith("_private.Mathlib.Logic.Nonempty.")]
        self.assertTrue(generated)
        dependencies = self.rows["Nonempty.map"]["proof_dependencies"]
        self.assertTrue(set(generated).intersection(dependencies))

    def test_compiler_range_points_to_real_declaration_and_doc_is_retained(self) -> None:
        row = self.rows["Nonempty.map"]
        source = row["source"]
        self.assertEqual(source["status"], "available")
        self.assertTrue(Path(source["path"]).is_absolute())
        text = Path(source["path"]).read_text(encoding="utf-8").splitlines()
        start, end = source["selection_range"]["start"], source["selection_range"]["end"]
        self.assertEqual(start["line"], end["line"])
        self.assertEqual(text[start["line"] - 1][start["column"]:end["column"]], "Nonempty.map")
        self.assertIn("Given", row["doc"])

    def test_protocol_rejects_empty_lists_for_unavailable_proofs(self) -> None:
        payload = copy.deepcopy(self.mathlib)
        payload["declarations"][0]["proof_dependencies_status"] = "unavailable"
        payload["declarations"][0]["proof_dependencies"] = []
        with self.assertRaisesRegex(ValueError, "fabricates unavailable"):
            exporter._parse_payload(exporter.EXPORT_SENTINEL + json.dumps(payload), "Mathlib.Logic.Nonempty")

    def test_small_init_module_without_builds(self) -> None:
        result = exporter.export_module(FORMAL, "Init.Data.Nat.Basic")
        self.assertEqual(result["status"], "ok", result["error"])
        row = next(row for row in result["declarations"] if row["name"] == "Nat.add_comm")
        self.assertEqual(row["module"], "Init.Data.Nat.Basic")
        self.assertIn("HAdd.hAdd", row["type_dependencies"])
        self.assertIn("instAddNat", row["type_dependencies"])
        self.assertIn("Eq", row["type_dependencies"])
        self.assertTrue(row["proof_dependencies"])
        self.assertEqual(len(row["binders"]), 2)

    def test_real_batch_retains_all_owners_and_confirms_snapshot_paths(self) -> None:
        modules = ["Mathlib.Logic.Nonempty", "Init.Data.Nat.Basic"]
        result = exporter.export_modules(FORMAL, modules, source_paths={
            modules[0]: Path(self.rows["Nonempty.map"]["source"]["path"])})
        self.assertEqual(result["status"], "ok", result["error"])
        self.assertEqual(result["modules"], modules)
        self.assertEqual(result["compiler_snapshot_status"], "compiled_snapshot")
        mathlib_rows = {row["name"]: row["type_shape"] for row in result["declarations"]
                        if row["module"] == modules[0]}
        self.assertEqual(mathlib_rows, {name: row["type_shape"] for name, row in self.rows.items()})
        self.assertTrue(any(row["name"] == "Nat.add_comm" for row in result["declarations"]))
        for module in modules:
            snapshot = result["snapshots"][module]
            self.assertTrue(snapshot["artifact_path_matches_compiler"], snapshot)
            self.assertTrue(snapshot["source_path_matches_compiler"], snapshot)
            self.assertTrue(snapshot["snapshot_stable"], snapshot)
            self.assertNotEqual(snapshot["freshness"], "current")
            self.assertEqual(snapshot["source_hash"], hashlib.sha256(Path(snapshot["source_path"]).read_bytes()).hexdigest())
            self.assertTrue(snapshot["artifact_set_hash"])
            self.assertIsInstance(snapshot["direct_imports"], list)
        self.assertTrue(all(row["compiler_snapshot_status"] == "compiled_snapshot" for row in result["declarations"]))

    def test_alpha_renaming_preserves_quantifiers_signs_visibility_and_scope(self) -> None:
        template = exporter.EXPORTER_PATH.read_text(encoding="utf-8")
        source = template + r'''
namespace ResearchCorpusExporter
universe u v
theorem corpusAlpha (α : Type u) (x : α) : x = x := rfl
theorem corpusRenamed (β : Type v) (y : β) : y = y := rfl
theorem corpusUniversal (n : Nat) : n = n := rfl
theorem corpusExistential : ∃ n : Nat, n = n := ⟨0, rfl⟩
theorem corpusPositive (x : Int) (h : x = 0) : x = 0 := h
theorem corpusNegative (x : Int) (h : -x = 0) : -x = 0 := h
theorem corpusLess (x : Nat) (h : x < 0) : x < 0 := h
theorem corpusLessEqual (x : Nat) (h : x ≤ 0) : x ≤ 0 := h
theorem corpusStrict ⦃α : Type⦄ (x : α) : x = x := rfl
theorem corpusImplicit {α : Type} (x : α) : x = x := rfl
theorem corpusDependent {α : Type} [Inhabited α] (x : α) (p : α → Prop) (h : p x) : p x := h
theorem corpusLeft (α : Type) (x y : α) (h : x = y) : x = y := h
theorem corpusRight (α : Type) (x y : α) (h : y = x) : y = x := h
opaque corpusOpaque : Nat := 3
run_meta do
  let names := #[``corpusAlpha, ``corpusRenamed, ``corpusUniversal, ``corpusExistential,
    ``corpusPositive, ``corpusNegative, ``corpusLess, ``corpusLessEqual,
    ``corpusStrict, ``corpusImplicit, ``corpusDependent, ``corpusLeft, ``corpusRight,
    ``corpusOpaque, ``Classical.choice]
  let rows ← names.mapM fun name => inspectDeclaration `CorpusTest Json.null name
  IO.println s!"HGT_CORPUS_TEST:{(toJson rows).compress}"
end ResearchCorpusExporter
'''
        rows = compile_scratch(source, "HGT_CORPUS_TEST:")
        by_name = {row["name"].removeprefix("ResearchCorpusExporter."): row for row in rows}
        def shape(name):
            return by_name[name]["type_shape"]
        self.assertEqual(shape("corpusAlpha"), shape("corpusRenamed"))
        for left, right in (("corpusUniversal", "corpusExistential"),
                            ("corpusPositive", "corpusNegative"), ("corpusLess", "corpusLessEqual"),
                            ("corpusStrict", "corpusImplicit"), ("corpusLeft", "corpusRight")):
            with self.subTest(left=left, right=right):
                self.assertNotEqual(shape(left), shape(right))
        self.assertIn('"Exists"', shape("corpusExistential"))
        self.assertIn('"Neg.neg"', shape("corpusNegative"))
        self.assertIn('"LT.lt"', shape("corpusLess"))
        self.assertIn('"LE.le"', shape("corpusLessEqual"))
        self.assertEqual(json.loads(shape("corpusUniversal"))[0], "forall")
        dependent = by_name["corpusDependent"]
        self.assertEqual([b["binder_info"] for b in dependent["binders"]],
                         ["implicit", "instance_implicit", "explicit", "explicit", "explicit"])
        self.assertEqual(dependent["binders"][-1]["type"], "p x")
        opaque = by_name["corpusOpaque"]
        self.assertEqual(opaque["kind"], "opaque")
        self.assertEqual(opaque["value_status"], "opaque")
        self.assertEqual(opaque["proof_dependencies_status"], "available")
        axiom = by_name["Classical.choice"]
        self.assertEqual(axiom["kind"], "axiom")
        self.assertIsNone(axiom["proof_dependencies"])
        self.assertEqual(axiom["proof_dependencies_status"], "not_applicable")
        self.assertEqual(axiom["axioms"], ["Classical.choice"])

    def test_hidden_theorem_values_are_not_misreported_as_axioms_or_empty_proofs(self) -> None:
        template = exporter.EXPORTER_PATH.read_text(encoding="utf-8")
        # A real module-system import exposes signatures but hides proof bodies.
        source = "module\n" + "\n".join(
            "public meta " + line for line in template.splitlines() if line.startswith("import ")
        ) + "\nimport Mathlib.Logic.Nonempty\nmeta section\n"
        source += template[template.index("/-!"):] + '\n#export_research_corpus ["Mathlib.Logic.Nonempty", "Init"]\n'
        result = compile_scratch(source, exporter.EXPORT_SENTINEL)
        self.assertEqual(result["status"], "ok", result["error"])
        self.assertEqual(result["modules"], ["Mathlib.Logic.Nonempty", "Init"])
        row = next(row for row in result["declarations"] if row["name"] == "Nonempty.map")
        self.assertEqual(row["kind"], "theorem")
        self.assertEqual(row["kernel_kind"], "axiom")
        self.assertEqual(row["value_status"], "unavailable")
        self.assertIsNone(row["proof_dependencies"])
        self.assertEqual(row["proof_dependencies_status"], "unavailable")
        self.assertEqual(row["axioms"], [])
        self.assertEqual(row["axioms_status"], "available")

    def test_missing_cached_module_fails_without_building(self) -> None:
        result = exporter.export_module(FORMAL, "HgtCorpusTestMissingModule")
        self.assertEqual(result["status"], "error")
        self.assertEqual(result["declarations"], [])
        self.assertIn("HgtCorpusTestMissingModule", result["error"])

    @unittest.skipUnless(os.name == "posix", "POSIX process-group cleanup")
    def test_real_timeout_reaps_the_lake_process_group(self) -> None:
        launch = subprocess.Popen
        processes = []

        def record_process(*args, **kwargs):
            process = launch(*args, **kwargs)
            processes.append(process)
            return process

        with mock.patch.object(exporter.subprocess, "Popen", side_effect=record_process):
            result = exporter.export_module(FORMAL, "Init", timeout_seconds=0.001)
        self.assertEqual(result["status"], "timeout", result)
        self.assertEqual(len(processes), 1)
        self.assertIsNotNone(processes[0].returncode)
        with self.assertRaises(ProcessLookupError):
            os.killpg(processes[0].pid, 0)


if __name__ == "__main__":
    unittest.main()
