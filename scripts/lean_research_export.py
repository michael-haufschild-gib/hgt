"""Export declarations from existing Lean v4.32.2 oleans, without building modules.

``export_module(formal_dir, module, timeout_seconds=60, source_path=None)`` and
``export_modules(formal_dir, modules, timeout_seconds=60, source_paths=None)`` run one
synchronous ``lake env lean /tmp/...lean`` subprocess. The scratch file imports
the requested module and the tooling template, never the project umbrella.
There is no compiler-data simulation, build, or persistent cache. Snapshot
validation runs before import and checks for file changes again after export.
``snapshots`` maps modules to artifact/source fingerprints and freshness evidence;
the single-module wrapper also supplies ``snapshot``. Every exported row carries
``compiler_snapshot_status='compiled_snapshot'`` independently of export success.

``validate_compiled_snapshot(formal_dir, module, source_path=None)`` reads existing
files only. SHA-256 fingerprints identify bytes, not which source built an olean.
Newer source/import artifacts and concurrent changes produce ``freshness=stale``.
Otherwise freshness is ``unavailable``: this implementation deliberately never
issues ``current`` without verifying Lake's complete build-input provenance.
Lake trace hashes are recorded as unverified evidence, not treated as SHA-256.
Transitive staleness checks cover existing setup.json importArts; absent/incomplete
setup metadata is explicit. Source-path candidates are confirmed by the compiler
after export. Configuration written in Lean is never executed by the validator.
``artifact_hash`` covers the main olean; ``artifact_set_hash`` also covers private,
server, and IR parts, whose independent changes can affect exported metadata.
Races invalidate artifact identities and set ``snapshot_stable=False``. Source
hashes identify the pre-export source; they never certify the compiled artifact.

Results always include ``declarations``, ``status``, ``error``, and ``toolchain``.
Statuses are ``ok``, ``partial`` (declaration inspection errors), ``error``,
``timeout``, or ``unavailable`` (missing executable/files). ``toolchain`` is the
compiler-reported toolchain, or None when no valid payload was received.

Declarations belong to the exact requested module, not its transitive imports.
Import-only modules can legitimately return no declarations. Private/generated
names are retained. ``kind`` records Lean's original kind (lemmas are theorems,
abbreviations are definitions); ``kernel_kind`` records the imported representation.
``type_shape`` is a JSON-encoded structural expression, format lean-expr-json-v1.
It alpha-renames binders/universe parameters without reducing expressions.
``binders`` includes every outer forall binder, in order, with contextual types.
``type_dependencies`` and ``proof_dependencies`` are direct Expr constants;
``axioms`` is Lean's transitive axiom audit. Value dependencies also cover defs.
Missing/non-applicable values have null dependencies and explicit status fields;
an empty available list is never substituted for missing metadata. Opaque values
are marked even when their bodies can be inspected. No proof validity claim is
inferred from these fields, including for unsafe/partial definitions.
``source`` holds a resolved path and optional compiler declaration/selection
ranges: one-based lines, zero-based columns, exclusive ends, plus UTF-16 columns.
Ranges describe the compiled snapshot and may differ from edited source files.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import signal
import subprocess
import tempfile
from pathlib import Path
from typing import Any
from research_runtime.processes import cancellation_signals


EXPORT_SENTINEL = "HGT_CORPUS_JSON:"
TOOLCHAIN = "leanprover/lean4:v4.32.2"
EXPORTER_PATH = Path(__file__).resolve().parent / "lean" / "export_research_corpus.lean"


def _file_state(path: Path) -> tuple | None:
    try:
        stat = path.stat()
        return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)
    except OSError:
        return None


def _fingerprint(path: Path, *, content: bool = True) -> dict:
    """Identify a stable read; ctime/inode catch writes that preserve size/mtime."""
    result = {"path": str(path), "hash": None, "mtime_ns": None, "state": None,
              "status": "unavailable", "error": None}
    try:
        before = _file_state(path)
        if before is None or not path.is_file():
            return result
        digest = None
        if content:
            sha = hashlib.sha256()
            with path.open("rb") as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    sha.update(block)
            digest = sha.hexdigest()
        after = _file_state(path)
        result.update(hash=digest, mtime_ns=before[3], state=before,
                      status="available" if before == after else "changed")
    except OSError as error:
        result["error"] = str(error)
    return result


class _SnapshotValidator:
    """Per-call filesystem inventory and observations shared by a small batch."""

    def __init__(self, formal_dir: Path):
        self.formal = Path(formal_dir).resolve()
        self.files: dict[Path, dict] = {}
        self.resolutions: dict[tuple[str, Path | None], dict] = {}
        self.scopes: dict[str, set[Path]] = {}
        self.roots: list[tuple[Path, list[Path], Path | None]] = []
        packages = [self.formal]
        manifest = self.formal / "lake-manifest.json"
        self.configs = [manifest, self.formal / "lean-toolchain"]
        try:
            data = json.loads(manifest.read_text(encoding="utf-8"))
            package_dir = self.formal / data.get("packagesDir", ".lake/packages")
            for item in data.get("packages", []):
                if item.get("type") == "path":
                    package = self.formal / item["dir"]
                else:
                    package = package_dir / item["name"]
                packages.append(package / (item.get("subDir") or ""))
        except (OSError, ValueError, TypeError, KeyError, AttributeError):
            packages.extend(sorted((self.formal / ".lake/packages").glob("*")))
        for package in dict.fromkeys(path.resolve() for path in packages):
            config = package / "lakefile.toml"
            self.configs.extend([config, package / "lakefile.lean"])
            try:
                text = config.read_text(encoding="utf-8")
            except OSError:
                text = ""
            # Discovery of literal TOML paths only; existing files and the later
            # compiler mapping decide whether a candidate is usable.
            sources = [package] + [package / value for value in re.findall(
                r'^\s*srcDir\s*=\s*"([^"\n]+)"', text, re.MULTILINE)]
            builds = [package / ".lake/build"] + [package / value for value in re.findall(
                r'^\s*buildDir\s*=\s*"([^"\n]+)"', text, re.MULTILINE)]
            for build in dict.fromkeys(builds):
                self.roots.append((build / "lib/lean", sources, build / "ir"))
        # No elan invocation/install: this is only a candidate. The compiler's
        # actual resolved artifact path is checked after the foreground call.
        elan = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
        toolchain_dir = elan / "toolchains" / TOOLCHAIN.replace("/", "--").replace(":", "---")
        self.roots.append((toolchain_dir / "lib/lean", [toolchain_dir / "src/lean"], None))
        self.roots = list(dict.fromkeys((a, tuple(b), c) for a, b, c in self.roots))

    def observe(self, path: Path, scope: set[Path], *, content: bool = True) -> dict:
        path = path.absolute()
        scope.add(path)
        if path not in self.files:
            self.files[path] = _fingerprint(path, content=content)
        elif content and self.files[path]["hash"] is None and self.files[path]["status"] == "available":
            previous = self.files[path]
            self.files[path] = _fingerprint(path, content=True)
            if previous["state"] != self.files[path]["state"]:
                self.files[path]["status"] = "changed"
        return self.files[path]

    def resolve(self, module: str, source_path: Path | None = None) -> dict:
        key = (module, source_path)
        if key in self.resolutions:
            return self.resolutions[key]
        relative = Path(*module.split("."))
        candidates = {}
        source_candidates = set()
        for artifacts, sources, ir in self.roots:
            artifact = artifacts / relative.with_suffix(".olean")
            for source_root in sources:
                candidate = source_root / relative.with_suffix(".lean")
                if candidate.is_file():
                    source_candidates.add(candidate.resolve())
            if artifact.is_file():
                candidates[artifact.resolve()] = (sources, ir)
        if source_path is not None:
            source = Path(source_path)
            source = (source if source.is_absolute() else self.formal / source).absolute()
        else:
            source = next(iter(source_candidates)) if len(source_candidates) == 1 else None
        artifact = next(iter(candidates)) if len(candidates) == 1 else None
        ir = candidates[artifact][1] if artifact else None
        result = {"artifact": artifact, "source": source,
                  "setup": ir / relative.with_suffix(".setup.json") if ir else None,
                  "candidates": [str(path) for path in sorted(candidates)]}
        self.resolutions[key] = result
        return result

    def validate(self, module: str, source_path: Path | None = None) -> dict:
        scope: set[Path] = set()
        self.scopes[module] = scope
        result = {"module": module, "artifact_path": None, "artifact_hash": None,
                  "artifact_mtime": None, "artifact_mtime_ns": None, "source_path": None,
                  "source_hash": None, "source_mtime_ns": None, "freshness": "unavailable",
                  "compiler_snapshot_status": "unavailable", "provenance_verified": False,
                  "transitive_status": "unavailable", "dependencies": [], "evidence": [],
                  "hash_algorithm": "sha256", "trace": None,
                  "artifact_parts": [], "artifact_set_hash": None, "snapshot_stable": False}
        try:
            _quoted_module(module)
            for config in self.configs:
                self.observe(config, scope)
            requested = (self.formal / "lean-toolchain").read_text(encoding="utf-8").strip()
            result["requested_toolchain"] = requested
            if requested != TOOLCHAIN:
                result["evidence"].append({"reason": "unsupported_toolchain", "required": TOOLCHAIN})
                return result
            resolved = self.resolve(module, source_path)
            artifact, source = resolved["artifact"], resolved["source"]
            if source is not None:
                info = self.observe(source, scope)
                result.update(source_path=str(source), source_hash=info["hash"],
                              source_mtime_ns=info["mtime_ns"])
            if artifact is None:
                result["evidence"].append({"reason": "artifact_missing_or_ambiguous",
                                           "candidates": resolved["candidates"]})
                return result
            info = self.observe(artifact, scope)
            result.update(artifact_path=str(artifact), artifact_hash=info["hash"],
                          artifact_mtime_ns=info["mtime_ns"],
                          artifact_mtime=info["mtime_ns"] / 1e9 if info["mtime_ns"] is not None else None,
                          compiler_snapshot_status="compiled_snapshot" if info["status"] == "available" else "unavailable")
            parts = [info]
            for extension in ("server", "private", "ir"):
                part = artifact.with_suffix(".ir") if extension == "ir" else Path(f"{artifact}.{extension}")
                parts.append(self.observe(part, scope))
            result["artifact_parts"] = [{key: part[key] for key in ("path", "hash", "mtime_ns", "status")}
                                        for part in parts]
            result["artifact_set_hash"] = hashlib.sha256(json.dumps(
                [(part["path"], part["hash"], part["status"]) for part in parts],
                separators=(",", ":")).encode()).hexdigest()
            trace_path = artifact.with_suffix(".trace")
            trace_state = self.observe(trace_path, scope)
            if trace_state["status"] == "available":
                try:
                    trace = json.loads(trace_path.read_text(encoding="utf-8"))
                    inputs = trace.get("inputs", [])
                    recorded = next((entry[1] for entry in inputs
                                     if isinstance(entry, list) and len(entry) == 2
                                     and source is not None and entry[0] == str(source)), None)
                    result["trace"] = {"path": str(trace_path), "hash": trace_state["hash"],
                                       "dep_hash": trace.get("depHash"), "source_hash": recorded,
                                       "status": "input_hashes_unverified" if inputs else "aggregate_only"}
                except (OSError, ValueError, TypeError, AttributeError):
                    result["evidence"].append({"reason": "trace_unreadable", "path": str(trace_path)})
            if result["source_mtime_ns"] is None:
                result["evidence"].append({"reason": "source_unavailable"})
            elif info["mtime_ns"] is not None and result["source_mtime_ns"] > info["mtime_ns"]:
                result["freshness"] = "stale"
                result["evidence"].append({"reason": "source_newer_than_artifact", "path": str(source)})
            setup_path = resolved["setup"]
            if setup_path is not None and self.observe(setup_path, scope)["status"] == "available":
                try:
                    setup = json.loads(setup_path.read_text(encoding="utf-8"))
                    imports = setup["importArts"]
                    if not isinstance(imports, dict) or setup.get("name") != module:
                        raise ValueError("setup module/importArts mismatch")
                    result["transitive_status"] = "checked_for_staleness"
                    for dependency, recorded_paths in sorted(imports.items()):
                        _quoted_module(dependency)
                        dep = self.resolve(dependency)
                        dep_source = self.observe(dep["source"], scope) if dep["source"] else None
                        dep_artifact = self.observe(dep["artifact"], scope, content=False) if dep["artifact"] else None
                        row = {"module": dependency, "artifact_path": str(dep["artifact"]) if dep["artifact"] else None,
                               "source_path": str(dep["source"]) if dep["source"] else None,
                               "source_hash": dep_source["hash"] if dep_source else None,
                               "freshness": "unavailable", "reasons": []}
                        if not dep_artifact or not dep_source or dep_source["status"] != "available":
                            result["transitive_status"] = "partial"
                            row["reasons"].append("dependency_source_or_artifact_unavailable")
                        elif dep_source["mtime_ns"] > dep_artifact["mtime_ns"]:
                            row["freshness"] = "stale"
                            row["reasons"].append("dependency_source_newer_than_artifact")
                        if not isinstance(recorded_paths, list) or not all(isinstance(p, str) for p in recorded_paths):
                            raise ValueError("invalid setup artifact paths")
                        for recorded_path in recorded_paths:
                            path = Path(recorded_path)
                            if not path.is_absolute():
                                path = self.formal / path
                            recorded_info = self.observe(path, scope, content=False)
                            if recorded_info["status"] != "available":
                                row["freshness"] = "stale"
                                row["reasons"].append("recorded_import_artifact_unavailable")
                            elif info["mtime_ns"] is not None and recorded_info["mtime_ns"] > info["mtime_ns"]:
                                row["freshness"] = "stale"
                                row["reasons"].append("import_artifact_newer_than_parent")
                        result["dependencies"].append(row)
                        if row["freshness"] == "stale":
                            result["freshness"] = "stale"
                    # setup files are evidence of the old graph, not proof that
                    # the current source still imports exactly that graph.
                except (OSError, ValueError, TypeError, KeyError, AttributeError) as error:
                    result["transitive_status"] = "partial"
                    result["evidence"].append({"reason": "setup_unreadable", "error": str(error)})
            result["evidence"].append({"reason": "complete_build_provenance_not_verified"})
        except (OSError, ValueError, TypeError) as error:
            result["evidence"].append({"reason": "validation_unavailable", "error": str(error)})
        return result

    def recheck(self, snapshots: dict[str, dict]) -> None:
        changed = {path for path, info in self.files.items()
                   if info["status"] == "changed" or _file_state(path) != info["state"]}
        for module, snapshot in snapshots.items():
            affected = changed.intersection(self.scopes.get(module, set()))
            snapshot["snapshot_stable"] = not affected
            if affected:
                snapshot["freshness"] = "stale"
                if any(Path(part["path"]) in affected for part in snapshot["artifact_parts"]):
                    snapshot["artifact_set_hash_before"] = snapshot["artifact_set_hash"]
                    snapshot["artifact_set_hash"] = None
                if snapshot["artifact_path"] and Path(snapshot["artifact_path"]) in affected:
                    snapshot["artifact_hash_before"] = snapshot["artifact_hash"]
                    snapshot["artifact_hash"] = None
                snapshot["evidence"].append({"reason": "files_changed_during_validation_or_export",
                                             "paths": sorted(str(path) for path in affected)})


def validate_compiled_snapshot(formal_dir: Path, module: str, source_path: Path | None = None) -> dict:
    """Read-only snapshot evidence; never certify source-current from mtime/hash alone.

    Standalone calls recheck their observed files before returning. Export calls
    share the same validator across modules and recheck after Lean has exited.
    Relative source paths are resolved against formal_dir; absolute paths are
    recommended when integrating a repository-wide source inventory.
    """
    validator = _SnapshotValidator(formal_dir)
    result = validator.validate(module, source_path)
    validator.recheck({module: result})
    return result


def _quoted_module(module: str) -> str:
    """Quote every component so keywords cannot inject import modifiers/commands.

    Accept unquoted dot-separated module names, including Unicode. File separators,
    control characters, whitespace and Lean identifier delimiters are rejected.
    """
    if not isinstance(module, str) or not module:
        raise ValueError("module must be a nonempty dot-separated Lean module name")
    if module == "GaloisForLFunctions":
        raise ValueError("the GaloisForLFunctions root umbrella must never be imported")
    parts = module.split(".")
    if any(
        not part or any(
            char.isspace() or ord(char) < 32 or ord(char) == 127 or char in '/\\«»"'
            for char in part
        )
        for part in parts
    ):
        raise ValueError("module must be an unquoted dot-separated name without path separators")
    return ".".join(f"«{part}»" for part in parts)


def _stop_process(process: subprocess.Popen[str]) -> tuple[str, str]:
    """Kill only this invocation's process group, then reap the foreground child."""
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        else:
            process.kill()
    except ProcessLookupError:
        pass
    return process.communicate()


def _diagnostics(stdout: str, stderr: str) -> str:
    # Avoid embedding an entire corpus in a diagnostic after a compiler error.
    lines = [line for line in stdout.splitlines() if not line.startswith(EXPORT_SENTINEL)]
    return "\n".join([stderr.strip(), *lines]).strip()[-12000:]


def _parse_payload(stdout: str, modules: str | list[str]) -> dict[str, Any]:
    modules = [modules] if isinstance(modules, str) else modules
    payloads = [line[len(EXPORT_SENTINEL):] for line in stdout.splitlines()
                if line.startswith(EXPORT_SENTINEL)]
    if len(payloads) != 1:
        raise ValueError(f"expected one Lean corpus payload, received {len(payloads)}")
    payload = json.loads(payloads[0])
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise ValueError("unsupported Lean corpus schema_version")
    if payload.get("modules") != modules:
        raise ValueError("Lean corpus payload module does not match request")
    if payload.get("status") not in {"ok", "partial"}:
        raise ValueError("invalid Lean corpus status")
    if "error" not in payload or not isinstance(payload.get("toolchain"), str):
        raise ValueError("Lean corpus payload is missing error/toolchain metadata")
    if "module_artifacts" in payload:
        reports = payload["module_artifacts"]
        if not isinstance(reports, list) or not all(isinstance(row, dict) for row in reports):
            raise ValueError("invalid compiler module artifact metadata")
        if [row.get("module") for row in reports] != modules:
            raise ValueError("compiler module artifact metadata does not match request")
        for row in reports:
            if any(row.get(f"{kind}_path") is not None and not isinstance(row[f"{kind}_path"], str)
                   for kind in ("source", "artifact")):
                raise ValueError("invalid compiler artifact/source path")
            imports = row.get("direct_imports")
            if imports is not None and (not isinstance(imports, list) or not all(isinstance(n, str) for n in imports)):
                raise ValueError("invalid compiler import metadata")
    rows = payload.get("declarations")
    if not isinstance(rows, list):
        raise ValueError("Lean corpus declarations must be a list")
    seen: set[str] = set()
    for row in rows:
        if not isinstance(row, dict) or row.get("module") not in modules:
            raise ValueError("Lean corpus declaration has incorrect owning module")
        name = row.get("name")
        if not isinstance(name, str) or not name or name in seen:
            raise ValueError("Lean corpus declaration has missing/duplicate name")
        seen.add(name)
        for field in ("kind", "type_text", "type_shape", "binders", "type_dependencies",
                      "proof_dependencies", "axioms", "value_status", "source", "status", "error"):
            if field not in row:
                raise ValueError(f"Lean corpus declaration {name} is missing {field}")
        if row["status"] not in {"ok", "error"}:
            raise ValueError(f"Lean corpus declaration {name} has invalid status")
        if row["status"] == "error" and payload["status"] != "partial":
            raise ValueError("Lean corpus failed declaration reported as complete")
        for field in ("proof_dependencies", "axioms"):
            state = row.get(f"{field}_status")
            if state not in {"available", "unavailable", "not_applicable"}:
                raise ValueError(f"Lean corpus declaration {name} lacks {field} availability")
            if state == "available":
                if not isinstance(row[field], list) or not all(isinstance(n, str) for n in row[field]):
                    raise ValueError(f"Lean corpus declaration {name} has invalid {field}")
            elif row[field] is not None:
                raise ValueError(f"Lean corpus declaration {name} fabricates unavailable {field}")
    return payload


def export_module(formal_dir: Path, module: str, *, timeout_seconds=60, source_path: Path | None = None) -> dict:
    """Compatible single-module wrapper with optional source mapping and snapshot."""
    source_paths = {module: source_path} if source_path is not None and isinstance(module, str) else None
    result = export_modules(formal_dir, [module], timeout_seconds=timeout_seconds, source_paths=source_paths)
    result["module"] = module
    result["snapshot"] = result["snapshots"].get(module) if isinstance(module, str) else None
    return result


def _attach_snapshot_metadata(result: dict) -> None:
    reports = result.get("module_artifacts", [])
    reports = {row["module"]: row for row in reports if isinstance(row, dict) and "module" in row}
    for module, snapshot in result["snapshots"].items():
        report = reports.get(module, {})
        snapshot["artifact_path_matches_compiler"] = False
        snapshot["source_path_matches_compiler"] = False
        for key in ("artifact", "source"):
            reported = report.get(f"{key}_path")
            candidate = snapshot[f"{key}_path"]
            if reported and candidate and Path(reported).resolve() == Path(candidate).resolve():
                snapshot[f"{key}_path_matches_compiler"] = True
            elif reported:
                snapshot["evidence"].append({"reason": f"{key}_mapping_changed_or_unresolved",
                                             "candidate": candidate, "compiler_path": reported})
                snapshot[f"{key}_path"] = reported
                snapshot[f"{key}_hash"] = None
                snapshot[f"{key}_mtime_ns"] = None
                if key == "artifact":
                    snapshot["artifact_mtime"] = None
                    snapshot["artifact_set_hash"] = None
                    snapshot["artifact_parts"] = []
                if candidate is not None:
                    snapshot["snapshot_stable"] = False
                    snapshot["freshness"] = "stale"
            else:
                snapshot["evidence"].append({"reason": f"compiler_{key}_mapping_unavailable"})
        snapshot["direct_imports"] = report.get("direct_imports")
        snapshot["compiler_snapshot_status"] = "compiled_snapshot"
    result["compiler_snapshot_status"] = "compiled_snapshot"
    result["freshness"] = "stale" if any(s["freshness"] == "stale" for s in result["snapshots"].values()) else "unavailable"
    for row in result["declarations"]:
        row["compiler_snapshot_status"] = "compiled_snapshot"
        row["freshness"] = result["snapshots"][row["module"]]["freshness"]


@cancellation_signals()
def export_modules(formal_dir: Path, modules: list[str], *, timeout_seconds=60,
                   source_paths: dict[str, Path] | None = None) -> dict:
    """Export a small group in one foreground Lean call; never build imports.

    Duplicate modules are coalesced in input order. Any import failure fails the
    batch (no partial compiler process output is trusted); per-declaration errors
    still return ``partial``. Snapshot freshness is separate from compiler status.
    """
    result: dict[str, Any] = {
        "schema_version": 1, "modules": modules, "declarations": [], "snapshots": {},
        "status": "error", "error": None, "toolchain": None,
        "compiler_snapshot_status": "unavailable", "freshness": "unavailable",
    }
    validator = None
    try:
        if not isinstance(modules, list) or not modules:
            raise ValueError("modules must be a nonempty list of Lean module names")
        for module in modules:
            _quoted_module(module)
        modules = list(dict.fromkeys(modules))
        result["modules"] = modules
        if isinstance(timeout_seconds, bool) or not math.isfinite(timeout_seconds) or timeout_seconds <= 0:
            raise ValueError("timeout_seconds must be a positive finite number")
        source_paths = {} if source_paths is None else source_paths
        if not isinstance(source_paths, dict) or set(source_paths) - set(modules):
            raise ValueError("source_paths must map requested modules to source paths")
        formal_dir = Path(formal_dir).resolve(strict=True)
        if not formal_dir.is_dir():
            raise ValueError("formal_dir must be a directory")
        requested_toolchain = (formal_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
        result["requested_toolchain"] = requested_toolchain
        if requested_toolchain != TOOLCHAIN:
            raise ValueError(f"exporter requires {TOOLCHAIN}, project requests {requested_toolchain!r}")
        validator = _SnapshotValidator(formal_dir)
        result["snapshots"] = {module: validator.validate(module, source_paths.get(module)) for module in modules}
        template = EXPORTER_PATH.read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory(prefix="hgt-corpus-") as temporary:
            scratch = Path(temporary) / "ExportResearchCorpus.lean"
            scratch.write_text(
                "".join(f"import {_quoted_module(module)}\n" for module in modules) + template
                + f"\n#export_research_corpus {json.dumps(modules, ensure_ascii=False)}\n",
                encoding="utf-8",
            )
            process = subprocess.Popen(
                ["lake", "env", "lean", str(scratch)], cwd=formal_dir,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, encoding="utf-8", errors="replace",
                start_new_session=(os.name == "posix"),
            )
            try:
                stdout, stderr = process.communicate(timeout=timeout_seconds)
            except subprocess.TimeoutExpired:
                stdout, stderr = _stop_process(process)
                result["status"] = "timeout"
                result["error"] = f"Lean corpus export exceeded {timeout_seconds} seconds"
                if detail := _diagnostics(stdout, stderr):
                    result["error"] += f":\n{detail}"
                return result
            except BaseException:
                _stop_process(process)
                raise
        if process.returncode:
            raise ValueError(f"Lean corpus export failed (exit {process.returncode}):\n"
                             + (_diagnostics(stdout, stderr) or "no compiler diagnostics"))
        payload = _parse_payload(stdout, modules)
        result["toolchain"] = payload["toolchain"]
        if payload["toolchain"] != TOOLCHAIN:
            raise ValueError(f"compiler reported unsupported toolchain {payload['toolchain']!r}")
        result.update(payload)
        if detail := _diagnostics(stdout, stderr):
            result["diagnostics"] = detail
    except FileNotFoundError as error:
        result["status"] = "unavailable"
        result["error"] = str(error)
    except (OSError, ValueError, TypeError) as error:
        result["error"] = str(error)
    finally:
        if validator is not None:
            validator.recheck(result["snapshots"])
            result["freshness"] = "stale" if any(s["freshness"] == "stale" for s in result["snapshots"].values()) else "unavailable"
    if result["status"] in {"ok", "partial"}:
        _attach_snapshot_metadata(result)
    return result
