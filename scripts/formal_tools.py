#!/usr/bin/env python3
"""Local automation for the hgt Lean formal project.

This script is intentionally CI-agnostic.  It gives agents local tools for:

* generating a declaration API index;
* generating a gap/status report;
* linting proof debt and project wiring;
* searching reusable formal infrastructure before reproving it.
"""

from __future__ import annotations

import argparse
import dataclasses
import functools
import json
import os
import re
import sqlite3
import sys
import time
from pathlib import Path

from lean_search_index import (
    DeclHit,
    DeclRow,
    LeanSearchIndex,
    MarkerRow,
    MarkerHit,
    SearchResults,
    SearchIndexUnavailable,
    SourceFile,
    SCHEMA_FINGERPRINT,
    build_match_expression,
    content_parts,
    matches_fields,
    module_matches,
    query_parts,
    select_results,
    split_identifier,
)
# `research_brief` and `subprocess` are imported inside the two commands that
# need them.  Every `research` query pays for this module's imports, and those
# two are a tenth of that startup for code a search never reaches.


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal"
SRC = FORMAL / "GaloisForLFunctions"
API_MD = FORMAL / "LEAN_API.md"
GAPS_MD = FORMAL / "LEAN_GAPS.md"
OVERVIEW_MD = FORMAL / "LEAN_OVERVIEW.md"
# Build a new generation beside the old database. Agents already querying the
# previous generation keep their own SQLite/WAL files during an upgrade.
SEARCH_DB = FORMAL / f".lean_search-{SCHEMA_FINGERPRINT}.db"

DECL_RE = re.compile(r"^\s*(theorem|lemma|def|structure|class|abbrev|inductive)\s+([\w'.]+)")
# `DECL_RE` drives the generated API catalog and must stay as it is; the search
# index uses this wider form instead.  On this corpus the narrow one misses
# 24,260 declarations — every `noncomputable def`, `private theorem`,
# same-line-attributed `@[simp] theorem`, and every named `instance` — which
# made them unfindable and so liable to be proved a second time.
INDEX_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"((?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*)"
    r"(theorem|lemma|def|structure|class|abbrev|inductive|instance|opaque)\s+([\w'.«»]+)"
)
ATTRIBUTE_LINE_RE = re.compile(r"^\s*@\[[^\]]*\]\s*$")
DEBT_RE = re.compile(r"^\s*(sorry|admit)\b|^\s*(axiom|opaque)\s+[A-Za-z_]|^\s*unsafe\s+(def|theorem|axiom)\b")
MARKER_RE = re.compile(r"\b(TODO|FIXME|OPEN|NEXT|Remaining|remaining|blocked|missing)\b")
# Accepts the Lean module-system import forms (`public import`, `meta import`,
# `private import`) alongside the plain one, so the import graph of a
# module-system area is traversable.
IMPORT_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$")
MODULE_NAME_RE = re.compile(
    r"^(?:[A-Za-z_][A-Za-z0-9_']*|«[^«».\s]+»)"
    r"(?:\.(?:[A-Za-z_][A-Za-z0-9_']*|«[^«».\s]+»))*$"
)

THEOREM_AREAS = {
    "rh_tower": {
        "module": "GaloisForLFunctions.RHTower",
        "path": SRC / "RHTower",
        "capstones": ["RHTower.rh_iff_tower", "RHTower.rh_iff_forall_ladder"],
    },
    "ht_geometry": {
        "module": "GaloisForLFunctions.HTGeometry",
        "path": SRC / "HTGeometry",
        "capstones": [
            "hypertranscendental_gamma",
            "HTGeometry.exists_wedgeFacetSewnUpperEndSystem",
        ],
    },
    "hurwitz": {
        "module": "GaloisForLFunctions.Hurwitz",
        "path": SRC / "Hurwitz",
        "capstones": ["hurwitz_n2_unconditional"],
    },
    "u0_pui": {
        "module": "GaloisForLFunctions.U0",
        "path": SRC / "U0",
        "capstones": [
            "U0PhiIndep.u0_phi_independence",
            "U0CardTheorems.u0_phi_independence_all_parameters",
        ],
    },
    "q62_boettcher": {
        "module": "GaloisForLFunctions.Bottcher",
        "path": SRC / "Bottcher",
        "capstones": ["Bottcher.q62_independence", "Bottcher.q62_mixed"],
    },
    "hilbert_metric": {
        "module": "GaloisForLFunctions.HilbertMetric",
        "path": SRC / "HilbertMetric",
        "capstones": [
            "gaussianCorrectedDeterminant_mul_sq_le",
            "gaussianDistanceMatrix_det_mul_sq_le",
        ],
    },
    "selberg_class": {
        "module": "GaloisForLFunctions.SelbergClass",
        "path": SRC / "SelbergClass",
        "capstones": [
            "SelbergClass.differentiable_dampedMultipleStandardTwist",
        ],
    },
    "bi_scale_uncertainty": {
        "module": "GaloisForLFunctions.BiScaleUncertainty",
        "path": SRC / "BiScaleUncertainty",
        "capstones": [
            "GaloisForLFunctions.BiScaleUncertainty.autocorr_krein_increment_sq_le",
            "GaloisForLFunctions.BiScaleUncertainty.autocorr_origin_singularity_leverage_sub",
            "GaloisForLFunctions.BiScaleUncertainty.weilArchRe_nonneg_iff_levy_sinh_ge_abs_gammaBracket",
        ],
    },
    "arithmetic_positivity_theory": {
        "module": "GaloisForLFunctions.ArithmeticPositivityTheory",
        "path": SRC / "arithmetic-positivity-theory",
        "capstones": [
            "GaloisForLFunctions.ArithmeticPositivityTheory.factorialWeightedTail_sq_integral_le",
            "GaloisForLFunctions.ArithmeticPositivityTheory.factorialTailTranslationEnergy_le_min",
            "GaloisForLFunctions.ArithmeticPositivityTheory.factorialTailLogTranslationEnergy_le",
            "GaloisForLFunctions.ArithmeticPositivityTheory.factorialTailLogFourier_integral_le",
            "GaloisForLFunctions.ArithmeticPositivityTheory.factorialCorrected_zeroSquare_le",
            "GaloisForLFunctions.ArithmeticPositivityTheory.exists_factorialTail_raw_and_smoothed_zeroSquare_bound",
            "GaloisForLFunctions.ArithmeticPositivityTheory.exists_factorialSmoothedTail_relative_positive_margin",
        ],
    },
    "bezout_valuation_incidence": {
        "module": "GaloisForLFunctions.BezoutValuationIncidence",
        "path": SRC / "BezoutValuationIncidence",
        "capstones": [
            "GaloisForLFunctions.BezoutValuationIncidence.bezout_valuation_incidence_four_requirement_synthesis",
            "GaloisForLFunctions.BezoutValuationIncidence.bezoutCoprimeQuadraticForm_eq_moebius_diagonal",
            "GaloisForLFunctions.BezoutValuationIncidence.two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero",
            "GaloisForLFunctions.BezoutValuationIncidence.selberg_and_mean_square_le_dirichlet_energy_of_harmonic_eq_zero",
        ],
    },
    "trans_horizon_incidence_mechanics": {
        "module": "GaloisForLFunctions.TransHorizonIncidenceMechanics",
        "path": SRC / "TransHorizonIncidenceMechanics",
        "capstones": [
            "GaloisForLFunctions.TransHorizonIncidenceMechanics.sieveSeq_mul_of_dvd_of_squarefree_support",
            "GaloisForLFunctions.TransHorizonIncidenceMechanics.horizonObservationState_eq_iff_all_sieveSeq",
            "GaloisForLFunctions.TransHorizonIncidenceMechanics.fermiBoundaryJump_exact_recovery_iff",
        ],
    },
    "arithmetic_criticality_theory": {
        "module": "GaloisForLFunctions.ArithmeticCriticalityTheory",
        "path": SRC / "ArithmeticCriticalityTheory",
        "capstones": [
            "GaloisForLFunctions.ArithmeticCriticalityTheory.riemannHypothesis_of_foldedSupersolution",
            "GaloisForLFunctions.ArithmeticCriticalityTheory.nonneg_iff_exists_pos_supersolution",
            "GaloisForLFunctions.ArithmeticCriticalityTheory.twoSidedGenerator_shiftedGroundState_sub_potential",
            "GaloisForLFunctions.ArithmeticCriticalityTheory.foldedGenerator_shiftedGroundState_sub_potential",
        ],
    },
    "square_root_threshold": {
        "module": "GaloisForLFunctions.SquareRootThreshold",
        "path": SRC / "SquareRootThreshold",
        "capstones": [
            "GaloisForLFunctions.SquareRootThreshold.isolatedPairConfig_weil_nonneg_iff",
            "GaloisForLFunctions.SquareRootThreshold.isolatedPairConfig_weil_nonneg_nyquist_iff",
            "GaloisForLFunctions.SquareRootThreshold.re_windowedW_nonneg_of_aperture_nonneg",
            "GaloisForLFunctions.SquareRootThreshold.exists_offLine_lattice_windowed_nonneg",
            "GaloisForLFunctions.SquareRootThreshold.windowedW_eq_integral_heightShift",
            "GaloisForLFunctions.SquareRootThreshold.zetaZeroConfig_re_W_nonneg_of_small_aperture",
            "GaloisForLFunctions.SquareRootThreshold.re_integral_heightShift_zetaZeroConfig_nonneg",
            "GaloisForLFunctions.SquareRootThreshold.exists_zetaZeroConfig_re_W_heightShift_nonneg",
            "GaloisForLFunctions.SquareRootThreshold.integral_normSq_mul_normSq_dirichletSum",
            "GaloisForLFunctions.SquareRootThreshold.integral_windowed_sq_deviation_eq",
            "GaloisForLFunctions.SquareRootThreshold.lintegral_bad_heights_le_of_height",
            "GaloisForLFunctions.SquareRootThreshold.zeta_weil_positive_forces_deep_companion",
            "GaloisForLFunctions.SquareRootThreshold.integral_windowed_sq_deviation_le",
            "GaloisForLFunctions.SquareRootThreshold.integral_pairTransform_mul_integral_windowed_eq",
            "GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_primePolynomial_le_archPart",
            "GaloisForLFunctions.SquareRootThreshold.exists_archPart_zero_lt_primePolynomial",
            "GaloisForLFunctions.SquareRootThreshold.primePolynomial_le_archPart_iff_poleCompression",
        ],
    },
    "arithmetic_incidence_positivity": {
        "module": "GaloisForLFunctions.ArithmeticIncidencePositivity",
        "path": SRC / "ArithmeticIncidencePositivity",
        "capstones": [
            "GaloisForLFunctions.ArithmeticIncidencePositivity.productAtom_le_ratioAtom",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.skeletonEnergy_nonneg",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.archPairKernel_pos_iff",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.crossingThreshold_mem",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.archPairKernel_reflection_pos_iff",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.min_lt_of_archPairKernel_pos",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.archPairKernel_neg_log_log_pos_iff_of_two_le",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.productAtom_lt_of_mem_lagPrimeWindow",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.lintegral_archCrossingDensity_offCollar_le",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.sqrt_sub_one_sq_lt_two_vonMangoldt_iff",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.innerEnds_subset_antiDiagonalCollar",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.antiDiagonalCollar_subset_outer",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.totalLatticeCrossingKernel_pos_iff",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.total_midpoint_inequality_iff",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.totalAntiDiagonalKernel_pos_forall_iff",
            "GaloisForLFunctions.ArithmeticIncidencePositivity.unpaid_level_subset_outer",
        ],
    },
    "signed_arithmetic_energy_incidence": {
        "module": "GaloisForLFunctions.SignedArithmeticEnergyIncidence",
        "path": SRC / "SignedArithmeticEnergyIncidence",
        "capstones": [
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.nonneg_iff_locallyPayable_of_isBalanced",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.localPayment_lossless_iff",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.locallyPayable_iff_comparison_nonneg",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.not_locallyPayable_rankOneCoupling",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.uniformTrain_capacity",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.autoCorr_sineTrain_first",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.grid_joint_capacity_attained",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.polarDefect_nonneg_iff",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.riemannHypothesis_iff_orbit_summable",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.admits_iff_summable_firstColumn",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.not_backward_stable_l2",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.summable_signBlind_iff",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.not_summable_positiveTwin",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.adverse_weakLimit",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.companions_pay",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.switchingEquivalent_iff_triangleHolonomy_eq",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.polarForm_abs_le",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.polarForm_nonneg_iff_polarSolution",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.signBlind_admission_iff",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.cartesian_lower_bound",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.ccmRestrictedWeilForm_adverse_weakLimit",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.few_companions_never_pay",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.abs_log_energy_sub_le",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.isBalanced_iff_alignedCycles",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.frustratedCycle_poincare",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.localPayment_lossless_iff_isBalanced",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.frustratedCycle_nonneg_iff",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.cycleWitness_window",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.evenFold_lossless",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.oddFold_primeTriangle_not_isBalanced",
            "GaloisForLFunctions.SignedArithmeticEnergyIncidence.frustrated_walk_has_primeSum",
        ],
    },
    "arithmetic_castelnuovo_severi": {
        "module": "GaloisForLFunctions.ArithmeticCastelnuovoSeveri",
        "path": SRC / "ArithmeticCastelnuovoSeveri",
        "capstones": [
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface.hodgeIndex_tfae",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.realizable_iff",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.hodgeIndexOnSpan_iff_unitary",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.goldenDatum_spanDefect_neg",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_hidden_on_window",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.witt_integral_not_pure",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.zetaSeries_hasGhost",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.toeplitz_pos_on_window_iff",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface.exists_effectivity_iff_hodgeIndex",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.scalingSurface_hodgeIndex_iff",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_one_positive_square",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.negIndex_weilGram_le_offLineCount",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.pontryagin_law_finite",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.pontryagin_law_of_tempered",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.pontryagin_law",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zeta_hodgeDefect_iff",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_weil_positive_definite",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.heckeIncidence_eq_towerWeight",
            "GaloisForLFunctions.ArithmeticCastelnuovoSeveri.not_exists_polynomial_adjunction_bound",
        ],
    },
    "arithmetic_compensation_theory": {
        "module": "GaloisForLFunctions.ArithmeticCompensationTheory",
        "path": SRC / "ArithmeticCompensationTheory",
        "capstones": [
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_odd_smooth_family_sharp_comb_rate",
            "GaloisForLFunctions.ArithmeticCompensationTheory.tendsto_combEnergy_div_combMass_sq_horizonEnergy",
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_pos_tendsto_combEnergy_div_exp",
            "GaloisForLFunctions.ArithmeticCompensationTheory.norm_add_sq_eq_compensation",
            "GaloisForLFunctions.ArithmeticCompensationTheory.pmCompleteHeadEnergy_eq_compensation",
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_compensationDefect_le_inv_log_pow_six",
            "GaloisForLFunctions.ArithmeticCompensationTheory.summable_compensationDefect_dyadic",
            "GaloisForLFunctions.ArithmeticCompensationTheory.pronicEnergy_shift_le",
            "GaloisForLFunctions.ArithmeticCompensationTheory.admits_dampedMobiusEnergy_iff_shift",
            "GaloisForLFunctions.ArithmeticCompensationTheory.pronicEnergy_shift_le_tail",
            "GaloisForLFunctions.ArithmeticCompensationTheory.forall_admitted_drift_admitted_iff",
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_dampedMobius_drift_le",
            "GaloisForLFunctions.ArithmeticCompensationTheory.admits_or_escapesToHorizon",
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_dampedMobiusEnergy_le",
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_admitted_monotone_not_positivePartContinuation",
            "GaloisForLFunctions.ArithmeticCompensationTheory.tendsto_integral_workCore_logZeta",
            "GaloisForLFunctions.ArithmeticCompensationTheory.not_forall_signedDampingWork_nonneg",
            "GaloisForLFunctions.ArithmeticCompensationTheory.not_relative_step_transport",
            "GaloisForLFunctions.ArithmeticCompensationTheory.adaptedEnergy_dampedMobiusEnergy_iff_admits",
            "GaloisForLFunctions.ArithmeticCompensationTheory.riemannHypothesis_iff_cofinal_adaptedEnergy",
            "GaloisForLFunctions.ArithmeticCompensationTheory.exists_abs_rowBilinear_centredPrimeRow_le_of_range",
        ],
    },
    "quantum_alg": {
        "module": "GaloisForLFunctions.QuantumAlg",
        "path": SRC / "QuantumAlg",
        "capstones": [
            "QuantumAlg.Factoring.ShorStyle.main_factorization",
            "QuantumAlg.Factoring.EkeraHastadStyle.main_factorization",
            "QuantumAlg.GroverSearch.main_success_probability",
            "QuantumAlg.DeutschJozsa.main",
        ],
    },
}

ALLOWED_ROOT_LEAN = {
    "ArithmeticCastelnuovoSeveri.lean",
    "ArithmeticCompensationTheory.lean",
    "ArithmeticContinuationAndCriticalEnergy.lean",
    "ArithmeticCriticalityTheory.lean",
    "ArithmeticIncidencePositivity.lean",
    "ArithmeticPositivityTheory.lean",
    "BezoutValuationIncidence.lean",
    "BiScaleUncertainty.lean",
    "Bottcher.lean",
    "Core.lean",
    "FullyProvenNewTargets.lean",
    "HTGeometry.lean",
    "HilbertMetric.lean",
    "Hurwitz.lean",
    "KummerRootApplications.lean",
    "MainTheorems.lean",
    "PNTPlus.lean",
    "QECLean.lean",
    "QuantumAlg.lean",
    "RHTower.lean",
    "ScaleSignedIncidenceCriticality.lean",
    "SelbergClass.lean",
    "SignedArithmeticEnergyIncidence.lean",
    "SquareRootThreshold.lean",
    "TransHorizonIncidenceMechanics.lean",
    "U0.lean",
}


@dataclasses.dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    module: str
    relpath: str
    line: int
    doc: str


@dataclasses.dataclass(frozen=True)
class Finding:
    kind: str
    relpath: str
    line: int
    text: str
    context: str


def rel(path: Path) -> str:
    """Repo-relative path, falling back to the absolute one for outside files.

    Callers pass this through to cache and index keys, and the reachability
    checker is exercised against throwaway trees outside the repo, so an
    out-of-tree path has to stay addressable rather than raise.
    """
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


@functools.lru_cache(maxsize=None)
def lean_files() -> list[Path]:
    return sorted(SRC.rglob("*.lean"))


def module_name(path: Path, *, formal: Path = FORMAL) -> str:
    """Dotted Lean module name, falling back to the bare stem outside the package.

    A file outside `formal/` has no module name; callers still need a label for
    it rather than an exception.
    """
    try:
        relative = path.relative_to(formal)
    except ValueError:
        return path.stem
    return ".".join(relative.with_suffix("").parts)


def read_lines(path: Path) -> list[str]:
    """Read one enumerated file, tolerating concurrent removal after discovery.

    Research agents share this worktree. A leaf module can disappear between an
    ``rglob`` snapshot and this read; at that point it is no longer part of the
    tree being linted. Required root files are checked explicitly by callers.
    """
    try:
        return path.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        return []


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Strip Lean line and block comments while preserving line numbers.

    Lines carrying no comment delimiter are passed through untouched, and the
    remaining ones are scanned by jumping between delimiters rather than one
    character at a time.  Block comments nest, so the depth carries across
    lines.
    """
    out: list[str] = []
    depth = 0
    for line in lines:
        if depth == 0:
            if "--" not in line and "/-" not in line:
                out.append(line)
                continue
        elif "/-" not in line and "-/" not in line:
            out.append("")
            continue
        kept: list[str] = []
        i = 0
        n = len(line)
        while i < n:
            if depth == 0:
                dash = line.find("--", i)
                open_ = line.find("/-", i)
                if dash == -1 and open_ == -1:
                    kept.append(line[i:])
                    break
                if dash != -1 and (open_ == -1 or dash < open_):
                    kept.append(line[i:dash])
                    break
                kept.append(line[i:open_])
                depth += 1
                i = open_ + 2
            else:
                close = line.find("-/", i)
                open_ = line.find("/-", i)
                if open_ != -1 and (close == -1 or open_ < close):
                    depth += 1
                    i = open_ + 2
                elif close != -1:
                    depth -= 1
                    i = close + 2
                else:
                    break
        out.append("".join(kept))
    return out


@dataclasses.dataclass(frozen=True)
class FileFacts:
    """Everything the reports need from one file, extracted in a single pass."""

    imports: tuple[str, ...]
    decls: tuple[tuple[str, str, int, str], ...]
    debt: tuple[tuple[int, str, str], ...]
    markers: tuple[tuple[int, str], ...]
    lines: int


def extract_facts(path: Path) -> FileFacts:
    """Read one file once and derive its imports, declarations, debt and markers.

    Markers are read from the raw text, the rest from the comment-stripped text.
    A debt line is attributed to the nearest declaration at or above it, which is
    the running declaration of the same left-to-right scan.
    """
    raw = read_lines(path)
    markers = tuple(
        (i + 1, line.strip()) for i, line in enumerate(raw) if MARKER_RE.search(line)
    )
    if path.suffix != ".lean":
        return FileFacts((), (), (), markers, len(raw))

    imports: list[str] = []
    decls: list[tuple[str, str, int, str]] = []
    debt: list[tuple[int, str, str]] = []
    context = ""
    for i, line in enumerate(strip_lean_comments(raw)):
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(
                token.replace("«", "").replace("»", "")
                for token in match.group(1).split()
                if MODULE_NAME_RE.fullmatch(token)
            )
        decl = DECL_RE.match(line)
        if decl:
            context = f"{decl.group(1)} {decl.group(2)}"
            decls.append((decl.group(1), decl.group(2), i + 1, doc_before(raw, i)))
        if DEBT_RE.search(line):
            debt.append((i + 1, raw[i].strip(), context))
    return FileFacts(tuple(imports), tuple(decls), tuple(debt), markers, len(raw))


CACHE_PATH = FORMAL / ".formal_tools_cache.json"
CACHE_VERSION = 2

_facts: dict[Path, FileFacts] = {}
_cache: dict[str, list] | None = None
_cache_dirty = False


def _load_cache() -> dict[str, list]:
    """Load the extraction cache, treating any damage as a cold cache.

    Several agents run these reports concurrently against one worktree, so the
    file on disk may be mid-replacement, truncated, or written by an older
    version of this script.  None of that is worth failing over: the entries are
    derivable from the tree.
    """
    global _cache
    if _cache is not None:
        return _cache
    _cache = {}
    try:
        with CACHE_PATH.open(encoding="utf-8") as handle:
            blob = json.load(handle)
        if blob.get("version") == CACHE_VERSION:
            _cache = blob.get("files", {})
    except (OSError, ValueError, AttributeError):
        _cache = {}
    return _cache


def _sweep_stale_temp_files(keep: Path) -> None:
    """Delete abandoned cache temporaries left by killed runs.

    Only long-dead files are swept, so a slow concurrent writer is never robbed
    of the temporary it is still filling.
    """
    try:
        now = time.time()
        for stale in CACHE_PATH.parent.glob(f"{CACHE_PATH.stem}.*.tmp"):
            if stale == keep:
                continue
            try:
                if now - stale.stat().st_mtime > 3600:
                    stale.unlink()
            except OSError:
                pass
    except OSError:
        pass


def _save_cache() -> None:
    """Replace the cache atomically so a concurrent reader never sees a partial file."""
    if not _cache_dirty or _cache is None:
        return
    tmp = CACHE_PATH.with_suffix(f".{os.getpid()}.tmp")
    try:
        with tmp.open("w", encoding="utf-8") as handle:
            json.dump({"version": CACHE_VERSION, "files": _cache}, handle)
        os.replace(tmp, CACHE_PATH)
    except OSError:
        pass
    finally:
        # `os.replace` consumes the temporary; anything left here is a failed write.
        try:
            tmp.unlink()
        except OSError:
            pass
        _sweep_stale_temp_files(tmp)


def facts_for(path: Path) -> FileFacts:
    """Return the extracted facts for one file, reusing the cache when it is current."""
    cached = _facts.get(path)
    if cached is not None:
        return cached
    try:
        stat = path.stat()
        stamp = [stat.st_size, stat.st_mtime_ns]
    except OSError:
        stamp = None

    key = rel(path)
    disk = _load_cache()
    if stamp is not None:
        entry = disk.get(key)
        if entry is not None and entry[:2] == stamp:
            facts = FileFacts(
                tuple(entry[2]),
                tuple(tuple(d) for d in entry[3]),
                tuple(tuple(d) for d in entry[4]),
                tuple(tuple(d) for d in entry[5]),
                entry[6],
            )
            _facts[path] = facts
            return facts

    facts = extract_facts(path)
    if stamp is not None:
        global _cache_dirty
        disk[key] = [
            stamp[0],
            stamp[1],
            list(facts.imports),
            [list(d) for d in facts.decls],
            [list(d) for d in facts.debt],
            [list(d) for d in facts.markers],
            facts.lines,
        ]
        _cache_dirty = True
    _facts[path] = facts
    return facts


def imported_modules(path: Path) -> set[str]:
    return set(facts_for(path).imports)


def unreachable_owned_modules(
    theorem_areas: dict[str, dict[str, object]] = THEOREM_AREAS,
    *,
    formal: Path = FORMAL,
    src: Path = SRC,
) -> dict[str, list[str]]:
    paths = sorted(src.rglob("*.lean"))
    root_module = formal / f"{src.name}.lean"
    if root_module.exists():
        paths.append(root_module)

    module_paths = {module_name(path, formal=formal): path for path in paths}
    import_graph = {name: imported_modules(path) for name, path in module_paths.items()}
    unreachable: dict[str, list[str]] = {}

    for area_name, info in theorem_areas.items():
        umbrella = str(info["module"])
        if umbrella not in module_paths:
            continue

        reachable: set[str] = set()
        pending = [umbrella]
        while pending:
            current = pending.pop()
            if current in reachable:
                continue
            reachable.add(current)
            pending.extend(
                imported
                for imported in import_graph.get(current, set())
                if imported in module_paths and imported not in reachable
            )

        area_path = Path(info["path"])
        owned = {
            module_name(path, formal=formal) for path in area_path.rglob("*.lean")
        }
        missing = sorted(owned - reachable)
        if missing:
            unreachable[area_name] = missing

    return unreachable


def doc_before(lines: list[str], index: int, *, limit: int | None = 180) -> str:
    """Return the adjacent docstring; limit=None indexes its full contents."""
    j = index - 1
    while j >= 0 and lines[j].strip() == "":
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    block: list[str] = []
    depth = 0
    while j >= 0:
        block.append(lines[j])
        found = False
        for delimiter in reversed(list(re.finditer(r"/-|-/", lines[j]))):
            depth += 1 if delimiter.group() == "-/" else -1
            if depth == 0:
                # A plain/module comment must not capture earlier declarations
                # and unrelated docs when searching backward for '/--'.
                if not lines[j][delimiter.start():].startswith("/--"):
                    return ""
                block[-1] = lines[j][delimiter.start():]
                found = True
                break
        if found:
            break
        j -= 1
    else:
        return ""
    block.reverse()
    text = " ".join(
        line.strip()
        .removeprefix("/--")
        .removesuffix("-/")
        .strip()
        .lstrip("*")
        .strip()
        for line in block
    )
    text = re.sub(r"\s+", " ", text).strip()
    return text[:limit]


def attribute_free_index(lines: list[str], index: int) -> int:
    """Step back over attribute-only lines so the docstring above them is found.

    `/-- doc -/` then `@[simp]` then `theorem foo` is common, and looking only
    at the line directly above the declaration would find the attribute.
    """
    while index > 0 and ATTRIBUTE_LINE_RE.match(lines[index - 1]):
        index -= 1
    return index


@functools.lru_cache(maxsize=None)
def declarations() -> list[Declaration]:
    out: list[Declaration] = []
    for path in lean_files():
        mod = module_name(path)
        relpath = rel(path)
        for kind, name, line, doc in facts_for(path).decls:
            out.append(
                Declaration(kind=kind, name=name, module=mod, relpath=relpath, line=line, doc=doc)
            )
    return out


@functools.lru_cache(maxsize=None)
def proof_debt() -> list[Finding]:
    out: list[Finding] = []
    for path in lean_files():
        relpath = rel(path)
        for line, text, context in facts_for(path).debt:
            out.append(Finding("proof-debt", relpath, line, text, context))
    return out


@functools.lru_cache(maxsize=None)
def marker_findings(limit: int = 250, *, include_status_logs: bool = False) -> list[Finding]:
    paths = sorted(list(SRC.rglob("*.lean")) + list(SRC.rglob("*.md")) + [FORMAL / "README.md"])
    out: list[Finding] = []
    for path in paths:
        if not path.exists():
            continue
        if path.name == "STATUS.md" and not include_status_logs:
            continue
        for line, text in facts_for(path).markers:
            out.append(Finding("marker", rel(path), line, text, ""))
            if len(out) >= limit:
                return out
    return out


@functools.lru_cache(maxsize=None)
def file_sizes(*, include_status_logs: bool = False) -> list[tuple[int, str]]:
    sizes: list[tuple[int, str]] = []
    for path in sorted(list(SRC.rglob("*.lean")) + list(SRC.rglob("*.md"))):
        if path.name == "STATUS.md" and not include_status_logs:
            continue
        sizes.append((facts_for(path).lines, rel(path)))
    return sorted(sizes, reverse=True)


def area_lean_files(path: Path) -> list[Path]:
    if path.is_dir():
        return sorted(path.rglob("*.lean"))
    if path.with_suffix(".lean").exists():
        return [path.with_suffix(".lean")]
    return []


def split_declarations_by_area(
    decls: list[Declaration] | None = None,
) -> tuple[dict[str, list[Declaration]], list[Declaration]]:
    by_area: dict[str, list[Declaration]] = {key: [] for key in THEOREM_AREAS}
    other: list[Declaration] = []
    for d in decls or declarations():
        placed = False
        for key, info in THEOREM_AREAS.items():
            area_path = rel(info["path"])
            if d.relpath.startswith(area_path + "/") or d.relpath == area_path + ".lean":
                by_area[key].append(d)
                placed = True
                break
        if not placed:
            other.append(d)
    return by_area, other


def api_markdown() -> str:
    decls = declarations()
    by_area, other = split_declarations_by_area(decls)

    lines = [
        "# Lean API Index",
        "",
        "Generated by `scripts/formal_tools.py index` from the current Lean tree.",
        "Use this before proving a lemma; search by declaration name, module, or docstring.",
        "",
        "## Theorem Areas",
        "",
        "| Area | Umbrella | Declarations | Capstones |",
        "|---|---|---:|---|",
    ]
    for key, info in THEOREM_AREAS.items():
        lines.append(
            f"| `{key}` | `{info['module']}` | {len(by_area[key])} | "
            f"{', '.join(f'`{x}`' for x in info['capstones'])} |"
        )
    lines.extend(["", "## Declarations", ""])

    def emit_group(title: str, group: list[Declaration]) -> None:
        lines.extend([f"### {title}", "", "| Kind | Name | Module | Location | Doc |", "|---|---|---|---|---|"])
        for d in sorted(group, key=lambda item: (item.module, item.line, item.name)):
            lines.append(f"| {d.kind} | `{d.name}` | `{d.module}` | `{d.relpath}:{d.line}` | {d.doc} |")
        lines.append("")

    for key in THEOREM_AREAS:
        emit_group(key, by_area[key])
    emit_group("shared and bridge infrastructure", other)
    return "\n".join(lines).rstrip() + "\n"


def overview_markdown() -> str:
    decls = declarations()
    by_area, other = split_declarations_by_area(decls)
    debt = proof_debt()
    root_imports = (FORMAL / "GaloisForLFunctions.lean").read_text(encoding="utf-8")
    root_wired = "yes" if "import GaloisForLFunctions.MainTheorems" in root_imports else "no"
    lines = [
        "# Lean Formal Overview",
        "",
        "Generated by `scripts/formal_tools.py index` from the current Lean tree.",
        "Use this as the quick map before opening large proof files.",
        "",
        "## Theorem Areas",
        "",
        "| Area | Umbrella | Lean modules | Declarations | Capstones |",
        "|---|---|---:|---:|---|",
    ]
    for key, info in THEOREM_AREAS.items():
        module_count = len(area_lean_files(info["path"]))
        lines.append(
            f"| `{key}` | `{info['module']}` | {module_count} | {len(by_area[key])} | "
            f"{', '.join(f'`{x}`' for x in info['capstones'])} |"
        )
    lines.extend(
        [
            "",
            "## Wiring",
            "",
            f"- Root imports `GaloisForLFunctions.MainTheorems`: **{root_wired}**.",
            f"- Package-level declarations outside the five theorem areas: **{len(other)}**.",
            f"- Active proof-debt findings: **{len(debt)}**.",
            "",
            "## Local Commands",
            "",
            "| Command | Purpose |",
            "|---|---|",
            "| `../scripts/formal_tools.py status` | Print theorem-area counts, proof debt, and largest files. |",
            "| `../scripts/formal_tools.py research \"<query>\"` | Search generated declarations and gap markers before proving a lemma. |",
            "| `../scripts/formal_tools.py index` | Regenerate this overview plus API and gap reports. |",
            "| `../scripts/formal_tools.py lint --check-generated` | Check proof debt, project wiring, file sizes, and generated-file freshness. |",
            "| `../scripts/formal_tools.py lint --check-generated --build --build-target GaloisForLFunctions.MainTheorems` | Run the local full formal gate. |",
            "",
            "## Largest Lean Files",
            "",
            "| Lines | File |",
            "|---:|---|",
        ]
    )
    emitted = 0
    for count, path in file_sizes():
        if path.endswith(".lean") and count >= 500:
            lines.append(f"| {count} | `{path}` |")
            emitted += 1
        if emitted >= 12:
            break
    return "\n".join(lines).rstrip() + "\n"


def gaps_markdown() -> str:
    debt = proof_debt()
    sizes = file_sizes()
    markers = marker_findings()
    lines = [
        "# Lean Gap and Order Report",
        "",
        "Generated by `scripts/formal_tools.py index` from local files.",
        "This is an agent worklist aid, not a mathematical ledger.",
        "",
        "## Proof Debt",
        "",
    ]
    if debt:
        lines.extend(["| Kind | Location | Context | Text |", "|---|---|---|---|"])
        for f in debt:
            lines.append(f"| {f.kind} | `{f.relpath}:{f.line}` | `{f.context}` | `{f.text}` |")
    else:
        lines.append("No active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declarations found.")

    lines.extend(
        [
            "",
            "## Large Files",
            "",
            "| Lines | File |",
            "|---:|---|",
        ]
    )
    for count, path in sizes[:25]:
        if count >= 500:
            lines.append(f"| {count} | `{path}` |")

    lines.extend(
        [
            "",
            "## Gap Markers",
            "",
            "| Location | Text |",
            "|---|---|",
        ]
    )
    for f in markers:
        lines.append(f"| `{f.relpath}:{f.line}` | {f.text} |")
    lines.extend(
        [
            "",
            "## Historical Status Logs",
            "",
            "`STATUS.md` progress logs are intentionally excluded from the default gap-marker table.",
            "Use `scripts/formal_tools.py research \"<query>\"` when you need to search those logs.",
            "",
            "| Lines | File |",
            "|---:|---|",
        ]
    )
    for path in sorted(SRC.rglob("STATUS.md")):
        lines.append(f"| {len(read_lines(path))} | `{rel(path)}` |")
    return "\n".join(lines).rstrip() + "\n"


def write_indexes(_: argparse.Namespace | None = None) -> int:
    API_MD.write_text(api_markdown(), encoding="utf-8")
    GAPS_MD.write_text(gaps_markdown(), encoding="utf-8")
    OVERVIEW_MD.write_text(overview_markdown(), encoding="utf-8")
    print(f"wrote {rel(API_MD)}")
    print(f"wrote {rel(GAPS_MD)}")
    print(f"wrote {rel(OVERVIEW_MD)}")
    try:
        _, stats = refresh_search_index()
    except SearchIndexUnavailable as error:
        print(f"skipped search index: {error}", file=sys.stderr)
    else:
        print(f"refreshed {rel(SEARCH_DB)} ({stats.changed} changed, {stats.removed} removed)")
    return 0


def check_generated() -> list[str]:
    errors: list[str] = []
    expected = {API_MD: api_markdown(), GAPS_MD: gaps_markdown(), OVERVIEW_MD: overview_markdown()}
    for path, content in expected.items():
        if not path.exists():
            errors.append(f"missing generated file: {rel(path)}")
        elif path.read_text(encoding="utf-8") != content:
            errors.append(f"stale generated file: {rel(path)}")
    return errors


def run_lake_build(target: str | None) -> tuple[int, str]:
    import subprocess

    cmd = ["lake", "build"]
    if target:
        cmd.append(target if target.startswith("+") else f"+{target}")
    result = subprocess.run(cmd, cwd=FORMAL, text=True, capture_output=True)
    if result.stdout:
        print(result.stdout, end="")
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    return result.returncode, result.stdout + result.stderr


HEARTBEAT_CEILING = 800_000
HEARTBEAT_BASELINE = FORMAL / "heartbeat-baseline.txt"
_HEARTBEAT_RE = re.compile(r"^\s*set_option\s+(maxHeartbeats|synthInstance\.maxHeartbeats)\s+(\d+)", re.M)


def heartbeat_maxima(*, src: Path = SRC) -> dict[str, int]:
    """Highest heartbeat budget each Lean file asks for, keyed by repo-relative path."""
    found: dict[str, int] = {}
    for path in sorted(src.rglob("*.lean")):
        values = [int(m.group(2)) for m in _HEARTBEAT_RE.finditer(path.read_text(encoding="utf-8"))]
        if values:
            found[rel(path)] = max(values)
    return found


def read_heartbeat_baseline() -> dict[str, int]:
    if not HEARTBEAT_BASELINE.exists():
        return {}
    baseline: dict[str, int] = {}
    for line in HEARTBEAT_BASELINE.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        value, _, name = line.partition(" ")
        baseline[name.strip()] = int(value)
    return baseline


def write_heartbeat_baseline(maxima: dict[str, int]) -> None:
    lines = [
        "# Grandfathered heartbeat budgets: <max-heartbeats> <path>.",
        f"# The lint ceiling is {HEARTBEAT_CEILING}. Entries here may only shrink -- lowering a",
        "# number is always accepted and re-recorded; raising one, or adding a new file above the",
        "# ceiling, fails the lint. Delete a line once its file is at or below the ceiling.",
    ]
    lines += [f"{value} {name}" for name, value in sorted(maxima.items(), key=lambda kv: (-kv[1], kv[0]))]
    HEARTBEAT_BASELINE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def heartbeat_errors() -> list[str]:
    """Ratchet: no new file may exceed the ceiling, and no file may raise its recorded budget."""
    maxima = heartbeat_maxima()
    baseline = read_heartbeat_baseline()
    errors: list[str] = []
    for name, value in sorted(maxima.items()):
        if value <= HEARTBEAT_CEILING:
            continue
        allowed = baseline.get(name)
        if allowed is None:
            errors.append(
                f"heartbeat budget {value} exceeds the {HEARTBEAT_CEILING} ceiling: {name}; "
                "optimize the proof instead of raising the budget"
            )
        elif value > allowed:
            errors.append(
                f"heartbeat budget raised from {allowed} to {value}: {name}; "
                "the grandfathered baseline may only shrink"
            )
    return errors


def lint(args: argparse.Namespace) -> int:
    errors: list[str] = []
    warnings: list[str] = []

    for name, info in THEOREM_AREAS.items():
        module_path = FORMAL / Path(*info["module"].split(".")).with_suffix(".lean")
        if not module_path.exists():
            errors.append(f"missing theorem-area umbrella for {name}: {rel(module_path)}")

    for name, modules in unreachable_owned_modules().items():
        umbrella = THEOREM_AREAS[name]["module"]
        for module in modules:
            errors.append(
                f"owned module unreachable from theorem-area umbrella {umbrella}: {module}"
            )

    root_imports = (FORMAL / "GaloisForLFunctions.lean").read_text(encoding="utf-8")
    if "import GaloisForLFunctions.MainTheorems" not in root_imports:
        errors.append("root module does not import GaloisForLFunctions.MainTheorems")

    unexpected_root_modules = sorted(
        path.name for path in SRC.glob("*.lean") if path.name not in ALLOWED_ROOT_LEAN
    )
    for name in unexpected_root_modules:
        errors.append(
            f"research leaf module at package root: {name}; move it into an owned theorem area"
        )

    formal_claude = FORMAL / "CLAUDE.md"
    formal_agents = FORMAL / "AGENTS.md"
    if not formal_claude.exists():
        errors.append(f"missing formal agent instructions: {rel(formal_claude)}")
    if not formal_agents.exists():
        errors.append(f"missing formal agent instructions: {rel(formal_agents)}")
    if formal_claude.exists() and formal_agents.exists():
        if formal_claude.read_text(encoding="utf-8") != formal_agents.read_text(encoding="utf-8"):
            errors.append("formal/CLAUDE.md and formal/AGENTS.md have drifted")

    errors.extend(heartbeat_errors())

    for f in proof_debt():
        errors.append(f"proof debt: {f.relpath}:{f.line}: {f.text} ({f.context})")

    for count, path in file_sizes():
        if path.endswith(".lean") and count > args.max_lines:
            warnings.append(f"large Lean file: {path} has {count} lines")

    if args.check_generated:
        errors.extend(check_generated())

    if args.build:
        build_code, build_output = run_lake_build(args.build_target)
        if build_code != 0:
            errors.append(f"lake build failed with exit code {build_code}")
        build_warnings = [line for line in build_output.splitlines() if line.startswith("warning:")]
        if build_warnings and not args.allow_build_warnings:
            errors.append(
                f"lake build emitted {len(build_warnings)} warnings "
                "(fix them or pass --allow-build-warnings)"
            )

    for msg in warnings:
        print(f"warning: {msg}", file=sys.stderr)
    for msg in errors:
        print(f"error: {msg}", file=sys.stderr)

    if errors:
        return 1
    print("formal lint passed")
    return 0


def status(_: argparse.Namespace) -> int:
    print("Theorem areas:")
    for key, info in THEOREM_AREAS.items():
        module_count = len(area_lean_files(info["path"]))
        print(f"- {key}: {info['module']} ({module_count} Lean modules)")
        print(f"  capstones: {', '.join(info['capstones'])}")
    print()
    debt = proof_debt()
    print(f"Proof debt findings: {len(debt)}")
    for f in debt:
        print(f"- {f.relpath}:{f.line}: {f.text}")
    print()
    print("Largest files:")
    for count, path in file_sizes()[:10]:
        print(f"- {count:5d} {path}")
    status_logs = sorted(SRC.rglob("STATUS.md"))
    if status_logs:
        print()
        print("Historical status logs:")
        for path in status_logs:
            print(f"- {len(read_lines(path)):5d} {rel(path)}")
    return 0


SEARCH_SUFFIXES = (".lean", ".md")


def search_sources() -> list[SourceFile]:
    """Every file the search index covers: Lean sources plus in-tree prose.

    Hand-rolled over `os.scandir` rather than `Path.rglob`, because this runs on
    every single query: two rglob passes over ~18.7k files, an `exists()` per
    hit and a later `stat()` per hit cost around 300 ms, where one walk that
    stats as it goes costs a fraction of that.
    """
    prefix = len(str(ROOT)) + 1
    out: list[SourceFile] = []
    stack = [str(SRC)]
    while stack:
        try:
            entries = list(os.scandir(stack.pop()))
        except OSError:
            continue
        for entry in entries:
            if entry.is_dir(follow_symlinks=False):
                stack.append(entry.path)
            elif entry.name.endswith(SEARCH_SUFFIXES):
                try:
                    stat = entry.stat()
                except OSError:
                    continue
                out.append(
                    SourceFile(entry.path[prefix:], entry.path, stat.st_size, stat.st_mtime_ns)
                )
    readme = FORMAL / "README.md"
    try:
        stat = readme.stat()
    except OSError:
        return out
    out.append(SourceFile(rel(readme), str(readme), stat.st_size, stat.st_mtime_ns))
    return out


def index_rows(source: SourceFile) -> tuple[list[DeclRow], list[MarkerRow]]:
    """Extract one file's searchable declarations and gap markers.

    This scans the file itself instead of reusing `facts_for`, for two reasons.
    It sees the ~10% of declarations that `DECL_RE` cannot (`INDEX_DECL_RE`
    below), and it keeps the search path off the JSON extraction cache, which a
    query would otherwise load and rewrite in full to record a handful of
    changed files.
    """
    path = Path(source.abspath)
    raw = read_lines(path)
    markers = [
        MarkerRow(line=i + 1, text=line.strip())
        for i, line in enumerate(raw)
        if MARKER_RE.search(line)
    ]
    if path.suffix != ".lean":
        return [], markers

    module = module_name(path)
    decls: list[DeclRow] = []
    for i, line in enumerate(strip_lean_comments(raw)):
        match = INDEX_DECL_RE.match(line)
        if not match:
            continue
        modifiers = " ".join(match.group(1).split())
        kind = f"{modifiers} {match.group(2)}".strip()
        decls.append(
            DeclRow(
                name=match.group(3),
                kind=kind,
                module=module,
                line=i + 1,
                doc=doc_before(raw, attribute_free_index(raw, i), limit=None),
            )
        )
    return decls, markers


def refresh_search_index(*, rebuild: bool = False) -> tuple[LeanSearchIndex, object]:
    index = LeanSearchIndex(SEARCH_DB)
    sources = search_sources()
    stats = index.rebuild(sources, index_rows) if rebuild else index.refresh(sources, index_rows)
    return index, stats


def research_options(args: argparse.Namespace) -> dict:
    return {
        "any_terms": getattr(args, "any_terms", False),
        "exact": getattr(args, "exact", False),
        "per_module": getattr(args, "per_module", 2),
        "offset": getattr(args, "offset", 0),
        "explore": getattr(args, "explore", 5),
        "module": getattr(args, "module", ""),
        "exclude_modules": getattr(args, "exclude_module", []),
        "scope": getattr(args, "scope", "ours"),
    }


def render_search(args: argparse.Namespace, result: SearchResults,
                  markers: list[MarkerHit], *, backend: str = "fts5") -> None:
    query = " ".join(args.query).strip()
    options = research_options(args)
    expression = build_match_expression(query, any_terms=options["any_terms"], exact=options["exact"])
    extra = {}
    lexical = getattr(args, "mode", "lexical") == "lexical"
    # Mathlib is only in the discovery corpus, so a lexical Mathlib search runs
    # discovery keyword-only instead of returning nothing.
    if not lexical or options['scope'] != 'ours':
        from lean_research_cli import discovery
        extra = discovery(ROOT, args, {**options, 'lexical_only': True} if lexical else options)
    if getattr(args, "json", False):
        print(json.dumps({"query": query, "match": expression, "backend": backend,
                          "options": options, **dataclasses.asdict(result),
                          "markers": [dataclasses.asdict(m) for m in markers], **extra}, ensure_ascii=False))
        return
    mode = "OR (any term/phrase)" if options["any_terms"] else "AND (every term/phrase)"
    scopes = {'ours': 'this project only', 'mathlib': 'installed Mathlib only (lexical)',
              'all': 'this project and Mathlib'}
    print(f"Query: {mode}; {'exact tokens' if options['exact'] else 'prefix expansion'}; {backend}")
    print(f"Scope: {scopes.get(options['scope'], options['scope'])}")

    def show(hit: DeclHit) -> None:
        print(f"- {hit.name} ({hit.kind}) {hit.module} {hit.relpath}:{hit.line}")
        if hit.doc:
            print(f"  {hit.doc[:240]}{'…' if len(hit.doc) > 240 else ''}")

    if options['scope'] == 'mathlib':
        print("Mathlib hits are listed under Candidate lemmas.")
    else:
        print(f"Matches: {result.total} declarations in {result.modules} modules; "
              f"{result.eligible} after module cap ({options['per_module'] or 'off'}).")
        print(f"Declarations (offset {options['offset']}, showing {len(result.declarations)}):")
        for hit in result.declarations:
            show(hit)
    if result.exploration:
        print("\nExplore other modules (same query; favors less represented filename families):")
        for hit in result.exploration:
            show(hit)
    if markers:
        print("\nGap markers (text mentions, not verified open obligations):")
        for hit in markers:
            print(f"- {hit.relpath}:{hit.line}: {hit.text}")
    if options["offset"] + len(result.declarations) < result.eligible:
        print(f"\nMore: --offset {options['offset'] + len(result.declarations)}; "
              "--module <substring> to focus; --per-module 0 to show all matches per module.")
    if not result.total and options['scope'] != 'mathlib':
        if extra.get('candidate_lemmas'):
            print("No declaration matches every keyword; see Candidate lemmas below.")
        else:
            print("No declarations matched. Try fewer terms, --any, alternate names, or describe the goal in words.")
    if extra:
        from lean_research_cli import render_discovery
        render_discovery(extra, query)


def research(args: argparse.Namespace) -> int:
    args.research_started = time.monotonic()
    if not getattr(args, "mode", None):
        from lean_research_cli import default_mode
        args.mode = default_mode(ROOT)
    query = " ".join(args.query).strip()
    try:
        if not build_match_expression(query):
            raise ValueError("provide a search query containing words or an identifier")
        options = research_options(args)
        if min(args.limit, options["per_module"], options["offset"], options["explore"]) < 0:
            raise ValueError("search limits and offset must be nonnegative")
        import math
        if not math.isfinite(args.budget_seconds) or args.budget_seconds <= 0:
            raise ValueError("search budget must be a finite positive number")
    except ValueError as error:
        print(str(error), file=sys.stderr)
        return 2

    if not getattr(args, "scan", False):
        index = LeanSearchIndex(SEARCH_DB)
        try:
            if not getattr(args, "no_refresh", False):
                stats = index.refresh(search_sources(), index_rows)
                if stats.stale:
                    print(
                        f"note: index refresh skipped ({stats.reason.strip() or 'locked'});"
                        " searching the last committed index",
                        file=sys.stderr,
                    )
            if getattr(args, "no_refresh", False) and not index.counts()["files"]:
                print("index is empty or requires rebuilding; rerun without --no-refresh", file=sys.stderr)
                return 2
            if options['scope'] == 'mathlib':
                # This index holds only our project; Mathlib hits come from discovery.
                result, marker_hits = SearchResults([], [], 0, 0, 0), []
            else:
                result = index.search(query, limit=args.limit,
                                      **{k: v for k, v in options.items() if k != 'scope'})
                marker_hits = index.search_markers(
                    query, args.limit, **{k: options[k] for k in
                    ("any_terms", "exact", "module", "exclude_modules")}
                )
        except (SearchIndexUnavailable, sqlite3.DatabaseError) as error:
            print(f"search index unavailable ({error}); scanning instead", file=sys.stderr)
        else:
            render_search(args, result, marker_hits)
            return 0
        finally:
            index.close()

    return research_scan(args)


def research_scan(args: argparse.Namespace) -> int:
    """Index-free fallback, using the same extractor, query grammar and diversity."""
    query = " ".join(args.query).strip()
    options = research_options(args)
    parts = content_parts(query_parts(query))
    match_options = {k: options[k] for k in ("any_terms", "exact")}
    hits: list[DeclHit] = []
    markers: list[MarkerHit] = []
    for source in search_sources():
        # Match paths first to avoid reading entire excluded subtrees.
        path_module = source.relpath.replace("/", ".")
        if not module_matches(path_module, options["module"], options["exclude_modules"]):
            continue
        decls, gap_rows = index_rows(source)
        for d in decls:
            if not module_matches(d.module, options["module"], options["exclude_modules"]):
                continue
            name_fields = [d.name, split_identifier(d.name)]
            fields = [*name_fields, d.doc, d.module, d.kind, split_identifier(d.module)]
            if matches_fields(parts, fields, **match_options):
                score = -sum(3 if matches_fields([p], name_fields, **match_options) else 1
                             for p in parts if matches_fields([p], fields, **match_options))
                if query.lower() == d.name.lower():
                    score -= 400
                if query.lower() in d.name.lower():
                    score -= 120
                hits.append(DeclHit(d.name, d.kind, d.module, source.relpath, d.line, d.doc, score))
        for m in gap_rows:
            fields = [m.text, split_identifier(source.relpath)]
            if matches_fields(parts, fields, **match_options):
                score = -sum(matches_fields([p], fields, **match_options) for p in parts)
                markers.append(MarkerHit(source.relpath, m.line, m.text, score))
    result = select_results(hits, limit=args.limit, **{k: options[k] for k in
                            ("per_module", "offset", "explore")})
    markers.sort(key=lambda m: (m.score, m.relpath, m.line))
    render_search(args, result, markers[:args.limit], backend="scan (approximate ranking)")
    return 0


def search_index_cmd(args: argparse.Namespace) -> int:
    if any(getattr(args, name, False) for name in ("corpus", "compiler", "methods", "vectors", "compact")):
        from lean_research_cli import corpus_index
        return corpus_index(ROOT, args)
    try:
        index, stats = refresh_search_index(rebuild=args.rebuild)
    except SearchIndexUnavailable as error:
        print(f"search index unavailable: {error}", file=sys.stderr)
        return 1
    counts = index.counts()
    size = sum(
        Path(str(SEARCH_DB) + suffix).stat().st_size
        for suffix in ("", "-wal", "-shm")
        if Path(str(SEARCH_DB) + suffix).exists()
    )
    print(f"{rel(SEARCH_DB)}: {size / 1e6:.1f} MB")
    print(
        f"indexed {counts['files']} files, {counts['declarations']} declarations,"
        f" {counts['markers']} gap markers"
    )
    print(f"refreshed {stats.changed} changed, {stats.removed} removed")
    if stats.stale:
        print(f"note: refresh incomplete ({stats.reason.strip() or 'locked'})", file=sys.stderr)
    return 0


def brief(args: argparse.Namespace) -> int:
    from research_brief import (
        build_research_brief,
        canonical_area,
        render_research_brief,
        render_research_brief_json,
    )

    try:
        canonical_area(args.area)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 2

    declaration_index = declarations() if args.refresh else ()
    try:
        try:
            result = build_research_brief(
                root=ROOT,
                area=args.area,
                graph_path=args.graph,
                declarations=declaration_index,
                limit=args.limit,
                refresh=args.refresh,
            )
        except ValueError as error:
            if args.graph is not None or "received no corpus theorem" not in str(error):
                raise
            result = build_research_brief(
                root=ROOT,
                area=args.area,
                declarations=declarations(),
                limit=args.limit,
                refresh=True,
            )
    except ValueError as error:
        print(error, file=sys.stderr)
        return 2
    rendered = (
        render_research_brief_json(result)
        if args.format == "json"
        else render_research_brief(result)
    )
    print(rendered, end="")
    return 0


def frontier_reports(args: argparse.Namespace) -> int:
    from research_brief import build_frontier_chains, canonical_area, write_chain_reports

    try:
        canonical_area(args.area)
    except ValueError as error:
        print(error, file=sys.stderr)
        return 2

    declaration_index = declarations() if args.refresh else ()
    try:
        try:
            result = build_frontier_chains(
                root=ROOT,
                area=args.area,
                graph_path=args.graph,
                declarations=declaration_index,
                max_gaps=args.max_gaps,
                refresh=args.refresh,
            )
        except ValueError as error:
            if args.graph is not None or "received no corpus theorem" not in str(error):
                raise
            result = build_frontier_chains(
                root=ROOT,
                area=args.area,
                declarations=declarations(),
                max_gaps=args.max_gaps,
                refresh=True,
            )
    except ValueError as error:
        print(error, file=sys.stderr)
        return 2

    output_dir = args.output if args.output.is_absolute() else ROOT / args.output
    paths = write_chain_reports(result, output_dir, limit=args.limit)
    print(f"Wrote {len(paths) - 1} chain reports plus index to {output_dir}")
    return 0


def research_setup_cmd(args: argparse.Namespace) -> int:
    from lean_research_corpus import cache_directory
    from lean_research_setup import main as setup_main
    flags = ["--cache-dir", str(cache_directory(ROOT))]
    flags.extend("--" + name for name in ("status", "verify", "smoke") if getattr(args, name, False))
    return setup_main(flags)


def research_release_cmd(args: argparse.Namespace) -> int:
    from lean_research_cli import release
    try:
        result = release(ROOT, args.report)
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result['accepted'] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser(
        "index",
        help="generate formal/LEAN_OVERVIEW.md, formal/LEAN_API.md, and formal/LEAN_GAPS.md",
    ).set_defaults(func=write_indexes)

    lint_parser = sub.add_parser("lint", help="run local formal-project lint checks")
    lint_parser.add_argument("--max-lines", type=int, default=1500)
    lint_parser.add_argument("--check-generated", action="store_true")
    lint_parser.add_argument("--build", action="store_true", help="also run lake build")
    lint_parser.add_argument("--build-target", default="GaloisForLFunctions.MainTheorems")
    lint_parser.add_argument("--allow-build-warnings", action="store_true")
    lint_parser.set_defaults(func=lint)

    sub.add_parser("status", help="print theorem-area and proof-debt summary").set_defaults(func=status)

    research_parser = sub.add_parser(
        "research", help="search Lean declarations: spaces mean AND; --any means OR",
        description='Require every term/phrase by default; --any matches alternatives. '
                    'Shell quotes group arguments; inner double quotes require a phrase.',
    )
    research_parser.add_argument("query", nargs="+", help='words, identifier, or inner-quoted phrase')
    research_parser.add_argument("--limit", type=int, default=20)
    research_parser.add_argument("--mode", choices=("deep", "hybrid", "lexical"), default=None,
                                 help="deep after acceptance; lexical preserves exact name/doc search")
    research_parser.add_argument("--budget-seconds", type=float, default=300,
                                 help="whole-request search budget (default: 300 seconds)")
    research_parser.add_argument("--retrieval-views", choices=("statements", "all"), default="all",
                                 help="statement-only retrieval ablation or full proof-method discovery")
    research_parser.add_argument("--max-rounds", type=int, choices=(1, 2, 3), default=3,
                                 help="deep retrieval rounds; use 1 for the single-round evaluation control")
    research_parser.add_argument("--any", dest="any_terms", action="store_true", help="match any term/phrase (OR)")
    research_parser.add_argument("--exact", action="store_true", help="disable automatic token prefixes")
    research_parser.add_argument("--per-module", type=int, default=2, help="declarations per module before paging; 0 disables cap")
    research_parser.add_argument("--explore", type=int, default=5, help="append this many other matching modules; 0 disables")
    research_parser.add_argument("--offset", type=int, default=0, help="page through results after module cap")
    research_parser.add_argument("--module", default="", help="literal substring of dotted module name")
    research_parser.add_argument("--exclude-module", action="append", default=[], help="exclude module substring; repeatable")
    research_parser.add_argument("--scope", choices=("ours", "mathlib", "all"), default="ours",
                                 help="ours: this project's Lean and research notes (default). "
                                      "mathlib: installed Mathlib only, lexical results. "
                                      "all: both. Only our corpus has semantic vectors.")
    research_parser.add_argument("--json", action="store_true", help="structured hits, match counts, query interpretation")
    research_parser.add_argument(
        "--no-refresh",
        action="store_true",
        help="search the index as-is instead of syncing changed files first",
    )
    research_parser.add_argument(
        "--scan",
        action="store_true",
        help="bypass the search index and scan the declaration list directly",
    )
    research_parser.set_defaults(func=research)

    search_index_parser = sub.add_parser(
        "search-index",
        help="refresh and report on the full-text search index used by `research`",
    )
    search_index_parser.add_argument(
        "--rebuild", action="store_true", help="discard and rebuild the index from scratch"
    )
    search_index_parser.set_defaults(func=search_index_cmd)
    search_index_parser.add_argument("--corpus", action="store_true", help="refresh all Lean/dependency/prose sources")
    search_index_parser.add_argument("--compiler", action="store_true", help="extract signatures from available fresh compiled modules")
    search_index_parser.add_argument("--methods", action="store_true", help="resume local proof-method descriptions")
    search_index_parser.add_argument("--vectors", action="store_true", help="resume local embeddings and FAISS publication")
    search_index_parser.add_argument("--compact", action="store_true", help="combine small vector shards")
    search_index_parser.add_argument("--module", default="", help="limit compiler extraction to module substring")
    search_index_parser.add_argument("--budget-seconds", type=float, default=120,
                                     help="bounded resumable indexing work budget")

    setup_parser = sub.add_parser("research-setup", help="install pinned local search runtime and model weights")
    setup_parser.add_argument("--status", action="store_true", help="read installation status without downloads")
    setup_parser.add_argument("--verify", action="store_true", help="verify downloaded model hashes")
    setup_parser.add_argument("--smoke", action="store_true", help="exercise actual local inference")
    setup_parser.set_defaults(func=research_setup_cmd)

    release_parser = sub.add_parser('research-release', help='activate deep default only after retrieval acceptance gates pass')
    release_parser.add_argument('--report', type=Path, required=True)
    release_parser.set_defaults(func=research_release_cmd)

    indexer_parser = sub.add_parser('research-indexer', help='control progressive local background enrichment')
    indexer_parser.add_argument('action', choices=('start', 'status', 'stop'))
    def research_indexer_cmd(args):
        from lean_research_background import command
        return command(ROOT, args.action)
    indexer_parser.set_defaults(func=research_indexer_cmd)

    brief_parser = sub.add_parser(
        "brief",
        help="compute Lean-native minimal open cuts to a research target",
    )
    brief_parser.add_argument("--area", required=True)
    brief_parser.add_argument("--limit", type=int, default=3)
    brief_parser.add_argument("--format", choices=("markdown", "json"), default="markdown")
    brief_parser.add_argument("--graph", type=Path, help="read an existing Lean graph export")
    brief_parser.add_argument(
        "--refresh",
        action="store_true",
        help="rebuild compiled Lean graph even when cache is current",
    )
    brief_parser.set_defaults(func=brief)

    reports_parser = sub.add_parser(
        "frontier-reports",
        help="write least-gap Lean frontier chain reports",
    )
    reports_parser.add_argument("--area", required=True)
    reports_parser.add_argument("--max-gaps", type=int, default=4)
    reports_parser.add_argument("--limit", type=int, default=20)
    reports_parser.add_argument("--output", type=Path, default=Path("docs/reports"))
    reports_parser.add_argument("--graph", type=Path, help="read an existing Lean graph export")
    reports_parser.add_argument(
        "--refresh",
        action="store_true",
        help="refresh from compiled corpus snapshot without building source files",
    )
    reports_parser.set_defaults(func=frontier_reports)

    args = parser.parse_args(argv)
    try:
        return args.func(args)
    finally:
        _save_cache()


if __name__ == "__main__":
    raise SystemExit(main())
