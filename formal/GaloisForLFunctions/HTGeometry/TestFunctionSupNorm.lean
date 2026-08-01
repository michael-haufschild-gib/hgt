import GaloisForLFunctions.HTGeometry.SmoothUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Smooth functions supported in a fixed compact set, and their derivative sup-norms

The test space of the trace-distribution argument is the smooth functions with support inside one
fixed compact set, topologised by the suprema of their iterated derivatives.  This module builds
that space as a module and its derivative sup-norms with the three seminorm properties.

Every iterated derivative of such a function is continuous with compact support, hence bounded,
so the suprema are genuine real numbers.

* `deningerTestSpace J` : the module of smooth functions with `tsupport ⊆ J`.
* `deningerTestSupNorm` : the sup-norm of the `m`-th derivative, with
  `deningerTestSupNorm_add_le` and `deningerTestSupNorm_smul`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section TestSpace

/-- Smooth functions on the line with support inside a fixed set. -/
def deningerTestSpace (J : Set ℝ) : Submodule ℝ (ℝ → ℂ) where
  carrier := {phi | ContDiff ℝ (⊤ : ℕ∞) phi ∧ tsupport phi ⊆ J}
  zero_mem' := by
    refine ⟨contDiff_const, ?_⟩
    rw [tsupport, Function.support_zero, closure_empty]
    exact empty_subset J
  add_mem' := by
    rintro phi psi ⟨hphi, hsphi⟩ ⟨hpsi, hspsi⟩
    refine ⟨hphi.add hpsi, ?_⟩
    have hsub : Function.support (phi + psi) ⊆ Function.support phi ∪ Function.support psi :=
      Function.support_add phi psi
    have hcl : closure (Function.support (phi + psi))
        ⊆ closure (Function.support phi) ∪ closure (Function.support psi) := by
      refine le_trans (closure_mono hsub) ?_
      rw [closure_union]
    exact le_trans hcl (union_subset hsphi hspsi)
  smul_mem' := by
    rintro a phi ⟨hphi, hsphi⟩
    refine ⟨hphi.const_smul a, ?_⟩
    refine le_trans (closure_mono (Function.support_const_smul_subset a phi)) hsphi

theorem mem_deningerTestSpace {J : Set ℝ} {phi : ℝ → ℂ} :
    phi ∈ deningerTestSpace J ↔ ContDiff ℝ (⊤ : ℕ∞) phi ∧ tsupport phi ⊆ J :=
  Iff.rfl

variable {J : Set ℝ}

theorem contDiff_of_mem_deningerTestSpace {phi : ℝ → ℂ} (h : phi ∈ deningerTestSpace J) :
    ContDiff ℝ (⊤ : ℕ∞) phi := h.1

/-- A test function has compact support when the ambient set is compact. -/
theorem hasCompactSupport_of_mem (hJ : IsCompact J) {phi : ℝ → ℂ}
    (h : phi ∈ deningerTestSpace J) : HasCompactSupport phi :=
  hJ.of_isClosed_subset isClosed_closure h.2

/-- Every iterated derivative of a test function has compact support. -/
theorem hasCompactSupport_iteratedDeriv (hJ : IsCompact J) {phi : ℝ → ℂ}
    (h : phi ∈ deningerTestSpace J) (m : ℕ) :
    HasCompactSupport (iteratedDeriv m phi) := by
  induction m with
  | zero =>
      rw [iteratedDeriv_zero]
      exact hasCompactSupport_of_mem hJ h
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- Every iterated derivative of a test function is continuous. -/
theorem continuous_iteratedDeriv_of_mem {phi : ℝ → ℂ} (h : phi ∈ deningerTestSpace J) (m : ℕ) :
    Continuous (iteratedDeriv m phi) :=
  h.1.continuous_iteratedDeriv m (by exact_mod_cast le_top)

/-- The norms of an iterated derivative of a test function are bounded. -/
theorem bddAbove_norm_iteratedDeriv (hJ : IsCompact J) {phi : ℝ → ℂ}
    (h : phi ∈ deningerTestSpace J) (m : ℕ) :
    BddAbove (Set.range fun t => ‖iteratedDeriv m phi t‖) := by
  refine Continuous.bddAbove_range_of_hasCompactSupport
    ((continuous_iteratedDeriv_of_mem h m).norm) ?_
  exact (hasCompactSupport_iteratedDeriv hJ h m).norm

end TestSpace

section SupNorm

variable {J : Set ℝ}

/-- The supremum of the `m`-th derivative of a test function. -/
noncomputable def deningerTestSupNorm (m : ℕ) (phi : ℝ → ℂ) : ℝ :=
  sSup (Set.range fun t => ‖iteratedDeriv m phi t‖)

theorem deningerTestSupNorm_nonneg (hJ : IsCompact J) {phi : ℝ → ℂ}
    (h : phi ∈ deningerTestSpace J) (m : ℕ) : 0 ≤ deningerTestSupNorm m phi := by
  refine le_csSup_of_le (bddAbove_norm_iteratedDeriv hJ h m) (Set.mem_range_self 0) ?_
  exact norm_nonneg _

theorem norm_iteratedDeriv_le_supNorm (hJ : IsCompact J) {phi : ℝ → ℂ}
    (h : phi ∈ deningerTestSpace J) (m : ℕ) (t : ℝ) :
    ‖iteratedDeriv m phi t‖ ≤ deningerTestSupNorm m phi :=
  le_csSup (bddAbove_norm_iteratedDeriv hJ h m) (Set.mem_range_self t)

theorem deningerTestSupNorm_le {phi : ℝ → ℂ} (m : ℕ) {c : ℝ}
    (hc : ∀ t, ‖iteratedDeriv m phi t‖ ≤ c) : deningerTestSupNorm m phi ≤ c := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨t, rfl⟩
  exact hc t

/-- **Subadditivity of the derivative sup-norms.** -/
theorem deningerTestSupNorm_add_le (hJ : IsCompact J) {phi psi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) (hpsi : psi ∈ deningerTestSpace J) (m : ℕ) :
    deningerTestSupNorm m (phi + psi)
      ≤ deningerTestSupNorm m phi + deningerTestSupNorm m psi := by
  refine deningerTestSupNorm_le m fun t => ?_
  have hderiv : iteratedDeriv m (phi + psi) t
      = iteratedDeriv m phi t + iteratedDeriv m psi t := by
    refine iteratedDeriv_add ?_ ?_
    · exact (hphi.1.of_le (by exact_mod_cast le_top)).contDiffAt
    · exact (hpsi.1.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [hderiv]
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add (norm_iteratedDeriv_le_supNorm hJ hphi m t)
    (norm_iteratedDeriv_le_supNorm hJ hpsi m t)

/-- **Absolute homogeneity of the derivative sup-norms.** -/
theorem deningerTestSupNorm_smul (hJ : IsCompact J) {phi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) (a : ℝ) (m : ℕ) :
    deningerTestSupNorm m (a • phi) = |a| * deningerTestSupNorm m phi := by
  have hsmul : a • phi ∈ deningerTestSpace J := (deningerTestSpace J).smul_mem a hphi
  have hderiv : ∀ t, iteratedDeriv m (a • phi) t = a • iteratedDeriv m phi t := by
    intro t
    exact iteratedDeriv_const_smul (hphi.1.of_le (by exact_mod_cast le_top)).contDiffAt a
  have hnorm : ∀ t, ‖iteratedDeriv m (a • phi) t‖ = |a| * ‖iteratedDeriv m phi t‖ := by
    intro t
    rw [hderiv t, norm_smul, Real.norm_eq_abs]
  refine le_antisymm ?_ ?_
  · refine deningerTestSupNorm_le m fun t => ?_
    rw [hnorm t]
    exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le_supNorm hJ hphi m t) (abs_nonneg a)
  · rcases eq_or_ne a 0 with rfl | ha
    · rw [abs_zero, zero_mul, zero_smul]
      exact deningerTestSupNorm_nonneg hJ (deningerTestSpace J).zero_mem m
    · have habs : 0 < |a| := abs_pos.mpr ha
      rw [← le_div_iff₀' habs]
      refine deningerTestSupNorm_le m fun t => ?_
      rw [le_div_iff₀' habs, ← hnorm t]
      exact norm_iteratedDeriv_le_supNorm hJ hsmul m t

end SupNorm

end GaloisForLFunctions.HTGeometry
