import GaloisForLFunctions.RHTower.HedenmalmThetaDerivativeJordan
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.HTGeometry.CompactAdjoint
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Proper quasinilpotent history of the actual theta source inverse

The compact inverse preserves the closed span of actual source derivatives.
Its restriction has spectrum exactly `{0}`: a nonzero adjoint eigenvalue
would annihilate every vector of the lowering chain and hence its closed span.
Hardy's real zeros supply genuine nonzero reciprocal eigenvalues of the full
source inverse, proving that the derivative history is a proper subspace.
-/

open MeasureTheory Set Topology Complex Module

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmHilbertSchmidt

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev RH := thetaQuantileDerivativeHistory

local instance : CompleteSpace RH :=
  (Submodule.span ℂ (range thetaQuantileDerivativeVector)).isClosed_topologicalClosure.completeSpace_coe

def thetaDerivativeHistoryInverse : RH →L[ℂ] RH :=
  thetaCompactSourceInverse.restrict (fun _ hf => thetaQuantileDerivativeHistory_invariant hf)

theorem isCompactOperator_thetaDerivativeHistoryInverse :
    IsCompactOperator thetaDerivativeHistoryInverse :=
  isCompactOperator_thetaCompactSourceInverse.restrict
    (fun _ hf => thetaQuantileDerivativeHistory_invariant hf)
    (Submodule.span ℂ (range thetaQuantileDerivativeVector)).isClosed_topologicalClosure

def thetaHistoryDerivativeVector (n : ℕ) : RH :=
  ⟨thetaQuantileDerivativeVector n, thetaQuantileDerivativeVector_mem_history n⟩

theorem thetaHistoryDerivativeVector_ne_zero (n : ℕ) :
    thetaHistoryDerivativeVector n ≠ 0 := by
  intro hzero
  exact thetaQuantileDerivativeVector_ne_zero n
    (congrArg (fun f : RH => (f : H)) hzero)

theorem thetaDerivativeHistoryInverse_zero :
    thetaDerivativeHistoryInverse (thetaHistoryDerivativeVector 0) = 0 :=
  Subtype.ext thetaCompactSourceInverse_thetaQuantileDerivativeVector_zero

theorem thetaDerivativeHistoryInverse_succ (n : ℕ) :
    thetaDerivativeHistoryInverse (thetaHistoryDerivativeVector (n + 1)) =
      Complex.I • thetaHistoryDerivativeVector n :=
  Subtype.ext (thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ n)

/-- A nonzero adjoint eigenvalue would annihilate the entire generating chain. -/
theorem thetaDerivativeHistoryInverse_adjoint_eigen_eq_zero
    {lam : ℂ} (hlam : lam ≠ 0) (u : RH)
    (heigen : thetaDerivativeHistoryInverse.adjoint u = lam • u) : u = 0 := by
  have hstar : star lam ≠ 0 := star_ne_zero.mpr hlam
  have hinner (n : ℕ) : inner ℂ u (thetaHistoryDerivativeVector n) = 0 := by
    induction n with
    | zero =>
        have h := thetaDerivativeHistoryInverse.adjoint_inner_left
          (thetaHistoryDerivativeVector 0) u
        rw [heigen, inner_smul_left (𝕜 := ℂ) u (thetaHistoryDerivativeVector 0) lam,
          thetaDerivativeHistoryInverse_zero, inner_zero_right] at h
        exact (mul_eq_zero.mp h).resolve_left hstar
    | succ n hn =>
        have h := thetaDerivativeHistoryInverse.adjoint_inner_left
          (thetaHistoryDerivativeVector (n + 1)) u
        rw [heigen, inner_smul_left (𝕜 := ℂ) u (thetaHistoryDerivativeVector (n + 1)) lam,
          thetaDerivativeHistoryInverse_succ,
          inner_smul_right (𝕜 := ℂ) u (thetaHistoryDerivativeVector n) Complex.I, hn, mul_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hstar
  have hspan : (u : H) ∈ (Submodule.span ℂ (range thetaQuantileDerivativeVector))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro f hf
    refine Submodule.span_induction (fun g hg => ?_) (by simp)
      (fun f g _ _ hf hg => by simp [inner_add_right, hf, hg])
      (fun a f _ hf => by simp [inner_smul_right, hf]) hf
    rcases hg with ⟨n, rfl⟩
    exact hinner n
  have hhistory : (u : H) ∈ thetaQuantileDerivativeHistoryᗮ := by
    simpa only [thetaQuantileDerivativeHistory, Submodule.orthogonal_closure] using hspan
  apply Subtype.ext
  exact inner_self_eq_zero.mp
    ((Submodule.mem_orthogonal' thetaQuantileDerivativeHistory (u : H)).mp hhistory (u : H) u.property)

/-- Compactness turns absence of nonzero adjoint eigenvalues into quasinilpotence. -/
theorem thetaDerivativeHistoryInverse_spectral_value_eq_zero
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ thetaDerivativeHistoryInverse) : lam = 0 := by
  by_contra hlam0
  have hspec : star lam ∈ spectrum ℂ thetaDerivativeHistoryInverse.adjoint := by
    change star lam ∈ spectrum ℂ (star thetaDerivativeHistoryInverse)
    rw [spectrum.map_star (R := ℂ) thetaDerivativeHistoryInverse, Set.mem_star, star_star]
    exact hlam
  have hcompact := isCompactOperator_adjoint_rectangular thetaDerivativeHistoryInverse
    isCompactOperator_thetaDerivativeHistoryInverse
  obtain ⟨u, hu⟩ :=
    ((hcompact.hasEigenvalue_iff_mem_spectrum (star_ne_zero.mpr hlam0)).mpr hspec).exists_hasEigenvector
  exact hu.2 (thetaDerivativeHistoryInverse_adjoint_eigen_eq_zero
    (star_ne_zero.mpr hlam0) u hu.apply_eq_smul)

theorem thetaDerivativeHistoryInverse_spectrum :
    spectrum ℂ thetaDerivativeHistoryInverse = {0} := by
  have heigen : Module.End.HasEigenvector thetaDerivativeHistoryInverse.toLinearMap 0
      (thetaHistoryDerivativeVector 0) :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by
      change thetaDerivativeHistoryInverse (thetaHistoryDerivativeVector 0) =
        0 • thetaHistoryDerivativeVector 0
      rw [zero_smul]
      exact thetaDerivativeHistoryInverse_zero),
      thetaHistoryDerivativeVector_ne_zero 0⟩
  have hzero : (0 : ℂ) ∈ spectrum ℂ thetaDerivativeHistoryInverse := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector heigen).mem_spectrum
  ext lam
  constructor
  · intro hlam
    exact Set.mem_singleton_iff.mpr (thetaDerivativeHistoryInverse_spectral_value_eq_zero hlam)
  · rintro rfl
    exact hzero

/-- Hardy's actual real Xi divisor excludes totality of the weighted derivative history. -/
theorem thetaQuantileDerivativeHistory_ne_top : thetaQuantileDerivativeHistory ≠ ⊤ := by
  intro htop
  obtain ⟨t, ht, htzero⟩ := exists_Xi_zero_gt 0
  have hstrip : |(t : ℂ).im| < 1 := by simp
  have hxi : xiC thetaSource (t : ℂ) = 0 := by
    rw [xiC_thetaSource hstrip, XiC_ofReal, htzero]
    simp
  let w : H := thetaDivisorEigenvector (t : ℂ) hstrip hxi
  let lam : ℂ := -(t : ℂ)⁻¹
  have hw : w ≠ 0 := thetaDivisorEigenvector_ne_zero (t : ℂ) hstrip hxi
  have hlam : lam ≠ 0 := by
    dsimp [lam]
    exact neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast ht.ne'))
  let u : RH := ⟨w, by change w ∈ thetaQuantileDerivativeHistory; rw [htop]; trivial⟩
  have hu : u ≠ 0 := by
    intro hzero
    exact hw (congrArg (fun f : RH => (f : H)) hzero)
  have heigen : Module.End.HasEigenvector thetaDerivativeHistoryInverse.toLinearMap lam u :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by
      change thetaDerivativeHistoryInverse u = lam • u
      exact Subtype.ext (thetaCompactSourceInverse_eigen (t : ℂ) hstrip hxi)), hu⟩
  have hspec : lam ∈ spectrum ℂ thetaDerivativeHistoryInverse := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector heigen).mem_spectrum
  exact hlam (thetaDerivativeHistoryInverse_spectral_value_eq_zero hspec)

end

end RHTower.HedenmalmThetaSource
