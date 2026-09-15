import GaloisForLFunctions.RHTower.SelbergMaassTraceMass

/-!
# High-cusp positivity isolates the Selberg core obstruction

The exact Bessel seam has only finitely many negative modes.  Above the explicit
transition cutoff for the principal-congruence width, every seam is nonnegative,
so the complete Maass Bessel boundary form is nonnegative.  Consequently an
exceptional source forces the literal compact-core quarter form to be strictly
negative at that cutoff.

This is a reduction, not a proof of Selberg's quarter conjecture: the remaining
open inequality is a lower bound for this source-attached compact-core form.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassBoundaryPositivity
open SelbergBesselSlope SelbergBesselModes SelbergBoundaryOperator
  SelbergMaassCongruenceTrace SelbergMaassTraceArea SelbergMaassTraceMass
noncomputable section

/-- Once the Bessel transition lies below the first Fourier frequency, every seam is nonnegative. -/
theorem seam_nonneg_of_transition_le {b T : ℝ}
    (htransition : transition ≤ Real.log (2 * Real.pi) - b + T) (n : ℤ) :
    0 ≤ seam b T n := by
  rw [seam_nonneg_outside]
  have hradius : radius b T ≤ 1 := by
    rw [radius, Real.exp_le_one_iff]
    linarith
  rw [(adverse_empty_iff b T).mpr hradius]
  simp

/-- The complete Bessel boundary form is nonnegative above its exact transition threshold. -/
theorem boundaryForm_nonneg_of_transition_le {b T : ℝ}
    (htransition : transition ≤ Real.log (2 * Real.pi) - b + T)
    (u : FormDomain b) :
    0 ≤ boundaryForm b T u := by
  unfold boundaryForm
  exact tsum_nonneg fun n =>
    mul_nonneg (seam_nonneg_of_transition_le htransition n) (Complex.normSq_nonneg _)

/-- The nonnegative logarithmic cutoff which places the first principal-congruence frequency at
or above the Bessel transition. -/
def transitionCutoff (N : ℕ) : ℝ :=
  max 0 (transition - (Real.log (2 * Real.pi) - Real.log (N + 1 : ℕ)))

/-- The selected cutoff is admissible for the core--cusp identity. -/
theorem transitionCutoff_nonneg (N : ℕ) : 0 ≤ transitionCutoff N :=
  le_max_left _ _

/-- At the selected cutoff, the first principal-congruence frequency reaches the transition. -/
theorem transition_le_first_frequency_at_cutoff (N : ℕ) :
    transition ≤ Real.log (2 * Real.pi) - Real.log (N + 1 : ℕ) + transitionCutoff N := by
  have h : transition - (Real.log (2 * Real.pi) - Real.log (N + 1 : ℕ)) ≤
      transitionCutoff N := le_max_right _ _
  linarith

/-- The full Bessel boundary form of every principal-congruence Maass source is nonnegative at
its transition cutoff. -/
theorem boundarySum_nonneg_at_transitionCutoff (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    0 ≤ boundarySum N f (transitionCutoff N) := by
  unfold boundarySum
  apply Finset.sum_nonneg
  intro q _
  apply boundaryForm_nonneg_of_transition_le
  exact transition_le_first_frequency_at_cutoff N

/-- An exceptional Maass source must have strictly negative compact-core quarter form after the
Bessel boundary has become nonnegative. -/
theorem coreQuarter_strict_neg_at_transitionCutoff (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    coreQuarter N f (Real.exp (transitionCutoff N)) < 0 := by
  have hcombined := core_boundary_strict_neg N lam f (transitionCutoff N)
    (transitionCutoff_nonneg N)
  have hboundary := boundarySum_nonneg_at_transitionCutoff N f
  linarith

end
end GaloisForLFunctions.RHTower.SelbergMaassBoundaryPositivity
