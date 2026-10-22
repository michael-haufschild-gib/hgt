import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiSpectralInclusion
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Pointwise invariant-gauge frontier for literal Meyer cohomology

The positive admissible Meyer completion proposed by the source--boundary
conservation law is substantially stronger than the hypothesis needed for
RH.  For each actual Xi divisor point separately, it is enough to construct
one finite nonnegative gauge on the algebraic Meyer quotient which

* is invariant under the centered dilation flow; and
* bounds that point's nonzero zeroth-jet evaluation.

The gauge need not be common to different divisor points.  It need not be a
norm or seminorm, need not satisfy a triangle or homogeneity law, and no
Hausdorff completion or inner product is required.  The proof uses arbitrary
real flow time: a nonzero real character makes one evaluation exceed every
fixed gauge bound.

Thus the exact remaining source obligation is pointwise finite invariant
evaluation control on genuine Meyer middle cohomology.  This file proves the
reduction; it does not postulate or construct those gauges.
-/

open Complex

namespace RHTower

noncomputable section

/-- A bounded nonzero exponential eigenfunctional of a finite invariant
nonnegative gauge has purely imaginary exponent.  No norm axioms are used. -/
theorem re_eq_zero_of_invariantGauge_bounded_eigenfunctional
    {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (V : ℝ → X →ₗ[ℂ] X) (E : X →ₗ[ℂ] ℂ) (hE : E ≠ 0)
    (gauge : X → ℝ)
    (hgauge_nonneg : ∀ u, 0 ≤ gauge u)
    (hgauge_invariant : ∀ (c : ℝ) (u : X), gauge (V c u) = gauge u)
    (hE_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖E u‖ ≤ C * gauge u)
    (z : ℂ)
    (heigen : ∀ (c : ℝ) (u : X),
      E (V c u) = Complex.exp ((c : ℂ) * z) * E u) :
    z.re = 0 := by
  have hexists : ∃ u : X, E u ≠ 0 := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    apply hE
    ext u
    exact hnone u
  obtain ⟨u, hu⟩ := hexists
  obtain ⟨C, hC, hbound⟩ := hE_bounded
  let A : ℝ := ‖E u‖
  let M : ℝ := C * gauge u
  have hA : 0 < A := norm_pos_iff.mpr hu
  have hM : 0 ≤ M := mul_nonneg hC (hgauge_nonneg u)
  by_contra hz
  let T : ℝ := M / A + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let c : ℝ := Real.log T / z.re
  have hcre : c * z.re = Real.log T := by
    dsimp [c]
    field_simp
  have hre : (((c : ℝ) : ℂ) * z).re = Real.log T := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact hcre
  have h := hbound (V c u)
  rw [heigen c u, norm_mul, Complex.norm_exp,
    hgauge_invariant c u, hre, Real.exp_log hT] at h
  change T * A ≤ M at h
  have hTA : T * A = M + A := by
    dsimp [T]
    rw [add_mul, div_mul_cancel₀ M hA.ne']
    ring
  rw [hTA] at h
  nlinarith

/-- Centered dilation on the literal algebraic Meyer middle quotient. -/
def deningerMeyerStrongLogCenteredCohomologyFlow (c : ℝ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology :=
  Complex.exp (-(c : ℂ) / 2) •
    deningerMeyerStrongLogCohomologyFlow c

/-- The canonical zeroth Xi evaluation has centered character
`exp(c * (rho - 1/2))`. -/
theorem deningerMeyerXiSupportEvaluationLM_centeredFlow
    (rho : XiDivisorSupport) (c : ℝ)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerStrongLogCenteredCohomologyFlow c u) =
      Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) *
        deningerMeyerXiSupportJetEvaluationLM rho
          (⟨0, xiSupportMultiplicity_pos rho⟩ :
            DeningerArithmeticJetIndex rho) u := by
  rw [deningerMeyerStrongLogCenteredCohomologyFlow,
    LinearMap.smul_apply, map_smul,
    deningerMeyerXiSupportJetEvaluationLM_flow]
  simp only [Nat.zero_add, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero,
    Nat.zero_sub, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

/-- Pointwise positive-admission gauge for one actual Xi evaluation. -/
def DeningerMeyerXiPointwiseInvariantEvaluationGauge
    (rho : XiDivisorSupport)
    (gauge : DeningerMeyerStrongLogCohomology → ℝ) : Prop :=
  (∀ u, 0 ≤ gauge u) ∧
  (∀ (c : ℝ) (u),
    gauge (deningerMeyerStrongLogCenteredCohomologyFlow c u) = gauge u) ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u,
    ‖deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho) u‖ ≤ C * gauge u

/-- One pointwise invariant evaluation gauge forces its divisor point onto
the critical line. -/
theorem xiDivisorSupport_re_eq_half_of_pointwiseInvariantEvaluationGauge
    (rho : XiDivisorSupport)
    (gauge : DeningerMeyerStrongLogCohomology → ℝ)
    (hgauge : DeningerMeyerXiPointwiseInvariantEvaluationGauge rho gauge) :
    (rho : ℂ).re = 1 / 2 := by
  let E := deningerMeyerXiSupportJetEvaluationLM rho
    (⟨0, xiSupportMultiplicity_pos rho⟩ :
      DeningerArithmeticJetIndex rho)
  have hz := re_eq_zero_of_invariantGauge_bounded_eigenfunctional
    deningerMeyerStrongLogCenteredCohomologyFlow E
    (deningerMeyerXiSupportEvaluationLM_ne_zero rho)
    gauge hgauge.1 hgauge.2.1 hgauge.2.2
    ((rho : ℂ) - 1 / 2)
    (deningerMeyerXiSupportEvaluationLM_centeredFlow rho)
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
  linarith

/-- **Strictly weakened Meyer closing theorem.** Pointwise invariant gauges
for the actual zeroth Xi evaluations imply RH. -/
theorem riemannHypothesis_of_deningerMeyerXiPointwiseInvariantEvaluationGauges
    (h : ∀ rho : XiDivisorSupport,
      ∃ gauge : DeningerMeyerStrongLogCohomology → ℝ,
        DeningerMeyerXiPointwiseInvariantEvaluationGauge rho gauge) :
    RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  intro rho
  apply
    (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (rho : ℂ)).2
  obtain ⟨gauge, hgauge⟩ := h rho
  exact xiDivisorSupport_re_eq_half_of_pointwiseInvariantEvaluationGauge
    rho gauge hgauge

end

end RHTower
