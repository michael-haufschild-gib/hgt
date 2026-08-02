import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityL1Completion
import GaloisForLFunctions.RHTower.DeningerMeyerLogGaussianUniversalOrbitCriterion

/-!
# Reflected Gaussian countertransport with uniform Meyer capacity

Let `h(t) = exp(-t/2) exp(-πt²)` be the target-free, Paugam-invariant Meyer
class constructed by `DeningerMeyerLogGaussianUniversalOrbitCriterion`.  For
every real depth `c`, form the depth-nonlocal two-sided countertransport

`H_c = V_c h + V_{-c} h`,

where `V_c` is centered logarithmic dilation.  Weighted reflection reverses
centered flow time, so every `H_c` remains in the reflected Hodge sector.

The canonical half-density `L¹` seminorm of `h` is exactly one.  Centered flow
is isometric and the triangle inequality therefore gives the unconditional,
depth-uniform capacity bound `p(H_c) ≤ 2`, before and after passage to literal
Meyer middle cohomology.

At a spectral parameter `s`, the transported Mellin value is exactly

`(exp(c(s-1/2)) + exp(-c(s-1/2))) exp((s-1/2)²/(4π))`.

The final theorem proves that uniform boundedness of these evaluations at every
actual Xi point is equivalent to RH.  Thus uniform reflected source capacity is
now constructed, not conjectural; the remaining hard arrow is continuity of Xi
evaluation against that capacity.  No RH premise is used in the construction or
capacity theorem.
-/

open Complex Filter Function Set Topology MeasureTheory Asymptotics
open scoped Real
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Paugam reflection reverses the exact centered flow without a residual
weight. -/
theorem deningerMeyerStrongLogJ_centeredFlow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ
        (deningerMeyerStrongLogCenteredFlow c g) =
      deningerMeyerStrongLogCenteredFlow (-c)
        (deningerMeyerStrongLogJ g) := by
  rw [deningerMeyerStrongLogCenteredFlow,
    deningerMeyerStrongLogCenteredFlow,
    LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.map_smul, deningerMeyerStrongLogJ_flow,
    smul_smul]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Two-sided centered countertransport of the reflected log-Gaussian. -/
def deningerMeyerReflectedGaussianCountertransport (c : ℝ) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogCenteredFlow c
      deningerMeyerReflectedLogGaussianSource +
    deningerMeyerStrongLogCenteredFlow (-c)
      deningerMeyerReflectedLogGaussianSource

/-- Every depth of the countertransport stays in the positive reflected Hodge
sector. -/
theorem deningerMeyerReflectedGaussianCountertransport_J_fixed (c : ℝ) :
    deningerMeyerStrongLogJ
        (deningerMeyerReflectedGaussianCountertransport c) =
      deningerMeyerReflectedGaussianCountertransport c := by
  rw [deningerMeyerReflectedGaussianCountertransport, LinearMap.map_add,
    deningerMeyerStrongLogJ_centeredFlow,
    deningerMeyerStrongLogJ_centeredFlow,
    deningerMeyerReflectedLogGaussianSource_J_fixed]
  rw [neg_neg, add_comm]

/-- Exact unit half-density capacity of the reflection-adapted Gaussian. -/
theorem deningerMeyerReflectedLogGaussian_halfDensityL1 :
    deningerMeyerHalfDensityL1Seminorm
        deningerMeyerReflectedLogGaussianSource = 1 := by
  rw [deningerMeyerHalfDensityL1Seminorm_apply]
  have hfun : (fun t : ℝ =>
      deningerMeyerHalfDensityWeight t *
        ‖(deningerMeyerReflectedLogGaussianSource : ℝ → ℂ) t‖) =
      gaussReal := by
    funext t
    rw [deningerMeyerReflectedLogGaussianSource_apply,
      norm_mul, Complex.norm_exp]
    simp only [deningerMeyerHalfDensityWeight]
    norm_num
    rw [abs_of_pos (gaussReal_pos t), ← mul_assoc, ← Real.exp_add]
    rw [show t / 2 + -t / 2 = 0 by ring, Real.exp_zero, one_mul]
  rw [hfun, show gaussReal = fun t : ℝ => Real.exp (-π * t ^ 2) by
      funext t
      rw [gaussReal]
      congr 1
      ring,
    integral_gaussian]
  rw [div_self Real.pi_ne_zero, Real.sqrt_one]

/-- **Uniform source capacity.**  All real countertransport depths have
half-density capacity at most two. -/
theorem deningerMeyerReflectedGaussianCountertransport_uniform_capacity
    (c : ℝ) :
    deningerMeyerHalfDensityL1Seminorm
        (deningerMeyerReflectedGaussianCountertransport c) ≤ 2 := by
  calc
    deningerMeyerHalfDensityL1Seminorm
        (deningerMeyerReflectedGaussianCountertransport c) ≤
      deningerMeyerHalfDensityL1Seminorm
          (deningerMeyerStrongLogCenteredFlow c
            deningerMeyerReflectedLogGaussianSource) +
        deningerMeyerHalfDensityL1Seminorm
          (deningerMeyerStrongLogCenteredFlow (-c)
            deningerMeyerReflectedLogGaussianSource) :=
      map_add_le_add _ _ _
    _ = 2 := by
      rw [deningerMeyerHalfDensityL1Seminorm_centeredFlow,
        deningerMeyerHalfDensityL1Seminorm_centeredFlow,
        deningerMeyerReflectedLogGaussian_halfDensityL1]
      norm_num

/-- Raw centered-flow character law for the entire Meyer transform. -/
theorem deningerMeyerStrongLogMellin_centeredFlow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogCenteredFlow c g) s =
      Complex.exp ((c : ℂ) * (s - 1 / 2)) *
        deningerMeyerStrongLogMellin g s := by
  change (deningerMeyerStrongLogMellinLM s)
      (Complex.exp (-(c : ℂ) / 2) •
        deningerMeyerStrongLogFlow c g) = _
  rw [(deningerMeyerStrongLogMellinLM s).map_smul]
  change Complex.exp (-(c : ℂ) / 2) *
      deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogFlow c g) s = _
  rw [deningerMeyerStrongLogMellin_flow, ← mul_assoc, ← Complex.exp_add]
  congr 1
  ring

/-- Exact cosh-type spectral profile of the reflected countertransport. -/
theorem deningerMeyerReflectedGaussianCountertransport_mellin
    (c : ℝ) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerReflectedGaussianCountertransport c) s =
      (Complex.exp ((c : ℂ) * (s - 1 / 2)) +
        Complex.exp (-(c : ℂ) * (s - 1 / 2))) *
        Complex.exp ((s - 1 / 2) ^ 2 / (4 * π)) := by
  change (deningerMeyerStrongLogMellinLM s)
      (deningerMeyerStrongLogCenteredFlow c
          deningerMeyerReflectedLogGaussianSource +
        deningerMeyerStrongLogCenteredFlow (-c)
          deningerMeyerReflectedLogGaussianSource) = _
  rw [(deningerMeyerStrongLogMellinLM s).map_add,
    show (deningerMeyerStrongLogMellinLM s)
        (deningerMeyerStrongLogCenteredFlow c
          deningerMeyerReflectedLogGaussianSource) =
        deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogCenteredFlow c
            deningerMeyerReflectedLogGaussianSource) s by rfl,
    show (deningerMeyerStrongLogMellinLM s)
        (deningerMeyerStrongLogCenteredFlow (-c)
          deningerMeyerReflectedLogGaussianSource) =
        deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogCenteredFlow (-c)
            deningerMeyerReflectedLogGaussianSource) s by rfl,
    deningerMeyerStrongLogMellin_centeredFlow,
    deningerMeyerStrongLogMellin_centeredFlow,
    deningerMeyerReflectedLogGaussianSource_mellin]
  push_cast
  ring

/-- Literal Meyer middle class of the depth-`c` countertransport. -/
def deningerMeyerReflectedGaussianCountertransportClass (c : ℝ) :
    DeningerMeyerStrongLogCohomology :=
  Submodule.Quotient.mk (deningerMeyerReflectedGaussianCountertransport c)

theorem deningerMeyerReflectedGaussianCountertransportClass_J_fixed
    (c : ℝ) :
    deningerMeyerStrongLogCohomologyJ
        (deningerMeyerReflectedGaussianCountertransportClass c) =
      deningerMeyerReflectedGaussianCountertransportClass c := by
  rw [deningerMeyerReflectedGaussianCountertransportClass,
    deningerMeyerStrongLogCohomologyJ_mk,
    deningerMeyerReflectedGaussianCountertransport_J_fixed]

/-- Uniform capacity survives passage to literal Meyer middle cohomology. -/
theorem
    deningerMeyerReflectedGaussianCountertransportClass_uniform_capacity
    (c : ℝ) :
    deningerMeyerHalfDensityCohomologySeminorm
        (deningerMeyerReflectedGaussianCountertransportClass c) ≤ 2 := by
  exact
    (deningerQuotientSeminorm_mk_le
      (LinearMap.range deningerMeyerStrongLogSumLM)
      deningerMeyerHalfDensityL1Seminorm
      (deningerMeyerReflectedGaussianCountertransport c)).trans
        (deningerMeyerReflectedGaussianCountertransport_uniform_capacity c)

/-- Exact actual Xi evaluation of the depth-nonlocal countertransport. -/
theorem deningerMeyerReflectedGaussianCountertransportClass_evaluation
    (rho : XiDivisorSupport) (c : ℝ) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerReflectedGaussianCountertransportClass c) =
      (Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) +
        Complex.exp (-(c : ℂ) * ((rho : ℂ) - 1 / 2))) *
        Complex.exp (((rho : ℂ) - 1 / 2) ^ 2 / (4 * π)) := by
  rw [deningerMeyerReflectedGaussianCountertransportClass,
    deningerMeyerXiSupportJetEvaluationLM_mk]
  simpa [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv] using
      deningerMeyerReflectedGaussianCountertransport_mellin c (rho : ℂ)

/-- A bounded two-sided exponential orbit with a nonzero coefficient has zero
real character rate. -/
theorem re_eq_zero_of_bounded_reflected_exponential_pair
    (A z : ℂ) (hA : A ≠ 0)
    (hbounded : ∃ C : ℝ, ∀ c : ℝ,
      ‖(Complex.exp ((c : ℂ) * z) +
          Complex.exp (-(c : ℂ) * z)) * A‖ ≤ C) :
    z.re = 0 := by
  obtain ⟨C, hbound⟩ := hbounded
  let N : ℝ := ‖A‖
  have hN : 0 < N := norm_pos_iff.mpr hA
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbound 0)
  let T : ℝ := C / N + 2
  have hTtwo : 2 ≤ T := by
    dsimp [T]
    have hdiv : 0 ≤ C / N := div_nonneg hC hN.le
    linarith
  have hT : 0 < T := zero_lt_two.trans_le hTtwo
  by_contra hz
  let c : ℝ := Real.log T / z.re
  have hcre : c * z.re = Real.log T := by
    dsimp [c]
    field_simp
  have hre : (((c : ℝ) : ℂ) * z).re = Real.log T := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact hcre
  have hnormPos : ‖Complex.exp ((c : ℂ) * z)‖ = T := by
    rw [Complex.norm_exp, hre, Real.exp_log hT]
  have hnormNeg : ‖Complex.exp (-(c : ℂ) * z)‖ = T⁻¹ := by
    rw [Complex.norm_exp]
    have hneg : (-(c : ℂ) * z).re = -Real.log T := by
      rw [show -(c : ℂ) * z = -((c : ℂ) * z) by ring,
        Complex.neg_re, hre]
    rw [hneg, Real.exp_neg, Real.exp_log hT]
  have hTinv : T⁻¹ ≤ 1 :=
    (inv_le_one₀ hT).2 (one_le_two.trans hTtwo)
  have htri := norm_sub_le
    ((Complex.exp ((c : ℂ) * z) + Complex.exp (-(c : ℂ) * z)) * A)
    (Complex.exp (-(c : ℂ) * z) * A)
  have heq :
      (Complex.exp ((c : ℂ) * z) + Complex.exp (-(c : ℂ) * z)) * A -
          Complex.exp (-(c : ℂ) * z) * A =
        Complex.exp ((c : ℂ) * z) * A := by
    ring
  rw [heq, norm_mul, hnormPos] at htri
  have hnormNegA :
      ‖Complex.exp (-(c : ℂ) * z) * A‖ = T⁻¹ * ‖A‖ := by
    rw [norm_mul, hnormNeg]
  rw [hnormNegA] at htri
  have h := hbound c
  have hupper : T * N ≤ C + N := by
    calc
      T * N ≤
          ‖(Complex.exp ((c : ℂ) * z) +
              Complex.exp (-(c : ℂ) * z)) * A‖ + T⁻¹ * N := htri
      _ ≤ C + N := add_le_add h (mul_le_of_le_one_left hN.le hTinv)
  have hTN : T * N = C + 2 * N := by
    dsimp [T, N]
    rw [add_mul, div_mul_cancel₀ C hN.ne']
  rw [hTN] at hupper
  linarith

/-- Pointwise evaluation boundedness on the reflected Gaussian
countertransport. -/
def DeningerMeyerReflectedGaussianCountertransportEvaluationBoundedAt
    (rho : XiDivisorSupport) : Prop :=
  ∃ C : ℝ, ∀ c : ℝ,
    ‖deningerMeyerXiSupportJetEvaluationLM rho
      (⟨0, xiSupportMultiplicity_pos rho⟩ :
        DeningerArithmeticJetIndex rho)
      (deningerMeyerReflectedGaussianCountertransportClass c)‖ ≤ C

/-- Exact pointwise continuity spectrum, witnessed inside the reflected Hodge
sector by one explicit uniformly capacity-bounded family. -/
theorem
    deningerMeyerReflectedGaussianCountertransportEvaluationBoundedAt_iff
    (rho : XiDivisorSupport) :
    DeningerMeyerReflectedGaussianCountertransportEvaluationBoundedAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hbounded
    have hz := re_eq_zero_of_bounded_reflected_exponential_pair
      (Complex.exp (((rho : ℂ) - 1 / 2) ^ 2 / (4 * π)))
      ((rho : ℂ) - 1 / 2)
      (Complex.exp_ne_zero _)
      (by
        obtain ⟨C, hC⟩ := hbounded
        refine ⟨C, fun c => ?_⟩
        rw [← deningerMeyerReflectedGaussianCountertransportClass_evaluation]
        exact hC c)
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
    linarith
  · intro hre
    let A := Complex.exp (((rho : ℂ) - 1 / 2) ^ 2 / (4 * π))
    refine ⟨2 * ‖A‖, fun c => ?_⟩
    rw [deningerMeyerReflectedGaussianCountertransportClass_evaluation,
      norm_mul]
    have hpos : ‖Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2))‖ = 1 := by
      rw [Complex.norm_exp]
      have hzero : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
        rw [hre]
        ring
      rw [hzero, Real.exp_zero]
    have hneg : ‖Complex.exp (-(c : ℂ) * ((rho : ℂ) - 1 / 2))‖ = 1 := by
      rw [Complex.norm_exp]
      have hzero : (-(c : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
        rw [show -(c : ℂ) * ((rho : ℂ) - 1 / 2) =
            -((c : ℂ) * ((rho : ℂ) - 1 / 2)) by ring,
          Complex.neg_re]
        have hposRe : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
          rw [hre]
          ring
        rw [hposRe, neg_zero]
      rw [hzero, Real.exp_zero]
    calc
      ‖Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) +
          Complex.exp (-(c : ℂ) * ((rho : ℂ) - 1 / 2))‖ * ‖A‖ ≤
        (1 + 1) * ‖A‖ :=
          mul_le_mul_of_nonneg_right
            ((norm_add_le _ _).trans_eq (by rw [hpos, hneg]))
            (norm_nonneg _)
      _ = 2 * ‖A‖ := by ring

/-- Off-line actual Xi points have an explicit reflected-Hodge escape family:
for every ceiling, one uniformly capacity-bounded countertransport depth exceeds
that ceiling under Xi evaluation. -/
theorem
    deningerMeyerReflectedGaussianCountertransport_evaluation_unbounded_of_re_ne_half
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    ∀ C : ℝ, ∃ c : ℝ,
      C < ‖deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ :
          DeningerArithmeticJetIndex rho)
        (deningerMeyerReflectedGaussianCountertransportClass c)‖ := by
  intro C
  by_contra hnone
  simp only [not_exists, not_lt] at hnone
  exact hrho
    ((deningerMeyerReflectedGaussianCountertransportEvaluationBoundedAt_iff rho).mp
      ⟨C, hnone⟩)

/-- Uniform boundedness of actual Xi evaluations on the explicit reflected
countertransport. -/
def DeningerMeyerReflectedGaussianCountertransportEvaluationsBounded : Prop :=
  ∀ rho : XiDivisorSupport,
    DeningerMeyerReflectedGaussianCountertransportEvaluationBoundedAt rho

/-- **Capacity-separation law.**  Source capacity is uniformly bounded
unconditionally, but uniform Xi evaluation on that same family holds exactly
under RH. -/
theorem
    deningerMeyerReflectedGaussianCountertransportEvaluationsBounded_iff_rh :
    DeningerMeyerReflectedGaussianCountertransportEvaluationsBounded ↔
      RiemannHypothesis := by
  constructor
  · intro hbounded
    rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
    intro rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    have hz := re_eq_zero_of_bounded_reflected_exponential_pair
      (Complex.exp (((rho : ℂ) - 1 / 2) ^ 2 / (4 * π)))
      ((rho : ℂ) - 1 / 2)
      (Complex.exp_ne_zero _)
      (by
        obtain ⟨C, hC⟩ := hbounded rho
        refine ⟨C, fun c => ?_⟩
        rw [← deningerMeyerReflectedGaussianCountertransportClass_evaluation]
        exact hC c)
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
    linarith
  · intro hRH rho
    have hre : (rho : ℂ).re = 1 / 2 := by
      have hfracture :=
        (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) rho
      exact
        (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
          (rho : ℂ)).mp hfracture
    let A := Complex.exp (((rho : ℂ) - 1 / 2) ^ 2 / (4 * π))
    refine ⟨2 * ‖A‖, fun c => ?_⟩
    rw [deningerMeyerReflectedGaussianCountertransportClass_evaluation,
      norm_mul]
    have hpos : ‖Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2))‖ = 1 := by
      rw [Complex.norm_exp]
      have hzero : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
        rw [hre]
        ring
      rw [hzero, Real.exp_zero]
    have hneg : ‖Complex.exp (-(c : ℂ) * ((rho : ℂ) - 1 / 2))‖ = 1 := by
      rw [Complex.norm_exp]
      have hzero : (-(c : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
        rw [show -(c : ℂ) * ((rho : ℂ) - 1 / 2) =
            -((c : ℂ) * ((rho : ℂ) - 1 / 2)) by ring,
          Complex.neg_re]
        have hposRe : (((c : ℝ) : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
          rw [hre]
          ring
        rw [hposRe, neg_zero]
      rw [hzero, Real.exp_zero]
    calc
      ‖Complex.exp ((c : ℂ) * ((rho : ℂ) - 1 / 2)) +
          Complex.exp (-(c : ℂ) * ((rho : ℂ) - 1 / 2))‖ * ‖A‖ ≤
        (1 + 1) * ‖A‖ :=
          mul_le_mul_of_nonneg_right
            ((norm_add_le _ _).trans_eq (by rw [hpos, hneg]))
            (norm_nonneg _)
      _ = 2 * ‖A‖ := by ring

end

end RHTower
