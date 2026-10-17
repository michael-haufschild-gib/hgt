import GaloisForLFunctions.RHTower.ThetaRenewalCausalResponse
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantRankOne

/-!
# A positive compact Fredholm realization of the actual theta renewal source

The operator is the literal causal half-density kernel plus one positive
rank-one feedback. Its global regularized determinant is the actual renewal
denominator with exactly the linear exponential normalization removed.
Positivity here means preservation of the real nonnegative L² cone.
-/

noncomputable section
open Set MeasureTheory Complex ContinuousLinearMap InnerProductSpace
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

namespace RHTower

def thetaRenewalFredholmGap : ℝ :=
  HurwitzZeta.evenKernel (0 : UnitAddCircle) 1 - thetaRenewalLaplaceReal 0

theorem thetaRenewalFredholmGap_pos : 0 < thetaRenewalFredholmGap :=
  sub_pos.mpr thetaRenewalLaplaceReal_zero_lt

theorem thetaRenewalFredholmGap_eq :
    (thetaRenewalFredholmGap : ℂ) = thetaRenewalDenominator 0 :=
  thetaRenewalDenominator_zero_eq.symm

theorem thetaRenewalFredholmGap_ne_zero : (thetaRenewalFredholmGap : ℂ) ≠ 0 := by
  rw [thetaRenewalFredholmGap_eq]
  exact thetaRenewalDenominator_zero_ne

def thetaRenewalFredholmOperator : ThetaRenewalL2 →L[ℂ] ThetaRenewalL2 :=
  thetaRenewalCausalOperator + (thetaRenewalFredholmGap : ℂ)⁻¹ •
    rankOne ℂ (thetaRenewalMode 0) (adjoint thetaRenewalCausalOperator (thetaRenewalMode 0))

theorem thetaRenewalFredholmOperator_isHilbertSchmidt :
    IsHilbertSchmidt thetaRenewalFredholmOperator :=
  thetaRenewalCausalOperator_isHilbertSchmidt.add
    ((isHilbertSchmidt_rankOne _ _).smul _)

theorem thetaRenewalFredholmOperator_isCompact :
    IsCompactOperator thetaRenewalFredholmOperator :=
  thetaRenewalFredholmOperator_isHilbertSchmidt.isCompactOperator

private theorem nonneg_smul_thetaRenewalL2 {c : ℂ} (hc : 0 ≤ c)
    {f : ThetaRenewalL2} (hf : 0 ≤ f) : 0 ≤ c • f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [Lp.coeFn_smul c f, (Lp.coeFn_nonneg f).mpr hf] with t ht hft
  rw [ht]
  exact mul_nonneg hc hft

theorem thetaRenewalFredholmOperator_nonneg {f : ThetaRenewalL2} (hf : 0 ≤ f) :
    0 ≤ thetaRenewalFredholmOperator f := by
  have hc : 0 ≤ (thetaRenewalFredholmGap : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr thetaRenewalFredholmGap_pos.le)
  change 0 ≤ thetaRenewalCausalOperator f + (thetaRenewalFredholmGap : ℂ)⁻¹ •
    (inner ℂ (adjoint thetaRenewalCausalOperator (thetaRenewalMode 0)) f • thetaRenewalMode 0)
  exact add_nonneg (thetaRenewalCausalOperator_nonneg hf)
    (nonneg_smul_thetaRenewalL2 hc (nonneg_smul_thetaRenewalL2
      (l2_inner_nonneg_of_nonneg (thetaRenewalCausalAdjoint_nonneg
        thetaRenewalMode_zero_nonneg) hf) thetaRenewalMode_zero_nonneg))

theorem inner_thetaRenewalCausalAdjoint_zero_eq_drift :
    inner ℂ (adjoint thetaRenewalCausalOperator (thetaRenewalMode 0)) (thetaRenewalMode 0) =
      (thetaRenewalDrift : ℂ) * (thetaRenewalFredholmGap : ℂ) := by
  rw [inner_thetaRenewalCausalAdjoint_zero, ← Complex.ofReal_mul]
  congr 1
  have hd : thetaRenewalFredholmGap ≠ 0 := ne_of_gt thetaRenewalFredholmGap_pos
  change _ = (_ / thetaRenewalFredholmGap) * thetaRenewalFredholmGap
  field_simp [hd]

/-- Exact global entire determinant, with no exceptional spectral parameter. -/
theorem thetaRenewalFredholm_det2
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2) (z : ℂ) :
    det2Op b (z • thetaRenewalFredholmOperator) =
      Complex.exp (-(thetaRenewalDrift : ℂ) * z) *
        thetaRenewalDenominator z / thetaRenewalDenominator 0 := by
  let a : ℂ := z / (thetaRenewalFredholmGap : ℂ)
  let y := adjoint thetaRenewalCausalOperator (thetaRenewalMode 0)
  have hu : a • thetaRenewalMode z + (z • thetaRenewalCausalOperator)
      (a • thetaRenewalMode z) = a • thetaRenewalMode 0 := by
    calc _ = a • (thetaRenewalMode z + z • thetaRenewalCausalOperator (thetaRenewalMode z)) := by
           simp [smul_add, smul_smul, mul_comm]
         _ = _ := by rw [thetaRenewalMode_add_smul_causal]
  have he : z • thetaRenewalCausalOperator + rankOne ℂ (a • thetaRenewalMode 0) y =
      z • thetaRenewalFredholmOperator := by
    ext f
    simp [thetaRenewalFredholmOperator, y, a, rankOne_apply, div_eq_mul_inv,
      smul_add, smul_smul, mul_assoc]
  have hd := thetaRenewalFredholmGap_ne_zero
  have hf : 1 + inner ℂ y (a • thetaRenewalMode z) =
      thetaRenewalDenominator z / (thetaRenewalFredholmGap : ℂ) := by
    rw [inner_smul_right]
    calc 1 + a * inner ℂ y (thetaRenewalMode z) =
        ((thetaRenewalFredholmGap : ℂ) + z * inner ℂ y (thetaRenewalMode z)) /
          (thetaRenewalFredholmGap : ℂ) := by dsimp only [a]; field_simp [hd]
      _ = _ := by
        rw [show z * inner ℂ y (thetaRenewalMode z) =
          thetaRenewalLaplace 0 - thetaRenewalLaplace z from
            mul_inner_thetaRenewalCausalAdjoint_mode z, thetaRenewalFredholmGap_eq]
        congr 1
        simp only [thetaRenewalDenominator]
        ring
  have hx : inner ℂ y (a • thetaRenewalMode 0) = (thetaRenewalDrift : ℂ) * z := by
    rw [inner_smul_right]
    change a * inner ℂ (adjoint thetaRenewalCausalOperator (thetaRenewalMode 0))
      (thetaRenewalMode 0) = _
    rw [inner_thetaRenewalCausalAdjoint_zero_eq_drift]
    dsimp only [a]
    field_simp [hd]
  rw [← he, det2Op_rankOne_update b (thetaRenewalCausalOperator_isHilbertSchmidt.smul z)
    _ _ _ hu, thetaRenewalCausalOperator_det2, hf, hx, thetaRenewalFredholmGap_eq]
  ring

/-- The determinant reconstructs the source denominator with its fixed normalization. -/
theorem thetaRenewalDenominator_eq_fredholm
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2) (z : ℂ) :
    thetaRenewalDenominator z = thetaRenewalDenominator 0 *
      Complex.exp ((thetaRenewalDrift : ℂ) * z) *
        det2Op b (z • thetaRenewalFredholmOperator) := by
  rw [thetaRenewalFredholm_det2]
  have he : Complex.exp ((thetaRenewalDrift : ℂ) * z) *
      Complex.exp (-((thetaRenewalDrift : ℂ) * z)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hd := thetaRenewalDenominator_zero_ne
  simp only [neg_mul]
  field_simp [hd]
  linear_combination -(thetaRenewalDenominator z) * he

/-- Both ends of the actual Xi identity use the same positive compact operator. -/
theorem XiC_eq_thetaRenewalFredholm
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2) (z : ℂ) :
    XiC (2 * z) = thetaRenewalDenominator 0 *
      ((1 / 4 - I * z) * Complex.exp (-I * (thetaRenewalDrift : ℂ) * z) *
          det2Op b ((-(I * z)) • thetaRenewalFredholmOperator) +
       (1 / 4 + I * z) * Complex.exp (I * (thetaRenewalDrift : ℂ) * z) *
          det2Op b ((I * z) • thetaRenewalFredholmOperator)) := by
  rw [← thetaRenewal_two_ended z, thetaRenewalDenominator_eq_fredholm b (-(I * z)),
    thetaRenewalDenominator_eq_fredholm b (I * z)]
  rw [show (thetaRenewalDrift : ℂ) * -(I * z) = -I * (thetaRenewalDrift : ℂ) * z by ring,
    show (thetaRenewalDrift : ℂ) * (I * z) = I * (thetaRenewalDrift : ℂ) * z by ring]
  ring

end RHTower
