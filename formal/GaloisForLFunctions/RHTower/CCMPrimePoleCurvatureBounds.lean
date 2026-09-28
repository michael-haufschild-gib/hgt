import GaloisForLFunctions.RHTower.CCMPrimePoleJumpBochner
import GaloisForLFunctions.HTGeometry.JumpCurvatureBounds

/-!
# An explicit curvature lower bound for the actual prime jumps

The literal jump degree equals the pole-normalized prime row inside the aperture
and vanishes outside it. Chebyshev and reciprocal-Mangoldt estimates bound it by
the existing explicit Schur envelope. The variable-rate square decomposition then
gives `Γ₂ ≥ (Lf)²/2 − envelope·Γ` without an assumed arithmetic comparison or an
assumption that the prime curvature is nonnegative.
-/

noncomputable section
open Set
open scoped BigOperators
namespace RHTower
open HTGeometry.JumpBochner

theorem ccmPrimePoleJumpDegree_eq_row
    (a : SuzukiPositiveAperture) {x : ℝ} (hx : x ∈ centralInterval a.1) :
    degree (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) x =
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          ((centralInterval a.1).indicator primePoleProfile (x-Real.log n) +
            (centralInterval a.1).indicator primePoleProfile (x+Real.log n))) / primePoleProfile x := by
  unfold degree ccmPrimePoleJumpIndices
  simp only [Finset.product_eq_sprod, Finset.sum_product, Fintype.sum_bool,
    ccmPrimePoleJumpRate, indicator_of_mem hx]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ccmPrimePoleJumpShift, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg]
  ring

theorem ccmPrimePoleJumpDegree_le_envelope (a : SuzukiPositiveAperture) (x : ℝ) :
    degree (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) x ≤
      ccmPrimePoleSchurEnvelope a := by
  by_cases hx : x ∈ centralInterval a.1
  · rw [ccmPrimePoleJumpDegree_eq_row a hx]
    apply (div_le_iff₀ (primePoleProfile_pos x)).mpr
    have h := primePoleRow_le a (Real.log 4) (4*a.1) 0 (Real.log 4+4)
      (by linarith [a.property])
      (fun X hX hXa => by
        have hp := Chebyshev.psi_le hX
        have hlog : Real.log X ≤ 2*a.1 := by
          rw [← Real.log_exp (2*a.1)]
          exact Real.log_le_log (by linarith) hXa
        nlinarith [Real.sqrt_nonneg X, Real.log_nonneg hX])
      (fun X hX _ => ccmReciprocalMangoldtCumulative_le_log_add X hX) hx
    simpa only [ccmPrimePoleSchurEnvelope, zero_add, add_zero] using h
  · simp only [degree, ccmPrimePoleJumpRate, indicator_of_notMem hx, Finset.sum_const_zero]
    have ha : 0 < a.1 := a.property
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    unfold ccmPrimePoleSchurEnvelope
    positivity

theorem ccmPrimePoleJump_generator_sq_sub_envelope_energy_le_gammaTwo
    (a : SuzukiPositiveAperture) (f : ℝ → ℝ) (x : ℝ) :
    (generator (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f x)^2 / 2 -
        ccmPrimePoleSchurEnvelope a *
          energyDensity (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f f x ≤
      gammaTwo (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f x :=
  generator_sq_sub_degree_mul_energy_le_gammaTwo _ _ _
    (fun j _ y => ccmPrimePoleJumpRate_nonneg a j y) _ (ccmPrimePoleJumpDegree_le_envelope a) f x

theorem ccmPrimePoleJump_gammaTwo_ge_neg_envelope_energy
    (a : SuzukiPositiveAperture) (f : ℝ → ℝ) (x : ℝ) :
    -ccmPrimePoleSchurEnvelope a *
        energyDensity (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f f x ≤
      gammaTwo (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f x :=
  gammaTwo_ge_neg_degree_mul_energy _ _ _
    (fun j _ y => ccmPrimePoleJumpRate_nonneg a j y) _ (ccmPrimePoleJumpDegree_le_envelope a) f x

end RHTower
