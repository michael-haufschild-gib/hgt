import GaloisForLFunctions.RHTower.DirichletLMixedAdditiveZeroAbscissaLaw
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower

/-!
# The radial bound from a subpower coefficient bound

A subpower upper bound on the Hermitian mixed convolution coefficients forces a power bound on the
radial generating function: if `Re R_k(N) ≤ C (N+1)^α` then, at radius `e^{-x}` with `0 < x ≤ 1`,

```
‖(∑ a(N) e^{-Nx})^k‖² ≤ C · A(α) · x^{-(α+1)},
```

with the explicit constant `A(α) = 1 + e · 2^α · Γ(α+1)`.

This is the passage from the coefficient side to the analytic side for an arbitrary complex
coefficient sequence, obtained by feeding the corpus moment estimate for `∑ (N+1)^α e^{-Nx}` into
the Hermitian positivity bound.  It is the general-sequence form of the estimate that the
Möbius/Mertens module carries only for its own coefficients.
-/

open Complex
open scoped BigOperators

namespace RHTower

/-- The explicit Abel constant of the subpower radial bound. -/
noncomputable def mixedSubpowerAbelConstant (α : ℝ) : ℝ :=
  1 + Real.exp 1 * 2 ^ α * Real.Gamma (α + 1)

theorem mixedSubpowerAbelConstant_nonneg {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ mixedSubpowerAbelConstant α := by
  have hgamma : 0 ≤ Real.Gamma (α + 1) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  unfold mixedSubpowerAbelConstant
  positivity

/-- At radius `e^{-x}` the `N`-th power of the radius is `e^{-Nx}`. -/
theorem exp_neg_pow (x : ℝ) (N : ℕ) :
    (Real.exp (-x)) ^ N = Real.exp (-((N : ℝ) * x)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- **The radial bound.**  A subpower bound on the Hermitian mixed convolution coefficients gives a
power bound on the radial generating function, with an explicit constant. -/
theorem norm_sq_pow_le_of_mixedAdditiveConvolutionPower_subpower
    {a : ℕ → ℂ} {k : ℕ} {α C x : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hx : 0 < x) (hxOne : x ≤ 1)
    (ha : Summable fun N : ℕ => ‖a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N‖)
    (hupper : ∀ N : ℕ, (mixedAdditiveConvolutionPower a k N).re ≤ C * ((N : ℝ) + 1) ^ α) :
    ‖(∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) ^ k‖ ^ 2 ≤
      C * mixedSubpowerAbelConstant α * (1 / x) ^ (α + 1) := by
  obtain ⟨hsummable, hmoment⟩ := summable_natSucc_rpow_exp_neg_and_tsum_le hα hx
  have hrnonneg : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hshape : ∀ N : ℕ,
      (C * ((N : ℝ) + 1) ^ α) * (Real.exp (-x)) ^ N =
        C * (((N : ℝ) + 1) ^ α * Real.exp (-((N : ℝ) * x))) := by
    intro N
    rw [exp_neg_pow]
    ring
  have hb : Summable fun N : ℕ => (C * ((N : ℝ) + 1) ^ α) * (Real.exp (-x)) ^ N := by
    refine (hsummable.mul_left C).congr fun N => ?_
    rw [hshape N]
  have hR8 := norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper
    a k (Real.exp (-x)) hrnonneg ha (fun N => C * ((N : ℝ) + 1) ^ α) hupper hb
  have htsum : (∑' N : ℕ, (C * ((N : ℝ) + 1) ^ α) * (Real.exp (-x)) ^ N) =
      C * ∑' N : ℕ, ((N : ℝ) + 1) ^ α * Real.exp (-((N : ℝ) * x)) := by
    rw [← tsum_mul_left]
    exact tsum_congr hshape
  have hXge : (1 : ℝ) ≤ (1 / x) ^ (α + 1) := by
    apply Real.one_le_rpow
    · exact (one_le_div hx).2 hxOne
    · linarith
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hxOne
  have hgamma : 0 ≤ Real.Gamma (α + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hcoarse :
      (∑' N : ℕ, ((N : ℝ) + 1) ^ α * Real.exp (-((N : ℝ) * x))) ≤
        mixedSubpowerAbelConstant α * (1 / x) ^ (α + 1) := by
    have hfactor : 0 ≤ 2 ^ α * (1 / x) ^ (α + 1) * Real.Gamma (α + 1) := by positivity
    have hstep : 1 + Real.exp x * 2 ^ α * (1 / x) ^ (α + 1) * Real.Gamma (α + 1) ≤
        1 + Real.exp 1 * 2 ^ α * (1 / x) ^ (α + 1) * Real.Gamma (α + 1) := by
      nlinarith [hfactor, hexp]
    refine hmoment.trans (hstep.trans ?_)
    unfold mixedSubpowerAbelConstant
    have hpos : 0 ≤ Real.exp 1 * 2 ^ α * Real.Gamma (α + 1) := by positivity
    nlinarith [hXge, hpos]
  calc ‖(∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N) ^ k‖ ^ 2
      ≤ ∑' N : ℕ, (C * ((N : ℝ) + 1) ^ α) * (Real.exp (-x)) ^ N := hR8
    _ = C * ∑' N : ℕ, ((N : ℝ) + 1) ^ α * Real.exp (-((N : ℝ) * x)) := htsum
    _ ≤ C * (mixedSubpowerAbelConstant α * (1 / x) ^ (α + 1)) :=
        mul_le_mul_of_nonneg_left hcoarse hC
    _ = C * mixedSubpowerAbelConstant α * (1 / x) ^ (α + 1) := by ring

/-- **The radial bound on the series itself.**  Taking the `2k`-th root of the previous estimate
turns the subpower coefficient bound into `‖A(e^{-x})‖ = O(x^{-(α+1)/(2k)})`, the exponent `b` of
the card's `(R11)`. -/
theorem norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower
    {a : ℕ → ℂ} {k : ℕ} {α C x : ℝ} (hk : 0 < k) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hx : 0 < x) (hxOne : x ≤ 1)
    (ha : Summable fun N : ℕ => ‖a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N‖)
    (hupper : ∀ N : ℕ, (mixedAdditiveConvolutionPower a k N).re ≤ C * ((N : ℝ) + 1) ^ α) :
    ‖∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N‖ ≤
      (C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹) *
        (1 / x) ^ ((α + 1) / (2 * (k : ℝ))) := by
  set z : ℂ := ∑' N : ℕ, a N * ((Real.exp (-x) : ℝ) : ℂ) ^ N with hzdef
  set M : ℝ := C * mixedSubpowerAbelConstant α * (1 / x) ^ (α + 1) with hMdef
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  have hxinv : (0 : ℝ) ≤ 1 / x := by positivity
  have hM0 : 0 ≤ M := by
    have hrp : (0 : ℝ) ≤ (1 / x) ^ (α + 1) := Real.rpow_nonneg hxinv _
    have : 0 ≤ C * mixedSubpowerAbelConstant α := mul_nonneg hC hAbel
    exact mul_nonneg this hrp
  have hsq := norm_sq_pow_le_of_mixedAdditiveConvolutionPower_subpower hα hC hx hxOne ha hupper
  have hpow : ‖z‖ ^ (2 * k) ≤ M := by
    rw [← hzdef] at hsq
    rwa [norm_pow, ← pow_mul, mul_comm k 2] at hsq
  have hroot : ‖z‖ ≤ M ^ ((2 * (k : ℝ))⁻¹) := by
    have hcast : ‖z‖ ^ ((2 * (k : ℝ))) = ‖z‖ ^ (2 * k) := by
      rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hle : ‖z‖ ^ ((2 * (k : ℝ))) ≤ M := by rw [hcast]; exact hpow
    have hmono := Real.rpow_le_rpow (by positivity) hle (le_of_lt (inv_pos.mpr hkR))
    rwa [← Real.rpow_mul (norm_nonneg z), mul_inv_cancel₀ (ne_of_gt hkR),
      Real.rpow_one] at hmono
  refine hroot.trans (le_of_eq ?_)
  rw [hMdef, Real.mul_rpow (mul_nonneg hC hAbel) (Real.rpow_nonneg hxinv _),
    ← Real.rpow_mul hxinv]
  congr 1

end RHTower
