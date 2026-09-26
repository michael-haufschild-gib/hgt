import GaloisForLFunctions.RHTower.OrdinateInjectivity
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# Taylor positivity on a horizontal slice excludes ordinate collisions

Fix a height `t` and put `g_t(x) = ξ(½+x+it)·ξ(½−x+it)`, an entire function of `x`.  An off-line
zero `ρ = ½ + b + it` with `b ≠ 0` makes `g_t` vanish at the real point `|b| > 0`: one of the two
factors is `ξ(ρ)`.  The Hermitian reflection `ρ ↦ 1 − ρ̄` keeps the ordinate, so such a zero and its
partner form an ordinate collision.

If every Taylor coefficient of `g_t` at `0` is nonnegative (in the order of `ℂ`, i.e. real and
`≥ 0`), then `g_t` is positive on `(0, ∞)`: the Taylor series of an entire function converges at every
point, its terms are nonnegative there, and not all coefficients vanish because
`g_t(3/2 − it) = ξ(2)·ξ(2 − 2it) ≠ 0`.  Hence the slice at height `t` carries no off-line zero, and
nonnegativity at every height gives the Riemann hypothesis.

For real `x`, `g_t(x) = |ξ(½+x+it)|²` by the functional equation.  Its coefficients are the higher
Laguerre expressions of `Ξ` at `t` (`c₀ = Ξ(t)²`, `c₂ = Ξ'(t)² − Ξ(t)Ξ''(t)`, …), so this module
states the slice form of the ordinate-injectivity target as a coefficient-sign condition at one
height.
-/

open Complex
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The horizontal slice product at height `t`: `x ↦ ξ(½+x+it)·ξ(½−x+it)`. -/
def xiSliceProduct (t : ℝ) (x : ℂ) : ℂ :=
  xi (1 / 2 + x + t * I) * xi (1 / 2 - x + t * I)

theorem differentiable_xiSliceProduct (t : ℝ) : Differentiable ℂ (xiSliceProduct t) := by
  unfold xiSliceProduct
  exact (xi_differentiable.comp (by fun_prop)).mul (xi_differentiable.comp (by fun_prop))

/-- The Taylor coefficients of the slice product at `0`. -/
def xiSliceCoeff (t : ℝ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n (xiSliceProduct t) 0

/-- The Taylor series of the slice product converges to it at every point. -/
theorem hasSum_xiSliceCoeff (t : ℝ) (x : ℂ) :
    HasSum (fun n => xiSliceCoeff t n * x ^ n) (xiSliceProduct t x) := by
  have h := hasSum_taylorSeries_of_entire (differentiable_xiSliceProduct t) 0 x
  have e : (fun n => xiSliceCoeff t n * x ^ n) =
      fun n => (n.factorial : ℂ)⁻¹ • (x - 0) ^ n • iteratedDeriv n (xiSliceProduct t) 0 := by
    funext n
    simp only [xiSliceCoeff, sub_zero, smul_eq_mul]
    ring
  rw [e]
  exact h

/-- The slice product is not identically zero: at `x = 3/2 − it` it equals `ξ(2)·ξ(2 − 2it)`. -/
theorem xiSliceProduct_ne_zero (t : ℝ) : xiSliceProduct t (3 / 2 - t * I) ≠ 0 := by
  unfold xiSliceProduct
  have h1 : (1 : ℂ) / 2 + (3 / 2 - t * I) + t * I = 2 := by ring
  have h2 : (1 : ℂ) / 2 - (3 / 2 - t * I) + t * I = 1 - (2 - 2 * t * I) := by ring
  rw [h1, h2, xi_one_sub]
  refine mul_ne_zero (xi_ne_zero_of_one_lt_re (by norm_num)) (xi_ne_zero_of_one_lt_re ?_)
  simp

/-- An off-line zero at height `t` makes the slice product vanish at the positive real point
`|Re ρ − ½|`. -/
theorem xiSliceProduct_abs_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    xiSliceProduct ρ.im (|ρ.re - 1 / 2| : ℝ) = 0 := by
  unfold xiSliceProduct
  rcases le_or_gt 0 (ρ.re - 1 / 2) with hs | hs
  · have e : (1 : ℂ) / 2 + ((|ρ.re - 1 / 2| : ℝ) : ℂ) + (ρ.im : ℂ) * I = ρ := by
      rw [abs_of_nonneg hs]
      apply Complex.ext <;> simp
    rw [e, hρ, zero_mul]
  · have e : (1 : ℂ) / 2 - ((|ρ.re - 1 / 2| : ℝ) : ℂ) + (ρ.im : ℂ) * I = ρ := by
      rw [abs_of_neg hs]
      apply Complex.ext <;> simp
    rw [e, hρ, mul_zero]

/-- **Taylor positivity on a slice excludes off-line zeros at that height.**  If every Taylor
coefficient of `x ↦ ξ(½+x+it)·ξ(½−x+it)` at `0` is real and nonnegative, every zero of `ξ` with
ordinate `t` lies on the critical line. -/
theorem re_eq_half_of_xiSliceCoeff_nonneg {t : ℝ} (h : ∀ n, 0 ≤ xiSliceCoeff t n)
    {ρ : ℂ} (hρ : xi ρ = 0) (him : ρ.im = t) : ρ.re = 1 / 2 := by
  by_contra hne
  have hbpos : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set b : ℝ := |ρ.re - 1 / 2| with hb
  have hzero : xiSliceProduct t b = 0 := by
    have := xiSliceProduct_abs_eq_zero hρ
    rwa [him] at this
  have hbpow : ∀ n : ℕ, (0 : ℂ) ≤ (b : ℂ) ^ n := fun n => by
    have : (0 : ℝ) ≤ b ^ n := pow_nonneg hbpos.le n
    exact_mod_cast this
  have hterm : ∀ n, 0 ≤ xiSliceCoeff t n * (b : ℂ) ^ n := fun n => mul_nonneg (h n) (hbpow n)
  have hS := hasSum_xiSliceCoeff t b
  rw [hzero] at hS
  have hall : ∀ n, xiSliceCoeff t n = 0 := by
    intro n
    have hle := le_hasSum hS n (fun j _ => hterm j)
    have h0 := le_antisymm hle (hterm n)
    refine (mul_eq_zero.mp h0).resolve_right (pow_ne_zero _ ?_)
    exact_mod_cast hbpos.ne'
  apply xiSliceProduct_ne_zero t
  have hT := hasSum_xiSliceCoeff t (3 / 2 - t * I)
  simp only [hall, zero_mul] at hT
  exact hT.unique hasSum_zero

/-- Contrapositive: an off-line zero forces a Taylor coefficient of the slice product at its own
ordinate to leave the nonnegative cone. -/
theorem exists_not_nonneg_xiSliceCoeff_of_offLine {ρ : ℂ} (hρ : xi ρ = 0) (hne : ρ.re ≠ 1 / 2) :
    ∃ n, ¬ 0 ≤ xiSliceCoeff ρ.im n := by
  by_contra hc
  push Not at hc
  exact hne (re_eq_half_of_xiSliceCoeff_nonneg hc hρ rfl)

/-- **Slice positivity makes the height collision-free.**  Under Taylor positivity at height `t`,
all divisor copies at ordinate `t` sit at the same point. -/
theorem slice_collision_free_of_xiSliceCoeff_nonneg {t : ℝ} (h : ∀ n, 0 ≤ xiSliceCoeff t n)
    (q r : XiZeroCopy) (hq : (q.1 : ℂ).im = t) (hr : (r.1 : ℂ).im = t) :
    (q.1 : ℂ) = (r.1 : ℂ) := by
  apply Complex.ext
  · rw [re_eq_half_of_xiSliceCoeff_nonneg h (xi_xiZeroCopy_eq_zero q) hq,
      re_eq_half_of_xiSliceCoeff_nonneg h (xi_xiZeroCopy_eq_zero r) hr]
  · rw [hq, hr]

/-- **Slice positivity at every height gives the Riemann hypothesis.** -/
theorem riemannHypothesis_of_xiSliceCoeff_nonneg (h : ∀ t : ℝ, ∀ n, 0 ≤ xiSliceCoeff t n) :
    RiemannHypothesis :=
  riemannHypothesis_iff_xi_zero_re_eq_half.mpr fun ρ hρ =>
    re_eq_half_of_xiSliceCoeff_nonneg (h ρ.im) hρ rfl

end

end RHTower
