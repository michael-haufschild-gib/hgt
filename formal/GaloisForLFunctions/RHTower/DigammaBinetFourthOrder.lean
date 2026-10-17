import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation
import GaloisForLFunctions.HTGeometry.FrullaniIntegral
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# The digamma function to fourth order on the right half plane

For `Re w > 0` (`norm_digamma_sub_stirling_le`):

`|ψ(w) − log w + 1/(2w) + 1/(12 w²)| ≤ 1/(120 (Re w)⁴)`.

Proof.  Gauss's integral for `ψ`, Frullani's integral for `log w` and the Laplace transforms of `1`
and `t` give `ψ(w) − log w + 1/(2w) + 1/(12w²) = ∫_0^∞ ρ(t) e^{−wt} dt` with
`ρ(t) = t/12 − (1/(1 − e^{−t}) − 1/t − ½)` (`binetRemainder`).  In terms of `x = t/2`,
`ρ(t) = ((x²/3) sinh x − (x cosh x − sinh x))/(2x sinh x)`, and the hyperbolic inequalities
`(x²/3 − x⁴/45) sinh x ≤ x cosh x − sinh x ≤ (x²/3) sinh x` (`x ≥ 0`), proved by repeated
differentiation, give `0 ≤ ρ(t) ≤ t³/720`.  Finally `∫_0^∞ t³ e^{−σt} dt = 6/σ⁴`.
-/

open Real Set MeasureTheory Filter Topology

namespace RHTower.DigammaBinet

noncomputable section

/-! ### Monotonicity from a nonnegative derivative -/

/-- A function vanishing at `0` with nonnegative derivative on `(0, ∞)` is nonnegative on
`[0, ∞)`. -/
theorem nonneg_of_hasDerivAt_nonneg {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : ∀ x, 0 < x → 0 ≤ g' x) (h0 : g 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g x := by
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y _ => (hg y).continuousAt.continuousWithinAt) (fun y _ => (hg y).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    exact hg' y hy
  have := hmono (self_mem_Ici) hx hx
  rw [h0] at this
  exact this

/-! ### Hyperbolic inequalities -/

/-- `x cosh x − sinh x ≥ 0` for `x ≥ 0`. -/
theorem mul_cosh_sub_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * cosh x - sinh x := by
  refine nonneg_of_hasDerivAt_nonneg (g := fun y => y * cosh y - sinh y)
    (g' := fun y => y * sinh y) (fun y => ?_) (fun y hy => ?_) (by simp) hx
  · exact (((hasDerivAt_id' y).mul (hasDerivAt_cosh y)).sub (hasDerivAt_sinh y)).congr_deriv
      (by ring)
  · exact mul_nonneg hy.le (sinh_nonneg_iff.mpr hy.le)

/-- `x cosh x − sinh x ≤ (x²/3) sinh x` for `x ≥ 0`. -/
theorem mul_cosh_sub_sinh_le {x : ℝ} (hx : 0 ≤ x) : x * cosh x - sinh x ≤ x ^ 2 / 3 * sinh x := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun y => y ^ 2 / 3 * sinh y - (y * cosh y - sinh y))
    (g' := fun y => y / 3 * (y * cosh y - sinh y)) (fun y => ?_) (fun y hy => ?_) (by simp) hx
  · linarith
  · exact ((((hasDerivAt_pow 2 y).div_const 3).mul (hasDerivAt_sinh y)).sub
      (((hasDerivAt_id' y).mul (hasDerivAt_cosh y)).sub (hasDerivAt_sinh y))).congr_deriv
      (by norm_num; try ring)
  · exact mul_nonneg (by positivity) (mul_cosh_sub_sinh_nonneg hy.le)

/-- `(x² − 7) sinh x + 7x cosh x ≥ 0` for `x ≥ 0`. -/
theorem aux_m_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (x ^ 2 - 7) * sinh x + 7 * x * cosh x := by
  refine nonneg_of_hasDerivAt_nonneg (g := fun y => (y ^ 2 - 7) * sinh y + 7 * y * cosh y)
    (g' := fun y => 9 * y * sinh y + y ^ 2 * cosh y) (fun y => ?_) (fun y hy => ?_) (by simp) hx
  · exact ((((hasDerivAt_pow 2 y).sub_const 7).mul (hasDerivAt_sinh y)).add
      (((hasDerivAt_id' y).const_mul 7).mul (hasDerivAt_cosh y))).congr_deriv
      (by norm_num; try ring)
  · have := sinh_nonneg_iff.mpr hy.le
    have := cosh_pos y
    positivity

/-- `(1/3 + 4x²/45) sinh x − (x/3 − x³/45) cosh x ≥ 0` for `x ≥ 0`. -/
theorem aux_k_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (1 / 3 + 4 * x ^ 2 / 45) * sinh x - (x / 3 - x ^ 3 / 45) * cosh x := by
  refine nonneg_of_hasDerivAt_nonneg
    (g := fun y => (1 / 3 + 4 * y ^ 2 / 45) * sinh y - (y / 3 - y ^ 3 / 45) * cosh y)
    (g' := fun y => y / 45 * ((y ^ 2 - 7) * sinh y + 7 * y * cosh y)) (fun y => ?_)
    (fun y hy => ?_) (by simp) hx
  · have h1 := (((((hasDerivAt_pow 2 y).const_mul 4).div_const 45).const_add (1 / 3)).mul
      (hasDerivAt_sinh y)).sub
      ((((hasDerivAt_id' y).div_const 3).sub ((hasDerivAt_pow 3 y).div_const 45)).mul
        (hasDerivAt_cosh y))
    refine h1.congr_deriv ?_
    norm_num
    try ring
  · exact mul_nonneg (by positivity) (aux_m_nonneg hy.le)

/-- `(x²/3 − x⁴/45) sinh x ≤ x cosh x − sinh x` for `x ≥ 0`. -/
theorem le_mul_cosh_sub_sinh {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2 / 3 - x ^ 4 / 45) * sinh x ≤ x * cosh x - sinh x := by
  have h := nonneg_of_hasDerivAt_nonneg
    (g := fun y => y * cosh y - sinh y - (y ^ 2 / 3 - y ^ 4 / 45) * sinh y)
    (g' := fun y => y * ((1 / 3 + 4 * y ^ 2 / 45) * sinh y - (y / 3 - y ^ 3 / 45) * cosh y))
    (fun y => ?_) (fun y hy => ?_) (by simp) hx
  · linarith
  · exact ((((hasDerivAt_id' y).mul (hasDerivAt_cosh y)).sub (hasDerivAt_sinh y)).sub
      ((((hasDerivAt_pow 2 y).div_const 3).sub ((hasDerivAt_pow 4 y).div_const 45)).mul
        (hasDerivAt_sinh y))).congr_deriv (by norm_num; try ring)
  · exact mul_nonneg hy.le (aux_k_nonneg hy.le)

/-! ### The Binet remainder kernel -/

/-- `ρ(t) = t/12 − (1/(1 − e^{−t}) − 1/t − ½)`. -/
def binetRemainder (t : ℝ) : ℝ := t / 12 - (1 / (1 - Real.exp (-t)) - 1 / t - 1 / 2)

theorem binetRemainder_eq {t : ℝ} (ht : 0 < t) :
    binetRemainder t = ((t / 2) ^ 2 / 3 * sinh (t / 2) - (t / 2 * cosh (t / 2) - sinh (t / 2))) /
      (2 * (t / 2) * sinh (t / 2)) := by
  have hs : 0 < sinh (t / 2) := sinh_pos_iff.mpr (by linarith)
  have he : Real.exp (-t) = Real.exp (-(t / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 - Real.exp (-t) = 2 * sinh (t / 2) * Real.exp (-(t / 2)) := by
    rw [he, Real.sinh_eq]
    have : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [this]
  have hE : 0 < Real.exp (-(t / 2)) := Real.exp_pos _
  have hcosh : cosh (t / 2) = (Real.exp (t / 2) + Real.exp (-(t / 2))) / 2 := Real.cosh_eq _
  have hsinh : sinh (t / 2) = (Real.exp (t / 2) - Real.exp (-(t / 2))) / 2 := Real.sinh_eq _
  have hprod : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [binetRemainder, h1]
  field_simp
  rw [hcosh, hsinh]
  field_simp
  nlinarith [hprod]

/-- **`0 ≤ ρ(t) ≤ t³/720`** for `t > 0`. -/
theorem binetRemainder_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ binetRemainder t ∧ binetRemainder t ≤ t ^ 3 / 720 := by
  have hx : 0 < t / 2 := by linarith
  have hs : 0 < sinh (t / 2) := sinh_pos_iff.mpr hx
  have hden : 0 < 2 * (t / 2) * sinh (t / 2) := by positivity
  rw [binetRemainder_eq ht]
  constructor
  · exact div_nonneg (by linarith [mul_cosh_sub_sinh_le hx.le]) hden.le
  · rw [div_le_iff₀ hden]
    have := le_mul_cosh_sub_sinh hx.le
    nlinarith [this]

/-! ### The integral identity and the remainder bound -/

theorem ofReal_binetRemainder_mul_cexp (w : ℂ) {t : ℝ} (ht : 0 < t) :
    (binetRemainder t : ℂ) * Complex.exp (-(w * t)) =
      RHTower.digammaGaussIntegrand w t -
        (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t +
        1 / 2 * ((t : ℂ) ^ 0 * Complex.exp (-(w * t))) +
        1 / 12 * ((t : ℂ) ^ 1 * Complex.exp (-(w * t))) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hr : Real.exp (-t) < 1 := by
    have := Real.exp_lt_exp.mpr (show -t < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hd : (1 : ℂ) - ((Real.exp (-t) : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact_mod_cast (sub_pos.mpr hr).ne'
  have hd' : (1 : ℝ) - Real.exp (-t) ≠ 0 := (sub_pos.mpr hr).ne'
  have e1 : Complex.exp (-(t : ℂ)) = ((Real.exp (-t) : ℝ) : ℂ) := by push_cast; ring_nf
  have e2 : Complex.exp (-(1 * (t : ℂ))) = ((Real.exp (-t) : ℝ) : ℂ) := by push_cast; ring_nf
  have e3 : Complex.exp (-w * (t : ℂ)) = Complex.exp (-(w * t)) := by ring_nf
  rw [RHTower.digammaGaussIntegrand, e1, e2, e3, binetRemainder]
  set E := Complex.exp (-(w * t))
  push_cast
  field_simp
  ring

theorem binet_integral_identity {w : ℂ} (hw : 0 < w.re) :
    ∫ t in Ioi (0 : ℝ), (binetRemainder t : ℂ) * Complex.exp (-(w * t)) =
      Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2) := by
  have h1 : (0 : ℝ) < (1 : ℂ).re := by simp
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl _ hw
  have iG := RHTower.integrableOn_digammaGaussIntegrand hw
  have iF := GaloisForLFunctions.HTGeometry.integrableOn_frullani h1 hw
  have i0 := GaloisForLFunctions.HTGeometry.integrableOn_natPow_mul_cexp hw 0
  have i1 := GaloisForLFunctions.HTGeometry.integrableOn_natPow_mul_cexp hw 1
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => ofReal_binetRemainder_mul_cexp w ht)]
  have s1 : ∫ t in Ioi (0 : ℝ), (RHTower.digammaGaussIntegrand w t -
        (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t +
        1 / 2 * ((t : ℂ) ^ 0 * Complex.exp (-(w * t))) +
        1 / 12 * ((t : ℂ) ^ 1 * Complex.exp (-(w * t)))) =
      (∫ t in Ioi (0 : ℝ), (RHTower.digammaGaussIntegrand w t -
        (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t +
        1 / 2 * ((t : ℂ) ^ 0 * Complex.exp (-(w * t))))) +
      ∫ t in Ioi (0 : ℝ), 1 / 12 * ((t : ℂ) ^ 1 * Complex.exp (-(w * t))) :=
    integral_add ((iG.sub iF).add (i0.const_mul _)) (i1.const_mul _)
  have s2 : ∫ t in Ioi (0 : ℝ), (RHTower.digammaGaussIntegrand w t -
        (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t +
        1 / 2 * ((t : ℂ) ^ 0 * Complex.exp (-(w * t)))) =
      (∫ t in Ioi (0 : ℝ), (RHTower.digammaGaussIntegrand w t -
        (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t)) +
      ∫ t in Ioi (0 : ℝ), 1 / 2 * ((t : ℂ) ^ 0 * Complex.exp (-(w * t))) :=
    integral_add (iG.sub iF) (i0.const_mul _)
  have s3 : ∫ t in Ioi (0 : ℝ), (RHTower.digammaGaussIntegrand w t -
        (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t) =
      (∫ t in Ioi (0 : ℝ), RHTower.digammaGaussIntegrand w t) -
      ∫ t in Ioi (0 : ℝ), (Complex.exp (-(1 * (t : ℂ))) - Complex.exp (-(w * t))) / t :=
    integral_sub iG iF
  rw [s1, s2, s3, integral_const_mul, integral_const_mul,
    ← RHTower.digamma_eq_integral_gauss hw, GaloisForLFunctions.HTGeometry.integral_frullani h1 hw,
    GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp hw 0,
    GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp hw 1, Complex.log_one]
  field_simp
  ring

theorem integral_pow_three_mul_exp {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi (0 : ℝ), t ^ 3 * Real.exp (-(σ * t)) = 6 / σ ^ 4 := by
  have hc : 0 < (σ : ℂ).re := by simpa using hσ
  have h := GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp hc 3
  have e : (fun x : ℝ => (x : ℂ) ^ 3 * Complex.exp (-((σ : ℂ) * x))) =
      fun x : ℝ => ((x ^ 3 * Real.exp (-(σ * x)) : ℝ) : ℂ) := by
    funext x; push_cast; ring_nf
  rw [e, integral_complex_ofReal] at h
  have h6 : ((Nat.factorial 3 : ℕ) : ℂ) / (σ : ℂ) ^ (3 + 1) = ((6 / σ ^ 4 : ℝ) : ℂ) := by
    push_cast; norm_num [Nat.factorial]
  rw [h6] at h
  exact_mod_cast h

theorem integrableOn_pow_three_mul_exp {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ 3 * Real.exp (-(σ * t))) (Ioi 0) := by
  have hc : 0 < (σ : ℂ).re := by simpa using hσ
  have h := (GaloisForLFunctions.HTGeometry.integrableOn_natPow_mul_cexp hc 3).re
  refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
  rw [show (-((σ : ℂ) * (x : ℂ))) = ((-(σ * x) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

/-- **The fourth-order digamma estimate**: for `Re w > 0`,
`|ψ(w) − log w + 1/(2w) + 1/(12w²)| ≤ 1/(120 (Re w)⁴)`. -/
theorem norm_digamma_sub_stirling_le {w : ℂ} (hw : 0 < w.re) :
    ‖Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)‖ ≤ 1 / (120 * w.re ^ 4) := by
  rw [← binet_integral_identity hw]
  have hint : IntegrableOn (fun t : ℝ => t ^ 3 / 720 * Real.exp (-(w.re * t))) (Ioi 0) := by
    have := (integrableOn_pow_three_mul_exp hw).div_const 720
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    ring
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_mem measurableSet_Ioi).mono
    fun t ht => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      GaloisForLFunctions.HTGeometry.norm_cexp_neg_mul_ofReal]
    obtain ⟨h0, h1⟩ := binetRemainder_bounds (show 0 < t from ht)
    rw [abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  · have : ∫ t in Ioi (0 : ℝ), t ^ 3 / 720 * Real.exp (-(w.re * t)) =
        (∫ t in Ioi (0 : ℝ), t ^ 3 * Real.exp (-(w.re * t))) / 720 := by
      rw [← integral_div]; congr 1; funext t; ring
    rw [this, integral_pow_three_mul_exp hw]
    field_simp
    ring

end

end RHTower.DigammaBinet
