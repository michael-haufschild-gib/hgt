import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The reciprocal work and its fusion rigidity

The reciprocal work is `ω(t) = eᵗ + e⁻ᵗ - 2 = 2(cosh t - 1) = 4 sinh²(t/2)`.

* **Theorem 2.1, `(RFT.2)`**: `ω(x + y) + ω(x - y) = ω(x) ω(y) + 2ω(x) + 2ω(y)`.
* **Theorem 2.1, `(RFT.3)`–`(RFT.6)`**: a `C²` function `F` with `F(0) = 0`, the same fusion
  identity and `F''(0) = 2` equals `ω`.  With `f = 1 + F/2` the identity is d'Alembert's equation;
  differentiating twice in `y` at `0` gives `F'' = F + 2`, evenness gives `F'(0) = 0`, and
  `g = F - ω` solves `g'' = g`, `g(0) = g'(0) = 0`, so `g' ∓ g` vanish and `g = 0`.
* **`(RFT.14)`, `(RFT.27)`**: `t² ≤ ω(t)` for all `t`, and `ω(t) ≤ cosh(1) t²` for `|t| ≤ 1`,
  both from the cosine-hyperbolic power series.
-/

open Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ReciprocalFusion

/-- **`(RFT.1)`** the reciprocal work `ω(t) = eᵗ + e⁻ᵗ - 2`. -/
def reciprocalWork (t : ℝ) : ℝ := Real.exp t + Real.exp (-t) - 2

/-- `(RFT.1)`: `ω(t) = 2(cosh t - 1)`. -/
theorem reciprocalWork_eq_cosh (t : ℝ) : reciprocalWork t = 2 * (Real.cosh t - 1) := by
  rw [reciprocalWork, Real.cosh_eq]
  ring

/-- `(RFT.1)`: `ω(t) = 4 sinh²(t/2)`. -/
theorem reciprocalWork_eq_sinh_sq (t : ℝ) : reciprocalWork t = 4 * Real.sinh (t / 2) ^ 2 := by
  have h : Real.cosh t = Real.cosh (2 * (t / 2)) := by ring_nf
  rw [reciprocalWork_eq_cosh, h, Real.cosh_two_mul, Real.cosh_sq]
  ring

theorem reciprocalWork_zero : reciprocalWork 0 = 0 := by
  simp [reciprocalWork]; norm_num

theorem reciprocalWork_neg (t : ℝ) : reciprocalWork (-t) = reciprocalWork t := by
  rw [reciprocalWork, reciprocalWork, neg_neg]
  ring

theorem reciprocalWork_nonneg (t : ℝ) : 0 ≤ reciprocalWork t := by
  rw [reciprocalWork_eq_sinh_sq]
  positivity

/-- **Theorem 2.1, `(RFT.2)`**: the fusion identity. -/
theorem reciprocalWork_fusion (x y : ℝ) :
    reciprocalWork (x + y) + reciprocalWork (x - y) =
      reciprocalWork x * reciprocalWork y + 2 * reciprocalWork x + 2 * reciprocalWork y := by
  simp only [reciprocalWork, Real.exp_add, Real.exp_sub, Real.exp_neg, neg_add, neg_sub]
  have hx := Real.exp_pos x
  have hy := Real.exp_pos y
  field_simp
  ring

/-! ### `(RFT.14)` and `(RFT.27)` -/

/-- **`(RFT.14)`**: `ω(t) ≥ t²`, from `cosh t ≥ 1 + t²/2`. -/
theorem sq_le_reciprocalWork (t : ℝ) : t ^ 2 ≤ reciprocalWork t := by
  have h := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)) (Real.hasSum_cosh t)
  simp [Finset.sum_range_succ] at h
  rw [reciprocalWork_eq_cosh]
  linarith

theorem cosh_one_le_two : Real.cosh 1 ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]; norm_num
  linarith

/-- **`(RFT.27)`**: `ω(t) ≤ cosh(1) t²` for `|t| ≤ 1`. -/
theorem reciprocalWork_le_cosh_one_mul_sq {t : ℝ} (ht : |t| ≤ 1) :
    reciprocalWork t ≤ Real.cosh 1 * t ^ 2 := by
  have hsq : t ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact ht
  -- termwise `t^(2n)/(2n)! ≤ t² /(2n)!` for `n ≥ 1`
  have hA := (Real.hasSum_cosh t).sub (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  have hB := ((Real.hasSum_cosh 1).sub (hasSum_ite_eq (0 : ℕ) (1 : ℝ))).mul_left (t ^ 2)
  have hle := hasSum_le (fun n => ?_) hA hB
  · rw [reciprocalWork_eq_cosh]
    have h2 := cosh_one_le_two
    have hcpos : 0 ≤ Real.cosh 1 - 1 := by linarith [Real.one_le_cosh (1 : ℝ)]
    nlinarith [sq_nonneg t]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : n ≠ 0 := hn.ne'
      simp only [hn0, if_false, sub_zero, one_pow]
      have hpow : t ^ (2 * n) ≤ t ^ 2 := by
        have : t ^ (2 * n) = (t ^ 2) ^ n := by rw [pow_mul]
        rw [this]
        exact pow_le_of_le_one (sq_nonneg t) hsq hn0
      have hfac : (0 : ℝ) < ((2 * n).factorial : ℝ) := by positivity
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hpow hfac.le

theorem reciprocalWork_eq_zero_iff (t : ℝ) : reciprocalWork t = 0 ↔ t = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ reciprocalWork_zero⟩
  have := sq_le_reciprocalWork t
  rw [h] at this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg t))

/-! ### Theorem 2.1: rigidity -/

theorem hasDerivAt_reciprocalWork (t : ℝ) :
    HasDerivAt reciprocalWork (Real.exp t - Real.exp (-t)) t := by
  have h := ((Real.hasDerivAt_exp t).add (hasDerivAt_neg t).exp).sub_const 2
  show HasDerivAt (fun s => Real.exp s + Real.exp (-s) - 2) _ t
  exact h.congr_deriv (by ring)

theorem hasDerivAt_reciprocalWork_deriv (t : ℝ) :
    HasDerivAt (fun s => Real.exp s - Real.exp (-s)) (reciprocalWork t + 2) t := by
  have h := (Real.hasDerivAt_exp t).sub (hasDerivAt_neg t).exp
  exact h.congr_deriv (by simp only [reciprocalWork]; ring)

/-- A function `g` with `g'' = g` everywhere and `g(0) = g'(0) = 0` vanishes. -/
theorem eq_zero_of_deriv_deriv_eq_self {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g t) t) (h0 : g 0 = 0) (h0' : g' 0 = 0) : g = 0 := by
  -- `h₁ = g' - g` solves `h₁' = -h₁`; `h₂ = g' + g` solves `h₂' = h₂`
  have hconst₁ : ∀ t, Real.exp t * (g' t - g t) = 0 := by
    have hd : ∀ t, HasDerivAt (fun s => Real.exp s * (g' s - g s)) 0 t := fun t => by
      have h := (Real.hasDerivAt_exp t).mul ((hg' t).sub (hg t))
      exact h.congr_deriv (by simp only [Pi.sub_apply]; ring)
    intro t
    have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    rw [this, h0, h0']
    simp
  have hconst₂ : ∀ t, Real.exp (-t) * (g' t + g t) = 0 := by
    have hd : ∀ t, HasDerivAt (fun s => Real.exp (-s) * (g' s + g s)) 0 t := fun t => by
      have h := (hasDerivAt_neg t).exp.mul ((hg' t).add (hg t))
      exact h.congr_deriv (by simp only [Pi.add_apply]; ring)
    intro t
    have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    rw [this, h0, h0']
    simp
  funext t
  have h1 := hconst₁ t
  have h2 := hconst₂ t
  have he1 := Real.exp_pos t
  have he2 := Real.exp_pos (-t)
  have hz1 : g' t - g t = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h he1.ne'
    · exact h
  have hz2 : g' t + g t = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h he2.ne'
    · exact h
  simp only [Pi.zero_apply]
  linarith

/-- **Theorem 2.1, `(RFT.3)`–`(RFT.6)`**: a `C²` solution of the fusion identity with `F(0) = 0`
and `F''(0) = 2` is the reciprocal work. -/
theorem eq_reciprocalWork_of_fusion (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (h0 : F 0 = 0)
    (hfus : ∀ x y, F (x + y) + F (x - y) = F x * F y + 2 * F x + 2 * F y)
    (h2 : deriv (deriv F) 0 = 2) : F = reciprocalWork := by
  have hd1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv F) := by
    have := hF.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at this
  set D1 := deriv F
  set D2 := deriv D1
  have hD1 : ∀ t, HasDerivAt F (D1 t) t := fun t => (hd1 t).hasDerivAt
  have hD2 : ∀ t, HasDerivAt D1 (D2 t) t := fun t => (hd2 t).hasDerivAt
  -- evenness and `F'(0) = 0`
  have heven : ∀ y, F (-y) = F y := fun y => by
    have := hfus 0 y
    rw [zero_add, zero_sub, h0] at this
    linarith
  have hD1zero : D1 0 = 0 := by
    have hcomp : HasDerivAt (fun y => F (-y)) (D1 0 * (-1)) 0 := by
      have := (hD1 (-(0 : ℝ))).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      rw [neg_zero] at this
      exact this
    have hfun : (fun y => F (-y)) = F := funext heven
    rw [hfun] at hcomp
    have := (hD1 0).unique hcomp
    linarith
  -- first derivative of the identity in `y`
  have hfirst : ∀ x y, D1 (x + y) - D1 (x - y) = (F x + 2) * D1 y := fun x y => by
    have hL : HasDerivAt (fun y => F (x + y) + F (x - y)) (D1 (x + y) - D1 (x - y)) y := by
      have ha := (hD1 (x + y)).comp y ((hasDerivAt_id' y).const_add x)
      have hb := (hD1 (x - y)).comp y ((hasDerivAt_id' y).const_sub x)
      exact (ha.add hb).congr_deriv (by ring)
    have hR : HasDerivAt (fun y => F x * F y + 2 * F x + 2 * F y) ((F x + 2) * D1 y) y := by
      have := (((hD1 y).const_mul (F x)).add_const (2 * F x)).add ((hD1 y).const_mul 2)
      exact this.congr_deriv (by ring)
    have hfun : (fun y => F (x + y) + F (x - y)) = fun y => F x * F y + 2 * F x + 2 * F y :=
      funext (hfus x)
    rw [hfun] at hL
    exact hL.unique hR
  -- second derivative: `F'' = F + 2`
  have hsecond : ∀ x, D2 x = F x + 2 := fun x => by
    have hL : HasDerivAt (fun y => D1 (x + y) - D1 (x - y)) (D2 (x + 0) + D2 (x - 0)) 0 := by
      have ha := (hD2 (x + 0)).comp (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).const_add x)
      have hb := (hD2 (x - 0)).comp (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).const_sub x)
      exact (ha.sub hb).congr_deriv (by ring)
    have hR : HasDerivAt (fun y => (F x + 2) * D1 y) ((F x + 2) * D2 0) 0 :=
      (hD2 0).const_mul _
    have hfun : (fun y => D1 (x + y) - D1 (x - y)) = fun y => (F x + 2) * D1 y :=
      funext (hfirst x)
    rw [hfun] at hL
    have h := hL.unique hR
    rw [add_zero, sub_zero, h2] at h
    linarith
  -- uniqueness for `g = F - ω`
  have hg : ∀ t, HasDerivAt (fun s => F s - reciprocalWork s)
      (D1 t - (Real.exp t - Real.exp (-t))) t := fun t =>
    (hD1 t).sub (hasDerivAt_reciprocalWork t)
  have hg' : ∀ t, HasDerivAt (fun s => D1 s - (Real.exp s - Real.exp (-s)))
      (F t - reciprocalWork t) t := fun t => by
    have := (hD2 t).sub (hasDerivAt_reciprocalWork_deriv t)
    rw [hsecond t] at this
    exact this.congr_deriv (by ring)
  have hzero := eq_zero_of_deriv_deriv_eq_self hg hg'
    (by simp [h0, reciprocalWork_zero]) (by simp [hD1zero])
  funext t
  have := congrFun hzero t
  simp only [Pi.zero_apply] at this
  linarith

/-- **Theorem 2.1** (both directions): `ω` is the unique normalized `C²` solution. -/
theorem reciprocalWork_rigidity (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) :
    (F 0 = 0 ∧ (∀ x y, F (x + y) + F (x - y) = F x * F y + 2 * F x + 2 * F y) ∧
        deriv (deriv F) 0 = 2) ↔ F = reciprocalWork := by
  refine ⟨fun ⟨h0, hfus, h2⟩ => eq_reciprocalWork_of_fusion F hF h0 hfus h2, ?_⟩
  rintro rfl
  refine ⟨reciprocalWork_zero, reciprocalWork_fusion, ?_⟩
  have hderiv : deriv reciprocalWork = fun s => Real.exp s - Real.exp (-s) :=
    funext fun t => (hasDerivAt_reciprocalWork t).deriv
  rw [hderiv, (hasDerivAt_reciprocalWork_deriv 0).deriv, reciprocalWork_zero]
  norm_num

end GaloisForLFunctions.HTGeometry.ReciprocalFusion
