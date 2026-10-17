import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Linear effectivity is impossible at a real zero of `Ξ`

Let `γ₁` be a real zero of `Ξ` and `|ε| < 2`.  The density
`w_ε(x) = 2 cosh(x/2) + ε cos(γ₁ x)` is positive (`weightDensity_pos`).  Paired with a real test `h`,
`⟨w_ε, h⟩ = Re(ĥ(i/2) + ĥ(−i/2)) + ε Re ĥ(γ₁)` (`pairing_eq`), so it

* annihilates every repaired principal class, i.e. every `h` whose transform is
  `(z² + ¼) Ξ(z) q(z)` on the strip `|Im z| ≤ ½` (`pairing_eq_zero_of_isRepairedPrincipal`), and
* pairs with every primitive `h` (pole part `Re(ĥ(i/2) + ĥ(−i/2)) = 0`) with `Re ĥ(γ₁) ≠ 0` with
  either sign, as `ε` ranges over `(−2, 2)` (`exists_pairing_pos_and_neg`).

So positivity of a linear functional cannot separate effective classes from principal ones.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower.LinearEffectivity

noncomputable section

/-- The density `2 cosh(x/2) + ε cos(γ x)`. -/
def weightDensity (ε γ x : ℝ) : ℝ := 2 * Real.cosh (x / 2) + ε * Real.cos (γ * x)

/-- **Positivity** for `|ε| < 2`. -/
theorem weightDensity_pos {ε : ℝ} (hε : |ε| < 2) (γ x : ℝ) : 0 < weightDensity ε γ x := by
  have h1 : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have h2 : |ε * Real.cos (γ * x)| ≤ |ε| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h3 := neg_abs_le (ε * Real.cos (γ * x))
  unfold weightDensity
  linarith

/-- The pairing `⟨w_ε, h⟩ = ∫ h(x) (2 cosh(x/2) + ε cos(γ x)) dx`. -/
def pairing (ε γ : ℝ) (h : ℝ → ℝ) : ℝ := ∫ x, h x * weightDensity ε γ x

/-- The transform of a real test. -/
abbrev hat (h : ℝ → ℝ) (z : ℂ) : ℂ := paperFT (fun u => (h u : ℂ)) z

theorem cexp_I_mul (γ u : ℝ) : Complex.exp (I * γ * u) = Complex.exp (((γ * u : ℝ) : ℂ) * I) := by
  congr 1
  push_cast
  ring

theorem integrable_ofReal_mul_cexp {h : ℝ → ℝ} (hc : Continuous h) (hi : Integrable h) (γ : ℝ) :
    Integrable fun u : ℝ => (h u : ℂ) * Complex.exp (I * γ * u) := by
  refine hi.norm.mono' ((Complex.continuous_ofReal.comp hc).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_real, cexp_I_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem re_hat_real {h : ℝ → ℝ} (hc : Continuous h) (hi : Integrable h) (γ : ℝ) :
    (hat h γ).re = ∫ x, h x * Real.cos (γ * x) := by
  show (∫ u : ℝ, (h u : ℂ) * Complex.exp (I * γ * u)).re = _
  have hre := integral_re (integrable_ofReal_mul_cexp hc hi γ)
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  congr 1
  funext u
  rw [cexp_I_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **The pairing in transform coordinates**: `⟨w_ε, h⟩ = Re(ĥ(i/2) + ĥ(−i/2)) + ε Re ĥ(γ)`. -/
theorem pairing_eq {h : ℝ → ℝ} (hc : Continuous h)
    (hint : Integrable fun x => h x * Real.cosh (x / 2)) (ε γ : ℝ) :
    pairing ε γ h = (hat h (I / 2) + hat h (-I / 2)).re + ε * (hat h γ).re := by
  have hcosh1 : ∀ x : ℝ, 1 ≤ Real.cosh (x / 2) := fun x => Real.one_le_cosh _
  have hi : Integrable h := hint.norm.mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos _)]
    exact le_mul_of_one_le_right (abs_nonneg _) (hcosh1 x))
  have hexp : ∀ c : ℝ, c = 1 ∨ c = -1 → Integrable fun x => h x * Real.exp (c * x / 2) := by
    intro c hc1
    refine (hint.norm.const_mul 2).mono' (hc.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
    have h1 : Real.exp (c * x / 2) ≤ Real.exp (x / 2) + Real.exp (-(x / 2)) := by
      rcases hc1 with rfl | rfl
      · rw [one_mul]; linarith [Real.exp_pos (-(x / 2))]
      · rw [show -1 * x / 2 = -(x / 2) by ring]; linarith [Real.exp_pos (x / 2)]
    nlinarith [abs_nonneg (h x), Real.exp_pos (c * x / 2)]
  have hp := hexp 1 (Or.inl rfl)
  have hm := hexp (-1) (Or.inr rfl)
  have hcos : Integrable fun x => h x * Real.cos (γ * x) :=
    hi.norm.mono' (hc.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  have hpole : (hat h (I / 2) + hat h (-I / 2)).re =
      (∫ x, h x * Real.exp (1 * x / 2)) + ∫ x, h x * Real.exp (-1 * x / 2) := by
    unfold hat
    rw [WeilLevyPole.paperFT_ofReal_I_div_two, WeilLevyPole.paperFT_ofReal_neg_I_div_two,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_re, add_comm]
    congr 2 <;> funext x <;> congr 2 <;> ring
  have e : (fun x => h x * weightDensity ε γ x) =
      fun x => (h x * Real.exp (1 * x / 2) + h x * Real.exp (-1 * x / 2)) +
        ε * (h x * Real.cos (γ * x)) := by
    funext x
    rw [weightDensity, Real.cosh_eq, show -(x / 2) = -1 * x / 2 by ring,
      show x / 2 = 1 * x / 2 by ring]
    ring
  have hA : ∫ x, ((h x * Real.exp (1 * x / 2) + h x * Real.exp (-1 * x / 2)) +
      ε * (h x * Real.cos (γ * x))) =
      (∫ x, (h x * Real.exp (1 * x / 2) + h x * Real.exp (-1 * x / 2))) +
        ∫ x, ε * (h x * Real.cos (γ * x)) := integral_add (hp.add hm) (hcos.const_mul ε)
  have hB : ∫ x, (h x * Real.exp (1 * x / 2) + h x * Real.exp (-1 * x / 2)) =
      (∫ x, h x * Real.exp (1 * x / 2)) + ∫ x, h x * Real.exp (-1 * x / 2) := integral_add hp hm
  rw [pairing, e, hA, hB, integral_const_mul, hpole, re_hat_real hc hi]

/-- Repaired principal classes: transforms divisible by `(z² + ¼) Ξ(z)` on the strip. -/
def IsRepairedPrincipal (h : ℝ → ℝ) : Prop :=
  ∃ q : ℂ → ℂ, ∀ z : ℂ, |z.im| ≤ 1 / 2 → hat h z = (z ^ 2 + 1 / 4) * XiC z * q z

/-- **The positive measure annihilates every repaired principal class.** -/
theorem pairing_eq_zero_of_isRepairedPrincipal {h : ℝ → ℝ} (hc : Continuous h)
    (hint : Integrable fun x => h x * Real.cosh (x / 2)) (hP : IsRepairedPrincipal h) {γ₁ : ℝ}
    (hγ : XiC γ₁ = 0) (ε : ℝ) : pairing ε γ₁ h = 0 := by
  obtain ⟨q, hq⟩ := hP
  have h1 : hat h (I / 2) = 0 := by
    rw [hq _ (by norm_num)]
    have : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, zero_mul, zero_mul]
  have h2 : hat h (-I / 2) = 0 := by
    rw [hq _ (by norm_num)]
    have : (-I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
    rw [this, zero_mul, zero_mul]
  have h3 : hat h γ₁ = 0 := by
    rw [hq _ (by simp), hγ, mul_zero, zero_mul]
  rw [pairing_eq hc hint, h1, h2, h3]
  simp

/-- **Either sign on primitive classes**: a primitive real test with `Re ĥ(γ₁) ≠ 0` is paired
positively by some `w_ε` and negatively by another, `|ε| < 2`. -/
theorem exists_pairing_pos_and_neg {h : ℝ → ℝ} (hc : Continuous h)
    (hint : Integrable fun x => h x * Real.cosh (x / 2))
    (hprim : (hat h (I / 2) + hat h (-I / 2)).re = 0) {γ₁ : ℝ} (hγ : (hat h γ₁).re ≠ 0) :
    ∃ ε ε' : ℝ, |ε| < 2 ∧ |ε'| < 2 ∧ 0 < pairing ε γ₁ h ∧ pairing ε' γ₁ h < 0 := by
  have hp : ∀ ε, pairing ε γ₁ h = ε * (hat h γ₁).re := fun ε => by
    rw [pairing_eq hc hint, hprim, zero_add]
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · refine ⟨-1, 1, by norm_num, by norm_num, ?_, ?_⟩ <;> rw [hp] <;> linarith
  · refine ⟨1, -1, by norm_num, by norm_num, ?_, ?_⟩ <;> rw [hp] <;> linarith

end

end RHTower.LinearEffectivity
