import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convolution

/-!+# Two-by-two positivity under integral composition

Log-concavity gives the four-point inequality for a translation kernel.
Integral composition preserves that inequality: the two-by-two determinant
is half the integral of a product of determinants with matching signs.
Only the four scalar integrals need to be integrable.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

/-- The multiplicative four-point inequality, including functions with zeros. -/
def LogFourPoint (f : ℝ → ℝ) : Prop :=
  ∀ x a b, 0 ≤ a → 0 ≤ b →
    f x * f (x + a + b) ≤ f (x + a) * f (x + b)

/-- Ordered two-by-two minors of a real kernel are nonnegative. -/
def KernelTP2 (K : ℝ → ℝ → ℝ) : Prop :=
  ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
    0 ≤ K x₁ y₁ * K x₂ y₂ - K x₁ y₂ * K x₂ y₁

/-- The two inner points of an interval dominate its endpoints for a concave function. -/
theorem ConcaveOn.add_four_point {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ s g) {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ∈ s) (hxab : x + a + b ∈ s) :
    g x + g (x + a + b) ≤ g (x + a) + g (x + b) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp only [ha0, hb0, add_zero, le_refl]
  have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  have hsum : b / (a + b) + a / (a + b) = 1 := by
    field_simp
    ring
  have hxa : b / (a + b) * x + a / (a + b) * (x + a + b) = x + a := by
    field_simp
    ring
  have hxb : a / (a + b) * x + b / (a + b) * (x + a + b) = x + b := by
    field_simp
    ring
  have h₁ := hg.2 hx hxab (div_nonneg hb hp.le) (div_nonneg ha hp.le) hsum
  have h₂ := hg.2 hx hxab (div_nonneg ha hp.le) (div_nonneg hb hp.le)
    (by simpa only [add_comm] using hsum)
  simp only [smul_eq_mul, hxa, hxb] at h₁ h₂
  have heq :
      b / (a + b) * g x + a / (a + b) * g (x + a + b) +
        (a / (a + b) * g x + b / (a + b) * g (x + a + b)) =
      g x + g (x + a + b) := by
    field_simp
    ring
  linarith only [h₁, h₂, heq]

theorem logFourPoint_of_concaveOn_log {f : ℝ → ℝ}
    (hf : ∀ x, 0 < f x)
    (hlog : ConcaveOn ℝ univ (fun x => Real.log (f x))) : LogFourPoint f := by
  intro x a b ha hb
  have h := ConcaveOn.add_four_point hlog ha hb (mem_univ x) (mem_univ (x + a + b))
  have he := Real.exp_le_exp.mpr h
  simpa only [Real.exp_add, Real.exp_log (hf x), Real.exp_log (hf (x + a + b)),
    Real.exp_log (hf (x + a)), Real.exp_log (hf (x + b))] using he

theorem kernelTP2_translation {f : ℝ → ℝ} (hf : LogFourPoint f) :
    KernelTP2 (fun x y => f (x - y)) := by
  intro x₁ x₂ y₁ y₂ hx hy
  have h := hf (x₁ - y₂) (x₂ - x₁) (y₂ - y₁)
    (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  rw [show x₁ - y₂ + (x₂ - x₁) + (y₂ - y₁) = x₂ - y₁ by ring,
    show x₁ - y₂ + (x₂ - x₁) = x₂ - y₂ by ring,
    show x₁ - y₂ + (y₂ - y₁) = x₁ - y₁ by ring] at h
  nlinarith only [h]

theorem logFourPoint_of_kernelTP2_translation {f : ℝ → ℝ}
    (hf : KernelTP2 (fun x y => f (x - y))) : LogFourPoint f := by
  intro x a b ha hb
  have h := hf x (x + a) (-b) 0 (by linarith) (by linarith)
  simp only [sub_zero, sub_neg_eq_add] at h
  nlinarith only [h]

theorem logFourPoint_reflect {f : ℝ → ℝ} (hf : LogFourPoint f) :
    LogFourPoint (fun x => f (-x)) := by
  intro x a b ha hb
  have h := hf (-(x + a + b)) a b ha hb
  rw [show -(x + a + b) + a + b = -x by ring,
    show -(x + a + b) + a = -(x + b) by ring,
    show -(x + a + b) + b = -(x + a) by ring] at h
  nlinarith only [h]

private theorem integral_four_products {a b c d : ℝ → ℝ}
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c) (hd : Integrable d) :
    (∫ u, ∫ v, a u * d v - b u * c v - c u * b v + d u * a v) =
      2 * ((∫ u, a u) * (∫ u, d u) - (∫ u, b u) * (∫ u, c u)) := by
  have hinner (u : ℝ) :
      (∫ v, a u * d v - b u * c v - c u * b v + d u * a v) =
        a u * (∫ v, d v) - b u * (∫ v, c v) -
          c u * (∫ v, b v) + d u * (∫ v, a v) := by
    rw [integral_add
      (f := fun v : ℝ => a u * d v - b u * c v - c u * b v)
      (g := fun v : ℝ => d u * a v)
      (((hd.const_mul (a u)).sub (hc.const_mul (b u))).sub (hb.const_mul (c u)))
      (ha.const_mul (d u)),
      integral_sub
      (f := fun v : ℝ => a u * d v - b u * c v)
      (g := fun v : ℝ => c u * b v)
      ((hd.const_mul (a u)).sub (hc.const_mul (b u))) (hb.const_mul (c u)),
      integral_sub
      (f := fun v : ℝ => a u * d v) (g := fun v : ℝ => b u * c v)
      (hd.const_mul (a u)) (hc.const_mul (b u))]
    simp only [integral_const_mul]
  simp_rw [hinner]
  rw [integral_add
    (f := fun u : ℝ => a u * (∫ v, d v) - b u * (∫ v, c v) - c u * (∫ v, b v))
    (g := fun u : ℝ => d u * (∫ v, a v))
    (((ha.mul_const _).sub (hb.mul_const _)).sub (hc.mul_const _)) (hd.mul_const _),
    integral_sub
    (f := fun u : ℝ => a u * (∫ v, d v) - b u * (∫ v, c v))
    (g := fun u : ℝ => c u * (∫ v, b v))
    ((ha.mul_const _).sub (hb.mul_const _)) (hc.mul_const _),
    integral_sub
    (f := fun u : ℝ => a u * (∫ v, d v)) (g := fun u : ℝ => b u * (∫ v, c v))
    (ha.mul_const _) (hb.mul_const _)]
  simp only [integral_mul_const]
  ring

/-- Integral composition preserves ordered two-by-two positivity. -/
theorem KernelTP2.integral_comp {A B : ℝ → ℝ → ℝ}
    (hA : KernelTP2 A) (hB : KernelTP2 B)
    (hAB : ∀ x y, Integrable (fun u => A x u * B u y)) :
    KernelTP2 (fun x y => ∫ u, A x u * B u y) := by
  intro x₁ x₂ y₁ y₂ hx hy
  have hsign (u v : ℝ) :
      0 ≤ (A x₁ u * A x₂ v - A x₁ v * A x₂ u) *
        (B u y₁ * B v y₂ - B u y₂ * B v y₁) := by
    rcases le_total u v with huv | hvu
    · exact mul_nonneg (hA x₁ x₂ u v hx huv) (hB u v y₁ y₂ huv hy)
    · have h := mul_nonneg (hA x₁ x₂ v u hx hvu) (hB v u y₁ y₂ hvu hy)
      have heq :
          (A x₁ u * A x₂ v - A x₁ v * A x₂ u) *
            (B u y₁ * B v y₂ - B u y₂ * B v y₁) =
          (A x₁ v * A x₂ u - A x₁ u * A x₂ v) *
            (B v y₁ * B u y₂ - B v y₂ * B u y₁) := by ring
      rw [heq]
      exact h
  have hnonneg : (0 : ℝ) ≤ ∫ u : ℝ, ∫ v : ℝ,
      (A x₁ u * B u y₁) * (A x₂ v * B v y₂) -
      (A x₁ u * B u y₂) * (A x₂ v * B v y₁) -
      (A x₂ u * B u y₁) * (A x₁ v * B v y₂) +
      (A x₂ u * B u y₂) * (A x₁ v * B v y₁) := by
    apply integral_nonneg
    intro u
    apply integral_nonneg
    intro v
    change (0 : ℝ) ≤
      (A x₁ u * B u y₁) * (A x₂ v * B v y₂) -
      (A x₁ u * B u y₂) * (A x₂ v * B v y₁) -
      (A x₂ u * B u y₁) * (A x₁ v * B v y₂) +
      (A x₂ u * B u y₂) * (A x₁ v * B v y₁)
    have heq :
        (A x₁ u * B u y₁) * (A x₂ v * B v y₂) -
        (A x₁ u * B u y₂) * (A x₂ v * B v y₁) -
        (A x₂ u * B u y₁) * (A x₁ v * B v y₂) +
        (A x₂ u * B u y₂) * (A x₁ v * B v y₁) =
        (A x₁ u * A x₂ v - A x₁ v * A x₂ u) *
          (B u y₁ * B v y₂ - B u y₂ * B v y₁) := by ring
    rw [heq]
    exact hsign u v
  rw [integral_four_products (hAB x₁ y₁) (hAB x₁ y₂)
    (hAB x₂ y₁) (hAB x₂ y₂)] at hnonneg
  linarith only [hnonneg]

/-- The four-point inequality survives convolution, without separate integrability
of the two factors. -/
theorem logFourPoint_convolution {f g : ℝ → ℝ}
    (hf : LogFourPoint f) (hg : LogFourPoint g)
    (hfg : ∀ x, Integrable (fun u => f (x - u) * g u)) :
    LogFourPoint (fun x => ∫ u, f (x - u) * g u) := by
  have hint (x y : ℝ) : Integrable (fun u => f (x - u) * g (u - y)) := by
    have h := (hfg (x - y)).comp_sub_right y
    have heq : (fun u : ℝ => f (x - y - (u - y)) * g (u - y)) =
        fun u : ℝ => f (x - u) * g (u - y) := by
      funext u
      congr 2
      ring
    rw [heq] at h
    exact h
  have heq (x y : ℝ) :
      (∫ u, f (x - u) * g (u - y)) = ∫ u, f (x - y - u) * g u := by
    calc
      _ = ∫ u : ℝ, f (x - y - (u - y)) * g (u - y) := by
        apply integral_congr_ae
        filter_upwards with u
        congr 2
        ring
      _ = _ := integral_sub_right_eq_self (μ := volume)
        (fun u : ℝ => f (x - y - u) * g u) y
  have h := KernelTP2.integral_comp (kernelTP2_translation hf)
    (kernelTP2_translation hg) hint
  simp_rw [heq] at h
  exact logFourPoint_of_kernelTP2_translation h

end

end GaloisForLFunctions.HTGeometry
