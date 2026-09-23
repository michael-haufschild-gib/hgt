import GaloisForLFunctions.HTGeometry.NonstationaryPhaseLowerBound
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The product of two oscillatory two-branch representations

A solution of a second-order oscillatory equation written in its two-branch form is

```text
U(x) = g₁(x) cos(c Φ(x)) + g₂(x) sin(c Φ(x)) .
```

Multiplying two such representations and applying the product-to-sum identities turns the product
into four oscillations, carried by the **difference** phase `Φ − Ψ` and the **sum** phase `Φ + Ψ`:

```text
U V = ½[ (g₁g₃ + g₂g₄) cos(c(Φ−Ψ)) + (g₁g₃ − g₂g₄) cos(c(Φ+Ψ))
       + (g₂g₃ − g₁g₄) sin(c(Φ−Ψ)) + (g₂g₃ + g₁g₄) sin(c(Φ+Ψ)) ] .
```

If both combined phases are nonstationary — `|Φ' ∓ Ψ'| ≥ m` — each of the four terms is `O(1/(cm))`
by the first-derivative test, so the whole product integral is.  This is the mechanism by which two
dilated radial oscillations with separated indices have a negligible overlap: the difference phase's
speed is bounded below by a multiple of the index gap, and the sum phase's by the index sum.

The estimate is packaged through one budget functional, so the four contributions read off the same
formula with different weights and different phases.
-/

open Set MeasureTheory intervalIntegral Filter

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- The endpoint-plus-variation budget of one oscillatory term. -/
noncomputable def oscBudget (a b m : ℝ) (g g' Θ'' : ℝ → ℝ) : ℝ :=
  |g a| / m + |g b| / m + ∫ x in a..b, (|g' x| / m + |g x| * |Θ'' x| / m ^ (2 : ℕ))

theorem oscBudget_nonneg {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m) (g g' Θ'' : ℝ → ℝ) :
    0 ≤ oscBudget a b m g g' Θ'' := by
  refine add_nonneg (add_nonneg (by positivity) (by positivity)) ?_
  refine intervalIntegral.integral_nonneg hab fun x _ => ?_
  positivity

/-- The first-derivative test, in budget form. -/
theorem abs_integral_mul_cos_phase_le' {a b c φ m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g g' ξ ξ' ξ'' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ')
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hξ''c : Continuous ξ'')
    (hlow : ∀ x, m ≤ |ξ' x|) :
    |∫ x in a..b, g x * Real.cos (c * ξ x + φ)| ≤ oscBudget a b m g g' ξ'' / c :=
  abs_integral_mul_cos_phase_le hab hc hm hg hgc hg'c hξ hξ'c hξ' hξ''c hlow

/-- The same test for a sine oscillation: a sine is a cosine with a shifted constant phase. -/
theorem abs_integral_mul_sin_phase_le {a b c φ m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g g' ξ ξ' ξ'' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g) (hg'c : Continuous g')
    (hξ : ∀ x, HasDerivAt ξ (ξ' x) x) (hξ'c : Continuous ξ')
    (hξ' : ∀ x, HasDerivAt ξ' (ξ'' x) x) (hξ''c : Continuous ξ'')
    (hlow : ∀ x, m ≤ |ξ' x|) :
    |∫ x in a..b, g x * Real.sin (c * ξ x + φ)| ≤ oscBudget a b m g g' ξ'' / c := by
  have hshift : ∀ x : ℝ, g x * Real.sin (c * ξ x + φ)
      = g x * Real.cos (c * ξ x + (φ - Real.pi / 2)) := by
    intro x
    have h : Real.sin (c * ξ x + φ) = Real.cos (c * ξ x + φ - Real.pi / 2) := by
      rw [Real.cos_sub]
      simp
    rw [h]
    ring_nf
  have heq : (∫ x in a..b, g x * Real.sin (c * ξ x + φ))
      = ∫ x in a..b, g x * Real.cos (c * ξ x + (φ - Real.pi / 2)) :=
    intervalIntegral.integral_congr fun x _ => hshift x
  rw [heq]
  exact abs_integral_mul_cos_phase_le hab hc hm hg hgc hg'c hξ hξ'c hξ' hξ''c hlow

/-! ## The product-to-sum expansion -/

/-- **Two-branch product expansion.**  A product of two two-branch oscillations is a combination of
four oscillations carried by the sum and difference phases. -/
theorem twoBranch_product_eq (c : ℝ) (g₁ g₂ g₃ g₄ Φ Ψ : ℝ → ℝ) (x : ℝ) :
    (g₁ x * Real.cos (c * Φ x) + g₂ x * Real.sin (c * Φ x))
        * (g₃ x * Real.cos (c * Ψ x) + g₄ x * Real.sin (c * Ψ x))
      = 1 / 2 * ((g₁ x * g₃ x + g₂ x * g₄ x) * Real.cos (c * (Φ x - Ψ x)))
        + 1 / 2 * ((g₁ x * g₃ x - g₂ x * g₄ x) * Real.cos (c * (Φ x + Ψ x)))
        + 1 / 2 * ((g₂ x * g₃ x - g₁ x * g₄ x) * Real.sin (c * (Φ x - Ψ x)))
        + 1 / 2 * ((g₂ x * g₃ x + g₁ x * g₄ x) * Real.sin (c * (Φ x + Ψ x))) := by
  have hsub : c * (Φ x - Ψ x) = c * Φ x - c * Ψ x := by ring
  have hadd : c * (Φ x + Ψ x) = c * Φ x + c * Ψ x := by ring
  rw [hsub, hadd, Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
  ring

/-! ## Four oscillations carried by two nonstationary phases -/

theorem integral_add₄ {a b : ℝ} {f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (h₁ : IntervalIntegrable f₁ volume a b) (h₂ : IntervalIntegrable f₂ volume a b)
    (h₃ : IntervalIntegrable f₃ volume a b) (h₄ : IntervalIntegrable f₄ volume a b) :
    (∫ x in a..b, (f₁ x + f₂ x + f₃ x + f₄ x))
      = (∫ x in a..b, f₁ x) + (∫ x in a..b, f₂ x) + (∫ x in a..b, f₃ x)
        + ∫ x in a..b, f₄ x := by
  have e1 : (∫ x in a..b, (f₁ x + f₂ x + f₃ x + f₄ x))
      = (∫ x in a..b, (f₁ x + f₂ x + f₃ x)) + ∫ x in a..b, f₄ x :=
    intervalIntegral.integral_add ((h₁.add h₂).add h₃) h₄
  have e2 : (∫ x in a..b, (f₁ x + f₂ x + f₃ x))
      = (∫ x in a..b, (f₁ x + f₂ x)) + ∫ x in a..b, f₃ x :=
    intervalIntegral.integral_add (h₁.add h₂) h₃
  have e3 : (∫ x in a..b, (f₁ x + f₂ x)) = (∫ x in a..b, f₁ x) + ∫ x in a..b, f₂ x :=
    intervalIntegral.integral_add h₁ h₂
  rw [e1, e2, e3]

/-- **Four oscillations, two nonstationary phases.**  Each of the four weights pays its own
endpoint-and-variation budget against the phase it rides, and the total is `1/c` times their
sum. -/
theorem abs_integral_fourOsc_le
    {a b c m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {w₁ w₂ w₃ w₄ w₁' w₂' w₃' w₄' D S D' S' D'' S'' : ℝ → ℝ}
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₁c : Continuous w₁) (hw₁'c : Continuous w₁')
    (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x) (hw₂c : Continuous w₂) (hw₂'c : Continuous w₂')
    (hw₃ : ∀ x, HasDerivAt w₃ (w₃' x) x) (hw₃c : Continuous w₃) (hw₃'c : Continuous w₃')
    (hw₄ : ∀ x, HasDerivAt w₄ (w₄' x) x) (hw₄c : Continuous w₄) (hw₄'c : Continuous w₄')
    (hD : ∀ x, HasDerivAt D (D' x) x) (hD'c : Continuous D')
    (hDd : ∀ x, HasDerivAt D' (D'' x) x) (hD''c : Continuous D'')
    (hS : ∀ x, HasDerivAt S (S' x) x) (hS'c : Continuous S')
    (hSd : ∀ x, HasDerivAt S' (S'' x) x) (hS''c : Continuous S'')
    (hDlow : ∀ x, m ≤ |D' x|) (hSlow : ∀ x, m ≤ |S' x|) :
    |∫ x in a..b, (w₁ x * Real.cos (c * D x) + w₂ x * Real.cos (c * S x)
        + w₃ x * Real.sin (c * D x) + w₄ x * Real.sin (c * S x))|
      ≤ (oscBudget a b m w₁ w₁' D'' + oscBudget a b m w₂ w₂' S''
        + oscBudget a b m w₃ w₃' D'' + oscBudget a b m w₄ w₄' S'') / c := by
  have hDc : Continuous D := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hSc : Continuous S := continuous_iff_continuousAt.mpr fun x => (hS x).continuousAt
  have hi₁ : IntervalIntegrable (fun x => w₁ x * Real.cos (c * D x)) volume a b :=
    (hw₁c.mul (Real.continuous_cos.comp (hDc.const_smul c))).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun x => w₂ x * Real.cos (c * S x)) volume a b :=
    (hw₂c.mul (Real.continuous_cos.comp (hSc.const_smul c))).intervalIntegrable a b
  have hi₃ : IntervalIntegrable (fun x => w₃ x * Real.sin (c * D x)) volume a b :=
    (hw₃c.mul (Real.continuous_sin.comp (hDc.const_smul c))).intervalIntegrable a b
  have hi₄ : IntervalIntegrable (fun x => w₄ x * Real.sin (c * S x)) volume a b :=
    (hw₄c.mul (Real.continuous_sin.comp (hSc.const_smul c))).intervalIntegrable a b
  rw [integral_add₄ hi₁ hi₂ hi₃ hi₄]
  have hz : ∀ (f Θ : ℝ → ℝ) (x : ℝ), f x * Real.cos (c * Θ x) = f x * Real.cos (c * Θ x + 0) := by
    intro f Θ x
    rw [add_zero]
  have hzs : ∀ (f Θ : ℝ → ℝ) (x : ℝ), f x * Real.sin (c * Θ x) = f x * Real.sin (c * Θ x + 0) := by
    intro f Θ x
    rw [add_zero]
  have h₁ : |∫ x in a..b, w₁ x * Real.cos (c * D x)| ≤ oscBudget a b m w₁ w₁' D'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hz w₁ D x]
    exact abs_integral_mul_cos_phase_le hab hc hm hw₁ hw₁c hw₁'c hD hD'c hDd hD''c hDlow
  have h₂ : |∫ x in a..b, w₂ x * Real.cos (c * S x)| ≤ oscBudget a b m w₂ w₂' S'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hz w₂ S x]
    exact abs_integral_mul_cos_phase_le hab hc hm hw₂ hw₂c hw₂'c hS hS'c hSd hS''c hSlow
  have h₃ : |∫ x in a..b, w₃ x * Real.sin (c * D x)| ≤ oscBudget a b m w₃ w₃' D'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hzs w₃ D x]
    exact abs_integral_mul_sin_phase_le hab hc hm hw₃ hw₃c hw₃'c hD hD'c hDd hD''c hDlow
  have h₄ : |∫ x in a..b, w₄ x * Real.sin (c * S x)| ≤ oscBudget a b m w₄ w₄' S'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hzs w₄ S x]
    exact abs_integral_mul_sin_phase_le hab hc hm hw₄ hw₄c hw₄'c hS hS'c hSd hS''c hSlow
  have hsplit : ((oscBudget a b m w₁ w₁' D'' + oscBudget a b m w₂ w₂' S''
        + oscBudget a b m w₃ w₃' D'' + oscBudget a b m w₄ w₄' S'') / c)
      = oscBudget a b m w₁ w₁' D'' / c + oscBudget a b m w₂ w₂' S'' / c
        + oscBudget a b m w₃ w₃' D'' / c + oscBudget a b m w₄ w₄' S'' / c := by
    ring
  rw [hsplit]
  calc |(∫ x in a..b, w₁ x * Real.cos (c * D x)) + (∫ x in a..b, w₂ x * Real.cos (c * S x))
        + (∫ x in a..b, w₃ x * Real.sin (c * D x)) + ∫ x in a..b, w₄ x * Real.sin (c * S x)|
      ≤ |(∫ x in a..b, w₁ x * Real.cos (c * D x)) + (∫ x in a..b, w₂ x * Real.cos (c * S x))
          + ∫ x in a..b, w₃ x * Real.sin (c * D x)|
        + |∫ x in a..b, w₄ x * Real.sin (c * S x)| := abs_add_le _ _
    _ ≤ (|(∫ x in a..b, w₁ x * Real.cos (c * D x)) + ∫ x in a..b, w₂ x * Real.cos (c * S x)|
          + |∫ x in a..b, w₃ x * Real.sin (c * D x)|)
        + |∫ x in a..b, w₄ x * Real.sin (c * S x)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ((|∫ x in a..b, w₁ x * Real.cos (c * D x)| + |∫ x in a..b, w₂ x * Real.cos (c * S x)|)
          + |∫ x in a..b, w₃ x * Real.sin (c * D x)|)
        + |∫ x in a..b, w₄ x * Real.sin (c * S x)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ oscBudget a b m w₁ w₁' D'' / c + oscBudget a b m w₂ w₂' S'' / c
        + oscBudget a b m w₃ w₃' D'' / c + oscBudget a b m w₄ w₄' S'' / c := by
        linarith [h₁, h₂, h₃, h₄]

/-! ## The product of two two-branch oscillations -/

/-- **The two-branch product estimate.**  If both the sum and the difference of the two phases are
nonstationary, the overlap of two two-branch oscillations is `O(1/c)` with the four explicit
budgets. -/
theorem abs_integral_twoBranch_product_le
    {a b c m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g₁ g₂ g₃ g₄ g₁' g₂' g₃' g₄' Φ Ψ Φ' Ψ' Φ'' Ψ'' : ℝ → ℝ}
    (hg₁ : ∀ x, HasDerivAt g₁ (g₁' x) x) (hg₁c : Continuous g₁) (hg₁'c : Continuous g₁')
    (hg₂ : ∀ x, HasDerivAt g₂ (g₂' x) x) (hg₂c : Continuous g₂) (hg₂'c : Continuous g₂')
    (hg₃ : ∀ x, HasDerivAt g₃ (g₃' x) x) (hg₃c : Continuous g₃) (hg₃'c : Continuous g₃')
    (hg₄ : ∀ x, HasDerivAt g₄ (g₄' x) x) (hg₄c : Continuous g₄) (hg₄'c : Continuous g₄')
    (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) (hΦ'c : Continuous Φ')
    (hΦd : ∀ x, HasDerivAt Φ' (Φ'' x) x) (hΦ''c : Continuous Φ'')
    (hΨ : ∀ x, HasDerivAt Ψ (Ψ' x) x) (hΨ'c : Continuous Ψ')
    (hΨd : ∀ x, HasDerivAt Ψ' (Ψ'' x) x) (hΨ''c : Continuous Ψ'')
    (hdiff : ∀ x, m ≤ |Φ' x - Ψ' x|) (hsum : ∀ x, m ≤ |Φ' x + Ψ' x|) :
    |∫ x in a..b, (g₁ x * Real.cos (c * Φ x) + g₂ x * Real.sin (c * Φ x))
        * (g₃ x * Real.cos (c * Ψ x) + g₄ x * Real.sin (c * Ψ x))|
      ≤ (oscBudget a b m (fun x => 1 / 2 * (g₁ x * g₃ x + g₂ x * g₄ x))
            (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
            (fun x => Φ'' x - Ψ'' x)
        + oscBudget a b m (fun x => 1 / 2 * (g₁ x * g₃ x - g₂ x * g₄ x))
            (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
            (fun x => Φ'' x + Ψ'' x)
        + oscBudget a b m (fun x => 1 / 2 * (g₂ x * g₃ x - g₁ x * g₄ x))
            (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
            (fun x => Φ'' x - Ψ'' x)
        + oscBudget a b m (fun x => 1 / 2 * (g₂ x * g₃ x + g₁ x * g₄ x))
            (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
            (fun x => Φ'' x + Ψ'' x)) / c := by
  have hrw : ∀ x : ℝ,
      (g₁ x * Real.cos (c * Φ x) + g₂ x * Real.sin (c * Φ x))
        * (g₃ x * Real.cos (c * Ψ x) + g₄ x * Real.sin (c * Ψ x))
      = (fun y => 1 / 2 * (g₁ y * g₃ y + g₂ y * g₄ y)) x
          * Real.cos (c * (fun y => Φ y - Ψ y) x)
        + (fun y => 1 / 2 * (g₁ y * g₃ y - g₂ y * g₄ y)) x
          * Real.cos (c * (fun y => Φ y + Ψ y) x)
        + (fun y => 1 / 2 * (g₂ y * g₃ y - g₁ y * g₄ y)) x
          * Real.sin (c * (fun y => Φ y - Ψ y) x)
        + (fun y => 1 / 2 * (g₂ y * g₃ y + g₁ y * g₄ y)) x
          * Real.sin (c * (fun y => Φ y + Ψ y) x) := by
    intro x
    rw [twoBranch_product_eq c g₁ g₂ g₃ g₄ Φ Ψ x]
    ring
  rw [intervalIntegral.integral_congr fun x _ => hrw x]
  refine abs_integral_fourOsc_le hab hc hm
    (w₁' := fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
    (w₂' := fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
    (w₃' := fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
    (w₄' := fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
    (D' := fun x => Φ' x - Ψ' x) (S' := fun x => Φ' x + Ψ' x)
    (D'' := fun x => Φ'' x - Ψ'' x) (S'' := fun x => Φ'' x + Ψ'' x)
    (fun x => (((hg₁ x).mul (hg₃ x)).add ((hg₂ x).mul (hg₄ x))).const_mul (1 / 2))
    ((hg₁c.mul hg₃c).add (hg₂c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₁'c.mul hg₃c).add (hg₁c.mul hg₃'c)).add
      ((hg₂'c.mul hg₄c).add (hg₂c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x => (((hg₁ x).mul (hg₃ x)).sub ((hg₂ x).mul (hg₄ x))).const_mul (1 / 2))
    ((hg₁c.mul hg₃c).sub (hg₂c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₁'c.mul hg₃c).add (hg₁c.mul hg₃'c)).sub
      ((hg₂'c.mul hg₄c).add (hg₂c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x => (((hg₂ x).mul (hg₃ x)).sub ((hg₁ x).mul (hg₄ x))).const_mul (1 / 2))
    ((hg₂c.mul hg₃c).sub (hg₁c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₂'c.mul hg₃c).add (hg₂c.mul hg₃'c)).sub
      ((hg₁'c.mul hg₄c).add (hg₁c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x => (((hg₂ x).mul (hg₃ x)).add ((hg₁ x).mul (hg₄ x))).const_mul (1 / 2))
    ((hg₂c.mul hg₃c).add (hg₁c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₂'c.mul hg₃c).add (hg₂c.mul hg₃'c)).add
      ((hg₁'c.mul hg₄c).add (hg₁c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x => (hΦ x).sub (hΨ x)) (hΦ'c.sub hΨ'c)
    (fun x => (hΦd x).sub (hΨd x)) (hΦ''c.sub hΨ''c)
    (fun x => (hΦ x).add (hΨ x)) (hΦ'c.add hΨ'c)
    (fun x => (hΦd x).add (hΨd x)) (hΦ''c.add hΨ''c)
    hdiff hsum

/-! ## Interval versions -/

/-- The sine test, with every hypothesis local to the interval. -/
theorem abs_integral_mul_sin_phase_le_on {a b c φ m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g g' ξ ξ' ξ'' : ℝ → ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hgc : ContinuousOn g (Icc a b)) (hg'c : ContinuousOn g' (Icc a b))
    (hξ : ∀ x ∈ Icc a b, HasDerivAt ξ (ξ' x) x) (hξ'c : ContinuousOn ξ' (Icc a b))
    (hξ'd : ∀ x ∈ Icc a b, HasDerivAt ξ' (ξ'' x) x) (hξ''c : ContinuousOn ξ'' (Icc a b))
    (hlow : ∀ x ∈ Icc a b, m ≤ |ξ' x|) :
    |∫ x in a..b, g x * Real.sin (c * ξ x + φ)| ≤ oscBudget a b m g g' ξ'' / c := by
  have hshift : ∀ x : ℝ, g x * Real.sin (c * ξ x + φ)
      = g x * Real.cos (c * ξ x + (φ - Real.pi / 2)) := by
    intro x
    have h : Real.sin (c * ξ x + φ) = Real.cos (c * ξ x + φ - Real.pi / 2) := by
      rw [Real.cos_sub]
      simp
    rw [h]
    ring_nf
  have heq : (∫ x in a..b, g x * Real.sin (c * ξ x + φ))
      = ∫ x in a..b, g x * Real.cos (c * ξ x + (φ - Real.pi / 2)) :=
    intervalIntegral.integral_congr fun x _ => hshift x
  rw [heq]
  exact abs_integral_mul_cos_phase_le_on hab hc hm hg hgc hg'c hξ hξ'c hξ'd hξ''c hlow

/-- Four oscillations, with both phases smooth and nonstationary only on the interval. -/
theorem abs_integral_fourOsc_le_on
    {a b c m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {w₁ w₂ w₃ w₄ w₁' w₂' w₃' w₄' D S D' S' D'' S'' : ℝ → ℝ}
    (hw₁ : ∀ x ∈ Icc a b, HasDerivAt w₁ (w₁' x) x)
    (hw₁c : ContinuousOn w₁ (Icc a b)) (hw₁'c : ContinuousOn w₁' (Icc a b))
    (hw₂ : ∀ x ∈ Icc a b, HasDerivAt w₂ (w₂' x) x)
    (hw₂c : ContinuousOn w₂ (Icc a b)) (hw₂'c : ContinuousOn w₂' (Icc a b))
    (hw₃ : ∀ x ∈ Icc a b, HasDerivAt w₃ (w₃' x) x)
    (hw₃c : ContinuousOn w₃ (Icc a b)) (hw₃'c : ContinuousOn w₃' (Icc a b))
    (hw₄ : ∀ x ∈ Icc a b, HasDerivAt w₄ (w₄' x) x)
    (hw₄c : ContinuousOn w₄ (Icc a b)) (hw₄'c : ContinuousOn w₄' (Icc a b))
    (hD : ∀ x ∈ Icc a b, HasDerivAt D (D' x) x) (hD'c : ContinuousOn D' (Icc a b))
    (hDd : ∀ x ∈ Icc a b, HasDerivAt D' (D'' x) x) (hD''c : ContinuousOn D'' (Icc a b))
    (hS : ∀ x ∈ Icc a b, HasDerivAt S (S' x) x) (hS'c : ContinuousOn S' (Icc a b))
    (hSd : ∀ x ∈ Icc a b, HasDerivAt S' (S'' x) x) (hS''c : ContinuousOn S'' (Icc a b))
    (hDlow : ∀ x ∈ Icc a b, m ≤ |D' x|) (hSlow : ∀ x ∈ Icc a b, m ≤ |S' x|) :
    |∫ x in a..b, (w₁ x * Real.cos (c * D x) + w₂ x * Real.cos (c * S x)
        + w₃ x * Real.sin (c * D x) + w₄ x * Real.sin (c * S x))|
      ≤ (oscBudget a b m w₁ w₁' D'' + oscBudget a b m w₂ w₂' S''
        + oscBudget a b m w₃ w₃' D'' + oscBudget a b m w₄ w₄' S'') / c := by
  have hDc : ContinuousOn D (Icc a b) := fun x hx => (hD x hx).continuousAt.continuousWithinAt
  have hSc : ContinuousOn S (Icc a b) := fun x hx => (hS x hx).continuousAt.continuousWithinAt
  have hcosD : ContinuousOn (fun x => Real.cos (c * D x)) (Icc a b) :=
    Real.continuous_cos.comp_continuousOn (hDc.const_smul c)
  have hcosS : ContinuousOn (fun x => Real.cos (c * S x)) (Icc a b) :=
    Real.continuous_cos.comp_continuousOn (hSc.const_smul c)
  have hsinD : ContinuousOn (fun x => Real.sin (c * D x)) (Icc a b) :=
    Real.continuous_sin.comp_continuousOn (hDc.const_smul c)
  have hsinS : ContinuousOn (fun x => Real.sin (c * S x)) (Icc a b) :=
    Real.continuous_sin.comp_continuousOn (hSc.const_smul c)
  have hi₁ : IntervalIntegrable (fun x => w₁ x * Real.cos (c * D x)) volume a b :=
    (hw₁c.mul hcosD).intervalIntegrable_of_Icc hab
  have hi₂ : IntervalIntegrable (fun x => w₂ x * Real.cos (c * S x)) volume a b :=
    (hw₂c.mul hcosS).intervalIntegrable_of_Icc hab
  have hi₃ : IntervalIntegrable (fun x => w₃ x * Real.sin (c * D x)) volume a b :=
    (hw₃c.mul hsinD).intervalIntegrable_of_Icc hab
  have hi₄ : IntervalIntegrable (fun x => w₄ x * Real.sin (c * S x)) volume a b :=
    (hw₄c.mul hsinS).intervalIntegrable_of_Icc hab
  rw [integral_add₄ hi₁ hi₂ hi₃ hi₄]
  have hz : ∀ (f Θ : ℝ → ℝ) (x : ℝ), f x * Real.cos (c * Θ x) = f x * Real.cos (c * Θ x + 0) := by
    intro f Θ x
    rw [add_zero]
  have hzs : ∀ (f Θ : ℝ → ℝ) (x : ℝ), f x * Real.sin (c * Θ x) = f x * Real.sin (c * Θ x + 0) := by
    intro f Θ x
    rw [add_zero]
  have h₁ : |∫ x in a..b, w₁ x * Real.cos (c * D x)| ≤ oscBudget a b m w₁ w₁' D'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hz w₁ D x]
    exact abs_integral_mul_cos_phase_le_on hab hc hm hw₁ hw₁c hw₁'c hD hD'c hDd hD''c hDlow
  have h₂ : |∫ x in a..b, w₂ x * Real.cos (c * S x)| ≤ oscBudget a b m w₂ w₂' S'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hz w₂ S x]
    exact abs_integral_mul_cos_phase_le_on hab hc hm hw₂ hw₂c hw₂'c hS hS'c hSd hS''c hSlow
  have h₃ : |∫ x in a..b, w₃ x * Real.sin (c * D x)| ≤ oscBudget a b m w₃ w₃' D'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hzs w₃ D x]
    exact abs_integral_mul_sin_phase_le_on hab hc hm hw₃ hw₃c hw₃'c hD hD'c hDd hD''c hDlow
  have h₄ : |∫ x in a..b, w₄ x * Real.sin (c * S x)| ≤ oscBudget a b m w₄ w₄' S'' / c := by
    rw [intervalIntegral.integral_congr fun x _ => hzs w₄ S x]
    exact abs_integral_mul_sin_phase_le_on hab hc hm hw₄ hw₄c hw₄'c hS hS'c hSd hS''c hSlow
  have hsplit : ((oscBudget a b m w₁ w₁' D'' + oscBudget a b m w₂ w₂' S''
        + oscBudget a b m w₃ w₃' D'' + oscBudget a b m w₄ w₄' S'') / c)
      = oscBudget a b m w₁ w₁' D'' / c + oscBudget a b m w₂ w₂' S'' / c
        + oscBudget a b m w₃ w₃' D'' / c + oscBudget a b m w₄ w₄' S'' / c := by
    ring
  rw [hsplit]
  calc |(∫ x in a..b, w₁ x * Real.cos (c * D x)) + (∫ x in a..b, w₂ x * Real.cos (c * S x))
        + (∫ x in a..b, w₃ x * Real.sin (c * D x)) + ∫ x in a..b, w₄ x * Real.sin (c * S x)|
      ≤ |(∫ x in a..b, w₁ x * Real.cos (c * D x)) + (∫ x in a..b, w₂ x * Real.cos (c * S x))
          + ∫ x in a..b, w₃ x * Real.sin (c * D x)|
        + |∫ x in a..b, w₄ x * Real.sin (c * S x)| := abs_add_le _ _
    _ ≤ (|(∫ x in a..b, w₁ x * Real.cos (c * D x)) + ∫ x in a..b, w₂ x * Real.cos (c * S x)|
          + |∫ x in a..b, w₃ x * Real.sin (c * D x)|)
        + |∫ x in a..b, w₄ x * Real.sin (c * S x)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ((|∫ x in a..b, w₁ x * Real.cos (c * D x)| + |∫ x in a..b, w₂ x * Real.cos (c * S x)|)
          + |∫ x in a..b, w₃ x * Real.sin (c * D x)|)
        + |∫ x in a..b, w₄ x * Real.sin (c * S x)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ oscBudget a b m w₁ w₁' D'' / c + oscBudget a b m w₂ w₂' S'' / c
        + oscBudget a b m w₃ w₃' D'' / c + oscBudget a b m w₄ w₄' S'' / c := by
        linarith [h₁, h₂, h₃, h₄]

/-- **The two-branch product estimate, with every hypothesis local to the interval.**  This is the
form the exterior radial problem produces: two dilated phases, each smooth and fast only on the
exterior ray, whose sum and difference speeds are separated by the index sum and the index gap. -/
theorem abs_integral_twoBranch_product_le_on
    {a b c m : ℝ} (hab : a ≤ b) (hc : 0 < c) (hm : 0 < m)
    {g₁ g₂ g₃ g₄ g₁' g₂' g₃' g₄' Φ Ψ Φ' Ψ' Φ'' Ψ'' : ℝ → ℝ}
    (hg₁ : ∀ x ∈ Icc a b, HasDerivAt g₁ (g₁' x) x)
    (hg₁c : ContinuousOn g₁ (Icc a b)) (hg₁'c : ContinuousOn g₁' (Icc a b))
    (hg₂ : ∀ x ∈ Icc a b, HasDerivAt g₂ (g₂' x) x)
    (hg₂c : ContinuousOn g₂ (Icc a b)) (hg₂'c : ContinuousOn g₂' (Icc a b))
    (hg₃ : ∀ x ∈ Icc a b, HasDerivAt g₃ (g₃' x) x)
    (hg₃c : ContinuousOn g₃ (Icc a b)) (hg₃'c : ContinuousOn g₃' (Icc a b))
    (hg₄ : ∀ x ∈ Icc a b, HasDerivAt g₄ (g₄' x) x)
    (hg₄c : ContinuousOn g₄ (Icc a b)) (hg₄'c : ContinuousOn g₄' (Icc a b))
    (hΦ : ∀ x ∈ Icc a b, HasDerivAt Φ (Φ' x) x) (hΦ'c : ContinuousOn Φ' (Icc a b))
    (hΦd : ∀ x ∈ Icc a b, HasDerivAt Φ' (Φ'' x) x) (hΦ''c : ContinuousOn Φ'' (Icc a b))
    (hΨ : ∀ x ∈ Icc a b, HasDerivAt Ψ (Ψ' x) x) (hΨ'c : ContinuousOn Ψ' (Icc a b))
    (hΨd : ∀ x ∈ Icc a b, HasDerivAt Ψ' (Ψ'' x) x) (hΨ''c : ContinuousOn Ψ'' (Icc a b))
    (hdiff : ∀ x ∈ Icc a b, m ≤ |Φ' x - Ψ' x|) (hsum : ∀ x ∈ Icc a b, m ≤ |Φ' x + Ψ' x|) :
    |∫ x in a..b, (g₁ x * Real.cos (c * Φ x) + g₂ x * Real.sin (c * Φ x))
        * (g₃ x * Real.cos (c * Ψ x) + g₄ x * Real.sin (c * Ψ x))|
      ≤ (oscBudget a b m (fun x => 1 / 2 * (g₁ x * g₃ x + g₂ x * g₄ x))
            (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
            (fun x => Φ'' x - Ψ'' x)
        + oscBudget a b m (fun x => 1 / 2 * (g₁ x * g₃ x - g₂ x * g₄ x))
            (fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
            (fun x => Φ'' x + Ψ'' x)
        + oscBudget a b m (fun x => 1 / 2 * (g₂ x * g₃ x - g₁ x * g₄ x))
            (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
            (fun x => Φ'' x - Ψ'' x)
        + oscBudget a b m (fun x => 1 / 2 * (g₂ x * g₃ x + g₁ x * g₄ x))
            (fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
            (fun x => Φ'' x + Ψ'' x)) / c := by
  have hrw : ∀ x : ℝ,
      (g₁ x * Real.cos (c * Φ x) + g₂ x * Real.sin (c * Φ x))
        * (g₃ x * Real.cos (c * Ψ x) + g₄ x * Real.sin (c * Ψ x))
      = (fun y => 1 / 2 * (g₁ y * g₃ y + g₂ y * g₄ y)) x
          * Real.cos (c * (fun y => Φ y - Ψ y) x)
        + (fun y => 1 / 2 * (g₁ y * g₃ y - g₂ y * g₄ y)) x
          * Real.cos (c * (fun y => Φ y + Ψ y) x)
        + (fun y => 1 / 2 * (g₂ y * g₃ y - g₁ y * g₄ y)) x
          * Real.sin (c * (fun y => Φ y - Ψ y) x)
        + (fun y => 1 / 2 * (g₂ y * g₃ y + g₁ y * g₄ y)) x
          * Real.sin (c * (fun y => Φ y + Ψ y) x) := by
    intro x
    rw [twoBranch_product_eq c g₁ g₂ g₃ g₄ Φ Ψ x]
    ring
  rw [intervalIntegral.integral_congr fun x _ => hrw x]
  refine abs_integral_fourOsc_le_on hab hc hm
    (w₁' := fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x + (g₂' x * g₄ x + g₂ x * g₄' x)))
    (w₂' := fun x => 1 / 2 * (g₁' x * g₃ x + g₁ x * g₃' x - (g₂' x * g₄ x + g₂ x * g₄' x)))
    (w₃' := fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x - (g₁' x * g₄ x + g₁ x * g₄' x)))
    (w₄' := fun x => 1 / 2 * (g₂' x * g₃ x + g₂ x * g₃' x + (g₁' x * g₄ x + g₁ x * g₄' x)))
    (D' := fun x => Φ' x - Ψ' x) (S' := fun x => Φ' x + Ψ' x)
    (D'' := fun x => Φ'' x - Ψ'' x) (S'' := fun x => Φ'' x + Ψ'' x)
    (fun x hx => (((hg₁ x hx).mul (hg₃ x hx)).add ((hg₂ x hx).mul (hg₄ x hx))).const_mul (1 / 2))
    ((hg₁c.mul hg₃c).add (hg₂c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₁'c.mul hg₃c).add (hg₁c.mul hg₃'c)).add
      ((hg₂'c.mul hg₄c).add (hg₂c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x hx => (((hg₁ x hx).mul (hg₃ x hx)).sub ((hg₂ x hx).mul (hg₄ x hx))).const_mul (1 / 2))
    ((hg₁c.mul hg₃c).sub (hg₂c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₁'c.mul hg₃c).add (hg₁c.mul hg₃'c)).sub
      ((hg₂'c.mul hg₄c).add (hg₂c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x hx => (((hg₂ x hx).mul (hg₃ x hx)).sub ((hg₁ x hx).mul (hg₄ x hx))).const_mul (1 / 2))
    ((hg₂c.mul hg₃c).sub (hg₁c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₂'c.mul hg₃c).add (hg₂c.mul hg₃'c)).sub
      ((hg₁'c.mul hg₄c).add (hg₁c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x hx => (((hg₂ x hx).mul (hg₃ x hx)).add ((hg₁ x hx).mul (hg₄ x hx))).const_mul (1 / 2))
    ((hg₂c.mul hg₃c).add (hg₁c.mul hg₄c) |>.const_smul (1 / 2 : ℝ))
    (((hg₂'c.mul hg₃c).add (hg₂c.mul hg₃'c)).add
      ((hg₁'c.mul hg₄c).add (hg₁c.mul hg₄'c)) |>.const_smul (1 / 2 : ℝ))
    (fun x hx => (hΦ x hx).sub (hΨ x hx)) (hΦ'c.sub hΨ'c)
    (fun x hx => (hΦd x hx).sub (hΨd x hx)) (hΦ''c.sub hΨ''c)
    (fun x hx => (hΦ x hx).add (hΨ x hx)) (hΦ'c.add hΨ'c)
    (fun x hx => (hΦd x hx).add (hΨd x hx)) (hΦ''c.add hΨ''c)
    hdiff hsum

/-! ## From a finite interval to the whole ray -/

/-- **Passing an oscillatory bound to the exterior ray.**  A bound valid on every finite interval,
whose right-hand side converges, bounds the improper integral by the limit.  This is how a
`1/(c|j−k|)` estimate proved on `[a,b]` becomes an estimate for the whole exterior Gram entry. -/
theorem abs_setIntegral_Ioi_le_of_tendsto {f : ℝ → ℝ} {a L : ℝ} {M : ℝ → ℝ}
    (hint : IntegrableOn f (Ioi a))
    (hb : ∀ b, |∫ x in a..b, f x| ≤ M b)
    (hM : Tendsto M atTop (𝓝 L)) :
    |∫ x in Ioi a, f x| ≤ L := by
  have htend : Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (𝓝 (∫ x in Ioi a, f x)) :=
    _root_.MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hint tendsto_id
  have habs : Tendsto (fun b : ℝ => |∫ x in a..b, f x|) atTop (𝓝 |∫ x in Ioi a, f x|) :=
    htend.abs
  exact le_of_tendsto_of_tendsto' habs hM hb

end GaloisForLFunctions.HTGeometry
