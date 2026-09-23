import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Comparison for a linear differential inequality with variable coefficient

Mathlib's Grönwall inequality is the constant-coefficient one.  What ODE comparison arguments need is the
variable-coefficient sign statement: if

```text
d(a) <= 0    and    d'(y) <= K(y) · d(y)   on (a,b),
```

with `K` merely continuous on `[a,b]`, then `d <= 0` on all of `[a,b]`.  The proof is the integrating
factor `exp(-∫_a^y K)`: the product `d(y) exp(-∫_a^y K)` has nonpositive derivative, hence is antitone,
hence is bounded by its value `d(a) <= 0` at the left endpoint.

The Riccati corollary is the form ODE comparison uses: a subsolution of `u' = u² + b u - q` starting below
a supersolution stays below it, because the difference satisfies exactly such a linear inequality with
`K = u₁ + u₂ + b`.  This is how a logarithmic derivative of a solution of a second-order equation is
bounded by an explicit comparison function.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set intervalIntegral MeasureTheory

/-- **Comparison for a linear differential inequality with variable coefficient.**  The integrating
factor `exp(-∫ K)` turns the inequality into antitonicity. -/
theorem nonpos_of_hasDerivAt_le_mul {a b : ℝ} {d d' K : ℝ → ℝ} (hab : a ≤ b)
    (hdc : ContinuousOn d (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt d (d' y) y)
    (hKc : ContinuousOn K (Icc a b))
    (h0 : d a ≤ 0)
    (hineq : ∀ y ∈ Ioo a b, d' y ≤ K y * d y) :
    ∀ y ∈ Icc a b, d y ≤ 0 := by
  -- a globally continuous representative of the coefficient
  set L : ℝ → ℝ := Set.IccExtend hab (fun x : Icc a b => K x) with hL
  have hLcont : Continuous L := by
    rw [hL]
    exact (continuous_IccExtend_iff (h := hab)).mpr hKc.restrict
  have hLeq : ∀ y ∈ Icc a b, L y = K y := by
    intro y hy
    rw [hL]
    exact Set.IccExtend_val hab (fun x : Icc a b => K x) ⟨y, hy⟩
  -- the integrating factor
  set F : ℝ → ℝ := fun y => ∫ t in a..y, L t with hF
  have hFderiv : ∀ y : ℝ, HasDerivAt F (L y) y := by
    intro y
    refine intervalIntegral.integral_hasDerivAt_right (hLcont.intervalIntegrable a y)
      (hLcont.stronglyMeasurableAtFilter _ _) hLcont.continuousAt
  set E : ℝ → ℝ := fun y => d y * Real.exp (-F y) with hE
  have hexpderiv : ∀ y : ℝ, HasDerivAt (fun t => Real.exp (-F t))
      (-(L y) * Real.exp (-F y)) y := by
    intro y
    have h := ((hFderiv y).neg).exp
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hEcont : ContinuousOn E (Icc a b) := by
    refine hdc.mul ?_
    exact (Real.continuous_exp.comp ((continuous_iff_continuousAt.mpr
      fun y => (hFderiv y).continuousAt).neg)).continuousOn
  have hEderiv : ∀ y ∈ Ioo a b,
      HasDerivAt E ((d' y - L y * d y) * Real.exp (-F y)) y := by
    intro y hy
    have h := (hd y hy).mul (hexpderiv y)
    refine h.congr_deriv ?_
    ring
  have hEnonpos : ∀ y ∈ Ioo a b, (d' y - L y * d y) * Real.exp (-F y) ≤ 0 := by
    intro y hy
    have hymem : y ∈ Icc a b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hK := hineq y hy
    rw [hLeq y hymem]
    have hle : d' y - K y * d y ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt (Real.exp_pos _))
  have hanti : AntitoneOn E (Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hEcont
      (f' := fun y => (d' y - L y * d y) * Real.exp (-F y)) ?_ ?_
    · intro y hy
      rw [interior_Icc] at hy
      exact (hEderiv y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact hEnonpos y hy
  intro y hy
  have hEa : E a = d a := by
    rw [hE, hF]
    simp
  have hcmp : E y ≤ E a := hanti (left_mem_Icc.mpr hab) hy hy.1
  rw [hEa] at hcmp
  have hEy : E y = d y * Real.exp (-F y) := rfl
  have hexppos : 0 < Real.exp (-F y) := Real.exp_pos _
  by_contra hpos
  push Not at hpos
  have : 0 < E y := by
    rw [hEy]
    exact mul_pos hpos hexppos
  linarith

/-- **Riccati comparison.**  A subsolution of `u' = u² + b u - q` that starts below a supersolution stays
below it: the difference satisfies a linear differential inequality with coefficient `u₁ + u₂ + b`. -/
theorem riccati_le_of_le_of_supersolution {a b : ℝ} {u U u' U' bcoef q : ℝ → ℝ} (hab : a ≤ b)
    (huc : ContinuousOn u (Icc a b)) (hUc : ContinuousOn U (Icc a b))
    (hu : ∀ y ∈ Ioo a b, HasDerivAt u (u' y) y)
    (hU : ∀ y ∈ Ioo a b, HasDerivAt U (U' y) y)
    (hbc : ContinuousOn bcoef (Icc a b))
    (hsub : ∀ y ∈ Ioo a b, u' y ≤ (u y) ^ (2 : ℕ) + bcoef y * u y - q y)
    (hsuper : ∀ y ∈ Ioo a b, (U y) ^ (2 : ℕ) + bcoef y * U y - q y ≤ U' y)
    (h0 : u a ≤ U a) :
    ∀ y ∈ Icc a b, u y ≤ U y := by
  have hkey := nonpos_of_hasDerivAt_le_mul (d := fun y => u y - U y)
    (d' := fun y => u' y - U' y) (K := fun y => u y + U y + bcoef y) hab
    (huc.sub hUc) (fun y hy => (hu y hy).sub (hU y hy)) ((huc.add hUc).add hbc)
    (by linarith [h0]) ?_
  · intro y hy
    have h := hkey y hy
    linarith
  · intro y hy
    have h1 := hsub y hy
    have h2 := hsuper y hy
    nlinarith [h1, h2]

/-! ## The backward comparison -/

/-- **Backward comparison for a linear differential inequality.**  If `d(b) <= 0` and `d' >= K d` on
`(a,b)` then `d <= 0` on `[a,b]`: the integrating factor makes `d exp(-∫ K)` monotone *increasing*, so it
is bounded by its value at the right endpoint. -/
theorem nonpos_of_hasDerivAt_ge_mul {a b : ℝ} {d d' K : ℝ → ℝ} (hab : a ≤ b)
    (hdc : ContinuousOn d (Icc a b))
    (hd : ∀ y ∈ Ioo a b, HasDerivAt d (d' y) y)
    (hKc : ContinuousOn K (Icc a b))
    (h0 : d b ≤ 0)
    (hineq : ∀ y ∈ Ioo a b, K y * d y ≤ d' y) :
    ∀ y ∈ Icc a b, d y ≤ 0 := by
  set L : ℝ → ℝ := Set.IccExtend hab (fun x : Icc a b => K x) with hL
  have hLcont : Continuous L := by
    rw [hL]
    exact (continuous_IccExtend_iff (h := hab)).mpr hKc.restrict
  have hLeq : ∀ y ∈ Icc a b, L y = K y := by
    intro y hy
    rw [hL]
    exact Set.IccExtend_val hab (fun x : Icc a b => K x) ⟨y, hy⟩
  set F : ℝ → ℝ := fun y => ∫ t in a..y, L t with hF
  have hFderiv : ∀ y : ℝ, HasDerivAt F (L y) y := by
    intro y
    exact intervalIntegral.integral_hasDerivAt_right (hLcont.intervalIntegrable a y)
      (hLcont.stronglyMeasurableAtFilter _ _) hLcont.continuousAt
  set E : ℝ → ℝ := fun y => d y * Real.exp (-F y) with hE
  have hexpderiv : ∀ y : ℝ, HasDerivAt (fun t => Real.exp (-F t))
      (-(L y) * Real.exp (-F y)) y := by
    intro y
    have h := ((hFderiv y).neg).exp
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hEcont : ContinuousOn E (Icc a b) := by
    refine hdc.mul ?_
    exact (Real.continuous_exp.comp ((continuous_iff_continuousAt.mpr
      fun y => (hFderiv y).continuousAt).neg)).continuousOn
  have hEderiv : ∀ y ∈ Ioo a b,
      HasDerivAt E ((d' y - L y * d y) * Real.exp (-F y)) y := by
    intro y hy
    have h := (hd y hy).mul (hexpderiv y)
    refine h.congr_deriv ?_
    ring
  have hEnonneg : ∀ y ∈ Ioo a b, 0 ≤ (d' y - L y * d y) * Real.exp (-F y) := by
    intro y hy
    have hymem : y ∈ Icc a b := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hK := hineq y hy
    rw [hLeq y hymem]
    have hle : 0 ≤ d' y - K y * d y := by linarith
    exact mul_nonneg hle (le_of_lt (Real.exp_pos _))
  have hmono : MonotoneOn E (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hEcont
      (f' := fun y => (d' y - L y * d y) * Real.exp (-F y)) ?_ ?_
    · intro y hy
      rw [interior_Icc] at hy
      exact (hEderiv y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact hEnonneg y hy
  intro y hy
  have hcmp : E y ≤ E b := hmono hy (right_mem_Icc.mpr hab) hy.2
  have hEb : E b = d b * Real.exp (-F b) := rfl
  have hexppos : 0 < Real.exp (-F b) := Real.exp_pos _
  have hEbnonpos : E b ≤ 0 := by
    rw [hEb]
    exact mul_nonpos_of_nonpos_of_nonneg h0 (le_of_lt hexppos)
  have hEy : E y = d y * Real.exp (-F y) := rfl
  have hexppos' : 0 < Real.exp (-F y) := Real.exp_pos _
  by_contra hpos
  push Not at hpos
  have hEypos : 0 < E y := by
    rw [hEy]
    exact mul_pos hpos hexppos'
  linarith

/-- **Riccati comparison, backward form.**  A *sub*solution of `u' = u² + b u - q` that dominates the
solution at the right endpoint dominates it on the whole interval. -/
theorem riccati_le_of_le_of_subsolution {a b : ℝ} {u U u' U' bcoef q : ℝ → ℝ} (hab : a ≤ b)
    (huc : ContinuousOn u (Icc a b)) (hUc : ContinuousOn U (Icc a b))
    (hu : ∀ y ∈ Ioo a b, HasDerivAt u (u' y) y)
    (hU : ∀ y ∈ Ioo a b, HasDerivAt U (U' y) y)
    (hbc : ContinuousOn bcoef (Icc a b))
    (heq : ∀ y ∈ Ioo a b, u' y = (u y) ^ (2 : ℕ) + bcoef y * u y - q y)
    (hsub : ∀ y ∈ Ioo a b, U' y ≤ (U y) ^ (2 : ℕ) + bcoef y * U y - q y)
    (h0 : u b ≤ U b) :
    ∀ y ∈ Icc a b, u y ≤ U y := by
  have hkey := nonpos_of_hasDerivAt_ge_mul (d := fun y => u y - U y)
    (d' := fun y => u' y - U' y) (K := fun y => u y + U y + bcoef y) hab
    (huc.sub hUc) (fun y hy => (hu y hy).sub (hU y hy)) ((huc.add hUc).add hbc)
    (by linarith [h0]) ?_
  · intro y hy
    have h := hkey y hy
    linarith
  · intro y hy
    have h1 := heq y hy
    have h2 := hsub y hy
    nlinarith [h1, h2]

end GaloisForLFunctions.HTGeometry

end
