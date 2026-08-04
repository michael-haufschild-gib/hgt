import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality in integral form with a variable coefficient

The Grönwall inequality available in mathlib is the differential form with a *constant* coefficient:
`‖f' x‖ ≤ K ‖f x‖ + ε` gives an exponential bound in `K (x - a)`.  For a coefficient that decays — the
situation in every error analysis of an asymptotic expansion — that form is useless: replacing `k x` by
its supremum turns an integrable perturbation into an exponentially growing bound.

This file proves the integral form with the variable coefficient kept intact: if

```text
S x ≤ C + int_A^x k S      on [A, B],      k ≥ 0,
```

then `S x ≤ C exp(int_A^x k)`.  The proof is the classical one, and it is exact rather than iterative:
the primitive `R x = C + int_A^x k S` satisfies `R' = k S ≤ k R`, so `R · exp(-int_A^x k)` has nonpositive
derivative and is therefore antitone; its value at `A` is `C`.

* **`le_mul_exp_integral_of_le_add_integral`** — the inequality.
* `le_mul_exp_integral_of_le_add_integral_of_nonneg` — the common special case where the total mass of
  the coefficient is bounded, giving a bound uniform in the length of the interval.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set intervalIntegral

/-- **Grönwall's inequality, integral form, variable coefficient.**  If `S x ≤ C + int_A^x k S` on
`[A, B]` with `k` continuous and nonnegative, then `S x ≤ C exp(int_A^x k)`. -/
theorem le_mul_exp_integral_of_le_add_integral {S k : ℝ → ℝ} {A B C : ℝ} (hAB : A ≤ B)
    (hS : ContinuousOn S (Icc A B)) (hk : ContinuousOn k (Icc A B))
    (hknn : ∀ x ∈ Icc A B, 0 ≤ k x)
    (hbound : ∀ x ∈ Icc A B, S x ≤ C + ∫ t in A..x, k t * S t) :
    ∀ x ∈ Icc A B, S x ≤ C * Real.exp (∫ t in A..x, k t) := by
  have huIcc : uIcc A B = Icc A B := uIcc_of_le hAB
  have hkS : ContinuousOn (fun t : ℝ => k t * S t) (Icc A B) := hk.mul hS
  have hkSint : IntegrableOn (fun t : ℝ => k t * S t) (uIcc A B) volume := by
    rw [huIcc]
    exact hkS.integrableOn_compact isCompact_Icc
  have hkint : IntegrableOn k (uIcc A B) volume := by
    rw [huIcc]
    exact hk.integrableOn_compact isCompact_Icc
  -- the primitive and the exponential weight
  set R : ℝ → ℝ := fun x => C + ∫ t in A..x, k t * S t with hRdef
  set Kf : ℝ → ℝ := fun x => ∫ t in A..x, k t with hKdef
  set Φ : ℝ → ℝ := fun x => Real.exp (-(Kf x)) with hΦdef
  have hRcont : ContinuousOn R (Icc A B) := by
    rw [hRdef]
    refine continuousOn_const.add ?_
    have h := intervalIntegral.continuousOn_primitive_interval hkSint
    rwa [huIcc] at h
  have hKcont : ContinuousOn Kf (Icc A B) := by
    rw [hKdef]
    have h := intervalIntegral.continuousOn_primitive_interval hkint
    rwa [huIcc] at h
  have hΦcont : ContinuousOn Φ (Icc A B) := by
    rw [hΦdef]
    exact Real.continuous_exp.comp_continuousOn hKcont.neg
  have hΦpos : ∀ x : ℝ, 0 < Φ x := fun x => Real.exp_pos _
  -- interior derivatives
  have hRderiv : ∀ x ∈ Ioo A B, HasDerivAt R (k x * S x) x := by
    intro x hx
    have hsub : Icc A x ⊆ Icc A B := Icc_subset_Icc le_rfl hx.2.le
    have hIab : IntervalIntegrable (fun t : ℝ => k t * S t) volume A x := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.le]
      exact (hkS.mono hsub).integrableOn_compact isCompact_Icc |>.mono_set
        (fun t ht => ⟨ht.1.le, ht.2⟩)
    have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => k t * S t) (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hkS.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)) x hx
    have hcont : ContinuousAt (fun t : ℝ => k t * S t) x :=
      (hkS.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)).continuousAt (isOpen_Ioo.mem_nhds hx)
    have h := intervalIntegral.integral_hasDerivAt_right hIab hmeas hcont
    rw [hRdef]
    exact h.const_add C
  have hKderiv : ∀ x ∈ Ioo A B, HasDerivAt Kf (k x) x := by
    intro x hx
    have hsub : Icc A x ⊆ Icc A B := Icc_subset_Icc le_rfl hx.2.le
    have hIab : IntervalIntegrable k volume A x := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.le]
      exact (hk.mono hsub).integrableOn_compact isCompact_Icc |>.mono_set
        (fun t ht => ⟨ht.1.le, ht.2⟩)
    have hmeas : StronglyMeasurableAtFilter k (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hk.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)) x hx
    have hcont : ContinuousAt k x :=
      (hk.mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)).continuousAt (isOpen_Ioo.mem_nhds hx)
    exact intervalIntegral.integral_hasDerivAt_right hIab hmeas hcont
  have hΦderiv : ∀ x ∈ Ioo A B, HasDerivAt Φ (-(k x) * Φ x) x := by
    intro x hx
    have h := ((hKderiv x hx).neg).exp
    simp only [Pi.neg_apply] at h
    have hval : Real.exp (-(Kf x)) * -(k x) = -(k x) * Real.exp (-(Kf x)) := by ring
    rw [hval] at h
    exact h
  -- the weighted primitive is antitone
  have hprodderiv : ∀ x ∈ Ioo A B,
      HasDerivAt (fun t : ℝ => R t * Φ t) (k x * Φ x * (S x - R x)) x := by
    intro x hx
    have h := (hRderiv x hx).fun_mul (hΦderiv x hx)
    have hval : k x * S x * Φ x + R x * (-(k x) * Φ x) = k x * Φ x * (S x - R x) := by ring
    rw [hval] at h
    exact h
  have hanti : AntitoneOn (fun t : ℝ => R t * Φ t) (Icc A B) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc A B) (hRcont.mul hΦcont) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hprodderiv x hx).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hprodderiv x hx).deriv]
      have hxIcc : x ∈ Icc A B := ⟨hx.1.le, hx.2.le⟩
      have hSR : S x - R x ≤ 0 := by
        have := hbound x hxIcc
        rw [hRdef]
        linarith
      have hkΦ : 0 ≤ k x * Φ x := mul_nonneg (hknn x hxIcc) (hΦpos x).le
      exact mul_nonpos_of_nonneg_of_nonpos hkΦ hSR
  -- conclude
  intro x hx
  have hle : R x * Φ x ≤ R A * Φ A := hanti (left_mem_Icc.mpr hAB) hx hx.1
  have hA : R A * Φ A = C := by
    simp only [hRdef, hΦdef, hKdef]
    simp
  rw [hA] at hle
  have hstep : R x ≤ C * Real.exp (Kf x) := by
    have hexp : Real.exp (-(Kf x)) * Real.exp (Kf x) = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (Kf x)).le
    rw [hΦdef] at hmul
    simp only at hmul
    rw [mul_assoc, hexp, mul_one] at hmul
    exact hmul
  have hSR := hbound x hx
  rw [hRdef] at hstep
  rw [hKdef] at hstep
  linarith

/-- The uniform form: if the total mass of the coefficient is at most `M`, the bound is uniform in the
length of the interval. -/
theorem le_mul_exp_of_le_add_integral_of_mass_le {S k : ℝ → ℝ} {A B C M : ℝ} (hAB : A ≤ B)
    (hS : ContinuousOn S (Icc A B)) (hk : ContinuousOn k (Icc A B))
    (hknn : ∀ x ∈ Icc A B, 0 ≤ k x) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc A B, S x ≤ C + ∫ t in A..x, k t * S t)
    (hmass : ∀ x ∈ Icc A B, (∫ t in A..x, k t) ≤ M) :
    ∀ x ∈ Icc A B, S x ≤ C * Real.exp M := by
  intro x hx
  refine le_trans (le_mul_exp_integral_of_le_add_integral hAB hS hk hknn hbound x hx) ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hmass x hx)) hC

/-! ## The two-Wronskian Volterra bound -/

/-- **The Volterra bound for a solution reconstructed from two Wronskians.**  This is the abstract form
of the error analysis of a comparison expansion.  The hypotheses are exactly what a comparison equation
supplies:

* `hrec` — the solution is recovered algebraically from its two Wronskians against the model pair,
  divided by the (constant, nonzero) Green kernel normalisation `W`;
* `hV₁`, `hV₂` — a common envelope `E` for the two model solutions;
* `hSbound` — the two transport laws, integrated and combined: the total Wronskian size grows by at most
  the integral of `2 κ E² / W` against itself, where `κ` carries the weight and the defect.

The conclusion is the envelope bound with the exponential of the defect mass — which is `1 + O(mass)`
when the mass is small, and that is where the relative `O(c^{-1})` of a pole-uniform expansion comes
from. -/
theorem abs_le_envelope_mul_exp_of_two_wronskian
    {U F₁ F₂ V₁ V₂ κ E : ℝ → ℝ} {W A B : ℝ}
    (hW : 0 < W) (hAB : A ≤ B)
    (hrec : ∀ x ∈ Icc A B, U x * W = F₂ x * V₁ x - F₁ x * V₂ x)
    (hV₁ : ∀ x ∈ Icc A B, |V₁ x| ≤ E x) (hV₂ : ∀ x ∈ Icc A B, |V₂ x| ≤ E x)
    (hκnn : ∀ x ∈ Icc A B, 0 ≤ κ x) (hEnn : ∀ x ∈ Icc A B, 0 ≤ E x)
    (hSbound : ∀ x ∈ Icc A B, |F₁ x| + |F₂ x|
      ≤ (|F₁ A| + |F₂ A|) + ∫ t in A..x, 2 * κ t * E t ^ 2 / W * (|F₁ t| + |F₂ t|))
    (hκc : ContinuousOn (fun t : ℝ => 2 * κ t * E t ^ 2 / W) (Icc A B))
    (hSc : ContinuousOn (fun t : ℝ => |F₁ t| + |F₂ t|) (Icc A B)) :
    ∀ x ∈ Icc A B, |U x|
      ≤ E x / W * ((|F₁ A| + |F₂ A|) * Real.exp (∫ t in A..x, 2 * κ t * E t ^ 2 / W)) := by
  have hknn : ∀ x ∈ Icc A B, 0 ≤ 2 * κ x * E x ^ 2 / W := by
    intro x hx
    have h1 : 0 ≤ 2 * κ x * E x ^ 2 := by
      have := hκnn x hx
      positivity
    positivity
  have hgron := le_mul_exp_integral_of_le_add_integral hAB hSc hκc hknn hSbound
  intro x hx
  have hS := hgron x hx
  have hU : |U x| * W ≤ E x * (|F₁ x| + |F₂ x|) := by
    have hrx := hrec x hx
    have habs : |U x| * W = |U x * W| := by
      rw [abs_mul, abs_of_pos hW]
    rw [habs, hrx]
    calc |F₂ x * V₁ x - F₁ x * V₂ x| ≤ |F₂ x * V₁ x| + |F₁ x * V₂ x| := abs_sub _ _
      _ = |F₂ x| * |V₁ x| + |F₁ x| * |V₂ x| := by rw [abs_mul, abs_mul]
      _ ≤ |F₂ x| * E x + |F₁ x| * E x := by
          have h1 := mul_le_mul_of_nonneg_left (hV₁ x hx) (abs_nonneg (F₂ x))
          have h2 := mul_le_mul_of_nonneg_left (hV₂ x hx) (abs_nonneg (F₁ x))
          linarith
      _ = E x * (|F₁ x| + |F₂ x|) := by ring
  have hEx : 0 ≤ E x := hEnn x hx
  have hstep : E x * (|F₁ x| + |F₂ x|)
      ≤ E x * ((|F₁ A| + |F₂ A|) * Real.exp (∫ t in A..x, 2 * κ t * E t ^ 2 / W)) :=
    mul_le_mul_of_nonneg_left hS hEx
  rw [div_mul_eq_mul_div, le_div_iff₀ hW]
  linarith [hU, hstep]

end GaloisForLFunctions.HTGeometry

end
