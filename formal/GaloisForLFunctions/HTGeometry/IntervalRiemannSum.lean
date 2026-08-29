import Mathlib

/-!
# Uniform Riemann sums for interval integrals

A continuous integrand on a compact interval is approximated by its left-endpoint Riemann sums on a
uniform partition, with error controlled by the oscillation of the integrand on each cell.  This is
the discretization step of Runge approximation: it turns a contour integral of a Cauchy kernel into
a rational function with simple poles on the contour.
-/

namespace GaloisForLFunctions.HTGeometry

open intervalIntegral MeasureTheory

noncomputable section

/-- The `i`-th node of the uniform partition of `[a, b]` into `N` cells. -/
def uniformNode (a b : ℝ) (N : ℕ) (i : ℕ) : ℝ := a + (i : ℝ) * (b - a) / N

@[simp] theorem uniformNode_zero (a b : ℝ) (N : ℕ) : uniformNode a b N 0 = a := by
  simp [uniformNode]

theorem uniformNode_last {a b : ℝ} {N : ℕ} (hN : 0 < N) : uniformNode a b N N = b := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [uniformNode]
  field_simp
  ring

theorem uniformNode_succ_sub {a b : ℝ} {N : ℕ} (hN : 0 < N) (i : ℕ) :
    uniformNode a b N (i + 1) - uniformNode a b N i = (b - a) / N := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [uniformNode]
  push_cast
  field_simp
  ring

/-- **Uniform Riemann-sum estimate.**  If the integrand deviates by at most `η` from its
left-endpoint value on each cell of the uniform partition, the integral differs from the
left-endpoint Riemann sum by at most `(b − a) η`. -/
theorem norm_intervalIntegral_sub_uniformRiemannSum_le {a b : ℝ} (hab : a ≤ b)
    {h : ℝ → ℂ} {N : ℕ} (hN : 0 < N)
    (hint : ∀ i < N, IntervalIntegrable h volume
      (uniformNode a b N i) (uniformNode a b N (i + 1)))
    {η : ℝ} (_hη : 0 ≤ η)
    (hmod : ∀ i < N, ∀ x ∈ Set.uIoc (uniformNode a b N i) (uniformNode a b N (i + 1)),
      ‖h x - h (uniformNode a b N i)‖ ≤ η) :
    ‖(∫ x in a..b, h x) -
        ∑ i ∈ Finset.range N, (((b - a) / N : ℝ)) • h (uniformNode a b N i)‖
      ≤ (b - a) * η := by
  classical
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsplit : ∑ i ∈ Finset.range N,
      (∫ x in (uniformNode a b N i)..(uniformNode a b N (i + 1)), h x) = ∫ x in a..b, h x := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := uniformNode a b N) (f := h) (μ := volume) (n := N) (fun k hk => hint k hk)
    rwa [uniformNode_zero, uniformNode_last hN] at this
  have hcell : ∀ i ∈ Finset.range N,
      ‖(∫ x in (uniformNode a b N i)..(uniformNode a b N (i + 1)), h x)
        - (((b - a) / N : ℝ)) • h (uniformNode a b N i)‖ ≤ η * ((b - a) / N) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.1 hi
    have hconst : (∫ _x in (uniformNode a b N i)..(uniformNode a b N (i + 1)),
        h (uniformNode a b N i))
        = (((b - a) / N : ℝ)) • h (uniformNode a b N i) := by
      rw [intervalIntegral.integral_const, uniformNode_succ_sub hN]
    have hsub : (∫ x in (uniformNode a b N i)..(uniformNode a b N (i + 1)), h x)
        - (((b - a) / N : ℝ)) • h (uniformNode a b N i)
        = ∫ x in (uniformNode a b N i)..(uniformNode a b N (i + 1)),
            (h x - h (uniformNode a b N i)) := by
      rw [← hconst, intervalIntegral.integral_sub (hint i hiN) intervalIntegrable_const]
    rw [hsub]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := η) (f := fun x => h x - h (uniformNode a b N i))
      (a := uniformNode a b N i) (b := uniformNode a b N (i + 1))
      (fun x hx => hmod i hiN x hx)
    have habs : |uniformNode a b N (i + 1) - uniformNode a b N i| = (b - a) / N := by
      rw [uniformNode_succ_sub hN]
      have : 0 ≤ (b - a) / N := by
        have : (0:ℝ) ≤ b - a := by linarith
        positivity
      exact abs_of_nonneg this
    rwa [habs] at hbound
  calc ‖(∫ x in a..b, h x) -
        ∑ i ∈ Finset.range N, (((b - a) / N : ℝ)) • h (uniformNode a b N i)‖
      = ‖∑ i ∈ Finset.range N,
          ((∫ x in (uniformNode a b N i)..(uniformNode a b N (i + 1)), h x)
            - (((b - a) / N : ℝ)) • h (uniformNode a b N i))‖ := by
        rw [Finset.sum_sub_distrib, hsplit]
    _ ≤ ∑ i ∈ Finset.range N, η * ((b - a) / N) :=
        norm_sum_le_of_le _ hcell
    _ = (b - a) * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end

end GaloisForLFunctions.HTGeometry
