import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.SpectatorReturns.Weighted.Rectangles

/-! # Uniform simultaneous approximation for all weights -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
open KleinbockMargulis
noncomputable section
variable {n : ℕ}

/-- For normalized real side lengths the lower bound is uniform in the
shape of the box and in the numerator and denominator of the winding. -/
theorem real_sides {y : Fin n→ℝ} (hn : 0<n) (hy : ¬VWMA y) {δ : ℝ} (hδ : 0<δ) :
    ∃ C≥(1:ℝ), ∀ (q : ℕ), 0<q → ∀ (p : Fin n→ℤ) (R : Fin n→ℝ),
      (∀ i, 1≤R i) → (∏ i, R i)=(q:ℝ) →
      (q:ℝ)^(-δ)≤C*∑ i, R i*|(q:ℝ)*y i-(p i:ℝ)| := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨C,hC,hh⟩ := rectangular_error_bound hy hδ
  refine ⟨C,hC,?_⟩
  intro q hq p R hR hprod
  let s := fun i => ⌊R i⌋₊
  have hs (i) : (s i:ℝ)≤R i := Nat.floor_le (zero_le_one.trans (hR i))
  have hl : (∏ i, max 1 (s i))≤q := by
    have hle : (∏ i, max (1:ℝ) (s i:ℝ))≤(q:ℝ) := by
      rw [←hprod]; exact prod_le_prod (fun i _ => zero_le_one.trans (le_max_left _ _))
        (fun i _ => max_le (hR i) (hs i))
    exact_mod_cast hle
  have hu : q<∏ i, (s i+1) := by
    have hlt : (q:ℝ)<∏ i, ((s i:ℝ)+1) := by
      rw [←hprod]
      exact prod_lt_prod_of_nonempty (fun i _ => zero_lt_one.trans_le (hR i))
        (fun i _ => Nat.lt_floor_add_one (R i)) univ_nonempty
    exact_mod_cast hlt
  exact (hh q hq p s hl hu).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hs i) (abs_nonneg _)) (zero_le_one.trans hC))

/-- Multiplicative extremality gives one constant for the entire simplex
of simultaneous approximation weights, including boundary weights. -/
theorem weighted_error_bound {y : Fin n→ℝ} (hn : 0<n) (hy : ¬VWMA y) {δ : ℝ} (hδ : 0<δ) :
    ∃ C≥(1:ℝ), ∀ (q : ℕ), 0<q → ∀ (p : Fin n→ℤ) (u : Fin n→ℝ),
      (∀ i, 0≤u i) → ∑ i, u i=1 →
      (q:ℝ)^(-δ)≤C*∑ i, (q:ℝ)^(u i)*|(q:ℝ)*y i-(p i:ℝ)| := by
  obtain ⟨C,hC,hh⟩ := real_sides hn hy hδ
  refine ⟨C,hC,?_⟩
  intro q hq p u hu hsum
  apply hh q hq p (fun i => (q:ℝ)^(u i))
  · exact fun i => one_le_rpow (by exact_mod_cast hq : (1:ℝ)≤q) (hu i)
  rw [←rpow_sum_of_pos (Nat.cast_pos.mpr hq),hsum,rpow_one]

#print axioms weighted_error_bound
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns.Weighted
