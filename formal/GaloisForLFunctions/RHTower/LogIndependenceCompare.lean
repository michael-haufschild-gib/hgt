import GaloisForLFunctions.RHTower.LogIndependence

/-!
# Finite prime-packet comparison

This file turns the one-packet Hurwitz/log-independence observability theorem
from `LogIndependence` into a two-packet comparison surface by padding both
supports to their union.
-/

namespace RHTower

open Finset

/-- Algebraic support-padding identity for comparing two Dirichlet packets. The
padded coefficient difference on `s ∪ t` is exactly the pointwise packet difference. -/
theorem dpoly_sub_eq_union (s t : Finset ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    dpoly (fun p => (if p ∈ s then a p else 0) - (if p ∈ t then b p else 0)) (s ∪ t) x =
      dpoly a s x - dpoly b t x := by
  classical
  let as : ℕ → ℝ := fun p => if p ∈ s then a p else 0
  let bt : ℕ → ℝ := fun p => if p ∈ t then b p else 0
  have hsplit : dpoly (fun p => as p - bt p) (s ∪ t) x =
      dpoly as (s ∪ t) x - dpoly bt (s ∪ t) x := by
    rw [dpoly, dpoly, dpoly]
    calc
      (∑ n ∈ s ∪ t, cterm (fun p => as p - bt p) x n)
          = ∑ n ∈ s ∪ t, (cterm as x n - cterm bt x n) := by
            apply Finset.sum_congr rfl
            intro p _hp
            unfold cterm
            push_cast
            ring
      _ = ∑ n ∈ s ∪ t, cterm as x n - ∑ n ∈ s ∪ t, cterm bt x n := by
            rw [Finset.sum_sub_distrib]
  have hsupp_s : dpoly as (s ∪ t) x = dpoly a s x := by
    rw [dpoly, dpoly]
    calc
      (∑ p ∈ s ∪ t, cterm as x p) = ∑ p ∈ s, cterm as x p := by
        exact (Finset.sum_subset (by intro p hp; exact Finset.mem_union_left t hp)
          (by intro p _hpU hps; simp [cterm, as, hps])).symm
      _ = ∑ p ∈ s, cterm a x p := by
        apply Finset.sum_congr rfl
        intro p hps
        simp [cterm, as, hps]
  have hsupp_t : dpoly bt (s ∪ t) x = dpoly b t x := by
    rw [dpoly, dpoly]
    calc
      (∑ p ∈ s ∪ t, cterm bt x p) = ∑ p ∈ t, cterm bt x p := by
        exact (Finset.sum_subset (by intro p hp; exact Finset.mem_union_right s hp)
          (by intro p _hpU hpt; simp [cterm, bt, hpt])).symm
      _ = ∑ p ∈ t, cterm b x p := by
        apply Finset.sum_congr rfl
        intro p hpt
        simp [cterm, bt, hpt]
  simpa [as, bt, hsupp_s, hsupp_t] using hsplit

/-- Two finite prime packets agree on a vertical interval exactly when their
coefficients agree after padding by zero on the union support. -/
theorem dpoly_prime_finset_eq_on_vertical_interval_iff_coeff_eq_on_union
    (s t : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    {a b : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∀ x ∈ Set.Ioo A B, dpoly a s x = dpoly b t x) ↔
      ∀ p ∈ s ∪ t, (if p ∈ s then a p else 0) = (if p ∈ t then b p else 0) := by
  classical
  let c : ℕ → ℝ := fun p => (if p ∈ s then a p else 0) - (if p ∈ t then b p else 0)
  have hprime : ∀ p ∈ s ∪ t, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hps | hpt
    · exact hs p hps
    · exact ht p hpt
  have hcrit := dpoly_prime_finset_eq_zero_on_vertical_interval_iff_coeff_eq_zero
    (s ∪ t) hprime (a := c) hAB
  have hdiff : ∀ x, dpoly c (s ∪ t) x = dpoly a s x - dpoly b t x := by
    intro x
    exact dpoly_sub_eq_union s t a b x
  constructor
  · intro heq p hp
    have hzero : ∀ x ∈ Set.Ioo A B, dpoly c (s ∪ t) x = 0 := by
      intro x hx
      rw [hdiff x, heq x hx, sub_self]
    have hc0 := hcrit.mp hzero p hp
    dsimp [c] at hc0
    exact sub_eq_zero.mp hc0
  · intro hcoeff x hx
    have hc0 : ∀ p ∈ s ∪ t, c p = 0 := by
      intro p hp
      exact sub_eq_zero.mpr (hcoeff p hp)
    have hzero := hcrit.mpr hc0 x hx
    rw [hdiff x] at hzero
    exact sub_eq_zero.mp hzero

/-- The interval `L²` distance between two finite prime packets vanishes exactly when
their coefficients agree after padding by zero on the union support. -/
theorem dpoly_prime_finset_secondMoment_sub_eq_zero_iff_coeff_eq_on_union
    (s t : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    {a b : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∫ x in A..B, ‖dpoly a s x - dpoly b t x‖ ^ (2 : ℕ)) = 0 ↔
      ∀ p ∈ s ∪ t, (if p ∈ s then a p else 0) = (if p ∈ t then b p else 0) := by
  classical
  let c : ℕ → ℝ := fun p => (if p ∈ s then a p else 0) - (if p ∈ t then b p else 0)
  have hprime : ∀ p ∈ s ∪ t, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hps | hpt
    · exact hs p hps
    · exact ht p hpt
  have hdiff : ∀ x, dpoly c (s ∪ t) x = dpoly a s x - dpoly b t x := by
    intro x
    exact dpoly_sub_eq_union s t a b x
  have hint : (∫ x in A..B, ‖dpoly a s x - dpoly b t x‖ ^ (2 : ℕ)) =
      ∫ x in A..B, ‖dpoly c (s ∪ t) x‖ ^ (2 : ℕ) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (hdiff x).symm
  rw [hint, dpoly_prime_finset_secondMoment_eq_zero_iff_eq_zero_on_vertical_interval
    (s ∪ t) hprime hAB]
  rw [← dpoly_prime_finset_eq_on_vertical_interval_iff_coeff_eq_on_union s t hs ht hAB]
  constructor
  · intro hzero x hx
    have hz := hzero x hx
    rw [hdiff x] at hz
    exact sub_eq_zero.mp hz
  · intro heq x hx
    rw [hdiff x, heq x hx, sub_self]

/-- The interval `L²` distance between two finite prime packets is positive exactly
when some coefficient differs after padding by zero on the union support. -/
theorem dpoly_prime_finset_secondMoment_sub_pos_iff_exists_coeff_ne_on_union
    (s t : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    {a b : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    0 < (∫ x in A..B, ‖dpoly a s x - dpoly b t x‖ ^ (2 : ℕ)) ↔
      ∃ p ∈ s ∪ t, (if p ∈ s then a p else 0) ≠ (if p ∈ t then b p else 0) := by
  classical
  let c : ℕ → ℝ := fun p => (if p ∈ s then a p else 0) - (if p ∈ t then b p else 0)
  have hprime : ∀ p ∈ s ∪ t, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hps | hpt
    · exact hs p hps
    · exact ht p hpt
  have hdiff : ∀ x, dpoly c (s ∪ t) x = dpoly a s x - dpoly b t x := by
    intro x
    exact dpoly_sub_eq_union s t a b x
  have hint : (∫ x in A..B, ‖dpoly a s x - dpoly b t x‖ ^ (2 : ℕ)) =
      ∫ x in A..B, ‖dpoly c (s ∪ t) x‖ ^ (2 : ℕ) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (hdiff x).symm
  have hpos := dpoly_prime_finset_secondMoment_pos_iff_exists_coeff_ne_zero_on_vertical_interval
    (s ∪ t) hprime (a := c) hAB
  rw [hint]
  constructor
  · intro h
    obtain ⟨p, hp, hcne⟩ := hpos.mp h
    dsimp [c] at hcne
    exact ⟨p, hp, fun heq => hcne (sub_eq_zero.mpr heq)⟩
  · rintro ⟨p, hp, hne⟩
    refine hpos.mpr ⟨p, hp, ?_⟩
    dsimp [c]
    exact fun hzero => hne (sub_eq_zero.mp hzero)

/-- The interval `L²` distance between two finite prime packets vanishes exactly when
the packets agree pointwise on the whole vertical interval. -/
theorem dpoly_prime_finset_secondMoment_sub_eq_zero_iff_eq_on_vertical_interval
    (s t : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    {a b : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    (∫ x in A..B, ‖dpoly a s x - dpoly b t x‖ ^ (2 : ℕ)) = 0 ↔
      ∀ x ∈ Set.Ioo A B, dpoly a s x = dpoly b t x := by
  exact (dpoly_prime_finset_secondMoment_sub_eq_zero_iff_coeff_eq_on_union
    s t hs ht hAB).trans
    (dpoly_prime_finset_eq_on_vertical_interval_iff_coeff_eq_on_union s t hs ht hAB).symm

/-- The interval `L²` distance between two finite prime packets is positive exactly
when the packets do not agree pointwise on the vertical interval. -/
theorem dpoly_prime_finset_secondMoment_sub_pos_iff_not_eq_on_vertical_interval
    (s t : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    {a b : ℕ → ℝ} {A B : ℝ} (hAB : A < B) :
    0 < (∫ x in A..B, ‖dpoly a s x - dpoly b t x‖ ^ (2 : ℕ)) ↔
      ¬ ∀ x ∈ Set.Ioo A B, dpoly a s x = dpoly b t x := by
  classical
  rw [dpoly_prime_finset_secondMoment_sub_pos_iff_exists_coeff_ne_on_union s t hs ht hAB]
  rw [dpoly_prime_finset_eq_on_vertical_interval_iff_coeff_eq_on_union s t hs ht hAB]
  constructor
  · rintro ⟨p, hp, hne⟩ hcoeff
    exact hne (hcoeff p hp)
  · intro hnot
    by_contra hnone
    apply hnot
    intro p hp
    by_contra hne
    exact hnone ⟨p, hp, hne⟩

end RHTower
