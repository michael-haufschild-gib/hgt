import Mathlib

/-!
# Boundary coefficients of Hahn series

The leading-coefficient calculus of `LaurentHasLead`, over an arbitrary linearly ordered value
group.  A multi-graded value group is what a several-variable Newton-corner degeneration needs: the
coordinate derivations shift one component of the degree, so a single integer degree cannot record
their effect.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R]

/-- `f` vanishes below degree `d` and has coefficient `c` there. -/
def HasLeadAt (f : HahnSeries Γ R) (d : Γ) (c : R) : Prop :=
  (∀ k < d, f.coeff k = 0) ∧ f.coeff d = c

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem hasLeadAt_zero (d : Γ) : HasLeadAt (0 : HahnSeries Γ R) d 0 :=
  ⟨fun _ _ => rfl, rfl⟩

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem HasLeadAt.mono {f : HahnSeries Γ R} {d e : Γ} {c : R} (h : HasLeadAt f d c) (hed : e < d) :
    HasLeadAt f e 0 :=
  ⟨fun k hk => h.1 k (lt_trans hk hed), h.1 e hed⟩

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem HasLeadAt.add {f g : HahnSeries Γ R} {d : Γ} {c c' : R}
    (hf : HasLeadAt f d c) (hg : HasLeadAt g d c') : HasLeadAt (f + g) d (c + c') :=
  ⟨fun k hk => by rw [HahnSeries.coeff_add, hf.1 k hk, hg.1 k hk, add_zero],
    by rw [HahnSeries.coeff_add, hf.2, hg.2]⟩

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem HasLeadAt.neg {f : HahnSeries Γ R} {d : Γ} {c : R} (hf : HasLeadAt f d c) :
    HasLeadAt (-f) d (-c) :=
  ⟨fun k hk => by rw [HahnSeries.coeff_neg, hf.1 k hk, neg_zero],
    by rw [HahnSeries.coeff_neg, hf.2]⟩

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem HasLeadAt.sub {f g : HahnSeries Γ R} {d : Γ} {c c' : R}
    (hf : HasLeadAt f d c) (hg : HasLeadAt g d c') : HasLeadAt (f - g) d (c - c') := by
  have h := hf.add hg.neg
  rwa [← sub_eq_add_neg, ← sub_eq_add_neg] at h

/-- A product vanishes below the sum of the bounds. -/
theorem coeffAt_mul_eq_zero_of_lt {f g : HahnSeries Γ R} {m n : Γ}
    (hf : ∀ i < m, f.coeff i = 0) (hg : ∀ j < n, g.coeff j = 0) :
    ∀ k < m + n, (f * g).coeff k = 0 := by
  classical
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  obtain ⟨-, -, hsum⟩ := hp
  by_cases h1 : p.1 < m
  · rw [hf p.1 h1, zero_mul]
  · have hm : m ≤ p.1 := not_lt.mp h1
    have : p.2 < n := by
      by_contra hcon
      have hn : n ≤ p.2 := not_lt.mp hcon
      exact absurd hsum (by
        intro hc
        exact absurd hk (not_lt.mpr (hc ▸ add_le_add hm hn)))
    rw [hg p.2 this, mul_zero]

/-- The boundary coefficient of a product is the product of the boundary coefficients. -/
theorem coeffAt_mul_of_vanishing_below {f g : HahnSeries Γ R} {m n : Γ}
    (hf : ∀ i < m, f.coeff i = 0) (hg : ∀ j < n, g.coeff j = 0) :
    (f * g).coeff (m + n) = f.coeff m * g.coeff n := by
  classical
  rw [HahnSeries.coeff_mul]
  by_cases hmem : ((m, n) : Γ × Γ) ∈
      Finset.antidiagonal f.isPWO_support g.isPWO_support (m + n)
  · refine Finset.sum_eq_single ((m, n) : Γ × Γ) ?_ (fun hcon => absurd hmem hcon)
    rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨hi, hj, hsum⟩ := hij
    by_cases h1 : i < m
    · rw [hf i h1, zero_mul]
    · have hm : m ≤ i := not_lt.mp h1
      by_cases h2 : j < n
      · rw [hg j h2, mul_zero]
      · have hn : n ≤ j := not_lt.mp h2
        have him : i = m := by
          by_contra hcon
          have hlt : m < i := lt_of_le_of_ne hm (Ne.symm hcon)
          have hgt : m + n < i + j := lt_of_lt_of_le (add_lt_add_of_lt_of_le hlt (le_refl n)) (add_le_add (le_refl i) hn)
          rw [hsum] at hgt
          exact lt_irrefl _ hgt
        have hjn : j = n := by
          have hs := hsum
          rw [him] at hs
          exact add_left_cancel hs
        exact absurd (Prod.ext him hjn) hne
  · rw [Finset.mem_antidiagonal] at hmem
    push Not at hmem
    have hzero : f.coeff m * g.coeff n = 0 := by
      by_cases hfm : f.coeff m = 0
      · rw [hfm, zero_mul]
      · have hgn : g.coeff n = 0 := by
          by_contra hgn
          exact absurd rfl (hmem (by simpa using hfm) (by simpa using hgn))
        rw [hgn, mul_zero]
    rw [hzero]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    obtain ⟨hi, hj, hsum⟩ := hp
    by_cases h1 : p.1 < m
    · rw [hf p.1 h1, zero_mul]
    · have hm : m ≤ p.1 := not_lt.mp h1
      by_cases h2 : p.2 < n
      · rw [hg p.2 h2, mul_zero]
      · have hn : n ≤ p.2 := not_lt.mp h2
        have hp1 : p.1 = m := by
          by_contra hcon
          have hlt : m < p.1 := lt_of_le_of_ne hm (Ne.symm hcon)
          have : m + n < p.1 + p.2 := lt_of_lt_of_le (add_lt_add_of_lt_of_le hlt (le_refl n)) (add_le_add (le_refl p.1) hn)
          rw [hsum] at this
          exact lt_irrefl _ this
        have hp2 : p.2 = n := by
          have := hsum
          rw [hp1] at this
          exact add_left_cancel this
        rw [hp1, hp2, hzero]

theorem HasLeadAt.mul {f g : HahnSeries Γ R} {d e : Γ} {c c' : R}
    (hf : HasLeadAt f d c) (hg : HasLeadAt g e c') : HasLeadAt (f * g) (d + e) (c * c') :=
  ⟨coeffAt_mul_eq_zero_of_lt hf.1 hg.1,
    by rw [coeffAt_mul_of_vanishing_below hf.1 hg.1, hf.2, hg.2]⟩

end GaloisForLFunctions.HTGeometry
