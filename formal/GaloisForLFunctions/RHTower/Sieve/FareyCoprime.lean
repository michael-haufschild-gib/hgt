import GaloisForLFunctions.RHTower.Sieve.LargeSieveFarey

/-!
# Reduced fractions are automatically distinct modulo one

`LargeSieveFarey.lean` assumes the fractions are distinct modulo one, stated as `qq' ∤ aq' - a'q`.
For *reduced* fractions in the standard range that hypothesis is a consequence of coprimality:

if `qq' ∣ aq' - a'q` with `(a,q) = (a',q') = 1`, then `q ∣ aq'` forces `q ∣ q'` and symmetrically
`q' ∣ q`, so `q = q'`; cancelling gives `q ∣ a - a'`, and `1 ≤ a, a' ≤ q` leaves `a = a'`.

So the large sieve applies to the Farey set of order `Q` with no hypothesis beyond membership.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Distinct reduced fractions are distinct modulo one.** -/
theorem not_dvd_farey_cross {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (ha1 : 1 ≤ a) (haq : a ≤ q) (ha1' : 1 ≤ a') (haq' : a' ≤ q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (hne : (a, q) ≠ (a', q')) :
    ¬ (((q * q' : ℕ) : ℤ) ∣ ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ))) := by
  intro hdvd
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hcast : (((q * q' : ℕ)) : ℤ) = (q : ℤ) * (q' : ℤ) := by push_cast; ring
  rw [hcast] at hdvd
  -- `q` divides the cross difference, hence `a q'`
  have hqd : (q : ℤ) ∣ ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)) :=
    dvd_trans (dvd_mul_right (q : ℤ) (q' : ℤ)) hdvd
  have hqa : (q : ℤ) ∣ (a : ℤ) * (q' : ℤ) := by
    have h3 := dvd_add hqd (dvd_mul_left (q : ℤ) (a' : ℤ))
    have heq : ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)) + (a' : ℤ) * (q : ℤ)
        = (a : ℤ) * (q' : ℤ) := by ring
    rwa [heq] at h3
  have hcq : IsCoprime ((q : ℤ)) ((a : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hdvd1 : (q : ℤ) ∣ (q' : ℤ) := hcq.dvd_of_dvd_mul_left hqa
  -- symmetrically `q'` divides `a' q`
  have hq'd : (q' : ℤ) ∣ ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ)) :=
    dvd_trans (dvd_mul_left (q' : ℤ) (q : ℤ)) hdvd
  have hq'a : (q' : ℤ) ∣ (a' : ℤ) * (q : ℤ) := by
    have h3 := dvd_sub (dvd_mul_left (q' : ℤ) (a : ℤ)) hq'd
    have heq : (a : ℤ) * (q' : ℤ) - ((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ))
        = (a' : ℤ) * (q : ℤ) := by ring
    rwa [heq] at h3
  have hcq' : IsCoprime ((q' : ℤ)) ((a' : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop'.symm
  have hdvd2 : (q' : ℤ) ∣ (q : ℤ) := hcq'.dvd_of_dvd_mul_left hq'a
  -- so the denominators agree
  have hqq : q = q' :=
    Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hdvd1) (Int.natCast_dvd_natCast.mp hdvd2)
  subst hqq
  -- cancelling the common denominator leaves `q ∣ a - a'`, and the range forces `a = a'`
  have hform : (a : ℤ) * (q : ℤ) - (a' : ℤ) * (q : ℤ) = (q : ℤ) * ((a : ℤ) - (a' : ℤ)) := by ring
  rw [hform] at hdvd
  have hcancel : (q : ℤ) ∣ ((a : ℤ) - (a' : ℤ)) :=
    (mul_dvd_mul_iff_left (ne_of_gt hqz)).mp hdvd
  have habs : |(a : ℤ) - (a' : ℤ)| < (q : ℤ) := by
    have h1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha1
    have h2 : (a : ℤ) ≤ (q : ℤ) := by exact_mod_cast haq
    have h3 : (1 : ℤ) ≤ (a' : ℤ) := by exact_mod_cast ha1'
    have h4 : (a' : ℤ) ≤ (q : ℤ) := by exact_mod_cast haq'
    rw [abs_lt]
    constructor <;> linarith
  have hzero : (a : ℤ) - (a' : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hcancel habs
  have haa : a = a' := by
    have hcastaa : (a : ℤ) = (a' : ℤ) := by linarith
    exact_mod_cast hcastaa
  exact hne (by rw [haa])

/-- **Large sieve on the Farey set of order `Q`.**  No hypothesis beyond membership. -/
theorem largeSieve_farey_reduced (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (s : Finset (ℕ × ℕ))
    (hmem : ∀ p ∈ s, 0 < p.2 ∧ p.2 ≤ Q ∧ 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2)
    (x : EuclideanSpace ℂ (Fin N)) :
    ∑ p ∈ s, ‖⟪expRow N (circleFreq ((p.1 : ℝ) / (p.2 : ℝ))), x⟫_ℂ‖ ^ 2
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2 + 1))) * ‖x‖ ^ 2 := by
  classical
  have hden : ∀ p ∈ s, 0 < (fun p : ℕ × ℕ => p.2) p := fun p hp => (hmem p hp).1
  have hQden : ∀ p ∈ s, (fun p : ℕ × ℕ => p.2) p ≤ Q := fun p hp => (hmem p hp).2.1
  have hdist : ∀ p ∈ s, ∀ r ∈ s, p ≠ r →
      ¬ ((((fun p : ℕ × ℕ => p.2) p * (fun p : ℕ × ℕ => p.2) r : ℕ) : ℤ) ∣
        ((fun p : ℕ × ℕ => (p.1 : ℤ)) p * (((fun p : ℕ × ℕ => p.2) r : ℕ) : ℤ)
          - (fun p : ℕ × ℕ => (p.1 : ℤ)) r * (((fun p : ℕ × ℕ => p.2) p : ℕ) : ℤ))) := by
    intro p hp r hr hpr
    obtain ⟨hp2, _, hp1, hp12, hpc⟩ := hmem p hp
    obtain ⟨hr2, _, hr1, hr12, hrc⟩ := hmem r hr
    have hne : (p.1, p.2) ≠ (r.1, r.2) := by simpa using hpr
    exact not_dvd_farey_cross hp2 hr2 hp1 hp12 hr1 hr12 hpc hrc hne
  have hbase := largeSieve_farey N s hQ (fun p : ℕ × ℕ => (p.1 : ℤ)) (fun p : ℕ × ℕ => p.2)
    hden hQden hdist x
  refine le_trans (le_of_eq ?_) hbase
  refine Finset.sum_congr rfl fun p _ => ?_
  have hc : ((((p.1 : ℕ) : ℤ)) : ℝ) = ((p.1 : ℕ) : ℝ) := by push_cast; ring
  rw [hc]

end RHTower.Sieve
