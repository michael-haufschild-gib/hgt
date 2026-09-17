import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale

/-!
# Prime-power support of Euler-deletion clock jumps

The chronological clock changes only at prime-power moduli.  This preserves
the literal EDQ source: it only identifies steps at which no new residue
information can enter a later history layer.
-/

noncomputable section
set_option autoImplicit false

namespace RHTower.DeletionResidueMartingale

/-- A non-prime-power next modulus is already resolved by the preceding
chronological clock. -/
theorem successor_dvd_clock_of_not_isPrimePow (n : ℕ) (hn : ¬ IsPrimePow (n + 1)) :
    n + 1 ∣ clock n := by
  apply (Nat.factorization_le_iff_dvd (Nat.succ_ne_zero n) (clock_pos n).ne').mp
  intro p
  by_cases hp0 : (n + 1).factorization p = 0
  · simp [hp0]
  · have hp : p.Prime := by
      by_contra hnot
      exact hp0 ((Nat.factorization_eq_zero_iff (n + 1) p).mpr (Or.inl hnot))
    have he : 0 < (n + 1).factorization p := Nat.pos_of_ne_zero hp0
    have hpdiv : p ^ (n + 1).factorization p ∣ n + 1 :=
      (hp.pow_dvd_iff_le_factorization (Nat.succ_ne_zero n)).mpr le_rfl
    have hlt : p ^ (n + 1).factorization p < n + 1 := by
      apply lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos n) hpdiv)
      intro hEq
      exact hn ((isPrimePow_nat_iff (n + 1)).mpr
        ⟨p, (n + 1).factorization p, hp, he, hEq⟩)
    have hclock : p ^ (n + 1).factorization p ∣ clock n :=
      dvd_clock (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))
        (Nat.le_of_lt_succ hlt)
    exact (hp.pow_dvd_iff_le_factorization (clock_pos n).ne').mp hclock

/-- Any positive modulus absent from a chronological clock has a prime-power divisor that is
strictly newer than that clock.  This is an exact factorization statement: it introduces no
size estimate and identifies the chronological prime-power coordinate that remains unresolved. -/
theorem exists_primePow_dvd_of_not_dvd_clock
    {L n : ℕ} (hn : n ≠ 0) (hnd : ¬ n ∣ clock L) :
    ∃ q : ℕ, IsPrimePow q ∧ q ∣ n ∧ L < q := by
  have hfac : ¬ n.factorization ≤ (clock L).factorization := by
    intro h
    exact hnd ((Nat.factorization_le_iff_dvd hn (clock_pos L).ne').mp h)
  rw [Finsupp.le_def] at hfac
  push Not at hfac
  obtain ⟨p, hp⟩ := hfac
  have he : 0 < n.factorization p :=
    lt_of_le_of_lt (Nat.zero_le _) hp
  have hprime : p.Prime := by
    by_contra hnot
    have hzero := Nat.factorization_eq_zero_of_not_prime n hnot
    omega
  have hdiv : p ^ n.factorization p ∣ n :=
    (hprime.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hgt : L < p ^ n.factorization p := by
    by_contra hle
    have hclock : p ^ n.factorization p ∣ clock L :=
      dvd_clock (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hprime.ne_zero))
        (Nat.le_of_not_gt hle)
    have hlefac := (hprime.pow_dvd_iff_le_factorization (clock_pos L).ne').mp hclock
    omega
  exact ⟨p ^ n.factorization p,
    (isPrimePow_nat_iff _).mpr ⟨p, n.factorization p, hprime, he, rfl⟩,
    hdiv, hgt⟩

end RHTower.DeletionResidueMartingale
