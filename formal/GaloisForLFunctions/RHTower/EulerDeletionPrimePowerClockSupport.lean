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

end RHTower.DeletionResidueMartingale
