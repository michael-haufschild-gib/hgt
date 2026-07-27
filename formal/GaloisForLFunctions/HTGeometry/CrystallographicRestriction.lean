import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge

/-!
# The crystallographic restriction

The parabolic sphere signatures have holonomy orders `1, 2, 3, 4, 6`, proved by inspecting the six
cases.  The list is not an accident of the enumeration: those are exactly the positive integers whose
totient is at most two, which is the arithmetic form of the crystallographic restriction — a rotation
preserving a rank-two lattice has order in that list.

* **`totient_le_two_iff`** — `φ n ≤ 2` exactly for `n ∈ {1, 2, 3, 4, 6}`;
* `holonomyOrder_totient_le_two` — the enumeration's holonomy orders satisfy it, derived from the
  general law rather than by inspection.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Crystallographic restriction.**  A positive integer has totient at most two exactly when it is
one of `1, 2, 3, 4, 6`.  A prime factor `p` contributes `p - 1` to the totient, `8` contributes `4`
and `9` contributes `6`, so the number divides twelve. -/
theorem totient_le_two_iff {n : ℕ} (hn : 0 < n) :
    n.totient ≤ 2 ↔ (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) := by
  constructor
  · intro h
    have hφpos : 0 < n.totient := Nat.totient_pos.mpr hn
    have hstep : ∀ d : ℕ, d ∣ n → d.totient ≤ 2 := by
      intro d hd
      exact le_trans (Nat.le_of_dvd hφpos (Nat.totient_dvd_of_dvd hd)) h
    have hdvd : n ∣ 12 := by
      rw [← Nat.factorization_le_iff_dvd hn.ne' (by norm_num)]
      intro p
      by_cases hp : p.Prime
      · rcases eq_or_ne p 2 with rfl | hp2
        · by_contra hcon
          push Not at hcon
          have h8 : (2 : ℕ) ^ 3 ∣ n := by
            rw [Nat.Prime.pow_dvd_iff_le_factorization hp hn.ne']
            have : (12 : ℕ).factorization 2 = 2 := by decide +kernel
            omega
          have h8' := hstep 8 (by norm_num at h8 ⊢; exact h8)
          rw [show Nat.totient 8 = 4 from by decide +kernel] at h8'
          omega
        · rcases eq_or_ne p 3 with rfl | hp3
          · by_contra hcon
            push Not at hcon
            have h9 : (3 : ℕ) ^ 2 ∣ n := by
              rw [Nat.Prime.pow_dvd_iff_le_factorization hp hn.ne']
              have : (12 : ℕ).factorization 3 = 1 := by decide +kernel
              omega
            have h9' := hstep 9 (by norm_num at h9 ⊢; exact h9)
            rw [show Nat.totient 9 = 6 from by decide +kernel] at h9'
            omega
          · have hnd : ¬p ∣ n := by
              intro hpdvd
              have hφp := hstep p hpdvd
              rw [Nat.totient_prime hp] at hφp
              have hple : p ≤ 2 + 1 := Nat.sub_le_iff_le_add.mp hφp
              have hpge := hp.two_le
              omega
            have hp12 : ¬p ∣ 12 := by
              intro hpdvd
              have hfactor : (12 : ℕ) = 3 * 2 ^ 2 := by norm_num
              rw [hfactor] at hpdvd
              rcases hp.dvd_mul.mp hpdvd with h3 | h2
              · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h3)
              · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
                  (hp.dvd_of_dvd_pow h2))
            simp [Nat.factorization_eq_zero_of_not_dvd hnd,
              Nat.factorization_eq_zero_of_not_dvd hp12]
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    have hle : n ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> revert h hdvd <;> decide +kernel
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> decide +kernel

/-- The holonomy orders of the parabolic sphere signatures satisfy the crystallographic restriction,
as a consequence of the general law. -/
theorem holonomyOrder_totient_le_two (s : ParabolicSphereSignature) :
    s.holonomyOrder.totient ≤ 2 :=
  (totient_le_two_iff s.holonomyOrder_pos).2 s.holonomyOrder_mem

end GaloisForLFunctions.HTGeometry
