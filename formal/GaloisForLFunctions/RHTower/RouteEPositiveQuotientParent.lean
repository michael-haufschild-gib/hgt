import GaloisForLFunctions.RHTower.RouteEQuotientParentLoad
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# A negative odd parent for every positive Möbius quotient

Every squarefree quotient q>=3 with Möbius sign +1 is the product of its
least prime factor p and an odd quotient u>=3 with sign -1. This is the
source-faithful parent map needed to test whether the weighted quotient
children can be charged to negative ancestors in Route E. It does not yet
establish the global signed quotient inequality.
-/

open Finset ArithmeticFunction

namespace RHTower

noncomputable section

theorem positive_mobius_quotient_has_negative_odd_parent
    {q : ℕ} (hq : 3 ≤ q) (hμ : moebius q = 1) :
    ∃ p u : ℕ, p.Prime ∧ 3 ≤ u ∧ Odd u ∧ q = p * u ∧
      moebius u = -1 ∧ p = q.minFac := by
  have hsf : Squarefree q := moebius_ne_zero_iff_squarefree.mp (by
    rw [hμ]
    norm_num)
  have hq1 : q ≠ 1 := by omega
  let p := q.minFac
  let u := q / p
  have hpprime : p.Prime := Nat.minFac_prime hq1
  have hpdvd : p ∣ q := Nat.minFac_dvd q
  have hsplit : p * u = q := Nat.mul_div_cancel' hpdvd
  have hnotdvd : ¬ p ∣ u := by
    intro hcon
    obtain ⟨k, hk⟩ := hcon
    have hsq : p * p ∣ q := by
      refine ⟨k, ?_⟩
      calc
        q = p * u := hsplit.symm
        _ = p * (p * k) := by rw [hk]
        _ = p * p * k := by ring
    exact hpprime.ne_one (Nat.isUnit_iff.mp (hsf p hsq))
  have hcop : p.Coprime u :=
    (Nat.Prime.coprime_iff_not_dvd hpprime).mpr hnotdvd
  have hμp : moebius p = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime hpprime
  have hμu : moebius u = -1 := by
    have hmul := Sieve.moebius_mul_of_coprime hcop
    have hq : moebius (p * u) = 1 := hsplit ▸ hμ
    rw [hmul, hμp] at hq
    omega
  have hodd : Odd u := by
    by_contra hodd
    have heven : Even u := (Nat.not_odd_iff_even).mp hodd
    have h2u : 2 ∣ u := even_iff_two_dvd.mp heven
    have h2q : 2 ∣ q := by
      rw [← hsplit]
      exact dvd_mul_of_dvd_right h2u p
    have hp2 : p = 2 := by
      have hple : p ≤ 2 := Nat.minFac_le_of_dvd (by norm_num) h2q
      have hpge := hpprime.two_le
      omega
    exact hnotdvd (hp2 ▸ h2u)
  have hu3 : 3 ≤ u := by
    have hu2 : 2 ≤ u := by
      by_contra hlt
      have hu1 : u ≤ 1 := by omega
      interval_cases u
      · simp at hμu
      · simp at hμu
    rcases hodd with ⟨k, hk⟩
    omega
  exact ⟨p, u, hpprime, hu3, hodd, hsplit.symm, hμu, rfl⟩

end
end RHTower
