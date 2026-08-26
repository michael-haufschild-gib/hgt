import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionPrimePowers

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

private theorem sum_divisor_subtype_eq_sum {M : Type*} [AddCommMonoid M]
    (s : Finset ℕ) (f : ℕ → M) :
    (∑ x : {x // x ∈ s}, f x.1) = ∑ x ∈ s, f x := by
  change (∑ x ∈ s.attach, f x.1) = _
  exact Finset.sum_attach s f

theorem selbergPrincipalCoeff_prime_pow_sum {p i j : ℕ} (hp : p.Prime) :
    selbergPrincipalCoeff (p ^ i) (p ^ j) =
      ∑ k ∈ Finset.range (min i j + 1),
        reciprocalNatArithmetic (p ^ k) *
          selbergMoebiusReciprocalCoeff (p ^ (i - k)) *
          selbergMoebiusReciprocalCoeff (p ^ (j - k)) := by
  rw [selbergPrincipalCoeff, bivariateDirichletConvolution,
    if_neg (by simp [hp.ne_zero]), Fintype.sum_prod_type]
  change (∑ x : {x // x ∈ (p ^ i).divisors},
      ∑ y : {y // y ∈ (p ^ j).divisors},
        selbergDiagonalReciprocalCoeff x.1 y.1 *
          selbergMoebiusReciprocalPair ((p ^ i) / x.1) ((p ^ j) / y.1)) = _
  have houter := sum_divisor_subtype_eq_sum (p ^ i).divisors
    (fun x => ∑ y : {y // y ∈ (p ^ j).divisors},
      selbergDiagonalReciprocalCoeff x y.1 *
        selbergMoebiusReciprocalPair ((p ^ i) / x) ((p ^ j) / y.1))
  rw [houter]
  have hinnerConvert :
      (∑ x ∈ (p ^ i).divisors,
        ∑ y : {y // y ∈ (p ^ j).divisors},
          selbergDiagonalReciprocalCoeff x y.1 *
            selbergMoebiusReciprocalPair ((p ^ i) / x) ((p ^ j) / y.1)) =
      ∑ x ∈ (p ^ i).divisors, ∑ y ∈ (p ^ j).divisors,
        selbergDiagonalReciprocalCoeff x y *
          selbergMoebiusReciprocalPair ((p ^ i) / x) ((p ^ j) / y) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact sum_divisor_subtype_eq_sum (p ^ j).divisors
      (fun y => selbergDiagonalReciprocalCoeff x y *
        selbergMoebiusReciprocalPair ((p ^ i) / x) ((p ^ j) / y))
  rw [hinnerConvert]
  rw [Nat.sum_divisors_prime_pow hp]
  have hexpand :
      (∑ a ∈ Finset.range (i + 1),
        ∑ y ∈ (p ^ j).divisors,
          selbergDiagonalReciprocalCoeff (p ^ a) y *
            selbergMoebiusReciprocalPair ((p ^ i) / (p ^ a)) ((p ^ j) / y)) =
      ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1),
          selbergDiagonalReciprocalCoeff (p ^ a) (p ^ b) *
            selbergMoebiusReciprocalPair (p ^ (i - a)) (p ^ (j - b)) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.sum_divisors_prime_pow hp]
    apply Finset.sum_congr rfl
    intro b hb
    have hai : a ≤ i := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hbj : b ≤ j := by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [Nat.pow_div hai hp.pos, Nat.pow_div hbj hp.pos]
  rw [hexpand]
  have hinner : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
        selbergDiagonalReciprocalCoeff (p ^ a) (p ^ b) *
          selbergMoebiusReciprocalPair (p ^ (i - a)) (p ^ (j - b))) =
        if a ≤ j then
          reciprocalNatArithmetic (p ^ a) *
            selbergMoebiusReciprocalPair (p ^ (i - a)) (p ^ (j - a))
        else 0 := by
    intro a ha
    by_cases haj : a ≤ j
    · rw [if_pos haj, Finset.sum_eq_single a]
      · simp [selbergDiagonalReciprocalCoeff]
      · intro b hb hba
        have hpab : p ^ a ≠ p ^ b := fun he =>
          hba ((Nat.pow_right_injective hp.two_le) he).symm
        simp [selbergDiagonalReciprocalCoeff, hpab]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg haj]
      apply Finset.sum_eq_zero
      intro b hb
      have hba : b ≠ a := by
        intro hEq
        subst b
        exact haj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
      have hpab : p ^ a ≠ p ^ b := fun he =>
        hba (Nat.pow_right_injective hp.two_le he).symm
      simp [selbergDiagonalReciprocalCoeff, hpab]
  rw [Finset.sum_congr rfl hinner]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range (i + 1)).filter (fun a => a ≤ j) =
      Finset.range (min i j + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [selbergMoebiusReciprocalPair]
  ring

end

end RHTower.Sieve
