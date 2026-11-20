import GaloisForLFunctions.SignedArithmeticCorrespondences.TheMinimizingCorrectionOnASublatticeOfTheWeilComb

/-!
# The odd–even coupling of the Weil comb sees only the prime two

Split the Weil comb into its even block `A`, odd block `C` and coupling `B`. The odd-sector Schur
complement `C − BᵀA⁻¹B` is driven by the even rows of an odd profile `o`, the forces that the even
correction must cancel. These rows are explicit:

  `row_i(o) = d₁(o) + d₂(o)/i − Σ_{m ≠ i} o_m J(m, i) − log 2 · o(i')`,

where `J` is the jet kernel and `i'` is the odd part of `i` (`combSiteRow_of_odd`). The reason is
arithmetic: an odd `m` and an even `i` are in contact only along the ray `i = 2^k m`, with weight
`Λ(2^k) = log 2` (`contact_odd_even`). So the coupling `B` carries no prime other than `2`; every
odd prime enters the odd sector through `C` alone. For a two-block odd profile, `α` up to a cut `T`
and `β` beyond it, the arithmetic force at `i` is `log 2` times `α` or `β` according to the side
of the cut on which the odd part of `i` lies (`combSiteRow_twoBlock`).
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open HodgeTheoryOfAFixedPart AbsoluteGeometryOfSpecZ

/-- **An odd and an even degree point meet only along a power-of-two ray.** -/
theorem contact_odd_even {m i : ℕ} (hm : ¬ 2 ∣ m) (hi : 2 ∣ i) (hi0 : 0 < i) :
    contact m i = if m = ordCompl[2] i then Real.log 2 else 0 := by
  unfold contact
  have h2 : ¬ i ∣ m := fun h => hm (hi.trans h)
  rw [if_neg h2, add_zero]
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hm (h ▸ dvd_zero 2)
  by_cases hd : m ∣ i
  · rw [if_pos hd]
    obtain ⟨q, rfl⟩ := hd
    have hq : 2 ∣ q := ((Nat.Prime.dvd_mul Nat.prime_two).mp hi).resolve_left hm
    have hq0 : q ≠ 0 := fun h => by rw [h, mul_zero] at hi0; exact lt_irrefl 0 hi0
    rw [Nat.mul_div_cancel_left q hm0]
    by_cases hpp : IsPrimePow q
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpp
      have hp2 : p = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow hq)).symm
      subst hp2
      have hfac : (m * 2^k).factorization 2 = k := by
        rw [Nat.factorization_mul hm0.ne' (pow_ne_zero k two_ne_zero), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hm, Nat.factorization_pow, Finsupp.smul_apply,
          Nat.prime_two.factorization_self, smul_eq_mul, mul_one, zero_add]
      have hoc : m = ordCompl[2] (m * 2^k) := by
        rw [hfac, Nat.mul_div_cancel _ (pow_pos two_pos k)]
      rw [if_pos hoc, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, if_neg]
      intro heq
      apply hpp
      have hself := Nat.ordProj_mul_ordCompl_eq_self (m * q) 2
      rw [← heq] at hself
      have hqeq : q = 2 ^ (m * q).factorization 2 := by
        apply Nat.eq_of_mul_eq_mul_left hm0
        rw [mul_comm m (2 ^ _), hself]
      have hv : (m * q).factorization 2 ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hqeq
        rw [hqeq] at hq
        exact absurd hq (by norm_num)
      rw [hqeq]
      exact Nat.prime_two.isPrimePow.pow hv
  · rw [if_neg hd, if_neg]
    intro heq
    exact hd (heq ▸ Nat.ordCompl_dvd i 2)

/-- The odd part of an even number is a different number. -/
private theorem ordCompl_ne_self {i : ℕ} (hi : 2 ∣ i) (hi0 : 0 < i) : ordCompl[2] i ≠ i := by
  intro h
  have hv : i.factorization 2 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hi0.ne' hi).ne'
  have hlt : i / 2 ^ i.factorization 2 < i :=
    Nat.div_lt_self hi0 (Nat.one_lt_two_pow hv)
  exact (ne_of_lt hlt) h

/-- **The even rows of an odd profile.** For a profile vanishing at the even sites of `S`, the row
of an even site `i ∈ S` is the degree term, minus the jet row, minus `log 2` times the profile at
the odd part of `i`. -/
theorem combSiteRow_of_odd (S : Finset ℕ) (o : ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n)
    (ho : ∀ n ∈ S, 2 ∣ n → o n = 0) {i : ℕ} (hiS : i ∈ S) (hi : 2 ∣ i) :
    combSiteRow S o i = degOne S o + degTwo S o / i - ∑ m ∈ S.erase i, o m * jetKernel m i -
      (if ordCompl[2] i ∈ S then Real.log 2 * o (ordCompl[2] i) else 0) := by
  have hi0 := hS i hiS
  let δ : ℕ → ℝ := fun n => if n = i then 1 else 0
  have hd2 : degTwo S δ = 1 := by
    simp only [degTwo, δ, sum_ite_eq', if_pos hiS]
  have hd1 : degOne S δ = 1 / i := by
    simp only [degOne, δ, ite_div, zero_div, sum_ite_eq', if_pos hiS]
  have hbil : combBilin S o δ = ∑ m ∈ S.erase i, o m * pairKernel m i := by
    unfold combBilin
    have h1 : ∑ n ∈ S, ∑ m ∈ S.erase n, o m * δ n * pairKernel m n =
        ∑ m ∈ S.erase i, o m * pairKernel m i := by
      rw [sum_eq_single i]
      · exact sum_congr rfl fun m _ => by simp [δ]
      · intro n _ hn; exact sum_eq_zero fun m _ => by simp [δ, hn]
      · intro h; exact absurd hiS h
    have h2 : ∑ n ∈ S, o n * δ n * counterterm n = 0 :=
      sum_eq_zero fun n hn => by
        by_cases h : n = i
        · subst h; rw [ho n hn hi]; ring
        · simp [δ, h]
    rw [h1, h2, sub_zero]
  have hcontact : ∑ m ∈ S.erase i, o m * contact m i =
      if ordCompl[2] i ∈ S then Real.log 2 * o (ordCompl[2] i) else 0 := by
    have hterm : ∀ m ∈ S.erase i, o m * contact m i =
        if m = ordCompl[2] i then Real.log 2 * o (ordCompl[2] i) else 0 := by
      intro m hm
      have hmS := mem_of_mem_erase hm
      by_cases hm2 : 2 ∣ m
      · rw [ho m hmS hm2, zero_mul]
        have hne : m ≠ ordCompl[2] i := by
          intro h
          have hodd : ¬ 2 ∣ ordCompl[2] i := Nat.not_dvd_ordCompl Nat.prime_two hi0.ne'
          exact hodd (h ▸ hm2)
        rw [if_neg hne]
      · rw [contact_odd_even hm2 hi hi0]
        split_ifs with h
        · subst h; ring
        · ring
    rw [sum_congr rfl hterm, sum_ite_eq']
    by_cases hc : ordCompl[2] i ∈ S
    · rw [if_pos (mem_erase.mpr ⟨ordCompl_ne_self hi hi0, hc⟩), if_pos hc]
    · rw [if_neg (fun h => hc (mem_of_mem_erase h)), if_neg hc]
  have hsplit : ∑ m ∈ S.erase i, o m * pairKernel m i =
      ∑ m ∈ S.erase i, o m * jetKernel m i + ∑ m ∈ S.erase i, o m * contact m i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun m _ => by rw [pairKernel]; ring
  change formBilin S o δ = _
  rw [formBilin, hd1, hd2, hbil, hsplit, hcontact]
  ring

/-- **Two-block odd profiles.** With the value `α` on the odd sites up to `T` and `β` beyond, the
arithmetic force on an even row is `log 2` times the value on the side of the odd part. -/
theorem combSiteRow_twoBlock (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (T : ℕ) (α β : ℝ)
    {i : ℕ} (hiS : i ∈ S) (hi : 2 ∣ i) :
    let o : ℕ → ℝ := fun n => if 2 ∣ n then 0 else if n ≤ T then α else β
    combSiteRow S o i = degOne S o + degTwo S o / i - ∑ m ∈ S.erase i, o m * jetKernel m i -
      (if ordCompl[2] i ∈ S then Real.log 2 * (if ordCompl[2] i ≤ T then α else β) else 0) := by
  intro o
  have hodd : ¬ 2 ∣ ordCompl[2] i := Nat.not_dvd_ordCompl Nat.prime_two (hS i hiS).ne'
  rw [combSiteRow_of_odd S o hS (fun n _ hn => if_pos hn) hiS hi]
  simp only [o, if_neg hodd]

#print axioms contact_odd_even
#print axioms combSiteRow_of_odd
#print axioms combSiteRow_twoBlock

end GaloisForLFunctions.SignedArithmeticCorrespondences
