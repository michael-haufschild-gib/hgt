import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ThinEditsPayAPowerInTheCount

/-!
# Additions are paid in full

A system whose norm multiplicities are `1 * u` with `u ≥ 0` contains the integers as a factor.
Chebyshev's identity `N(x) − 2 N(x/2) = Σ_d u(d) [⌊x/d⌋ odd]` then bounds the mass of `u` on
`(x/2, x]` by the count remainder (`sum_Ioc_half_le_of_count`).

* **Add-only edits** (`expo_plus_le_of_add_only`).  An edit without deleted primes with count
  `A x + O(x^β)` has `κ₊ ≤ β`.  With the count of an edit (every `β > κ₊` is a count exponent)
  the count exponent of an add-only edit is exactly the exponent of its doubled primes.
* **Putting the deleted primes back** (`freeFn_mul_freeFn_compl`, `intCount_restored`).  The
  system of an edit with the deleted primes added again has the norm count `1 * 1_{Tᶜ}`; thin
  additions keep the count rate.
* **Count balance** (`expo_plus_le_max`).  `κ₊ ≤ max(β, κ₋)` for every edit: doubled primes
  beyond the count exponent are matched by deleted primes.  No continuation of the zeta function
  is used.

Deletions are not paid in full: for them only `κ (1 − κ) ≤ 2β (2 − κ)` is known.
-/

open Complex Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountFloor

open ThinAdditions TwoSidedEdits NormCount BalanceLaw PrimeEdits

/-! ## From dyadic bounds to the exponent -/

open Classical in
/-- A set of integers above `1` with `O(x^β)` elements in every `(x/2, x]` has `O(Q^η)` elements
below `Q`, for every `η ≥ β`, `η > 0`. -/
theorem card_le_of_dyadic {U : Set ℕ} (hU : ∀ k ∈ U, 2 ≤ k) {c₁ c₂ β η : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hβη : β ≤ η) (hη0 : 0 < η)
    (hdy : ∀ x : ℕ, 2 ≤ x → (((Ioc (x / 2) x).filter (fun k => k ∈ U)).card : ℝ) ≤
      c₁ * (x : ℝ) ^ β + c₂) :
    ∀ Q : ℕ, (((Ioc 0 Q).filter (fun k => k ∈ U)).card : ℝ) ≤
      (c₁ + c₂) / (1 - (2 : ℝ) ^ (-η)) * (Q : ℝ) ^ η := by
  classical
  have hq1 : (2 : ℝ) ^ (-η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1q : 0 < 1 - (2 : ℝ) ^ (-η) := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (c₁ + c₂) / (1 - (2 : ℝ) ^ (-η)) := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (by linarith) h1q.le
  have h1q' : 1 - (2 : ℝ) ^ (-η) ≠ 0 := h1q.ne'
  have hcq : c * (2 : ℝ) ^ (-η) + (c₁ + c₂) = c := by
    rw [hc]
    field_simp
    ring
  intro Q
  induction Q using Nat.strong_induction_on with
  | _ Q ih =>
    rcases Nat.lt_or_ge Q 2 with h2 | h2
    · have hempty : (Ioc 0 Q).filter (fun k => k ∈ U) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk hmem
        have h1 := (mem_Ioc.mp hk).2
        have h3 := hU k hmem
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
      have hsplit : (Ioc 0 Q).filter (fun k => k ∈ U) =
          (Ioc 0 (Q / 2)).filter (fun k => k ∈ U) ∪ (Ioc (Q / 2) Q).filter (fun k => k ∈ U) := by
        rw [← Finset.filter_union]
        congr 1
        ext k
        simp only [mem_Ioc, mem_union]
        omega
      have hcard := Finset.card_union_le ((Ioc 0 (Q / 2)).filter (fun k => k ∈ U))
        ((Ioc (Q / 2) Q).filter (fun k => k ∈ U))
      rw [← hsplit] at hcard
      have hcardR : (((Ioc 0 Q).filter (fun k => k ∈ U)).card : ℝ) ≤
          (((Ioc 0 (Q / 2)).filter (fun k => k ∈ U)).card : ℝ) +
            (((Ioc (Q / 2) Q).filter (fun k => k ∈ U)).card : ℝ) := by
        exact_mod_cast hcard
      have hih := ih (Q / 2) (by omega)
      have hd := hdy Q h2
      have hpow : ((Q / 2 : ℕ) : ℝ) ^ η ≤ (Q : ℝ) ^ η * (2 : ℝ) ^ (-η) := by
        have h := Real.rpow_le_rpow (Nat.cast_nonneg _)
          (Nat.cast_div_le (α := ℝ) (m := Q) (n := 2)) hη0.le
        rw [Nat.cast_ofNat, Real.div_rpow (Nat.cast_nonneg Q) (by norm_num)] at h
        rwa [Real.rpow_neg (by norm_num), ← div_eq_mul_inv]
      have hQη : (1 : ℝ) ≤ (Q : ℝ) ^ η := Real.one_le_rpow hQ1 hη0.le
      have hQβ : (Q : ℝ) ^ β ≤ (Q : ℝ) ^ η := Real.rpow_le_rpow_of_exponent_le hQ1 hβη
      have h3 : c₁ * (Q : ℝ) ^ β + c₂ ≤ (c₁ + c₂) * (Q : ℝ) ^ η := by
        nlinarith [mul_le_mul_of_nonneg_left hQβ hc₁, mul_le_mul_of_nonneg_left hQη hc₂]
      have h4 := mul_le_mul_of_nonneg_left hpow hc0
      calc (((Ioc 0 Q).filter (fun k => k ∈ U)).card : ℝ)
          ≤ c * ((Q / 2 : ℕ) : ℝ) ^ η + (c₁ * (Q : ℝ) ^ β + c₂) := by linarith
        _ ≤ c * ((Q : ℝ) ^ η * (2 : ℝ) ^ (-η)) + (c₁ + c₂) * (Q : ℝ) ^ η := by linarith
        _ = (c * (2 : ℝ) ^ (-η) + (c₁ + c₂)) * (Q : ℝ) ^ η := by ring
        _ = c * (Q : ℝ) ^ η := by rw [hcq]

open Classical in
/-- A set of integers above `1` with `O(x^β)` elements in every `(x/2, x]` has exponent at most
`β`. -/
theorem expo_le_of_dyadic {U : Set ℕ} (hU : ∀ k ∈ U, 2 ≤ k) {c₁ c₂ β : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hβ : 0 ≤ β)
    (hdy : ∀ x : ℕ, 2 ≤ x → (((Ioc (x / 2) x).filter (fun k => k ∈ U)).card : ℝ) ≤
      c₁ * (x : ℝ) ^ β + c₂) : expo U ≤ β := by
  classical
  by_contra hlt
  have hlt' : β < expo U := not_le.mp hlt
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (β + expo U) / 2 := ⟨_, rfl⟩
  have hη1 : β < η := by rw [hη]; linarith
  have hη2 : η < expo U := by rw [hη]; linarith
  have hη0 : 0 < η := lt_of_le_of_lt hβ hη1
  have hq1 : (2 : ℝ) ^ (-η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc0 : 0 ≤ (c₁ + c₂) / (1 - (2 : ℝ) ^ (-η)) := div_nonneg (by linarith) (by linarith)
  have hsum : SummableAt U ((η + expo U) / 2) := by
    refine summableAt_of_card_le hc0 hη0.le hU (fun Q D _ hD => ?_) (by linarith)
    refine le_trans ?_ (card_le_of_dyadic hU hc₁ hc₂ hη1.le hη0 hdy Q)
    have hsub : D ⊆ (Ioc 0 Q).filter (fun k => k ∈ U) := fun p hp => by
      obtain ⟨hpQ, hpU⟩ := hD p hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := hU p hpU; omega, hpQ⟩, hpU⟩
    exact_mod_cast Finset.card_le_card hsub
  have h := expo_le_of_summableAt (T := U) (by linarith) hsum
  linarith

/-! ## Chebyshev's identity for a system -/

/-- If the norm multiplicities of `B` are `1 * u` with `u ≥ 0` and `N(x) = A x + O(x^β)`, the
mass of `u` on `(x/2, x]` is at most `3 C x^β + A`. -/
theorem sum_Ioc_half_le_of_count {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hd : B.IsDiscrete) {u : ℕ → ℝ} (hu : ∀ d, 0 ≤ u d)
    (hau : ∀ n, 1 ≤ n → (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ) =
      ∑ d ∈ n.divisors, u d)
    {A C β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) {x : ℕ} (hx : 2 ≤ x) :
    ∑ d ∈ Ioc (x / 2) x, u d ≤ 3 * C * (x : ℝ) ^ β + A := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have h1 : ∑ d ∈ Ioc (x / 2) x, u d ≤
      (∑ n ∈ Ioc 0 x, (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ)) -
        2 * ∑ n ∈ Ioc 0 (x / 2), (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ) :=
    CountSieve.sum_Ioc_half_le
      (a := fun n => (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ)) hau hu x
  rw [sum_intCount_eq_countBall h hd, sum_intCount_eq_countBall h hd] at h1
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx2 : (1 : ℝ) ≤ ((x / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ x / 2)
  have hc1 := abs_le.mp (hN (x : ℝ) hx1)
  have hc2 := abs_le.mp (hN ((x / 2 : ℕ) : ℝ) hx2)
  have hpow : C * ((x / 2 : ℕ) : ℝ) ^ β ≤ C * (x : ℝ) ^ β :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.div_le_self x 2) hβ) hC
  have hhalf : (x : ℝ) - 2 * ((x / 2 : ℕ) : ℝ) ≤ 1 := by
    have h2 : x ≤ 2 * (x / 2) + 1 := by omega
    have h2' : (x : ℝ) ≤ 2 * ((x / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    linarith
  have hAh := mul_le_mul_of_nonneg_left hhalf hA
  linarith [hc1.2, hc2.1]

open Classical in
/-- The doubled primes in `(x/2, x]` are counted by the integers composed of doubled primes. -/
theorem card_plus_Ioc_le_sum {e : ℕ → ℤ} (he : IsEdit e) (x : ℕ) :
    (((Ioc (x / 2) x).filter (fun k => k ∈ plusSet e)).card : ℝ) ≤
      ∑ d ∈ Ioc (x / 2) x, freeFn (plusSet e)ᶜ d := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [freeFn_apply]
  split_ifs with hk
  · rw [sFreeR_prime _ (prime_of_mem_plusSet he hk),
      if_neg (fun hc : k ∈ (plusSet e)ᶜ => hc hk)]
    simp
  · simpa using sFreeR_nonneg (plusSet e)ᶜ k

/-! ## Add-only edits -/

/-- The Möbius function of the empty set of primes is the unit. -/
theorem mobFn_empty : mobFn (∅ : Set ℕ) = 1 := by
  classical
  ext n
  rw [mobFn_apply, ArithmeticFunction.one_apply]
  unfold mobSet
  by_cases hn : n = 1
  · subst hn
    rw [if_pos ⟨one_ne_zero, by simp⟩]
    simp
  · rw [if_neg hn, if_neg]
    rintro ⟨hn0, hall⟩
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
    exact (Set.mem_empty_iff_false p).mp (hall p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩))

/-- **Additions are paid in full.**  An edit without deleted primes with count
`A x + O(x^β)` has `κ₊ ≤ β`. -/
theorem expo_plus_le_of_add_only {e : ℕ → ℤ} (he : IsEdit e) (hm : minusSet e = ∅) {A C β : ℝ}
    (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    expo (plusSet e) ≤ β := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have hN' : ∀ y : ℝ, 1 ≤ y →
      |((sumSystem (keptPrimeSystem ∅) (keptPrimeSystem (plusSet e)ᶜ)).countBall y : ℝ) - A * y| ≤
        C * y ^ β := by
    intro y hy
    have h := hN y hy
    unfold editSystem at h
    rwa [hm] at h
  have hau : ∀ n, 1 ≤ n → (SumProductArithmeticOfTheLogarithm.intCount
      (sumSystem (keptPrimeSystem ∅) (keptPrimeSystem (plusSet e)ᶜ))
      (hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem ∅)
        (hasIntegerNorms_keptPrimeSystem (plusSet e)ᶜ)) n : ℝ) =
      ∑ d ∈ n.divisors, (fun d => freeFn (plusSet e)ᶜ d) d := by
    intro n _
    rw [intCount_eq, normCount_eq_sum_divisors, mobFn_empty, one_mul]
  refine expo_le_of_dyadic (c₁ := 3 * C) (c₂ := A)
    (fun k hk => (prime_of_mem_plusSet he hk).two_le) (by linarith) hA hβ fun x hx => ?_
  exact (card_plus_Ioc_le_sum he x).trans
    (sum_Ioc_half_le_of_count _ (isDiscrete_sumSystem (isDiscrete_keptPrimeSystem ∅)
      (isDiscrete_keptPrimeSystem (plusSet e)ᶜ)) (fun d => freeFn_nonneg _ d) hau hA hβ hN' hx)

/-! ## Putting the deleted primes back -/

/-- `μ_S * 1_{Sᶜ}` is the unit: on an integer composed of primes of `S` it is the divisor sum of
`μ`, and any other integer has no decomposition. -/
theorem mobFn_mul_freeFn_compl (S : Set ℕ) : mobFn S * freeFn Sᶜ = 1 := by
  classical
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  by_cases hcomp : SFree Sᶜ n
  · have hterm : ∀ x ∈ n.divisorsAntidiagonal,
        mobFn S x.1 * freeFn Sᶜ x.2 = ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) := by
      intro x hx
      obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have h1 : x.1 ≠ 0 := fun h0 => hn (by rw [← hx1, h0, zero_mul])
      have h2 : x.2 ≠ 0 := fun h0 => hn (by rw [← hx1, h0, mul_zero])
      have hd1 : x.1 ∣ n := ⟨x.2, hx1.symm⟩
      have hd2 : x.2 ∣ n := ⟨x.1, by rw [← hx1, mul_comm]⟩
      have hs1 : sOnly S x.1 :=
        ⟨h1, fun p hp => by simpa using hcomp.2 p (Nat.primeFactors_mono hd1 hn hp)⟩
      have hs2 : SFree Sᶜ x.2 :=
        ⟨h2, fun p hp => hcomp.2 p (Nat.primeFactors_mono hd2 hn hp)⟩
      rw [mobFn_apply, freeFn_apply]
      unfold mobSet sFreeR
      rw [if_pos hs1, if_pos hs2, mul_one]
    have hmu : ∑ i ∈ n.divisors, ((ArithmeticFunction.moebius i : ℤ) : ℝ) =
        (1 : ArithmeticFunction ℝ) n := by
      rw [← ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ),
        ArithmeticFunction.coe_mul_zeta_apply]
      simp
    rw [Finset.sum_congr rfl hterm,
      Nat.sum_divisorsAntidiagonal fun i _ => ((ArithmeticFunction.moebius i : ℤ) : ℝ)]
    exact hmu
  · have hex : ∃ q ∈ n.primeFactors, q ∈ Sᶜ := by
      by_contra hcon
      exact hcomp ⟨hn, fun p hp hpS => hcon ⟨p, hp, hpS⟩⟩
    obtain ⟨q, hq, hqS⟩ := hex
    obtain ⟨hqp, hqn, -⟩ := Nat.mem_primeFactors.mp hq
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at hq
    rw [ArithmeticFunction.one_apply, if_neg hn1]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hx1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hdiv : q ∣ x.1 * x.2 := by
      rw [hx1]
      exact hqn
    rcases (Nat.Prime.dvd_mul hqp).mp hdiv with h | h
    · rw [mobFn_apply, mobSet_eq_zero_of_dvd hqp hqS h, zero_mul]
    · rw [freeFn_apply, sFreeR_eq_zero_of_dvd hqp hqS h, mul_zero]

/-- Every positive integer is uniquely an integer without prime factor in `S` times an integer
composed of primes of `S`: `1_S * 1_{Sᶜ} = 1`. -/
theorem freeFn_mul_freeFn_compl (S : Set ℕ) :
    freeFn S * freeFn Sᶜ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  rw [freeFn_eq S, mul_assoc, mobFn_mul_freeFn_compl, mul_one]

/-- The system of an edit with the deleted primes put back has the norm count `1 * 1_{Tᶜ}`. -/
theorem intCount_restored (S T : Set ℕ) (n : ℕ) :
    (SumProductArithmeticOfTheLogarithm.intCount
      (sumSystem (sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ)) (keptPrimeSystem Sᶜ))
      (hasIntegerNorms_sumSystem (hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem S)
        (hasIntegerNorms_keptPrimeSystem Tᶜ)) (hasIntegerNorms_keptPrimeSystem Sᶜ)) n : ℝ) =
      ∑ d ∈ n.divisors, freeFn Tᶜ d := by
  have h : freeFn S * freeFn Tᶜ * freeFn Sᶜ =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * freeFn Tᶜ := by
    rw [mul_right_comm, freeFn_mul_freeFn_compl]
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ← h,
    intCount_sumSystem (hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem S)
      (hasIntegerNorms_keptPrimeSystem Tᶜ)) (hasIntegerNorms_keptPrimeSystem Sᶜ)
      (isDiscrete_sumSystem (isDiscrete_keptPrimeSystem S) (isDiscrete_keptPrimeSystem Tᶜ))
      (isDiscrete_keptPrimeSystem Sᶜ), Nat.cast_sum, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul, intCount_eq, intCount_keptPrimeSystem, freeFn_apply]

/-- Summability of a set of positive integers in the two notations. -/
theorem summable_indicator_of_summableAt {U : Set ℕ} (h0 : 0 ∉ U) {η : ℝ}
    (h : SummableAt U η) : Summable fun p : ℕ => U.indicator (fun n => (n : ℝ) ^ (-η)) p := by
  classical
  refine (show Summable (gdTwistTerm (wt U) freq η 0) from h).congr fun p => ?_
  rw [gdTwistTerm_wt]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [wt_of_notMem h0, zero_mul, Set.indicator_of_notMem h0]
  · rw [exp_neg_mul_freq hp]
    by_cases hpU : p ∈ U
    · rw [wt_of_mem hpU, one_mul, Set.indicator_of_mem hpU]
    · rw [wt_of_notMem hpU, zero_mul, Set.indicator_of_notMem hpU]

/-- **Count balance.**  `κ₊ ≤ max(β, κ₋)`: doubled primes beyond the count exponent are matched
by deleted primes. -/
theorem expo_plus_le_max {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    expo (plusSet e) ≤ max β (expo (minusSet e)) := by
  by_contra hlt
  have hlt' : max β (expo (minusSet e)) < expo (plusSet e) := not_le.mp hlt
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (max β (expo (minusSet e)) + expo (plusSet e)) / 2 := ⟨_, rfl⟩
  have hη1 : max β (expo (minusSet e)) < η := by rw [hη]; linarith
  have hη2 : η < expo (plusSet e) := by rw [hη]; linarith
  have hβη : β < η := lt_of_le_of_lt (le_max_left _ _) hη1
  have hκη : expo (minusSet e) < η := lt_of_le_of_lt (le_max_right _ _) hη1
  have hη0 : 0 < η := lt_of_le_of_lt hβ hβη
  have hη1' : η < 1 := lt_of_lt_of_le hη2 (expo_le_one _)
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have h0 : (0 : ℕ) ∉ minusSet e := fun h => by
    have h1 : e 0 = -1 := h
    rw [he.prime 0 Nat.not_prime_zero] at h1
    omega
  -- the deleted primes are summable at `η`, so they can be put back at the rate `η`
  have hS := summable_indicator_of_summableAt h0 (summableAt_of_expo_lt hκη)
  have hNη : ∀ y : ℝ, 1 ≤ y → |((editSystem e).countBall y : ℝ) - A * y| ≤ C * y ^ η :=
    fun y hy => (hN y hy).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy hβη.le) hC)
  have hZ := summable_intNorm_kept_compl hη0 hS
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z₁ : ℝ, Z₁ = ∑' v : (keptPrimeSystem (minusSet e)ᶜ).Integer,
      ((keptPrimeSystem (minusSet e)ᶜ).intNorm v) ^ (-(1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = ∑' v : (keptPrimeSystem (minusSet e)ᶜ).Integer,
      ((keptPrimeSystem (minusSet e)ᶜ).intNorm v) ^ (-η) := ⟨_, rfl⟩
  have hZ₁0 : 0 ≤ Z₁ := by
    rw [hZ₁]
    exact tsum_nonneg fun v =>
      Real.rpow_nonneg ((keptPrimeSystem (minusSet e)ᶜ).intNorm_pos v).le _
  have hZ0 : 0 ≤ Z := by
    rw [hZdef]
    exact tsum_nonneg fun v =>
      Real.rpow_nonneg ((keptPrimeSystem (minusSet e)ᶜ).intNorm_pos v).le _
  have hcount : ∀ x : ℝ, 1 ≤ x →
      |((sumSystem (sumSystem (keptPrimeSystem (minusSet e)) (keptPrimeSystem (plusSet e)ᶜ))
        (keptPrimeSystem (minusSet e)ᶜ)).countBall x : ℝ) - A * Z₁ * x| ≤
        (C + A) * Z * x ^ η := by
    intro x hx
    rw [hZ₁, hZdef]
    exact sumSystem_count_sub_le (isDiscrete_editSystem e) (isDiscrete_keptPrimeSystem _) hA hC
      hη1'.le hNη hZ hx
  -- Chebyshev for the restored system
  have hexp : expo (plusSet e) ≤ η := by
    refine expo_le_of_dyadic (c₁ := 3 * ((C + A) * Z)) (c₂ := A * Z₁)
      (fun k hk => (prime_of_mem_plusSet he hk).two_le)
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hZ0)) (mul_nonneg hA hZ₁0) hη0.le
      fun x hx => ?_
    exact (card_plus_Ioc_le_sum he x).trans
      (sum_Ioc_half_le_of_count _ (isDiscrete_sumSystem (isDiscrete_sumSystem
        (isDiscrete_keptPrimeSystem _) (isDiscrete_keptPrimeSystem _))
        (isDiscrete_keptPrimeSystem _)) (fun d => freeFn_nonneg _ d)
        (fun n _ => intCount_restored (minusSet e) (plusSet e) n) (mul_nonneg hA hZ₁0) hη0.le
        hcount hx)
  linarith

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountFloor
