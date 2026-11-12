import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheCountSeesTheEditedPrimes
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheNormCountOfAnEditIsAConvolution
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheBalanceLawOfTwoSidedEdits

/-!
# Thin edits pay a power in the count

An edit is *thin at `θ`* if `Σ_p |e(p)| p^{−θ} < ∞` for some `θ < 1`.  Let the system of the edit
have the count `N(x) = A x + O(x^β)`, and let `κ₊`, `κ₋` be the exponents of the doubled and of
the deleted primes.

* **Primes that divide no norm** (`card_normless_le`).  For every integer-norm system with count
  `A x + O(x^β)` whose twin coefficients `u` (the coefficients of `ζ_B / ζ`) satisfy
  `Σ |u(d)| d^{−θ} < ∞`, `θ < 1`, at most `c Q^{2β(2−θ)/(1−θ)}` primes up to `Q` divide no norm.
* **The count sees the edited primes** (`card_edited_le`).  For the system with the primes of `S`
  deleted and the primes of `T` doubled, both thin at `θ`: at most `c Q^{2β(2−θ)/(1−θ)}` primes
  of the symmetric difference of `S` and `T` lie below `Q`.  A deleted prime divides no norm, a
  doubled prime leaves `u` invariant, and the large sieve over the seen primes applies.
* **The exponents are bounded by the count** (`expo_le_of_count`, `expo_mul_one_sub_le`).
  `κ₊, κ₋ ≤ 2β(2−θ)/(1−θ)`, and `κ (1 − κ) ≤ 2β (2 − κ)` for `κ = max(κ₊, κ₋) < 1`.
* **Exponent zero** (`expo_eq_zero_iff`).  A thin edit has a count remainder below every power
  if and only if `κ₊ = κ₋ = 0`.
* **A fake zero is paid in the count** (`mul_re_le_of_fake_zero`, `one_sub_expo_mul_re_le`).
  If `(s − 1) ζ_B(s)` continues to `Re s > 1/2` with a zero `ρ`, `Re ρ > 1/2`, `ζ(ρ) ≠ 0`, then
  `(1 − θ) Re ρ ≤ 2β (2 − θ)` and `(1 − κ₋) Re ρ ≤ 2β (2 − κ₋)`: the zero lies below the
  exponents, and the exponents are bounded by the count.
* **A thin edit pays a power** (`lt_of_isIntegerNormFakeAt`).  An integer-norm fake that is an
  edit thin at `θ` has `β > (1 − θ) / (4 (2 − θ))`.

For the greedy edit at `ρ` the count remainder exponents `β` satisfy
`Re ρ (1 − Re ρ) ≤ 2β (2 − Re ρ)` (`greedy_count_floor`), and every `β > Re ρ` is realized.
-/

open Complex Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountFloor

open ThinAdditions TwoSidedEdits NormCount BalanceLaw PrimeEdits

/-! ## Primes that divide no norm -/

/-- The norm multiplicities of an integer-norm system, as an arithmetic function. -/
def normFn (B : BeurlingSystem) (h : HasIntegerNorms B) : ArithmeticFunction ℝ :=
  ⟨fun n => (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ), by
    rw [intCount_zero, Nat.cast_zero]⟩

/-- The twin coefficients of an integer-norm system: the Dirichlet coefficients of `ζ_B / ζ`. -/
def twinFn (B : BeurlingSystem) (h : HasIntegerNorms B) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * normFn B h

theorem normFn_eq_sum_divisors (B : BeurlingSystem) (h : HasIntegerNorms B) (n : ℕ) :
    normFn B h n = ∑ d ∈ n.divisors, twinFn B h d := by
  have h1 := ArithmeticFunction.coe_zeta_mul_apply (f := twinFn B h) (x := n)
  rw [← h1, twinFn, ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

/-- **The count sees the primes that divide no norm.** -/
theorem card_normless_le {B : BeurlingSystem} (h : HasIntegerNorms B) (hd : B.IsDiscrete)
    {A C Z β θ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hβθ : β + (1 - θ) / (2 - θ) < 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hZ : ∀ y : ℕ, ∑ d ∈ Ioc 0 y, |twinFn B h d| * (d : ℝ) ^ (-θ) ≤ Z) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : ℕ) (D : Finset ℕ), 2 ≤ Q →
      (∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ ∀ g : B.Integer, ¬ p ∣ natIntNorm h g) →
      (D.card : ℝ) ≤ c * (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ)) := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have hau : ∀ n, 1 ≤ n → (fun n => normFn B h n) n =
      ∑ d ∈ n.divisors, (fun d => twinFn B h d) d := fun n _ => normFn_eq_sum_divisors B h n
  have hcount : ∀ x : ℕ, 1 ≤ x →
      |CountSieve.cnt (fun n => normFn B h n) x - A * x| ≤ C * (x : ℝ) ^ β := by
    intro x hx
    have h1 := hN (x : ℝ) (by exact_mod_cast hx)
    rw [← sum_intCount_eq_countBall h hd] at h1
    exact h1
  obtain ⟨c, hc0, hc⟩ := CountSieve.card_le_rpow hau hA hC hβ hθ hθ1 hβθ hcount hZ
  refine ⟨c, hc0, fun Q D hQ hD => hc Q D hQ fun p hp => ?_⟩
  obtain ⟨hpp, hpQ, hdiv⟩ := hD p hp
  refine ⟨hpp, hpQ, CountSieve.isSeen_of_deleted hau
    (fun n => (Nat.cast_nonneg _ : (0 : ℝ) ≤ (SumProductArithmeticOfTheLogarithm.intCount B h n : ℝ)))
    hpp fun n _ hpn => ?_⟩
  have hempty : {g : B.Integer | natIntNorm h g = n} = ∅ :=
    Set.eq_empty_of_forall_notMem fun g hg => hdiv g (by
      rw [show natIntNorm h g = n from hg]
      exact hpn)
  show ((SumProductArithmeticOfTheLogarithm.intCount B h n : ℕ) : ℝ) = 0
  rw [SumProductArithmeticOfTheLogarithm.intCount, hempty, Set.ncard_empty, Nat.cast_zero]

/-! ## The edited primes of a sum of kept-prime systems -/

/-- **The count sees the edited primes.** -/
theorem card_edited_le {S T : Set ℕ} {A C β θ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβθ : β + (1 - θ) / (2 - θ) < 1)
    (hS : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-θ)) p)
    (hT : Summable fun p : ℕ => T.indicator (fun n => (n : ℝ) ^ (-θ)) p)
    (hN : ∀ x : ℝ, 1 ≤ x →
      |((sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ)).countBall x : ℝ) - A * x| ≤
        C * x ^ β) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : ℕ) (D : Finset ℕ), 2 ≤ Q →
      (∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ ((p ∈ S ∧ p ∉ T) ∨ (p ∈ T ∧ p ∉ S))) →
      (D.card : ℝ) ≤ c * (Q : ℝ) ^ (2 * β * (2 - θ) / (1 - θ)) := by
  have hC : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h
  have hau : ∀ n, 1 ≤ n → (fun n => (freeFn S * freeFn Tᶜ) n) n =
      ∑ d ∈ n.divisors, (fun d => (mobFn S * freeFn Tᶜ) d) d :=
    fun n _ => normCount_eq_sum_divisors S T n
  have hcount : ∀ x : ℕ, 1 ≤ x →
      |CountSieve.cnt (fun n => (freeFn S * freeFn Tᶜ) n) x - A * x| ≤ C * (x : ℝ) ^ β := by
    intro x hx
    have h := hN (x : ℝ) (by exact_mod_cast hx)
    rw [← sum_normCount_eq_countBall] at h
    exact h
  obtain ⟨c, hc0, hc⟩ := CountSieve.card_le_rpow hau hA hC hβ hθ.le hθ1 hβθ hcount
    (fun y => sum_abs_twinCoeff_mul_rpow_le hθ hS hT y)
  refine ⟨c, hc0, fun Q D hQ hD => hc Q D hQ fun p hp => ?_⟩
  obtain ⟨hpp, hpQ, hedit⟩ := hD p hp
  refine ⟨hpp, hpQ, ?_⟩
  rcases hedit with ⟨hpS, hpT⟩ | ⟨hpT, hpS⟩
  · exact CountSieve.isSeen_of_deleted hau (normCount_nonneg S T) hpp
      fun n _ hpn => normCount_eq_zero hpp hpS hpT hpn
  · exact CountSieve.isSeen_of_mul_invariant hau hpp
      fun d hd => twinCoeff_prime_mul hpp hpS hpT hd

/-! ## Edits -/

theorem wt_of_mem {T : Set ℕ} {k : ℕ} (h : k ∈ T) : wt T k = 1 := by
  unfold wt
  rw [Set.indicator_of_mem h]

theorem wt_of_notMem {T : Set ℕ} {k : ℕ} (h : k ∉ T) : wt T k = 0 := by
  unfold wt
  rw [Set.indicator_of_notMem h]

/-- An edit thin at `θ` has both sets of edited primes summable at `θ`. -/
theorem summable_indicator_of_edit {e : ℕ → ℤ} {θ : ℝ}
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ)) :
    (Summable fun p : ℕ => (minusSet e).indicator (fun n => (n : ℝ) ^ (-θ)) p) ∧
      Summable fun p : ℕ => (plusSet e).indicator (fun n => (n : ℝ) ^ (-θ)) p := by
  have hpow : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ (-θ) := fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _
  constructor
  · refine Summable.of_nonneg_of_le (fun p => Set.indicator_nonneg (fun n _ => hpow n) p)
      (fun p => ?_) hS
    by_cases h : p ∈ minusSet e
    · have h' : e p = -1 := h
      rw [Set.indicator_of_mem h, h']
      simp
    · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (abs_nonneg _) (hpow p)
  · refine Summable.of_nonneg_of_le (fun p => Set.indicator_nonneg (fun n _ => hpow n) p)
      (fun p => ?_) hS
    by_cases h : p ∈ plusSet e
    · have h' : e p = 1 := h
      rw [Set.indicator_of_mem h, h']
      simp
    · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (abs_nonneg _) (hpow p)

/-- Both sets of edited primes summable at `θ` make the edit thin at `θ`. -/
theorem summable_abs_edit_of_summableAt {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ}
    (hp : SummableAt (plusSet e) θ) (hm : SummableAt (minusSet e) θ) :
    Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ) := by
  refine ((show Summable (gdTwistTerm (wt (plusSet e)) freq θ 0) from hp).add
    (show Summable (gdTwistTerm (wt (minusSet e)) freq θ 0) from hm)).congr fun k => ?_
  rw [gdTwistTerm_wt, gdTwistTerm_wt]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : e 0 = 0 := he.prime 0 Nat.not_prime_zero
    have hp0 : wt (plusSet e) 0 = 0 := wt_of_notMem fun h => by
      have h1 : e 0 = 1 := h
      omega
    have hm0 : wt (minusSet e) 0 = 0 := wt_of_notMem fun h => by
      have h1 : e 0 = -1 := h
      omega
    rw [hp0, hm0, h0]
    simp
  · rw [exp_neg_mul_freq hk]
    rcases he.range k with h | h | h
    · have hm1 : wt (minusSet e) k = 0 := wt_of_notMem fun hc => by
        have h1 : e k = -1 := hc
        omega
      rw [wt_of_mem (show k ∈ plusSet e from h), hm1, h]
      simp
    · have hp1 : wt (plusSet e) k = 0 := wt_of_notMem fun hc => by
        have h1 : e k = 1 := hc
        omega
      rw [hp1, wt_of_mem (show k ∈ minusSet e from h), h]
      simp
    · have hp1 : wt (plusSet e) k = 0 := wt_of_notMem fun hc => by
        have h1 : e k = 1 := hc
        omega
      have hm1 : wt (minusSet e) k = 0 := wt_of_notMem fun hc => by
        have h1 : e k = -1 := hc
        omega
      rw [hp1, hm1, h]
      simp

/-- A set of integers above `1` whose elements below `Q` number `O(Q^η)` is summable right of
`η`. -/
theorem summableAt_of_card_le {U : Set ℕ} {c η σ : ℝ} (hc0 : 0 ≤ c) (hη0 : 0 ≤ η)
    (hU : ∀ k ∈ U, 2 ≤ k)
    (hcard : ∀ (Q : ℕ) (D : Finset ℕ), 2 ≤ Q → (∀ p ∈ D, p ≤ Q ∧ p ∈ U) →
      (D.card : ℝ) ≤ c * (Q : ℝ) ^ η) (hσ : η < σ) : SummableAt U σ := by
  classical
  have hw0 : wt U 0 = 0 := wt_of_notMem fun h => by
    have := hU 0 h
    omega
  have hpart : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ Ioc 0 n, wt U k ≤ c * (n : ℝ) ^ η := by
    intro n hn
    have hcardeq : ∑ k ∈ Ioc 0 n, wt U k = (((Ioc 0 n).filter (fun k => k ∈ U)).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold wt
      rw [Set.indicator_apply]
      split_ifs <;> simp
    rw [hcardeq]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hempty : (Ioc 0 n).filter (fun k => k ∈ U) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk hmem
        have h1 := (mem_Ioc.mp hk).2
        have h3 := hU k hmem
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact hcard n _ h2 fun p hp =>
        ⟨(mem_Ioc.mp (mem_filter.mp hp).1).2, (mem_filter.mp hp).2⟩
  have hsum := summable_mul_rpow_of_sum_le (wt_nonneg U) hw0 hη0 hc0 hpart hσ
  show Summable (gdTwistTerm (wt U) freq σ 0)
  refine hsum.congr fun k => ?_
  rw [gdTwistTerm_wt]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hw0, zero_mul, zero_mul]
  · rw [exp_neg_mul_freq hk]

theorem prime_of_mem_minusSet {e : ℕ → ℤ} (he : IsEdit e) {k : ℕ} (hk : k ∈ minusSet e) :
    k.Prime := by
  by_contra hnp
  have h1 : e k = -1 := hk
  rw [he.prime k hnp] at h1
  omega

theorem prime_of_mem_plusSet {e : ℕ → ℤ} (he : IsEdit e) {k : ℕ} (hk : k ∈ plusSet e) :
    k.Prime := by
  by_contra hnp
  have h1 : e k = 1 := hk
  rw [he.prime k hnp] at h1
  omega

/-- The edited primes of an edit thin at `θ` are summable right of `2β(2−θ)/(1−θ)`. -/
theorem summableAt_edited {e : ℕ → ℤ} (he : IsEdit e) {A C β θ σ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβθ : β + (1 - θ) / (2 - θ) < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hσ : 2 * β * (2 - θ) / (1 - θ) < σ) :
    SummableAt (minusSet e) σ ∧ SummableAt (plusSet e) σ := by
  obtain ⟨hSm, hSp⟩ := summable_indicator_of_edit hSum
  obtain ⟨c, hc0, hc⟩ := card_edited_le hA hβ hθ hθ1 hβθ hSm hSp hN
  have h1θ : 0 < 1 - θ := by linarith
  have hη0 : 0 ≤ 2 * β * (2 - θ) / (1 - θ) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) h1θ.le
  constructor
  · refine summableAt_of_card_le hc0 hη0
      (fun k hk => (prime_of_mem_minusSet he hk).two_le) (fun Q D hQ hD => ?_) hσ
    refine hc Q D hQ fun p hp => ?_
    obtain ⟨hpQ, hpm⟩ := hD p hp
    refine ⟨prime_of_mem_minusSet he hpm, hpQ, Or.inl ⟨hpm, fun hpl => ?_⟩⟩
    have h1 : e p = -1 := hpm
    have h2 : e p = 1 := hpl
    omega
  · refine summableAt_of_card_le hc0 hη0
      (fun k hk => (prime_of_mem_plusSet he hk).two_le) (fun Q D hQ hD => ?_) hσ
    refine hc Q D hQ fun p hp => ?_
    obtain ⟨hpQ, hpl⟩ := hD p hp
    refine ⟨prime_of_mem_plusSet he hpl, hpQ, Or.inr ⟨hpl, fun hpm => ?_⟩⟩
    have h1 : e p = 1 := hpl
    have h2 : e p = -1 := hpm
    omega

/-- **The exponents are bounded by the count**: `κ₋, κ₊ ≤ 2β(2−θ)/(1−θ)`. -/
theorem expo_le_of_count {e : ℕ → ℤ} (he : IsEdit e) {A C β θ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβθ : β + (1 - θ) / (2 - θ) < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    expo (minusSet e) ≤ 2 * β * (2 - θ) / (1 - θ) ∧
      expo (plusSet e) ≤ 2 * β * (2 - θ) / (1 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hη0 : 0 ≤ 2 * β * (2 - θ) / (1 - θ) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) h1θ.le
  have hkey : ∀ U : Set ℕ, (∀ σ, 2 * β * (2 - θ) / (1 - θ) < σ → SummableAt U σ) →
      expo U ≤ 2 * β * (2 - θ) / (1 - θ) := by
    intro U hU
    by_contra hlt
    have hlt' : 2 * β * (2 - θ) / (1 - θ) < expo U := not_le.mp hlt
    have h := expo_le_of_summableAt (T := U) (σ := (2 * β * (2 - θ) / (1 - θ) + expo U) / 2)
      (by linarith) (hU _ (by linarith))
    linarith
  exact ⟨hkey _ fun σ hσ => (summableAt_edited he hA hβ hθ hθ1 hβθ hSum hN hσ).1,
    hkey _ fun σ hσ => (summableAt_edited he hA hβ hθ hθ1 hβθ hSum hN hσ).2⟩

/-- The count rate of a thin edit bounds both exponents: `κ (1 − θ) ≤ 2β (2 − θ)`. -/
theorem expo_mul_le {e : ℕ → ℤ} (he : IsEdit e) {A C β θ : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    expo (minusSet e) * (1 - θ) ≤ 2 * β * (2 - θ) ∧
      expo (plusSet e) * (1 - θ) ≤ 2 * β * (2 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h2θ : 0 < 2 - θ := by linarith
  have hfrac : 0 < (1 - θ) / (2 - θ) := div_pos h1θ h2θ
  rcases lt_or_ge (β + (1 - θ) / (2 - θ)) 1 with hβθ | hβθ
  · have hA' : 0 < A :=
      density_pos hA (by linarith) hθ hθ1 (summable_indicator_of_edit hSum).1 hN
    obtain ⟨hm, hp⟩ := expo_le_of_count he hA' hβ hθ hθ1 hβθ hSum hN
    rw [le_div_iff₀ h1θ] at hm hp
    exact ⟨hm, hp⟩
  · -- `β (2 − θ) ≥ 1`, and both exponents are at most `1`
    have hcancel : (1 - θ) / (2 - θ) * (2 - θ) = 1 - θ := div_mul_cancel₀ _ h2θ.ne'
    have hβ2 : 1 ≤ β * (2 - θ) := by
      have h := mul_le_mul_of_nonneg_right hβθ h2θ.le
      rw [add_mul, hcancel] at h
      linarith
    have hle : ∀ U : Set ℕ, expo U * (1 - θ) ≤ 2 * β * (2 - θ) := fun U => by
      nlinarith [mul_nonneg h1θ.le (sub_nonneg.mpr (expo_le_one U))]
    exact ⟨hle _, hle _⟩

/-- **The exponent law of the count**: `κ (1 − κ) ≤ 2β (2 − κ)` for `κ = max(κ₊, κ₋) < 1`. -/
theorem expo_mul_one_sub_le {e : ℕ → ℤ} (he : IsEdit e) {A C β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hκ : max (expo (plusSet e)) (expo (minusSet e)) < 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    max (expo (plusSet e)) (expo (minusSet e)) *
        (1 - max (expo (plusSet e)) (expo (minusSet e))) ≤
      2 * β * (2 - max (expo (plusSet e)) (expo (minusSet e))) := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = max (expo (plusSet e)) (expo (minusSet e)) := ⟨_, rfl⟩
  rw [← hκdef] at hκ ⊢
  have hκp : expo (plusSet e) ≤ κ := by rw [hκdef]; exact le_max_left _ _
  have hκm : expo (minusSet e) ≤ κ := by rw [hκdef]; exact le_max_right _ _
  have hκ0 : 0 ≤ κ := (expo_nonneg _).trans hκp
  have hstep : ∀ θ : ℝ, κ < θ → θ < 1 → κ * (1 - θ) ≤ 2 * β * (2 - θ) := by
    intro θ hθ hθ1
    have hθ0 : 0 < θ := lt_of_le_of_lt hκ0 hθ
    obtain ⟨hm, hp⟩ := expo_mul_le he hA hβ hθ0 hθ1
      (summable_abs_edit_of_summableAt he (summableAt_of_expo_lt (lt_of_le_of_lt hκp hθ))
        (summableAt_of_expo_lt (lt_of_le_of_lt hκm hθ))) hN
    rcases le_max_iff.mp (le_of_eq hκdef) with h | h
    · exact (mul_le_mul_of_nonneg_right h (by linarith)).trans hp
    · exact (mul_le_mul_of_nonneg_right h (by linarith)).trans hm
  by_contra hcon
  have hd : 0 < κ * (1 - κ) - 2 * β * (2 - κ) := by linarith [not_le.mp hcon]
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = min (κ * (1 - κ) - 2 * β * (2 - κ)) (1 - κ) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm_def]
    exact lt_min hd (by linarith)
  have hm1 : m ≤ κ * (1 - κ) - 2 * β * (2 - κ) := by
    rw [hm_def]
    exact min_le_left _ _
  have hm2 : m ≤ 1 - κ := by
    rw [hm_def]
    exact min_le_right _ _
  have h := hstep (κ + m / 2) (by linarith) (by linarith)
  have h3 := mul_le_mul_of_nonneg_left hκ.le hm0.le
  have h4 := mul_nonneg hβ hm0.le
  nlinarith

/-- **Exponent zero.**  A thin edit has a count remainder below every power if and only if both
exponents vanish. -/
theorem expo_eq_zero_iff {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ)) :
    (∀ β : ℝ, 0 < β → β < 1 → ∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) ↔
      expo (plusSet e) = 0 ∧ expo (minusSet e) = 0 := by
  have h1θ : 0 < 1 - θ := by linarith
  constructor
  · intro hall
    have hzero : ∀ U : Set ℕ, (∀ β A C : ℝ, 0 < β → 0 ≤ A →
        (∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) →
        expo U * (1 - θ) ≤ 2 * β * (2 - θ)) → expo U = 0 := by
      intro U hU
      refine le_antisymm ?_ (expo_nonneg U)
      by_contra hpos
      have hpos' : 0 < expo U := not_le.mp hpos
      obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min (expo U * (1 - θ) / 8) (1 / 2) := ⟨_, rfl⟩
      have hβ0 : 0 < β := by
        rw [hβdef]
        exact lt_min (by positivity) (by norm_num)
      have hβ1 : β ≤ expo U * (1 - θ) / 8 := by
        rw [hβdef]
        exact min_le_left _ _
      have hβ2 : β ≤ 1 / 2 := by
        rw [hβdef]
        exact min_le_right _ _
      obtain ⟨A, C, hA, hN⟩ := hall β hβ0 (by linarith)
      have h := hU β A C hβ0 hA hN
      nlinarith [mul_pos hpos' h1θ, mul_pos hβ0 hθ]
    exact ⟨hzero _ fun β A C hβ hA hN => (expo_mul_le he hA hβ.le hθ hθ1 hSum hN).2,
      hzero _ fun β A C hβ hA hN => (expo_mul_le he hA hβ.le hθ hθ1 hSum hN).1⟩
  · rintro ⟨hp, hm⟩ β hβ0 hβ1
    exact editSystem_count hβ0 hβ1 (summable_abs_edit_of_summableAt he
      (summableAt_of_expo_lt (by rw [hp]; exact hβ0))
      (summableAt_of_expo_lt (by rw [hm]; exact hβ0)))

/-! ## Fake zeros -/

section FakeZero

variable {e : ℕ → ℤ} {G : ℂ → ℂ} {ρ : ℂ} {A C β : ℝ}

/-- A fake zero right of `1/2` lies below the exponent of the deleted primes, which dominates
the exponent of the doubled primes. -/
theorem re_le_expo_minus (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) :
    ρ.re ≤ expo (minusSet e) ∧ expo (plusSet e) ≤ expo (minusSet e) := by
  have hre := re_le_of_fake_zero he hG hGeq hρ1 hzero hζ
  have hplus := expo_plus_le he hG hGeq
  have hρm : ρ.re ≤ expo (minusSet e) := by
    rcases le_max_iff.mp hre with h | h
    · rcases le_max_iff.mp h with h' | h'
      · rcases le_max_iff.mp (h'.trans hplus) with h'' | h''
        · exact h''
        · linarith
      · exact h'
    · linarith
  refine ⟨hρm, ?_⟩
  rcases le_max_iff.mp hplus with h | h
  · exact h
  · linarith

/-- **A fake zero of a thin edit is paid in the count**: `(1 − θ) Re ρ ≤ 2β (2 − θ)`. -/
theorem mul_re_le_of_fake_zero (he : IsEdit e) {θ : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) :
    (1 - θ) * ρ.re ≤ 2 * β * (2 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hρm := (re_le_expo_minus he hG hGeq hρ hρ1 hzero hζ).1
  have h := (expo_mul_le he hA hβ hθ hθ1 hSum hN).1
  nlinarith [mul_le_mul_of_nonneg_right hρm h1θ.le]

/-- **The exponent law of a fake zero**: `(1 − κ₋) Re ρ ≤ 2β (2 − κ₋)`, `κ₋` the exponent of the
deleted primes. -/
theorem one_sub_expo_mul_re_le (he : IsEdit e) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hκ : expo (minusSet e) < 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) :
    (1 - expo (minusSet e)) * ρ.re ≤ 2 * β * (2 - expo (minusSet e)) := by
  obtain ⟨hρm, hpm⟩ := re_le_expo_minus he hG hGeq hρ hρ1 hzero hζ
  have hstep : ∀ θ : ℝ, expo (minusSet e) < θ → θ < 1 →
      (1 - θ) * ρ.re ≤ 2 * β * (2 - θ) := by
    intro θ hθ hθ1
    have hθ0 : 0 < θ := lt_of_le_of_lt (expo_nonneg _) hθ
    exact mul_re_le_of_fake_zero he hA hβ hθ0 hθ1
      (summable_abs_edit_of_summableAt he (summableAt_of_expo_lt (lt_of_le_of_lt hpm hθ))
        (summableAt_of_expo_lt hθ)) hN hG hGeq hρ hρ1 hzero hζ
  by_contra hcon
  have hd : 0 < (1 - expo (minusSet e)) * ρ.re - 2 * β * (2 - expo (minusSet e)) := by
    linarith [not_le.mp hcon]
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ,
      m = min ((1 - expo (minusSet e)) * ρ.re - 2 * β * (2 - expo (minusSet e)))
        (1 - expo (minusSet e)) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm_def]
    exact lt_min hd (by linarith)
  have hm1 : m ≤ (1 - expo (minusSet e)) * ρ.re - 2 * β * (2 - expo (minusSet e)) := by
    rw [hm_def]
    exact min_le_left _ _
  have hm2 : m ≤ 1 - expo (minusSet e) := by
    rw [hm_def]
    exact min_le_right _ _
  have h := hstep (expo (minusSet e) + m / 2) (by linarith) (by linarith)
  have hρ1' : ρ.re ≤ 1 := hρm.trans (expo_le_one _)
  have h3 := mul_le_mul_of_nonneg_left hρ1' hm0.le
  have h4 := mul_nonneg hβ hm0.le
  nlinarith

end FakeZero

/-- **The count floor of the greedy pair twin.**  Every count remainder exponent of the greedy
edit at a non-real `ρ` with `ζ(ρ) ≠ 0` satisfies `Re ρ (1 − Re ρ) ≤ 2β (2 − Re ρ)`. -/
theorem greedy_count_floor {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15) (him : ρ.im ≠ 0)
    (hζ : riemannZeta ρ ≠ 0) {A C β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x →
      |((editSystem (edit ρ)).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ρ.re * (1 - ρ.re) ≤ 2 * β * (2 - ρ.re) := by
  obtain ⟨hp, hm⟩ := expo_edit_eq hρ hρ1 him hζ
  have h := expo_mul_one_sub_le (isEdit_edit ρ) hA hβ (by rw [hp, hm, max_self]; linarith) hN
  rwa [hp, hm, max_self] at h

/-- **A thin edit pays a power.**  An integer-norm fake that is an edit thin at `θ < 1` has a
count remainder exponent `β > (1 − θ) / (4 (2 − θ))`. -/
theorem lt_of_isIntegerNormFakeAt {e : ℕ → ℤ} (he : IsEdit e) {β θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hfake : IsIntegerNormFakeAt (editSystem e) β) : (1 - θ) / (4 * (2 - θ)) < β := by
  have hβ : 0 ≤ β := nonneg_of_integerNormFakeAt hfake
  obtain ⟨-, -, -, ⟨A, C, hA, hN⟩, G, hG, hGeq, ρ, hρ, hρ1, hzero, hζ⟩ := hfake
  have h := mul_re_le_of_fake_zero he hA hβ hθ hθ1 hSum hN hG hGeq hρ hρ1 hzero hζ
  have h1θ : 0 < 1 - θ := by linarith
  have h2θ : 0 < 2 - θ := by linarith
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [mul_lt_mul_of_pos_left hρ h1θ]

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountFloor
