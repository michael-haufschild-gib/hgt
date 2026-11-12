import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheCountSeesTheDeletedPrimes
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheNormCountOfAnEditIsAConvolution
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheBalanceLawOfTwoSidedEdits

/-!
# A fake zero of a thin edit is paid in the count

An edit is *thin at `θ`* if `Σ_p |e(p)| p^{−θ} < ∞` for some `θ < 1`.  Let the system of the edit
have the count `N(x) = A x + O(x^β)`.

* **Primes that divide no norm** (`card_normless_le`).  For every integer-norm system with count
  `A x + O(x^β)` whose twin coefficients (the coefficients of `ζ_B / ζ`) have mass `O(y^θ)`,
  `θ < 1`, at most `c Q^{4β/(1−θ)}` primes up to `Q` divide no norm.
* **The count sees the deleted primes** (`card_deleted_le`).  For the system with the primes of
  `S` deleted and the primes of `T` doubled, both thin at `θ`: at most `c Q^{4β/(1−θ)}` primes of
  `S ∖ T` lie below `Q`.  The norm count is `1 * u` with twin coefficients of mass `O(y^θ)`, and
  the deleted primes divide no norm, so the large sieve over the deleted primes applies.
* **Exponent of the deleted primes** (`expo_minus_le`).  `κ₋ ≤ 4β/(1−θ)`.
* **A fake zero is paid in the count** (`mul_re_le_of_fake_zero`, `one_sub_expo_mul_re_le`).
  If `(s − 1) ζ_B(s)` continues to `Re s > 1/2` with a zero `ρ`, `Re ρ > 1/2`, `ζ(ρ) ≠ 0`, then
  `(1 − θ) Re ρ ≤ 4β`; with the exponent of the deleted primes, `(1 − κ₋) Re ρ ≤ 4β`.  By the
  balance law the zero lies below `κ₋`, and `κ₋` is bounded by the count.
* **A thin edit pays a power** (`lt_of_isIntegerNormFakeAt`).  An integer-norm fake that is an
  edit thin at `θ` has `β > (1 − θ)/8`: its count remainder is not below every power.

For the greedy edit at `ρ` the count remainder exponents `β` satisfy `Re ρ (1 − Re ρ) ≤ 4β`
(`greedy_count_floor`), and every `β > Re ρ` is realized.
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

/-- **The count sees the primes that divide no norm.**  For an integer-norm system with count
`A x + O(x^β)` whose twin coefficients have mass `O(y^θ)`, `θ < 1`, at most `c Q^{4β/(1−θ)}`
primes up to `Q` divide no norm. -/
theorem card_normless_le {B : BeurlingSystem} (h : HasIntegerNorms B) (hd : B.IsDiscrete)
    {A C K β θ : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hβθ : β + (1 - θ) / 2 < 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hU : ∀ y : ℕ, 1 ≤ y → ∑ d ∈ Ioc 0 y, |twinFn B h d| ≤ K * (y : ℝ) ^ θ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : ℕ) (D : Finset ℕ), 2 ≤ Q →
      (∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ ∀ g : B.Integer, ¬ p ∣ natIntNorm h g) →
      (D.card : ℝ) ≤ c * (Q : ℝ) ^ (4 * β / (1 - θ)) := by
  have hC : 0 ≤ C := by
    have h1 := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h1
  have hcount : ∀ x : ℕ, 1 ≤ x →
      |CountSieve.cnt (fun n => normFn B h n) x - A * x| ≤ C * (x : ℝ) ^ β := by
    intro x hx
    have h1 := hN (x : ℝ) (by exact_mod_cast hx)
    rw [← sum_intCount_eq_countBall h hd] at h1
    exact h1
  obtain ⟨c, hc0, hc⟩ := CountSieve.card_le_rpow (a := fun n => normFn B h n)
    (u := fun d => twinFn B h d) (fun n _ => normFn_eq_sum_divisors B h n)
    (fun n => Nat.cast_nonneg _) hA hC hK hβ hθ hθ1 hβθ hcount hU
  refine ⟨c, hc0, fun Q D hQ hD => hc Q D hQ fun p hp => ?_⟩
  obtain ⟨hpp, hpQ, hdiv⟩ := hD p hp
  refine ⟨hpp, hpQ, fun n _ hpn => ?_⟩
  have hempty : {g : B.Integer | natIntNorm h g = n} = ∅ :=
    Set.eq_empty_of_forall_notMem fun g hg => hdiv g (by
      rw [show natIntNorm h g = n from hg]
      exact hpn)
  show ((SumProductArithmeticOfTheLogarithm.intCount B h n : ℕ) : ℝ) = 0
  rw [SumProductArithmeticOfTheLogarithm.intCount, hempty, Set.ncard_empty, Nat.cast_zero]

/-! ## The deleted primes of a sum of kept-prime systems -/

/-- **The count sees the deleted primes of an edit.** -/
theorem card_deleted_le {S T : Set ℕ} {A C β θ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβθ : β + (1 - θ) / 2 < 1)
    (hS : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-θ)) p)
    (hT : Summable fun p : ℕ => T.indicator (fun n => (n : ℝ) ^ (-θ)) p)
    (hN : ∀ x : ℝ, 1 ≤ x →
      |((sumSystem (keptPrimeSystem S) (keptPrimeSystem Tᶜ)).countBall x : ℝ) - A * x| ≤
        C * x ^ β) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Q : ℕ) (D : Finset ℕ), 2 ≤ Q →
      (∀ p ∈ D, p.Prime ∧ p ≤ Q ∧ p ∈ S ∧ p ∉ T) →
      (D.card : ℝ) ≤ c * (Q : ℝ) ^ (4 * β / (1 - θ)) := by
  have hC : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hN 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at h
  have hZ : ∀ U : Set ℕ, 0 ≤ ∑' j : ℕ, sFreeR Uᶜ j * (j : ℝ) ^ (-θ) := fun U =>
    tsum_nonneg fun j => mul_nonneg (sFreeR_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hcount : ∀ x : ℕ, 1 ≤ x →
      |CountSieve.cnt (fun n => (freeFn S * freeFn Tᶜ) n) x - A * x| ≤ C * (x : ℝ) ^ β := by
    intro x hx
    have h := hN (x : ℝ) (by exact_mod_cast hx)
    rw [← sum_normCount_eq_countBall] at h
    exact h
  obtain ⟨c, hc0, hc⟩ := CountSieve.card_le_rpow (a := fun n => (freeFn S * freeFn Tᶜ) n)
    (u := fun d => (mobFn S * freeFn Tᶜ) d)
    (fun n _ => normCount_eq_sum_divisors S T n) (normCount_nonneg S T) hA hC
    (mul_nonneg (hZ S) (hZ T)) hβ hθ.le hθ1 hβθ hcount
    (fun y _ => sum_abs_twinCoeff_le hθ hS hT y)
  refine ⟨c, hc0, fun Q D hQ hD => hc Q D hQ fun p hp => ?_⟩
  obtain ⟨hpp, hpQ, hpS, hpT⟩ := hD p hp
  exact ⟨hpp, hpQ, fun n _ hpn => normCount_eq_zero hpp hpS hpT hpn⟩

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

/-- The deleted primes of an edit thin at `θ` are summable right of `4β/(1−θ)`. -/
theorem summableAt_minus {e : ℕ → ℤ} (he : IsEdit e) {A C β θ σ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβθ : β + (1 - θ) / 2 < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hσ : 4 * β / (1 - θ) < σ) : SummableAt (minusSet e) σ := by
  classical
  obtain ⟨hSm, hSp⟩ := summable_indicator_of_edit hSum
  obtain ⟨c, hc0, hc⟩ := card_deleted_le hA hβ hθ hθ1 hβθ hSm hSp hN
  have h1θ : 0 < 1 - θ := by linarith
  have hη0 : 0 ≤ 4 * β / (1 - θ) := div_nonneg (by linarith) h1θ.le
  have hw0 : wt (minusSet e) 0 = 0 := wt_of_notMem fun h => by
    have h1 : e 0 = -1 := h
    rw [he.prime 0 Nat.not_prime_zero] at h1
    omega
  -- the deleted primes below `n`
  have hpart : ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Ioc 0 n, wt (minusSet e) k ≤ c * (n : ℝ) ^ (4 * β / (1 - θ)) := by
    intro n hn
    have hcard : ∑ k ∈ Ioc 0 n, wt (minusSet e) k =
        (((Ioc 0 n).filter (fun k => k ∈ minusSet e)).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold wt
      rw [Set.indicator_apply]
      split_ifs <;> simp
    rw [hcard]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hempty : (Ioc 0 n).filter (fun k => k ∈ minusSet e) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk hmem
        have hk1 : k = 1 := by
          have := mem_Ioc.mp hk
          omega
        have h1 : e k = -1 := hmem
        rw [he.prime k (by rw [hk1]; exact Nat.not_prime_one)] at h1
        omega
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · refine hc n _ h2 fun p hp => ?_
      obtain ⟨hpI, hpm⟩ := mem_filter.mp hp
      have h1 : e p = -1 := hpm
      refine ⟨?_, (mem_Ioc.mp hpI).2, hpm, fun hpl => ?_⟩
      · by_contra hnp
        rw [he.prime p hnp] at h1
        omega
      · have h2' : e p = 1 := hpl
        omega
  have hsum := summable_mul_rpow_of_sum_le (wt_nonneg (minusSet e)) hw0 hη0 hc0 hpart hσ
  show Summable (gdTwistTerm (wt (minusSet e)) freq σ 0)
  refine hsum.congr fun k => ?_
  rw [gdTwistTerm_wt]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hw0, zero_mul, zero_mul]
  · rw [exp_neg_mul_freq hk]

/-- **The exponent of the deleted primes** is at most `4β/(1−θ)`. -/
theorem expo_minus_le {e : ℕ → ℤ} (he : IsEdit e) {A C β θ : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hβθ : β + (1 - θ) / 2 < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    expo (minusSet e) ≤ 4 * β / (1 - θ) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hη0 : 0 ≤ 4 * β / (1 - θ) := div_nonneg (by linarith) h1θ.le
  by_contra hlt
  have hlt' : 4 * β / (1 - θ) < expo (minusSet e) := not_le.mp hlt
  have h := expo_le_of_summableAt (T := minusSet e)
    (σ := (4 * β / (1 - θ) + expo (minusSet e)) / 2) (by linarith)
    (summableAt_minus he hA hβ hθ hθ1 hβθ hSum hN (by linarith))
  linarith

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

/-- **A fake zero of a thin edit is paid in the count**: `(1 − θ) Re ρ ≤ 4β`. -/
theorem mul_re_le_of_fake_zero (he : IsEdit e) {θ : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) :
    (1 - θ) * ρ.re ≤ 4 * β := by
  have h1θ : 0 < 1 - θ := by linarith
  have hρm := (re_le_expo_minus he hG hGeq hρ hρ1 hzero hζ).1
  rcases lt_or_ge (β + (1 - θ) / 2) 1 with hβθ | hβθ
  · have hA' : 0 < A :=
      density_pos hA (by linarith) hθ hθ1 (summable_indicator_of_edit hSum).1 hN
    have h := hρm.trans (expo_minus_le he hA' hβ hθ hθ1 hβθ hSum hN)
    rw [le_div_iff₀ h1θ] at h
    linarith
  · have h1 : ρ.re ≤ 1 := hρm.trans (expo_le_one _)
    nlinarith [mul_nonneg h1θ.le (sub_nonneg.mpr h1)]

/-- **The exponent law of a fake zero**: `(1 − κ₋) Re ρ ≤ 4β`, `κ₋` the exponent of the deleted
primes. -/
theorem one_sub_expo_mul_re_le (he : IsEdit e) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hκ : expo (minusSet e) < 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hzero : G ρ = 0) (hζ : riemannZeta ρ ≠ 0) :
    (1 - expo (minusSet e)) * ρ.re ≤ 4 * β := by
  obtain ⟨hρm, hpm⟩ := re_le_expo_minus he hG hGeq hρ hρ1 hzero hζ
  have hstep : ∀ θ : ℝ, expo (minusSet e) < θ → θ < 1 → (1 - θ) * ρ.re ≤ 4 * β := by
    intro θ hθ hθ1
    have hθ0 : 0 < θ := lt_of_le_of_lt (expo_nonneg _) hθ
    exact mul_re_le_of_fake_zero he hA hβ hθ0 hθ1
      (summable_abs_edit_of_summableAt he (summableAt_of_expo_lt (lt_of_le_of_lt hpm hθ))
        (summableAt_of_expo_lt hθ)) hN hG hGeq hρ hρ1 hzero hζ
  by_contra hcon
  have hd : 0 < (1 - expo (minusSet e)) * ρ.re - 4 * β := by linarith [not_le.mp hcon]
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ,
      m = min ((1 - expo (minusSet e)) * ρ.re - 4 * β) (1 - expo (minusSet e)) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm_def]
    exact lt_min hd (by linarith)
  have hm1 : m ≤ (1 - expo (minusSet e)) * ρ.re - 4 * β := by
    rw [hm_def]
    exact min_le_left _ _
  have hm2 : m ≤ 1 - expo (minusSet e) := by
    rw [hm_def]
    exact min_le_right _ _
  have h := hstep (expo (minusSet e) + m / 2) (by linarith) (by linarith)
  have hρ1' : ρ.re ≤ 1 := hρm.trans (expo_le_one _)
  have h3 := mul_le_mul_of_nonneg_left hρ1' hm0.le
  nlinarith

end FakeZero

/-- **The count floor of the greedy pair twin.**  Every count remainder exponent of the greedy
edit at a non-real `ρ` with `ζ(ρ) ≠ 0` satisfies `Re ρ (1 − Re ρ) ≤ 4β`. -/
theorem greedy_count_floor {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15) (him : ρ.im ≠ 0)
    (hζ : riemannZeta ρ ≠ 0) {A C β : ℝ} (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x →
      |((editSystem (edit ρ)).countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    ρ.re * (1 - ρ.re) ≤ 4 * β := by
  have he := isEdit_edit ρ
  obtain ⟨C₀, H, -, hdiff, hfac⟩ := (isPairTwin_editSystem hρ hρ1).exists_continuation
  have hρne : ρ ≠ 1 := fun h => by
    rw [h] at hρ1
    norm_num at hρ1
  have hexp := (expo_edit_eq hρ hρ1 him hζ).2
  have h := one_sub_expo_mul_re_le (G := fun s => zetaResidueUnit s *
    (C₀ * (s - ρ) * (s - (starRingEnd ℂ) ρ) * cexp (H s))) he hA hβ
    (by rw [hexp]; linarith) hN hdiff (fun s hs => (hfac s hs).symm) hρ hρne (by simp) hζ
  rw [hexp] at h
  linarith

/-- **A thin edit pays a power.**  An integer-norm fake that is an edit thin at `θ < 1` has a
count remainder exponent `β > (1 − θ)/8`. -/
theorem lt_of_isIntegerNormFakeAt {e : ℕ → ℤ} (he : IsEdit e) {β θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hSum : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-θ))
    (hfake : IsIntegerNormFakeAt (editSystem e) β) : (1 - θ) / 8 < β := by
  have hβ : 0 ≤ β := nonneg_of_integerNormFakeAt hfake
  obtain ⟨-, -, -, ⟨A, C, hA, hN⟩, G, hG, hGeq, ρ, hρ, hρ1, hzero, hζ⟩ := hfake
  have h := mul_re_le_of_fake_zero he hA hβ hθ hθ1 hSum hN hG hGeq hρ hρ1 hzero hζ
  have h1θ : 0 < 1 - θ := by linarith
  nlinarith [mul_lt_mul_of_pos_left hρ h1θ]

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.CountFloor
