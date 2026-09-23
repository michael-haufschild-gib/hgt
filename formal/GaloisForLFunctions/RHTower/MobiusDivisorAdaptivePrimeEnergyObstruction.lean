import GaloisForLFunctions.RHTower.MobiusDivisorElevenChannelBounds

/-!
# Every prime order forces a final energy increase at cutoff seven

The last remaining prime partitions the original signed source into its divisible
and prime-free groups. Exact sum preservation identifies these as the final two
signed coefficients, independently of the order in which other primes were removed.
At cutoff seven both coefficients are negative for every possible last prime.
Their merger therefore increases energy. Nevertheless the final scalar energy
is strictly below the original arithmetic diagonal.

All bounds are analytic; no numerical experiment is a proof input. This rules
out adaptive monotone prime elimination, while the all-cutoff SD1 remains open.
-/

open Finset
noncomputable section
namespace RHTower

/-- Signed coefficient left at cofactor one when only prime `p` remains. -/
def mobiusDivisorLastPrimeFree (M p : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 M).filter (fun d => ¬p∣d), mobiusDivisorDilationChannel M d

/-- Signed coefficient left at cofactor `p` when only that prime remains. -/
def mobiusDivisorLastPrimeDivisible (M p : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 M).filter (fun d => p∣d), mobiusDivisorDilationChannel M d

/-- Exact energy immediately before the final prime-pair merger. -/
def mobiusDivisorLastPrimeEnergy (M p : ℕ) : ℝ :=
  mobiusDivisorLastPrimeFree M p ^ (2 : ℕ) + mobiusDivisorLastPrimeDivisible M p ^ (2 : ℕ)

/-- The final two signed groups retain the complete source sum. -/
theorem mobiusDivisorLastPrime_add_eq_total (M p : ℕ) :
    mobiusDivisorLastPrimeFree M p + mobiusDivisorLastPrimeDivisible M p =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
  simpa only [mobiusDivisorLastPrimeFree,mobiusDivisorLastPrimeDivisible,add_comm]
    using sum_filter_add_sum_filter_not (s := Icc 1 M) (p := fun d => p∣d)
      (f := fun d => mobiusDivisorDilationChannel M d)

/-- The final energy change is precisely the signed overlap of the two surviving groups. -/
theorem total_sq_sub_mobiusDivisorLastPrimeEnergy (M p : ℕ) :
    (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^(2 : ℕ) - mobiusDivisorLastPrimeEnergy M p =
      2*mobiusDivisorLastPrimeFree M p*mobiusDivisorLastPrimeDivisible M p := by
  rw [← mobiusDivisorLastPrime_add_eq_total M p,mobiusDivisorLastPrimeEnergy]
  ring

/-- Both final groups at seven have negative sign, for every possible last prime. -/
theorem mobiusDivisorLastPrime_seven_both_neg :
    ∀ p ∈ ({2,3,5} : Finset ℕ), mobiusDivisorLastPrimeFree 7 p < 0 ∧
      mobiusDivisorLastPrimeDivisible 7 p < 0 := by
  intro p hp
  obtain ⟨ha,hb,hc,he,hf⟩ := mobiusDivisorDilationChannel_seven_box
  obtain ⟨h4,h7⟩ := mobiusDivisorDilationChannel_seven_zero
  simp only [mem_insert,mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  all_goals norm_num [mobiusDivisorLastPrimeFree,mobiusDivisorLastPrimeDivisible,
    sum_filter,sum_Icc_succ_top,h4,h7]
  all_goals constructor <;> linarith

/-- Every possible terminal prime forces a strict energy increase at cutoff seven. -/
theorem mobiusDivisorLastPrimeEnergy_seven_lt_total_sq :
    ∀ p ∈ ({2,3,5} : Finset ℕ), mobiusDivisorLastPrimeEnergy 7 p <
      (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) := by
  intro p hp
  obtain ⟨hfree,hdiv⟩ := mobiusDivisorLastPrime_seven_both_neg p hp
  have hprod := mul_pos_of_neg_of_neg hfree hdiv
  have heq := total_sq_sub_mobiusDivisorLastPrimeEnergy 7 p
  linarith only [hprod,heq]

/-- No choice of final prime can complete a nonincreasing-energy elimination at seven. -/
theorem not_exists_contracting_lastPrime_seven :
    ¬∃ p : ℕ, p.Prime ∧ p<7 ∧
      (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) ≤ mobiusDivisorLastPrimeEnergy 7 p := by
  rintro ⟨p,hp,hp7,henergy⟩
  have hp2 := hp.two_le
  have hmem : p ∈ ({2,3,5} : Finset ℕ) := by
    interval_cases p <;> norm_num at *
  exact (not_le_of_gt (mobiusDivisorLastPrimeEnergy_seven_lt_total_sq p hmem)) henergy

/-- Strict global diagonal dominance survives every order's unavoidable terminal increase. -/
theorem mobiusDivisor_seven_strict_diagonal_margin :
    (1:ℝ)/125 < (∑ d ∈ Icc 1 7, (mobiusDivisorDilationChannel 7 d)^(2 : ℕ)) -
      (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) := by
  obtain ⟨ha,hb,hc,he,hf⟩ := mobiusDivisorDilationChannel_seven_box
  obtain ⟨h4,h7⟩ := mobiusDivisorDilationChannel_seven_zero
  let S : ℝ := ∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d
  have hS : -(193:ℝ)/1000 ≤ S ∧ S ≤ -(163:ℝ)/1000 := by
    dsimp [S]
    norm_num [sum_Icc_succ_top,h4,h7]
    constructor <;> linarith
  have hSsq : S^(2 : ℕ) ≤ (193:ℝ)^(2 : ℕ)/1000^(2 : ℕ) := by
    have h := mul_nonneg (show 0≤S+193/1000 by linarith)
      (show 0≤193/1000-S by linarith)
    nlinarith only [h]
  have hQ : (46325:ℝ)/1000000 ≤ ∑ d ∈ Icc 1 7, (mobiusDivisorDilationChannel 7 d)^(2 : ℕ) := by
    norm_num [sum_Icc_succ_top,h4,h7]
    nlinarith [sq_nonneg (mobiusDivisorDilationChannel 7 1-0.102),
      sq_nonneg (mobiusDivisorDilationChannel 7 2+0.139),
      sq_nonneg (mobiusDivisorDilationChannel 7 3+0.110),
      sq_nonneg (mobiusDivisorDilationChannel 7 5+0.060),
      sq_nonneg (mobiusDivisorDilationChannel 7 6-0.030)]
  change (1:ℝ)/125 < _-S^(2 : ℕ)
  linarith only [hSsq,hQ]
/-- Literal merger of the two signed coefficients on every prime-free cofactor. -/
def mobiusDivisorPrimeMerge (p : ℕ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  if p∣d then 0 else f d+f (p*d)

/-- Energy after two actual successive prime mergers, retaining the original source. -/
def mobiusDivisorTwoPrimeEnergy (M p q : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M,
    (mobiusDivisorPrimeMerge q (mobiusDivisorPrimeMerge p (mobiusDivisorDilationChannel M)) d)^(2 : ℕ)

private theorem channel_seven_large {d : ℕ} (hd : 7 ≤ d) :
    mobiusDivisorDilationChannel 7 d = 0 := by
  simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt (by omega : 6<d)]

private theorem twoPrimeEnergy_seven_table :
    mobiusDivisorTwoPrimeEnergy 7 2 3 = mobiusDivisorLastPrimeEnergy 7 5 ∧
    mobiusDivisorTwoPrimeEnergy 7 3 2 = mobiusDivisorLastPrimeEnergy 7 5 ∧
    mobiusDivisorTwoPrimeEnergy 7 2 5 = mobiusDivisorLastPrimeEnergy 7 3 ∧
    mobiusDivisorTwoPrimeEnergy 7 5 2 = mobiusDivisorLastPrimeEnergy 7 3 ∧
    mobiusDivisorTwoPrimeEnergy 7 3 5 = mobiusDivisorLastPrimeEnergy 7 2 ∧
    mobiusDivisorTwoPrimeEnergy 7 5 3 = mobiusDivisorLastPrimeEnergy 7 2 := by
  obtain ⟨h4,h7⟩ := mobiusDivisorDilationChannel_seven_zero
  norm_num [mobiusDivisorTwoPrimeEnergy,mobiusDivisorPrimeMerge,
    mobiusDivisorLastPrimeEnergy,mobiusDivisorLastPrimeFree,mobiusDivisorLastPrimeDivisible,
    sum_filter,sum_Icc_succ_top,h4,h7,channel_seven_large]
  all_goals ring_nf
  all_goals trivial

/-- Every ordered pair of distinct initial primes leaves less energy than the final source.
Thus all six complete prime orders must increase energy in their final step. -/
theorem mobiusDivisorTwoPrimeEnergy_seven_lt_total_sq :
    ∀ p ∈ ({2,3,5} : Finset ℕ), ∀ q ∈ ({2,3,5} : Finset ℕ), p≠q →
      mobiusDivisorTwoPrimeEnergy 7 p q <
        (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) := by
  intro p hp q hq hpq
  obtain ⟨h23,h32,h25,h52,h35,h53⟩ := twoPrimeEnergy_seven_table
  have h2 := mobiusDivisorLastPrimeEnergy_seven_lt_total_sq 2 (by simp)
  have h3 := mobiusDivisorLastPrimeEnergy_seven_lt_total_sq 3 (by simp)
  have h5 := mobiusDivisorLastPrimeEnergy_seven_lt_total_sq 5 (by simp)
  simp only [mem_insert,mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals simp_all only [ne_eq,not_true_eq_false]

/-- Energy after the literal third merger, without replacing the final source. -/
def mobiusDivisorThreePrimeEnergy (M p q r : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, (mobiusDivisorPrimeMerge r
    (mobiusDivisorPrimeMerge q (mobiusDivisorPrimeMerge p (mobiusDivisorDilationChannel M))) d)^(2 : ℕ)

private theorem threePrimeEnergy_seven_table :
    mobiusDivisorThreePrimeEnergy 7 2 3 5 = (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) ∧
    mobiusDivisorThreePrimeEnergy 7 2 5 3 = (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) ∧
    mobiusDivisorThreePrimeEnergy 7 3 2 5 = (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) ∧
    mobiusDivisorThreePrimeEnergy 7 3 5 2 = (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) ∧
    mobiusDivisorThreePrimeEnergy 7 5 2 3 = (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) ∧
    mobiusDivisorThreePrimeEnergy 7 5 3 2 = (∑ d ∈ Icc 1 7, mobiusDivisorDilationChannel 7 d)^(2 : ℕ) := by
  obtain ⟨h4,h7⟩ := mobiusDivisorDilationChannel_seven_zero
  norm_num [mobiusDivisorThreePrimeEnergy,mobiusDivisorPrimeMerge,
    sum_Icc_succ_top,h4,h7,channel_seven_large]
  all_goals ring_nf
  all_goals trivial

/-- Adaptive order cannot make every step contract: all six literal orders increase at the end. -/
theorem mobiusDivisor_every_order_seven_final_increase :
    ∀ p ∈ ({2,3,5} : Finset ℕ), ∀ q ∈ ({2,3,5} : Finset ℕ),
      ∀ r ∈ ({2,3,5} : Finset ℕ), p≠q → p≠r → q≠r →
        mobiusDivisorTwoPrimeEnergy 7 p q < mobiusDivisorThreePrimeEnergy 7 p q r := by
  intro p hp q hq r hr hpq hpr hqr
  have h := mobiusDivisorTwoPrimeEnergy_seven_lt_total_sq p hp q hq hpq
  obtain ⟨h235,h253,h325,h352,h523,h532⟩ := threePrimeEnergy_seven_table
  simp only [mem_insert,mem_singleton] at hp hq hr
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl
  all_goals simp_all only [ne_eq,not_true_eq_false]

end RHTower
