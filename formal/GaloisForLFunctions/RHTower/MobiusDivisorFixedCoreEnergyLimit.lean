import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreBlockLimit
import GaloisForLFunctions.RHTower.MobiusDivisorLocalizedInteractions
import Mathlib.Topology.Algebra.InfiniteSum.Real
/-!
# Complete fixed-core divisor-energy limit

The actual squarefree source decomposes into quotient blocks with a
nonnegative remainder. The corpus's source amplitude bound and the count
of labels below M/T give an explicit reciprocal-depth bound, valid even
for the empty processed core. This uniform tail joins the previously
proved arithmetic block limits into a convergent nonnegative series and
the complete energy's quadratic-scale limit.

The bound depends on processed cardinality. No signed reserve, uniformity
through growing processed cores, complete selection or RH is asserted.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

private lemma term_nonneg (P : Finset ℕ) (M r : ℕ) :
    0 ≤ (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 := by positivity

private lemma sample_self (P : Finset ℕ) {M : ℕ} (hM : 0 < M) :
    mobiusDivisorInterpolatedFibre M M P ∅ = 0 := by
  have hw : divisorPrimeClipWeight M M = 0 := by
    simp [divisorPrimeClipWeight, Nat.div_self hM]
  simp [mobiusDivisorInterpolatedFibre, hw, Nat.div_self hM,
    mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]

theorem mobiusDivisorSelectionEnergy_eq_inclusive_squarefree (P : Finset ℕ) (M : ℕ) :
    mobiusDivisorSelectionEnergy M P = ∑ r ∈ fixedCoreSquarefreeIndices P M,
      (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 := by
  rw [mobiusDivisorSelectionEnergy_eq_squarefree_processedHead]
  apply sum_subset
  · intro r hr
    simp only [mobiusDivisorSelectionIndices, fixedCoreSquarefreeIndices,
      mem_filter, mem_Icc] at hr ⊢
    exact ⟨⟨hr.1.1.1, (hr.1.1.2.trans (Nat.sub_le _ _))⟩, hr.1.2, hr.2⟩
  · intro r hr hnot
    simp only [mobiusDivisorSelectionIndices, fixedCoreSquarefreeIndices,
      mem_filter, mem_Icc] at hr hnot
    have hlt : ¬ r ≤ M-1 := by
      intro h
      exact hnot ⟨⟨⟨hr.1.1,h⟩,hr.2.1⟩,hr.2.2⟩
    have he : r=M := by omega
    subst r
    rw [sample_self P (by omega), sq, zero_mul, mul_zero]

private lemma prefix_eq (P : Finset ℕ) (M T : ℕ) :
    ∑ n ∈ range T, mobiusDivisorFixedCoreBlockEnergy P M n =
      ∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => M/r<T),
        (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 := by
  simpa only [mobiusDivisorFixedCoreBlockEnergy, mem_range] using
    sum_fiberwise_eq_sum_filter (fixedCoreSquarefreeIndices P M) (range T)
      (fun r => M/r) (fun r => (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2)

private lemma term_as_fibre (P : Finset ℕ) (M : ℕ) {r : ℕ}
    (hr : Squarefree r) (hd : Disjoint r.primeFactors P) :
    (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 =
      (mobiusDivisorSelectionFibre M P r.primeFactors)^2 := by
  have h := mobiusDivisorSelectionFibre_product_interpolation M P r.primeFactors
    (fun p hp => (Nat.mem_primeFactors.mp hp).1) hd
  rw [Nat.prod_primeFactors_of_squarefree hr] at h
  have hm : (((ArithmeticFunction.moebius r : ℤ) : ℝ))^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr
  rw [h, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg r), hm, mul_one]

/-- The entire large-quotient energy has a reciprocal-depth bound for every
fixed prime core, including the empty core. Its constant is explicit. -/
theorem mobiusDivisorFixedCoreEnergy_quotient_tail_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) {T : ℕ} (hT : 0 < T) :
    (∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => T ≤ M/r),
      (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2) ≤
        (((3/5:ℝ)*2^(P.card-1))^2/(T : ℝ))*(M : ℝ)^2 := by
  let C : ℝ := (3/5:ℝ)*2^(P.card-1)
  let A := (fixedCoreSquarefreeIndices P M).filter (fun r => T ≤ M/r)
  have hcard : A.card ≤ M/T := by
    have hs : A ⊆ Icc 1 (M/T) := by
      intro r hr
      obtain ⟨hr,hquot⟩ := mem_filter.mp hr
      have hr' := mem_Icc.mp (mem_filter.mp hr).1
      apply mem_Icc.mpr
      refine ⟨hr'.1, (Nat.le_div_iff_mul_le hT).mpr ?_⟩
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hr'.1).mp hquot
    simpa using card_le_card hs
  calc
    _ ≤ ∑ r ∈ A, C^2*(M : ℝ) := by
      apply sum_le_sum
      intro r hr
      obtain ⟨hr,_⟩ := mem_filter.mp hr
      obtain ⟨_,hsf,hd⟩ := mem_filter.mp hr
      rw [term_as_fibre P M hsf hd]
      have hb := abs_mobiusDivisorSelectionFibre_le_source_amplitude M P r.primeFactors hP
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
      change |mobiusDivisorSelectionFibre M P r.primeFactors| ≤ C*Real.sqrt M at hb
      have hs := Real.sq_sqrt (Nat.cast_nonneg M)
      have hab := abs_nonneg (mobiusDivisorSelectionFibre M P r.primeFactors)
      have hsq := sq_abs (mobiusDivisorSelectionFibre M P r.primeFactors)
      nlinarith [sq_nonneg (C*Real.sqrt M-|mobiusDivisorSelectionFibre M P r.primeFactors|)]
    _ = (A.card : ℝ)*(C^2*(M : ℝ)) := by simp
    _ ≤ ((M/T : ℕ) : ℝ)*(C^2*(M : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      positivity
    _ ≤ ((M : ℝ)/T)*(C^2*(M : ℝ)) := by
      apply mul_le_mul_of_nonneg_right Nat.cast_div_le
      positivity
    _ = _ := by dsimp [C]; ring

private lemma tail_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M : ℕ,
      (∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => T ≤ M/r),
        (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2) ≤ ε*(M : ℝ)^2 := by
  let C : ℝ := (3/5:ℝ)*2^(P.card-1)
  obtain ⟨T,hT⟩ := exists_nat_gt (max (C^2/ε) 0)
  have hTR : 0 < (T : ℝ) := (le_max_right _ _).trans_lt hT
  have hTN : 0 < T := by exact_mod_cast hTR
  have hsmall : C^2/(T : ℝ) ≤ ε := by
    apply (div_le_iff₀ hTR).mpr
    have h := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hT)
    linarith
  refine ⟨T,hTN,fun M => ?_⟩
  exact (mobiusDivisorFixedCoreEnergy_quotient_tail_le P hP M hTN).trans
    (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))

private lemma prefix_remainder (P : Finset ℕ) (M T : ℕ) :
    mobiusDivisorSelectionEnergy M P-∑ n ∈ range T, mobiusDivisorFixedCoreBlockEnergy P M n =
      ∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => T ≤ M/r),
        (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2 := by
  rw [mobiusDivisorSelectionEnergy_eq_inclusive_squarefree, prefix_eq]
  have h := sum_filter_add_sum_filter_not (s:=fixedCoreSquarefreeIndices P M)
    (fun r => M/r<T) (fun r => (r : ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^2)
  simpa only [not_lt] using (eq_sub_of_add_eq' h).symm

/-- Explicit limiting mass of one quotient block, including its empty zero cell. -/
def mobiusDivisorFixedCoreBlockMass (P : Finset ℕ) (n : ℕ) : ℝ :=
  if n=0 then 0 else
    (Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*
      (mobiusDivisorHeadBlockPrimitive P n (1/(n : ℝ))-
        mobiusDivisorHeadBlockPrimitive P n (1/((n : ℝ)+1)))

private lemma block_zero (P : Finset ℕ) (M : ℕ) :
    mobiusDivisorFixedCoreBlockEnergy P M 0 = 0 := by
  unfold mobiusDivisorFixedCoreBlockEnergy
  apply sum_eq_zero
  intro r hr
  obtain ⟨hr,he⟩ := mem_filter.mp hr
  have hr' := mem_Icc.mp (mem_filter.mp hr).1
  have h : 1 ≤ M/r := (Nat.le_div_iff_mul_le hr'.1).mpr (by simpa using hr'.2)
  omega

private lemma block_limit (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    Tendsto (fun M : ℕ => mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^2) atTop
      (𝓝 (mobiusDivisorFixedCoreBlockMass P n)) := by
  by_cases hn : n=0
  · simp [hn, block_zero, mobiusDivisorFixedCoreBlockMass]
  · simpa only [mobiusDivisorFixedCoreBlockMass, if_neg hn] using
      tendsto_mobiusDivisorFixedCoreBlockEnergy_div_sq P hP (by omega : 0<n)

/-- Finite quotient depth approximates the complete normalized energy
uniformly at every cutoff, with the full omitted source nonnegative. -/
theorem exists_mobiusDivisorSelectionEnergy_uniform_block_approx
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M : ℕ,
      0 ≤ mobiusDivisorSelectionEnergy M P/(M : ℝ)^2-
        ∑ n ∈ range T, mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^2 ∧
      mobiusDivisorSelectionEnergy M P/(M : ℝ)^2-
        ∑ n ∈ range T, mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^2 ≤ ε := by
  obtain ⟨T,hT,hbound⟩ := tail_bound P hP ε hε
  refine ⟨T,hT,fun M => ?_⟩
  rw [← sum_div, ← sub_div, prefix_remainder]
  constructor
  · exact div_nonneg (sum_nonneg (fun r _ => term_nonneg P M r)) (sq_nonneg _)
  · by_cases hM : M=0
    · simp [hM, hε.le]
    · have hMR : 0 < (M : ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hM)
      apply (div_le_iff₀ hMR).mpr
      exact hbound M

private lemma prefix_limit (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (T : ℕ) :
    Tendsto (fun M : ℕ => ∑ n ∈ range T,
      mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^2) atTop
      (𝓝 (∑ n ∈ range T, mobiusDivisorFixedCoreBlockMass P n)) :=
  tendsto_finsetSum _ (fun n _ => block_limit P hP n)

private lemma prefix_le (P : Finset ℕ) (M T : ℕ) :
    (∑ n ∈ range T, mobiusDivisorFixedCoreBlockEnergy P M n/(M : ℝ)^2) ≤
      mobiusDivisorSelectionEnergy M P/(M : ℝ)^2 := by
  apply sub_nonneg.mp
  rw [← sum_div, ← sub_div, prefix_remainder]
  exact div_nonneg (sum_nonneg (fun r _ => term_nonneg P M r)) (sq_nonneg _)

private lemma energy_limit_exists (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∃ κ : ℝ, Tendsto (fun M : ℕ => mobiusDivisorSelectionEnergy M P/(M : ℝ)^2) atTop (𝓝 κ) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨T,_,hT⟩ := exists_mobiusDivisorSelectionEnergy_uniform_block_approx P hP
    (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (prefix_limit P hP T).cauchySeq (ε/3) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have hm' := hT m
  have hn' := hT n
  have hmid := hN m hm n hn
  rw [Real.dist_eq] at hmid ⊢
  rw [abs_lt] at hmid ⊢
  constructor <;> linarith

/-- Every explicit limiting quotient mass is nonnegative, from its literal
nonnegative arithmetic energy rather than a sign assumption on its formula. -/
theorem mobiusDivisorFixedCoreBlockMass_nonneg
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    0 ≤ mobiusDivisorFixedCoreBlockMass P n := by
  apply ge_of_tendsto' (block_limit P hP n)
  intro M
  exact div_nonneg (sum_nonneg (fun r _ => term_nonneg P M r)) (sq_nonneg _)

private lemma energy_series_limit (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (mobiusDivisorFixedCoreBlockMass P) ∧
      Tendsto (fun M : ℕ => mobiusDivisorSelectionEnergy M P/(M : ℝ)^2) atTop
        (𝓝 (∑' n, mobiusDivisorFixedCoreBlockMass P n)) := by
  obtain ⟨κ,hκ⟩ := energy_limit_exists P hP
  have hprefix (T : ℕ) : (∑ n ∈ range T, mobiusDivisorFixedCoreBlockMass P n) ≤ κ :=
    le_of_tendsto_of_tendsto' (prefix_limit P hP T) hκ (fun M => prefix_le P M T)
  have hs := summable_of_sum_range_le (mobiusDivisorFixedCoreBlockMass_nonneg P hP) hprefix
  refine ⟨hs, ?_⟩
  have he : κ = ∑' n, mobiusDivisorFixedCoreBlockMass P n := by
    apply le_antisymm
    · by_contra hnot
      have hgap : 0 < κ-∑' n, mobiusDivisorFixedCoreBlockMass P n := sub_pos.mpr (lt_of_not_ge hnot)
      obtain ⟨T,_,hT⟩ := exists_mobiusDivisorSelectionEnergy_uniform_block_approx P hP
        ((κ-∑' n, mobiusDivisorFixedCoreBlockMass P n)/2) (by positivity)
      have hb : κ-(∑ n ∈ range T, mobiusDivisorFixedCoreBlockMass P n) ≤
          (κ-∑' n, mobiusDivisorFixedCoreBlockMass P n)/2 :=
        le_of_tendsto' (hκ.sub (prefix_limit P hP T)) (fun M => (hT M).2)
      have hle := hs.sum_le_tsum (range T) (fun n _ => mobiusDivisorFixedCoreBlockMass_nonneg P hP n)
      linarith
    · exact hs.tsum_le_of_sum_range_le hprefix
  simpa only [he] using hκ

/-- All quotient masses of any fixed prime core form a convergent
nonnegative series; no upper cutoff on quotient depth is assumed. -/
theorem summable_mobiusDivisorFixedCoreBlockMass
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (mobiusDivisorFixedCoreBlockMass P) :=
  (energy_series_limit P hP).1

/-- The complete fixed-core divisor energy has its explicit quadratic-scale
limit, the sum of all actual quotient masses. -/
theorem tendsto_mobiusDivisorSelectionEnergy_div_sq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun M : ℕ => mobiusDivisorSelectionEnergy M P/(M : ℝ)^2) atTop
      (𝓝 (∑' n, mobiusDivisorFixedCoreBlockMass P n)) :=
  (energy_series_limit P hP).2

end RHTower
