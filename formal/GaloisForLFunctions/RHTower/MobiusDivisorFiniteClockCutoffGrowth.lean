import GaloisForLFunctions.RHTower.MobiusDivisorFiniteClockCountingCancellation

/-!
# Actual cutoff debt in the logarithmically weighted finite source

The first quotient cell survives every finite processed prime core. Its
exact squared source and positive quadratic counting limit force logarithmic
growth of the normalized finite clock energy at each fixed core.

For any prescribed sequence of finite prime cores, strictly increasing
cutoffs can force this actual energy above any prescribed sequence of
heights. Every cutoff lies beyond all primes in its core. Thus a cumulative
payment bound cannot cover arbitrary cutoff schedules, even when the cores
are prescribed to exhaust the primes. This does not exclude a bounded
action along a deliberately coupled core/cutoff schedule.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma first_slope (P : Finset ℕ) :
    mobiusDivisorHeadBlockSlope P 1 = primeFreeDivisorDefect 1 := by
  have h1 : mobiusDivisorSelectionFibre 1 P ∅ = 0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  have h2 : mobiusDivisorSelectionFibre 2 P ∅ =
      (Real.sqrt 2-1)*primeFreeDivisorDefect 1 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre,
      mobiusDivisorDilationChannel_eq_moebius_unsigned, divisorUnsignedDilationChannel]
    norm_num [Finset.filter_singleton]
  have hd : Real.sqrt 2-1 ≠ 0 := ne_of_gt (by
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<2)
    simpa using sub_pos.mpr this)
  simp only [mobiusDivisorHeadBlockSlope, h1, h2]
  norm_num
  exact mul_div_cancel_left₀ _ hd

private lemma first_defect_positive : 0 < primeFreeDivisorDefect 1 := by
  have h := divisorContinuousUnitHead_pos_first (x:=3/2) (by constructor <;> norm_num)
  rw [divisorContinuousUnitHead_between (k:=1) le_rfl (by norm_num) (by norm_num)] at h
  have hz : divisorUnsignedDilationChannel 1 1=0 := by simp [divisorUnsignedDilationChannel]
  norm_num only [hz,zero_add,Nat.cast_one,Real.sqrt_one] at h
  have hs : 0 ≤ Real.sqrt (3/2)-1 := by
    have := Real.sqrt_le_sqrt (show (1:ℝ)≤3/2 by norm_num)
    simpa using sub_nonneg.mpr this
  by_contra hn
  exact (not_le_of_gt h) (mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_gt hn))

private lemma first_primitive (P : Finset ℕ) :
    mobiusDivisorHeadBlockPrimitive P 1 1 -
      mobiusDivisorHeadBlockPrimitive P 1 (1/2) =
        (primeFreeDivisorDefect 1)^(2 : ℕ)*((2/3)*Real.sqrt (1/2)-11/24) := by
  have hi : mobiusDivisorHeadBlockIntercept P 1 = -primeFreeDivisorDefect 1 := by
    simp [mobiusDivisorHeadBlockIntercept, first_slope,
      mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  simp only [mobiusDivisorHeadBlockPrimitive, first_slope, hi, Real.sqrt_one]
  ring

private lemma first_primitive_positive (P : Finset ℕ) :
    0 < mobiusDivisorHeadBlockPrimitive P 1 1 -
      mobiusDivisorHeadBlockPrimitive P 1 (1/2) := by
  rw [first_primitive]
  have hs := Real.sq_sqrt (show (0:ℝ)≤1/2 by norm_num)
  have hn := Real.sqrt_nonneg (1/2:ℝ)
  have hd := first_defect_positive
  apply mul_pos (sq_pos_of_pos hd)
  nlinarith

private lemma first_block_lower (P : Finset ℕ) {M : ℕ} (hM : 2≤M) :
    Real.log ((M:ℝ)/2) * (mobiusDivisorFixedCoreBlockEnergy P M 1/(M:ℝ)^(2 : ℕ)) ≤
      mobiusDivisorFiniteClockEnergy 1 M P/(M:ℝ)^(2 : ℕ) := by
  have hsum : Real.log ((M:ℝ)/2) * mobiusDivisorFixedCoreBlockEnergy P M 1 ≤
      mobiusDivisorFiniteClockEnergy 1 M P := by
    unfold mobiusDivisorFixedCoreBlockEnergy mobiusDivisorFiniteClockEnergy
    rw [mul_sum]
    calc
      _ ≤ ∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=1),
          (1+Real.log r)*(r:ℝ)*(mobiusDivisorInterpolatedFibre M r P ∅)^(2 : ℕ) := by
        apply sum_le_sum
        intro r hr
        obtain ⟨hr,he⟩ := mem_filter.mp hr
        have hr1 := (mem_Icc.mp (mem_filter.mp hr).1).1
        have hh := Nat.lt_mul_div_succ M hr1
        rw [he] at hh
        have hMr : (M:ℝ)/2 ≤ r := by
          have : (M:ℝ)<(r:ℝ)*2 := by exact_mod_cast hh
          linarith
        have hlo : 0<(M:ℝ)/2 := by
          have : (2:ℝ)≤M := by exact_mod_cast hM
          positivity
        have hl := Real.log_le_log hlo hMr
        have hl' : Real.log ((M:ℝ)/2) ≤ 1+Real.log r := by linarith
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hl'
          (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg (mobiusDivisorInterpolatedFibre M r P ∅)))
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro r hr _
        have hr1 : (1:ℝ)≤r := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hr).1).1
        exact mul_nonneg (mul_nonneg (by linarith [Real.log_nonneg hr1])
          (Nat.cast_nonneg r)) (sq_nonneg _)
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hsum (sq_nonneg (M:ℝ))

/-- Positive first-cell mass forces eventual logarithmic cutoff debt in the
literal finite counting measure. The coefficient may depend on the core. -/
theorem exists_mobiusDivisorFiniteClockEnergy_log_lower (P : Finset Nat.Primes) :
    ∃ a : ℝ, 0<a ∧ ∀ᶠ M : ℕ in atTop,
      a*Real.log ((M:ℝ)/2) ≤
      mobiusDivisorFiniteClockEnergy 1 M (P.image (fun p : Nat.Primes => (p:ℕ)))/(M:ℝ)^(2 : ℕ) := by
  let Q := P.image (fun p : Nat.Primes => (p:ℕ))
  have hQ : ∀p∈Q,p.Prime := by
    intro p hp
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hp
    exact p.property
  let m := (Sieve.squarefreeDensity*∏p∈Q,(p:ℝ)/(p+1))*
    (mobiusDivisorHeadBlockPrimitive Q 1 1-mobiusDivisorHeadBlockPrimitive Q 1 (1/2))
  have hm : 0 < m := by
    apply mul_pos _ (first_primitive_positive Q)
    apply mul_pos
    · rw [Sieve.squarefreeDensity_eq]; positivity
    · exact prod_pos (fun p hp => div_pos (by exact_mod_cast (hQ p hp).pos) (by positivity))
  have ht := tendsto_mobiusDivisorFixedCoreBlockEnergy_div_sq Q hQ (by omega : 0<1)
  have ht' : Tendsto (fun M : ℕ => mobiusDivisorFixedCoreBlockEnergy Q M 1/(M:ℝ)^(2 : ℕ))
      atTop (𝓝 m) := by convert ht using 1; norm_num [m]
  refine ⟨m/2,by positivity,?_⟩
  filter_upwards [ht'.eventually (eventually_gt_nhds (show m/2 < m by linarith)),
    eventually_ge_atTop (2:ℕ)] with M hmass hM
  have hlog : 0≤Real.log ((M:ℝ)/2) := Real.log_nonneg (by
    have : (2:ℝ)≤M := by exact_mod_cast hM
    linarith)
  exact (mul_le_mul_of_nonneg_right hmass.le hlog).trans
    (by simpa only [mul_comm] using first_block_lower Q hM)

/-- No fixed finite prime core bounds the normalized logarithmic clock energy. -/
theorem tendsto_mobiusDivisorFiniteClockEnergy_div_sq_atTop (P : Finset Nat.Primes) :
    Tendsto (fun M : ℕ =>
      mobiusDivisorFiniteClockEnergy 1 M (P.image (fun p : Nat.Primes => (p:ℕ)))/(M:ℝ)^(2 : ℕ)) atTop atTop := by
  obtain ⟨a,ha,hl⟩ := exists_mobiusDivisorFiniteClockEnergy_log_lower P
  have ht : Tendsto (fun M : ℕ => a*Real.log ((M:ℝ)/2)) atTop atTop :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0:ℝ)<2))).const_mul_atTop ha
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hl,(tendsto_atTop.mp ht) b] with M hM hb
  exact hb.trans hM

/-- Exact positive source surviving in the first quotient cell, before any
density limit: the core affects only which squarefree indices are counted. -/
theorem mobiusDivisorFixedCoreBlockEnergy_first_eq (P : Finset ℕ) (M : ℕ) :
    mobiusDivisorFixedCoreBlockEnergy P M 1 = (primeFreeDivisorDefect 1)^(2 : ℕ) *
      ∑ r ∈ (fixedCoreSquarefreeIndices P M).filter (fun r => M/r=1),
        (Real.sqrt M-Real.sqrt r)^(2 : ℕ) := by
  have hi : mobiusDivisorHeadBlockIntercept P 1 = -primeFreeDivisorDefect 1 := by
    simp [mobiusDivisorHeadBlockIntercept,first_slope,
      mobiusDivisorSelectionFibre,mobiusDivisorSelectionIndices,subsetLabelFibre]
  unfold mobiusDivisorFixedCoreBlockEnergy
  rw [mul_sum]
  apply sum_congr rfl
  intro r hr
  obtain ⟨hr,he⟩ := mem_filter.mp hr
  have hr0 := (mem_Icc.mp (mem_filter.mp hr).1).1
  have h := mobiusDivisorInterpolatedHead_eq_block_affine P hr0 he
  rw [first_slope,hi] at h
  have hh := congrArg (fun x : ℝ => x^(2 : ℕ)) h
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg r)] at hh
  rw [hh]
  ring

/-- Produce arbitrarily large action along any prescribed finite-core history
by advancing the cutoff. This is an adverse schedule, not a bounded schedule. -/
theorem exists_mobiusDivisorFiniteClockEnergy_growing_cutoffs
    (P : ℕ → Finset Nat.Primes) (b : ℕ → ℝ) :
    ∃ M : ℕ → ℕ, StrictMono M ∧ ∀ n,
      (∀ p ∈ P n, (p:ℕ) < M n) ∧
      b n ≤ mobiusDivisorFiniteClockEnergy 1 (M n)
        ((P n).image (fun p : Nat.Primes => (p:ℕ)))/(M n:ℝ)^(2 : ℕ) := by
  have hthreshold : ∀ n, ∃ N : ℕ, ∀ M : ℕ, N≤M →
      b n ≤ mobiusDivisorFiniteClockEnergy 1 M
        ((P n).image (fun p : Nat.Primes => (p:ℕ)))/(M:ℝ)^(2 : ℕ) := by
    intro n
    exact eventually_atTop.mp ((tendsto_atTop.mp
      (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_atTop (P n))) (b n))
  choose N hN using hthreshold
  let L : ℕ → ℕ := fun n => N n + (P n).sup (fun p : Nat.Primes => (p:ℕ)) + 1
  let M : ℕ → ℕ := fun n => ∑ k ∈ range (n+1), L k
  have hLM (n : ℕ) : L n ≤ M n :=
    single_le_sum (fun k _ => Nat.zero_le (L k)) (mem_range.mpr (Nat.lt_succ_self n))
  refine ⟨M,strictMono_nat_of_lt_succ (fun n => ?_),fun n => ⟨?_,?_⟩⟩
  · change (∑ k ∈ range (n+1), L k) < ∑ k ∈ range ((n+1)+1), L k
    rw [Finset.sum_range_succ (f := L) (n := n+1)]
    have : 0 < L (n+1) := by dsimp [L]; omega
    omega
  · intro p hp
    have hp' : (p:ℕ) ≤ (P n).sup (fun p : Nat.Primes => (p:ℕ)) := le_sup hp
    have hh := hLM n
    dsimp [L] at hh
    omega
  · apply hN n (M n)
    have hh := hLM n
    dsimp [L] at hh
    omega
end RHTower
