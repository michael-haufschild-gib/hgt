import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitPrimeWork
import GaloisForLFunctions.RHTower.CCM.CCMPrimeEntryOverlapKernel

/-!
# The critical deficit energy as a centered prime-pair quadratic

All prime entries below the terminal cutoff are placed in one common finite
prefix. The exact squared deficit then consists of continuous background,
signed mixed work, and the complete prime-pair overlap. The mixed term and
the overlap boundary correction are retained; positivity alone is not used
as an upper estimate for the centered energy.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace RHTower

def ccmPrimeEntryPrefix (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * ccmPrimeEntryTent (Real.log n) t

def ccmPrimeEntryPairPrefix (T : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
      ccmPrimeEntryOverlap T (Real.log n) (Real.log m)

def ccmPrimeEntryBackgroundPrefix (T : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n *
    ((T - Real.log n) ^ 2 / 2 - Real.exp (-Real.log n) +
      Real.exp (-T) * (T - Real.log n + 1))

theorem continuous_ccmPrimeEntryPrefix (N : ℕ) : Continuous (ccmPrimeEntryPrefix N) := by
  unfold ccmPrimeEntryPrefix ccmPrimeEntryTent
  fun_prop

/-- A single terminal prefix represents the actual deficit at every earlier
time; future prime entries have zero causal tent. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_entry_prefix {N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hcut : ⌊Real.exp t⌋₊ ≤ N) :
    ccmLogChebyshevDeficitPrimitive t = Real.exp t - 1 - ccmPrimeEntryPrefix N t := by
  have hsmall : ccmPrimeEntryPrefix ⌊Real.exp t⌋₊ t =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt n * (t - Real.log n) := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
    have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp hnR).mpr
      ((Nat.le_floor_iff (Real.exp_pos t).le).mp hnT)
    rw [ccmPrimeEntryTent, max_eq_left (sub_nonneg.mpr hlog)]
  have hbig : ccmPrimeEntryPrefix ⌊Real.exp t⌋₊ t = ccmPrimeEntryPrefix N t := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hcut⟩
    · intro n hn hnot
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
      have hnt : ¬n ≤ ⌊Real.exp t⌋₊ := fun h => hnot (Finset.mem_Icc.mpr ⟨hn1, h⟩)
      have he : Real.exp t < n := lt_of_not_ge fun h =>
        hnt ((Nat.le_floor_iff (Real.exp_pos t).le).mpr h)
      have hlog : t < Real.log n := (Real.lt_log_iff_exp_lt hnR).mpr he
      simp only [ccmPrimeEntryTent, max_eq_right (sub_nonpos.mpr hlog.le), mul_zero]
  rw [ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents ht, ← hsmall, hbig]

/-- All pair interactions, including distinct prime powers, form the literal
quadratic energy of the common finite prime prefix. -/
theorem integral_ccmPrimeEntryPrefix_sq_eq_pair (T : ℝ) (N : ℕ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeEntryPrefix N t ^ 2) =
      ccmPrimeEntryPairPrefix T N := by
  let S := Finset.Icc 1 N
  let f : ℕ → ℕ → ℝ → ℝ := fun n m t =>
    ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m *
      (Real.exp (-t) * ccmPrimeEntryTent (Real.log n) t * ccmPrimeEntryTent (Real.log m) t)
  have hf (n m : ℕ) : IntervalIntegrable (f n m) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold f ccmPrimeEntryTent
    fun_prop
  have hp (t : ℝ) : Real.exp (-t) * ccmPrimeEntryPrefix N t ^ 2 =
      ∑ n ∈ S, ∑ m ∈ S, f n m t := by
    unfold ccmPrimeEntryPrefix
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    dsimp only [f]
    ring
  simp_rw [hp]
  have hinner (n : ℕ) : IntervalIntegrable (fun t => ∑ m ∈ S, f n m t) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold f ccmPrimeEntryTent
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun n _ => hinner n)]
  unfold ccmPrimeEntryPairPrefix
  apply Finset.sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_finsetSum (fun m _ => hf n m)]
  apply Finset.sum_congr rfl
  intro m _
  exact intervalIntegral.integral_const_mul _ _

theorem integral_ccmPrimeEntryPrefix_background (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (1 - Real.exp (-t)) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) =
      ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ := by
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  let f : ℕ → ℝ → ℝ := fun n t => ArithmeticFunction.vonMangoldt n *
    ((1 - Real.exp (-t)) * ccmPrimeEntryTent (Real.log n) t)
  have hf (n : ℕ) : IntervalIntegrable (f n) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold f ccmPrimeEntryTent
    fun_prop
  have hp (t : ℝ) : (1 - Real.exp (-t)) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t =
      ∑ n ∈ S, f n t := by
    unfold ccmPrimeEntryPrefix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [f]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun n _ => hf n)]
  unfold ccmPrimeEntryBackgroundPrefix
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnT : n ≤ ⌊Real.exp T⌋₊ := (Finset.mem_Icc.mp hn).2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog0 := Real.log_nonneg hnR
  have hlogT : Real.log n ≤ T := (Real.log_le_iff_le_exp (zero_lt_one.trans_le hnR)).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT)
  dsimp only [f]
  rw [intervalIntegral.integral_const_mul, ccmPrimeEntry_background_overlap hlog0 hlogT]

/-- Exact centered prime-pair formula for the full critical energy. The
mixed term is subtracted before any size estimate is applied. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_eq_pair {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      Real.exp T - Real.exp (-T) - 2 * T -
        2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
          ccmPrimeEntryPairPrefix T ⌊Real.exp T⌋₊ := by
  let N := ⌊Real.exp T⌋₊
  let B : ℝ → ℝ := fun t => Real.exp (-t) * (Real.exp t - 1) ^ 2
  let M : ℝ → ℝ := fun t => (1 - Real.exp (-t)) * ccmPrimeEntryPrefix N t
  let P : ℝ → ℝ := fun t => Real.exp (-t) * ccmPrimeEntryPrefix N t ^ 2
  have hB : IntervalIntegrable B volume 0 T := by apply Continuous.intervalIntegrable; fun_prop
  have hM : IntervalIntegrable M volume 0 T := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).mul
      (continuous_ccmPrimeEntryPrefix N)
  have hP : IntervalIntegrable P volume 0 T := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp continuous_neg).mul ((continuous_ccmPrimeEntryPrefix N).pow 2)
  have hp (t : ℝ) (ht : t ∈ uIcc 0 T) : ccmPrimeDeficitCriticalEnergy t = B t - 2 * M t + P t := by
    have ht' := uIcc_of_le hT ▸ ht
    rw [ccmPrimeDeficitCriticalEnergy,
      ccmLogChebyshevDeficitPrimitive_eq_entry_prefix ht'.1
        (Nat.floor_mono (Real.exp_le_exp.mpr ht'.2))]
    dsimp only [B, M, P, N]
    have hc : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hmul := congrArg (fun x : ℝ => x * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) hc
    nlinarith only [hmul]
  rw [intervalIntegral.integral_congr hp,
    intervalIntegral.integral_add (hB.sub (hM.const_mul 2)) hP,
    intervalIntegral.integral_sub hB (hM.const_mul 2), intervalIntegral.integral_const_mul]
  rw [show (∫ t in (0 : ℝ)..T, B t) = Real.exp T - Real.exp (-T) - 2 * T from
    ccmPrimeEntry_background_energy T,
    show (∫ t in (0 : ℝ)..T, M t) = ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ from
      integral_ccmPrimeEntryPrefix_background T,
    show (∫ t in (0 : ℝ)..T, P t) = ccmPrimeEntryPairPrefix T ⌊Real.exp T⌋₊ from
      integral_ccmPrimeEntryPrefix_sq_eq_pair T N]

end RHTower
