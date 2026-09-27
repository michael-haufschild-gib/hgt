import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating a finite logarithmic entry sum

Arbitrary signed coefficients enter at their logarithmic integer times.
On a bounded time interval a common finite prefix gives integrability and
an exact sum of tail integrals. No infinite interchange is needed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def logarithmicEntrySum (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, w n

theorem logarithmicEntrySum_eq_common_prefix (w : ℕ → ℝ) {T t : ℝ} (ht : t ≤ T) :
    logarithmicEntrySum w t =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        (Ici (Real.log n)).indicator (fun _ : ℝ => w n) t := by
  classical
  have hset : (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun n : ℕ => Real.log n ≤ t) =
      Finset.Icc 1 ⌊Real.exp t⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn, _⟩, hlog⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      exact ⟨hn, (Nat.le_floor_iff (Real.exp_pos t).le).mpr
        ((Real.log_le_iff_le_exp hnpos).mp hlog)⟩
    · rintro ⟨hn, hnt⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      exact ⟨⟨hn, hnt.trans (Nat.floor_mono (Real.exp_le_exp.mpr ht))⟩,
        (Real.log_le_iff_le_exp hnpos).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hnt)⟩
  rw [logarithmicEntrySum, ← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ t <;> simp [hn]

private theorem weighted_common_prefix (w : ℕ → ℝ) (g : ℝ → ℝ)
    {T t : ℝ} (ht : t ≤ T) :
    g t * logarithmicEntrySum w t =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        (Ici (Real.log n)).indicator (fun s : ℝ => w n * g s) t := by
  rw [logarithmicEntrySum_eq_common_prefix w ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ t <;> simp [hn, mul_comm]

theorem intervalIntegrable_mul_logarithmicEntrySum_of_intervalIntegrable (w : ℕ → ℝ)
    (g : ℝ → ℝ) {T : ℝ} (hg : IntervalIntegrable g volume 0 T) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => g t * logarithmicEntrySum w t) volume 0 T := by
  classical
  have hi (n : ℕ) : IntervalIntegrable
      ((Ici (Real.log n)).indicator (fun t : ℝ => w n * g t)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact (hg.const_mul (w n)).1.indicator measurableSet_Ici
  have hs := IntervalIntegrable.sum (s := Finset.Icc 1 ⌊Real.exp T⌋₊) (fun n _ => hi n)
  apply hs.congr
  intro t ht
  have htT : t ≤ T := (uIoc_of_le hT ▸ ht).2
  simpa only [Finset.sum_apply] using (weighted_common_prefix w g htT).symm

theorem intervalIntegrable_mul_logarithmicEntrySum (w : ℕ → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => g t * logarithmicEntrySum w t) volume 0 T :=
  intervalIntegrable_mul_logarithmicEntrySum_of_intervalIntegrable w g
    (hg.intervalIntegrable 0 T) hT

private theorem integral_indicator_Ici (g : ℝ → ℝ) {c T : ℝ}
    (hc : 0 ≤ c) (hcT : c ≤ T) :
    (∫ t in (0 : ℝ)..T, (Ici c).indicator g t) = ∫ t in c..T, g t := by
  rw [intervalIntegral.integral_of_le (hc.trans hcT),
    integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    intervalIntegral.integral_of_le hcT]
  apply setIntegral_congr_set
  have hset : Ioi c ∩ Ioc 0 T = Ioc c T := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨hct, _, htT⟩
      exact ⟨hct, htT⟩
    · rintro ⟨hct, htT⟩
      exact ⟨hct, hc.trans_lt hct, htT⟩
  simpa only [hset] using
    ((Ioi_ae_eq_Ici (μ := volume) (a := c)).inter (ae_eq_refl (Ioc 0 T))).symm

theorem integral_mul_logarithmicEntrySum_of_intervalIntegrable (w : ℕ → ℝ)
    (g : ℝ → ℝ) {T : ℝ} (hg : IntervalIntegrable g volume 0 T) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, g t * logarithmicEntrySum w t) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, w n * ∫ t in Real.log n..T, g t := by
  classical
  have hi (n : ℕ) : IntervalIntegrable
      ((Ici (Real.log n)).indicator (fun t : ℝ => w n * g t)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact (hg.const_mul (w n)).1.indicator measurableSet_Ici
  have hp (t : ℝ) (ht : t ∈ uIcc 0 T) :=
    weighted_common_prefix w g ((uIcc_of_le hT ▸ ht).2)
  rw [intervalIntegral.integral_congr hp,
    intervalIntegral.integral_finsetSum (fun n _ => hi n)]
  apply Finset.sum_congr rfl
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlogT : Real.log n ≤ T := (Real.log_le_iff_le_exp (zero_lt_one.trans_le hnR)).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
  rw [integral_indicator_Ici _ (Real.log_nonneg hnR) hlogT,
    intervalIntegral.integral_const_mul]

theorem integral_mul_logarithmicEntrySum (w : ℕ → ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, g t * logarithmicEntrySum w t) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, w n * ∫ t in Real.log n..T, g t :=
  integral_mul_logarithmicEntrySum_of_intervalIntegrable w g
    (hg.intervalIntegrable 0 T) hT

end RHTower
