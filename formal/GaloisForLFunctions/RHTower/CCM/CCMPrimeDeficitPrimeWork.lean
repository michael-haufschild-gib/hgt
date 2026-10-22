import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitCriticalEnergy

/-!
# The critical signed work as a finite prime-entry sum

The damping identity is expanded into the literal continuous background work
minus finite prime-entry work. Each prime power carries its own von Mangoldt
weight and a tail integral of the signed deficit. These tails may have either
sign. No independence, random-prime model, or unproved sign estimate is used.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace RHTower

private theorem integral_indicator_Ici_of_between (g : ℝ → ℝ) {c T : ℝ}
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

private theorem psi_exp_eq_common_entry_sum {T t : ℝ} (ht : t ≤ T) :
    Chebyshev.psi (Real.exp t) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        (Ici (Real.log n)).indicator (fun _ : ℝ => ArithmeticFunction.vonMangoldt n) t := by
  classical
  have hset : (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun n : ℕ => Real.log n ≤ t) =
      Finset.Icc 1 ⌊Real.exp t⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn, _⟩, hlog⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      exact ⟨hn, (Nat.le_floor_iff (Real.exp_pos t).le).mpr
        ((Real.log_le_iff_le_exp hnpos).mp hlog)⟩
    · rintro ⟨hn, hnt⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      exact ⟨⟨hn, hnt.trans (Nat.floor_mono (Real.exp_le_exp.mpr ht))⟩,
        (Real.log_le_iff_le_exp hnpos).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hnt)⟩
  have hpsi : Chebyshev.psi (Real.exp t) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, ArithmeticFunction.vonMangoldt n := by
    simp only [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  rw [hpsi, ← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ t <;> simp [hn]

/-- Continuous signed weights pass through the literal finite prime-entry
sum, with the exact tail interval starting at each logarithmic prime power. -/
theorem integral_mul_psi_exp_eq_prime_entry_tails (g : ℝ → ℝ) (hg : Continuous g)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, g t * Chebyshev.psi (Real.exp t)) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        ArithmeticFunction.vonMangoldt n * ∫ t in Real.log n..T, g t := by
  classical
  let f : ℕ → ℝ → ℝ := fun n => (Ici (Real.log n)).indicator
    (fun t => ArithmeticFunction.vonMangoldt n * g t)
  have hf (n : ℕ) : IntervalIntegrable (f n) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hi := ((hg.const_mul (ArithmeticFunction.vonMangoldt n)).intervalIntegrable
      (μ := volume) 0 T).1
    exact hi.indicator measurableSet_Ici
  have hpoint (t : ℝ) (ht : t ∈ uIcc 0 T) :
      g t * Chebyshev.psi (Real.exp t) = ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, f n t := by
    rw [psi_exp_eq_common_entry_sum ((uIcc_of_le hT ▸ ht).2), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : Real.log n ≤ t <;> simp [f, hn, mul_comm]
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_finsetSum (fun n _ => hf n)]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlogT : Real.log n ≤ T := (Real.log_le_iff_le_exp (zero_lt_one.trans_le hnR)).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT)
  dsimp only [f]
  rw [integral_indicator_Ici_of_between _ hlog0 hlogT,
    intervalIntegral.integral_const_mul]

/-- The signed deficit is a literal finite logarithmic tent sum. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_prime_log_tents {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T = Real.exp T - 1 -
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        ArithmeticFunction.vonMangoldt n * (T - Real.log n) := by
  have hi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi (Real.exp t)) volume 0 T :=
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable
  have h := integral_mul_psi_exp_eq_prime_entry_tails (fun _ => 1) continuous_const hT
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  rw [ccmLogChebyshevDeficitPrimitive,
    intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 T) hi,
    integral_exp, Real.exp_zero, h]

/-- The literal arithmetic work retains cancellation between continuous
background and the weighted future deficit seen by every prime entry. -/
theorem ccmPrimeDeficitSignedWork_eq_prime_entry_tails {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitSignedWorkDensity t) =
      (∫ t in (0 : ℝ)..T, ccmLogChebyshevDeficitPrimitive t) -
        ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ArithmeticFunction.vonMangoldt n *
          ∫ t in Real.log n..T, Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t := by
  let g : ℝ → ℝ := fun t => Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t
  have hg : Continuous g := (Real.continuous_exp.comp continuous_neg).mul
    continuous_ccmLogChebyshevDeficitPrimitive
  have hpoint (t : ℝ) : ccmPrimeDeficitSignedWorkDensity t =
      ccmLogChebyshevDeficitPrimitive t - g t * Chebyshev.psi (Real.exp t) := by
    have he : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    dsimp only [ccmPrimeDeficitSignedWorkDensity, g]
    calc
      _ = (Real.exp (-t) * Real.exp t) * ccmLogChebyshevDeficitPrimitive t -
          Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t * Chebyshev.psi (Real.exp t) := by ring
      _ = _ := by rw [he, one_mul]
  simp_rw [hpoint]
  have hi : IntervalIntegrable (fun t => g t * Chebyshev.psi (Real.exp t)) volume 0 T :=
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable.continuousOn_mul hg.continuousOn
  rw [intervalIntegral.integral_sub
    (continuous_ccmLogChebyshevDeficitPrimitive.intervalIntegrable 0 T) hi,
    integral_mul_psi_exp_eq_prime_entry_tails g hg hT]

/-- A new unconditional signed inequality: prime-entry work cannot exceed
the continuous background work. The exact gap pays for critical energy. -/
theorem ccmPrimeDeficit_prime_entry_work_le_background {T : ℝ} (hT : 0 ≤ T) :
    (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ArithmeticFunction.vonMangoldt n *
      ∫ t in Real.log n..T, Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t) ≤
      ∫ t in (0 : ℝ)..T, ccmLogChebyshevDeficitPrimitive t := by
  have h := ccmPrimeDeficitSignedWork_nonneg hT
  rw [ccmPrimeDeficitSignedWork_eq_prime_entry_tails hT] at h
  exact sub_nonneg.mp h

/-- Full finite prime-work identity at square-root scale. This gives an
exact arithmetic target for an upper bound without taking absolute values. -/
theorem ccmPrimeDeficitCriticalEnergy_prime_work_balance {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCriticalEnergy T +
      (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      2 * ((∫ t in (0 : ℝ)..T, ccmLogChebyshevDeficitPrimitive t) -
        ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ArithmeticFunction.vonMangoldt n *
          ∫ t in Real.log n..T, Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t) := by
  have h := ccmPrimeDeficitCriticalEnergy_balance 0 T
  rw [ccmPrimeDeficitSignedWork_eq_prime_entry_tails hT] at h
  simpa only [ccmPrimeDeficitCriticalEnergy_zero, sub_zero] using h

end RHTower
