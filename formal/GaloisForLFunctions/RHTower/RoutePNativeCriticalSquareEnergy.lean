import GaloisForLFunctions.RHTower.RoutePSourceCriticalSquareNonintegrability
import GaloisForLFunctions.RHTower.CriticalAbelRoutePAsymptoticBridge
import GaloisForLFunctions.RHTower.MobiusDivisorFullHeadCompletion
import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadBlocks
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadFiniteSource
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeAbelMellinFactorization

/-!
# Infinite undamped square energy of the complete native Möbius head

The complete head agrees with the critical Abel primitive at every real
cutoff. The exponentially decaying Route-P correction then transfers the
unconditional critical square-energy obstruction to this literal head.
No finite-core limit or RH premise is used.
-/

noncomputable section
open MeasureTheory Set Finset Filter Topology

namespace RHTower

private theorem fullHead_nat_eq_criticalAbel (M : ℕ) :
    mobiusDivisorFullHead M = criticalContinuousAbel M := by
  calc
    mobiusDivisorFullHead M = ∑ d ∈ Finset.Icc 1 M, mobiusDivisorDilationChannel M d := by
      rw [mobiusDivisorFullHead, Nat.floor_natCast]
      apply Finset.sum_congr rfl
      intro d hd
      rw [mul_assoc, divisorContinuousUnitHead_dilation M d (Finset.mem_Icc.mp hd).1,
        mobiusDivisorDilationChannel_eq_moebius_unsigned]
    _ = ∑ k ∈ Finset.Ico 1 M,
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k :=
      sum_mobiusDivisorDilationChannel_eq_psiDefect_abel M
    _ = criticalContinuousAbel M := by
      rw [criticalContinuousAbel, squareRootSummatoryPrimitive_nat, Complex.re_sum]
      have hsets : Finset.Icc 1 (M - 1) = Finset.Ico 1 M := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hsets]
      apply Finset.sum_congr rfl
      intro k hk
      rw [criticalSourceCoeff_cumulative k (Finset.mem_Ico.mp hk).1]
      simp

/-- Exact all-real identification, including the original physical cutoff. -/
theorem mobiusDivisorFullHead_eq_criticalContinuousAbel (x : ℝ) :
    mobiusDivisorFullHead x = criticalContinuousAbel x := by
  classical
  by_cases hx : x ≤ 1
  · rw [mobiusDivisorFullHead_eq_zero hx, criticalContinuousAbel_eq_zero_le_one hx]
  have hx1 : 1 < x := lt_of_not_ge hx
  let n : ℕ := ⌊x⌋₊
  have hn : 1 ≤ n := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx1.le)
  have hlo : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hhi : x ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.lt_floor_add_one x).le
  let P : Finset ℕ := (Finset.Icc 1 (n + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2
  have hcov : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (n + 1 : ℕ) → p ∈ P := by
    intro p hp hpn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, by exact_mod_cast hpn⟩, hp⟩
  let a := mobiusDivisorHeadBlockSlope P n
  let b := mobiusDivisorHeadBlockIntercept P n
  have haff (y : ℝ) (hy : y ∈ Set.Icc (n : ℝ) (n + 1 : ℕ)) :
      mobiusDivisorFullHead y = a * Real.sqrt y + b := by
    rw [← mobiusDivisorContinuousHead_eq_fullHead P hP hcov hy.2]
    exact mobiusDivisorContinuousHead_eq_block_affine P hP n hy
  have hstep : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have h0 := haff n ⟨le_rfl, hstep⟩
  have h1 := haff (n + 1 : ℕ) ⟨hstep, le_rfl⟩
  rw [fullHead_nat_eq_criticalAbel] at h0 h1
  have hcrit := criticalContinuousAbel_between hn hstep (le_refl ((n + 1 : ℕ) : ℝ))
  have hne : Real.sqrt (n + 1 : ℕ) - Real.sqrt n ≠ 0 :=
    sub_ne_zero.mpr (Real.sqrt_lt_sqrt (Nat.cast_nonneg n)
      (by exact_mod_cast Nat.lt_succ_self n)).ne'
  have heq : (a - psiDefect n) * (Real.sqrt (n + 1 : ℕ) - Real.sqrt n) = 0 := by
    linear_combination hcrit - h1 + h0
  have ha : a = psiDefect n := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hne)
  rw [haff x ⟨hlo, hhi⟩, criticalContinuousAbel_between hn hlo hhi, h0, ha]
  ring

/-- Native full-head profile at the undamped square-energy boundary. -/
def routePNativeCriticalProfile (t : ℝ) : ℝ :=
  Real.exp (-t) * mobiusDivisorFullHead (Real.exp t)

private theorem native_source_square_bound {t : ℝ} (ht : 0 ≤ t) :
    routePSourceRay t ^ 2 ≤
      8 * routePNativeCriticalProfile t ^ 2 + 2 * (20 / 3 : ℝ) ^ 2 * Real.exp (-t) := by
  have hd := criticalAbel_routeP_difference_le ht
  rw [← mobiusDivisorFullHead_eq_criticalContinuousAbel] at hd
  have hd' : 0 < 2 * routePNativeCriticalProfile t - routePSourceRay t ∧
    2 * routePNativeCriticalProfile t - routePSourceRay t ≤
      20 / 3 * Real.exp (-t / 2) := by
    simpa only [routePNativeCriticalProfile, mul_assoc, neg_div] using hd
  have hs : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hsq : (2 * routePNativeCriticalProfile t - routePSourceRay t) ^ 2 ≤
      (20 / 3 : ℝ) ^ 2 * Real.exp (-t) := by
    rw [← hs, ← mul_pow]
    nlinarith [hd'.1, hd'.2, Real.exp_pos (-t / 2)]
  nlinarith [sq_nonneg (4 * routePNativeCriticalProfile t - routePSourceRay t)]

/-- The complete native head has no finite zero-damping square budget. -/
theorem not_integrableOn_routePNativeCriticalProfile_sq :
    ¬ IntegrableOn (fun t => routePNativeCriticalProfile t ^ 2) (Set.Ioi 0) := by
  intro hi
  apply not_integrableOn_routePSourceRay_sq
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have hmajor := (hi.const_mul 8).add (he.const_mul (2 * (20 / 3 : ℝ) ^ 2))
  have hm : AEStronglyMeasurable (fun t => routePSourceRay t ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.pow 2).aestronglyMeasurable
  apply hmajor.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact native_source_square_bound ht.le

/-- Every finite physical interval admits the native critical square. -/
theorem integrableOn_routePNativeCriticalProfile_sq_Ioc (U : ℝ) :
    IntegrableOn (fun t => routePNativeCriticalProfile t ^ 2) (Set.Ioc 0 U) := by
  let b : ℝ → ℝ := fun t =>
    (Real.exp (-t) * ((3 / 5 : ℝ) * Real.exp t * Real.sqrt (Real.exp t))) ^ 2
  have hb : Continuous b := by fun_prop
  have hm : Measurable routePNativeCriticalProfile :=
    (Real.measurable_exp.comp measurable_id.neg).mul
      (measurable_mobiusDivisorFullHead.comp Real.measurable_exp)
  apply (hb.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mono'
    (hm.pow_const 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h : |routePNativeCriticalProfile t| ≤
      Real.exp (-t) * ((3 / 5 : ℝ) * Real.exp t * Real.sqrt (Real.exp t)) := by
    rw [routePNativeCriticalProfile, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_mobiusDivisorFullHead_le _) (Real.exp_pos _).le
  dsimp only [b]
  nlinarith [abs_nonneg (routePNativeCriticalProfile t), sq_abs (routePNativeCriticalProfile t)]

/-- Unconditional positive survivor on the literal complete native head. -/
theorem routePNativeCritical_square_energy_cofinally_unbounded (B T : ℝ) :
    ∃ U : ℝ, T ≤ U ∧ B < ∫ t in (0 : ℝ)..U, routePNativeCriticalProfile t ^ 2 := by
  by_contra hn
  push Not at hn
  apply not_integrableOn_routePNativeCriticalProfile_sq
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded B 0
    integrableOn_routePNativeCriticalProfile_sq_Ioc tendsto_id
  filter_upwards [eventually_ge_atTop T] with U hU
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hn U hU

end RHTower
