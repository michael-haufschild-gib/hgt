import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set Finset Filter Topology MeasureTheory
open scoped BigOperators Interval

noncomputable section

namespace RHTower

lemma sinh_sq_le_mul_sinh_cosh (x : ℝ) :
    Real.sinh x ^ 2 ≤ x * Real.sinh x * Real.cosh x := by
  have h := abs_sinh_le_abs_mul_cosh (abs_nonneg x) (le_refl |x|)
  have hmul := mul_le_mul_of_nonneg_right h (abs_nonneg (Real.sinh x))
  calc
    Real.sinh x ^ 2 = |Real.sinh x| * |Real.sinh x| := by
      rw [← pow_two, sq_abs]
    _ ≤ (|x| * Real.cosh |x|) * |Real.sinh x| := hmul
    _ = x * Real.sinh x * Real.cosh x := by
      rw [Real.cosh_abs]
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)]
        ring
      · have hx' : x ≤ 0 := le_of_not_ge hx
        rw [abs_of_nonpos hx', abs_of_nonpos (Real.sinh_nonpos_iff.mpr hx')]
        ring

private def scalingTest (N : ℕ) (c t : ℝ) : ℝ :=
  4 * Real.sinh (c * Real.log t / Real.log N) ^ 2 / Real.log t

def primeClockScalingProfileIntegrand (c u : ℝ) : ℝ :=
  4 * Real.sinh (c * u) ^ 2 / u

def primeClockUniversalProfile (c : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, primeClockScalingProfileIntegrand c u

private def scalingMain (N : ℕ) (c : ℝ) : ℝ :=
  scalingTest N c N * Real.log N -
    ∫ t in Set.Ioc (2 : ℝ) N, deriv (scalingTest N c) t * Real.log t

private def scalingTestDeriv (N : ℕ) (c t : ℝ) : ℝ :=
  ((8 * Real.sinh (c * Real.log t / Real.log N) *
      Real.cosh (c * Real.log t / Real.log N) * (c / (Real.log N * t))) *
      Real.log t -
    4 * Real.sinh (c * Real.log t / Real.log N) ^ 2 * t⁻¹) /
    Real.log t ^ 2

private def primeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / n else 0

private def cumulativePrimeWeight (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, primeWeight n

private def mertensBound : ℝ :=
  (Real.log 4 + 4) + (8 + Mertens.mertensTail)

private theorem cumulativePrimeWeight_eq (N : ℕ) :
    cumulativePrimeWeight N =
      ∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / (n : ℝ) := by
  rw [cumulativePrimeWeight]
  simp only [primeWeight]
  rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega,
    Finset.sum_insert (by simp), Finset.sum_filter]
  simp

private theorem cumulativePrimeWeight_error_bound (N : ℕ) (hN : 1 ≤ N) :
    |cumulativePrimeWeight N - Real.log N| ≤ mertensBound := by
  rw [cumulativePrimeWeight_eq]
  exact Mertens.mertens_first_prime N hN

private theorem cumulativePrimeWeight_floor_error_bound {t : ℝ} (ht : 2 ≤ t) :
    |cumulativePrimeWeight ⌊t⌋₊ - Real.log t| ≤ mertensBound + 1 := by
  have ht0 : 0 ≤ t := by linarith
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
  have hfloorpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (Nat.zero_lt_of_lt hfloor1)
  have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hratio0 : 0 < t / (⌊t⌋₊ : ℝ) := div_pos (by linarith) hfloorpos
  have hratio2 : t / (⌊t⌋₊ : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hfloorpos]
    nlinarith
  have hlogdiff : 0 ≤ Real.log t - Real.log (⌊t⌋₊ : ℝ) := by
    exact sub_nonneg.mpr (Real.log_le_log hfloorpos hfloorle)
  have hlogdiff1 : Real.log t - Real.log (⌊t⌋₊ : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hratio0
    rw [Real.log_div (by linarith) hfloorpos.ne'] at h
    linarith
  have hprime := cumulativePrimeWeight_error_bound ⌊t⌋₊ hfloor1
  calc
    |cumulativePrimeWeight ⌊t⌋₊ - Real.log t| =
        |(cumulativePrimeWeight ⌊t⌋₊ - Real.log ⌊t⌋₊) +
          (Real.log ⌊t⌋₊ - Real.log t)| := by ring_nf
    _ ≤ |cumulativePrimeWeight ⌊t⌋₊ - Real.log ⌊t⌋₊| +
        |Real.log ⌊t⌋₊ - Real.log t| := abs_add_le _ _
    _ ≤ mertensBound + 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hfloorpos hfloorle))]
      linarith

private theorem mertensBound_nonneg : 0 ≤ mertensBound := by
  have htail : 0 ≤ Mertens.mertensTail := by
    rw [Mertens.mertensTail]
    exact tsum_nonneg fun i => by positivity
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [mertensBound]
  positivity

private theorem primeClockCutoffEnergy_eq_weighted_test (N : ℕ) (c : ℝ) :
    primeClockCutoffEnergy N (c / Real.log N) =
      ∑ n ∈ Finset.Icc 0 N, scalingTest N c n * primeWeight n := by
  rw [primeClockCutoffEnergy_eq_sinh]
  rw [show Nat.primesLE N = (Finset.Icc 0 N).filter Nat.Prime by
      ext n
      simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hnN, hp⟩
        exact ⟨⟨Nat.zero_le n, hnN⟩, hp⟩
      · rintro ⟨⟨hn0, hnN⟩, hp⟩
        exact ⟨hnN, hp⟩,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hnlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp only [hp, ↓reduceIte, primeWeight, scalingTest]
    field_simp
  · simp [hp, primeWeight]

private theorem weighted_test_sum_decomposition (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 0 N, scalingTest N c n * primeWeight n =
      scalingTest N c 2 * cumulativePrimeWeight 2 +
        ∑ n ∈ Finset.Ioc 2 N, scalingTest N c n * primeWeight n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc,
    Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  norm_num
  rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons]
  have hc2 : cumulativePrimeWeight 2 = Real.log 2 / 2 := by
    have hi : Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) := by decide
    rw [cumulativePrimeWeight, hi]
    norm_num [primeWeight]
  rw [hc2]
  norm_num [primeWeight]

private theorem hasDerivAt_scalingTest (N : ℕ) (c : ℝ) (hN : 1 < N)
    {t : ℝ} (ht : 1 < t) :
    HasDerivAt (scalingTest N c) (scalingTestDeriv N c t) t := by
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlogt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hz : HasDerivAt (fun x : ℝ => c * Real.log x / Real.log N)
      (c / (Real.log N * t)) t := by
    convert ((Real.hasDerivAt_log ht0).const_mul c).div_const (Real.log N) using 1
    field_simp
  have hs := hz.sinh
  have hsq : HasDerivAt (fun x => Real.sinh (c * Real.log x / Real.log N) ^ 2)
      (2 * Real.sinh (c * Real.log t / Real.log N) *
        Real.cosh (c * Real.log t / Real.log N) * (c / (Real.log N * t))) t := by
    convert hs.pow 2 using 1
    norm_num
    ring
  have hnum := hsq.const_mul 4
  have hden := Real.hasDerivAt_log ht0
  convert hnum.div hden hlogt using 1
  simp only [scalingTestDeriv]
  field_simp
  ring

private theorem scalingTestDeriv_continuousOn (N : ℕ) (c : ℝ) (hN : 1 < N) :
    ContinuousOn (scalingTestDeriv N c) (Set.Ioi 1) := by
  intro t ht
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlogt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hz : ContinuousAt (fun x : ℝ => c * Real.log x / Real.log N) t :=
    (continuousAt_const.mul hlog).div_const _
  have hs : ContinuousAt (fun x : ℝ => Real.sinh (c * Real.log x / Real.log N)) t :=
    Real.continuous_sinh.continuousAt.comp hz
  have hc : ContinuousAt (fun x : ℝ => Real.cosh (c * Real.log x / Real.log N)) t :=
    Real.continuous_cosh.continuousAt.comp hz
  have hden : ContinuousAt (fun x : ℝ => Real.log x ^ 2) t := hlog.pow 2
  have hinner : ContinuousAt (fun x : ℝ => Real.log N * x) t :=
    continuousAt_const.mul continuousAt_id
  have hfrac : ContinuousAt (fun x : ℝ => c / (Real.log N * x)) t :=
    continuousAt_const.div hinner (mul_ne_zero hlogN ht0)
  have hinv : ContinuousAt (fun x : ℝ => x⁻¹) t := continuousAt_inv₀ ht0
  have h8 : ContinuousAt (fun _ : ℝ => (8 : ℝ)) t := continuousAt_const
  have h4 : ContinuousAt (fun _ : ℝ => (4 : ℝ)) t := continuousAt_const
  have hleft : ContinuousAt (fun x : ℝ =>
      8 * Real.sinh (c * Real.log x / Real.log N) *
        Real.cosh (c * Real.log x / Real.log N) *
        (c / (Real.log N * x)) * Real.log x) t :=
    (((h8.mul hs).mul hc).mul hfrac).mul hlog
  have hright : ContinuousAt (fun x : ℝ =>
      4 * Real.sinh (c * Real.log x / Real.log N) ^ 2 * x⁻¹) t :=
    (h4.mul (hs.pow 2)).mul hinv
  simpa only [scalingTestDeriv] using
    ((hleft.sub hright).div hden (pow_ne_zero 2 hlogt)).continuousWithinAt

private theorem scalingTestDeriv_nonneg (N : ℕ) (c : ℝ) (hN : 1 < N)
    {t : ℝ} (ht : 1 < t) : 0 ≤ scalingTestDeriv N c t := by
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hlogt : 0 < Real.log t := Real.log_pos ht
  let x := c * Real.log t / Real.log N
  have hs := sinh_sq_le_mul_sinh_cosh x
  have hbracket : 0 ≤ 2 * x * Real.sinh x * Real.cosh x - Real.sinh x ^ 2 := by
    have hxprod : 0 ≤ x * Real.sinh x * Real.cosh x := by
      have hxs : 0 ≤ x * Real.sinh x := by
        by_cases hx : 0 ≤ x
        · exact mul_nonneg hx (Real.sinh_nonneg_iff.mpr hx)
        · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx)
            (Real.sinh_nonpos_iff.mpr (le_of_not_ge hx))
      positivity
    linarith
  have hnum : 0 ≤
      (8 * Real.sinh x * Real.cosh x * (c / (Real.log N * t))) * Real.log t -
        4 * Real.sinh x ^ 2 * t⁻¹ := by
    calc
      (8 * Real.sinh x * Real.cosh x * (c / (Real.log N * t))) * Real.log t -
          4 * Real.sinh x ^ 2 * t⁻¹ =
        (4 / t) * (2 * x * Real.sinh x * Real.cosh x - Real.sinh x ^ 2) := by
          dsimp [x]
          field_simp
          ring
      _ ≥ 0 := mul_nonneg (by positivity) hbracket
  rw [scalingTestDeriv]
  exact div_nonneg (by simpa [x] using hnum) (sq_nonneg _)

theorem continuous_primeClockScalingProfileIntegrand (c : ℝ) :
    Continuous (primeClockScalingProfileIntegrand c) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    let F : ℝ → ℝ := fun x => 4 * Real.sinh (c * x) ^ 2
    let q : ℝ → ℝ := fun x => x⁻¹ * (F (0 + x) - F 0)
    have hz : HasDerivAt (fun x : ℝ => c * x) c 0 := by
      simpa using (hasDerivAt_id (x := (0 : ℝ))).const_mul c
    have hs := hz.sinh
    have hF : HasDerivAt F 0 0 := by
      dsimp [F]
      convert (hs.pow 2).const_mul 4 using 1
      norm_num
    have hupdate : ContinuousAt (Function.update q 0 0) 0 :=
      continuousAt_update_same.mpr (by simpa [q] using hF.tendsto_slope_zero)
    convert hupdate using 1
    funext x
    by_cases hx : x = 0
    · subst x
      simp [primeClockScalingProfileIntegrand, q, F]
    · simp [hx, primeClockScalingProfileIntegrand, q, F]
      field_simp
  · unfold primeClockScalingProfileIntegrand
    fun_prop

private theorem primeClockCutoffEnergy_abel (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    primeClockCutoffEnergy N (c / Real.log N) =
      scalingTest N c N * cumulativePrimeWeight N -
        ∫ t in Set.Ioc (2 : ℝ) N,
          deriv (scalingTest N c) t * cumulativePrimeWeight ⌊t⌋₊ := by
  have hN' : 1 < N := lt_of_lt_of_le one_lt_two hN
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) N,
      DifferentiableAt ℝ (scalingTest N c) t := by
    intro t ht
    exact (hasDerivAt_scalingTest N c hN' (lt_of_lt_of_le one_lt_two ht.1)).differentiableAt
  have hcontExplicit : ContinuousOn (scalingTestDeriv N c) (Set.Icc (2 : ℝ) N) :=
    (scalingTestDeriv_continuousOn N c hN').mono (by
      intro t ht
      exact lt_of_lt_of_le one_lt_two ht.1)
  have hcontDeriv : ContinuousOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontExplicit.congr (fun t ht =>
      (hasDerivAt_scalingTest N c hN' (lt_of_lt_of_le one_lt_two ht.1)).deriv)
  have hint : IntegrableOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontDeriv.integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul' primeWeight hN hdiff hint
  rw [primeClockCutoffEnergy_eq_weighted_test N c,
    weighted_test_sum_decomposition N c hN, hab]
  simp only [cumulativePrimeWeight]
  ring_nf

private theorem primeClockCutoffEnergy_sub_scalingMain (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    primeClockCutoffEnergy N (c / Real.log N) - scalingMain N c =
      scalingTest N c N * (cumulativePrimeWeight N - Real.log N) -
        ∫ t in Set.Ioc (2 : ℝ) N,
          deriv (scalingTest N c) t *
            (cumulativePrimeWeight ⌊t⌋₊ - Real.log t) := by
  have hN' : 1 < N := lt_of_lt_of_le one_lt_two hN
  have hcontExplicit : ContinuousOn (scalingTestDeriv N c) (Set.Icc (2 : ℝ) N) :=
    (scalingTestDeriv_continuousOn N c hN').mono (by
      intro t ht
      exact lt_of_lt_of_le one_lt_two ht.1)
  have hcontDeriv : ContinuousOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontExplicit.congr (fun t ht =>
      (hasDerivAt_scalingTest N c hN' (lt_of_lt_of_le one_lt_two ht.1)).deriv)
  have hint : IntegrableOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontDeriv.integrableOn_Icc
  have hfloor : IntegrableOn (fun t : ℝ =>
      deriv (scalingTest N c) t * cumulativePrimeWeight ⌊t⌋₊)
      (Set.Icc (2 : ℝ) N) := by
    simpa only [cumulativePrimeWeight] using
      (integrableOn_mul_sum_Icc primeWeight (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hint)
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc (2 : ℝ) N) :=
    Real.continuousOn_log.mono (by
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [ht.1])
  have hlog : IntegrableOn (fun t : ℝ =>
      deriv (scalingTest N c) t * Real.log t) (Set.Icc (2 : ℝ) N) :=
    (hcontDeriv.mul hlogcont).integrableOn_Icc
  have herr : IntegrableOn (fun t : ℝ =>
      deriv (scalingTest N c) t *
        (cumulativePrimeWeight ⌊t⌋₊ - Real.log t)) (Set.Icc (2 : ℝ) N) := by
    convert hfloor.sub hlog using 1
    ext t
    simp only [Pi.sub_apply]
    ring
  have hlog' := hlog.mono_set Set.Ioc_subset_Icc_self
  have herr' := herr.mono_set Set.Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Set.Ioc (2 : ℝ) N,
        deriv (scalingTest N c) t * cumulativePrimeWeight ⌊t⌋₊) =
      (∫ t in Set.Ioc (2 : ℝ) N,
        deriv (scalingTest N c) t * Real.log t) +
      ∫ t in Set.Ioc (2 : ℝ) N,
        deriv (scalingTest N c) t *
          (cumulativePrimeWeight ⌊t⌋₊ - Real.log t) := by
    rw [← MeasureTheory.integral_add hlog' herr']
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  rw [primeClockCutoffEnergy_abel N c hN, scalingMain, hsplit]
  ring

private theorem primeClockCutoffEnergy_sub_scalingMain_bound
    (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    |primeClockCutoffEnergy N (c / Real.log N) - scalingMain N c| ≤
      2 * (mertensBound + 1) * scalingTest N c N := by
  let D : ℝ := mertensBound + 1
  have hD : 0 ≤ D := by dsimp [D]; linarith [mertensBound_nonneg]
  have hN' : 1 < N := lt_of_lt_of_le one_lt_two hN
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) N,
      DifferentiableAt ℝ (scalingTest N c) t := by
    intro t ht
    exact (hasDerivAt_scalingTest N c hN' (lt_of_lt_of_le one_lt_two ht.1)).differentiableAt
  have hcontExplicit : ContinuousOn (scalingTestDeriv N c) (Set.Icc (2 : ℝ) N) :=
    (scalingTestDeriv_continuousOn N c hN').mono (by
      intro t ht
      exact lt_of_lt_of_le one_lt_two ht.1)
  have hcontDeriv : ContinuousOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontExplicit.congr (fun t ht =>
      (hasDerivAt_scalingTest N c hN' (lt_of_lt_of_le one_lt_two ht.1)).deriv)
  have hint : IntegrableOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontDeriv.integrableOn_Icc
  have hintIoc := hint.mono_set Set.Ioc_subset_Icc_self
  have hdom : IntegrableOn (fun t : ℝ => D * deriv (scalingTest N c) t)
      (Set.Ioc (2 : ℝ) N) := hintIoc.const_mul D
  have hderivNonneg : ∀ t ∈ Set.Ioc (2 : ℝ) N,
      0 ≤ deriv (scalingTest N c) t := by
    intro t ht
    rw [(hasDerivAt_scalingTest N c hN' (by linarith [ht.1])).deriv]
    exact scalingTestDeriv_nonneg N c hN' (by linarith [ht.1])
  have herrIntegral :
      |∫ t in Set.Ioc (2 : ℝ) N,
          deriv (scalingTest N c) t *
            (cumulativePrimeWeight ⌊t⌋₊ - Real.log t)| ≤
        D * (scalingTest N c N - scalingTest N c 2) := by
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le
      (f := fun t : ℝ => deriv (scalingTest N c) t *
        (cumulativePrimeWeight ⌊t⌋₊ - Real.log t))
      (g := fun t : ℝ => D * deriv (scalingTest N c) t)
      (μ := volume.restrict (Set.Ioc (2 : ℝ) N)) hdom (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hderivNonneg t ht)]
      simpa [D, mul_comm] using mul_le_mul_of_nonneg_left
          (cumulativePrimeWeight_floor_error_bound (le_of_lt ht.1))
          (hderivNonneg t ht))
    rw [MeasureTheory.integral_const_mul] at hnorm
    have hdiffU : ∀ t ∈ [[(2 : ℝ), N]],
        DifferentiableAt ℝ (scalingTest N c) t := by
      rw [Set.uIcc_of_le (by exact_mod_cast hN)]
      exact hdiff
    have hcontU : ContinuousOn (deriv (scalingTest N c)) [[(2 : ℝ), N]] := by
      rw [Set.uIcc_of_le (by exact_mod_cast hN)]
      exact hcontDeriv
    have hftc := intervalIntegral.integral_deriv_eq_sub hdiffU hcontU.intervalIntegrable
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hN)] at hftc
    rw [hftc] at hnorm
    simpa [D, Real.norm_eq_abs] using hnorm
  have hendpoint :
      |scalingTest N c N * (cumulativePrimeWeight N - Real.log N)| ≤
        D * scalingTest N c N := by
    have htest : 0 ≤ scalingTest N c N := by
      rw [scalingTest]
      positivity
    rw [abs_mul, abs_of_nonneg htest, mul_comm]
    apply mul_le_mul_of_nonneg_right _ htest
    dsimp [D]
    linarith [cumulativePrimeWeight_error_bound N (by omega)]
  have htest2 : 0 ≤ scalingTest N c 2 := by
    rw [scalingTest]
    positivity
  rw [primeClockCutoffEnergy_sub_scalingMain N c hN]
  calc
    |scalingTest N c ↑N * (cumulativePrimeWeight N - Real.log ↑N) -
        ∫ t in Set.Ioc (2 : ℝ) ↑N,
          deriv (scalingTest N c) t *
            (cumulativePrimeWeight ⌊t⌋₊ - Real.log t)| ≤
      |scalingTest N c ↑N * (cumulativePrimeWeight N - Real.log ↑N)| +
        |∫ t in Set.Ioc (2 : ℝ) ↑N,
          deriv (scalingTest N c) t *
            (cumulativePrimeWeight ⌊t⌋₊ - Real.log t)| := abs_sub _ _
    _ ≤ D * scalingTest N c N +
        D * (scalingTest N c N - scalingTest N c 2) := add_le_add hendpoint herrIntegral
    _ ≤ 2 * D * scalingTest N c N := by nlinarith
    _ = 2 * (mertensBound + 1) * scalingTest N c N := by rfl

private theorem tendsto_scalingTest_self_zero (c : ℝ) :
    Tendsto (fun N : ℕ => scalingTest N c N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun N : ℕ =>
      (4 * Real.sinh c ^ 2) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply hzero.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlogne : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [scalingTest]
  congr 2
  field_simp

private theorem tendsto_primeClockCutoffEnergy_sub_scalingMain_zero (c : ℝ) :
    Tendsto (fun N : ℕ =>
      primeClockCutoffEnergy N (c / Real.log N) - scalingMain N c)
      atTop (𝓝 0) := by
  have hbound : Tendsto (fun N : ℕ =>
      2 * (mertensBound + 1) * scalingTest N c N) atTop (𝓝 0) := by
    simpa using (tendsto_scalingTest_self_zero c).const_mul
      (2 * (mertensBound + 1))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _)
      (show ∀ᶠ N : ℕ in atTop,
        |primeClockCutoffEnergy N (c / Real.log N) - scalingMain N c| ≤
          2 * (mertensBound + 1) * scalingTest N c N by
        filter_upwards [eventually_ge_atTop 2] with N hN
        exact primeClockCutoffEnergy_sub_scalingMain_bound N c hN)
      hbound

private theorem scalingMain_eq_boundary_add_integral (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    scalingMain N c =
      scalingTest N c 2 * Real.log 2 +
        ∫ t in (2 : ℝ)..N, scalingTest N c t / t := by
  have hN' : 1 < N := lt_of_lt_of_le one_lt_two hN
  have hprodDeriv : ∀ t ∈ [[(2 : ℝ), N]],
      HasDerivAt (fun x => scalingTest N c x * Real.log x)
        (deriv (scalingTest N c) t * Real.log t + scalingTest N c t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by exact_mod_cast hN)] at ht
    have ht1 : 1 < t := lt_of_lt_of_le one_lt_two ht.1
    have ht0 : t ≠ 0 := by positivity
    have hf := hasDerivAt_scalingTest N c hN' ht1
    convert hf.mul (Real.hasDerivAt_log ht0) using 1
    rw [hf.deriv]
    ring
  have hcontExplicit : ContinuousOn (scalingTestDeriv N c) (Set.Icc (2 : ℝ) N) :=
    (scalingTestDeriv_continuousOn N c hN').mono (by
      intro t ht
      exact lt_of_lt_of_le one_lt_two ht.1)
  have hcontDeriv : ContinuousOn (deriv (scalingTest N c)) (Set.Icc (2 : ℝ) N) :=
    hcontExplicit.congr (fun t ht =>
      (hasDerivAt_scalingTest N c hN' (lt_of_lt_of_le one_lt_two ht.1)).deriv)
  have hcontTest : ContinuousOn (scalingTest N c) (Set.Icc (2 : ℝ) N) := by
    intro t ht
    exact (hasDerivAt_scalingTest N c hN'
      (lt_of_lt_of_le one_lt_two ht.1)).continuousAt.continuousWithinAt
  have hcontLog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc (2 : ℝ) N) :=
    Real.continuousOn_log.mono (by
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [ht.1])
  have hcontInv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc (2 : ℝ) N) := by
    intro t ht
    exact (continuousAt_inv₀ (by linarith [ht.1])).continuousWithinAt
  have hcontSum : ContinuousOn (fun t : ℝ =>
      deriv (scalingTest N c) t * Real.log t + scalingTest N c t / t)
      (Set.Icc (2 : ℝ) N) := by
    simpa only [div_eq_mul_inv] using (hcontDeriv.mul hcontLog).add (hcontTest.mul hcontInv)
  have hcontSumU : ContinuousOn (fun t : ℝ =>
      deriv (scalingTest N c) t * Real.log t + scalingTest N c t / t)
      [[(2 : ℝ), N]] := by
    rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    exact hcontSum
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprodDeriv
    hcontSumU.intervalIntegrable
  have hlogProdInt : IntervalIntegrable (fun t : ℝ =>
      deriv (scalingTest N c) t * Real.log t) volume 2 N := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    exact hcontDeriv.mul hcontLog
  have htestInvInt : IntervalIntegrable (fun t : ℝ =>
      scalingTest N c t / t) volume 2 N := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    simpa only [div_eq_mul_inv] using hcontTest.mul hcontInv
  rw [intervalIntegral.integral_add
    hlogProdInt htestInvInt] at hftc
  rw [scalingMain, ← intervalIntegral.integral_of_le (by exact_mod_cast hN)]
  linarith

private theorem integral_scalingTest_div_eq_profile_interval
    (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    (∫ t in (2 : ℝ)..N, scalingTest N c t / t) =
      ∫ u in Real.log 2 / Real.log N..1, primeClockScalingProfileIntegrand c u := by
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hN))
  let f : ℝ → ℝ := fun t => Real.log t / Real.log N
  let f' : ℝ → ℝ := fun t => 1 / (Real.log N * t)
  have hf : ∀ t ∈ [[(2 : ℝ), N]], HasDerivAt f (f' t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by exact_mod_cast hN)] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    dsimp [f, f']
    convert (Real.hasDerivAt_log ht0).div_const (Real.log N) using 1
    field_simp
  have hf' : ContinuousOn f' [[(2 : ℝ), N]] := by
    rw [Set.uIcc_of_le (by exact_mod_cast hN)]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    dsimp [f']
    exact (continuousAt_const.div
      (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero hlogN.ne' ht0)).continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := (2 : ℝ)) (b := (N : ℝ))
    (f := f) (f' := f') (g := primeClockScalingProfileIntegrand c)
    hf hf' (continuous_primeClockScalingProfileIntegrand c)
  calc
    (∫ t in (2 : ℝ)..N, scalingTest N c t / t) =
        ∫ t in (2 : ℝ)..N, (primeClockScalingProfileIntegrand c ∘ f) t * f' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by exact_mod_cast hN)] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogt : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      dsimp [scalingTest, primeClockScalingProfileIntegrand, f, f', Function.comp_apply]
      field_simp
    _ = ∫ u in f 2..f N, primeClockScalingProfileIntegrand c u := hsubst
    _ = ∫ u in Real.log 2 / Real.log N..1, primeClockScalingProfileIntegrand c u := by
      have hlogNne : Real.log (N : ℝ) ≠ 0 := hlogN.ne'
      simp only [f]
      rw [div_self hlogNne]

private theorem tendsto_profile_interval (c : ℝ) :
    Tendsto (fun N : ℕ =>
      ∫ u in Real.log 2 / Real.log N..1, primeClockScalingProfileIntegrand c u)
      atTop (𝓝 (primeClockUniversalProfile c)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  let P : ℝ → ℝ := fun a => ∫ u in (0 : ℝ)..a, primeClockScalingProfileIntegrand c u
  have hP : Continuous P :=
    (intervalIntegral.differentiable_integral_of_continuous
      (a := (0 : ℝ)) (continuous_primeClockScalingProfileIntegrand c)).continuous
  have hPzero : P 0 = 0 := by simp [P]
  have hPa : Tendsto (fun N : ℕ => P (Real.log 2 / Real.log N)) atTop (𝓝 0) := by
    simpa [hPzero] using hP.continuousAt.tendsto.comp ha
  have hrewrite : ∀ N : ℕ,
      (∫ u in Real.log 2 / Real.log N..1, primeClockScalingProfileIntegrand c u) =
        primeClockUniversalProfile c - P (Real.log 2 / Real.log N) := by
    intro N
    dsimp [primeClockUniversalProfile, P]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (f := primeClockScalingProfileIntegrand c)
      (μ := volume)
      (a := (0 : ℝ)) (b := Real.log 2 / Real.log N) (c := (1 : ℝ))
      ((continuous_primeClockScalingProfileIntegrand c).intervalIntegrable _ _)
      ((continuous_primeClockScalingProfileIntegrand c).intervalIntegrable _ _)
    linarith
  have ht := (tendsto_const_nhds.sub hPa).congr'
    (Eventually.of_forall fun N => (hrewrite N).symm)
  simpa only [sub_zero] using ht

private theorem tendsto_scalingMain_primeClockUniversalProfile (c : ℝ) :
    Tendsto (fun N : ℕ => scalingMain N c) atTop (𝓝 (primeClockUniversalProfile c)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have harg : Tendsto (fun N : ℕ => c * (Real.log 2 / Real.log N)) atTop (𝓝 0) := by
    simpa using ha.const_mul c
  have hboundary0 : Tendsto (fun N : ℕ =>
      4 * Real.sinh (c * (Real.log 2 / Real.log N)) ^ 2) atTop (𝓝 0) := by
    have hs := Real.continuous_sinh.continuousAt.tendsto.comp harg
    simpa using (hs.pow 2).const_mul 4
  have hboundary0' : Tendsto (fun N : ℕ =>
      scalingTest N c 2 * Real.log 2) atTop (𝓝 0) := by
    apply hboundary0.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [scalingTest]
    field_simp
  have hsum := hboundary0'.add (tendsto_profile_interval c)
  have ht := hsum.congr' (show ∀ᶠ N : ℕ in atTop,
      scalingTest N c 2 * Real.log 2 +
          (∫ u in Real.log 2 / Real.log N..1, primeClockScalingProfileIntegrand c u) =
        scalingMain N c by
      filter_upwards [eventually_ge_atTop 2] with N hN
      rw [scalingMain_eq_boundary_add_integral N c hN,
        integral_scalingTest_div_eq_profile_interval N c hN])
  simpa only [zero_add] using ht

/-- Fixed critical-window crossover: at `ε = c / log N`, the prime-clock energy converges to the
universal nonlinear profile `4 ∫₀¹ sinh²(cu)/u du`. -/
theorem tendsto_primeClockCutoffEnergy_critical_profile (c : ℝ) :
    Tendsto (fun N : ℕ =>
      primeClockCutoffEnergy N (c / Real.log N))
      atTop (𝓝 (primeClockUniversalProfile c)) := by
  have hdiff := tendsto_primeClockCutoffEnergy_sub_scalingMain_zero c
  have hmain := tendsto_scalingMain_primeClockUniversalProfile c
  have hsum := hdiff.add hmain
  have ht := hsum.congr' (Eventually.of_forall fun N => by ring)
  simpa only [zero_add] using ht

lemma abs_sinh_sub_le_cosh_mul_abs_sub {x y C : ℝ}
    (hC : 0 ≤ C) (hx : |x| ≤ C) (hy : |y| ≤ C) :
    |Real.sinh x - Real.sinh y| ≤ Real.cosh C * |x - y| := by
  have hordered : ∀ {a b : ℝ}, |a| ≤ C → |b| ≤ C → a ≤ b →
      |Real.sinh a - Real.sinh b| ≤ Real.cosh C * |a - b| := by
    intro a b ha hb hab
    have hderiv : ∀ z ∈ Set.Icc a b,
        HasDerivWithinAt Real.sinh (Real.cosh z) (Set.Icc a b) z := by
      intro z hz
      exact (Real.hasDerivAt_sinh z).hasDerivWithinAt
    have hbound : ∀ z ∈ Set.Ico a b, ‖Real.cosh z‖ ≤ Real.cosh C := by
      intro z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos z)]
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg hC]
      exact abs_le.mpr ⟨(abs_le.mp ha).1.trans hz.1, hz.2.le.trans (abs_le.mp hb).2⟩
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b
      (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)
    rw [Real.norm_eq_abs, abs_sub_comm] at hmv
    simpa [abs_of_nonpos (sub_nonpos.mpr hab)] using hmv
  by_cases hxy : x ≤ y
  · exact hordered hx hy hxy
  · have h := hordered hy hx (le_of_not_ge hxy)
    simpa [abs_sub_comm] using h

lemma primeClockCutoffEnergy_scaled_lipschitz
    (N : ℕ) (c₁ c₂ C : ℝ) (hN : 2 ≤ N) (hC : 0 ≤ C)
    (hc₁ : |c₁| ≤ C) (hc₂ : |c₂| ≤ C) :
    |primeClockCutoffEnergy N (c₁ / Real.log N) -
        primeClockCutoffEnergy N (c₂ / Real.log N)| ≤
      8 * C * Real.cosh C ^ 2 * |c₁ - c₂| *
        (primeClockSusceptibility N / Real.log N ^ 2) := by
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [primeClockCutoffEnergy_eq_sinh, primeClockCutoffEnergy_eq_sinh,
    ← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ Nat.primesLE N,
        (4 * Real.sinh (c₁ / Real.log ↑N * Real.log ↑p) ^ 2 / ↑p -
          4 * Real.sinh (c₂ / Real.log ↑N * Real.log ↑p) ^ 2 / ↑p)| ≤
      ∑ p ∈ Nat.primesLE N,
        |4 * Real.sinh (c₁ / Real.log ↑N * Real.log ↑p) ^ 2 / ↑p -
          4 * Real.sinh (c₂ / Real.log ↑N * Real.log ↑p) ^ 2 / ↑p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesLE N,
        (8 * C * Real.cosh C ^ 2 * |c₁ - c₂|) *
          (Real.log p ^ 2 / (Real.log N ^ 2 * p)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := Nat.mem_primesLE.mp hp
      have hpprime : p.Prime := hpdata.2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
      have hlogp_le : Real.log p ≤ Real.log N :=
        Real.log_le_log hp0 (by exact_mod_cast hpdata.1)
      let u : ℝ := Real.log p / Real.log N
      have hu0 : 0 ≤ u := div_nonneg hlogp0 hlogN.le
      have hu1 : u ≤ 1 := (div_le_one hlogN).mpr hlogp_le
      let x : ℝ := c₁ * u
      let y : ℝ := c₂ * u
      have hx : |x| ≤ C := by
        dsimp [x]
        rw [abs_mul, abs_of_nonneg hu0]
        exact (mul_le_mul_of_nonneg_left hu1 (abs_nonneg c₁)).trans (by simpa using hc₁)
      have hy : |y| ≤ C := by
        dsimp [y]
        rw [abs_mul, abs_of_nonneg hu0]
        exact (mul_le_mul_of_nonneg_left hu1 (abs_nonneg c₂)).trans (by simpa using hc₂)
      have hdiff := abs_sinh_sub_le_cosh_mul_abs_sub hC hx hy
      have hsx := abs_sinh_le_abs_mul_cosh hC hx
      have hsy := abs_sinh_le_abs_mul_cosh hC hy
      have hsum : |Real.sinh x + Real.sinh y| ≤ 2 * C * u * Real.cosh C := by
        calc
          |Real.sinh x + Real.sinh y| ≤ |Real.sinh x| + |Real.sinh y| := abs_add_le _ _
          _ ≤ |x| * Real.cosh C + |y| * Real.cosh C := add_le_add hsx hsy
          _ ≤ C * u * Real.cosh C + C * u * Real.cosh C := by
            gcongr
            · dsimp [x]
              rw [abs_mul, abs_of_nonneg hu0]
              exact mul_le_mul_of_nonneg_right hc₁ hu0
            · dsimp [y]
              rw [abs_mul, abs_of_nonneg hu0]
              exact mul_le_mul_of_nonneg_right hc₂ hu0
          _ = 2 * C * u * Real.cosh C := by ring
      have hdiff' : |Real.sinh x - Real.sinh y| ≤
          Real.cosh C * |c₁ - c₂| * u := by
        calc
          |Real.sinh x - Real.sinh y| ≤ Real.cosh C * |x - y| := hdiff
          _ = Real.cosh C * |c₁ - c₂| * u := by
            dsimp [x, y]
            rw [← sub_mul, abs_mul, abs_of_nonneg hu0]
            ring
      have hprod : |Real.sinh x ^ 2 - Real.sinh y ^ 2| ≤
          2 * C * Real.cosh C ^ 2 * |c₁ - c₂| * u ^ 2 := by
        rw [sq_sub_sq, abs_mul]
        calc
          |Real.sinh x + Real.sinh y| * |Real.sinh x - Real.sinh y| ≤
              (2 * C * u * Real.cosh C) *
                (Real.cosh C * |c₁ - c₂| * u) :=
            mul_le_mul hsum hdiff' (abs_nonneg _) (by positivity)
          _ = 2 * C * Real.cosh C ^ 2 * |c₁ - c₂| * u ^ 2 := by ring
      have hxy₁ : c₁ / Real.log N * Real.log p = x := by
        dsimp [x, u]
        ring
      have hxy₂ : c₂ / Real.log N * Real.log p = y := by
        dsimp [y, u]
        ring
      rw [hxy₁, hxy₂, div_eq_mul_inv, div_eq_mul_inv, ← sub_mul, abs_mul,
        abs_inv, abs_of_pos hp0]
      rw [show 4 * Real.sinh x ^ 2 - 4 * Real.sinh y ^ 2 =
          4 * (Real.sinh x ^ 2 - Real.sinh y ^ 2) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      calc
        4 * |Real.sinh x ^ 2 - Real.sinh y ^ 2| * (p : ℝ)⁻¹ ≤
            4 * (2 * C * Real.cosh C ^ 2 * |c₁ - c₂| * u ^ 2) * (p : ℝ)⁻¹ := by
          gcongr
        _ = (8 * C * Real.cosh C ^ 2 * |c₁ - c₂|) *
            (Real.log p ^ 2 / (Real.log N ^ 2 * p)) := by
          dsimp [u]
          field_simp
          ring
    _ = 8 * C * Real.cosh C ^ 2 * |c₁ - c₂| *
        (primeClockSusceptibility N / Real.log N ^ 2) := by
      rw [primeClockSusceptibility]
      let K : ℝ := 8 * C * Real.cosh C ^ 2 * |c₁ - c₂|
      calc
        ∑ p ∈ Nat.primesLE N,
            K * (Real.log p ^ 2 / (Real.log N ^ 2 * p)) =
          ∑ p ∈ Nat.primesLE N,
            (K * (Real.log p ^ 2 / p)) * (Real.log N ^ 2)⁻¹ := by
            apply Finset.sum_congr rfl
            intro p hp
            field_simp
        _ = (∑ p ∈ Nat.primesLE N, K * (Real.log p ^ 2 / p)) *
            (Real.log N ^ 2)⁻¹ := by rw [Finset.sum_mul]
        _ = (K * ∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p) *
            (Real.log N ^ 2)⁻¹ := by rw [Finset.mul_sum]
        _ = K * ((∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p) /
            Real.log N ^ 2) := by rw [div_eq_mul_inv]; ring
        _ = 8 * C * Real.cosh C ^ 2 * |c₁ - c₂| *
            ((∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p) /
              Real.log N ^ 2) := by rfl

/-- Moving critical-window crossover: if the scaled horizontal coordinate `c_N` tends to `c`,
then the prime-clock energy at `ε_N = c_N / log N` tends to the same universal profile. -/
theorem tendsto_primeClockCutoffEnergy_critical_profile_of_tendsto
    (cN : ℕ → ℝ) (c : ℝ) (hcN : Tendsto cN atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => primeClockCutoffEnergy N (cN N / Real.log N))
      atTop (𝓝 (primeClockUniversalProfile c)) := by
  let C : ℝ := |c| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcC : |c| ≤ C := by dsimp [C]; linarith
  have hcNbound : ∀ᶠ N : ℕ in atTop, |cN N| ≤ C := by
    have hnear := (Metric.tendsto_atTop.mp hcN) 1 zero_lt_one
    rcases hnear with ⟨N₀, hN₀⟩
    filter_upwards [eventually_ge_atTop N₀] with N hNN₀
    have hd := (hN₀ N hNN₀).le
    rw [Real.dist_eq] at hd
    dsimp [C]
    calc
      |cN N| ≤ |cN N - c| + |c| := by
        have := abs_add_le (cN N - c) c
        simpa only [sub_add_cancel] using this
      _ ≤ |c| + 1 := by linarith
  have habsSub : Tendsto (fun N : ℕ => |cN N - c|) atTop (𝓝 0) := by
    have hsub : Tendsto (fun N : ℕ => cN N - c) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
      simpa using hcN.sub hconst
    simpa using hsub.abs
  have hratio := tendsto_primeClockSusceptibility_div_log_sq
  have hupper : Tendsto (fun N : ℕ =>
      (8 * C * Real.cosh C ^ 2) *
        (|cN N - c| * (primeClockSusceptibility N / Real.log N ^ 2)))
      atTop (𝓝 0) := by
    have hprod := habsSub.mul hratio
    simpa using hprod.const_mul (8 * C * Real.cosh C ^ 2)
  have hdiff : Tendsto (fun N : ℕ =>
      primeClockCutoffEnergy N (cN N / Real.log N) -
        primeClockCutoffEnergy N (c / Real.log N)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero, Real.norm_eq_abs] using
      squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _)
        (show ∀ᶠ N : ℕ in atTop,
          |primeClockCutoffEnergy N (cN N / Real.log N) -
            primeClockCutoffEnergy N (c / Real.log N)| ≤
              8 * C * Real.cosh C ^ 2 * |cN N - c| *
                (primeClockSusceptibility N / Real.log N ^ 2) by
          filter_upwards [eventually_ge_atTop 2, hcNbound] with N hN hcNb
          exact primeClockCutoffEnergy_scaled_lipschitz N (cN N) c C hN hC hcNb hcC)
        (by simpa [mul_assoc] using hupper)
  have hfixed := tendsto_primeClockCutoffEnergy_critical_profile c
  have hsum := hdiff.add hfixed
  have ht := hsum.congr' (Eventually.of_forall fun N => by ring)
  simpa only [zero_add] using ht


end RHTower
