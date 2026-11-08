import GaloisForLFunctions.ArithmeticPositiveDuality.AnIntegerNormBeurlingOneOff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!+# Weighted prime counts under quantile discretization and integer rounding

Quantile discretization changes the logarithmically weighted prime count by at most the
logarithmic horizon. Upward integer rounding adds a nonnegative drift smaller than every
positive power of the norm horizon. Both statements concern the literal rounded prime labels,
including their multiplicities.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

open DiscreteOneOff

/-- The weighted count of the quantile primes up to logarithmic horizon `t`. -/
def discretePrimeTheta (P : Params) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range ⌊P.W t⌋₊, P.atom k

/-- The logarithmic weight gained by rounding the prime labels below `t`. -/
def roundingDrift (P : Params) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range ⌊P.W t⌋₊, (roundedAtom P k - P.atom k)

/-- The Chebyshev prime sum for the integer-norm Euler product. -/
def integerPrimeTheta (P : Params) (n : ℕ) : ℝ :=
  ∑' k, if primeNorm P k ≤ n then Real.log (primeNorm P k) else 0

/-- The weighted prime count of the continuous density. -/
def continuousPrimeTheta (P : Params) (t : ℝ) : ℝ :=
  ∫ u in Ioc 0 t, u * P.w u

theorem primeNorm_le_iff_atom_le_log (P : Params) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    primeNorm P k ≤ n ↔ P.atom k ≤ Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [primeNorm, Nat.ceil_le, Real.le_log_iff_exp_le hn0]

/-- At an integer horizon, rounding changes weights but not the included labels. -/
theorem integerPrimeTheta_eq_discrete_add_drift (P : Params) {n : ℕ} (hn : 1 ≤ n) :
    integerPrimeTheta P n =
      discretePrimeTheta P (Real.log n) + roundingDrift P (Real.log n) := by
  have ht : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hmem (k : ℕ) : primeNorm P k ≤ n ↔ k ∈ Finset.range ⌊P.W (Real.log n)⌋₊ := by
    rw [primeNorm_le_iff_atom_le_log P hn, Finset.mem_range,
      P.atom_le_iff_lt_floor k ht]
  rw [integerPrimeTheta, tsum_eq_sum (s := Finset.range ⌊P.W (Real.log n)⌋₊)
    (fun k hk => if_neg (mt (hmem k).mp hk))]
  simp only [discretePrimeTheta, roundingDrift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_pos ((hmem k).mpr hk)]
  change roundedAtom P k = P.atom k + (roundedAtom P k - P.atom k)
  ring

theorem roundingDrift_nonneg (P : Params) (t : ℝ) : 0 ≤ roundingDrift P t :=
  Finset.sum_nonneg fun k _ => sub_nonneg.mpr (atom_le_roundedAtom P k)

/-- The cumulative rounding drift is controlled by a convergent prime sum. -/
theorem roundingDrift_le (P : Params) {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    roundingDrift P t ≤
      Real.exp (ε * t) * ∑' k, Real.exp (-((1 + ε) * P.atom k)) := by
  have hsum := P.summable_exp_atom (a := 1 + ε) (by linarith only [hε])
  calc
    roundingDrift P t ≤ ∑ k ∈ Finset.range ⌊P.W t⌋₊, Real.exp (-(P.atom k)) := by
      apply Finset.sum_le_sum
      intro k _
      have h := roundedAtom_le P k
      linarith only [h]
    _ ≤ ∑ k ∈ Finset.range ⌊P.W t⌋₊,
        Real.exp (ε * t) * Real.exp (-((1 + ε) * P.atom k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkt := (P.atom_le_iff_lt_floor k ht).mpr (Finset.mem_range.mp hk)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hε.le (sub_nonneg.mpr hkt)]
    _ = Real.exp (ε * t) *
        ∑ k ∈ Finset.range ⌊P.W t⌋₊, Real.exp (-((1 + ε) * P.atom k)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (ε * t) * ∑' k, Real.exp (-((1 + ε) * P.atom k)) :=
      mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum _ (fun k _ => (Real.exp_pos _).le)) (Real.exp_pos _).le

private theorem atomCount_integrable (P : Params) (t : ℝ) :
    IntegrableOn (atomCount P.atom) (Ioc 0 t) := by
  have hmono : Monotone (atomCount P.atom) := by
    intro a b hab
    rw [P.atomCount_eq, P.atomCount_eq]
    exact_mod_cast Nat.floor_le_floor (P.W_le_W hab)
  exact hmono.intervalIntegrable.1

private theorem integral_atomCount (P : Params) {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in Ioc 0 t, atomCount P.atom u =
      t * (⌊P.W t⌋₊ : ℝ) - discretePrimeTheta P t := by
  let S := Finset.range ⌊P.W t⌋₊
  have hfun (u : ℝ) (hu : u ∈ Ioc 0 t) :
      atomCount P.atom u = ∑ k ∈ S, (Ici (P.atom k)).indicator (fun _ => (1 : ℝ)) u := by
    rw [atomCount, tsum_eq_sum (s := S) (fun k hk => ?_)]
    · apply Finset.sum_congr rfl
      intro k _
      simp only [Set.indicator_apply, mem_Ici]
    · apply if_neg
      intro hku
      exact hk (Finset.mem_range.mpr ((P.atom_le_iff_lt_floor k ht).mp (hku.trans hu.2)))
  have hint (k : ℕ) : IntegrableOn
      ((Ici (P.atom k)).indicator (fun _ => (1 : ℝ))) (Ioc 0 t) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ici
  calc
    (∫ u in Ioc 0 t, atomCount P.atom u) =
        ∫ u in Ioc 0 t, ∑ k ∈ S, (Ici (P.atom k)).indicator (fun _ => (1 : ℝ)) u :=
      setIntegral_congr_fun measurableSet_Ioc hfun
    _ = ∑ k ∈ S, ∫ u in Ioc 0 t, (Ici (P.atom k)).indicator (fun _ => (1 : ℝ)) u :=
      integral_finsetSum S (fun k _ => hint k)
    _ = ∑ k ∈ S, (t - P.atom k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkt := (P.atom_le_iff_lt_floor k ht).mpr (Finset.mem_range.mp hk)
      rw [setIntegral_indicator measurableSet_Ici]
      have hset : Ioc 0 t ∩ Ici (P.atom k) = Icc (P.atom k) t := by
        ext u
        simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨⟨_, hut⟩, hku⟩
          exact ⟨hku, hut⟩
        · rintro ⟨hku, hut⟩
          exact ⟨⟨(P.atom_pos k).trans_le hku, hut⟩, hku⟩
      rw [hset, integral_const, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, ENNReal.toReal_ofReal
        (sub_nonneg.mpr hkt), smul_eq_mul, mul_one]
    _ = t * (⌊P.W t⌋₊ : ℝ) - discretePrimeTheta P t := by
      rw [Finset.sum_sub_distrib]
      simp only [S, Finset.sum_const, Finset.card_range, nsmul_eq_mul, discretePrimeTheta]
      ring

private theorem hasDerivAt_W (P : Params) {x : ℝ} (hx : 0 < x) :
    HasDerivAt P.W (P.wt x) x := by
  have hc : ContinuousAt P.w x := by
    unfold Params.w RHTower.BeurlingOverRegularIntegers.primeDensity
      RHTower.BeurlingOverRegularIntegers.primeNumerator
    fun_prop (disch := exact hx.ne')
  have heq : P.wt =ᶠ[𝓝 x] P.w := by
    filter_upwards [Ioi_mem_nhds hx] with u hu
    exact Set.indicator_of_mem hu _
  have hmeas : Measurable P.wt := P.measurable_w.indicator measurableSet_Ioi
  have hd := intervalIntegral.integral_hasDerivAt_right
    (P.intervalIntegrable_wt le_rfl hx.le)
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter (hc.congr heq.symm)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with u hu
  exact P.W_eq_intervalIntegral hu.le

private theorem continuousPrimeTheta_eq (P : Params) {t : ℝ} (ht : 0 ≤ t) :
    continuousPrimeTheta P t = t * P.W t - ∫ u in Ioc 0 t, P.W u := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => x) (u' := fun _ => (1 : ℝ)) (v := P.W) (v' := P.wt)
    (by fun_prop)
    (by simpa only [uIcc_of_le ht] using P.continuousOn_W ht)
    (fun x _ => hasDerivAt_id x)
    (fun x hx => hasDerivAt_W P (by simpa only [min_eq_left ht, max_eq_right ht,
      mem_Ioo] using hx.1))
    intervalIntegrable_const (P.intervalIntegrable_wt le_rfl ht)
  simp only [zero_mul, sub_zero, one_mul, intervalIntegral.integral_of_le ht] at h
  refine (setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)).trans h
  change u * P.w u = u * P.wt u
  rw [Params.wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

/-- Quantile discretization loses at most one logarithmic horizon in weighted prime mass. -/
theorem abs_discretePrimeTheta_sub_continuous_le (P : Params) {t : ℝ} (ht : 0 ≤ t) :
    |discretePrimeTheta P t - continuousPrimeTheta P t| ≤ t := by
  have hWmono : Monotone P.W := fun _ _ h => P.W_le_W h
  have hWint : IntegrableOn P.W (Ioc 0 t) := hWmono.intervalIntegrable.1
  have hEint : IntegrableOn P.discrepancy (Ioc 0 t) :=
    (atomCount_integrable P t).sub hWint
  have hElo (u : ℝ) : -1 ≤ P.discrepancy u := (abs_le.mp (P.abs_discrepancy_le u)).1
  have hEhi (u : ℝ) : P.discrepancy u ≤ 0 := by
    rw [Params.discrepancy, P.atomCount_eq]
    exact sub_nonpos.mpr (Nat.floor_le (P.W_nonneg u))
  have hIlo : -t ≤ ∫ u in Ioc 0 t, P.discrepancy u := by
    have h := setIntegral_mono_on (integrable_const (-1 : ℝ)) hEint measurableSet_Ioc
      (fun u _ => hElo u)
    rw [← intervalIntegral.integral_of_le ht, intervalIntegral.integral_const,
      smul_eq_mul] at h
    simpa only [sub_zero, mul_neg_one] using h
  have hIhi : (∫ u in Ioc 0 t, P.discrepancy u) ≤ 0 :=
    integral_nonpos_of_ae (Eventually.of_forall hEhi)
  have hid : discretePrimeTheta P t - continuousPrimeTheta P t =
      t * P.discrepancy t - ∫ u in Ioc 0 t, P.discrepancy u := by
    rw [continuousPrimeTheta_eq P ht]
    simp only [Params.discrepancy]
    rw [integral_sub (atomCount_integrable P t) hWint, integral_atomCount P ht,
      P.atomCount_eq]
    ring
  have hlo := mul_le_mul_of_nonneg_left (hElo t) ht
  have hhi := mul_le_mul_of_nonneg_left (hEhi t) ht
  rw [hid, abs_le]
  constructor <;> linarith only [hlo, hhi, hIlo, hIhi]

/-- Integer rounding preserves the continuous prime count up to a subpower error. -/
theorem abs_integerPrimeTheta_sub_continuous_le (P : Params) {n : ℕ} (hn : 1 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    |integerPrimeTheta P n - continuousPrimeTheta P (Real.log n)| ≤
      Real.log n + Real.exp (ε * Real.log n) *
        ∑' k, Real.exp (-((1 + ε) * P.atom k)) := by
  have ht := Real.log_natCast_nonneg n
  rw [integerPrimeTheta_eq_discrete_add_drift P hn]
  have htri := abs_add_le
    (discretePrimeTheta P (Real.log n) - continuousPrimeTheta P (Real.log n))
    (roundingDrift P (Real.log n))
  rw [abs_of_nonneg (roundingDrift_nonneg P _)] at htri
  have hq := abs_discretePrimeTheta_sub_continuous_le P ht
  have hr := roundingDrift_le P hε ht
  have heq : discretePrimeTheta P (Real.log n) + roundingDrift P (Real.log n) -
      continuousPrimeTheta P (Real.log n) =
      (discretePrimeTheta P (Real.log n) - continuousPrimeTheta P (Real.log n)) +
        roundingDrift P (Real.log n) := by ring
  rw [heq]
  exact htri.trans (add_le_add hq hr)

/-- The real oscillation contributed by the conjugate zero pair `1−μ ± iγ`. -/
def primeOscillation (P : Params) (t : ℝ) : ℝ :=
  -2 * ((1 - P.μ) * Real.cos (P.γ * t) + P.γ * Real.sin (P.γ * t)) /
    ((1 - P.μ) ^ 2 + P.γ ^ 2)

private def oscillatoryPrimitive (β γ t : ℝ) : ℝ :=
  Real.exp (β * t) * (β * Real.cos (γ * t) + γ * Real.sin (γ * t)) / (β ^ 2 + γ ^ 2)

private theorem hasDerivAt_oscillatoryPrimitive {β : ℝ} (hβ : 0 < β) (γ t : ℝ) :
    HasDerivAt (oscillatoryPrimitive β γ)
      (Real.exp (β * t) * Real.cos (γ * t)) t := by
  have hb : HasDerivAt (fun x : ℝ => β * x) β t := by
    convert (hasDerivAt_id t).const_mul β using 1 <;> first | rfl | simp only [mul_one]
  have hg : HasDerivAt (fun x : ℝ => γ * x) γ t := by
    convert (hasDerivAt_id t).const_mul γ using 1 <;> first | rfl | simp only [mul_one]
  have hden : β ^ 2 + γ ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hβ) (sq_nonneg γ))
  have hd := (hb.exp.mul ((hg.cos.const_mul β).add (hg.sin.const_mul γ))).div_const
    (β ^ 2 + γ ^ 2)
  convert hd using 1 <;> first | rfl |
    (dsimp only [Pi.add_apply, Pi.mul_apply]; field_simp [hden]; ring)

private def primeTail (P : Params) (t : ℝ) : ℝ :=
  Real.exp (-((3 * P.μ - 1 - P.ν) * t)) +
    Real.exp (-((3 * P.μ - 1 + P.ν) * t)) - Real.exp (-((4 * P.μ - 1) * t))

private theorem abs_primeTail_le (P : Params) {t : ℝ} (ht : 0 ≤ t) :
    |primeTail P t| ≤ 2 := by
  have h₁ := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg P.hlow ht))
  have h₂ := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg P.hhigh ht))
  have h₃ := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg P.h4 ht))
  have h₁₀ := Real.exp_pos (-((3 * P.μ - 1 - P.ν) * t))
  have h₂₀ := Real.exp_pos (-((3 * P.μ - 1 + P.ν) * t))
  have h₃₀ := Real.exp_pos (-((4 * P.μ - 1) * t))
  rw [primeTail, abs_le]
  constructor <;> linarith only [h₁, h₂, h₃, h₁₀, h₂₀, h₃₀]

private theorem continuousPrimeTheta_oscillation (P : Params) {t : ℝ} (ht : 0 ≤ t) :
    continuousPrimeTheta P t = Real.exp t - 1 -
      2 * (oscillatoryPrimitive (1 - P.μ) P.γ t -
        oscillatoryPrimitive (1 - P.μ) P.γ 0) + ∫ u in (0 : ℝ)..t, primeTail P u := by
  have hβ : 0 < 1 - P.μ := by linarith only [P.hμ2]
  have hc : Continuous (fun u : ℝ =>
      Real.exp ((1 - P.μ) * u) * Real.cos (P.γ * u)) := by fun_prop
  have htail : Continuous (primeTail P) := by unfold primeTail; fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_oscillatoryPrimitive hβ P.γ u) (hc.intervalIntegrable 0 t)
  have hnum : continuousPrimeTheta P t = ∫ u in (0 : ℝ)..t,
      Real.exp u - 2 * (Real.exp ((1 - P.μ) * u) * Real.cos (P.γ * u)) + primeTail P u := by
    rw [continuousPrimeTheta, intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    unfold Params.w RHTower.BeurlingOverRegularIntegers.primeDensity
      RHTower.BeurlingOverRegularIntegers.primeNumerator primeTail
    field_simp [hu.1.ne']
    ring
  rw [hnum, intervalIntegral.integral_add
    (Real.continuous_exp.intervalIntegrable 0 t |>.sub
      ((hc.intervalIntegrable 0 t).const_mul 2)) (htail.intervalIntegrable 0 t),
    intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 t)
      ((hc.intervalIntegrable 0 t).const_mul 2),
    intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero, hint]

/-- The continuous density has an explicit finite oscillation; its remaining terms cost at
most a constant plus twice the logarithmic horizon. -/
theorem abs_continuousPrimeTheta_sub_oscillation_le (P : Params) {t : ℝ} (ht : 0 ≤ t) :
    |continuousPrimeTheta P t -
        (Real.exp t + Real.exp ((1 - P.μ) * t) * primeOscillation P t)| ≤
      1 + 2 * |oscillatoryPrimitive (1 - P.μ) P.γ 0| + 2 * t := by
  have htail : |∫ u in (0 : ℝ)..t, primeTail P u| ≤ 2 * t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (C := (2 : ℝ)) (f := primeTail P) (fun u hu => ?_)
    · simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] using h
    · rw [uIoc_of_le ht] at hu
      simpa only [Real.norm_eq_abs] using abs_primeTail_le P hu.1.le
  have hmain : Real.exp ((1 - P.μ) * t) * primeOscillation P t =
      -2 * oscillatoryPrimitive (1 - P.μ) P.γ t := by
    unfold primeOscillation oscillatoryPrimitive
    ring
  rw [continuousPrimeTheta_oscillation P ht, hmain]
  have heq : Real.exp t - 1 -
      2 * (oscillatoryPrimitive (1 - P.μ) P.γ t -
        oscillatoryPrimitive (1 - P.μ) P.γ 0) + (∫ u in (0 : ℝ)..t, primeTail P u) -
        (Real.exp t + -2 * oscillatoryPrimitive (1 - P.μ) P.γ t) =
      (-1 + 2 * oscillatoryPrimitive (1 - P.μ) P.γ 0) +
        ∫ u in (0 : ℝ)..t, primeTail P u := by ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ htail)
  have h := abs_add_le (-1 : ℝ) (2 * oscillatoryPrimitive (1 - P.μ) P.γ 0)
  simpa only [abs_neg, abs_one, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using h

/-- At every positive power scale, upward integer rounding retains the leading conjugate
prime oscillation of the continuous Beurling model. -/
theorem integerPrimeTheta_finiteOscillation (P : Params) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |integerPrimeTheta P n -
          ((n : ℝ) + Real.exp ((1 - P.μ) * Real.log n) * primeOscillation P (Real.log n))| ≤
        C * Real.exp (ε * Real.log n) := by
  let K : ℝ := 1 + 2 * |oscillatoryPrimitive (1 - P.μ) P.γ 0|
  let S : ℝ := ∑' k, Real.exp (-((1 + ε) * P.atom k))
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS : 0 ≤ S := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨K + 3 / ε + S, by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht := Real.log_natCast_nonneg n
  have hr := abs_integerPrimeTheta_sub_continuous_le P hn hε
  have hc := abs_continuousPrimeTheta_sub_oscillation_le P ht
  rw [Real.exp_log hn0] at hc
  have hbase : |integerPrimeTheta P n -
      ((n : ℝ) + Real.exp ((1 - P.μ) * Real.log n) * primeOscillation P (Real.log n))| ≤
      K + 3 * Real.log n + S * Real.exp (ε * Real.log n) := by
    have h := abs_add_le
      (integerPrimeTheta P n - continuousPrimeTheta P (Real.log n))
      (continuousPrimeTheta P (Real.log n) -
        ((n : ℝ) + Real.exp ((1 - P.μ) * Real.log n) * primeOscillation P (Real.log n)))
    rw [sub_add_sub_cancel] at h
    dsimp only [K, S]
    linarith only [h, hr, hc]
  have he : 1 ≤ Real.exp (ε * Real.log n) := Real.one_le_exp (mul_nonneg hε.le ht)
  have hKe := mul_le_mul_of_nonneg_left he hK.le
  have hte : ε * Real.log n ≤ Real.exp (ε * Real.log n) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hte' := mul_le_mul_of_nonneg_left hte (show 0 ≤ 3 / ε by positivity)
  have hcancel : (3 / ε) * (ε * Real.log n) = 3 * Real.log n := by
    field_simp [hε.ne']
  rw [hcancel] at hte'
  refine hbase.trans ?_
  nlinarith only [hKe, hte']

/-- The finite prime oscillation is nonzero for every admissible parameter. -/
theorem primeOscillation_zero_neg (P : Params) : primeOscillation P 0 < 0 := by
  have hβ : 0 < 1 - P.μ := by linarith only [P.hμ2]
  have hden : 0 < (1 - P.μ) ^ 2 + P.γ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hβ) (sq_nonneg P.γ)
  simp only [primeOscillation, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero]
  exact div_neg_of_neg_of_pos (by linarith only [hβ]) hden

/-- An integer-norm Euler product has exactly the finite zero pair `3/5 ± iγ` and a
nonzero leading prime oscillation with an error smaller than every positive power. -/
theorem integer_norm_one_off_with_prime_oscillation (γ : ℝ) :
    ∃ q : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ Ω : ℝ → ℝ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - Complex.exp (-(s * Real.log (q k))))⁻¹) (F s)) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * Complex.I, (3 / 5 : ℂ) - (γ : ℂ) * Complex.I} ∧
      (∀ t : ℝ, Ω t =
        -2 * ((3 / 5 : ℝ) * Real.cos (γ * t) + γ * Real.sin (γ * t)) /
          ((3 / 5 : ℝ) ^ 2 + γ ^ 2)) ∧
      Ω 0 < 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        |(∑' k, if q k ≤ n then Real.log (q k) else 0) -
            ((n : ℝ) + Real.exp ((3 / 5 : ℝ) * Real.log n) * Ω (Real.log n))| ≤
          C * Real.exp (ε * Real.log n) := by
  let P := fixedParams γ
  refine ⟨primeNorm P, primeNorm_ge_two P, roundedContinuation P, primeOscillation P,
    fun s hs => hasProd_roundedContinuation P hs, differentiableOn_roundedContinuation P,
    ?_, ?_, primeOscillation_zero_neg P, fun ε hε => ?_⟩
  · have h := rounded_zeros_right_of_eq_pair P (h := 0)
      (by norm_num [P, fixedParams]) le_rfl
    norm_num [P, fixedParams] at h ⊢
    exact h
  · intro t
    norm_num [primeOscillation, P, fixedParams]
  · obtain ⟨C, hC, hbound⟩ := integerPrimeTheta_finiteOscillation P hε
    refine ⟨C, hC, fun n hn => ?_⟩
    have h := hbound n hn
    norm_num only [P, fixedParams, integerPrimeTheta, show (1 : ℝ) - 2 / 5 = 3 / 5 by norm_num]
      at h
    exact h

end GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff.abs_discretePrimeTheta_sub_continuous_le
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff.integerPrimeTheta_finiteOscillation
#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.IntegerNormOneOff.integer_norm_one_off_with_prime_oscillation
