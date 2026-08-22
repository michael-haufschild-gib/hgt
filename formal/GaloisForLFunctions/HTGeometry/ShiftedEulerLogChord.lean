import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Complex Filter Set Topology LSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions RHTower

/-- First divided hyperbolic jet at the origin. -/
theorem tendsto_real_sinh_div_self_nhdsNE_zero :
    Tendsto (fun y : ℝ => Real.sinh y / y) (𝓝[≠] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_sinh 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.cosh_zero] at h
  refine h.congr (fun y => ?_)
  rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]

/-- Third divided hyperbolic jet at the origin. -/
theorem tendsto_real_sinh_sub_self_div_cube_nhdsNE_zero :
    Tendsto (fun y : ℝ => (Real.sinh y - y) / y ^ 3)
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
  have hbase : Tendsto (fun y : ℝ => Real.sinh y / (y * 6))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    simpa only [div_div] using
      tendsto_real_sinh_div_self_nhdsNE_zero.div_const 6
  have hcosh : Tendsto (fun y : ℝ => (Real.cosh y - 1) / (3 * y ^ 2))
      (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => Real.sinh y) (g' := fun y : ℝ => y * 6)
      ?_ ?_ ?_ ?_ ?_ hbase
    · exact Filter.Eventually.of_forall fun y =>
        (Real.hasDerivAt_cosh y).sub_const 1
    · exact Filter.Eventually.of_forall fun y => by
        exact (((hasDerivAt_id y).pow 2).const_mul 3).congr_deriv (by
          simp only [Function.id_def]
          ring)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      exact mul_ne_zero hy (by norm_num)
    · have hcont : ContinuousAt (fun y : ℝ => Real.cosh y - 1) 0 := by fun_prop
      have ht : Tendsto (fun y : ℝ => Real.cosh y - 1) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · have hcont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) 0 := by fun_prop
      have ht : Tendsto (fun y : ℝ => 3 * y ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun y : ℝ => Real.cosh y - 1) (g' := fun y : ℝ => 3 * y ^ 2)
    ?_ ?_ ?_ ?_ ?_ hcosh
  · exact Filter.Eventually.of_forall fun y =>
      (Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)
  · exact Filter.Eventually.of_forall fun y => hasDerivAt_pow 3 y
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
  · have hcont : ContinuousAt (fun y : ℝ => Real.sinh y - y) 0 := by fun_prop
    have ht : Tendsto (fun y : ℝ => Real.sinh y - y) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  · have hcont : ContinuousAt (fun y : ℝ => y ^ 3) 0 := by fun_prop
    have ht : Tendsto (fun y : ℝ => y ^ 3) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto
    exact ht.mono_left nhdsWithin_le_nhds

/-- Coefficient stream of the logarithm of the shifted Euler quotient. -/
def shiftedEulerLogIncrementCoeff (ω : ℂ) : ℕ → ℂ :=
  lseriesPowerTwistCoeff eulerLogDirichletCoeff ω -
    lseriesPowerTwistCoeff eulerLogDirichletCoeff (-ω)

theorem shiftedEulerLogIncrementCoeff_apply (ω : ℂ) (n : ℕ) :
    shiftedEulerLogIncrementCoeff ω n =
      eulerLogDirichletCoeff n * ((n : ℂ) ^ ω - (n : ℂ) ^ (-ω)) := by
  rw [shiftedEulerLogIncrementCoeff]
  simp only [Pi.sub_apply, lseriesPowerTwistCoeff]
  ring

/-- The shifted Euler logarithm is the difference of the two canonical Euler-log branches. -/
theorem LSeries_shiftedEulerLogIncrementCoeff_eq
    {ω s : ℂ}
    (hminus : LSeriesSummable eulerLogDirichletCoeff (s - ω))
    (hplus : LSeriesSummable eulerLogDirichletCoeff (s + ω)) :
    LSeries (shiftedEulerLogIncrementCoeff ω) s =
      canonicalEulerLogZeta (s - ω) - canonicalEulerLogZeta (s + ω) := by
  have htwistMinus : LSeriesSummable
      (lseriesPowerTwistCoeff eulerLogDirichletCoeff ω) s :=
    (LSeriesSummable_powerTwist eulerLogDirichletCoeff ω s).mpr hminus
  have htwistPlus : LSeriesSummable
      (lseriesPowerTwistCoeff eulerLogDirichletCoeff (-ω)) s := by
    apply (LSeriesSummable_powerTwist eulerLogDirichletCoeff (-ω) s).mpr
    simpa only [sub_neg_eq_add] using hplus
  rw [shiftedEulerLogIncrementCoeff, LSeries_sub htwistMinus htwistPlus,
    LSeries_powerTwist, LSeries_powerTwist]
  simp only [canonicalEulerLogZeta, sub_neg_eq_add]

/-- Branch-free certification: exponentiating the shifted Euler-log series recovers the literal
Suzuki Euler quotient. -/
theorem exp_LSeries_shiftedEulerLogIncrementCoeff_eq_zeta_ratio
    {ω s : ℂ} (hminus : 1 < (s - ω).re) (hplus : 1 < (s + ω).re) :
    Complex.exp (LSeries (shiftedEulerLogIncrementCoeff ω) s) =
      riemannZeta (s - ω) / riemannZeta (s + ω) := by
  rw [LSeries_shiftedEulerLogIncrementCoeff_eq
      (canonicalEulerLogZeta_summable hminus)
      (canonicalEulerLogZeta_summable hplus),
    Complex.exp_sub,
    exp_canonicalEulerLogZeta_eq_riemannZeta hminus,
    exp_canonicalEulerLogZeta_eq_riemannZeta hplus]

/-- Positive finite chord of the shifted Euler logarithm. -/
def shiftedEulerLogChordCoefficient (ω : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (Real.sinh (ω * Real.log n) / (ω * Real.log n))

/-- The positive real chord is literally the divided coefficient of the shifted Euler-log
increment whose exponential is Suzuki's Euler quotient. -/
theorem shiftedEulerLogChordCoefficient_eq_increment
    {ω : ℝ} (hω : ω ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    shiftedEulerLogChordCoefficient ω n =
      (shiftedEulerLogIncrementCoeff (ω : ℂ) n / (2 * (ω : ℂ))).re := by
  have hn0R : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpowPos : ((n : ℕ) : ℂ) ^ (ω : ℂ) = (((n : ℝ) ^ ω : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) ω).symm
  have hpowNeg : ((n : ℕ) : ℂ) ^ (-(ω : ℂ)) = (((n : ℝ) ^ (-ω) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-ω)).symm
  have hcomplex :
      shiftedEulerLogIncrementCoeff (ω : ℂ) n / (2 * (ω : ℂ)) =
        (((ArithmeticFunction.vonMangoldt n / Real.log n) *
          ((n : ℝ) ^ ω - (n : ℝ) ^ (-ω)) / (2 * ω) : ℝ) : ℂ) := by
    rw [shiftedEulerLogIncrementCoeff_apply, eulerLogDirichletCoeff,
      ← Complex.natCast_log, hpowPos, hpowNeg]
    push_cast
    rfl
  rw [hcomplex, Complex.ofReal_re, shiftedEulerLogChordCoefficient,
    Real.rpow_def_of_pos hn0R, Real.rpow_def_of_pos hn0R,
    Real.sinh_eq]
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  have hexpNeg : Real.exp (Real.log n * -ω) =
      Real.exp (-(ω * Real.log n)) := by congr 1; ring
  rw [hexpNeg]
  field_simp [hω, hlog]

/-- Connected third excess of the finite Euler-log chord. -/
def shiftedEulerLogChordConnectedThirdExcess (ω : ℝ) (n : ℕ) : ℝ :=
  12 * (shiftedEulerLogChordCoefficient ω n -
    ArithmeticFunction.vonMangoldt n) / ω ^ 2

theorem shiftedEulerLogChordConnectedThirdExcess_eq_increment
    {ω : ℝ} (hω : ω ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    shiftedEulerLogChordConnectedThirdExcess ω n =
      12 * ((shiftedEulerLogIncrementCoeff (ω : ℂ) n /
          (2 * (ω : ℂ))).re - ArithmeticFunction.vonMangoldt n) / ω ^ 2 := by
  rw [shiftedEulerLogChordConnectedThirdExcess,
    shiftedEulerLogChordCoefficient_eq_increment hω hn]

theorem shiftedEulerLogChordCoefficient_nonneg
    {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    0 ≤ shiftedEulerLogChordCoefficient ω n := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [shiftedEulerLogChordCoefficient, hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast IsPrimePow.one_lt hnpp)
    have hy : 0 < ω * Real.log n := mul_pos hω hlog
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg (Real.sinh_nonneg_iff.mpr hy.le) hy.le)

theorem shiftedEulerLogChordConnectedThirdExcess_nonneg
    {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    0 ≤ shiftedEulerLogChordConnectedThirdExcess ω n := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [shiftedEulerLogChordConnectedThirdExcess,
      shiftedEulerLogChordCoefficient, hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast IsPrimePow.one_lt hnpp)
    have hy : 0 < ω * Real.log n := mul_pos hω hlog
    have hratio : 1 ≤ Real.sinh (ω * Real.log n) / (ω * Real.log n) := by
      exact (le_div_iff₀ hy).2 (by
        simpa only [one_mul] using Real.self_le_sinh_iff.mpr hy.le)
    rw [shiftedEulerLogChordConnectedThirdExcess,
      shiftedEulerLogChordCoefficient]
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hdiff : 0 ≤ ArithmeticFunction.vonMangoldt n *
          (Real.sinh (ω * Real.log n) / (ω * Real.log n)) -
        ArithmeticFunction.vonMangoldt n := by
      nlinarith
    positivity

theorem shiftedEulerLogChordConnectedThirdExcess_pos_iff
    {ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    0 < shiftedEulerLogChordConnectedThirdExcess ω n ↔ IsPrimePow n := by
  constructor
  · intro h
    by_contra hn
    have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp [shiftedEulerLogChordConnectedThirdExcess,
      shiftedEulerLogChordCoefficient, hΛ] at h
  · intro hnpp
    have hΛ : 0 < ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_pos_iff.mpr hnpp
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast IsPrimePow.one_lt hnpp)
    have hy : 0 < ω * Real.log n := mul_pos hω hlog
    have hratio : 1 < Real.sinh (ω * Real.log n) / (ω * Real.log n) := by
      exact (lt_div_iff₀ hy).2 (by
        simpa only [one_mul] using Real.self_lt_sinh_iff.mpr hy)
    rw [shiftedEulerLogChordConnectedThirdExcess,
      shiftedEulerLogChordCoefficient]
    have hdiff : 0 < ArithmeticFunction.vonMangoldt n *
          (Real.sinh (ω * Real.log n) / (ω * Real.log n)) -
        ArithmeticFunction.vonMangoldt n := by
      nlinarith
    positivity

theorem tendsto_shiftedEulerLogChordConnectedThirdExcess (n : ℕ) :
    Tendsto (fun ω : ℝ => shiftedEulerLogChordConnectedThirdExcess ω n)
      (𝓝[>] 0)
      (𝓝 (2 * ArithmeticFunction.vonMangoldt n * Real.log n ^ 2)) := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [shiftedEulerLogChordConnectedThirdExcess,
      shiftedEulerLogChordCoefficient, hΛ]
  · have hnpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast IsPrimePow.one_lt hnpp)
    have hscale : Tendsto (fun ω : ℝ => ω * Real.log n)
        (𝓝[>] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Tendsto (fun ω : ℝ => ω * Real.log n) (𝓝 0) (𝓝 0) := by
          simpa using
            ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).mul_const
              (Real.log n)).tendsto
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ω hω
        exact mul_ne_zero hω.ne' hlog.ne'
    have hjet := tendsto_real_sinh_sub_self_div_cube_nhdsNE_zero.comp hscale
    have hconst : Tendsto (fun _ : ℝ =>
        12 * ArithmeticFunction.vonMangoldt n * Real.log n ^ 2)
        (𝓝[>] 0)
        (𝓝 (12 * ArithmeticFunction.vonMangoldt n * Real.log n ^ 2)) :=
      tendsto_const_nhds
    have hprod := hjet.mul hconst
    convert hprod using 1
    · funext ω
      rw [shiftedEulerLogChordConnectedThirdExcess,
        shiftedEulerLogChordCoefficient]
      by_cases hω : ω = 0
      · simp [hω]
      · change
          12 * (ArithmeticFunction.vonMangoldt n *
              (Real.sinh (ω * Real.log n) / (ω * Real.log n)) -
            ArithmeticFunction.vonMangoldt n) / ω ^ 2 =
          ((Real.sinh (ω * Real.log n) - ω * Real.log n) /
              (ω * Real.log n) ^ 3) *
            (12 * ArithmeticFunction.vonMangoldt n * Real.log n ^ 2)
        field_simp [hω, hlog.ne']
    · ring

end

end GaloisForLFunctions.HTGeometry
