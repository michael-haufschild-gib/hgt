import GaloisForLFunctions.HTGeometry.ExponentialSeriesAlgebra
import GaloisForLFunctions.HTGeometry.ShiftLatticeThetaSeries
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.HTGeometry.RectangleResidue
import GaloisForLFunctions.HTGeometry.AbeDerivativeDampingNoGo
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureColdWatson
import GaloisForLFunctions.RHTower.HeatEnergyExpand
import GaloisForLFunctions.RHTower.PrimeTailCoPoissonBoundary
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.ZetaUnitIntervalIntegrals
import GaloisForLFunctions.RHTower.Sieve.LogNormSegment
import GaloisForLFunctions.RHTower.XiShiftEulerProductBridge
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.HTGeometry.UnitaryReflectionPhaseHalving
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireLogDerivative
import GaloisForLFunctions.Core
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Gaussian Euler--continuum relative formation

The Gaussian-damped unsquared Euler logarithm is built as an actual normally convergent entire
exponential series.  Its derivative is the negative Gaussian von Mangoldt current, coefficient
for coefficient.  The continuum zero-mode, normalized entire primitive, zero-free formation,
and safe-chart convergence are developed below from the same source clock.

No divisor, zero ordinate, RH hypothesis, axiom, or numerical computation enters the module.
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural-number carrier with the zero and unit coefficients removed definitionally. -/
abbrev GaussianEulerIndex := {n : ℕ // 2 ≤ n}

/-- Gaussian-damped unsquared Euler-log coefficient. -/
def gaussianEulerAmplitude (x : ℝ) (n : GaussianEulerIndex) : ℂ :=
  eulerLogDirichletCoeff n.1 *
    (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ)

/-- Dirichlet frequency associated to `n⁻ˢ`. -/
def gaussianEulerFrequency (n : GaussianEulerIndex) : ℝ :=
  -Real.log (n.1 : ℝ)

/-- Gaussian damping beats every exponential weight in the logarithmic frequency. -/
theorem gaussianEulerAmplitude_normallySummable {x : ℝ} (hx : 0 < x) :
    GaloisForLFunctions.ExpSeriesNormallySummable
      (gaussianEulerAmplitude x) gaussianEulerFrequency := by
  intro R
  have hc : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hraw := GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow
      (A := R) (c := Real.pi * x) (e := 2) hc (by norm_num)
  have hbase : Summable (fun n : GaussianEulerIndex =>
      (n.1 : ℝ) ^ R * Real.exp (-(Real.pi * x * (n.1 : ℝ) ^ (2 : ℝ)))) :=
    hraw.subtype (fun n : ℕ => 2 ≤ n)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have hnpos : (0 : ℝ) < n.1 := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) n.2
  have hnone : (1 : ℝ) ≤ n.1 := by
    exact_mod_cast (le_trans (by omega : 1 ≤ 2) n.2)
  have hnlog : 0 ≤ Real.log (n.1 : ℝ) := Real.log_nonneg hnone
  have hcoeff := norm_eulerLogDirichletCoeff_le_one n.1
  rw [gaussianEulerAmplitude, gaussianEulerFrequency, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_nonneg hnlog]
  rw [Real.rpow_def_of_pos hnpos]
  have hexp : Real.exp (R * Real.log (n.1 : ℝ)) =
      Real.exp (Real.log (n.1 : ℝ) * R) := by ring_nf
  rw [hexp]
  calc
    ‖eulerLogDirichletCoeff n.1‖ *
          Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) *
          Real.exp (Real.log (n.1 : ℝ) * R)
        ≤ 1 * Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) *
          Real.exp (Real.log (n.1 : ℝ) * R) := by
            gcongr
    _ = Real.exp (Real.log (n.1 : ℝ) * R) *
          Real.exp (-(Real.pi * x * (n.1 : ℝ) ^ (2 : ℝ))) := by
      rw [Real.rpow_two]
      ring_nf

/-- Entire Gaussian Euler logarithm `Lₓ(s)`. -/
def gaussianEulerLog (x : ℝ) (s : ℂ) : ℂ :=
  GaloisForLFunctions.cexpSeriesCarrier
    (gaussianEulerAmplitude x) gaussianEulerFrequency (-Complex.I * s)

/-- Entire Gaussian von Mangoldt current `Jₓ(s)`. -/
def gaussianVonMangoldtCurrent (x : ℝ) (s : ℂ) : ℂ :=
  GaloisForLFunctions.cexpSeriesCarrier
    (fun n => gaussianEulerAmplitude x n * (Real.log (n.1 : ℝ) : ℂ))
    gaussianEulerFrequency (-Complex.I * s)

theorem differentiable_gaussianEulerLog {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (gaussianEulerLog x) := by
  intro s
  exact (GaloisForLFunctions.differentiable_cexpSeriesCarrier
    (gaussianEulerAmplitude_normallySummable hx) (-Complex.I * s)).comp s (by fun_prop)

/-- Exact unsquared current law `Lₓ'=-Jₓ`. -/
theorem hasDerivAt_gaussianEulerLog {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (gaussianEulerLog x) (-gaussianVonMangoldtCurrent x s) s := by
  let hnormal := gaussianEulerAmplitude_normallySummable hx
  have houter := (GaloisForLFunctions.differentiable_cexpSeriesCarrier hnormal
    (-Complex.I * s)).hasDerivAt
  rw [congrFun (GaloisForLFunctions.deriv_cexpSeriesCarrier hnormal)
    (-Complex.I * s)] at houter
  have hinner : HasDerivAt (fun z : ℂ => -Complex.I * z) (-Complex.I) s := by
    simpa using (hasDerivAt_id s).const_mul (-Complex.I)
  have hcomp := houter.comp s hinner
  have hvalue :
      GaloisForLFunctions.cexpSeriesCarrier
          (fun n => gaussianEulerAmplitude x n *
            (Complex.I * (gaussianEulerFrequency n : ℂ)))
          gaussianEulerFrequency (-Complex.I * s) * (-Complex.I) =
        -gaussianVonMangoldtCurrent x s := by
    rw [gaussianVonMangoldtCurrent,
      GaloisForLFunctions.cexpSeriesCarrier,
      GaloisForLFunctions.cexpSeriesCarrier]
    have hsum := GaloisForLFunctions.summable_cexpSeries hnormal.deriv (-Complex.I * s)
    rw [← hsum.tsum_mul_right]
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    rw [gaussianEulerFrequency]
    ring_nf
    rw [show Complex.I ^ 2 = -(1 : ℂ) by norm_num]
    push_cast
    ring_nf
  rw [hvalue] at hcomp
  exact hcomp

theorem deriv_gaussianEulerLog {x : ℝ} (hx : 0 < x) :
    deriv (gaussianEulerLog x) = -gaussianVonMangoldtCurrent x := by
  funext s
  exact (hasDerivAt_gaussianEulerLog hx s).deriv

/-! ## Continuum zero-mode and normalized primitive -/

/-- Literal Gaussian continuum integrand on `[1,∞)`. -/
def gaussianContinuumIntegrand (x : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-Real.pi * x * u ^ 2) : ℂ) * (u : ℂ) ^ (-s)

/-- Continuum heat zero-mode `Mₓ(s)=∫₁^∞ exp(-πxu²)u⁻ˢ du`. -/
def gaussianContinuumCurrent (x : ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ in Ici 1, gaussianContinuumIntegrand x s u

/-- Full-line cutoff used only to invoke a global dominated-integral theorem. -/
private def gaussianContinuumCutoff (x : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  (Ici (1 : ℝ)).indicator (gaussianContinuumIntegrand x s) u

/-- Undamped continuum Mellin carrier, extended by zero off `[1,∞)`. -/
private def gaussianContinuumUndampedCutoff (s : ℂ) (u : ℝ) : ℂ :=
  (Ici (1 : ℝ)).indicator (fun u : ℝ => (u : ℂ) ^ (-s)) u

private theorem gaussianContinuumCurrent_eq_integral_cutoff (x : ℝ) (s : ℂ) :
    gaussianContinuumCurrent x s =
      ∫ u : ℝ, gaussianContinuumCutoff x s u := by
  simp [gaussianContinuumCurrent, gaussianContinuumCutoff,
    integral_indicator measurableSet_Ici]

private theorem gaussianContinuumCutoff_measurable (x : ℝ) (s : ℂ) :
    AEStronglyMeasurable (gaussianContinuumCutoff x s) volume := by
  apply AEStronglyMeasurable.indicator _ measurableSet_Ici
  exact ((by fun_prop : Continuous (fun u : ℝ =>
      (Real.exp (-Real.pi * x * u ^ 2) : ℂ))).measurable.mul
        (Complex.measurable_ofReal.pow_const (-s))).aestronglyMeasurable

private theorem gaussianContinuumCutoff_differentiableOn (x : ℝ) (u : ℝ) :
    DifferentiableOn ℂ (fun s : ℂ => gaussianContinuumCutoff x s u) univ := by
  by_cases hu : u ∈ Ici (1 : ℝ)
  · simp only [gaussianContinuumCutoff, indicator_of_mem hu]
    have hu0 : (u : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (zero_lt_one.trans_le hu))
    have hpow : Differentiable ℂ (fun s : ℂ => (u : ℂ) ^ (-s)) := by
      have heq : (fun s : ℂ => (u : ℂ) ^ (-s)) =
          fun s : ℂ => Complex.exp (Complex.log (u : ℂ) * (-s)) := by
        funext s
        exact Complex.cpow_def_of_ne_zero hu0 _
      rw [heq]
      fun_prop
    intro s _
    unfold gaussianContinuumIntegrand
    exact ((differentiable_const _).mul hpow).differentiableAt.differentiableWithinAt
  · simp [gaussianContinuumCutoff, hu]

private theorem gaussianContinuumBound_integrable
    (x : ℝ) (hx : 0 < x) (z₀ : ℂ) :
    Integrable (fun u : ℝ => (Ici (1 : ℝ)).indicator
      (fun u => u ^ (|z₀.re| + 1) *
        Real.exp (-(Real.pi * x) * u ^ (2 : ℝ))) u) := by
  have hraw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := |z₀.re| + 1) (p := 2) (b := Real.pi * x)
    (by linarith [abs_nonneg z₀.re]) (by norm_num) (mul_pos Real.pi_pos hx)
  have hsub : IntegrableOn
      (fun u : ℝ => u ^ (|z₀.re| + 1) *
        Real.exp (-(Real.pi * x) * u ^ (2 : ℝ)))
      (Ici (1 : ℝ)) volume :=
    hraw.mono_set (fun u hu => show 0 < u from zero_lt_one.trans_le hu)
  exact hsub.integrable_indicator measurableSet_Ici

private theorem gaussianContinuumCutoff_bound
    (x : ℝ) (z₀ s : ℂ) (u : ℝ) (hs : s ∈ ball z₀ 1) :
    ‖gaussianContinuumCutoff x s u‖ ≤
      (Ici (1 : ℝ)).indicator
        (fun u => u ^ (|z₀.re| + 1) *
          Real.exp (-(Real.pi * x) * u ^ (2 : ℝ))) u := by
  by_cases hu : u ∈ Ici (1 : ℝ)
  · simp only [gaussianContinuumCutoff, indicator_of_mem hu,
      gaussianContinuumIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),
      GaloisForLFunctions.norm_cpow_neg_eq_rpow_re u
        (zero_lt_one.trans_le hu) s]
    have hre : |s.re - z₀.re| < 1 := by
      have hdist : ‖s - z₀‖ < 1 := by
        simpa only [mem_ball, dist_eq] using hs
      have hle := abs_re_le_norm (s - z₀)
      have hre_eq : (s - z₀).re = s.re - z₀.re := rfl
      rw [hre_eq] at hle
      exact lt_of_le_of_lt hle hdist
    have hexp : -s.re ≤ |z₀.re| + 1 := by
      have hz : -z₀.re ≤ |z₀.re| := neg_le_abs z₀.re
      have hlow : -1 < s.re - z₀.re := (abs_lt.mp hre).1
      linarith
    have hrpow := Real.rpow_le_rpow_of_exponent_le hu hexp
    rw [Real.rpow_two]
    calc
      Real.exp (-Real.pi * x * u ^ 2) * u ^ (-s.re)
          ≤ Real.exp (-Real.pi * x * u ^ 2) * u ^ (|z₀.re| + 1) :=
        mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le
      _ = u ^ (|z₀.re| + 1) *
          Real.exp (-(Real.pi * x) * u ^ 2) := by ring_nf
  · simp [gaussianContinuumCutoff, hu]

/-- The literal continuum zero-mode is entire for every positive Gaussian time. -/
theorem differentiable_gaussianContinuumCurrent {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (gaussianContinuumCurrent x) := by
  intro z₀
  rw [show gaussianContinuumCurrent x =
      fun s => ∫ u : ℝ, gaussianContinuumCutoff x s u by
    funext s
    exact gaussianContinuumCurrent_eq_integral_cutoff x s]
  exact GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
    (F := gaussianContinuumCutoff x) (R := 1) (bound := fun u : ℝ =>
      (Ici (1 : ℝ)).indicator
        (fun u => u ^ (|z₀.re| + 1) *
          Real.exp (-(Real.pi * x) * u ^ (2 : ℝ))) u)
    (by norm_num)
    (fun s _ => gaussianContinuumCutoff_measurable x s)
    (fun u => (gaussianContinuumCutoff_differentiableOn x u).mono (subset_univ _))
    (fun u s hs => gaussianContinuumCutoff_bound x z₀ s u hs)
    (gaussianContinuumBound_integrable x hx z₀)

/-- Existence of the unique entire continuum primitive normalized at `s=2`. -/
theorem exists_gaussianContinuumPrimitive {x : ℝ} (hx : 0 < x) :
    ∃ A : ℂ → ℂ, A 2 = 0 ∧
      ∀ s : ℂ, HasDerivAt A (gaussianContinuumCurrent x s) s := by
  obtain ⟨F, hF⟩ := (differentiable_gaussianContinuumCurrent hx).isExactOn_univ
  exact ⟨fun s => F s - F 2, by simp,
    fun s => (hF s (mem_univ s)).sub_const (F 2)⟩

/-- Canonical normalized entire primitive `Aₓ`. -/
def gaussianContinuumPrimitive (x : ℝ) : ℂ → ℂ :=
  if hx : 0 < x then (exists_gaussianContinuumPrimitive hx).choose else 0

@[simp] theorem gaussianContinuumPrimitive_two {x : ℝ} (hx : 0 < x) :
    gaussianContinuumPrimitive x 2 = 0 := by
  rw [gaussianContinuumPrimitive, dif_pos hx]
  exact (exists_gaussianContinuumPrimitive hx).choose_spec.1

theorem hasDerivAt_gaussianContinuumPrimitive {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (gaussianContinuumPrimitive x) (gaussianContinuumCurrent x s) s := by
  rw [gaussianContinuumPrimitive, dif_pos hx]
  exact (exists_gaussianContinuumPrimitive hx).choose_spec.2 s

theorem differentiable_gaussianContinuumPrimitive {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (gaussianContinuumPrimitive x) :=
  fun s => (hasDerivAt_gaussianContinuumPrimitive hx s).differentiableAt

/-- Normalization makes the entire primitive unique. -/
theorem gaussianContinuumPrimitive_unique {x : ℝ} (hx : 0 < x)
    {A : ℂ → ℂ} (hA2 : A 2 = 0)
    (hA : ∀ s : ℂ, HasDerivAt A (gaussianContinuumCurrent x s) s) :
    A = gaussianContinuumPrimitive x := by
  funext s
  have hzero : ∀ z : ℂ,
      HasDerivAt (A - gaussianContinuumPrimitive x) 0 z := by
    intro z
    simpa only [sub_self] using
      (hA z).sub (hasDerivAt_gaussianContinuumPrimitive hx z)
  let D : ℂ → ℂ := A - gaussianContinuumPrimitive x
  have hD : Differentiable ℂ D := fun z => (hzero z).differentiableAt
  have hDf : ∀ z : ℂ, fderiv ℂ D z = 0 := by
    intro z
    rw [(hzero z).hasFDerivAt.fderiv]
    simp
  have hconst := is_const_of_fderiv_eq_zero hD hDf s 2
  apply sub_eq_zero.mp
  simpa [D, hA2, gaussianContinuumPrimitive_two hx] using hconst

/-! ## Schwarz reality -/

private theorem gaussianEulerAmplitude_conj (x : ℝ) (n : GaussianEulerIndex) :
    (starRingEnd ℂ) (gaussianEulerAmplitude x n) = gaussianEulerAmplitude x n := by
  rw [gaussianEulerAmplitude, map_mul]
  congr 1
  · simp [eulerLogDirichletCoeff, ← Complex.natCast_log]
  · exact Complex.conj_ofReal _

private theorem gaussianCexpChar_conj (omega : ℝ) (s : ℂ) :
    (starRingEnd ℂ) (GaloisForLFunctions.cexpChar omega (-Complex.I * s)) =
      GaloisForLFunctions.cexpChar omega (-Complex.I * (starRingEnd ℂ) s) := by
  rw [GaloisForLFunctions.cexpChar, GaloisForLFunctions.cexpChar,
    ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The Gaussian Euler logarithm has real Dirichlet coefficients. -/
theorem gaussianEulerLog_conj (x : ℝ) (s : ℂ) :
    gaussianEulerLog x ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianEulerLog x s) := by
  rw [gaussianEulerLog, gaussianEulerLog,
    GaloisForLFunctions.cexpSeriesCarrier,
    GaloisForLFunctions.cexpSeriesCarrier]
  change (∑' i : GaussianEulerIndex,
      gaussianEulerAmplitude x i *
        GaloisForLFunctions.cexpChar (gaussianEulerFrequency i)
          (-Complex.I * (starRingEnd ℂ) s)) =
    star (∑' i : GaussianEulerIndex,
      gaussianEulerAmplitude x i *
        GaloisForLFunctions.cexpChar (gaussianEulerFrequency i) (-Complex.I * s))
  rw [tsum_star]
  apply tsum_congr
  intro n
  change gaussianEulerAmplitude x n *
      GaloisForLFunctions.cexpChar (gaussianEulerFrequency n)
        (-Complex.I * (starRingEnd ℂ) s) =
    (starRingEnd ℂ) (gaussianEulerAmplitude x n *
      GaloisForLFunctions.cexpChar (gaussianEulerFrequency n) (-Complex.I * s))
  rw [map_mul, gaussianEulerAmplitude_conj,
    gaussianCexpChar_conj]

private theorem integrable_gaussianContinuumCutoff
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Integrable (gaussianContinuumCutoff x s) volume := by
  exact Integrable.mono'
    (gaussianContinuumBound_integrable x hx s)
    (gaussianContinuumCutoff_measurable x s)
    (Filter.Eventually.of_forall fun u =>
      gaussianContinuumCutoff_bound x s s u (mem_ball_self zero_lt_one))

private theorem gaussianContinuumCutoff_conj
    (x : ℝ) (s : ℂ) (u : ℝ) :
    gaussianContinuumCutoff x ((starRingEnd ℂ) s) u =
      (starRingEnd ℂ) (gaussianContinuumCutoff x s u) := by
  by_cases hu : u ∈ Ici (1 : ℝ)
  · simp only [gaussianContinuumCutoff, indicator_of_mem hu,
      gaussianContinuumIntegrand]
    rw [map_mul, Complex.conj_ofReal,
      conj_ofReal_cpow (zero_lt_one.trans_le hu)]
    simp only [map_neg]
  · simp [gaussianContinuumCutoff, hu]

/-- The Gaussian continuum current is Schwarz-real. -/
theorem gaussianContinuumCurrent_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    gaussianContinuumCurrent x ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianContinuumCurrent x s) := by
  rw [gaussianContinuumCurrent_eq_integral_cutoff,
    gaussianContinuumCurrent_eq_integral_cutoff]
  have hmap := Complex.conjCLE.toContinuousLinearMap.integral_comp_comm
    (integrable_gaussianContinuumCutoff hx s)
  calc
    (∫ u : ℝ, gaussianContinuumCutoff x ((starRingEnd ℂ) s) u) =
        ∫ u : ℝ, Complex.conjCLE (gaussianContinuumCutoff x s u) := by
      apply integral_congr_ae
      filter_upwards with u
      exact gaussianContinuumCutoff_conj x s u
    _ = Complex.conjCLE (∫ u : ℝ, gaussianContinuumCutoff x s u) := hmap

/-- The normalized continuum primitive is Schwarz-real. -/
theorem gaussianContinuumPrimitive_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    gaussianContinuumPrimitive x ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianContinuumPrimitive x s) := by
  let B : ℂ → ℂ := fun z =>
    (starRingEnd ℂ) (gaussianContinuumPrimitive x ((starRingEnd ℂ) z))
  have hB2 : B 2 = 0 := by
    change (starRingEnd ℂ)
      (gaussianContinuumPrimitive x ((starRingEnd ℂ) (2 : ℂ))) = 0
    rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by exact map_ofNat (starRingEnd ℂ) 2,
      gaussianContinuumPrimitive_two hx, map_zero]
  have hB : ∀ z : ℂ, HasDerivAt B (gaussianContinuumCurrent x z) z := by
    intro z
    have h := (hasDerivAt_gaussianContinuumPrimitive hx
      ((starRingEnd ℂ) z)).conj_conj
    have hcurrent := gaussianContinuumCurrent_conj hx z
    simpa [B, Function.comp_def, hcurrent] using h
  have huniq := gaussianContinuumPrimitive_unique hx hB2 hB
  have hvalue := congrFun huniq s
  simpa [B] using congrArg (starRingEnd ℂ) hvalue

/-! ## Zero-free relative formation and exact current law -/

/-- Archimedean half-completion `h∞(s)=(1/2)sπ^{-s/2}Γ(s/2)`. -/
def gaussianArchimedeanHalfFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

theorem gaussianArchimedeanHalfFactor_ne_zero {s : ℂ} (hs : 0 < s.re) :
    gaussianArchimedeanHalfFactor s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast Real.pi_ne_zero))
  have hhalf : 0 < (s / 2).re := by
    norm_num
    linarith
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hpi)
    (GaloisForLFunctions.HTGeometry.gamma_ne_zero_of_re_pos hhalf)

theorem differentiableAt_gaussianArchimedeanHalfFactor
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ gaussianArchimedeanHalfFactor s := by
  have hpow : DifferentiableAt ℂ (fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2)) s :=
    ((differentiableAt_id.neg.div_const 2).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero)))
  have hhalf : 0 < (s / 2).re := by
    norm_num
    linarith
  have hGamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (GaloisForLFunctions.HTGeometry.differentiableAt_gamma_of_re_pos hhalf).comp s
      (differentiableAt_id.div_const 2)
  exact (((differentiableAt_const (c := (1 / 2 : ℂ))).mul
    differentiableAt_id).mul hpow).mul hGamma

theorem gaussianArchimedeanHalfFactor_eq_gammaReal (s : ℂ) :
    gaussianArchimedeanHalfFactor s =
      (1 / 2 : ℂ) * s * Complex.Gammaℝ s := by
  rw [gaussianArchimedeanHalfFactor, Complex.Gammaℝ_def]
  ring

theorem gaussianArchimedeanHalfFactor_conj (s : ℂ) :
    gaussianArchimedeanHalfFactor ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianArchimedeanHalfFactor s) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [gaussianArchimedeanHalfFactor_eq_gammaReal,
    gaussianArchimedeanHalfFactor_eq_gammaReal, Gammaℝ_conj,
    map_mul, map_mul, hhalf]

/-- Entire additive potential carrying both atomic Euler and continuum channels. -/
def gaussianRelativePotential (x : ℝ) (s : ℂ) : ℂ :=
  gaussianEulerLog x s + gaussianContinuumPrimitive x s

theorem hasDerivAt_gaussianRelativePotential {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (gaussianRelativePotential x)
      (-gaussianVonMangoldtCurrent x s + gaussianContinuumCurrent x s) s := by
  exact (hasDerivAt_gaussianEulerLog hx s).add
    (hasDerivAt_gaussianContinuumPrimitive hx s)

theorem differentiable_gaussianRelativePotential {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (gaussianRelativePotential x) :=
  fun s => (hasDerivAt_gaussianRelativePotential hx s).differentiableAt

theorem gaussianRelativePotential_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    gaussianRelativePotential x ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianRelativePotential x s) := by
  rw [gaussianRelativePotential, gaussianRelativePotential,
    gaussianEulerLog_conj, gaussianContinuumPrimitive_conj hx, map_add]

/-- Gaussian Euler--continuum relative formation `Φₓ`. -/
def gaussianEulerContinuumFormation (x : ℝ) (s : ℂ) : ℂ :=
  gaussianArchimedeanHalfFactor s * Complex.exp (gaussianRelativePotential x s)

/-- The relative formation is holomorphic throughout the open right half-plane. -/
theorem differentiableAt_gaussianEulerContinuumFormation
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (gaussianEulerContinuumFormation x) s := by
  exact (differentiableAt_gaussianArchimedeanHalfFactor hs).mul
    ((hasDerivAt_gaussianRelativePotential hx s).cexp.differentiableAt)

/-- `Φₓ` is zero-free throughout the open right half-plane. -/
theorem gaussianEulerContinuumFormation_ne_zero
    (x : ℝ) {s : ℂ} (hs : 0 < s.re) :
    gaussianEulerContinuumFormation x s ≠ 0 :=
  mul_ne_zero (gaussianArchimedeanHalfFactor_ne_zero hs)
    (Complex.exp_ne_zero _)

/-- The relative formation has the real structure inherited from its literal sources. -/
theorem gaussianEulerContinuumFormation_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    gaussianEulerContinuumFormation x ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianEulerContinuumFormation x s) := by
  rw [gaussianEulerContinuumFormation, gaussianEulerContinuumFormation,
    gaussianArchimedeanHalfFactor_conj, gaussianRelativePotential_conj hx,
    Complex.exp_conj, map_mul]

/-- Exact combined atomic-minus-continuum current law `(GECRF.2)`. -/
theorem logDeriv_gaussianEulerContinuumFormation
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (gaussianEulerContinuumFormation x) s =
      logDeriv gaussianArchimedeanHalfFactor s -
        gaussianVonMangoldtCurrent x s + gaussianContinuumCurrent x s := by
  let D : ℂ := -gaussianVonMangoldtCurrent x s + gaussianContinuumCurrent x s
  let E : ℂ := Complex.exp (gaussianRelativePotential x s)
  have hH := differentiableAt_gaussianArchimedeanHalfFactor hs
  have hP := hasDerivAt_gaussianRelativePotential hx s
  have hE : HasDerivAt (fun z => Complex.exp (gaussianRelativePotential x z))
      (E * D) s := by
    simpa [D, E] using hP.cexp
  have hderiv : deriv (gaussianEulerContinuumFormation x) s =
      (deriv gaussianArchimedeanHalfFactor s * E +
        gaussianArchimedeanHalfFactor s * (E * D)) := by
    change deriv (fun z => gaussianArchimedeanHalfFactor z *
      Complex.exp (gaussianRelativePotential x z)) s = _
    rw [show (fun z => gaussianArchimedeanHalfFactor z *
        Complex.exp (gaussianRelativePotential x z)) =
      gaussianArchimedeanHalfFactor *
        (fun z => Complex.exp (gaussianRelativePotential x z)) by
      funext z
      rfl]
    simpa [E] using (hH.hasDerivAt.mul hE).deriv
  have hH0 := gaussianArchimedeanHalfFactor_ne_zero hs
  have hE0 : E ≠ 0 := by simp [E]
  rw [logDeriv_apply, hderiv, logDeriv_apply,
    gaussianEulerContinuumFormation]
  dsimp only [D]
  change (deriv gaussianArchimedeanHalfFactor s * E +
      gaussianArchimedeanHalfFactor s *
        (E * (-gaussianVonMangoldtCurrent x s + gaussianContinuumCurrent x s))) /
      (gaussianArchimedeanHalfFactor s * E) = _
  field_simp [hH0, hE0]
  ring

/-! ## Safe Euler-chart damping limits -/

/-- Open half-plane where the undamped Euler and continuum carriers converge absolutely. -/
def gaussianSafeEulerChart : Set ℂ := {s | 1 < s.re}

theorem isOpen_gaussianSafeEulerChart : IsOpen gaussianSafeEulerChart := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Continuous Gaussian damping tends compact-uniformly to the identity in every absolutely
convergent Dirichlet series.  This is the uniform Tannery lemma used by both atomic channels. -/
private theorem tendstoUniformlyOn_gaussianDampedDirichletSeries
    (a : GaussianEulerIndex → ℂ)
    (habs : ∀ s : ℂ, 1 < s.re → Summable (fun n : GaussianEulerIndex =>
      ‖a n * (n.1 : ℂ) ^ (-s)‖))
    {K : Set ℂ} (hK : IsCompact K) (hKsafe : K ⊆ gaussianSafeEulerChart) :
    TendstoUniformlyOn
      (fun x : ℝ => fun s : ℂ => ∑' n : GaussianEulerIndex,
        a n * (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s))
      (fun s : ℂ => ∑' n : GaussianEulerIndex, a n * (n.1 : ℂ) ^ (-s))
      (nhdsWithin (0 : ℝ) (Ioi 0)) K := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀K, hs₀min⟩ :=
    hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  have hs₀safe : 1 < s₀.re := hKsafe hs₀K
  let σ : ℂ := (s₀.re : ℂ)
  let g : GaussianEulerIndex → ℝ := fun n =>
    ‖a n * (n.1 : ℂ) ^ (-σ)‖
  have hgsum : Summable g := by
    exact habs σ (by simpa [σ] using hs₀safe)
  have hpow_le : ∀ s ∈ K, ∀ n : GaussianEulerIndex,
      ‖(n.1 : ℂ) ^ (-s)‖ ≤ ‖(n.1 : ℂ) ^ (-σ)‖ := by
    intro s hs n
    have hnpos : (0 : ℝ) < n.1 := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) n.2
    have hn1 : (1 : ℝ) ≤ n.1 := by
      exact_mod_cast le_trans (by omega : 1 ≤ 2) n.2
    change ‖((n.1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖((n.1 : ℝ) : ℂ) ^ (-σ)‖
    rw [GaloisForLFunctions.norm_cpow_neg_eq_rpow_re n.1 hnpos s,
      GaloisForLFunctions.norm_cpow_neg_eq_rpow_re n.1 hnpos σ]
    exact Real.rpow_le_rpow_of_exponent_le hn1
      (neg_le_neg (hs₀min hs))
  let d : ℝ → GaussianEulerIndex → ℝ := fun x n =>
    (1 - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)) * g n
  have hdpoint : ∀ n : GaussianEulerIndex,
      Tendsto (fun x : ℝ => d x n) (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => d x n) 0 := by
      dsimp [d]
      fun_prop
    simpa [d] using hcont.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 from inf_le_left)
  have hddom : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ n : GaussianEulerIndex, ‖d x n‖ ≤ g n := by
    filter_upwards [self_mem_nhdsWithin] with x hx n
    have hexp0 : 0 ≤ Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) :=
      (Real.exp_pos _).le
    have hexp1 : Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ Real.pi * x * (n.1 : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg Real.pi_pos.le hx.le) (sq_nonneg _)
      linarith
    have hg0 : 0 ≤ g n := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hexp1) hg0)]
    have hcoef : 1 - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
      linarith
    simpa using mul_le_mul_of_nonneg_right hcoef hg0
  have hdlim : Tendsto (fun x : ℝ => ∑' n : GaussianEulerIndex, d x n)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hgsum hdpoint hddom
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have heps := (tendsto_order.1 hdlim).2 ε hε
  filter_upwards [self_mem_nhdsWithin, heps] with x hx hxε s hs
  have hexp0 : ∀ n : GaussianEulerIndex,
      0 ≤ Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) :=
    fun n => (Real.exp_pos _).le
  have hexp1 : ∀ n : GaussianEulerIndex,
      Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
    intro n
    rw [Real.exp_le_one_iff]
    have : 0 ≤ Real.pi * x * (n.1 : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg Real.pi_pos.le hx.le) (sq_nonneg _)
    linarith
  let U : GaussianEulerIndex → ℂ := fun n => a n * (n.1 : ℂ) ^ (-s)
  let D : GaussianEulerIndex → ℂ := fun n =>
    a n * (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
      (n.1 : ℂ) ^ (-s)
  have hUnorm : Summable (fun n => ‖U n‖) := by
    simpa only [U] using habs s (hKsafe hs)
  have hDnorm_le : ∀ n, ‖D n‖ ≤ ‖U n‖ := by
    intro n
    simp only [D, U, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖a n‖ * Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) *
            ‖(n.1 : ℂ) ^ (-s)‖
          ≤ ‖a n‖ * 1 * ‖(n.1 : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hexp1 n) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖a n‖ * ‖(n.1 : ℂ) ^ (-s)‖ := by ring
  have hDnorm : Summable (fun n => ‖D n‖) :=
    hUnorm.of_nonneg_of_le (fun n => norm_nonneg _) hDnorm_le
  have hdiff_bound : ∀ n, ‖U n - D n‖ ≤ d x n := by
    intro n
    have heq : U n - D n =
        ((1 - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℝ) : ℂ) *
          (a n * (n.1 : ℂ) ^ (-s)) := by
      dsimp [U, D]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hexp1 n))]
    dsimp only [d, g]
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hpow_le s hs n) (norm_nonneg _))
      (sub_nonneg.mpr (hexp1 n))
  have hdsum : Summable (d x) := by
    refine hgsum.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (sub_nonneg.mpr (hexp1 n)) (norm_nonneg _)
    · have hcoef : 1 - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
        linarith [hexp0 n]
      change (1 - Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)) * g n ≤ g n
      have hg0 : 0 ≤ g n := norm_nonneg _
      simpa using mul_le_mul_of_nonneg_right hcoef hg0
  have hdiffnorm : Summable (fun n => ‖U n - D n‖) :=
    hdsum.of_nonneg_of_le (fun n => norm_nonneg _) hdiff_bound
  rw [dist_eq_norm]
  calc
    ‖(∑' n, U n) - ∑' n, D n‖ = ‖∑' n, (U n - D n)‖ := by
      rw [hUnorm.of_norm.tsum_sub hDnorm.of_norm]
    _ ≤ ∑' n, ‖U n - D n‖ := norm_tsum_le_tsum_norm hdiffnorm
    _ ≤ ∑' n, d x n := Summable.tsum_mono hdiffnorm hdsum hdiff_bound
    _ < ε := hxε

/-- Compact-uniform convergence is preserved by the complex exponential when the limit is
continuous on the compact set. -/
private theorem TendstoUniformlyOn.cexp_of_isCompact
    {ι X : Type*} [TopologicalSpace X] {l : Filter ι}
    {F : ι → X → ℂ} {f : X → ℂ} {K : Set X}
    (hF : TendstoUniformlyOn F f l K) (hK : IsCompact K)
    (hf : ContinuousOn f K) :
    TendstoUniformlyOn (fun i x => Complex.exp (F i x))
      (fun x => Complex.exp (f x)) l K := by
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn
    (Complex.continuous_exp.continuousOn.comp hf (fun _ _ => mem_univ _))
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ x ∈ K, ‖Complex.exp (f x)‖ ≤ M := fun x hx =>
    (hM₀ x hx).trans (le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  let δ : ℝ := min 1 (ε / (2 * M + 2))
  have hδ0 : 0 < δ := by
    dsimp only [δ]
    exact lt_min one_pos (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 2 * M * δ < ε := by
    have h1 : δ ≤ ε / (2 * M + 2) := min_le_right _ _
    have h2 : 2 * M * δ ≤ 2 * M * (ε / (2 * M + 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * M * (ε / (2 * M + 2)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  filter_upwards [hF δ hδ0] with i hi x hx
  have hdist : ‖F i x - f x‖ < δ := by
    have := hi x hx
    rwa [dist_eq_norm, norm_sub_rev] at this
  have hle1 : ‖F i x - f x‖ ≤ 1 := hdist.le.trans hδ1
  have hsplit : Complex.exp (F i x) - Complex.exp (f x) =
      Complex.exp (f x) * (Complex.exp (F i x - f x) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  have hbound : ‖Complex.exp (F i x) - Complex.exp (f x)‖ ≤
      M * (2 * ‖F i x - f x‖) := by
    rw [hsplit, norm_mul]
    exact mul_le_mul (hM x hx) (Complex.norm_exp_sub_one_le hle1)
      (norm_nonneg _) hM0
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt hbound (by nlinarith [norm_nonneg (F i x - f x)])

private theorem gaussianCexpChar_eq_cpow (n : GaussianEulerIndex) (s : ℂ) :
    GaloisForLFunctions.cexpChar (gaussianEulerFrequency n) (-Complex.I * s) =
      (n.1 : ℂ) ^ (-s) := by
  have hn0 : (n.1 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) n.2))
  rw [GaloisForLFunctions.cexpChar, gaussianEulerFrequency,
    Complex.cpow_def_of_ne_zero hn0]
  congr 1
  have hnpos : (0 : ℝ) < n.1 := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) n.2
  have hlog : Complex.log (n.1 : ℂ) = (Real.log (n.1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  rw [hlog]
  rw [Complex.ofReal_neg]
  calc
    Complex.I * -(Real.log (n.1 : ℝ) : ℂ) * (-Complex.I * s) =
        Complex.I ^ 2 * (Real.log (n.1 : ℝ) : ℂ) * s := by ring
    _ = (Real.log (n.1 : ℝ) : ℂ) * -s := by
      rw [show Complex.I ^ 2 = -(1 : ℂ) by norm_num]
      ring

theorem gaussianEulerLog_eq_tsum_cpow (x : ℝ) (s : ℂ) :
    gaussianEulerLog x s =
      ∑' n : GaussianEulerIndex,
        gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-s) := by
  rw [gaussianEulerLog, GaloisForLFunctions.cexpSeriesCarrier]
  apply tsum_congr
  intro n
  rw [gaussianCexpChar_eq_cpow]

/-- Undamped unsquared Euler logarithm on its literal `n≥2` carrier. -/
def gaussianUndampedEulerLog (s : ℂ) : ℂ :=
  ∑' n : GaussianEulerIndex,
    eulerLogDirichletCoeff n.1 * (n.1 : ℂ) ^ (-s)

/-- The subtype carrier is exactly the canonical Euler logarithm. -/
theorem gaussianUndampedEulerLog_eq_canonicalEulerLogZeta (s : ℂ) :
    gaussianUndampedEulerLog s = canonicalEulerLogZeta s := by
  rw [gaussianUndampedEulerLog]
  change (∑' n : ↥({n : ℕ | 2 ≤ n} : Set ℕ),
      eulerLogDirichletCoeff n.1 * (n.1 : ℂ) ^ (-s)) = _
  rw [tsum_subtype ({n : ℕ | 2 ≤ n} : Set ℕ)
      (fun n => eulerLogDirichletCoeff n * (n : ℂ) ^ (-s)),
    canonicalEulerLogZeta, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · have hnmem : n ∈ ({n : ℕ | 2 ≤ n} : Set ℕ) := hn
    rw [Set.indicator_of_mem hnmem,
      LSeries.term_of_ne_zero (by omega), div_eq_mul_inv,
      Complex.cpow_neg]
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · simp [LSeries.term_zero]
    · simp [eulerLogDirichletCoeff_one]

private theorem summable_norm_gaussianUndampedEulerTerm
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : GaussianEulerIndex =>
      ‖eulerLogDirichletCoeff n.1 * (n.1 : ℂ) ^ (-s)‖) := by
  have hnat : Summable (fun n : ℕ =>
      ‖LSeries.term eulerLogDirichletCoeff s n‖) :=
    summable_norm_iff.mpr (canonicalEulerLogZeta_summable hs)
  refine (hnat.subtype (fun n : ℕ => 2 ≤ n)).congr ?_
  intro n
  simp only [Function.comp_apply]
  rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv,
    Complex.cpow_neg]

/-- Gaussian Euler damping converges to the canonical Euler logarithm at every safe-chart point. -/
theorem tendsto_gaussianEulerLog_nhdsWithin_zero
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun x : ℝ => gaussianEulerLog x s)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (canonicalEulerLogZeta s)) := by
  let f : ℝ → GaussianEulerIndex → ℂ := fun x n =>
    gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-s)
  let g : GaussianEulerIndex → ℂ := fun n =>
    eulerLogDirichletCoeff n.1 * (n.1 : ℂ) ^ (-s)
  have hpoint : ∀ n, Tendsto (fun x : ℝ => f x n)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (g n)) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => f x n) 0 := by
      dsimp [f, gaussianEulerAmplitude]
      fun_prop
    have ht : Tendsto (fun x : ℝ => f x n)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (f 0 n)) := by
      refine hcont.tendsto.mono_left ?_
      exact inf_le_left
    simpa [f, g, gaussianEulerAmplitude] using
      ht
  have hdom : ∀ᶠ x : ℝ in (nhdsWithin (0 : ℝ) (Ioi 0)), ∀ n,
      ‖f x n‖ ≤ ‖g n‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx n
    have hexp : Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnonneg : 0 ≤ Real.pi * x * (n.1 : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (le_of_lt hx)) (sq_nonneg _)
      linarith
    dsimp [f, g, gaussianEulerAmplitude]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖eulerLogDirichletCoeff n.1‖ *
            Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) * ‖(n.1 : ℂ) ^ (-s)‖
          ≤ ‖eulerLogDirichletCoeff n.1‖ * 1 * ‖(n.1 : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) (norm_nonneg _)
      _ = ‖eulerLogDirichletCoeff n.1‖ * ‖(n.1 : ℂ) ^ (-s)‖ := by ring
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_norm_gaussianUndampedEulerTerm hs) hpoint hdom
  have htarget : (∑' n : GaussianEulerIndex,
      eulerLogDirichletCoeff n.1 * (n.1 : ℂ) ^ (-s)) =
      canonicalEulerLogZeta s := by
    rw [← gaussianUndampedEulerLog_eq_canonicalEulerLogZeta,
      gaussianUndampedEulerLog]
  rw [htarget] at hlim
  simpa only [f, g, gaussianEulerLog_eq_tsum_cpow] using hlim

theorem gaussianVonMangoldtCurrent_eq_tsum_cpow (x : ℝ) (s : ℂ) :
    gaussianVonMangoldtCurrent x s =
      ∑' n : GaussianEulerIndex,
        (ArithmeticFunction.vonMangoldt n.1 : ℂ) *
          (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s) := by
  rw [gaussianVonMangoldtCurrent,
    GaloisForLFunctions.cexpSeriesCarrier]
  apply tsum_congr
  intro n
  rw [gaussianCexpChar_eq_cpow, gaussianEulerAmplitude]
  calc
    (eulerLogDirichletCoeff n.1 *
          (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
        (Real.log (n.1 : ℝ) : ℂ)) * (n.1 : ℂ) ^ (-s) =
        (eulerLogDirichletCoeff n.1 * (Real.log (n.1 : ℝ) : ℂ)) *
          (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s) := by ring
    _ = (ArithmeticFunction.vonMangoldt n.1 : ℂ) *
          (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s) := by
      rw [eulerLogDirichletCoeff_mul_log n.2]

/-- Undamped von Mangoldt current on the same literal `n≥2` carrier. -/
def gaussianUndampedVonMangoldtCurrent (s : ℂ) : ℂ :=
  ∑' n : GaussianEulerIndex,
    (ArithmeticFunction.vonMangoldt n.1 : ℂ) * (n.1 : ℂ) ^ (-s)

theorem gaussianUndampedVonMangoldtCurrent_eq_LSeries (s : ℂ) :
    gaussianUndampedVonMangoldtCurrent s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [gaussianUndampedVonMangoldtCurrent]
  change (∑' n : ↥({n : ℕ | 2 ≤ n} : Set ℕ),
      (ArithmeticFunction.vonMangoldt n.1 : ℂ) * (n.1 : ℂ) ^ (-s)) = _
  rw [tsum_subtype ({n : ℕ | 2 ≤ n} : Set ℕ)
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)),
    LSeries]
  apply tsum_congr
  intro n
  by_cases hn : 2 ≤ n
  · have hnmem : n ∈ ({n : ℕ | 2 ≤ n} : Set ℕ) := hn
    rw [Set.indicator_of_mem hnmem,
      LSeries.term_of_ne_zero (by omega), div_eq_mul_inv,
      Complex.cpow_neg]
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · simp [LSeries.term_zero]
    · simp [ArithmeticFunction.vonMangoldt_apply_one]

private theorem summable_norm_gaussianUndampedVonMangoldtTerm
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : GaussianEulerIndex =>
      ‖(ArithmeticFunction.vonMangoldt n.1 : ℂ) * (n.1 : ℂ) ^ (-s)‖) := by
  have hnat : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  refine (hnat.subtype (fun n : ℕ => 2 ≤ n)).congr ?_
  intro n
  simp only [Function.comp_apply]
  rw [LSeries.term_of_ne_zero (by omega), div_eq_mul_inv,
    Complex.cpow_neg]

/-- Gaussian von Mangoldt damping converges to the literal zeta logarithmic current. -/
theorem tendsto_gaussianVonMangoldtCurrent_nhdsWithin_zero
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun x : ℝ => gaussianVonMangoldtCurrent x s)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (-deriv riemannZeta s / riemannZeta s)) := by
  let f : ℝ → GaussianEulerIndex → ℂ := fun x n =>
    (ArithmeticFunction.vonMangoldt n.1 : ℂ) *
      (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
      (n.1 : ℂ) ^ (-s)
  let g : GaussianEulerIndex → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n.1 : ℂ) * (n.1 : ℂ) ^ (-s)
  have hpoint : ∀ n, Tendsto (fun x : ℝ => f x n)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (g n)) := by
    intro n
    have hcont : ContinuousAt (fun x : ℝ => f x n) 0 := by
      dsimp [f]
      fun_prop
    have ht : Tendsto (fun x : ℝ => f x n)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (f 0 n)) := by
      refine hcont.tendsto.mono_left ?_
      exact inf_le_left
    simpa [f, g] using ht
  have hdom : ∀ᶠ x : ℝ in (nhdsWithin (0 : ℝ) (Ioi 0)), ∀ n,
      ‖f x n‖ ≤ ‖g n‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx n
    have hexp : Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hnonneg : 0 ≤ Real.pi * x * (n.1 : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (le_of_lt hx)) (sq_nonneg _)
      linarith
    dsimp [f, g]
    have hexpnorm :
        ‖(Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ)‖ =
          Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, norm_mul, norm_mul, hexpnorm]
    calc
      ‖(ArithmeticFunction.vonMangoldt n.1 : ℂ)‖ *
            Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) * ‖(n.1 : ℂ) ^ (-s)‖
          ≤ ‖(ArithmeticFunction.vonMangoldt n.1 : ℂ)‖ * 1 *
              ‖(n.1 : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) (norm_nonneg _)
      _ = ‖(ArithmeticFunction.vonMangoldt n.1 : ℂ)‖ *
          ‖(n.1 : ℂ) ^ (-s)‖ := by ring
  have hlim := tendsto_tsum_of_dominated_convergence
    (summable_norm_gaussianUndampedVonMangoldtTerm hs) hpoint hdom
  have htarget : (∑' n : GaussianEulerIndex,
      (ArithmeticFunction.vonMangoldt n.1 : ℂ) * (n.1 : ℂ) ^ (-s)) =
      -deriv riemannZeta s / riemannZeta s := by
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      ← gaussianUndampedVonMangoldtCurrent_eq_LSeries,
      gaussianUndampedVonMangoldtCurrent]
  rw [htarget] at hlim
  simpa only [f, g, gaussianVonMangoldtCurrent_eq_tsum_cpow] using hlim

/-- Gaussian continuum damping converges to its exact Mellin zero-mode on the safe chart. -/
theorem tendsto_gaussianContinuumCurrent_nhdsWithin_zero
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun x : ℝ => gaussianContinuumCurrent x s)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 ((s - 1)⁻¹)) := by
  let F : ℝ → ℝ → ℂ := fun x => gaussianContinuumCutoff x s
  let f : ℝ → ℂ := fun u => (Ici (1 : ℝ)).indicator
    (fun u : ℝ => (u : ℂ) ^ (-s)) u
  let bound : ℝ → ℝ := fun u => (Ici (1 : ℝ)).indicator
    (fun u : ℝ => ‖(u : ℂ) ^ (-s)‖) u
  have hmeas : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      AEStronglyMeasurable (F x) volume := by
    exact Filter.Eventually.of_forall fun x => gaussianContinuumCutoff_measurable x s
  have hbound : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ᵐ u : ℝ ∂volume, ‖F x u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [] with u
    by_cases hu : u ∈ Ici (1 : ℝ)
    · have hexp : Real.exp (-Real.pi * x * u ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hnonneg : 0 ≤ Real.pi * x * u ^ 2 :=
          mul_nonneg (mul_nonneg Real.pi_pos.le (le_of_lt hx)) (sq_nonneg _)
        linarith
      simp only [F, bound, gaussianContinuumCutoff, gaussianContinuumIntegrand,
        indicator_of_mem hu, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-Real.pi * x * u ^ 2) * ‖(u : ℂ) ^ (-s)‖
            ≤ 1 * ‖(u : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
        _ = ‖(u : ℂ) ^ (-s)‖ := one_mul _
    · simp [F, bound, gaussianContinuumCutoff, hu]
  have hbound_integrable : Integrable bound volume := by
    have hpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s))
        (Ici (1 : ℝ)) volume :=
      integrableOn_Ici_ofReal_cpow one_pos (by simp; linarith)
    change Integrable ((Ici (1 : ℝ)).indicator
      (fun u : ℝ => ‖(u : ℂ) ^ (-s)‖)) volume
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
    exact hpow.norm
  have hpoint : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun x : ℝ => F x u)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (f u)) := by
    filter_upwards [] with u
    by_cases hu : u ∈ Ici (1 : ℝ)
    · have hcont : ContinuousAt
          (fun x : ℝ => (Real.exp (-Real.pi * x * u ^ 2) : ℂ) *
            (u : ℂ) ^ (-s)) 0 := by
        fun_prop
      have ht := hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 from inf_le_left)
      simpa [F, f, gaussianContinuumCutoff, gaussianContinuumIntegrand, hu] using ht
    · simp [F, f, gaussianContinuumCutoff, hu]
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    bound hmeas hbound hbound_integrable hpoint
  have htarget : (∫ u : ℝ, f u) = (s - 1)⁻¹ := by
    rw [show (∫ u : ℝ, f u) = ∫ u : ℝ in Ici 1, (u : ℂ) ^ (-s) by
      simp [f, integral_indicator measurableSet_Ici]]
    rw [integral_Ici_ofReal_cpow one_pos (by simp; linarith)]
    norm_num
    have hdeneq : -s + 1 = -(s - 1) := by ring
    calc
      -1 / (-s + 1) = -1 / (-(s - 1)) := by rw [hdeneq]
      _ = 1 / (s - 1) := neg_div_neg_eq 1 (s - 1)
      _ = (s - 1)⁻¹ := one_div (s - 1)
  rw [← htarget]
  simpa only [F, gaussianContinuumCurrent_eq_integral_cutoff] using hlim

private theorem integral_gaussianContinuumUndampedCutoff
    {s : ℂ} (hs : 1 < s.re) :
    (∫ u : ℝ, gaussianContinuumUndampedCutoff s u) = (s - 1)⁻¹ := by
  rw [show (∫ u : ℝ, gaussianContinuumUndampedCutoff s u) =
      ∫ u : ℝ in Ici 1, (u : ℂ) ^ (-s) by
    simp [gaussianContinuumUndampedCutoff, integral_indicator measurableSet_Ici]]
  rw [integral_Ici_ofReal_cpow one_pos (by simp; linarith)]
  norm_num
  have hdeneq : -s + 1 = -(s - 1) := by ring
  calc
    -1 / (-s + 1) = -1 / (-(s - 1)) := by rw [hdeneq]
    _ = 1 / (s - 1) := neg_div_neg_eq 1 (s - 1)
    _ = (s - 1)⁻¹ := one_div (s - 1)

private theorem integrable_gaussianContinuumUndampedCutoff
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (gaussianContinuumUndampedCutoff s) volume := by
  change Integrable ((Ici (1 : ℝ)).indicator
    (fun u : ℝ => (u : ℂ) ^ (-s))) volume
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
  exact integrableOn_Ici_ofReal_cpow one_pos (by simp; linarith)

/-- The continuum zero-modes converge locally uniformly on the full safe Euler chart. -/
theorem tendstoLocallyUniformlyOn_gaussianContinuumCurrent :
    TendstoLocallyUniformlyOn (fun x : ℝ => gaussianContinuumCurrent x)
      (fun s => (s - 1)⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨s₀, hs₀K, hs₀min⟩ :=
    hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  have hs₀safe : 1 < s₀.re := hKsafe hs₀K
  let σ : ℂ := (s₀.re : ℂ)
  let g : ℝ → ℝ := fun u => (Ici (1 : ℝ)).indicator
    (fun u : ℝ => ‖(u : ℂ) ^ (-σ)‖) u
  let d : ℝ → ℝ → ℝ := fun x u => (Ici (1 : ℝ)).indicator
    (fun u : ℝ =>
      (1 - Real.exp (-Real.pi * x * u ^ 2)) * ‖(u : ℂ) ^ (-σ)‖) u
  have hgintegrable : Integrable g volume := by
    have hpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-σ))
        (Ici (1 : ℝ)) volume :=
      integrableOn_Ici_ofReal_cpow one_pos (by simpa [σ] using hs₀safe)
    change Integrable ((Ici (1 : ℝ)).indicator
      (fun u : ℝ => ‖(u : ℂ) ^ (-σ)‖)) volume
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ici]
    exact hpow.norm
  have hdmeas : ∀ x : ℝ, AEStronglyMeasurable (d x) volume := by
    intro x
    apply AEStronglyMeasurable.indicator _ measurableSet_Ici
    exact (((by fun_prop : Continuous (fun u : ℝ =>
        1 - Real.exp (-Real.pi * x * u ^ 2))).measurable.mul
      (Complex.measurable_ofReal.pow_const (-σ)).norm).aestronglyMeasurable)
  have hddom : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ᵐ u : ℝ ∂volume, ‖d x u‖ ≤ g u := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [] with u
    by_cases hu : u ∈ Ici (1 : ℝ)
    · have hexp0 : 0 ≤ Real.exp (-Real.pi * x * u ^ 2) := (Real.exp_pos _).le
      have hexp1 : Real.exp (-Real.pi * x * u ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.pi * x * u ^ 2 :=
          mul_nonneg (mul_nonneg Real.pi_pos.le hx.le) (sq_nonneg _)
        linarith
      simp only [d, g, indicator_of_mem hu, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hexp1) (norm_nonneg _))]
      have hcoef : 1 - Real.exp (-Real.pi * x * u ^ 2) ≤ 1 := by linarith
      simpa using mul_le_mul_of_nonneg_right hcoef
        (norm_nonneg ((u : ℂ) ^ (-σ)))
    · simp [d, g, hu]
  have hdpoint : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun x : ℝ => d x u)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
    filter_upwards [] with u
    by_cases hu : u ∈ Ici (1 : ℝ)
    · have hcont : ContinuousAt (fun x : ℝ => d x u) 0 := by
        simp only [d, indicator_of_mem hu]
        fun_prop
      simpa [d, hu] using hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 from inf_le_left)
    · simp [d, hu]
  have hdlim : Tendsto (fun x : ℝ => ∫ u : ℝ, d x u)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      g (Filter.Eventually.of_forall hdmeas) hddom hgintegrable hdpoint
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have heps := (tendsto_order.1 hdlim).2 ε hε
  filter_upwards [self_mem_nhdsWithin, heps] with x hx hxε s hs
  have hsSafe : 1 < s.re := hKsafe hs
  have hU := integrable_gaussianContinuumUndampedCutoff hsSafe
  have hD := integrable_gaussianContinuumCutoff hx s
  have hdint : Integrable (d x) volume := by
    exact Integrable.mono' hgintegrable (hdmeas x)
      (Filter.Eventually.of_forall fun u => by
        have h := hddom
        by_cases hu : u ∈ Ici (1 : ℝ)
        · have hexp0 : 0 ≤ Real.exp (-Real.pi * x * u ^ 2) := (Real.exp_pos _).le
          have hexp1 : Real.exp (-Real.pi * x * u ^ 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have : 0 ≤ Real.pi * x * u ^ 2 :=
              mul_nonneg (mul_nonneg Real.pi_pos.le hx.le) (sq_nonneg _)
            linarith
          simp only [d, g, indicator_of_mem hu, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hexp1) (norm_nonneg _))]
          have hcoef : 1 - Real.exp (-Real.pi * x * u ^ 2) ≤ 1 := by linarith
          simpa using mul_le_mul_of_nonneg_right hcoef
            (norm_nonneg ((u : ℂ) ^ (-σ)))
        · simp [d, g, hu])
  have hdiff : ∀ᵐ u : ℝ ∂volume,
      ‖gaussianContinuumUndampedCutoff s u - gaussianContinuumCutoff x s u‖ ≤ d x u := by
    filter_upwards [] with u
    by_cases hu : u ∈ Ici (1 : ℝ)
    · have hu0 : (0 : ℝ) < u := zero_lt_one.trans_le hu
      have hu1 : (1 : ℝ) ≤ u := hu
      have hexp1 : Real.exp (-Real.pi * x * u ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.pi * x * u ^ 2 :=
          mul_nonneg (mul_nonneg Real.pi_pos.le hx.le) (sq_nonneg _)
        linarith
      have hpow : ‖(u : ℂ) ^ (-s)‖ ≤ ‖(u : ℂ) ^ (-σ)‖ := by
        rw [GaloisForLFunctions.norm_cpow_neg_eq_rpow_re u hu0 s,
          GaloisForLFunctions.norm_cpow_neg_eq_rpow_re u hu0 σ]
        exact Real.rpow_le_rpow_of_exponent_le hu1 (neg_le_neg (hs₀min hs))
      simp only [gaussianContinuumUndampedCutoff, gaussianContinuumCutoff,
        gaussianContinuumIntegrand, indicator_of_mem hu]
      have heq : (u : ℂ) ^ (-s) -
          (Real.exp (-Real.pi * x * u ^ 2) : ℂ) * (u : ℂ) ^ (-s) =
          ((1 - Real.exp (-Real.pi * x * u ^ 2) : ℝ) : ℂ) *
            (u : ℂ) ^ (-s) := by
        push_cast
        ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hexp1)]
      dsimp only [d]
      rw [indicator_of_mem hu]
      exact mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hexp1)
    · simp [gaussianContinuumUndampedCutoff, gaussianContinuumCutoff, d, hu]
  rw [dist_eq_norm, ← integral_gaussianContinuumUndampedCutoff hsSafe,
    gaussianContinuumCurrent_eq_integral_cutoff,
    ← MeasureTheory.integral_sub hU hD]
  exact lt_of_le_of_lt
    (MeasureTheory.norm_integral_le_of_norm_le hdint hdiff) hxε

/-- Canonical safe-chart limit of the normalized continuum primitive. -/
def gaussianContinuumPrimitiveLimit (s : ℂ) : ℂ := Complex.log (s - 1)

@[simp] theorem gaussianContinuumPrimitiveLimit_two :
    gaussianContinuumPrimitiveLimit 2 = 0 := by
  change Complex.log ((2 : ℂ) - 1) = 0
  norm_num

theorem hasDerivAt_gaussianContinuumPrimitiveLimit
    {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt gaussianContinuumPrimitiveLimit (s - 1)⁻¹ s := by
  have hslit : s - 1 ∈ Complex.slitPlane := by
    exact Or.inl (by simp; linarith)
  have hinner : HasDerivAt (fun z : ℂ => z - 1) 1 s :=
    (hasDerivAt_id s).sub_const 1
  have h := (Complex.hasDerivAt_log hslit).comp s hinner
  change HasDerivAt (fun z : ℂ => Complex.log (z - 1)) (s - 1)⁻¹ s
  simpa only [Function.comp_def, mul_one] using h

/-- Normalization at `2` promotes the compact-uniform current limit to compact-uniform
convergence of the entire primitives. -/
theorem tendstoLocallyUniformlyOn_gaussianContinuumPrimitive :
    TendstoLocallyUniformlyOn (fun x : ℝ => gaussianContinuumPrimitive x)
      gaussianContinuumPrimitiveLimit (nhdsWithin (0 : ℝ) (Ioi 0))
      gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  let Kseg : Set ℂ := (fun p : ℝ × ℂ =>
    (2 : ℂ) + (p.1 : ℂ) * (p.2 - 2)) '' (Icc (0 : ℝ) 1 ×ˢ K)
  have hKseg : IsCompact Kseg := by
    exact (isCompact_Icc.prod hK).image (by fun_prop)
  have hKsegSafe : Kseg ⊆ gaussianSafeEulerChart := by
    rintro z ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    have hsSafe : 1 < s.re := hKsafe hs
    change 1 < ((2 : ℂ) + (t : ℂ) * (s - 2)).re
    have hre : ((2 : ℂ) + (t : ℂ) * (s - 2)).re =
        2 + t * (s.re - 2) := by norm_num
    rw [hre]
    by_cases ht1 : t = 1
    · subst t
      norm_num
      exact hsSafe
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hleft : (1 - t) * 1 < (1 - t) * 2 :=
        mul_lt_mul_of_pos_left (by norm_num) (sub_pos.mpr htlt)
      have hright : t * 1 ≤ t * s.re :=
        mul_le_mul_of_nonneg_left hsSafe.le ht.1
      nlinarith
  have hM : TendstoUniformlyOn (fun x : ℝ => gaussianContinuumCurrent x)
      (fun s => (s - 1)⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) Kseg :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact
      isOpen_gaussianSafeEulerChart).mp
      tendstoLocallyUniformlyOn_gaussianContinuumCurrent Kseg hKsegSafe hKseg
  obtain ⟨smax, hsmaxK, hsmax⟩ := hK.exists_isMaxOn hKne
    ((continuous_id.sub continuous_const).norm.continuousOn)
  let R : ℝ := ‖smax - 2‖
  have hR0 : 0 ≤ R := norm_nonneg _
  have hR : ∀ s ∈ K, ‖s - 2‖ ≤ R := fun s hs => by
    simpa [R] using hsmax hs
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := ε / (R + 1)
  have hden : 0 < R + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hMev := (Metric.tendstoUniformlyOn_iff.mp hM) δ hδ
  filter_upwards [self_mem_nhdsWithin, hMev] with x hx hxM s hs
  let L : ℂ → ℂ := fun z =>
    gaussianContinuumPrimitive x z - gaussianContinuumPrimitiveLimit z
  have hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      (2 : ℂ) + (t : ℂ) * (s - 2) ∈ Kseg := by
    intro t ht
    exact ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℂ L ((2 : ℂ) + (t : ℂ) * (s - 2)) := by
    intro t ht
    have hzSafe := hKsegSafe (hsegment t ht)
    exact ((hasDerivAt_gaussianContinuumPrimitive hx _).sub
      (hasDerivAt_gaussianContinuumPrimitiveLimit hzSafe)).differentiableAt
  have hderivBound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv L ((2 : ℂ) + (t : ℂ) * (s - 2))‖ ≤ δ := by
    intro t ht
    let z : ℂ := (2 : ℂ) + (t : ℂ) * (s - 2)
    have hzK : z ∈ Kseg := hsegment t ht
    have hzSafe := hKsegSafe hzK
    have hder := (hasDerivAt_gaussianContinuumPrimitive hx z).sub
      (hasDerivAt_gaussianContinuumPrimitiveLimit hzSafe)
    have hclose := hxM z hzK
    have hderEq : deriv L z =
        gaussianContinuumCurrent x z - (z - 1)⁻¹ := by
      change deriv (gaussianContinuumPrimitive x - gaussianContinuumPrimitiveLimit) z = _
      exact hder.deriv
    change ‖deriv L z‖ ≤ δ
    rw [hderEq]
    rw [dist_eq_norm] at hclose
    have heq : gaussianContinuumCurrent x z - (z - 1)⁻¹ =
        -((z - 1)⁻¹ - gaussianContinuumCurrent x z) := by ring
    rw [heq, norm_neg]
    exact hclose.le
  have hmean := RHTower.Sieve.norm_sub_le_segment
    (L := L) (z₁ := s) (z₂ := 2) hdiff hderivBound
  have hLtwo : L 2 = 0 := by
    simp [L, gaussianContinuumPrimitive_two hx]
  have hδR : δ * R < ε := by
    have hfrac : R / (R + 1) < 1 := (div_lt_one hden).2 (by linarith)
    calc
      δ * R = ε * (R / (R + 1)) := by dsimp [δ]; ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hfrac hε
      _ = ε := mul_one ε
  rw [dist_comm, dist_eq_norm]
  change ‖gaussianContinuumPrimitive x s - gaussianContinuumPrimitiveLimit s‖ < ε
  calc
    ‖gaussianContinuumPrimitive x s - gaussianContinuumPrimitiveLimit s‖ =
        ‖L s - L 2‖ := by rw [hLtwo, sub_zero]
    _ ≤ δ * ‖s - 2‖ := by simpa using hmean
    _ ≤ δ * R := mul_le_mul_of_nonneg_left (hR s hs) hδ.le
    _ < ε := hδR

/-- The Gaussian Euler logarithms converge locally uniformly on the full safe Euler chart. -/
theorem tendstoLocallyUniformlyOn_gaussianEulerLog :
    TendstoLocallyUniformlyOn (fun x : ℝ => gaussianEulerLog x)
      canonicalEulerLogZeta (nhdsWithin (0 : ℝ) (Ioi 0)) gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  have hraw := tendstoUniformlyOn_gaussianDampedDirichletSeries
    (fun n : GaussianEulerIndex => eulerLogDirichletCoeff n.1)
    (fun s hs => summable_norm_gaussianUndampedEulerTerm hs) hK hKsafe
  have hsource : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      EqOn
        (fun s : ℂ => ∑' n : GaussianEulerIndex,
          eulerLogDirichletCoeff n.1 *
            (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
            (n.1 : ℂ) ^ (-s))
        (gaussianEulerLog x) K := by
    filter_upwards [] with x s hs
    rw [gaussianEulerLog_eq_tsum_cpow]
    apply tsum_congr
    intro n
    rw [gaussianEulerAmplitude]
  refine (hraw.congr hsource).congr_right ?_
  intro s hs
  exact gaussianUndampedEulerLog_eq_canonicalEulerLogZeta s

/-- The Gaussian von Mangoldt currents converge locally uniformly to the zeta logarithmic
derivative on the full safe Euler chart. -/
theorem tendstoLocallyUniformlyOn_gaussianVonMangoldtCurrent :
    TendstoLocallyUniformlyOn (fun x : ℝ => gaussianVonMangoldtCurrent x)
      (fun s => -deriv riemannZeta s / riemannZeta s)
      (nhdsWithin (0 : ℝ) (Ioi 0)) gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  have hraw := tendstoUniformlyOn_gaussianDampedDirichletSeries
    (fun n : GaussianEulerIndex => (ArithmeticFunction.vonMangoldt n.1 : ℂ))
    (fun s hs => summable_norm_gaussianUndampedVonMangoldtTerm hs) hK hKsafe
  have hsource : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      EqOn
        (fun s : ℂ => ∑' n : GaussianEulerIndex,
          (ArithmeticFunction.vonMangoldt n.1 : ℂ) *
            (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
            (n.1 : ℂ) ^ (-s))
        (gaussianVonMangoldtCurrent x) K := by
    filter_upwards [] with x s hs
    exact (gaussianVonMangoldtCurrent_eq_tsum_cpow x s).symm
  refine (hraw.congr hsource).congr_right ?_
  intro s hs
  change gaussianUndampedVonMangoldtCurrent s =
    -deriv riemannZeta s / riemannZeta s
  rw [gaussianUndampedVonMangoldtCurrent_eq_LSeries,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hKsafe hs)]

/-- Safe-chart limit of the additive relative potential. -/
def gaussianRelativePotentialLimit (s : ℂ) : ℂ :=
  canonicalEulerLogZeta s + gaussianContinuumPrimitiveLimit s

theorem tendstoLocallyUniformlyOn_gaussianRelativePotential :
    TendstoLocallyUniformlyOn (fun x : ℝ => gaussianRelativePotential x)
      gaussianRelativePotentialLimit (nhdsWithin (0 : ℝ) (Ioi 0))
      gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  have hL := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    isOpen_gaussianSafeEulerChart).mp
    tendstoLocallyUniformlyOn_gaussianEulerLog K hKsafe hK
  have hA := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    isOpen_gaussianSafeEulerChart).mp
    tendstoLocallyUniformlyOn_gaussianContinuumPrimitive K hKsafe hK
  have hsum := hL.add hA
  have hsource : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      EqOn ((fun s => gaussianEulerLog x s) +
        fun s => gaussianContinuumPrimitive x s)
        (gaussianRelativePotential x) K := by
    filter_upwards [] with x s hs
    rfl
  have htarget : EqOn
      (canonicalEulerLogZeta + gaussianContinuumPrimitiveLimit)
      gaussianRelativePotentialLimit K := by
    intro s hs
    rfl
  exact (hsum.congr hsource).congr_right htarget

/-- Safe-chart multiplicative limit before identifying it with completed Xi. -/
def gaussianEulerContinuumFormationLimit (s : ℂ) : ℂ :=
  gaussianArchimedeanHalfFactor s * Complex.exp (gaussianRelativePotentialLimit s)

/-- Exact Euler--continuum recombination into completed Xi. -/
theorem gaussianEulerContinuumFormationLimit_eq_xi
    {s : ℂ} (hs : 1 < s.re) :
    gaussianEulerContinuumFormationLimit s = xi s := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hre : s.re - 1 = 0 := by
      apply_fun Complex.re at h
      simpa using h
    linarith
  rw [gaussianEulerContinuumFormationLimit, gaussianRelativePotentialLimit,
    gaussianContinuumPrimitiveLimit, Complex.exp_add,
    exp_canonicalEulerLogZeta_eq_riemannZeta hs,
    Complex.exp_log hs1,
    xi_eq_eulerXiArchimedeanFactor_mul_zeta_of_one_lt_re hs,
    gaussianArchimedeanHalfFactor_eq_gammaReal]
  unfold eulerXiArchimedeanFactor
  ring

/-- The complete zero-free Gaussian formation converges locally uniformly to completed Xi on
the safe Euler chart. -/
theorem tendstoLocallyUniformlyOn_gaussianEulerContinuumFormation :
    TendstoLocallyUniformlyOn (fun x : ℝ => gaussianEulerContinuumFormation x)
      xi (nhdsWithin (0 : ℝ) (Ioi 0)) gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  have hPot := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    isOpen_gaussianSafeEulerChart).mp
    tendstoLocallyUniformlyOn_gaussianRelativePotential K hKsafe hK
  have hPotContinuous : ContinuousOn gaussianRelativePotentialLimit K := by
    apply hPot.continuousOn
    refine Filter.Eventually.frequently ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (differentiable_gaussianRelativePotential hx).continuous.continuousOn
  have hExp := TendstoUniformlyOn.cexp_of_isCompact hPot hK hPotContinuous
  have hHalf : TendstoUniformlyOn
      (fun _ : ℝ => gaussianArchimedeanHalfFactor)
      gaussianArchimedeanHalfFactor (nhdsWithin (0 : ℝ) (Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall fun x s hs => by simpa using hε
  have hHalfContinuous : ContinuousOn gaussianArchimedeanHalfFactor K := by
    intro s hs
    exact (differentiableAt_gaussianArchimedeanHalfFactor
      (lt_trans zero_lt_one (hKsafe hs))).continuousAt.continuousWithinAt
  have hExpContinuous : ContinuousOn
      (fun s => Complex.exp (gaussianRelativePotentialLimit s)) K :=
    Complex.continuous_exp.continuousOn.comp hPotContinuous
      (fun _ _ => mem_univ _)
  have hprod := GaloisForLFunctions.HTGeometry.TendstoUniformlyOn.mul_of_isCompact
    hHalf hExp hK hHalfContinuous hExpContinuous
  have hformation : TendstoUniformlyOn
      (fun x : ℝ => gaussianEulerContinuumFormation x)
      gaussianEulerContinuumFormationLimit (nhdsWithin (0 : ℝ) (Ioi 0)) K := by
    have hsource : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        EqOn
          (fun s => gaussianArchimedeanHalfFactor s *
            Complex.exp (gaussianRelativePotential x s))
          (gaussianEulerContinuumFormation x) K := by
      filter_upwards [] with x s hs
      rfl
    have htarget : EqOn
        (fun s => gaussianArchimedeanHalfFactor s *
          Complex.exp (gaussianRelativePotentialLimit s))
        gaussianEulerContinuumFormationLimit K := by
      intro s hs
      rfl
    exact (hprod.congr hsource).congr_right htarget
  exact hformation.congr_right fun s hs =>
    gaussianEulerContinuumFormationLimit_eq_xi (hKsafe hs)

/-- Locally uniform convergence returns the full logarithmic jet on the zero-free Euler chart. -/
theorem tendstoLocallyUniformlyOn_logDeriv_gaussianEulerContinuumFormation :
    TendstoLocallyUniformlyOn
      (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x))
      (logDeriv xi) (nhdsWithin (0 : ℝ) (Ioi 0)) gaussianSafeEulerChart := by
  apply RiemannGaussian.logDeriv_tendstoLocallyUniformlyOn
    tendstoLocallyUniformlyOn_gaussianEulerContinuumFormation
  · filter_upwards [self_mem_nhdsWithin] with x hx
    intro s hs
    exact (differentiableAt_gaussianEulerContinuumFormation hx
      (lt_trans zero_lt_one hs)).differentiableWithinAt
  · exact isOpen_gaussianSafeEulerChart
  · intro s hs
    rw [← gaussianEulerContinuumFormationLimit_eq_xi hs]
    exact mul_ne_zero
      (gaussianArchimedeanHalfFactor_ne_zero (lt_trans zero_lt_one hs))
      (Complex.exp_ne_zero _)

/-- Unit-modulus phase of a nonzero complex formation. -/
def gaussianNormalizedPhase (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  F s / (‖F s‖ : ℂ)

theorem norm_gaussianNormalizedPhase {F : ℂ → ℂ} {s : ℂ} (hF : F s ≠ 0) :
    ‖gaussianNormalizedPhase F s‖ = 1 := by
  rw [gaussianNormalizedPhase, norm_div, norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hF)]

/-- Normalized phases converge locally uniformly on the safe chart. -/
theorem tendstoLocallyUniformlyOn_gaussianNormalizedPhase :
    TendstoLocallyUniformlyOn
      (fun x : ℝ => gaussianNormalizedPhase (gaussianEulerContinuumFormation x))
      (gaussianNormalizedPhase xi) (nhdsWithin (0 : ℝ) (Ioi 0))
      gaussianSafeEulerChart := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_gaussianSafeEulerChart]
  intro K hKsafe hK
  have hPhi := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    isOpen_gaussianSafeEulerChart).mp
    tendstoLocallyUniformlyOn_gaussianEulerContinuumFormation K hKsafe hK
  have hNorm : TendstoUniformlyOn
      (fun x : ℝ => fun s : ℂ => (‖gaussianEulerContinuumFormation x s‖ : ℂ))
      (fun s : ℂ => (‖xi s‖ : ℂ)) (nhdsWithin (0 : ℝ) (Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff] at hPhi ⊢
    intro ε hε
    filter_upwards [hPhi ε hε] with x hx s hs
    have h := abs_norm_sub_norm_le (xi s) (gaussianEulerContinuumFormation x s)
    have hx' := hx s hs
    rw [dist_eq_norm] at hx' ⊢
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_le_of_lt h hx'
  have hXiContinuous : ContinuousOn xi K := by
    apply hPhi.continuousOn
    refine Filter.Eventually.frequently ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro s hs
    exact (differentiableAt_gaussianEulerContinuumFormation hx
      (lt_trans zero_lt_one (hKsafe hs))).continuousAt.continuousWithinAt
  have hNormContinuous : ContinuousOn (fun s : ℂ => (‖xi s‖ : ℂ)) K :=
    Complex.continuous_ofReal.continuousOn.comp hXiContinuous.norm
      (fun _ _ => mem_univ _)
  have hXiNe : ∀ s ∈ K, (‖xi s‖ : ℂ) ≠ 0 := by
    intro s hs
    exact_mod_cast norm_ne_zero_iff.mpr (by
      rw [← gaussianEulerContinuumFormationLimit_eq_xi (hKsafe hs)]
      exact mul_ne_zero
        (gaussianArchimedeanHalfFactor_ne_zero
          (lt_trans zero_lt_one (hKsafe hs)))
        (Complex.exp_ne_zero _))
  have hquot := GaloisForLFunctions.HTGeometry.TendstoUniformlyOn.div_of_isCompact_of_ne_zero
    hK hPhi hNorm hXiContinuous hNormContinuous hXiNe
  exact hquot

/-- Normalized-phase velocity of a nonvanishing differentiable complex path. -/
theorem hasDerivAt_gaussianNormalizedPhase_path
    {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (h0 : f t ≠ 0) :
    HasDerivAt (fun u => f u / (‖f u‖ : ℂ))
      ((Complex.I * ((f' / f t).im : ℂ)) * (f t / (‖f t‖ : ℂ))) t := by
  have hconj := GaloisForLFunctions.HTGeometry.hasDerivAt_normalizedConjPhase hf h0
  have h := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hconj
  have hfun : (Complex.conjCLE ∘ fun y =>
      (starRingEnd ℂ) (f y) / (‖f y‖ : ℂ)) =
      fun y => f y / (‖f y‖ : ℂ) := by
    funext u
    simp only [Function.comp_apply, Complex.conjCLE_apply, map_div₀,
      Complex.conj_conj, Complex.conj_ofReal]
  rw [hfun] at h
  refine h.congr_deriv ?_
  change (starRingEnd ℂ)
      ((-Complex.I * ((f' / f t).im : ℂ)) *
        ((starRingEnd ℂ) (f t) / (‖f t‖ : ℂ))) = _
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
    map_div₀, Complex.conj_conj]
  ring

/-- Smooth closed contour carried entirely by the safe Euler chart. -/
structure GaussianSafeContour where
  a : ℝ
  b : ℝ
  path : ℝ → ℂ
  velocity : ℝ → ℂ
  hasDerivAt_path : ∀ t ∈ Icc a b, HasDerivAt path (velocity t) t
  continuousOn_velocity : ContinuousOn velocity (Icc a b)
  closed : path a = path b
  safe : ∀ t ∈ Icc a b, path t ∈ gaussianSafeEulerChart

def gaussianContourPhase (F : ℂ → ℂ) (D : GaussianSafeContour) (t : ℝ) : ℂ :=
  gaussianNormalizedPhase F (D.path t)

def gaussianContourPhaseTangent (F : ℂ → ℂ)
    (D : GaussianSafeContour) (t : ℝ) : ℂ :=
  (Complex.I * ((logDeriv F (D.path t) * D.velocity t).im : ℂ)) *
    gaussianContourPhase F D t

/-- The displayed phase tangent is the actual real derivative along every safe contour. -/
theorem hasDerivAt_gaussianContourPhase
    {F : ℂ → ℂ} (D : GaussianSafeContour) {t : ℝ} (ht : t ∈ Icc D.a D.b)
    (hF : DifferentiableAt ℂ F (D.path t)) (hF0 : F (D.path t) ≠ 0) :
    HasDerivAt (gaussianContourPhase F D)
      (gaussianContourPhaseTangent F D t) t := by
  have hcomp : HasDerivAt (fun u : ℝ => F (D.path u))
      (D.velocity t * deriv F (D.path t)) t :=
    HasDerivAt.scomp t hF.hasDerivAt (D.hasDerivAt_path t ht)
  have hphase := hasDerivAt_gaussianNormalizedPhase_path hcomp hF0
  change HasDerivAt (fun u => F (D.path u) / (‖F (D.path u)‖ : ℂ))
    (gaussianContourPhaseTangent F D t) t
  refine hphase.congr_deriv ?_
  rw [gaussianContourPhaseTangent, gaussianContourPhase, logDeriv_apply]
  congr 3
  field_simp

/-- Safe-contour normalized phases and their actual tangents converge uniformly: the exact
continuous-time `C¹` convergence asserted by `(GECRF.3)`. -/
theorem tendstoUniformlyOn_gaussianContourPhase_c1 (D : GaussianSafeContour) :
    TendstoUniformlyOn
        (fun x : ℝ => gaussianContourPhase (gaussianEulerContinuumFormation x) D)
        (gaussianContourPhase xi D) (nhdsWithin (0 : ℝ) (Ioi 0)) (Icc D.a D.b) ∧
      TendstoUniformlyOn
        (fun x : ℝ => gaussianContourPhaseTangent
          (gaussianEulerContinuumFormation x) D)
        (gaussianContourPhaseTangent xi D) (nhdsWithin (0 : ℝ) (Ioi 0))
        (Icc D.a D.b) := by
  let K : Set ℂ := D.path '' Icc D.a D.b
  have hPathContinuous : ContinuousOn D.path (Icc D.a D.b) :=
    HasDerivAt.continuousOn D.hasDerivAt_path
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hPathContinuous
  have hKsafe : K ⊆ gaussianSafeEulerChart := by
    rintro s ⟨t, ht, rfl⟩
    exact D.safe t ht
  have hPhaseK := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    isOpen_gaussianSafeEulerChart).mp
    tendstoLocallyUniformlyOn_gaussianNormalizedPhase K hKsafe hK
  have hLogK := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    isOpen_gaussianSafeEulerChart).mp
    tendstoLocallyUniformlyOn_logDeriv_gaussianEulerContinuumFormation K hKsafe hK
  have hPhase : TendstoUniformlyOn
      (fun x : ℝ => gaussianContourPhase (gaussianEulerContinuumFormation x) D)
      (gaussianContourPhase xi D) (nhdsWithin (0 : ℝ) (Ioi 0)) (Icc D.a D.b) := by
    rw [Metric.tendstoUniformlyOn_iff] at hPhaseK ⊢
    intro ε hε
    filter_upwards [hPhaseK ε hε] with x hx t ht
    exact hx (D.path t) ⟨t, ht, rfl⟩
  have hLog : TendstoUniformlyOn
      (fun x : ℝ => fun t => logDeriv (gaussianEulerContinuumFormation x) (D.path t))
      (fun t => logDeriv xi (D.path t)) (nhdsWithin (0 : ℝ) (Ioi 0))
      (Icc D.a D.b) := by
    rw [Metric.tendstoUniformlyOn_iff] at hLogK ⊢
    intro ε hε
    filter_upwards [hLogK ε hε] with x hx t ht
    exact hx (D.path t) ⟨t, ht, rfl⟩
  have hLogContinuous : ContinuousOn (fun t => logDeriv xi (D.path t))
      (Icc D.a D.b) := by
    have hXiLogK : ContinuousOn (logDeriv xi) K := by
      apply hLogK.continuousOn
      refine Filter.Eventually.frequently ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hdiff : DifferentiableOn ℂ (gaussianEulerContinuumFormation x)
          gaussianSafeEulerChart := by
        intro s hs
        exact (differentiableAt_gaussianEulerContinuumFormation hx
          (lt_trans zero_lt_one hs)).differentiableWithinAt
      have hzero : ∀ s ∈ K, gaussianEulerContinuumFormation x s ≠ 0 := by
        intro s hs
        exact gaussianEulerContinuumFormation_ne_zero x
          (lt_trans zero_lt_one (hKsafe hs))
      unfold logDeriv
      exact ((hdiff.deriv isOpen_gaussianSafeEulerChart).continuousOn.mono hKsafe).div₀
        (hdiff.continuousOn.mono hKsafe) hzero
    exact ContinuousOn.comp hXiLogK hPathContinuous
      (fun t ht => ⟨t, ht, rfl⟩)
  have hVelocity : TendstoUniformlyOn (fun _ : ℝ => D.velocity) D.velocity
      (nhdsWithin (0 : ℝ) (Ioi 0)) (Icc D.a D.b) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall fun x t ht => by simpa using hε
  have hProduct := GaloisForLFunctions.HTGeometry.TendstoUniformlyOn.mul_of_isCompact
    hLog hVelocity isCompact_Icc hLogContinuous D.continuousOn_velocity
  have hImag : TendstoUniformlyOn
      (fun x : ℝ => fun t =>
        (Complex.I * ((logDeriv (gaussianEulerContinuumFormation x) (D.path t) *
          D.velocity t).im : ℂ)))
      (fun t => Complex.I * ((logDeriv xi (D.path t) * D.velocity t).im : ℂ))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (Icc D.a D.b) := by
    rw [Metric.tendstoUniformlyOn_iff] at hProduct ⊢
    intro ε hε
    filter_upwards [hProduct ε hε] with x hx t ht
    have hxt := hx t ht
    rw [dist_eq_norm] at hxt ⊢
    rw [← mul_sub, norm_mul, norm_I]
    simp only [one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have him : |(logDeriv xi (D.path t) * D.velocity t).im -
        (logDeriv (gaussianEulerContinuumFormation x) (D.path t) *
          D.velocity t).im| ≤
        ‖logDeriv xi (D.path t) * D.velocity t -
          logDeriv (gaussianEulerContinuumFormation x) (D.path t) *
            D.velocity t‖ := by
      rw [← sub_im]
      exact abs_im_le_norm _
    exact lt_of_le_of_lt him hxt
  have hPhaseContinuous : ContinuousOn (gaussianContourPhase xi D) (Icc D.a D.b) := by
    apply hPhase.continuousOn
    refine Filter.Eventually.frequently ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro t ht
    exact (hasDerivAt_gaussianContourPhase D ht
      (differentiableAt_gaussianEulerContinuumFormation hx
        (lt_trans zero_lt_one (D.safe t ht)))
      (gaussianEulerContinuumFormation_ne_zero x
        (lt_trans zero_lt_one (D.safe t ht)))).continuousAt.continuousWithinAt
  have hImagContinuous : ContinuousOn
      (fun t => Complex.I * ((logDeriv xi (D.path t) * D.velocity t).im : ℂ))
      (Icc D.a D.b) := by
    have hmul : ContinuousOn
        (fun t => logDeriv xi (D.path t) * D.velocity t) (Icc D.a D.b) :=
      hLogContinuous.mul D.continuousOn_velocity
    have him : ContinuousOn
        (fun t => (logDeriv xi (D.path t) * D.velocity t).im) (Icc D.a D.b) :=
      Complex.continuous_im.continuousOn.comp hmul (fun _ _ => mem_univ _)
    have hcast : ContinuousOn
        (fun t => ((logDeriv xi (D.path t) * D.velocity t).im : ℂ))
        (Icc D.a D.b) :=
      Complex.continuous_ofReal.continuousOn.comp him (fun _ _ => mem_univ _)
    exact continuousOn_const.mul hcast
  have hTangent := GaloisForLFunctions.HTGeometry.TendstoUniformlyOn.mul_of_isCompact
    hImag hPhase isCompact_Icc hImagContinuous hPhaseContinuous
  exact ⟨hPhase, hTangent⟩

/-! ## Zero winding and reflected transition -/

/-- The normalized rectangle boundary winding of the relative formation. -/
def gaussianFormationRectangleWinding (x : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    rectIntegral (logDeriv (gaussianEulerContinuumFormation x)) z₁ z₂

/-- Every rectangle contained in the open right half-plane has zero formation winding. -/
theorem gaussianFormationRectangleWinding_eq_zero
    {x : ℝ} (hx : 0 < x) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.re) (hz₂ : 0 < z₂.re) :
    gaussianFormationRectangleWinding x z₁ z₂ = 0 := by
  let H : Set ℂ := {z | 0 < z.re}
  have hopen : IsOpen H :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (gaussianEulerContinuumFormation x) H := by
    intro z hz
    exact (differentiableAt_gaussianEulerContinuumFormation hx hz).differentiableWithinAt
  have han : AnalyticOnNhd ℂ (gaussianEulerContinuumFormation x) H :=
    hdiff.analyticOnNhd hopen
  have hsub :
      (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ H := by
    intro z hz
    change 0 < z.re
    have hzre := (Complex.mem_reProdIm.mp hz).1
    have hmin : 0 < min z₁.re z₂.re := lt_min hz₁ hz₂
    rcases mem_uIcc.mp hzre with h | h <;> linarith [min_le_left z₁.re z₂.re,
      min_le_right z₁.re z₂.re]
  have hrect := rectIntegral_logDeriv_multi_zero
    (t := (∅ : Finset Empty))
    (ρ := fun i : Empty => nomatch i)
    (m := fun i : Empty => nomatch i)
    (z₁ := z₁) (z₂ := z₂) (U := H)
    (by simp) hsub han
    (fun z hz => gaussianEulerContinuumFormation_ne_zero x hz)
  have hzero : rectIntegral
      (logDeriv (gaussianEulerContinuumFormation x)) z₁ z₂ = 0 := by
    simpa using hrect
  rw [gaussianFormationRectangleWinding, hzero, mul_zero]

/-- Reflected-chart transition `Gₓ(s)=Φₓ(s)/Φₓ(1-s)`. -/
def gaussianReflectedTransition (x : ℝ) (s : ℂ) : ℂ :=
  gaussianEulerContinuumFormation x s /
    gaussianEulerContinuumFormation x (1 - s)

/-- The reflected transition is holomorphic on the open critical strip. -/
theorem differentiableAt_gaussianReflectedTransition
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DifferentiableAt ℂ (gaussianReflectedTransition x) s := by
  have href : 0 < (1 - s).re := by
    norm_num
    linarith
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by
    fun_prop
  have hden : DifferentiableAt ℂ
      (fun z => gaussianEulerContinuumFormation x (1 - z)) s :=
    (differentiableAt_gaussianEulerContinuumFormation hx href).comp s hinner
  exact (differentiableAt_gaussianEulerContinuumFormation hx hs0).div hden
    (gaussianEulerContinuumFormation_ne_zero x href)

/-- The reflected transition is zero-free on the open critical strip. -/
theorem gaussianReflectedTransition_ne_zero
    (x : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    gaussianReflectedTransition x s ≠ 0 := by
  have href : 0 < (1 - s).re := by
    norm_num
    linarith
  exact div_ne_zero
    (gaussianEulerContinuumFormation_ne_zero x hs0)
    (gaussianEulerContinuumFormation_ne_zero x href)

/-- Reflection acts by reciprocal transition, with no divisor hypothesis. -/
theorem gaussianReflectedTransition_one_sub
    (x : ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    gaussianReflectedTransition x (1 - s) =
      (gaussianReflectedTransition x s)⁻¹ := by
  have href : 0 < (1 - s).re := by
    norm_num
    linarith
  have hnum := gaussianEulerContinuumFormation_ne_zero x hs0
  have hden := gaussianEulerContinuumFormation_ne_zero x href
  rw [gaussianReflectedTransition, gaussianReflectedTransition]
  ring_nf
  field_simp

/-- On the critical line the reflected transition is unitary. -/
theorem norm_gaussianReflectedTransition_critical
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖gaussianReflectedTransition x
      ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ = 1 := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have hsre : s.re = 1 / 2 := by simp [s]
  have hs : 0 < s.re := by rw [hsre]; norm_num
  have href : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · dsimp [s]
      norm_num
    · simp [s]
  have hne := gaussianEulerContinuumFormation_ne_zero x hs
  change ‖gaussianReflectedTransition x s‖ = 1
  rw [gaussianReflectedTransition, href,
    gaussianEulerContinuumFormation_conj hx, norm_div, norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hne)

end
end RHTower
