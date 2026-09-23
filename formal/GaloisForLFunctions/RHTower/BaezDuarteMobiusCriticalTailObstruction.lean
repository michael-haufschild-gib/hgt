import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.RHTower.MobiusLaplaceBoundaryMultiplicity
import GaloisForLFunctions.RHTower.MobiusMertensFiniteSectionEnergy
import GaloisForLFunctions.RHTower.TwistedMertensOrderLowerBound
import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureRH
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.CarrierLineSup
import GaloisForLFunctions.RHTower.MellinHeadChart
import GaloisForLFunctions.RHTower.MobiusPowerSumBoundaryLaplace
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Critical obstruction to raw Möbius Báez--Duarte convergence

The raw modular approximants contain the critical arithmetic defect
`N * deningerHarmonicPartial N ^ 2`.  This file proves that defect cannot tend to zero.

The new bridge is an inverse Abel identity
`M(N) = N H_N - ∑_{n<N} H_n`.  Thus critical-energy decay would imply
`M(N) / sqrt N → 0`, and power-series Abel summation would force the canonical critical
Möbius--Laplace profile to tend to zero.  A sharp Abel final-value theorem then makes the
normalized radial Mellin residue vanish at every critical-line zeta zero.  This contradicts
the denominator-free Mellin identity because `Gamma rho * (rho - 1) ≠ 0`.

Consequently the raw full error and its canonical complementary tail do not converge to zero.
The positive survivor is stronger: each critical energy has a fixed positive floor on a cofinal
subsequence.
-/

open Complex Filter Set ArithmeticFunction MeasureTheory Asymptotics Topology
open GaloisForLFunctions.HTGeometry
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Critical harmonic energy decay also kills the shifted square-root normalization. -/
theorem tendsto_sqrt_succ_mul_deningerHarmonicPartial_zero_of_critical_energy
    (hcrit : Tendsto (fun N : ℕ => (N : ℝ) * deningerHarmonicPartial N ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) + 1) * deningerHarmonicPartial N)
      atTop (𝓝 0) := by
  have hH : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
    simpa [deningerHarmonicLimit_eq_zero] using deningerHarmonicPartial_tendsto
  have henergy : Tendsto
      (fun N : ℕ => ((N : ℝ) + 1) * deningerHarmonicPartial N ^ 2)
      atTop (𝓝 0) := by
    convert hcrit.add (hH.pow 2) using 1
    · funext N
      ring_nf
    · ring_nf
  have hroot := henergy.sqrt
  rw [Real.sqrt_zero] at hroot
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hroot using 1
  funext N
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    ← Real.sqrt_sq_eq_abs (deningerHarmonicPartial N),
    ← Real.sqrt_mul (by positivity)]

/-- Critical harmonic energy decay kills the unshifted square-root normalization. -/
theorem tendsto_sqrt_mul_deningerHarmonicPartial_zero_of_critical_energy
    (hcrit : Tendsto (fun N : ℕ => (N : ℝ) * deningerHarmonicPartial N ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.sqrt N * deningerHarmonicPartial N)
      atTop (𝓝 0) := by
  have hroot := hcrit.sqrt
  rw [Real.sqrt_zero] at hroot
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hroot using 1
  funext N
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    ← Real.sqrt_sq_eq_abs (deningerHarmonicPartial N),
    ← Real.sqrt_mul (Nat.cast_nonneg N)]

/-- Exact inverse Abel identity between Mertens and harmonic Möbius partial sums. -/
theorem sieveMertensM_eq_nat_mul_deningerHarmonicPartial_sub_sum (N : ℕ) :
    (Sieve.mertensM N : ℝ) =
      (N : ℝ) * deningerHarmonicPartial N -
        ∑ i ∈ Finset.range N, deningerHarmonicPartial i := by
  let F : ℕ → ℝ := fun n => (n : ℝ)
  let G : ℕ → ℝ := fun n => ((moebius n : ℤ) : ℝ) / (n : ℝ)
  have hbp := Finset.sum_range_by_parts F G (N + 1)
  have hleft : (∑ i ∈ Finset.range (N + 1), F i * G i) = Sieve.mertensM N := by
    rw [Sieve.mertensM]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [F, G]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · have hir : (0 : ℝ) < i := by exact_mod_cast hi0
      field_simp
  have hpartial (i : ℕ) : (∑ j ∈ Finset.range (i + 1), G j) =
      deningerHarmonicPartial i := by
    rfl
  simp only [smul_eq_mul] at hbp
  rw [hleft] at hbp
  rw [hpartial N] at hbp
  have hdiff (i : ℕ) : F (i + 1) - F i = 1 := by
    dsimp only [F]
    push_cast
    ring_nf
  simp_rw [hdiff, one_mul, hpartial] at hbp
  simpa using hbp

private theorem sum_inv_sqrt_succ_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / Real.sqrt ((n : ℝ) + 1)) ≤
      2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hkey : 1 / Real.sqrt ((N : ℝ) + 1) ≤
          2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ)) := by
        have hpos : (0 : ℝ) < Real.sqrt ((N : ℝ) + 1) :=
          Real.sqrt_pos.mpr (by positivity)
        have hs : Real.sqrt (N : ℝ) * Real.sqrt ((N : ℝ) + 1) ≤
            (N : ℝ) + 1 / 2 := by
          rw [← Real.sqrt_mul (Nat.cast_nonneg N)]
          calc
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) ≤
                Real.sqrt (((N : ℝ) + 1 / 2) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith)
            _ = (N : ℝ) + 1 / 2 := Real.sqrt_sq (by positivity)
        have hself : Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) =
            (N : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
        rw [div_le_iff₀ hpos]
        nlinarith
      have hcast : Real.sqrt ((N + 1 : ℕ) : ℝ) =
          Real.sqrt ((N : ℝ) + 1) := by
        push_cast
        ring_nf
      rw [hcast]
      linarith

private theorem tendsto_sqrtWeighted_error_zero {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, e n / Real.sqrt ((n : ℝ) + 1)) / Real.sqrt N)
      atTop (𝓝 0) := by
  have heo : (fun n : ℕ => e n / Real.sqrt ((n : ℝ) + 1)) =o[atTop]
      (fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1)) := by
    apply (isLittleO_iff_tendsto (fun n hzero => by
      exfalso
      exact (by positivity : (0 : ℝ) < 1 / Real.sqrt ((n : ℝ) + 1)).ne' hzero)).2
    convert he using 1
    funext n
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hweight : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / Real.sqrt ((n : ℝ) + 1))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ GaloisForLFunctions.tendsto_harmonic_cast_atTop
    filter_upwards with N
    rw [harmonic]
    push_cast
    apply Finset.sum_le_sum
    intro n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
    have hspos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsle : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 :=
      Real.sqrt_le_self_iff.mpr (Or.inr hx)
    simpa [one_div] using one_div_le_one_div_of_le hspos hsle
  have hsum := heo.sum_range (fun n => by positivity) hweight
  have hweightO :
      (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / Real.sqrt ((n : ℝ) + 1))
        =O[atTop] (fun N : ℕ => Real.sqrt N) := by
    apply IsBigO.of_bound 2
    filter_upwards with N
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity),
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sum_inv_sqrt_succ_le N
  exact (hsum.trans_isBigO hweightO).tendsto_div_nhds_zero

/-- Critical harmonic energy decay would force the forbidden law `M(N) = o(sqrt N)`. -/
theorem tendsto_sieveMertensM_div_sqrt_zero_of_critical_energy
    (hcrit : Tendsto (fun N : ℕ => (N : ℝ) * deningerHarmonicPartial N ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Sieve.mertensM N : ℝ) / Real.sqrt N)
      atTop (𝓝 0) := by
  have heSucc := tendsto_sqrt_succ_mul_deningerHarmonicPartial_zero_of_critical_energy hcrit
  have he := tendsto_sqrt_mul_deningerHarmonicPartial_zero_of_critical_energy hcrit
  have hsum := tendsto_sqrtWeighted_error_zero heSucc
  have hsub := he.sub hsum
  have heq :
      (fun N : ℕ => Real.sqrt N * deningerHarmonicPartial N -
        (∑ n ∈ Finset.range N,
          (Real.sqrt ((n : ℝ) + 1) * deningerHarmonicPartial n) /
            Real.sqrt ((n : ℝ) + 1)) / Real.sqrt N) =ᶠ[atTop]
      (fun N : ℕ => (Sieve.mertensM N : ℝ) / Real.sqrt N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsqrt : Real.sqrt (N : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
    rw [sieveMertensM_eq_nat_mul_deningerHarmonicPartial_sub_sum]
    have hsumEq :
        (∑ n ∈ Finset.range N,
          (Real.sqrt ((n : ℝ) + 1) * deningerHarmonicPartial n) /
            Real.sqrt ((n : ℝ) + 1)) =
          ∑ n ∈ Finset.range N, deningerHarmonicPartial n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hsumEq]
    field_simp [hsqrt]
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    ring_nf
  simpa using hsub.congr' heq

private theorem norm_partialSumSeq_mobiusCoeff (N : ℕ) :
    ‖partialSumSeq mobiusCoeff N‖ = |Sieve.mertensM N| := by
  have h := congrArg norm (mobiusMertensPartialSum_eq_sieveMertensM N)
  simpa [mobiusMertensPartialSum, mobiusComplexCoefficient, mobiusCoeff,
    partialSumSeq, Complex.norm_real, Real.norm_eq_abs] using h

private theorem norm_source_le_of_mertens_tail
    (K : ℕ) {delta x : ℝ} (hdelta : 0 ≤ delta) (hx : 0 < x) (hx1 : x ≤ 1)
    (hM : ∀ n : ℕ, K ≤ n →
      |Sieve.mertensM n| ≤ delta * Real.sqrt ((n : ℝ) + 1)) :
    ‖mobiusDiscreteLaplaceTransform x‖ ≤
      x * ((∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) +
        delta * mixedSubpowerAbelConstant (1 / 2) *
          (1 / x) ^ (3 / 2 : ℝ)) := by
  set q : ℂ := ((Real.exp (-x) : ℝ) : ℂ) with hq
  have hq0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hq1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hraw : Summable fun n : ℕ => ‖mobiusCoeff n * q ^ n‖ := by
    simpa [hq] using summable_norm_mobiusCoeff_mul_pow hx
  have hpartial : Summable fun n : ℕ =>
      ‖partialSumSeq mobiusCoeff n * q ^ n‖ :=
    summable_norm_partialSumSeq_mul_pow norm_mobiusCoeff_le_one hx
  have hid := tsum_partialSumSeq_mul_pow (a := mobiusCoeff) hqnorm hraw
  have hsource : mobiusDiscreteLaplaceTransform x =
      (1 - q) * ∑' n : ℕ, partialSumSeq mobiusCoeff n * q ^ n := by
    rw [mobiusDiscreteLaplaceTransform_eq_tsum]
    exact hid.symm
  have hmomentSummable :=
    (summable_natSucc_rpow_exp_neg_and_tsum_le (r := (1 / 2 : ℝ))
      (by norm_num) hx).1
  have htailSummable : Summable fun n : ℕ =>
      ‖partialSumSeq mobiusCoeff (n + K) * q ^ (n + K)‖ := by
    simpa [Function.comp_def] using
      hpartial.comp_injective (i := fun n : ℕ => n + K)
        (fun _ _ h => Nat.add_right_cancel h)
  have htailMajorSummable : Summable fun n : ℕ =>
      delta * (((n + K : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
        Real.exp (-(((n + K : ℕ) : ℝ) * x)) := by
    have hs := hmomentSummable.comp_injective (i := fun n : ℕ => n + K)
      (fun _ _ h => Nat.add_right_cancel h)
    simpa only [Function.comp_apply, mul_assoc] using hs.mul_left delta
  have htail :
      (∑' n : ℕ, ‖partialSumSeq mobiusCoeff (n + K) * q ^ (n + K)‖) ≤
        delta * ∑' n : ℕ,
          (((n + K : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
            Real.exp (-(((n + K : ℕ) : ℝ) * x)) := by
    calc
      _ ≤ ∑' n : ℕ, delta * (((n + K : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
          Real.exp (-(((n + K : ℕ) : ℝ) * x)) := by
        apply htailSummable.tsum_le_tsum
        · intro n
          rw [norm_mul, norm_pow, hq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hq0, ← Real.exp_nat_mul]
          have hcoeff := hM (n + K) (Nat.le_add_left K n)
          rw [norm_partialSumSeq_mobiusCoeff]
          rw [Real.sqrt_eq_rpow] at hcoeff
          simpa [mul_neg] using
            mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
        · exact htailMajorSummable
      _ = delta * ∑' n : ℕ,
          (((n + K : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
            Real.exp (-(((n + K : ℕ) : ℝ) * x)) := by
        simp_rw [mul_assoc]
        rw [tsum_mul_left]
  have hmomentTail :
      (∑' n : ℕ, (((n + K : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
        Real.exp (-(((n + K : ℕ) : ℝ) * x))) ≤
      ∑' n : ℕ, ((n : ℝ) + 1) ^ (1 / 2 : ℝ) *
        Real.exp (-((n : ℝ) * x)) := by
    have hsplit := hmomentSummable.sum_add_tsum_nat_add K
    rw [← hsplit]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => by positivity)
  have hmoment :=
    tsum_natSucc_rpow_exp_neg_le_mixedSubpowerAbelConstant
      (theta := (1 / 2 : ℝ)) (by norm_num) hx hx1
  have hseries :
      ‖∑' n : ℕ, partialSumSeq mobiusCoeff n * q ^ n‖ ≤
        (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) +
          delta * mixedSubpowerAbelConstant (1 / 2) * (1 / x) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ, ‖partialSumSeq mobiusCoeff n * q ^ n‖ :=
        norm_tsum_le_tsum_norm hpartial
      _ = (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n * q ^ n‖) +
          ∑' n : ℕ, ‖partialSumSeq mobiusCoeff (n + K) * q ^ (n + K)‖ := by
        exact (hpartial.sum_add_tsum_nat_add K).symm
      _ ≤ (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) +
          delta * ∑' n : ℕ, (((n + K : ℕ) : ℝ) + 1) ^ (1 / 2 : ℝ) *
            Real.exp (-(((n + K : ℕ) : ℝ) * x)) := by
        gcongr
        ·
          rw [norm_mul, norm_pow, hq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hq0]
          have hpow : Real.exp (-x) ^ n ≤ 1 := pow_le_one₀ hq0 hq1.le
          simpa using mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ ≤ (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) +
          delta * (mixedSubpowerAbelConstant (1 / 2) *
            (1 / x) ^ ((1 / 2 : ℝ) + 1)) := by
        gcongr
        exact hmomentTail.trans hmoment
      _ = _ := by norm_num; ring_nf
  rw [hsource, norm_mul]
  have hfac : ‖(1 : ℂ) - q‖ ≤ x := by
    have hreal : (1 : ℂ) - q = ((1 - Real.exp (-x) : ℝ) : ℂ) := by
      rw [hq]
      push_cast
      ring_nf
    rw [hreal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hq1.le)]
    exact one_sub_exp_neg_le x
  exact mul_le_mul hfac hseries (norm_nonneg _) (by positivity)

private theorem norm_criticalProfile_le_of_mertens_tail
    (K : ℕ) {delta y : ℝ} (hdelta : 0 ≤ delta) (hy : 0 ≤ y)
    (hM : ∀ n : ℕ, K ≤ n →
      |Sieve.mertensM n| ≤ delta * Real.sqrt ((n : ℝ) + 1)) :
    ‖mobiusLaplaceCriticalProfile y‖ ≤
      (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) *
          Real.exp (-(3 * y / 2)) +
        delta * mixedSubpowerAbelConstant (1 / 2) := by
  let x := Real.exp (-y)
  have hx : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsource := norm_source_le_of_mertens_tail K hdelta hx hx1 hM
  have hxinv : 1 / x = Real.exp y := by
    dsimp only [x]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring_nf
  have hxpow : (1 / x) ^ (3 / 2 : ℝ) = Real.exp (3 * y / 2) := by
    rw [hxinv, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring_nf
  rw [mobiusLaplaceCriticalProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  dsimp only [x] at hsource hxpow ⊢
  have hscaled := mul_le_mul_of_nonneg_left hsource
    (show 0 ≤ Real.exp (-y / 2) from (Real.exp_pos _).le)
  rw [hxpow] at hscaled
  calc
    Real.exp (-y / 2) * ‖mobiusDiscreteLaplaceTransform (Real.exp (-y))‖ ≤
        Real.exp (-y / 2) *
          (Real.exp (-y) *
            ((∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) +
              delta * mixedSubpowerAbelConstant (1 / 2) * Real.exp (3 * y / 2))) :=
      hscaled
    _ = (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) *
          Real.exp (-(3 * y / 2)) +
        delta * mixedSubpowerAbelConstant (1 / 2) := by
      have hheadExp : Real.exp (-y / 2) * Real.exp (-y) =
          Real.exp (-(3 * y / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
      have htailExp : Real.exp (-y / 2) * Real.exp (-y) *
          Real.exp (3 * y / 2) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        convert Real.exp_zero
        ring_nf
      have hcancel : Real.exp (-(3 * y / 2)) * Real.exp (3 * y / 2) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero
        ring_nf
      calc
        _ = (Real.exp (-y / 2) * Real.exp (-y)) *
              (∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖) +
            delta * mixedSubpowerAbelConstant (1 / 2) *
              (Real.exp (-y / 2) * Real.exp (-y) * Real.exp (3 * y / 2)) := by ring_nf
        _ = _ := by rw [hheadExp, hcancel]; ring_nf

/-- The forbidden Mertens law transfers to little-o decay of the critical Laplace profile. -/
theorem tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_energy
    (hcrit : Tendsto (fun N : ℕ => (N : ℝ) * deningerHarmonicPartial N ^ 2)
      atTop (𝓝 0)) :
    Tendsto mobiusLaplaceCriticalProfile atTop (𝓝 0) := by
  have hMlim := tendsto_sieveMertensM_div_sqrt_zero_of_critical_energy hcrit
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let A := mixedSubpowerAbelConstant (1 / 2)
  have hA : 0 ≤ A := mixedSubpowerAbelConstant_nonneg (by norm_num)
  let delta := epsilon / (2 * (A + 1))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hMnorm := hMlim.norm
  rw [norm_zero, Metric.tendsto_atTop] at hMnorm
  obtain ⟨K₀, hK₀⟩ := hMnorm delta hdelta
  let K := max K₀ 1
  have hMtail : ∀ n : ℕ, K ≤ n →
      |Sieve.mertensM n| ≤ delta * Real.sqrt ((n : ℝ) + 1) := by
    intro n hn
    have hnK₀ : K₀ ≤ n := (le_max_left _ _).trans hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hspos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast hn1)
    have hsmall := hK₀ n hnK₀
    rw [Real.dist_eq, sub_zero, abs_norm, norm_div, Real.norm_eq_abs,
      Real.norm_eq_abs] at hsmall
    rw [abs_of_pos hspos] at hsmall
    have hMn : |Sieve.mertensM n| < delta * Real.sqrt n :=
      (div_lt_iff₀ hspos).mp hsmall
    have hsle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    exact hMn.le.trans (mul_le_mul_of_nonneg_left hsle hdelta.le)
  let P := ∑ n ∈ Finset.range K, ‖partialSumSeq mobiusCoeff n‖
  have hP : 0 ≤ P := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hhead : Tendsto (fun y : ℝ => P * Real.exp (-(3 * y / 2)))
      atTop (𝓝 0) := by
    have htop : Tendsto (fun y : ℝ => 3 * y / 2) atTop atTop := by
      rw [show (fun y : ℝ => 3 * y / 2) = fun y => (3 / 2 : ℝ) * y by
        funext y; ring_nf]
      exact (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 3 / 2)).mpr
        tendsto_id
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop).const_mul P
  have hheadMetric := (Metric.tendsto_atTop.1 hhead) (epsilon / 2) (by positivity)
  obtain ⟨Y₀, hY₀⟩ := hheadMetric
  refine ⟨max Y₀ 0, ?_⟩
  intro y hy
  have hyY₀ : Y₀ ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 ≤ y := (le_max_right _ _).trans hy
  have hbound := norm_criticalProfile_le_of_mertens_tail K hdelta.le hy0 hMtail
  change dist (mobiusLaplaceCriticalProfile y) 0 < epsilon
  rw [dist_zero_right]
  have hheadSmall := hY₀ y hyY₀
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hP (Real.exp_pos _).le)] at hheadSmall
  have htail : delta * A ≤ epsilon / 2 := by
    dsimp only [delta]
    have hden : 0 < 2 * (A + 1) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  exact hbound.trans_lt (by linarith)

private theorem halfDecay_of_profile_tendsto_zero
    (hprofile : Tendsto mobiusLaplaceCriticalProfile atTop (𝓝 0)) :
    MobiusDiscreteLaplaceHalfDecay := by
  have hevent : ∀ᶠ y : ℝ in atTop, ‖mobiusLaplaceCriticalProfile y‖ < 1 := by
    have := hprofile.eventually (Metric.ball_mem_nhds 0 zero_lt_one)
    filter_upwards [this] with y hy
    simpa [Complex.dist_eq] using hy
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hevent
  let Y := max Y₀ 0
  have hY0 : 0 ≤ Y := le_max_right _ _
  refine ⟨1, Real.exp (-Y), zero_le_one, Real.exp_pos _, ?_⟩
  intro x hx hxd
  let y := -Real.log x
  have hyY : Y < y := by
    dsimp only [y]
    have hlog := Real.strictMonoOn_log
      (show x ∈ Ioi (0 : ℝ) from hx)
      (show Real.exp (-Y) ∈ Ioi (0 : ℝ) by
        change 0 < Real.exp (-Y)
        positivity) hxd
    rw [Real.log_exp] at hlog
    linarith
  have hprof := (hY₀ y ((le_max_left _ _).trans hyY.le)).le
  have hxy : Real.exp (-y) = x := by
    dsimp only [y]
    rw [neg_neg, Real.exp_log hx]
  have hhalf : Real.exp (-y / 2) = Real.sqrt x := by
    dsimp only [y]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring_nf
  rw [mobiusLaplaceCriticalProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hxy, hhalf] at hprof
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [one_mul, show x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hx.le]
    simp only [one_div]]
  rw [le_div_iff₀ hspos]
  simpa [mul_comm] using hprof

private theorem continuous_mobiusLaplaceCriticalProfile :
    Continuous mobiusLaplaceCriticalProfile := by
  rw [continuous_iff_continuousAt]
  intro y
  change ContinuousAt (fun y : ℝ =>
    (Real.exp (-y / 2) : ℂ) *
      mobiusDiscreteLaplaceTransform (Real.exp (-y))) y
  apply ContinuousAt.mul
  · fun_prop
  · have hx : Real.exp (-y) ∈ Ioi (0 : ℝ) := by
      change 0 < Real.exp (-y)
      positivity
    have hsrc := continuousOn_mobiusDiscreteLaplaceTransform.continuousAt
      (isOpen_Ioi.mem_nhds hx)
    have hinner : ContinuousAt (fun u : ℝ => Real.exp (-u)) y := by fun_prop
    simpa [Function.comp_def] using hsrc.comp_of_eq hinner rfl

private theorem tendsto_mul_laplaceRay_of_tendsto_zero
    {f : ℝ → ℂ} (hfcont : Continuous f) (hf : Tendsto f atTop (𝓝 0))
    {tau : ℂ} (htau : tau.re = 0) :
    Tendsto (fun r : ℝ => (r : ℂ) * laplaceRay f (tau + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro epsilon hepsilon
  have heta : 0 < epsilon / 4 := by positivity
  have hsmallEventually : ∀ᶠ y : ℝ in atTop, ‖f y‖ < epsilon / 4 := by
    have := hf.eventually (Metric.ball_mem_nhds 0 heta)
    filter_upwards [this] with y hy
    simpa [Complex.dist_eq] using hy
  obtain ⟨Y₀, hY₀⟩ := (eventually_atTop.1 hsmallEventually)
  let Y := max Y₀ 0
  have hY0 : 0 ≤ Y := le_max_right _ _
  have hsmall : ∀ y : ℝ, Y ≤ y → ‖f y‖ < epsilon / 4 := by
    intro y hy
    exact hY₀ y ((le_max_left _ _).trans hy)
  have hcompact : IsCompact (Icc (0 : ℝ) Y) := isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hcompact.bddAbove_image hfcont.norm.continuousOn
  let B := max B₀ 0 + 1
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hB : ∀ y ∈ Ioc (0 : ℝ) Y, ‖f y‖ ≤ B := by
    intro y hy
    have hyIcc : y ∈ Icc (0 : ℝ) Y := ⟨hy.1.le, hy.2⟩
    have hleB₀ : ‖f y‖ ≤ B₀ := hB₀ ⟨y, hyIcc, rfl⟩
    exact hleB₀.trans (by dsimp only [B]; linarith [le_max_left B₀ 0])
  let delta := min (1 / 4) (epsilon / (4 * (B * (Y + 1) + 1)))
  have hdelta : 0 < delta := lt_min (by norm_num) (by positivity)
  refine ⟨delta, hdelta, ?_⟩
  intro r hrPosMem hrdist
  have hrPos : 0 < r := hrPosMem
  have hrδ : r < delta := by simpa [Real.dist_eq, abs_of_pos hrPos] using hrdist
  have hrSmall : r < 1 / 4 := hrδ.trans_le (min_le_left _ _)
  let w : ℂ := tau + (r : ℂ)
  have hwre : w.re = r := by simp [w, htau]
  have hwpos : 0 < w.re := by rw [hwre]; exact hrPos
  have hheadInt : IntegrableOn (fun y : ℝ => f y * expRay w y) (Ioc 0 Y) := by
    exact ((hfcont.mul (continuous_expRay w)).integrableOn_Icc).mono_set
      (fun y hy => ⟨hy.1.le, hy.2⟩)
  have htailInt : IntegrableOn (fun y : ℝ => f y * expRay w y) (Ioi Y) := by
    have hmajor := (integrableOn_Ioi_exp_neg_mul_shift hrPos Y).const_mul (epsilon / 4)
    apply Integrable.mono' hmajor
    · exact (hfcont.mul (continuous_expRay w)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [norm_mul, norm_expRay, hwre]
      have hfy := (hsmall y hy.le).le
      exact mul_le_mul hfy le_rfl (Real.exp_pos _).le (by positivity)
  have hsplit : laplaceRay f w =
      (∫ y : ℝ in Ioc 0 Y, f y * expRay w y) +
        ∫ y : ℝ in Ioi Y, f y * expRay w y := by
    rw [laplaceRay]
    rw [← Ioc_union_Ioi_eq_Ioi hY0]
    exact setIntegral_union (by
      rw [disjoint_left]
      intro y hy hy'
      exact (not_lt_of_ge hy.2) hy') measurableSet_Ioi hheadInt htailInt
  have hheadNorm : ‖∫ y : ℝ in Ioc 0 Y, f y * expRay w y‖ ≤ B * Y := by
    calc
      _ ≤ ∫ y : ℝ in Ioc 0 Y, ‖f y * expRay w y‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _y : ℝ in Ioc 0 Y, B := by
        apply MeasureTheory.integral_mono_ae hheadInt.norm
          (integrableOn_const (C := B) (hs := measure_Ioc_lt_top.ne))
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        rw [norm_mul, norm_expRay, hwre]
        have hexp : Real.exp (-(r * y)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hrPos, hy.1])
        exact (mul_le_mul (hB y hy) hexp (Real.exp_pos _).le (by positivity)).trans_eq
          (mul_one B)
      _ = B * Y := by simp [hY0]; ring_nf
  have htailNorm : ‖∫ y : ℝ in Ioi Y, f y * expRay w y‖ ≤
      (epsilon / 4) * (Real.exp (-(r * Y)) / r) := by
    calc
      _ ≤ ∫ y : ℝ in Ioi Y, ‖f y * expRay w y‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y : ℝ in Ioi Y, (epsilon / 4) * Real.exp (-(r * y)) := by
        apply MeasureTheory.integral_mono_ae htailInt.norm
          ((integrableOn_Ioi_exp_neg_mul_shift hrPos Y).const_mul (epsilon / 4))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        rw [norm_mul, norm_expRay, hwre]
        exact mul_le_mul (hsmall y hy.le).le le_rfl (Real.exp_pos _).le heta.le
      _ = (epsilon / 4) * (Real.exp (-(r * Y)) / r) := by
        rw [integral_const_mul, integral_Ioi_exp_neg_mul_shift hrPos Y]
  rw [show tau + (r : ℂ) = w from rfl, hsplit, mul_add]
  rw [Complex.dist_eq, sub_zero]
  have hheadScaled : ‖(r : ℂ) * ∫ y : ℝ in Ioc 0 Y, f y * expRay w y‖ <
      epsilon / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
    calc
      r * ‖∫ y : ℝ in Ioc 0 Y, f y * expRay w y‖ ≤ r * (B * Y) :=
        mul_le_mul_of_nonneg_left hheadNorm hrPos.le
      _ < epsilon / 2 := by
        have hrδ : r < epsilon / (4 * (B * (Y + 1) + 1)) :=
          hrδ.trans_le (min_le_right _ _)
        have hBY : B * Y ≤ B * (Y + 1) + 1 := by nlinarith [hBpos, hY0]
        have hden : 0 < 4 * (B * (Y + 1) + 1) := by positivity
        have hrδ' := (lt_div_iff₀ hden).mp hrδ
        nlinarith
  have htailScaled : ‖(r : ℂ) * ∫ y : ℝ in Ioi Y, f y * expRay w y‖ ≤
      epsilon / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
    calc
      r * ‖∫ y : ℝ in Ioi Y, f y * expRay w y‖ ≤
          r * ((epsilon / 4) * (Real.exp (-(r * Y)) / r)) :=
        mul_le_mul_of_nonneg_left htailNorm hrPos.le
      _ = (epsilon / 4) * Real.exp (-(r * Y)) := by field_simp
      _ ≤ epsilon / 4 := by
        have hneg : -(r * Y) ≤ 0 :=
          neg_nonpos.mpr (mul_nonneg hrPos.le hY0)
        simpa using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr hneg) heta.le
  exact (norm_add_le _ _).trans_lt (by linarith)

private theorem mobius_mellinHead_eq_laplaceRay (s : ℂ) :
    (∫ x : ℝ in Ioc 0 1,
      (x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x) =
      laplaceRay mobiusLaplaceCriticalProfile (s - 1 / 2) := by
  have h := mellinHead_eq_laplaceRay (a := (1 : ℝ)) one_pos
    mobiusDiscreteLaplaceTransform (1 - s)
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc] at h
  have hchart : logChartHead 1 mobiusDiscreteLaplaceTransform =
      mobiusLaplaceCriticalProfile := by
    funext y
    rw [logChartHead, mobiusLaplaceCriticalProfile]
    norm_num
  rw [hchart] at h
  calc
    (∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x) =
        ∫ x : ℝ in Ioc 0 1,
          (x : ℂ) ^ (-(1 - s)) * mobiusDiscreteLaplaceTransform x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      rw [smul_eq_mul]
      congr 2
      ring_nf
    _ = ((1 : ℝ) : ℂ) ^ (1 / 2 - (1 - s)) *
          laplaceRay mobiusLaplaceCriticalProfile (1 / 2 - (1 - s)) := h
    _ = laplaceRay mobiusLaplaceCriticalProfile (s - 1 / 2) := by
      simp
      congr 1
      ring_nf

private theorem norm_mobius_mellinTail_le
    (hdecay : MobiusDiscreteLaplaceHalfDecay) {rho : ℂ}
    (hrho : rho.re = 1 / 2) {r : ℝ} (hr : 0 < r) (hrHalf : r < 1 / 2) :
    ‖∫ x : ℝ in Ioi 1,
      (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x‖ ≤
        1 / (1 / 2 - r) := by
  let s : ℂ := rho + (r : ℂ)
  have hsRe : s.re = 1 / 2 + r := by simp [s, hrho]
  have hsHalf : 1 / 2 < s.re := by rw [hsRe]; linarith
  have hconv : MellinConvergent mobiusDiscreteLaplaceTransform s :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 1 / 2) (by norm_num)
      mobiusDiscreteLaplaceTransform_locallyIntegrableOn
      mobiusDiscreteLaplaceTransform_isBigO_exp_neg hdecay.isBigO hsHalf
  let F : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x
  have hFtail : IntegrableOn (fun x => ‖F x‖) (Ioi 1) := by
    have hFint : IntegrableOn F (Ioi 0) := by
      simpa only [MellinConvergent, F] using hconv
    exact (hFint.mono_set (Ioi_subset_Ioi zero_le_one)).norm
  have hmajor : IntegrableOn (fun x : ℝ => x ^ (r - 3 / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  calc
    ‖∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x‖ ≤
        ∫ x : ℝ in Ioi 1, ‖F x‖ := by
      change ‖∫ x : ℝ in Ioi 1, F x‖ ≤ _
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 1, x ^ (r - 3 / 2) := by
      apply MeasureTheory.integral_mono_ae hFtail hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxPos : 0 < x := zero_lt_one.trans hx
      change ‖(x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x‖ ≤ _
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
        Complex.sub_re, Complex.one_re, hsRe]
      calc
        x ^ (1 / 2 + r - 1) * ‖mobiusDiscreteLaplaceTransform x‖ ≤
            x ^ (1 / 2 + r - 1) * (1 / x) :=
          mul_le_mul_of_nonneg_left
            (norm_mobiusDiscreteLaplaceTransform_le_inv hxPos)
            (Real.rpow_nonneg hxPos.le _)
        _ = x ^ (r - 3 / 2) := by
          calc
            x ^ (1 / 2 + r - 1) * (1 / x) =
                x ^ (1 / 2 + r - 1) * x ^ (-1 : ℝ) := by
              simp only [one_div, Real.rpow_neg_one]
            _ = x ^ ((1 / 2 + r - 1) + (-1 : ℝ)) := by
              rw [Real.rpow_add hxPos]
            _ = x ^ (r - 3 / 2) := by
              congr 1
              ring_nf
    _ = 1 / (1 / 2 - r) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : r - 3 / 2 < -1) zero_lt_one,
        Real.one_rpow, show r - 3 / 2 + 1 = -(1 / 2 - r) by ring_nf]
      field_simp

private theorem tendsto_mul_mobius_mellinTail_zero
    (hdecay : MobiusDiscreteLaplaceHalfDecay) {rho : ℂ}
    (hrho : rho.re = 1 / 2) :
    Tendsto (fun r : ℝ => (r : ℂ) *
      ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x)
      (𝓝[>] 0) (𝓝 0) := by
  let T : ℝ → ℂ := fun r =>
    ∫ x : ℝ in Ioi 1,
      (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x
  have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ T) := by
    apply isBoundedUnder_of_eventually_le (a := 4)
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 4 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrSmall
    have htail := norm_mobius_mellinTail_le hdecay hrho hr (by linarith)
    change ‖T r‖ ≤ 4
    refine htail.trans ?_
    rw [div_le_iff₀ (by linarith : 0 < 1 / 2 - r)]
    linarith
  have hrzero : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds using 1
    norm_num
  have hprod := Filter.isBoundedUnder_le_mul_tendsto_zero hbounded hrzero
  exact hprod.congr' (Filter.Eventually.of_forall fun r => by
    dsimp only [T, Function.comp_apply]
    ring_nf)

private theorem tendsto_mul_mobius_mellin_zero_of_profile
    (hprofile : Tendsto mobiusLaplaceCriticalProfile atTop (𝓝 0))
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    Tendsto (fun r : ℝ => (r : ℂ) *
      mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  have hdecay := halfDecay_of_profile_tendsto_zero hprofile
  let tau : ℂ := rho - 1 / 2
  have htau : tau.re = 0 := by simp [tau, hrho]
  have hheadRaw := tendsto_mul_laplaceRay_of_tendsto_zero
    continuous_mobiusLaplaceCriticalProfile hprofile htau
  have hhead : Tendsto (fun r : ℝ => (r : ℂ) *
      ∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x)
      (𝓝[>] 0) (𝓝 0) := by
    refine hheadRaw.congr' (Filter.Eventually.of_forall fun r => ?_)
    dsimp only
    rw [mobius_mellinHead_eq_laplaceRay]
    congr 2
    dsimp only [tau]
    ring_nf
  have htail := tendsto_mul_mobius_mellinTail_zero hdecay hrho
  have hsum := hhead.add htail
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrPos : 0 < r := hr
  have hsHalf : 1 / 2 < (rho + (r : ℂ)).re := by simp [hrho, hrPos]
  have hconv : MellinConvergent mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 1 / 2) (by norm_num)
      mobiusDiscreteLaplaceTransform_locallyIntegrableOn
      mobiusDiscreteLaplaceTransform_isBigO_exp_neg hdecay.isBigO hsHalf
  have hFint : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x) (Ioi 0) := by
    simpa only [MellinConvergent] using hconv
  have hheadInt : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x)
      (Ioc 0 1) := hFint.mono_set (fun _ hx => hx.1)
  have htailInt : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x)
      (Ioi 1) := hFint.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsplit : mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) =
      (∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x) +
      ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ (rho + (r : ℂ) - 1) • mobiusDiscreteLaplaceTransform x := by
    rw [mellin]
    have hcover : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
    rw [← hcover]
    exact setIntegral_union (by
      rw [disjoint_left]
      intro x hx hxt
      exact (not_lt_of_ge hx.2) hxt) measurableSet_Ioi hheadInt htailInt
  rw [hsplit, mul_add]

private theorem tendsto_ofReal_nhdsGT_zero_nhdsNE_zero :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.ne'

/-- A critical-line zeta zero forbids vanishing of the canonical critical Laplace profile. -/
theorem not_tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_zeta_zero
    {rho : ℂ} (hrho : rho.re = 1 / 2) (hzero : riemannZeta rho = 0) :
    ¬ Tendsto mobiusLaplaceCriticalProfile atTop (𝓝 0) := by
  intro hprofile
  have hdecay := halfDecay_of_profile_tendsto_zero hprofile
  have hmellinZero := tendsto_mul_mobius_mellin_zero_of_profile hprofile hrho
  have hrhoPos : 0 < rho.re := by rw [hrho]; norm_num
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
  have hunitZero : zetaResidueUnit rho = 0 := by
    simp [zetaResidueUnit, hrhoOne, hzero]
  have hunitDeriv : HasDerivAt zetaResidueUnit (deriv zetaResidueUnit rho) rho :=
    (analyticAt_zetaResidueUnit rho).differentiableAt.hasDerivAt
  have hslopeComplex := hunitDeriv.tendsto_slope_zero
  have hslope : Tendsto
      (fun r : ℝ => (r : ℂ)⁻¹ * zetaResidueUnit (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 (deriv zetaResidueUnit rho)) := by
    have h := hslopeComplex.comp tendsto_ofReal_nhdsGT_zero_nhdsNE_zero
    simpa [hunitZero, smul_eq_mul] using! h
  have hproductZero : Tendsto
      (fun r : ℝ =>
        ((r : ℂ) * mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))) *
          ((r : ℂ)⁻¹ * zetaResidueUnit (rho + (r : ℂ))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hmellinZero.mul hslope
  have hmellinUnitZero : Tendsto
      (fun r : ℝ =>
        mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
          zetaResidueUnit (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    refine hproductZero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    field_simp
  have hcanonicalIdentity :=
    mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_analyticOnNhd
      (analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform hdecay)
  have hrightZero : Tendsto
      (fun r : ℝ => Complex.Gamma (rho + (r : ℂ)) * (rho + (r : ℂ) - 1))
      (𝓝[>] 0) (𝓝 0) := by
    refine hmellinUnitZero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply hcanonicalIdentity
    rw [mem_rightHalf]
    norm_num [Complex.add_re, hrho]
    exact hr
  have hnotGammaPole : ∀ m : ℕ, rho ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hray : Tendsto (fun r : ℝ => rho + (r : ℂ)) (𝓝[>] 0) (𝓝 rho) := by
    simpa using!
      ((continuous_const.add Complex.continuous_ofReal).tendsto 0).mono_left
        nhdsWithin_le_nhds
  have hrightActual : Tendsto
      (fun r : ℝ => Complex.Gamma (rho + (r : ℂ)) * (rho + (r : ℂ) - 1))
      (𝓝[>] 0) (𝓝 (Complex.Gamma rho * (rho - 1))) := by
    exact ((Complex.continuousAt_Gamma rho hnotGammaPole).tendsto.comp hray).mul
      (((continuous_id.sub continuous_const).tendsto rho).comp hray)
  have hvanish : Complex.Gamma rho * (rho - 1) = 0 :=
    tendsto_nhds_unique hrightActual hrightZero
  exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhoPos)
    (sub_ne_zero.mpr hrhoOne)) hvanish

/-- **Unconditional critical-energy obstruction.**  `N * H_N^(2 : ℕ)` cannot tend to zero. -/
theorem not_tendsto_nat_mul_deningerHarmonicPartial_sq_zero :
    ¬ Tendsto (fun N : ℕ => (N : ℝ) * deningerHarmonicPartial N ^ 2)
      atTop (𝓝 0) := by
  intro hcrit
  have hprofile := tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_energy hcrit
  have hdecay := halfDecay_of_profile_tendsto_zero hprofile
  have hRH := mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis hdecay
  obtain ⟨rho, hrho0, hrho1, hzeta⟩ := exists_riemannZeta_zero_mem_openStrip
  have hrhoHalf : rho.re = 1 / 2 := by
    apply hRH rho hzeta
    · intro htrivial
      obtain ⟨n, hn⟩ := htrivial
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [hn] at hrho0
      norm_num [Complex.mul_re] at hrho0
      linarith
    · exact riemannZeta_zero_ne_one hzeta
  exact not_tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_zeta_zero hrhoHalf hzeta hprofile

/-- Raw Möbius Báez--Duarte full error cannot converge to zero. -/
theorem not_tendsto_bdMobiusFullErrorEnergy_zero :
    ¬ Tendsto bdMobiusFullErrorEnergy atTop (𝓝 0) := by
  intro hfull
  exact not_tendsto_nat_mul_deningerHarmonicPartial_sq_zero
    (tendsto_nat_mul_deningerHarmonicPartial_sq_zero_of_fullError hfull)

/-- Canonical raw complementary-tail convergence is unconditionally false. -/
theorem not_tendsto_bdMobiusComplementaryTailErrorEnergy_zero :
    ¬ Tendsto (fun N : ℕ =>
      bdMobiusComplementaryTailErrorEnergy N (bdMobiusLogPrefix N))
      atTop (𝓝 0) := by
  intro htail
  exact not_tendsto_bdMobiusFullErrorEnergy_zero
    (tendsto_bdMobiusFullErrorEnergy_zero_iff_complementaryTail.mpr htail)

private theorem exists_frequent_floor_of_not_tendsto_zero
    {a : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N) (hnot : ¬ Tendsto a atTop (𝓝 0)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ᶠ N : ℕ in atTop, epsilon ≤ a N := by
  by_contra hfloor
  push Not at hfloor
  apply hnot
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hevent : ∀ᶠ N : ℕ in atTop, a N < epsilon := hfloor epsilon hepsilon
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
  refine ⟨N₀, ?_⟩
  intro N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha N)]
  exact hN₀ N hN

/-- Positive survivor: critical harmonic energy exceeds one fixed floor cofinally often. -/
theorem frequent_harmonic_energy_floor :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ N₀ : ℕ, ∃ N : ℕ,
      N₀ ≤ N ∧ epsilon ≤ (N : ℝ) * deningerHarmonicPartial N ^ 2 := by
  obtain ⟨epsilon, hepsilon, hfreq⟩ :=
    exists_frequent_floor_of_not_tendsto_zero
      (fun N => mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
      not_tendsto_nat_mul_deningerHarmonicPartial_sq_zero
  refine ⟨epsilon, hepsilon, ?_⟩
  simpa only [frequently_atTop] using hfreq

/-- Positive survivor: raw full error exceeds one fixed floor cofinally often. -/
theorem frequent_bdMobiusFullErrorEnergy_floor :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ N₀ : ℕ, ∃ N : ℕ,
      N₀ ≤ N ∧ epsilon ≤ bdMobiusFullErrorEnergy N := by
  obtain ⟨epsilon, hepsilon, hfreq⟩ :=
    exists_frequent_floor_of_not_tendsto_zero
      (fun N => by rw [bdMobiusFullErrorEnergy_eq_norm_sq]; positivity)
      not_tendsto_bdMobiusFullErrorEnergy_zero
  refine ⟨epsilon, hepsilon, ?_⟩
  simpa only [frequently_atTop] using hfreq

/-- Positive survivor: canonical complementary-tail error has a cofinal positive floor. -/
theorem frequent_bdMobiusComplementaryTailErrorEnergy_floor :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ N₀ : ℕ, ∃ N : ℕ,
      N₀ ≤ N ∧ epsilon ≤
        bdMobiusComplementaryTailErrorEnergy N (bdMobiusLogPrefix N) := by
  have hnonneg : ∀ N : ℕ,
      0 ≤ bdMobiusComplementaryTailErrorEnergy N (bdMobiusLogPrefix N) := by
    intro N
    rw [bdMobiusComplementaryTailErrorEnergy]
    apply tsum_nonneg
    intro j
    positivity
  obtain ⟨epsilon, hepsilon, hfreq⟩ :=
    exists_frequent_floor_of_not_tendsto_zero hnonneg
      not_tendsto_bdMobiusComplementaryTailErrorEnergy_zero
  refine ⟨epsilon, hepsilon, ?_⟩
  simpa only [frequently_atTop] using hfreq

end
end RHTower
