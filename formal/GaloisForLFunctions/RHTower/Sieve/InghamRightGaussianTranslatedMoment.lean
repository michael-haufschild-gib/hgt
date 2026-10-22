import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGaussianTranslatedMoment
import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgePowerSaving

/-!
# Translated Gaussian moment of Ingham's pole-cleared error on the line `Re s = 181/180`

Let `M_X(s) = ∑_{n ≤ X} μ(n) n^{-s}` and let `E_X(z) = exp((z/X)^2) ((z-1)ζ(z) M_X(z) - (z-1)) / z`
be the Gaussian-regularized pole-cleared mollified zeta error (`inghamGabrielPoleClearedError`
with `κ = 1`, `T = X`). This module proves that on the fixed right line `Re z = 181/180` every
window of length `2X`, centred at any height, satisfies `∫_{-X}^{X} |E_X(z+it)|^2 dt ≤ C X^{-1/180}`
with `C` independent of the centre. The proof bounds the raw mean square of `ζ M_X - 1` on
symmetric windows `[-N, N]`, covers the translated window by `N = ⌈|Im z| + X⌉`, and absorbs the
linear growth in `N` by the Gaussian decay `exp(-2 (max(0, |Im z| - X)/X)^2)`.

## Main results

- `gaussianLinearWindowAbsorption`: for `X ≥ 4` and `N = ⌈|τ| + X⌉`,
  `exp(-2 (max(0, |τ| - X)/X)^2) N ≤ 4 e^{1/2} X`.
- `integral_Icc_normSq_inghamMollifiedError_powerSavingRightEdge_symmetric_le`: explicit bound
  for `∫_{-N}^{N} |ζ M_X - 1|^2 (181/180 + it) dt` of the form `A X^{-1/180} + B X^{-181/180} N`.
- `exists_inghamGabrielPoleClearedError_powerSavingRight_translatedMoment_le`: some `C ≥ 0` gives
  `∫_{-X}^{X} |E_X(z+it)|^2 dt ≤ C X^{-1/180}` for all `X ≥ 4` and all `z` with `Re z = 181/180`.

## Hypotheses

The main results are unconditional. The only conditions are the ranges `X ≥ 4` (or `X, N ≥ 1` for
the raw symmetric bound) and the abscissa condition `Re z = 181/180`.
-/

noncomputable section

open Complex Set MeasureTheory intervalIntegral

namespace RHTower.Sieve

/-- Gaussian absorption of linear window growth: for `X ≥ 4`, any real `τ` and
`N = ⌈|τ| + X⌉`, `exp(-2 (max(0, |τ| - X)/X)^2) N ≤ 4 e^{1/2} X`. -/
theorem gaussianLinearWindowAbsorption
    (X : ℕ) (tau : ℝ) (hX : 4 ≤ X) :
    let N := Nat.ceil (|tau| + (X : ℝ))
    Real.exp (-2 *
        (max 0 (|tau| - (X : ℝ)) / (X : ℝ)) ^ 2) * (N : ℝ) ≤
      4 * Real.exp (1 / 2 : ℝ) * (X : ℝ) := by
  let d : ℝ := max 0 (|tau| - (X : ℝ))
  let y : ℝ := d / (X : ℝ)
  let N : ℕ := Nat.ceil (|tau| + (X : ℝ))
  dsimp only
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hd0 : 0 ≤ d := by dsimp only [d]; exact le_max_left _ _
  have hy0 : 0 ≤ y := div_nonneg hd0 hXpos.le
  have habsd : |tau| + (X : ℝ) ≤ d + 2 * (X : ℝ) := by
    by_cases h : |tau| ≤ (X : ℝ)
    · have hd : d = 0 := by
        dsimp only [d]
        rw [max_eq_left (sub_nonpos.mpr h)]
      rw [hd]
      linarith
    · have hd : d = |tau| - (X : ℝ) := by
        dsimp only [d]
        rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
      rw [hd]
      linarith
  have hceil : (N : ℝ) < |tau| + (X : ℝ) + 1 := by
    dsimp only [N]
    exact Nat.ceil_lt_add_one (by positivity)
  have hNle : (N : ℝ) ≤ d + 3 * (X : ℝ) := by linarith
  have hfactor : d + 3 * (X : ℝ) = (X : ℝ) * (y + 3) := by
    dsimp only [y]
    field_simp
  have hcore : Real.exp (-2 * y ^ 2) * (y + 3) ≤
      4 * Real.exp (1 / 2 : ℝ) := by
    by_cases hy : y ≤ 1
    · have hy4 : y + 3 ≤ 4 := by linarith
      have hexp : Real.exp (-2 * y ^ 2) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg y]
      have hexpone : (1 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := Real.one_le_exp (by norm_num)
      calc
        Real.exp (-2 * y ^ 2) * (y + 3) ≤ 1 * 4 :=
          mul_le_mul hexp hy4 (by linarith) (by norm_num)
        _ = 4 := by ring
        _ ≤ 4 * Real.exp (1 / 2 : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hexpone (by norm_num : (0 : ℝ) ≤ 4)]
    · have hy1 : 1 ≤ y := le_of_not_ge hy
      have hy4 : y + 3 ≤ 4 * y := by linarith
      have hySq : y ≤ y ^ 2 := by nlinarith
      have habsorb := RHTower.rpow_mul_exp_neg_le
        (m := (1 : ℝ)) (c := (2 : ℝ)) (u := y ^ 2)
        (by norm_num) (by norm_num) (by nlinarith)
      have habsorb' : y ^ 2 * Real.exp (-(2 * y ^ 2)) ≤
          Real.exp (1 / 2 : ℝ) := by
        convert habsorb using 1 <;> norm_num
      calc
        Real.exp (-2 * y ^ 2) * (y + 3) ≤
            Real.exp (-2 * y ^ 2) * (4 * y) := by gcongr
        _ = 4 * (y * Real.exp (-(2 * y ^ 2))) := by ring
        _ ≤ 4 * (y ^ 2 * Real.exp (-(2 * y ^ 2))) := by gcongr
        _ ≤ 4 * Real.exp (1 / 2 : ℝ) := by gcongr
  rw [show max 0 (|tau| - (X : ℝ)) = d by rfl,
    show d / (X : ℝ) = y by rfl]
  calc
    Real.exp (-2 * y ^ 2) * (N : ℝ) ≤
        Real.exp (-2 * y ^ 2) * (d + 3 * (X : ℝ)) := by gcongr
    _ = (X : ℝ) * (Real.exp (-2 * y ^ 2) * (y + 3)) := by
      rw [hfactor]
      ring
    _ ≤ (X : ℝ) * (4 * Real.exp (1 / 2 : ℝ)) := by gcongr
    _ = 4 * Real.exp (1 / 2 : ℝ) * (X : ℝ) := by ring

/-- Raw mean square on the line `Re s = 181/180` for `X, N ≥ 1`:
`∫_{-N}^{N} |ζ(s) M_X(s) - 1|^2 dt ≤ A X^{-1/180} + B X^{-181/180} N`, with explicit constants
`A`, `B` built from the divisor-bound constant `inghamPowerSavingDivisorConstant`. -/
theorem integral_Icc_normSq_inghamMollifiedError_powerSavingRightEdge_symmetric_le
    {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) :
    (∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
      ‖riemannZeta (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1‖ ^ 2) ≤
      5 * Real.pi * Real.exp 1 *
          (inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ)) *
            (X : ℝ) ^ (-(1 / 180 : ℝ)) +
        (5 * Real.pi / 2) *
          (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ)) *
            (X : ℝ) ^ (-(181 / 180 : ℝ)) * (N : ℝ) := by
  let a : ℕ → ℂ := complexCoeff (moebiusZetaDefect X)
  have hbeta : 1 < inghamPowerSavingRightEdge := by
    norm_num [inghamPowerSavingRightEdge]
  have habs := summable_norm_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hplain := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hweighted :=
    summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase := integral_Icc_normSq_LSeries_le_general_affine_infinite
    (a := a) (complexCoeff_moebiusZetaDefect_zero X)
    inghamPowerSavingRightEdge habs hplain hweighted hNR
  have hsource (t : ℝ) :
      ‖LSeries a (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I)‖ =
        ‖riemannZeta (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1‖ := by
    have hs : 1 <
        ((((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I)).re := by
      simpa using hbeta
    rw [show a = complexCoeff (moebiusZetaDefect X) by rfl,
      LSeries_complexCoeff_moebiusZetaDefect_eq X hs]
    rw [show 1 - inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          riemannZeta
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) =
        -(riemannZeta
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1) by ring,
      norm_neg]
  have hW := tsum_inghamRightEdgeWeightedSquareMass_le hX
  have hP := tsum_inghamRightEdgeSquareMass_le hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    (∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
      ‖riemannZeta (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1‖ ^ 2) =
        ∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
          ‖LSeries a
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I)‖ ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [hsource]
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n : ℝ) *
            ‖a n * (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2) +
        (5 * Real.pi / 2) *
          (∑' n : ℕ,
            ‖a n * (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2) *
              (N : ℝ) := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (inghamPowerSavingDivisorConstant ^ 2 *
            (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ)) +
        (5 * Real.pi / 2) *
          (inghamPowerSavingDivisorConstant ^ 2 *
            (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ)) *
              (N : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (by simpa [a, inghamRightEdgeSquareMass] using hW)
          (by positivity))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa [a, inghamRightEdgeSquareMass] using hP) (by positivity))
          (by positivity))
    _ = _ := by ring

private def powerSavingRightPoint (t : ℝ) : ℂ :=
  (inghamPowerSavingRightEdge : ℂ) + (t : ℂ) * I

/-- The raw density `|ζ(s) M_X(s) - 1|^2` at `s = 181/180 + it`. -/
private def powerSavingRightRawDensity (X : ℕ) (t : ℝ) : ℝ :=
  ‖riemannZeta (powerSavingRightPoint t) *
      inghamMollifier X (powerSavingRightPoint t) - 1‖ ^ (2 : ℝ)

private theorem continuous_powerSavingRightPoint :
    Continuous powerSavingRightPoint := by
  unfold powerSavingRightPoint
  fun_prop

private theorem powerSavingRightPoint_ne_one (t : ℝ) :
    powerSavingRightPoint t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [powerSavingRightPoint, inghamPowerSavingRightEdge] at hre

private theorem continuous_powerSavingRightRawDensity (X : ℕ) :
    Continuous (powerSavingRightRawDensity X) := by
  have hzeta : Continuous fun t : ℝ => riemannZeta (powerSavingRightPoint t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (differentiableAt_riemannZeta (powerSavingRightPoint_ne_one t)).continuousAt.comp'
      continuous_powerSavingRightPoint.continuousAt
  have hmoll : Continuous fun t : ℝ => inghamMollifier X (powerSavingRightPoint t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_inghamMollifier X (powerSavingRightPoint t)).continuousAt.comp'
      continuous_powerSavingRightPoint.continuousAt
  exact (((hzeta.mul hmoll).sub continuous_const).norm).rpow_const
    (fun _ => Or.inr (by norm_num))

private theorem right_setIntegral_Icc_eq_intervalIntegral
    {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, g t) = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- A window `[τ - X, τ + X]` lies inside `[-N, N]` when `|τ| + X ≤ N`, so its raw mean square is
at most the symmetric one. -/
private theorem translated_powerSavingRightRawDensity_integral_le
    (X N : ℕ) (tau : ℝ) (hcover : |tau| + (X : ℝ) ≤ N) :
    (∫ t in Icc (-(X : ℝ)) (X : ℝ),
      powerSavingRightRawDensity X (tau + t)) ≤
        ∫ t in Icc (-(N : ℝ)) (N : ℝ), powerSavingRightRawDensity X t := by
  have hshift :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        powerSavingRightRawDensity X (tau + t)) =
        ∫ t in Icc (-(X : ℝ) + tau) ((X : ℝ) + tau),
          powerSavingRightRawDensity X t := by
    rw [right_setIntegral_Icc_eq_intervalIntegral (by
        have hX0 : (0 : ℝ) ≤ X := by positivity
        linarith),
      right_setIntegral_Icc_eq_intervalIntegral (by linarith)]
    calc
      (∫ t in -(X : ℝ)..(X : ℝ), powerSavingRightRawDensity X (tau + t)) =
          ∫ t in -(X : ℝ)..(X : ℝ), powerSavingRightRawDensity X (t + tau) := by
        apply intervalIntegral.integral_congr
        intro t _
        change powerSavingRightRawDensity X (tau + t) =
          powerSavingRightRawDensity X (t + tau)
        rw [add_comm]
      _ = _ := intervalIntegral.integral_comp_add_right _ _
  rw [hshift]
  exact MeasureTheory.setIntegral_mono_set
    (continuous_powerSavingRightRawDensity X).integrableOn_Icc
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun u hu => by
      constructor
      · linarith [hu.1, neg_le_abs tau]
      · linarith [hu.2, le_abs_self tau])

private theorem powerSavingRight_shift_eq
    {z : ℂ} (hz : z.re = inghamPowerSavingRightEdge) (t : ℝ) :
    z + (t : ℂ) * I = powerSavingRightPoint (z.im + t) := by
  apply Complex.ext
  · simp [powerSavingRightPoint, hz]
  · simp [powerSavingRightPoint]

private theorem continuous_powerSavingRight_shift_poleCleared
    (X : ℕ) {z : ℂ} (hz : z.re = inghamPowerSavingRightEdge) :
    Continuous fun t : ℝ =>
      inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hpoint0 : z + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [hz, inghamPowerSavingRightEdge] at hre
  have hpath : ContinuousAt (fun u : ℝ => z + (u : ℂ) * I) t := by fun_prop
  change ContinuousAt
    (inghamGabrielPoleClearedError X 1 (X : ℝ) ∘
      fun u : ℝ => z + (u : ℂ) * I) t
  exact ContinuousAt.comp_of_eq
    (analyticAt_inghamGabrielPoleClearedError X 1 (X : ℝ) hpoint0).continuousAt
    hpath rfl

private theorem right_max_sub_le_abs_add
    (X : ℕ) (tau t : ℝ) (ht : t ∈ Icc (-(X : ℝ)) (X : ℝ)) :
    max 0 (|tau| - (X : ℝ)) ≤ |tau + t| := by
  have htAbs : |t| ≤ (X : ℝ) := (abs_le).2 ht
  have htri : |tau| ≤ |tau + t| + |t| := by
    calc
      |tau| = |(tau + t) + (-t)| := by ring_nf
      _ ≤ |tau + t| + |-t| := abs_add_le _ _
      _ = |tau + t| + |t| := by rw [abs_neg]
  apply max_le (abs_nonneg _)
  linarith

/-- Pointwise comparison on a translated window: for `Re z = 181/180`, `X ≥ 4` and `|t| ≤ X`,
`|E_X(z+it)|^2 ≤ e^8 exp(-2 (max(0, |Im z| - X)/X)^2) |ζ M_X - 1|^2 (z+it)`. -/
private theorem poleCleared_powerSavingRight_shift_rpow_le
    (X : ℕ) {z : ℂ} (hz : z.re = inghamPowerSavingRightEdge) (hX : 4 ≤ X)
    {t : ℝ} (ht : t ∈ Icc (-(X : ℝ)) (X : ℝ)) :
    ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
        (z + (t : ℂ) * I)‖ ^ (2 : ℝ) ≤
      Real.exp 8 *
        Real.exp (-2 *
          (max 0 (|z.im| - (X : ℝ)) / (X : ℝ)) ^ 2) *
        powerSavingRightRawDensity X (z.im + t) := by
  let d : ℝ := max 0 (|z.im| - (X : ℝ))
  let y : ℝ := z.im + t
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX4 : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hpoint : z + (t : ℂ) * I = powerSavingRightPoint y := by
    dsimp only [y]
    exact powerSavingRight_shift_eq hz t
  have hraw := norm_inghamGabrielPoleClearedError_le_raw X 1 (X : ℝ)
    (z := z + (t : ℂ) * I)
    (by norm_num [hz, inghamPowerSavingRightEdge]) (by
      rw [hpoint]
      exact powerSavingRightPoint_ne_one y)
  have hgauss := norm_inghamGabrielGaussian_vertical
    1 (X : ℝ) inghamPowerSavingRightEdge y hXpos.ne'
  have hgaussPoint :
      ‖Complex.exp ((1 : ℂ) *
        (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ =
        Real.exp (inghamPowerSavingRightEdge ^ 2 / (X : ℝ) ^ 2) *
          Real.exp (-y ^ 2 / (X : ℝ) ^ 2) := by
    rw [hpoint]
    simpa [powerSavingRightPoint] using hgauss
  have habscissa :
      Real.exp (inghamPowerSavingRightEdge ^ 2 / (X : ℝ) ^ 2) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (sq_pos_of_pos hXpos)]
    norm_num [inghamPowerSavingRightEdge]
    nlinarith [sq_nonneg ((X : ℝ) - 4)]
  have hdist : d ^ 2 ≤ y ^ 2 := by
    have hd := right_max_sub_le_abs_add X z.im t ht
    have hd0 : 0 ≤ d := by dsimp only [d]; exact le_max_left _ _
    have habs0 : 0 ≤ |y| := abs_nonneg _
    have hprod : 0 ≤ (|y| - d) * (|y| + d) :=
      mul_nonneg (sub_nonneg.mpr (by simpa only [y] using hd))
        (add_nonneg habs0 hd0)
    nlinarith [sq_abs y]
  have hdecay : Real.exp (-y ^ 2 / (X : ℝ) ^ 2) ≤
      Real.exp (-d ^ 2 / (X : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hdist) (sq_nonneg _)
  have hgaussBound :
      ‖Complex.exp ((1 : ℂ) *
        (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ ≤
        Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2) := by
    rw [hgaussPoint]
    exact mul_le_mul habscissa hdecay (Real.exp_pos _).le (Real.exp_pos _).le
  have hfield :
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I)‖ ≤
        (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
          ‖riemannZeta (powerSavingRightPoint y) *
            inghamMollifier X (powerSavingRightPoint y) - 1‖ := by
    calc
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I)‖ ≤
          ‖Complex.exp ((1 : ℂ) *
            (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ *
            ‖riemannZeta (z + (t : ℂ) * I) *
              inghamMollifier X (z + (t : ℂ) * I) - 1‖ := hraw
      _ ≤ (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
            ‖riemannZeta (z + (t : ℂ) * I) *
              inghamMollifier X (z + (t : ℂ) * I) - 1‖ :=
        mul_le_mul_of_nonneg_right hgaussBound (norm_nonneg _)
      _ = (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
            ‖riemannZeta (powerSavingRightPoint y) *
              inghamMollifier X (powerSavingRightPoint y) - 1‖ := by rw [hpoint]
  have hrpow := Real.rpow_le_rpow (norm_nonneg _) hfield (by norm_num : (0 : ℝ) ≤ 2)
  have hconst :
      (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) ^ (2 : ℝ) =
        Real.exp 8 * Real.exp (-2 * (d / (X : ℝ)) ^ 2) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), hconst] at hrpow
  simpa only [powerSavingRightRawDensity, d, y] using hrpow

/-- Uniform translated moment on `Re z = 181/180`: some `C ≥ 0` gives
`∫_{-X}^{X} |E_X(z+it)|^2 dt ≤ C X^{-1/180}` for every `X ≥ 4` and every `z` with
`Re z = 181/180`, where `E_X` is the Gaussian pole-cleared mollified zeta error. -/
theorem exists_inghamGabrielPoleClearedError_powerSavingRight_translatedMoment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X → ∀ z : ℂ,
      z.re = inghamPowerSavingRightEdge →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤
        C * (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
  let A : ℝ := 5 * Real.pi * Real.exp 1 *
    (inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ))
  let B : ℝ := (5 * Real.pi / 2) *
    (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ))
  let K : ℝ := 4 * Real.exp (1 / 2 : ℝ)
  let C : ℝ := Real.exp 8 * (A + B * K)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX z hz
  let tau : ℝ := z.im
  let d : ℝ := max 0 (|tau| - (X : ℝ))
  let N : ℕ := Nat.ceil (|tau| + (X : ℝ))
  let E : ℝ := Real.exp (-2 * (d / (X : ℝ)) ^ 2)
  let G : ℝ := Real.exp 8 * E
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcover : |tau| + (X : ℝ) ≤ (N : ℝ) := by
    dsimp only [N]
    exact Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    exact_mod_cast (show (1 : ℝ) ≤ N by linarith [abs_nonneg tau])
  have hrawN :=
    integral_Icc_normSq_inghamMollifiedError_powerSavingRightEdge_symmetric_le
      (X := X) (N := N) (by omega) hN1
  have hrawN' :
      (∫ t in Icc (-(N : ℝ)) (N : ℝ), powerSavingRightRawDensity X t) ≤
        A * (X : ℝ) ^ (-(1 / 180 : ℝ)) +
          B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (N : ℝ) := by
    simpa only [powerSavingRightRawDensity, powerSavingRightPoint,
      Real.rpow_two, A, B] using hrawN
  have htranslate := translated_powerSavingRightRawDensity_integral_le X N tau hcover
  have hrawShift := htranslate.trans hrawN'
  have hfieldCont : Continuous fun t : ℝ =>
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
        (z + (t : ℂ) * I)‖ ^ (2 : ℝ) :=
    (((continuous_powerSavingRight_shift_poleCleared X hz).norm).rpow_const
      (fun _ => Or.inr (by norm_num)))
  have hrawShiftCont : Continuous fun t : ℝ =>
      powerSavingRightRawDensity X (tau + t) :=
    (continuous_powerSavingRightRawDensity X).comp (by fun_prop)
  have hpointwise : ∀ t ∈ Icc (-(X : ℝ)) (X : ℝ),
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ) ≤
        G * powerSavingRightRawDensity X (tau + t) := by
    intro t ht
    simpa only [G, E, d, tau] using
      poleCleared_powerSavingRight_shift_rpow_le X hz hX ht
  have hintegral :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤
        G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          powerSavingRightRawDensity X (tau + t)) := by
    calc
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤
          ∫ t in Icc (-(X : ℝ)) (X : ℝ),
            G * powerSavingRightRawDensity X (tau + t) := by
        exact integral_mono_ae hfieldCont.integrableOn_Icc
          ((continuous_const.mul hrawShiftCont).integrableOn_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpointwise)
      _ = G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          powerSavingRightRawDensity X (tau + t)) := by
        rw [MeasureTheory.integral_const_mul]
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hE1 : E ≤ 1 := by
    dsimp only [E]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (d / (X : ℝ))]
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have habsorb := gaussianLinearWindowAbsorption X tau hX
  dsimp only at habsorb
  have hEN : E * (N : ℝ) ≤ K * (X : ℝ) := by
    simpa only [E, d, N, K] using habsorb
  have hpow : (X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ) =
      (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
    calc
      (X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ) =
          (X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (X : ℝ) ^ (-(181 / 180 : ℝ) + 1) := by
        rw [Real.rpow_add hXpos]
      _ = (X : ℝ) ^ (-(1 / 180 : ℝ)) := by norm_num
  have hfirstE : E * (X : ℝ) ^ (-(1 / 180 : ℝ)) ≤
      (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
    calc
      E * (X : ℝ) ^ (-(1 / 180 : ℝ)) ≤
          1 * (X : ℝ) ^ (-(1 / 180 : ℝ)) :=
        mul_le_mul hE1 le_rfl (Real.rpow_nonneg hXpos.le _) (by norm_num)
      _ = (X : ℝ) ^ (-(1 / 180 : ℝ)) := one_mul _
  have hsecondE :
      (X : ℝ) ^ (-(181 / 180 : ℝ)) * (E * (N : ℝ)) ≤
        (X : ℝ) ^ (-(181 / 180 : ℝ)) * (K * (X : ℝ)) :=
    mul_le_mul_of_nonneg_left hEN (Real.rpow_nonneg hXpos.le _)
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤
        G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          powerSavingRightRawDensity X (tau + t)) := hintegral
    _ ≤ G * (A * (X : ℝ) ^ (-(1 / 180 : ℝ)) +
          B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hrawShift hG0
    _ = Real.exp 8 *
        (A * (E * (X : ℝ) ^ (-(1 / 180 : ℝ))) +
          B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (E * (N : ℝ))) := by
      dsimp only [G]
      ring
    _ ≤ Real.exp 8 *
        (A * (X : ℝ) ^ (-(1 / 180 : ℝ)) +
          B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (K * (X : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfirstE hA)
        (by
          calc
            B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (E * (N : ℝ)) =
                B * ((X : ℝ) ^ (-(181 / 180 : ℝ)) * (E * (N : ℝ))) := by ring
            _ ≤ B * ((X : ℝ) ^ (-(181 / 180 : ℝ)) * (K * (X : ℝ))) :=
              mul_le_mul_of_nonneg_left hsecondE hB
            _ = B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (K * (X : ℝ)) := by ring)
    _ = C * (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
      calc
        Real.exp 8 *
            (A * (X : ℝ) ^ (-(1 / 180 : ℝ)) +
              B * (X : ℝ) ^ (-(181 / 180 : ℝ)) * (K * (X : ℝ))) =
            Real.exp 8 *
              (A * (X : ℝ) ^ (-(1 / 180 : ℝ)) +
                B * K * ((X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ))) := by ring
        _ = Real.exp 8 *
              (A * (X : ℝ) ^ (-(1 / 180 : ℝ)) +
                B * K * (X : ℝ) ^ (-(1 / 180 : ℝ))) := by rw [hpow]
        _ = C * (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
          dsimp only [C]
          ring

end RHTower.Sieve
