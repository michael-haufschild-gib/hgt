import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureFiniteSectionMaximum
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Cold Watson positivity for completed-theta aperture curvature

The completed theta source has an even sixth-order seam jet and a globally controlled eighth
derivative. Integrating its Taylor remainder against the cold Gaussian aperture gives a
four-term Watson expansion with an explicit `O(L⁻⁴)` normalized error. Quotient algebra then
identifies the first degree-curvature coefficient with the already-proved positive sixth-seam
numerator.

Consequently, every fixed ratio-curvature coordinate is strictly positive for all sufficiently
cold apertures. Finite intersections discharge the initial-data hypothesis in the completed-theta
finite-section maximum principle: only its outgoing degree boundary remains.
-/

open Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

private theorem thetaCuspFullSource_taylor_seven
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval thetaCuspFullSource 7 (uIcc 0 x) 0 x =
      thetaCuspFullSource 0 +
        iteratedDeriv 2 thetaCuspFullSource 0 / 2 * x ^ 2 +
        iteratedDeriv 4 thetaCuspFullSource 0 / 24 * x ^ 4 +
        iteratedDeriv 6 thetaCuspFullSource 0 / 720 * x ^ 6 := by
  have hu : uIcc (0 : ℝ) x = Icc 0 x := uIcc_of_le hx.le
  have hud : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) := by
    rw [hu]
    exact uniqueDiffOn_Icc hx
  have hder (n : ℕ) :
      iteratedDerivWithin n thetaCuspFullSource (uIcc 0 x) 0 =
        iteratedDeriv n thetaCuspFullSource 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hud
      (contDiff_thetaCuspFullSource.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (by rw [hu]; exact left_mem_Icc.mpr hx.le)
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) (by norm_num)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 3) (by norm_num)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 5) (by norm_num)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 7) (by norm_num)
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hder,
    h1, h3, h5, h7, smul_eq_mul, mul_zero, add_zero]
  ring

theorem thetaCuspFullSource_taylor_six_remainder_bound
    {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspFullSource x -
        (thetaCuspFullSource 0 +
          iteratedDeriv 2 thetaCuspFullSource 0 / 2 * x ^ 2 +
          iteratedDeriv 4 thetaCuspFullSource 0 / 24 * x ^ 4 +
          iteratedDeriv 6 thetaCuspFullSource 0 / 720 * x ^ 6)| ≤
      thetaCuspDerivativeExpConstant 8 / 40320 * x ^ 8 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have h8 : ((7 + 1 : ℕ) : WithTop ℕ∞) ≤
      ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl (7 + 1)
  obtain ⟨y, _hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := thetaCuspFullSource) (x := x) (x₀ := 0) (n := 7)
      hx.ne
      (contDiff_thetaCuspFullSource.contDiffOn.of_le h8)
  rw [thetaCuspFullSource_taylor_seven hx] at hrem
  rw [hrem]
  have hder := weighted_iteratedDeriv_thetaCuspFullSource_le 0 8 y
  norm_num at hder
  norm_num only [sub_zero, Nat.factorial, Nat.cast_ofNat]
  calc
    |iteratedDeriv 8 thetaCuspFullSource y * x ^ 8 / 40320| =
        |iteratedDeriv 8 thetaCuspFullSource y| * x ^ 8 / 40320 := by
          rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hx.le]
          norm_num
    _ ≤ thetaCuspDerivativeExpConstant 8 * x ^ 8 / 40320 := by
      gcongr
    _ = thetaCuspDerivativeExpConstant 8 / 40320 * x ^ 8 := by ring

def coldGaussianHalfMoment (L : ℝ) (j : ℕ) : ℝ :=
  L ^ (-(thetaCuspGaussianApertureGammaShape j)) *
    (1 / 2) * Real.Gamma (thetaCuspGaussianApertureGammaShape j)

theorem integral_coldGaussianHalfMoment
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * j) * Real.exp (-L * x ^ 2)) =
      coldGaussianHalfMoment L j := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (((2 * j : ℕ) : ℝ))) (b := L)
    (by norm_num) (by
      have hq0 : 0 ≤ (((2 * j : ℕ) : ℝ)) := Nat.cast_nonneg _
      linarith) hL
  rw [coldGaussianHalfMoment]
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    norm_num only [Real.rpow_natCast, Real.rpow_two]
  · simp only [thetaCuspGaussianApertureGammaShape]
    push_cast
    ring

theorem coldGaussianHalfMoment_pos
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    0 < coldGaussianHalfMoment L j := by
  rw [coldGaussianHalfMoment]
  exact mul_pos
    (mul_pos (Real.rpow_pos_of_pos hL _)
      (by norm_num : (0 : ℝ) < 1 / 2))
    (Real.Gamma_pos_of_pos
      (thetaCuspGaussianApertureGammaShape_pos j))

theorem coldGaussianHalfMoment_succ
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    coldGaussianHalfMoment L (j + 1) =
      thetaCuspGaussianApertureGammaShape j / L *
        coldGaussianHalfMoment L j := by
  have hGammaShape :
      thetaCuspGaussianApertureGammaShape (j + 1) =
        thetaCuspGaussianApertureGammaShape j + 1 := by
    simp only [thetaCuspGaussianApertureGammaShape]
    push_cast
    ring
  have hshape0 : thetaCuspGaussianApertureGammaShape j ≠ 0 :=
    (thetaCuspGaussianApertureGammaShape_pos j).ne'
  rw [coldGaussianHalfMoment, coldGaussianHalfMoment, hGammaShape,
    Real.Gamma_add_one hshape0]
  rw [show -(thetaCuspGaussianApertureGammaShape j + 1) =
      -thetaCuspGaussianApertureGammaShape j + (-1 : ℝ) by ring,
    Real.rpow_add hL, Real.rpow_neg_one]
  field_simp [hL.ne']

def coldGammaRising (a : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (a + i)

theorem thetaCuspGaussianApertureGammaShape_add
    (j k : ℕ) :
    thetaCuspGaussianApertureGammaShape (j + k) =
      thetaCuspGaussianApertureGammaShape j + k := by
  simp only [thetaCuspGaussianApertureGammaShape]
  push_cast
  ring

theorem coldGaussianHalfMoment_add
    {L : ℝ} (hL : 0 < L) (j k : ℕ) :
    coldGaussianHalfMoment L (j + k) =
      coldGammaRising (thetaCuspGaussianApertureGammaShape j) k /
          L ^ k * coldGaussianHalfMoment L j := by
  induction k with
  | zero =>
      simp [coldGammaRising]
  | succ k ih =>
      rw [show j + (k + 1) = (j + k) + 1 by omega,
        coldGaussianHalfMoment_succ hL, ih,
        thetaCuspGaussianApertureGammaShape_add]
      simp only [coldGammaRising, Finset.prod_range_succ]
      field_simp [hL.ne']
      ring

theorem integrableOn_coldGaussianHalfMoment
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    IntegrableOn
      (fun x : ℝ => x ^ (2 * j) * Real.exp (-L * x ^ 2))
      (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (s := (((2 * j : ℕ) : ℝ))) (b := L)
    (by
      have hq0 : 0 ≤ (((2 * j : ℕ) : ℝ)) := Nat.cast_nonneg _
      linarith)
    (by norm_num) hL
  convert h using 1
  funext x
  norm_num only [Real.rpow_natCast, Real.rpow_two]

def thetaCuspColdTaylorMoment (L : ℝ) (j : ℕ) : ℝ :=
  thetaCuspFullSource 0 * coldGaussianHalfMoment L j +
    (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
      coldGaussianHalfMoment L (j + 1) +
    (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
      coldGaussianHalfMoment L (j + 2) +
    (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
      coldGaussianHalfMoment L (j + 3)

def thetaCuspColdTaylorResidualIntegrand
    (L : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * j) * thetaCuspGaussianApertureDensity (-L) x -
    (thetaCuspFullSource 0 *
        (x ^ (2 * j) * Real.exp (-L * x ^ 2)) +
      (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
        (x ^ (2 * (j + 1)) * Real.exp (-L * x ^ 2)) +
      (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
        (x ^ (2 * (j + 2)) * Real.exp (-L * x ^ 2)) +
      (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
        (x ^ (2 * (j + 3)) * Real.exp (-L * x ^ 2)))

theorem integral_thetaCuspColdTaylorResidualIntegrand
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    (∫ x : ℝ in Ioi 0,
        thetaCuspColdTaylorResidualIntegrand L j x) =
      thetaCuspGaussianApertureHalfMoment (-L) j -
        thetaCuspColdTaylorMoment L j := by
  have hs :
      IntegrableOn
        (fun x : ℝ =>
          x ^ (2 * j) * thetaCuspGaussianApertureDensity (-L) x)
        (Ioi 0) :=
    integrableOn_thetaCuspGaussianApertureMomentIntegrand
      (by linarith) j
  have hg0 := integrableOn_coldGaussianHalfMoment hL j
  have hg1 := integrableOn_coldGaussianHalfMoment hL (j + 1)
  have hg2 := integrableOn_coldGaussianHalfMoment hL (j + 2)
  have hg3 := integrableOn_coldGaussianHalfMoment hL (j + 3)
  let f0 : ℝ → ℝ := fun x =>
    thetaCuspFullSource 0 *
      (x ^ (2 * j) * Real.exp (-L * x ^ 2))
  let f1 : ℝ → ℝ := fun x =>
    (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
      (x ^ (2 * (j + 1)) * Real.exp (-L * x ^ 2))
  let f2 : ℝ → ℝ := fun x =>
    (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
      (x ^ (2 * (j + 2)) * Real.exp (-L * x ^ 2))
  let f3 : ℝ → ℝ := fun x =>
    (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
      (x ^ (2 * (j + 3)) * Real.exp (-L * x ^ 2))
  have h0 : IntegrableOn f0 (Ioi 0) := by
    simpa only [MeasureTheory.IntegrableOn, f0] using hg0.const_mul (thetaCuspFullSource 0)
  have h1 : IntegrableOn f1 (Ioi 0) := by
    simpa only [MeasureTheory.IntegrableOn, f1] using
      hg1.const_mul (iteratedDeriv 2 thetaCuspFullSource 0 / 2)
  have h2 : IntegrableOn f2 (Ioi 0) := by
    simpa only [MeasureTheory.IntegrableOn, f2] using
      hg2.const_mul (iteratedDeriv 4 thetaCuspFullSource 0 / 24)
  have h3 : IntegrableOn f3 (Ioi 0) := by
    simpa only [MeasureTheory.IntegrableOn, f3] using
      hg3.const_mul (iteratedDeriv 6 thetaCuspFullSource 0 / 720)
  have h01 := h0.add h1
  have h012 := h01.add h2
  have h01' : IntegrableOn (fun x => f0 x + f1 x) (Ioi 0) := by
    exact h01
  have h012' : IntegrableOn (fun x => f0 x + f1 x + f2 x) (Ioi 0) := by
    exact h012
  have hp :
      IntegrableOn
        (fun x : ℝ =>
          thetaCuspFullSource 0 *
              (x ^ (2 * j) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
              (x ^ (2 * (j + 1)) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
              (x ^ (2 * (j + 2)) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
              (x ^ (2 * (j + 3)) * Real.exp (-L * x ^ 2)))
        (Ioi 0) :=
    by exact h012.add h3
  have hpolyint :
      (∫ x : ℝ in Ioi 0,
          thetaCuspFullSource 0 *
              (x ^ (2 * j) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
              (x ^ (2 * (j + 1)) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
              (x ^ (2 * (j + 2)) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
              (x ^ (2 * (j + 3)) * Real.exp (-L * x ^ 2))) =
        (∫ x : ℝ in Ioi 0,
            thetaCuspFullSource 0 *
              (x ^ (2 * j) * Real.exp (-L * x ^ 2))) +
          (∫ x : ℝ in Ioi 0,
            (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
              (x ^ (2 * (j + 1)) * Real.exp (-L * x ^ 2))) +
          (∫ x : ℝ in Ioi 0,
            (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
              (x ^ (2 * (j + 2)) * Real.exp (-L * x ^ 2))) +
          ∫ x : ℝ in Ioi 0,
            (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
              (x ^ (2 * (j + 3)) * Real.exp (-L * x ^ 2)) := by
    change (∫ x : ℝ in Ioi 0, (((f0 + f1) + f2) + f3) x) =
      (∫ x : ℝ in Ioi 0, f0 x) + (∫ x : ℝ in Ioi 0, f1 x) +
        (∫ x : ℝ in Ioi 0, f2 x) + ∫ x : ℝ in Ioi 0, f3 x
    simp only [Pi.add_apply]
    rw [integral_add h012' h3, integral_add h01' h2, integral_add h0 h1]
  simp only [thetaCuspColdTaylorResidualIntegrand]
  rw [integral_sub hs hp,
    hpolyint,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul,
    integral_coldGaussianHalfMoment hL,
    integral_coldGaussianHalfMoment hL,
    integral_coldGaussianHalfMoment hL,
    integral_coldGaussianHalfMoment hL,
    thetaCuspGaussianApertureHalfMoment,
    thetaCuspColdTaylorMoment]

theorem norm_thetaCuspColdTaylorResidualIntegrand_le
    {L : ℝ} (j : ℕ) {x : ℝ} (hx : x ∈ Ioi 0) :
    ‖thetaCuspColdTaylorResidualIntegrand L j x‖ ≤
      thetaCuspDerivativeExpConstant 8 / 40320 *
        (x ^ (2 * (j + 4)) * Real.exp (-L * x ^ 2)) := by
  have hTaylor := thetaCuspFullSource_taylor_six_remainder_bound hx.le
  have hx0 : 0 ≤ x := hx.le
  rw [Real.norm_eq_abs]
  rw [thetaCuspColdTaylorResidualIntegrand,
    thetaCuspGaussianApertureDensity]
  have hexp0 : 0 ≤ Real.exp (-L * x ^ 2) := Real.exp_nonneg _
  have hfactor :
      x ^ (2 * j) * (Real.exp (-L * x ^ 2) * thetaCuspFullSource x) -
          (thetaCuspFullSource 0 *
              (x ^ (2 * j) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 2 thetaCuspFullSource 0 / 2) *
              (x ^ (2 * (j + 1)) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 4 thetaCuspFullSource 0 / 24) *
              (x ^ (2 * (j + 2)) * Real.exp (-L * x ^ 2)) +
            (iteratedDeriv 6 thetaCuspFullSource 0 / 720) *
              (x ^ (2 * (j + 3)) * Real.exp (-L * x ^ 2))) =
        x ^ (2 * j) * Real.exp (-L * x ^ 2) *
          (thetaCuspFullSource x -
            (thetaCuspFullSource 0 +
              iteratedDeriv 2 thetaCuspFullSource 0 / 2 * x ^ 2 +
              iteratedDeriv 4 thetaCuspFullSource 0 / 24 * x ^ 4 +
              iteratedDeriv 6 thetaCuspFullSource 0 / 720 * x ^ 6)) := by
    ring_nf
  rw [hfactor, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx0 _),
    abs_of_nonneg hexp0]
  calc
    x ^ (2 * j) * Real.exp (-L * x ^ 2) *
        |thetaCuspFullSource x -
          (thetaCuspFullSource 0 +
            iteratedDeriv 2 thetaCuspFullSource 0 / 2 * x ^ 2 +
            iteratedDeriv 4 thetaCuspFullSource 0 / 24 * x ^ 4 +
            iteratedDeriv 6 thetaCuspFullSource 0 / 720 * x ^ 6)| ≤
        x ^ (2 * j) * Real.exp (-L * x ^ 2) *
          (thetaCuspDerivativeExpConstant 8 / 40320 * x ^ 8) := by
      gcongr
    _ = thetaCuspDerivativeExpConstant 8 / 40320 *
        (x ^ (2 * (j + 4)) * Real.exp (-L * x ^ 2)) := by
      ring_nf

theorem abs_thetaCuspGaussianApertureHalfMoment_sub_coldTaylorMoment_le
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    |thetaCuspGaussianApertureHalfMoment (-L) j -
        thetaCuspColdTaylorMoment L j| ≤
      thetaCuspDerivativeExpConstant 8 / 40320 *
        coldGaussianHalfMoment L (j + 4) := by
  let C : ℝ := thetaCuspDerivativeExpConstant 8 / 40320
  have hG := integrableOn_coldGaussianHalfMoment hL (j + 4)
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          C * (x ^ (2 * (j + 4)) * Real.exp (-L * x ^ 2)))
        (Ioi 0) := hG.const_mul C
  rw [← integral_thetaCuspColdTaylorResidualIntegrand hL j,
    ← Real.norm_eq_abs]
  calc
    ‖∫ x : ℝ in Ioi 0,
        thetaCuspColdTaylorResidualIntegrand L j x‖ ≤
        ∫ x : ℝ in Ioi 0,
          C * (x ^ (2 * (j + 4)) * Real.exp (-L * x ^ 2)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_thetaCuspColdTaylorResidualIntegrand_le j hx
    _ = C * coldGaussianHalfMoment L (j + 4) := by
      rw [integral_const_mul, integral_coldGaussianHalfMoment hL]
    _ = thetaCuspDerivativeExpConstant 8 / 40320 *
        coldGaussianHalfMoment L (j + 4) := rfl

def thetaCuspColdNormalizedMoment (L : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureHalfMoment (-L) j /
    (thetaCuspFullSource 0 * coldGaussianHalfMoment L j)

def thetaCuspColdNormalizedJet (L : ℝ) (j : ℕ) : ℝ :=
  1 +
    thetaCuspGaussianApertureColdJetOne *
      coldGammaRising (thetaCuspGaussianApertureGammaShape j) 1 / L +
    thetaCuspGaussianApertureColdJetTwo *
      coldGammaRising (thetaCuspGaussianApertureGammaShape j) 2 / L ^ 2 +
    thetaCuspGaussianApertureColdJetThree *
      coldGammaRising (thetaCuspGaussianApertureGammaShape j) 3 / L ^ 3

theorem thetaCuspColdTaylorMoment_div_eq_normalizedJet
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspColdTaylorMoment L j /
        (thetaCuspFullSource 0 * coldGaussianHalfMoment L j) =
      thetaCuspColdNormalizedJet L j := by
  have hf0 := thetaCuspFullSource_zero_pos_for_cold_seam.ne'
  have hG := (coldGaussianHalfMoment_pos hL j).ne'
  have h1 := coldGaussianHalfMoment_add hL j 1
  have h2 := coldGaussianHalfMoment_add hL j 2
  have h3 := coldGaussianHalfMoment_add hL j 3
  norm_num only [Nat.add_one] at h1
  rw [thetaCuspColdTaylorMoment, h1, h2, h3,
    thetaCuspColdNormalizedJet,
    thetaCuspGaussianApertureColdJetOne,
    thetaCuspGaussianApertureColdJetTwo,
    thetaCuspGaussianApertureColdJetThree]
  field_simp [hf0, hG, hL.ne']

theorem abs_thetaCuspColdNormalizedMoment_sub_normalizedJet_le
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    |thetaCuspColdNormalizedMoment L j -
        thetaCuspColdNormalizedJet L j| ≤
      thetaCuspDerivativeExpConstant 8 /
          (40320 * thetaCuspFullSource 0) *
        coldGammaRising (thetaCuspGaussianApertureGammaShape j) 4 / L ^ 4 := by
  have hf0p := thetaCuspFullSource_zero_pos_for_cold_seam
  have hGp := coldGaussianHalfMoment_pos hL j
  have hdenp :
      0 < thetaCuspFullSource 0 * coldGaussianHalfMoment L j :=
    mul_pos hf0p hGp
  have hrem :=
    abs_thetaCuspGaussianApertureHalfMoment_sub_coldTaylorMoment_le hL j
  have h4 := coldGaussianHalfMoment_add hL j 4
  rw [thetaCuspColdNormalizedMoment,
    ← thetaCuspColdTaylorMoment_div_eq_normalizedJet hL j,
    ← sub_div, abs_div, abs_of_pos hdenp]
  calc
    |thetaCuspGaussianApertureHalfMoment (-L) j -
          thetaCuspColdTaylorMoment L j| /
        (thetaCuspFullSource 0 * coldGaussianHalfMoment L j) ≤
      (thetaCuspDerivativeExpConstant 8 / 40320 *
          coldGaussianHalfMoment L (j + 4)) /
        (thetaCuspFullSource 0 * coldGaussianHalfMoment L j) :=
      div_le_div_of_nonneg_right hrem hdenp.le
    _ = thetaCuspDerivativeExpConstant 8 /
          (40320 * thetaCuspFullSource 0) *
        coldGammaRising (thetaCuspGaussianApertureGammaShape j) 4 / L ^ 4 := by
      rw [h4]
      field_simp [hf0p.ne', hGp.ne', hL.ne']

theorem tendsto_thetaCuspColdNormalizedMoment_sub_normalizedJet_scaled
    (j : ℕ) :
    Tendsto
      (fun L : ℝ => L ^ 3 *
        (thetaCuspColdNormalizedMoment L j -
          thetaCuspColdNormalizedJet L j))
      atTop (nhds 0) := by
  let K : ℝ :=
    thetaCuspDerivativeExpConstant 8 /
        (40320 * thetaCuspFullSource 0) *
      coldGammaRising (thetaCuspGaussianApertureGammaShape j) 4
  have hK :
      Tendsto (fun L : ℝ => K / L) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, zero_mul, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul K)
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hrem :=
    abs_thetaCuspColdNormalizedMoment_sub_normalizedJet_le hL0 j
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hL0.le]
  calc
    L ^ 3 *
        |thetaCuspColdNormalizedMoment L j -
          thetaCuspColdNormalizedJet L j| ≤
      L ^ 3 *
        (thetaCuspDerivativeExpConstant 8 /
            (40320 * thetaCuspFullSource 0) *
          coldGammaRising (thetaCuspGaussianApertureGammaShape j) 4 / L ^ 4) := by
      gcongr
    _ = K / L := by
      dsimp only [K]
      field_simp [hL0.ne']

def thetaCuspColdNormalizedJetOne (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureColdJetOne *
    thetaCuspGaussianApertureGammaShape j

def thetaCuspColdNormalizedJetTwo (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureColdJetTwo *
    thetaCuspGaussianApertureGammaShape j *
    (thetaCuspGaussianApertureGammaShape j + 1)

def thetaCuspColdNormalizedJetThree (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureColdJetThree *
    thetaCuspGaussianApertureGammaShape j *
    (thetaCuspGaussianApertureGammaShape j + 1) *
    (thetaCuspGaussianApertureGammaShape j + 2)

def thetaCuspColdRatioCorrectionTwo (j : ℕ) : ℝ :=
  2 * thetaCuspGaussianApertureColdJetTwo *
      (thetaCuspGaussianApertureGammaShape j + 1) -
    thetaCuspGaussianApertureGammaShape j *
      thetaCuspGaussianApertureColdJetOne ^ 2

def thetaCuspColdRatioJet (L : ℝ) (j : ℕ) : ℝ :=
  1 + thetaCuspGaussianApertureColdJetOne / L +
    thetaCuspColdRatioCorrectionTwo j / L ^ 2 +
    thetaCuspGaussianApertureColdRatioCorrectionThree j / L ^ 3

theorem thetaCuspColdNormalizedJet_eq_coefficients
    (L : ℝ) (j : ℕ) :
    thetaCuspColdNormalizedJet L j =
      1 + thetaCuspColdNormalizedJetOne j / L +
        thetaCuspColdNormalizedJetTwo j / L ^ 2 +
        thetaCuspColdNormalizedJetThree j / L ^ 3 := by
  simp only [thetaCuspColdNormalizedJet, coldGammaRising,
    thetaCuspColdNormalizedJetOne, thetaCuspColdNormalizedJetTwo,
    thetaCuspColdNormalizedJetThree, Finset.prod_range_succ,
    Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, add_zero]
  ring

theorem thetaCuspColdNormalizedJetOne_succ (j : ℕ) :
    thetaCuspColdNormalizedJetOne (j + 1) =
      thetaCuspColdNormalizedJetOne j +
        thetaCuspGaussianApertureColdJetOne := by
  simp only [thetaCuspColdNormalizedJetOne,
    thetaCuspGaussianApertureGammaShape]
  push_cast
  ring

theorem thetaCuspColdNormalizedJetTwo_succ (j : ℕ) :
    thetaCuspColdNormalizedJetTwo (j + 1) =
      thetaCuspColdNormalizedJetTwo j +
        thetaCuspColdNormalizedJetOne j *
          thetaCuspGaussianApertureColdJetOne +
        thetaCuspColdRatioCorrectionTwo j := by
  simp only [thetaCuspColdNormalizedJetTwo,
    thetaCuspColdNormalizedJetOne,
    thetaCuspColdRatioCorrectionTwo,
    thetaCuspGaussianApertureGammaShape]
  push_cast
  ring

theorem thetaCuspColdNormalizedJetThree_succ (j : ℕ) :
    thetaCuspColdNormalizedJetThree (j + 1) =
      thetaCuspColdNormalizedJetThree j +
        thetaCuspColdNormalizedJetOne j *
          thetaCuspColdRatioCorrectionTwo j +
        thetaCuspColdNormalizedJetTwo j *
          thetaCuspGaussianApertureColdJetOne +
        thetaCuspGaussianApertureColdRatioCorrectionThree j := by
  simp only [thetaCuspColdNormalizedJetThree,
    thetaCuspColdNormalizedJetTwo,
    thetaCuspColdNormalizedJetOne,
    thetaCuspColdRatioCorrectionTwo,
    thetaCuspGaussianApertureColdRatioCorrectionThree,
    thetaCuspGaussianApertureGammaShape]
  push_cast
  ring

theorem thetaCuspColdNormalizedJet_quotientResidual
    {L : ℝ} (hL : L ≠ 0) (j : ℕ) :
    L ^ 3 *
        (thetaCuspColdNormalizedJet L (j + 1) -
          thetaCuspColdNormalizedJet L j *
            thetaCuspColdRatioJet L j) =
      -(thetaCuspColdNormalizedJetOne j *
            thetaCuspGaussianApertureColdRatioCorrectionThree j +
          thetaCuspColdNormalizedJetTwo j *
            thetaCuspColdRatioCorrectionTwo j +
          thetaCuspColdNormalizedJetThree j *
            thetaCuspGaussianApertureColdJetOne) / L -
        (thetaCuspColdNormalizedJetTwo j *
            thetaCuspGaussianApertureColdRatioCorrectionThree j +
          thetaCuspColdNormalizedJetThree j *
            thetaCuspColdRatioCorrectionTwo j) / L ^ 2 -
        (thetaCuspColdNormalizedJetThree j *
          thetaCuspGaussianApertureColdRatioCorrectionThree j) / L ^ 3 := by
  rw [thetaCuspColdNormalizedJet_eq_coefficients,
    thetaCuspColdNormalizedJet_eq_coefficients,
    thetaCuspColdRatioJet,
    thetaCuspColdNormalizedJetOne_succ,
    thetaCuspColdNormalizedJetTwo_succ,
    thetaCuspColdNormalizedJetThree_succ]
  field_simp [hL]
  ring

theorem tendsto_thetaCuspColdNormalizedJet_quotientResidual
    (j : ℕ) :
    Tendsto
      (fun L : ℝ => L ^ 3 *
        (thetaCuspColdNormalizedJet L (j + 1) -
          thetaCuspColdNormalizedJet L j *
            thetaCuspColdRatioJet L j))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h1 : Tendsto (fun L : ℝ =>
      -(thetaCuspColdNormalizedJetOne j *
            thetaCuspGaussianApertureColdRatioCorrectionThree j +
          thetaCuspColdNormalizedJetTwo j *
            thetaCuspColdRatioCorrectionTwo j +
          thetaCuspColdNormalizedJetThree j *
            thetaCuspGaussianApertureColdJetOne) / L)
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinv.const_mul
        (-(thetaCuspColdNormalizedJetOne j *
              thetaCuspGaussianApertureColdRatioCorrectionThree j +
            thetaCuspColdNormalizedJetTwo j *
              thetaCuspColdRatioCorrectionTwo j +
            thetaCuspColdNormalizedJetThree j *
              thetaCuspGaussianApertureColdJetOne))
  have h2 : Tendsto (fun L : ℝ =>
      -(thetaCuspColdNormalizedJetTwo j *
            thetaCuspGaussianApertureColdRatioCorrectionThree j +
          thetaCuspColdNormalizedJetThree j *
            thetaCuspColdRatioCorrectionTwo j) / L ^ 2)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (hinv.pow 2).const_mul
        (-(thetaCuspColdNormalizedJetTwo j *
              thetaCuspGaussianApertureColdRatioCorrectionThree j +
            thetaCuspColdNormalizedJetThree j *
              thetaCuspColdRatioCorrectionTwo j))
  have h3 : Tendsto (fun L : ℝ =>
      -(thetaCuspColdNormalizedJetThree j *
          thetaCuspGaussianApertureColdRatioCorrectionThree j) / L ^ 3)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (hinv.pow 3).const_mul
        (-(thetaCuspColdNormalizedJetThree j *
          thetaCuspGaussianApertureColdRatioCorrectionThree j))
  have hev :
      (fun L : ℝ =>
        -(thetaCuspColdNormalizedJetOne j *
              thetaCuspGaussianApertureColdRatioCorrectionThree j +
            thetaCuspColdNormalizedJetTwo j *
              thetaCuspColdRatioCorrectionTwo j +
            thetaCuspColdNormalizedJetThree j *
              thetaCuspGaussianApertureColdJetOne) / L +
          -(thetaCuspColdNormalizedJetTwo j *
              thetaCuspGaussianApertureColdRatioCorrectionThree j +
            thetaCuspColdNormalizedJetThree j *
              thetaCuspColdRatioCorrectionTwo j) / L ^ 2 +
          -(thetaCuspColdNormalizedJetThree j *
            thetaCuspGaussianApertureColdRatioCorrectionThree j) / L ^ 3) =ᶠ[atTop]
        (fun L : ℝ => L ^ 3 *
          (thetaCuspColdNormalizedJet L (j + 1) -
            thetaCuspColdNormalizedJet L j *
              thetaCuspColdRatioJet L j)) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
    rw [thetaCuspColdNormalizedJet_quotientResidual hL j]
    ring
  simpa only [zero_add] using ((h1.add h2).add h3).congr' hev

theorem thetaCuspColdNormalizedMoment_pos
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    0 < thetaCuspColdNormalizedMoment L j := by
  rw [thetaCuspColdNormalizedMoment]
  exact div_pos
    (thetaCuspGaussianApertureHalfMoment_pos (by linarith) j)
    (mul_pos thetaCuspFullSource_zero_pos_for_cold_seam
      (coldGaussianHalfMoment_pos hL j))

theorem tendsto_thetaCuspColdNormalizedJet (j : ℕ) :
    Tendsto (fun L : ℝ => thetaCuspColdNormalizedJet L j)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  rw [show (fun L : ℝ => thetaCuspColdNormalizedJet L j) =
      fun L => 1 +
        thetaCuspColdNormalizedJetOne j * L⁻¹ +
        thetaCuspColdNormalizedJetTwo j * (L⁻¹) ^ 2 +
        thetaCuspColdNormalizedJetThree j * (L⁻¹) ^ 3 by
    funext L
    rw [thetaCuspColdNormalizedJet_eq_coefficients]
    simp only [div_eq_mul_inv, inv_pow]]
  have h0 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h1 := hinv.const_mul (thetaCuspColdNormalizedJetOne j)
  have h2 := (hinv.pow 2).const_mul (thetaCuspColdNormalizedJetTwo j)
  have h3 := (hinv.pow 3).const_mul (thetaCuspColdNormalizedJetThree j)
  simpa using (((h0.add h1).add h2).add h3)

theorem tendsto_thetaCuspColdNormalizedMoment_sub_normalizedJet
    (j : ℕ) :
    Tendsto
      (fun L : ℝ =>
        thetaCuspColdNormalizedMoment L j -
          thetaCuspColdNormalizedJet L j)
      atTop (nhds 0) := by
  have hscaled :=
    tendsto_thetaCuspColdNormalizedMoment_sub_normalizedJet_scaled j
  have hinv3 :
      Tendsto (fun L : ℝ => (L⁻¹) ^ 3) atTop (nhds 0) := by
    simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 3)
  have h :
      Tendsto
        (fun L : ℝ =>
          (L ^ 3 *
            (thetaCuspColdNormalizedMoment L j -
              thetaCuspColdNormalizedJet L j)) * (L⁻¹) ^ 3)
        atTop (nhds 0) := by
    simpa only [mul_zero] using hscaled.mul hinv3
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
  field_simp [hL]

theorem tendsto_thetaCuspColdNormalizedMoment (j : ℕ) :
    Tendsto (fun L : ℝ => thetaCuspColdNormalizedMoment L j)
      atTop (nhds 1) := by
  have h :=
    (tendsto_thetaCuspColdNormalizedMoment_sub_normalizedJet j).add
      (tendsto_thetaCuspColdNormalizedJet j)
  have h' :
      Tendsto
        (fun L : ℝ =>
          (thetaCuspColdNormalizedMoment L j -
              thetaCuspColdNormalizedJet L j) +
            thetaCuspColdNormalizedJet L j)
        atTop (nhds 1) := by
    simpa only [zero_add] using h
  apply h'.congr'
  exact Eventually.of_forall fun L => by ring

theorem tendsto_thetaCuspColdRatioJet (j : ℕ) :
    Tendsto (fun L : ℝ => thetaCuspColdRatioJet L j)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  rw [show (fun L : ℝ => thetaCuspColdRatioJet L j) =
      fun L => 1 +
        thetaCuspGaussianApertureColdJetOne * L⁻¹ +
        thetaCuspColdRatioCorrectionTwo j * (L⁻¹) ^ 2 +
        thetaCuspGaussianApertureColdRatioCorrectionThree j *
          (L⁻¹) ^ 3 by
    funext L
    simp only [thetaCuspColdRatioJet, div_eq_mul_inv, inv_pow]]
  have h0 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h1 := hinv.const_mul thetaCuspGaussianApertureColdJetOne
  have h2 := (hinv.pow 2).const_mul (thetaCuspColdRatioCorrectionTwo j)
  have h3 := (hinv.pow 3).const_mul
    (thetaCuspGaussianApertureColdRatioCorrectionThree j)
  simpa using (((h0.add h1).add h2).add h3)

theorem tendsto_thetaCuspColdNormalizedMoment_quotient_sub_ratioJet_scaled
    (j : ℕ) :
    Tendsto
      (fun L : ℝ => L ^ 3 *
        (thetaCuspColdNormalizedMoment L (j + 1) /
            thetaCuspColdNormalizedMoment L j -
          thetaCuspColdRatioJet L j))
      atTop (nhds 0) := by
  have hE :=
    tendsto_thetaCuspColdNormalizedMoment_sub_normalizedJet_scaled j
  have hE1 :=
    tendsto_thetaCuspColdNormalizedMoment_sub_normalizedJet_scaled (j + 1)
  have hR := tendsto_thetaCuspColdRatioJet j
  have hPResidual :=
    tendsto_thetaCuspColdNormalizedJet_quotientResidual j
  have hN := tendsto_thetaCuspColdNormalizedMoment j
  have hnum :=
    (hE1.sub (hE.mul hR)).add hPResidual
  have hquot := hnum.div hN (by norm_num)
  have hquot' :
      Tendsto
        (fun L : ℝ =>
          (L ^ 3 *
                (thetaCuspColdNormalizedMoment L (j + 1) -
                  thetaCuspColdNormalizedJet L (j + 1)) -
              L ^ 3 *
                  (thetaCuspColdNormalizedMoment L j -
                    thetaCuspColdNormalizedJet L j) *
                thetaCuspColdRatioJet L j +
              L ^ 3 *
                (thetaCuspColdNormalizedJet L (j + 1) -
                  thetaCuspColdNormalizedJet L j *
                    thetaCuspColdRatioJet L j)) /
            thetaCuspColdNormalizedMoment L j)
        atTop (nhds 0) := by
    have hval : (0 - 0 * 1 + 0 : ℝ) / 1 = 0 := by norm_num
    rw [hval] at hquot
    exact hquot
  apply hquot'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hN0 := (thetaCuspColdNormalizedMoment_pos hL0 j).ne'
  field_simp [hN0]
  ring

theorem thetaCuspGaussianApertureGammaRatio_neg_eq_coldNormalizedMoment
    {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaRatio (-L) j =
      thetaCuspColdNormalizedMoment L (j + 1) /
        (L * thetaCuspColdNormalizedMoment L j) := by
  have hf0 := thetaCuspFullSource_zero_pos_for_cold_seam.ne'
  have hG0 := (coldGaussianHalfMoment_pos hL j).ne'
  have hG1 := (coldGaussianHalfMoment_pos hL (j + 1)).ne'
  have hH0 :=
    (thetaCuspGaussianApertureHalfMoment_pos
      (lambda := -L) (by linarith) j).ne'
  have ha := (thetaCuspGaussianApertureGammaShape_pos j).ne'
  have hsucc := coldGaussianHalfMoment_succ hL j
  have hsucc' :
      L * coldGaussianHalfMoment L (j + 1) =
        thetaCuspGaussianApertureGammaShape j *
          coldGaussianHalfMoment L j := by
    rw [hsucc]
    field_simp [hL.ne']
  rw [thetaCuspGaussianApertureGammaRatio,
    thetaCuspColdNormalizedMoment, thetaCuspColdNormalizedMoment]
  field_simp [hf0, hG0, hG1, hH0, ha, hL.ne']
  calc
    L * thetaCuspGaussianApertureHalfMoment (-L) (j + 1) *
          coldGaussianHalfMoment L (j + 1) =
        thetaCuspGaussianApertureHalfMoment (-L) (j + 1) *
          (L * coldGaussianHalfMoment L (j + 1)) := by ring
    _ = thetaCuspGaussianApertureHalfMoment (-L) (j + 1) *
          (thetaCuspGaussianApertureGammaShape j *
            coldGaussianHalfMoment L j) := by rw [hsucc']
    _ = thetaCuspGaussianApertureHalfMoment (-L) (j + 1) *
          thetaCuspGaussianApertureGammaShape j *
            coldGaussianHalfMoment L j := by ring

theorem thetaCuspColdRatioCorrectionTwo_secondDiff (j : ℕ) :
    thetaCuspColdRatioCorrectionTwo j -
        2 * thetaCuspColdRatioCorrectionTwo (j + 1) +
        thetaCuspColdRatioCorrectionTwo (j + 2) = 0 := by
  simp only [thetaCuspColdRatioCorrectionTwo,
    thetaCuspGaussianApertureGammaShape]
  push_cast
  ring

theorem thetaCuspColdRatioJet_secondDiff_scaled
    {L : ℝ} (hL : L ≠ 0) (j : ℕ) :
    L ^ 3 *
        (thetaCuspColdRatioJet L j -
          2 * thetaCuspColdRatioJet L (j + 1) +
          thetaCuspColdRatioJet L (j + 2)) =
      thetaCuspGaussianApertureColdRatioCorrectionThree j -
        2 * thetaCuspGaussianApertureColdRatioCorrectionThree (j + 1) +
        thetaCuspGaussianApertureColdRatioCorrectionThree (j + 2) := by
  have htwo := thetaCuspColdRatioCorrectionTwo_secondDiff j
  rw [thetaCuspColdRatioJet, thetaCuspColdRatioJet,
    thetaCuspColdRatioJet]
  field_simp [hL]
  linear_combination L * htwo

theorem tendsto_thetaCuspGaussianApertureRatioCurvature_cold_scaled
    (j : ℕ) :
    Tendsto
      (fun L : ℝ =>
        L ^ 4 * thetaCuspGaussianApertureRatioCurvature (-L) j)
      atTop
      (nhds
        (thetaCuspGaussianApertureColdRatioCorrectionThree j -
          2 * thetaCuspGaussianApertureColdRatioCorrectionThree (j + 1) +
          thetaCuspGaussianApertureColdRatioCorrectionThree (j + 2))) := by
  have h0 :=
    tendsto_thetaCuspColdNormalizedMoment_quotient_sub_ratioJet_scaled j
  have h1 :=
    tendsto_thetaCuspColdNormalizedMoment_quotient_sub_ratioJet_scaled (j + 1)
  have h2 :=
    tendsto_thetaCuspColdNormalizedMoment_quotient_sub_ratioJet_scaled (j + 2)
  have herr := (h0.sub (h1.const_mul 2)).add h2
  let D : ℝ :=
    thetaCuspGaussianApertureColdRatioCorrectionThree j -
      2 * thetaCuspGaussianApertureColdRatioCorrectionThree (j + 1) +
      thetaCuspGaussianApertureColdRatioCorrectionThree (j + 2)
  have htotal := herr.add (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => D) atTop (nhds D))
  have htotal' :
      Tendsto
        (fun L : ℝ =>
          (L ^ 3 *
                (thetaCuspColdNormalizedMoment L (j + 1) /
                    thetaCuspColdNormalizedMoment L j -
                  thetaCuspColdRatioJet L j) -
              2 * (L ^ 3 *
                (thetaCuspColdNormalizedMoment L (j + 1 + 1) /
                    thetaCuspColdNormalizedMoment L (j + 1) -
                  thetaCuspColdRatioJet L (j + 1))) +
              L ^ 3 *
                (thetaCuspColdNormalizedMoment L (j + 2 + 1) /
                    thetaCuspColdNormalizedMoment L (j + 2) -
                  thetaCuspColdRatioJet L (j + 2))) + D)
        atTop (nhds D) := by
    simpa only [mul_zero, sub_zero, add_zero, zero_add] using htotal
  apply htotal'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hjet := thetaCuspColdRatioJet_secondDiff_scaled hL0.ne' j
  have hN0 := (thetaCuspColdNormalizedMoment_pos hL0 j).ne'
  have hN1 := (thetaCuspColdNormalizedMoment_pos hL0 (j + 1)).ne'
  have hN2 := (thetaCuspColdNormalizedMoment_pos hL0 (j + 2)).ne'
  rw [thetaCuspGaussianApertureRatioCurvature,
    thetaCuspGaussianApertureGammaRatio_neg_eq_coldNormalizedMoment hL0,
    thetaCuspGaussianApertureGammaRatio_neg_eq_coldNormalizedMoment hL0,
    thetaCuspGaussianApertureGammaRatio_neg_eq_coldNormalizedMoment hL0]
  dsimp only [D]
  rw [← hjet]
  field_simp [hL0.ne', hN0, hN1, hN2]
  ring

theorem eventually_thetaCuspGaussianApertureRatioCurvature_neg_pos
    (j : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      0 < thetaCuspGaussianApertureRatioCurvature (-L) j := by
  let D : ℝ :=
    thetaCuspGaussianApertureColdRatioCorrectionThree j -
      2 * thetaCuspGaussianApertureColdRatioCorrectionThree (j + 1) +
      thetaCuspGaussianApertureColdRatioCorrectionThree (j + 2)
  have hD : 0 < D := by
    dsimp only [D]
    rw [thetaCuspGaussianApertureColdRatioCorrectionThree_secondDiff]
    exact div_pos thetaCuspGaussianApertureSixthSeamNumerator_pos
      (mul_pos (by norm_num)
        (pow_pos thetaCuspFullSource_zero_pos_for_cold_seam 3))
  have hscaled :
      ∀ᶠ L : ℝ in atTop,
        0 < L ^ 4 *
          thetaCuspGaussianApertureRatioCurvature (-L) j :=
    (tendsto_thetaCuspGaussianApertureRatioCurvature_cold_scaled j).eventually
      (Ioi_mem_nhds hD)
  filter_upwards [hscaled, eventually_gt_atTop (0 : ℝ)] with L hprod hL
  exact pos_of_mul_pos_right hprod (pow_nonneg hL.le 4)

theorem eventually_thetaCuspGaussianApertureRatioCurvature_neg_pos_finiteSection
    (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ j, j ≤ J →
      0 < thetaCuspGaussianApertureRatioCurvature (-L) j := by
  have hfinite :
      ∀ᶠ L : ℝ in atTop, ∀ j ∈ Finset.range (J + 1),
        0 < thetaCuspGaussianApertureRatioCurvature (-L) j := by
    rw [Finset.eventually_all]
    intro j hj
    exact eventually_thetaCuspGaussianApertureRatioCurvature_neg_pos j
  filter_upwards [hfinite] with L hL
  intro j hj
  exact hL j (Finset.mem_range.mpr (by omega))

theorem exists_cold_thetaCuspGaussianApertureRatioCurvature_finiteSection_pos
    {b : ℝ} (hb : b < 0) (J : ℕ) :
    ∃ a : ℝ, a ≤ b ∧ a < 0 ∧ ∀ j, j ≤ J →
      0 < thetaCuspGaussianApertureRatioCurvature a j := by
  have hev :
      ∀ᶠ L : ℝ in atTop,
        -b ≤ L ∧ ∀ j, j ≤ J →
          0 < thetaCuspGaussianApertureRatioCurvature (-L) j := by
    filter_upwards [eventually_ge_atTop (-b),
      eventually_thetaCuspGaussianApertureRatioCurvature_neg_pos_finiteSection J]
      with L hLb hcurv
    exact ⟨hLb, hcurv⟩
  obtain ⟨L, hLb, hcurv⟩ := hev.exists
  refine ⟨-L, by linarith, by linarith, hcurv⟩

theorem exists_cold_thetaCuspGaussianApertureRatioCurvature_finiteSection_transport
    {b : ℝ} (hb : b < 0) (J : ℕ) :
    ∃ a : ℝ, a ≤ b ∧ a < 0 ∧
      ((∀ lambda ∈ Icc a b,
          0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1)) →
        ∀ j, j ≤ J → ∀ lambda ∈ Icc a b,
          0 ≤ thetaCuspGaussianApertureRatioCurvature lambda j) := by
  obtain ⟨a, hab, ha, hinit⟩ :=
    exists_cold_thetaCuspGaussianApertureRatioCurvature_finiteSection_pos hb J
  refine ⟨a, hab, ha, ?_⟩
  intro hboundary
  exact thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
    hab hb J (fun j hj => (hinit j hj).le) hboundary

theorem exists_cold_thetaCuspGaussianApertureBalance_finiteSection_transport
    {b : ℝ} (hb : b < 0) (J : ℕ) :
    ∃ a : ℝ, a ≤ b ∧ a < 0 ∧
      ((∀ lambda ∈ Icc a b,
          0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1)) →
        ∀ lambda ∈ Icc a b,
          0 ≤ thetaCuspGaussianApertureBalance lambda) := by
  obtain ⟨a, hab, ha, htransport⟩ :=
    exists_cold_thetaCuspGaussianApertureRatioCurvature_finiteSection_transport hb J
  refine ⟨a, hab, ha, ?_⟩
  intro hboundary lambda hlambda
  rw [thetaCuspGaussianApertureBalance_eq_ratioCurvature]
  exact mul_nonneg (by norm_num)
    (htransport hboundary 0 (Nat.zero_le J) lambda hlambda)

end

end RHTower
