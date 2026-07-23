import GaloisForLFunctions.RHTower.ThetaCuspShellHedenmalmCurrent
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Convex.Deriv

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Multiplicative Gaussian coordinate of the `n`-th positive theta shell. -/
def thetaCuspShellGammaMap (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * Real.exp (2 * x)

/-- Logarithmic inverse of `thetaCuspShellGammaMap` on its positive image. -/
def thetaCuspShellGammaCoordinate (n : ℕ) (t : ℝ) : ℝ :=
  Real.log (t / (n : ℝ) ^ 2) / 2

/-- Pushforward of one completed theta shell under its multiplicative Gaussian coordinate. -/
def thetaCuspShellGammaIntegrand
    (P : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ((thetaCuspSourceTerm (thetaCuspShellGammaCoordinate n t) n / (2 * t) : ℝ) : ℂ) *
    P (thetaCuspShellGammaCoordinate n t)

@[simp] theorem thetaCuspShellGammaMap_zero (n : ℕ) :
    thetaCuspShellGammaMap n 0 = (n : ℝ) ^ 2 := by
  simp [thetaCuspShellGammaMap]

theorem thetaCuspShellGammaMap_pos
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 < thetaCuspShellGammaMap n x := by
  unfold thetaCuspShellGammaMap
  positivity

@[simp] theorem thetaCuspShellGammaCoordinate_map
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    thetaCuspShellGammaCoordinate n (thetaCuspShellGammaMap n x) = x := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold thetaCuspShellGammaCoordinate thetaCuspShellGammaMap
  rw [show (n : ℝ) ^ 2 * Real.exp (2 * x) / (n : ℝ) ^ 2 =
      Real.exp (2 * x) by field_simp]
  rw [Real.log_exp]
  ring

theorem thetaCuspShellGamma_deriv_smul_integrand
    (P : ℝ → ℂ) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (2 * thetaCuspShellGammaMap n x) •
        thetaCuspShellGammaIntegrand P n (thetaCuspShellGammaMap n x) =
      (thetaCuspSourceTerm x n : ℂ) * P x := by
  have hmap : thetaCuspShellGammaMap n x ≠ 0 :=
    (thetaCuspShellGammaMap_pos hn x).ne'
  have hmapC : (thetaCuspShellGammaMap n x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hmap
  rw [thetaCuspShellGammaIntegrand, thetaCuspShellGammaCoordinate_map hn]
  rw [Complex.real_smul]
  push_cast
  field_simp [hmapC]

/-- Exact incomplete-Gamma coordinate for every positive completed theta shell. -/
theorem thetaCuspShellHalfLineTransform_eq_gammaIntegral
    (P : ℝ → ℂ) (hP : Continuous P)
    {n : ℕ} (hn : 0 < n)
    (hInt : IntegrableOn
      (fun x : ℝ => (thetaCuspSourceTerm x n : ℂ) * P x) (Ioi 0)) :
    thetaCuspShellHalfLineTransform P n =
      ∫ t : ℝ in Ioi ((n : ℝ) ^ 2),
        thetaCuspShellGammaIntegrand P n t := by
  let f : ℝ → ℝ := thetaCuspShellGammaMap n
  let f' : ℝ → ℝ := fun x => 2 * thetaCuspShellGammaMap n x
  let g : ℝ → ℂ := thetaCuspShellGammaIntegrand P n
  have hf : ContinuousOn f (Ici 0) := by
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  have hft : Tendsto f atTop atTop := by
    dsimp [f, thetaCuspShellGammaMap]
    apply Filter.Tendsto.const_mul_atTop
    · positivity
    · exact Real.tendsto_exp_atTop.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hderiv (x : ℝ) :
      HasDerivAt f (f' x) x := by
    dsimp [f, f', thetaCuspShellGammaMap]
    convert ((Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2)).const_mul ((n : ℝ) ^ 2) using 1
    all_goals ring
  have hff' : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x _hx
    exact (hderiv x).hasDerivWithinAt
  have hderivIci : ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt f (f' x) (Ici 0) x := by
    intro x _hx
    exact (hderiv x).hasDerivWithinAt
  have hmono : MonotoneOn f (Ici (0 : ℝ)) := by
    intro x _hx y _hy hxy
    dsimp [f, thetaCuspShellGammaMap]
    gcongr
  have hgcont : ContinuousOn g (f '' Ioi (0 : ℝ)) := by
    have hgpos : ContinuousOn g (Ioi 0) := by
      intro t ht
      have hnR : 0 < (n : ℝ) ^ 2 := by positivity
      have hratio : 0 < t / (n : ℝ) ^ 2 := div_pos ht hnR
      have htpos : 0 < t := ht
      have htne : 2 * t ≠ 0 := by nlinarith
      have hcoord : ContinuousAt (thetaCuspShellGammaCoordinate n) t := by
        unfold thetaCuspShellGammaCoordinate
        fun_prop
      have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
        unfold thetaCuspSourceTerm thetaCuspSeed
        fun_prop
      have hsourceCoord :
          ContinuousAt
            (fun u => thetaCuspSourceTerm (thetaCuspShellGammaCoordinate n u) n) t :=
        hsource.continuousAt.comp hcoord
      have hquot :
          ContinuousAt
            (fun u => thetaCuspSourceTerm (thetaCuspShellGammaCoordinate n u) n /
              (2 * u)) t :=
        hsourceCoord.div (continuous_const.mul continuous_id).continuousAt htne
      have hPcoord :
          ContinuousAt (fun u => P (thetaCuspShellGammaCoordinate n u)) t :=
        hP.continuousAt.comp hcoord
      apply ContinuousAt.continuousWithinAt
      exact (Complex.continuous_ofReal.continuousAt.comp hquot).mul hPcoord
    exact hgpos.mono (by
      rintro _ ⟨x, _hx, rfl⟩
      exact thetaCuspShellGammaMap_pos hn x)
  have hcompose :
      (fun x : ℝ => f' x • (g ∘ f) x) =
        fun x : ℝ => (thetaCuspSourceTerm x n : ℂ) * P x := by
    funext x
    exact thetaCuspShellGamma_deriv_smul_integrand P hn x
  have hg2 : IntegrableOn
      (fun x : ℝ => f' x • (g ∘ f) x) (Ici 0) := by
    rw [hcompose, integrableOn_Ici_iff_integrableOn_Ioi]
    exact hInt
  have hg1 : IntegrableOn g (f '' Ici (0 : ℝ)) :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Ici hderivIci hmono g).2 hg2
  have hsubst := integral_deriv_smul_comp_Ioi
    hf hft hff' hgcont hg1 hg2
  rw [hcompose] at hsubst
  simpa only [thetaCuspShellHalfLineTransform, f, thetaCuspShellGammaMap_zero, g]
    using hsubst

/-- Explicit exponentially damped amplitude in the incomplete-Gamma coordinate. -/
def thetaCuspShellGammaAmplitude (n : ℕ) (t : ℝ) : ℝ :=
  Real.pi * Real.exp (Real.log (t / (n : ℝ) ^ 2) / 4) *
    (2 * Real.pi * t - 3) * Real.exp (-Real.pi * t)

theorem thetaCuspShellGammaIntegrand_eq_explicit
    (P : ℝ → ℂ) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    thetaCuspShellGammaIntegrand P n t =
      (thetaCuspShellGammaAmplitude n t : ℂ) *
        P (thetaCuspShellGammaCoordinate n t) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hnR
  have hratio : 0 < t / (n : ℝ) ^ 2 := div_pos ht hn2
  have hsquare :
      ((n : ℝ) * Real.exp (thetaCuspShellGammaCoordinate n t)) ^ 2 = t := by
    rw [mul_pow, ← Real.exp_nat_mul]
    change (n : ℝ) ^ 2 *
        Real.exp (2 * thetaCuspShellGammaCoordinate n t) = t
    rw [show (2 : ℝ) * thetaCuspShellGammaCoordinate n t =
        Real.log (t / (n : ℝ) ^ 2) by
      unfold thetaCuspShellGammaCoordinate
      ring]
    rw [Real.exp_log hratio]
    field_simp
  have hfour :
      ((n : ℝ) * Real.exp (thetaCuspShellGammaCoordinate n t)) ^ 4 = t ^ 2 := by
    calc
      ((n : ℝ) * Real.exp (thetaCuspShellGammaCoordinate n t)) ^ 4 =
          (((n : ℝ) * Real.exp (thetaCuspShellGammaCoordinate n t)) ^ 2) ^ 2 := by
            ring
      _ = t ^ 2 := by rw [hsquare]
  have hdensity :
      thetaCuspSourceTerm (thetaCuspShellGammaCoordinate n t) n / (2 * t) =
        thetaCuspShellGammaAmplitude n t := by
    unfold thetaCuspSourceTerm thetaCuspSeed thetaCuspShellGammaAmplitude
    rw [hsquare, hfour]
    rw [show thetaCuspShellGammaCoordinate n t / 2 =
        Real.log (t / (n : ℝ) ^ 2) / 4 by
      unfold thetaCuspShellGammaCoordinate
      ring]
    field_simp [ht.ne']
  unfold thetaCuspShellGammaIntegrand
  rw [hdensity]

/-- Shell dependence in the inverse coordinate is a pure logarithmic translation. -/
theorem thetaCuspShellGammaCoordinate_eq_sub_log
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    thetaCuspShellGammaCoordinate n t =
      Real.log t / 2 - Real.log (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold thetaCuspShellGammaCoordinate
  rw [Real.log_div ht.ne' (sq_pos_of_pos hnR).ne',
    Real.log_pow]
  push_cast
  ring

/-- Universal Gaussian amplitude after extracting the shell translation. -/
def thetaCuspUniversalGammaAmplitude (t : ℝ) : ℝ :=
  Real.pi * Real.exp (Real.log t / 4) *
    (2 * Real.pi * t - 3) * Real.exp (-Real.pi * t)

theorem thetaCuspShellGammaAmplitude_eq_universal
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    thetaCuspShellGammaAmplitude n t =
      Real.exp (-Real.log (n : ℝ) / 2) *
        thetaCuspUniversalGammaAmplitude t := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold thetaCuspShellGammaAmplitude thetaCuspUniversalGammaAmplitude
  rw [Real.log_div ht.ne' (sq_pos_of_pos hnR).ne', Real.log_pow]
  push_cast
  rw [show (Real.log t - 2 * Real.log (n : ℝ)) / 4 =
      -Real.log (n : ℝ) / 2 + Real.log t / 4 by ring,
    Real.exp_add]
  ring

/-- Universal complex incomplete-Gamma kernel before the shell-dependent lower cut. -/
def thetaCuspUniversalGammaPhaseIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  (thetaCuspUniversalGammaAmplitude t : ℂ) *
    spectralTranslationPhase (Real.log t / 2) z

/-- Exact separation of shell translation from the universal incomplete-Gamma kernel. -/
theorem thetaCuspShellGammaPhaseIntegrand_eq_universal
    {z : ℂ} {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    thetaCuspShellGammaIntegrand
        (fun x => spectralTranslationPhase x z) n t =
      ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
        spectralTranslationPhase (-Real.log (n : ℝ)) z *
          thetaCuspUniversalGammaPhaseIntegrand z t := by
  rw [thetaCuspShellGammaIntegrand_eq_explicit _ hn ht,
    thetaCuspShellGammaAmplitude_eq_universal hn ht,
    thetaCuspShellGammaCoordinate_eq_sub_log hn ht]
  rw [show Real.log t / 2 - Real.log (n : ℝ) =
      -Real.log (n : ℝ) + Real.log t / 2 by ring,
    spectralTranslationPhase_add]
  unfold thetaCuspUniversalGammaPhaseIntegrand
  push_cast
  ring

/-- Product-fibre shell cuts multiply to the square of the fibre index. -/
theorem thetaCuspShellGammaThreshold_productFiber
    {m n k : ℕ} (h : m * n = k) :
    (m : ℝ) ^ 2 * (n : ℝ) ^ 2 = (k : ℝ) ^ 2 := by
  subst k
  push_cast
  ring

private lemma norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma
    (t : ℝ) (z : ℂ) :
    ‖spectralTranslationPhase t z‖ = Real.exp (-t * z.im) := by
  unfold spectralTranslationPhase
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Every polynomial theta atom remains phase-integrable on a positive half-line whenever the
phase growth stays below the atom's exponential envelope. -/
theorem integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n)
    {z : ℂ} (hz : -1 < z.im) :
    IntegrableOn
      (fun x : ℝ =>
        (thetaCuspPolynomialAtom P n x : ℂ) *
          spectralTranslationPhase x z)
      (Ioi 0) := by
  have hmajor :=
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      P hn (z := -z.im) (by linarith)
  apply Integrable.mono hmajor
  · have hcont :
        Continuous (thetaCuspPolynomialAtom P n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom P n x).continuousAt
    exact ((Complex.continuous_ofReal.comp hcont).mul
      (by
        unfold spectralTranslationPhase
        fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real,
      norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma,
      Real.norm_eq_abs]
    rw [show -x * z.im = -z.im * x by ring]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]

theorem integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : -1 < z.im) :
    IntegrableOn
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) * spectralTranslationPhase x z)
      (Ioi 0) := by
  have hmajor :=
    integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
      hn (z := -z.im) (by linarith)
  change Integrable
    (fun x : ℝ =>
      (thetaCuspSourceTerm x n : ℂ) * spectralTranslationPhase x z)
    (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop
    exact ((Complex.continuous_ofReal.comp hsource).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hsource0 : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hsource0,
      norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsource0)]
    rw [show -x * z.im = -z.im * x by ring]
    simp only [mul_comm, le_refl]

/-- One spectral insertion remains integrable shellwise throughout the open Fourier strip. -/
theorem integrableOn_thetaCuspSourceTerm_mul_phaseSpectralDerivative
    {z : ℂ} (hz : |z.im| < 1) (n : ℕ) :
    IntegrableOn
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          (((x : ℂ) * I) * spectralTranslationPhase x z))
      (Ioi 0) := by
  have hfull :
      IntegrableOn
        (thetaCuspFourierLaplaceJetIntegrand 1 (-z))
        (Ioi 0) :=
    (integrable_thetaCuspFourierLaplaceJetIntegrand 1
      (by simpa only [neg_im, abs_neg] using hz)).integrableOn
  apply Integrable.mono hfull
  · exact ((by
      unfold thetaCuspSourceTerm thetaCuspSeed spectralTranslationPhase
      fun_prop : Continuous (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          (((x : ℂ) * I) * spectralTranslationPhase x z)))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hterm0 : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    have hfull0 : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    have hterm :
        thetaCuspSourceTerm x n ≤ thetaCuspFullSource x := by
      rw [thetaCuspFullSource]
      exact (summable_thetaCuspSourceTerm x).le_tsum n
        (fun k _ => thetaCuspSourceTerm_nonneg_of_pos hx k)
    rw [thetaCuspFourierLaplaceJetIntegrand,
      thetaCuspFourierLaplaceIntegrand]
    simp only [pow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hterm0, abs_of_nonneg hx0, abs_of_nonneg hfull0,
      norm_I, norm_neg, mul_one, one_mul]
    have hphase :
        Complex.exp (-I * -z * (x : ℂ)) =
          spectralTranslationPhase x z := by
      unfold spectralTranslationPhase
      congr 1
      ring
    rw [hphase]
    calc
      thetaCuspSourceTerm x n *
          (x * ‖spectralTranslationPhase x z‖) =
        (x * ‖spectralTranslationPhase x z‖) *
          thetaCuspSourceTerm x n := by ring
      _ ≤ (x * ‖spectralTranslationPhase x z‖) *
          thetaCuspFullSource x :=
        mul_le_mul_of_nonneg_left hterm
          (mul_nonneg hx0 (norm_nonneg _))
      _ = x * (‖spectralTranslationPhase x z‖ *
          thetaCuspFullSource x) := by ring

/-- A positive shell branch is holomorphic in the lower open half-strip.  Its derivative is the
literal `i x` spectral insertion, not a formal `deriv` placeholder. -/
theorem hasDerivAt_thetaCuspShellPhaseTransform
    {z₀ : ℂ} (hz₀ : -1 < z₀.im) {n : ℕ} (hn : 0 < n) :
    HasDerivAt
      (fun z =>
        thetaCuspShellHalfLineTransform
          (fun x => spectralTranslationPhase x z) n)
      (thetaCuspShellHalfLineTransform
        (fun x => ((x : ℂ) * I) *
          spectralTranslationPhase x z₀) n) z₀ := by
  let ε : ℝ := (1 + z₀.im) / 4
  let L : ℝ := z₀.im - ε
  let c : ℝ := -L
  let d : ℝ := (1 - c) / 2
  let q : ℝ := c + d
  let C : ℝ := 1 / d
  let bound : ℝ → ℝ := fun x =>
    C * (Real.exp (q * x) * thetaCuspSourceTerm x n)
  let F : ℂ → ℝ → ℂ := fun z x =>
    (thetaCuspSourceTerm x n : ℂ) *
      spectralTranslationPhase x z
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (thetaCuspSourceTerm x n : ℂ) *
      (((x : ℂ) * I) * spectralTranslationPhase x z)
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  have hL : -1 < L := by
    dsimp only [L, ε]
    linarith
  have hc : c < 1 := by
    dsimp only [c]
    linarith
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hq : q < 1 := by
    dsimp only [q, d]
    linarith
  have him {z : ℂ} (hz : z ∈ Metric.ball z₀ ε) :
      L < z.im := by
    have hdist : ‖z - z₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have himdiff : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
    have hlower : -‖z - z₀‖ ≤ z.im - z₀.im :=
      (abs_le.mp himdiff).1
    dsimp only [L]
    linarith
  have hbound :
      Integrable bound (volume.restrict (Ioi 0)) := by
    dsimp only [bound]
    exact
      (integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
        hn hq).const_mul C
  have hFmeas : ∀ z : ℂ,
      AEStronglyMeasurable (F z)
        (volume.restrict (Ioi 0)) := by
    intro z
    have hsource :
        Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop
    dsimp only [F]
    exact ((Complex.continuous_ofReal.comp hsource).mul
      (by
        unfold spectralTranslationPhase
        fun_prop)).aestronglyMeasurable.restrict
  have hF'meas :
      AEStronglyMeasurable (F' z₀)
        (volume.restrict (Ioi 0)) := by
    have hsource :
        Continuous (fun x : ℝ => thetaCuspSourceTerm x n) := by
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop
    dsimp only [F']
    exact ((Complex.continuous_ofReal.comp hsource).mul
      (((Complex.continuous_ofReal.comp continuous_id).mul
        continuous_const).mul
        (by
          unfold spectralTranslationPhase
          fun_prop))).aestronglyMeasurable.restrict
  have hdom : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    have hx0 : 0 ≤ x := hx.le
    have hzL := him hz
    have hrate : -z.im ≤ c := by
      dsimp only [c]
      linarith
    have hdx0 : 0 ≤ d * x := mul_nonneg hd.le hx0
    have hdxle : d * x ≤ Real.exp (d * x) := by
      exact (le_add_of_nonneg_left zero_le_one).trans
        (by
          simpa only [add_comm] using
            Real.add_one_le_exp (d * x))
    have hxle : x ≤ Real.exp (d * x) / d := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hdxle
    have hexp :
        Real.exp (-x * z.im) ≤ Real.exp (c * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hosc :
        x * Real.exp (-x * z.im) ≤
          C * Real.exp (q * x) := by
      calc
        x * Real.exp (-x * z.im) ≤
            x * Real.exp (c * x) := by gcongr
        _ ≤ (Real.exp (d * x) / d) *
            Real.exp (c * x) := by gcongr
        _ = C * Real.exp (q * x) := by
          rw [show Real.exp (d * x) / d * Real.exp (c * x) =
              (1 / d) *
                (Real.exp (d * x) * Real.exp (c * x)) by ring,
            ← Real.exp_add]
          dsimp only [C, q]
          congr 2
          ring
    have hsource0 : 0 ≤ thetaCuspSourceTerm x n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    rw [show ‖F' z x‖ =
        thetaCuspSourceTerm x n *
          (x * Real.exp (-x * z.im)) by
      dsimp only [F']
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hsource0, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hx0, norm_I, mul_one,
        norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma]]
    dsimp only [bound]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hosc hsource0
  have hFint :
      Integrable (F z₀) (volume.restrict (Ioi 0)) := by
    dsimp only [F]
    exact
      integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im
        hn hz₀
  have hdiff : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ ε,
        HasDerivAt (fun z => F z x) (F' z x) z := by
    filter_upwards with x
    intro z _hz
    dsimp only [F, F']
    convert
      (hasDerivAt_spectralTranslationPhase x z).const_mul
        (thetaCuspSourceTerm x n : ℂ) using 1 <;> ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := z₀)
    (s := Metric.ball z₀ ε) (bound := bound)
    (Metric.ball_mem_nhds z₀ hε)
    (Eventually.of_forall hFmeas)
    hFint hF'meas hdom hbound hdiff
  simpa only [thetaCuspShellHalfLineTransform, F, F'] using
    hresult.2

/-- Universal upper incomplete-Gamma tail attached to the completed theta source. -/
def thetaCuspUniversalGammaPhaseTail (z : ℂ) (N : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi N, thetaCuspUniversalGammaPhaseIntegrand z t

/-- Exact shellwise incomplete-Gamma tail, including the Dirichlet shell character. -/
theorem thetaCuspShellPhaseTransform_eq_universalGammaTail
    {z : ℂ} (hz : -1 < z.im) {n : ℕ} (hn : 0 < n) :
    thetaCuspShellHalfLineTransform
        (fun x => spectralTranslationPhase x z) n =
      ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
        spectralTranslationPhase (-Real.log (n : ℝ)) z *
          thetaCuspUniversalGammaPhaseTail z ((n : ℝ) ^ 2) := by
  rw [thetaCuspShellHalfLineTransform_eq_gammaIntegral
    (fun x => spectralTranslationPhase x z)
    (by unfold spectralTranslationPhase; fun_prop)
    hn
    (integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im hn hz)]
  unfold thetaCuspUniversalGammaPhaseTail
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact thetaCuspShellGammaPhaseIntegrand_eq_universal hn
    (lt_trans (by positivity : (0 : ℝ) < (n : ℝ) ^ 2) ht)

/-- Above every positive shell cut, the universal incomplete-Gamma amplitude is strictly positive. -/
theorem thetaCuspUniversalGammaAmplitude_pos
    {t : ℝ} (ht : 1 ≤ t) :
    0 < thetaCuspUniversalGammaAmplitude t := by
  have hlinear : 0 < 2 * Real.pi * t - 3 := by
    nlinarith [Real.pi_gt_three]
  unfold thetaCuspUniversalGammaAmplitude
  positivity

/-- Real-part-uniform norm of the universal Mellin--Gamma kernel. -/
theorem norm_thetaCuspUniversalGammaPhaseIntegrand
    {z : ℂ} {t : ℝ} (ht : 1 ≤ t) :
    ‖thetaCuspUniversalGammaPhaseIntegrand z t‖ =
      thetaCuspUniversalGammaAmplitude t *
        Real.exp (-(Real.log t / 2) * z.im) := by
  unfold thetaCuspUniversalGammaPhaseIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaCuspUniversalGammaAmplitude_pos ht),
    norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma]

/-- Shell prefactor has critical-line weight `exp ((Im z - 1/2) log n)`;
its norm is independent of `Re z`. -/
theorem norm_thetaCuspShellGammaDirichletPrefactor
    {z : ℂ} {n : ℕ} :
    ‖((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
        spectralTranslationPhase (-Real.log (n : ℝ)) z‖ =
      Real.exp ((z.im - 1 / 2) * Real.log (n : ℝ)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),
    norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma,
    ← Real.exp_add]
  congr 1
  ring

/-- Base complex Mellin--Gamma kernel whose logarithmic derivative exposes the complex saddle. -/
def thetaCuspUniversalGammaCore (z : ℂ) (t : ℝ) : ℂ :=
  ((Real.exp (Real.log t / 4) * Real.exp (-Real.pi * t) : ℝ) : ℂ) *
    spectralTranslationPhase (Real.log t / 2) z

theorem thetaCuspUniversalGammaPhaseIntegrand_eq_core
    (z : ℂ) (t : ℝ) :
    thetaCuspUniversalGammaPhaseIntegrand z t =
      (Real.pi * (2 * Real.pi * t - 3) : ℝ) *
        thetaCuspUniversalGammaCore z t := by
  unfold thetaCuspUniversalGammaPhaseIntegrand
    thetaCuspUniversalGammaAmplitude thetaCuspUniversalGammaCore
  push_cast
  ring

/-- Exact modulus of the base Mellin--Gamma kernel on its positive domain. -/
theorem norm_thetaCuspUniversalGammaCore
    {z : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖thetaCuspUniversalGammaCore z t‖ =
      t ^ ((1 / 4 : ℝ) - z.im / 2) * Real.exp (-Real.pi * t) := by
  unfold thetaCuspUniversalGammaCore
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
    norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma,
    Real.rpow_def_of_pos ht]
  calc
    (Real.exp (Real.log t / 4) * Real.exp (-Real.pi * t)) *
          Real.exp (-(Real.log t / 2) * z.im) =
        Real.exp
          (Real.log t / 4 - Real.pi * t -
            (Real.log t / 2) * z.im) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ = Real.exp (Real.log t * ((1 / 4 : ℝ) - z.im / 2)) *
          Real.exp (-Real.pi * t) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Every nonnegative real-power multiple of the base Gamma core is integrable in the Fourier
strip. This is the absolute input for the exact tail recurrence. -/
theorem integrableOn_rpow_mul_thetaCuspUniversalGammaCore
    (j : ℕ) {z : ℂ} (hz : |z.im| < 1) :
    IntegrableOn
      (fun t : ℝ =>
        (((t ^ (j : ℝ) : ℝ) : ℂ) *
          thetaCuspUniversalGammaCore z t))
      (Ioi 0) := by
  let q : ℝ := (j : ℝ) + ((1 / 4 : ℝ) - z.im / 2)
  have hq : -1 < q := by
    have him := (abs_lt.mp hz).2
    dsimp [q]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have hbase :
      IntegrableOn
        (fun t : ℝ => t ^ q * Real.exp (-Real.pi * t))
        (Ioi 0) := by
    simpa only [Real.rpow_one, mul_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := q) hq (by norm_num) Real.pi_pos)
  change Integrable
    (fun t : ℝ =>
      (((t ^ (j : ℝ) : ℝ) : ℂ) *
        thetaCuspUniversalGammaCore z t))
    (volume.restrict (Ioi 0))
  apply Integrable.mono hbase
  · have hcont : ContinuousOn
        (fun t : ℝ =>
          (((t ^ (j : ℝ) : ℝ) : ℂ) *
            thetaCuspUniversalGammaCore z t))
        (Ioi 0) := by
      intro t ht
      have hrpow :
          ContinuousAt (fun u : ℝ => u ^ (j : ℝ)) t :=
        continuousAt_id.rpow_const (Or.inl ht.ne')
      have hcore :
          ContinuousAt (thetaCuspUniversalGammaCore z) t := by
        have hlog : ContinuousAt Real.log t :=
          Real.continuousAt_log ht.ne'
        have hquarter :
            ContinuousAt (fun u : ℝ => Real.exp (Real.log u / 4)) t :=
          Real.continuous_exp.continuousAt.comp (hlog.div_const 4)
        have hdamp :
            ContinuousAt (fun u : ℝ => Real.exp (-Real.pi * u)) t :=
          Real.continuous_exp.continuousAt.comp
            (continuousAt_const.mul continuousAt_id)
        have hampC :
            ContinuousAt
              (fun u : ℝ =>
                ((Real.exp (Real.log u / 4) *
                  Real.exp (-Real.pi * u) : ℝ) : ℂ)) t :=
          Complex.continuous_ofReal.continuousAt.comp (hquarter.mul hdamp)
        have hcoordC :
            ContinuousAt (fun u : ℝ => ((Real.log u / 2 : ℝ) : ℂ)) t :=
          Complex.continuous_ofReal.continuousAt.comp (hlog.div_const 2)
        have hphase :
            ContinuousAt
              (fun u : ℝ =>
                spectralTranslationPhase (Real.log u / 2) z) t := by
          unfold spectralTranslationPhase
          exact Complex.continuous_exp.continuousAt.comp
            ((hcoordC.mul continuousAt_const).mul continuousAt_const)
        exact hampC.mul hphase
      exact ((Complex.continuous_ofReal.continuousAt.comp hrpow).mul hcore).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.le _),
      norm_thetaCuspUniversalGammaCore ht,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
        (Real.exp_pos _).le)]
    dsimp only [q]
    rw [Real.rpow_add ht]
    simp only [mul_assoc, le_refl]

/-- Exact complex-saddle logarithmic derivative of the universal Gamma core. -/
theorem hasDerivAt_thetaCuspUniversalGammaCore
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspUniversalGammaCore z)
      (((((1 / (4 * t) : ℝ) : ℂ) +
          ((1 / (2 * t) : ℝ) : ℂ) * I * z -
          (Real.pi : ℂ)) *
        thetaCuspUniversalGammaCore z t)) t := by
  have hlog : HasDerivAt Real.log (1 / t) t :=
    by simpa only [one_div] using Real.hasDerivAt_log ht.ne'
  have hquarter :
      HasDerivAt (fun u : ℝ => Real.exp (Real.log u / 4))
        (Real.exp (Real.log t / 4) * (1 / t / 4)) t :=
    (Real.hasDerivAt_exp _).comp t (hlog.div_const 4)
  have hdamp :
      HasDerivAt (fun u : ℝ => Real.exp (-Real.pi * u))
        (Real.exp (-Real.pi * t) * (-Real.pi)) t := by
    simpa only [mul_one] using
      (Real.hasDerivAt_exp (-Real.pi * t)).comp t
        ((hasDerivAt_id t).const_mul (-Real.pi))
  have hreal :
      HasDerivAt
        (fun u : ℝ =>
          Real.exp (Real.log u / 4) * Real.exp (-Real.pi * u))
        (Real.exp (Real.log t / 4) * Real.exp (-Real.pi * t) *
          (1 / t / 4 - Real.pi)) t := by
    convert hquarter.mul hdamp using 1
    all_goals ring
  have hcoord : HasDerivAt (fun u : ℝ => Real.log u / 2) (1 / t / 2) t :=
    hlog.div_const 2
  have hphase :
      HasDerivAt
        (fun u : ℝ => spectralTranslationPhase (Real.log u / 2) z)
        ((((1 / t / 2 : ℝ) : ℂ) * I * z) *
          spectralTranslationPhase (Real.log t / 2) z) t := by
    unfold spectralTranslationPhase
    have hcoordC :
        HasDerivAt (fun u : ℝ => ((Real.log u / 2 : ℝ) : ℂ))
          ((1 / t / 2 : ℝ) : ℂ) t :=
      hcoord.ofReal_comp
    have hinner :
        HasDerivAt
          (fun u : ℝ => (((Real.log u / 2 : ℝ) : ℂ) * I) * z)
          (((1 / t / 2 : ℝ) : ℂ) * I * z) t :=
      (hcoordC.mul_const I).mul_const z
    simpa only [Function.comp_apply, mul_comm] using
      (Complex.hasDerivAt_exp _).comp t hinner
  unfold thetaCuspUniversalGammaCore
  convert hreal.ofReal_comp.mul hphase using 1 <;> push_cast <;>
    field_simp [ht.ne'] <;> ring

/-- Pointwise integration-by-parts identity: source polynomial equals a total derivative plus one
base incomplete-Gamma channel. -/
theorem thetaCuspUniversalGammaPhaseIntegrand_eq_derivative_remainder
    (z : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    thetaCuspUniversalGammaPhaseIntegrand z t =
      -2 * Real.pi *
          (((1 : ℂ) +
              ((1 / (4 * t) : ℝ) : ℂ) * (t : ℂ) +
              ((1 / (2 * t) : ℝ) : ℂ) * (t : ℂ) * I * z -
              (Real.pi : ℂ) * (t : ℂ)) *
            thetaCuspUniversalGammaCore z t) +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspUniversalGammaCore z t := by
  rw [thetaCuspUniversalGammaPhaseIntegrand_eq_core z t]
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) ht)
  push_cast
  field_simp [ht0]
  ring

/-- Primitive carrying the total-derivative channel in the Gamma recurrence. -/
def thetaCuspUniversalGammaPrimitive (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * thetaCuspUniversalGammaCore z t

theorem hasDerivAt_thetaCuspUniversalGammaPrimitive
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaCuspUniversalGammaPrimitive z)
      (((1 : ℂ) +
          ((1 / (4 * t) : ℝ) : ℂ) * (t : ℂ) +
          ((1 / (2 * t) : ℝ) : ℂ) * (t : ℂ) * I * z -
          (Real.pi : ℂ) * (t : ℂ)) *
        thetaCuspUniversalGammaCore z t) t := by
  have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  unfold thetaCuspUniversalGammaPrimitive
  convert hid.mul (hasDerivAt_thetaCuspUniversalGammaCore z ht) using 1
  field_simp [ht.ne']
  ring

/-- Exact first recurrence for the universal upper incomplete-Gamma channel. -/
theorem thetaCuspUniversalGammaPhaseIntegrand_eq_primitiveDerivative
    (z : ℂ) {t : ℝ} (ht : 1 ≤ t) :
    thetaCuspUniversalGammaPhaseIntegrand z t =
      -2 * Real.pi * deriv (thetaCuspUniversalGammaPrimitive z) t +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspUniversalGammaCore z t := by
  rw [thetaCuspUniversalGammaPhaseIntegrand_eq_derivative_remainder z ht,
    (hasDerivAt_thetaCuspUniversalGammaPrimitive z
      (lt_of_lt_of_le (by norm_num) ht)).deriv]

/-- Base universal upper incomplete-Gamma tail after removing the source polynomial. -/
def thetaCuspUniversalGammaCoreTail (z : ℂ) (N : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi N, thetaCuspUniversalGammaCore z t

theorem integrableOn_thetaCuspUniversalGammaCore
    {z : ℂ} (hz : |z.im| < 1) :
    IntegrableOn (thetaCuspUniversalGammaCore z) (Ioi 0) := by
  simpa using
    (integrableOn_rpow_mul_thetaCuspUniversalGammaCore 0 hz)

/-- Spectral derivative of the base Mellin--Gamma kernel.  The logarithmic coordinate is the
exact insertion generated by horizontal spectral differentiation. -/
def thetaCuspUniversalGammaCoreSpectralDerivative
    (z : ℂ) (t : ℝ) : ℂ :=
  (((Real.log t / 2 : ℝ) : ℂ) * I) *
    thetaCuspUniversalGammaCore z t

theorem hasDerivAt_thetaCuspUniversalGammaCore_spectral
    (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => thetaCuspUniversalGammaCore w t)
      (thetaCuspUniversalGammaCoreSpectralDerivative z t) z := by
  convert
    (hasDerivAt_spectralTranslationPhase (Real.log t / 2) z).const_mul
      (((Real.exp (Real.log t / 4) *
        Real.exp (-Real.pi * t) : ℝ) : ℂ)) using 1 <;>
    simp [thetaCuspUniversalGammaCoreSpectralDerivative,
      thetaCuspUniversalGammaCore] <;> ring

/-- Spectral derivative tail of the base incomplete-Gamma channel. -/
def thetaCuspUniversalGammaCoreTailSpectralDerivative
    (z : ℂ) (N : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi N,
    thetaCuspUniversalGammaCoreSpectralDerivative z t

/-- Differentiation under the moving-cut Gamma tail.  The cut is fixed during spectral
differentiation; Gaussian decay supplies a neighborhood-uniform majorant throughout the strip. -/
theorem hasDerivAt_thetaCuspUniversalGammaCoreTail
    {z₀ : ℂ} (hz₀ : |z₀.im| < 1) {N : ℝ} (hN : 1 ≤ N) :
    HasDerivAt (fun z => thetaCuspUniversalGammaCoreTail z N)
      (thetaCuspUniversalGammaCoreTailSpectralDerivative z₀ N) z₀ := by
  let ε : ℝ := (1 - |z₀.im|) / 4
  let B : ℝ := |z₀.im| + ε
  let bound : ℝ → ℝ := fun t =>
    t ^ 2 * Real.exp (-Real.pi * t)
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  have hB : B < 1 := by
    dsimp only [B, ε]
    linarith
  have him {z : ℂ} (hz : z ∈ Metric.ball z₀ ε) : |z.im| ≤ B := by
    have hdist : ‖z - z₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have himdiff : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
    calc
      |z.im| = |z₀.im + (z.im - z₀.im)| := by ring_nf
      _ ≤ |z₀.im| + |z.im - z₀.im| := abs_add_le _ _
      _ ≤ |z₀.im| + ε := by linarith
      _ = B := by rfl
  have hbound : Integrable bound (volume.restrict (Ioi N)) := by
    have hbase : IntegrableOn bound (Ioi 0) := by
      dsimp only [bound]
      simpa only [Real.rpow_two, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow
          (p := (1 : ℝ)) (s := (2 : ℝ))
          (by norm_num) (by norm_num) Real.pi_pos)
    exact hbase.mono_set
      (fun t ht => lt_trans (by linarith : 0 < N) ht)
  have hFmeas : ∀ z : ℂ,
      AEStronglyMeasurable (thetaCuspUniversalGammaCore z)
        (volume.restrict (Ioi N)) := by
    intro z
    have hcont :
        ContinuousOn (thetaCuspUniversalGammaCore z) (Ioi N) := by
      intro t ht
      have ht0 : 0 < t := lt_trans (by linarith : 0 < N) ht
      have hlog : ContinuousAt Real.log t :=
        Real.continuousAt_log ht0.ne'
      unfold thetaCuspUniversalGammaCore spectralTranslationPhase
      exact
        ((Complex.continuous_ofReal.continuousAt.comp
          ((Real.continuous_exp.continuousAt.comp
            (hlog.div_const 4)).mul
            (Real.continuous_exp.continuousAt.comp
              (continuousAt_const.mul continuousAt_id)))).mul
          (Complex.continuous_exp.continuousAt.comp
            (((Complex.continuous_ofReal.continuousAt.comp
              (hlog.div_const 2)).mul continuousAt_const).mul
                continuousAt_const))).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hF'meas :
      AEStronglyMeasurable
        (thetaCuspUniversalGammaCoreSpectralDerivative z₀)
        (volume.restrict (Ioi N)) := by
    have hcont :
        ContinuousOn
          (thetaCuspUniversalGammaCoreSpectralDerivative z₀)
          (Ioi N) := by
      intro t ht
      have ht0 : 0 < t := lt_trans (by linarith : 0 < N) ht
      have hlog : ContinuousAt Real.log t :=
        Real.continuousAt_log ht0.ne'
      have hcoord :
          ContinuousAt
            (fun u : ℝ => ((Real.log u / 2 : ℝ) : ℂ)) t :=
        Complex.continuous_ofReal.continuousAt.comp
          (hlog.div_const 2)
      have hcore :
          ContinuousAt (thetaCuspUniversalGammaCore z₀) t := by
        unfold thetaCuspUniversalGammaCore spectralTranslationPhase
        exact
          (Complex.continuous_ofReal.continuousAt.comp
            ((Real.continuous_exp.continuousAt.comp
              (hlog.div_const 4)).mul
              (Real.continuous_exp.continuousAt.comp
                (continuousAt_const.mul continuousAt_id)))).mul
            (Complex.continuous_exp.continuousAt.comp
              ((hcoord.mul continuousAt_const).mul continuousAt_const))
      unfold thetaCuspUniversalGammaCoreSpectralDerivative
      exact
        ((hcoord.mul continuousAt_const).mul hcore).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hdom : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi N)),
      ∀ z ∈ Metric.ball z₀ ε,
        ‖thetaCuspUniversalGammaCoreSpectralDerivative z t‖ ≤
          bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have ht1 : 1 ≤ t := hN.trans (le_of_lt ht)
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    have hzB := him hz
    have hq : (1 / 4 : ℝ) - z.im / 2 ≤ 1 := by
      have hzlower : -B ≤ z.im := (abs_le.mp hzB).1
      linarith
    have hpow :
        t ^ ((1 / 4 : ℝ) - z.im / 2) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1 hq
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlog : Real.log t / 2 ≤ t := by
      have h := Real.log_le_self (zero_le_one.trans ht1)
      linarith
    rw [thetaCuspUniversalGammaCoreSpectralDerivative,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hlog0 (by norm_num)),
      norm_I, mul_one, norm_thetaCuspUniversalGammaCore ht0]
    dsimp only [bound]
    calc
      Real.log t / 2 *
          (t ^ ((1 / 4 : ℝ) - z.im / 2) *
            Real.exp (-Real.pi * t)) ≤
        t * (t * Real.exp (-Real.pi * t)) := by gcongr
      _ = t ^ 2 * Real.exp (-Real.pi * t) := by ring
  have hInt :
      Integrable (thetaCuspUniversalGammaCore z₀)
        (volume.restrict (Ioi N)) :=
    (integrableOn_thetaCuspUniversalGammaCore hz₀).mono_set
      (fun t ht => lt_trans (by linarith : 0 < N) ht)
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => thetaCuspUniversalGammaCore z t)
    (F' := fun z t =>
      thetaCuspUniversalGammaCoreSpectralDerivative z t)
    (x₀ := z₀) (s := Metric.ball z₀ ε) (bound := bound)
    (Metric.ball_mem_nhds z₀ hε)
    (Eventually.of_forall hFmeas)
    hInt hF'meas hdom hbound
    (by
      filter_upwards with t
      intro z _hz
      exact hasDerivAt_thetaCuspUniversalGammaCore_spectral z t)
  simpa only [thetaCuspUniversalGammaCoreTail,
    thetaCuspUniversalGammaCoreTailSpectralDerivative] using hresult.2

theorem integrableOn_exp_neg_two_Ioi {N : ℝ} (hN : 0 ≤ N) :
    IntegrableOn (fun t : ℝ => Real.exp (-(2 * t))) (Ioi N) := by
  have hbase :
      IntegrableOn (fun t : ℝ => Real.exp (-(2 * t))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (b := (2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    apply h.congr
    filter_upwards [] with t
    simp only [Real.rpow_zero, one_mul, Real.rpow_one]
    congr 1
    ring
  exact hbase.mono_set (fun t ht => lt_of_le_of_lt hN ht)

theorem integral_exp_neg_two_Ioi (N : ℝ) :
    (∫ t : ℝ in Ioi N, Real.exp (-(2 * t))) =
      Real.exp (-(2 * N)) / 2 := by
  have hzero :
      (∫ t : ℝ in Ioi 0, Real.exp (-(2 * t))) = 1 / 2 := by
    have h := integral_comp_mul_left_Ioi
      (fun x : ℝ => Real.exp (-x)) 0
      (by norm_num : (0 : ℝ) < 2)
    simp only [mul_zero, smul_eq_mul] at h
    rw [integral_exp_neg_Ioi] at h
    norm_num at h ⊢
    simpa [mul_comm] using h
  have htranslate :=
    integral_Ioi_comp_add_eq_integral_Ioi
      (fun t : ℝ => Real.exp (-(2 * t))) N
  rw [show
      (fun u : ℝ => Real.exp (-(2 * (u + N)))) =
        fun u : ℝ => Real.exp (-(2 * N)) *
          Real.exp (-(2 * u)) by
      funext u
      rw [show -(2 * (u + N)) = -(2 * N) + -(2 * u) by ring,
        Real.exp_add],
    integral_const_mul, hzero] at htranslate
  nlinarith

/-- Real-part-uniform Gaussian tail bound for the base incomplete-Gamma channel. -/
theorem norm_thetaCuspUniversalGammaCoreTail_le
    {z : ℂ} (hz : |z.im| < 1) {N : ℝ} (hN : 1 ≤ N) :
    ‖thetaCuspUniversalGammaCoreTail z N‖ ≤
      Real.exp (-(2 * N)) / 2 := by
  unfold thetaCuspUniversalGammaCoreTail
  have hmajor := integrableOn_exp_neg_two_Ioi
    (show (0 : ℝ) ≤ N by linarith)
  calc
    ‖∫ t : ℝ in Ioi N, thetaCuspUniversalGammaCore z t‖ ≤
        ∫ t : ℝ in Ioi N, Real.exp (-(2 * t)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := hN.trans (le_of_lt ht)
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
      have him := (abs_lt.mp hz).1
      have hpow :
          t ^ ((1 / 4 : ℝ) - z.im / 2) ≤ t := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le ht1
            (by linarith : (1 / 4 : ℝ) - z.im / 2 ≤ 1)
      rw [norm_thetaCuspUniversalGammaCore ht0]
      calc
        t ^ ((1 / 4 : ℝ) - z.im / 2) *
            Real.exp (-Real.pi * t) ≤
          t * Real.exp (-Real.pi * t) := by
            exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ ≤ Real.exp t * Real.exp (-Real.pi * t) := by
          exact mul_le_mul_of_nonneg_right
            ((le_add_of_nonneg_right zero_le_one).trans
              (Real.add_one_le_exp t))
            (Real.exp_pos _).le
        _ = Real.exp (-(Real.pi - 1) * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(2 * t)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_gt_three]
    _ = Real.exp (-(2 * N)) / 2 := integral_exp_neg_two_Ioi N

theorem integrableOn_thetaCuspUniversalGammaPrimitive
    {z : ℂ} (hz : |z.im| < 1) :
    IntegrableOn (thetaCuspUniversalGammaPrimitive z) (Ioi 0) := by
  simpa only [thetaCuspUniversalGammaPrimitive, Nat.cast_one,
    Real.rpow_one] using
      (integrableOn_rpow_mul_thetaCuspUniversalGammaCore 1 hz)

theorem integrableOn_thetaCuspUniversalGammaPhaseIntegrand
    {z : ℂ} (hz : |z.im| < 1) :
    IntegrableOn (thetaCuspUniversalGammaPhaseIntegrand z) (Ioi 0) := by
  have hcore := integrableOn_thetaCuspUniversalGammaCore hz
  have hprimitive := integrableOn_thetaCuspUniversalGammaPrimitive hz
  have hcomb :=
    (hprimitive.const_mul ((2 * Real.pi ^ 2 : ℝ) : ℂ)).sub
      (hcore.const_mul ((3 * Real.pi : ℝ) : ℂ))
  apply hcomb.congr
  filter_upwards [] with t
  simp only [Pi.sub_apply]
  rw [thetaCuspUniversalGammaPhaseIntegrand_eq_core z t]
  unfold thetaCuspUniversalGammaPrimitive
  push_cast
  ring

theorem tendsto_thetaCuspUniversalGammaPrimitive_atTop_zero
    (z : ℂ) :
    Tendsto (thetaCuspUniversalGammaPrimitive z) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let q : ℝ := 1 + ((1 / 4 : ℝ) - z.im / 2)
  have hbase :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q Real.pi Real.pi_pos
  apply hbase.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold thetaCuspUniversalGammaPrimitive
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    norm_thetaCuspUniversalGammaCore ht]
  dsimp only [q]
  norm_num
  rw [Real.rpow_add ht, Real.rpow_one]
  ring

theorem integrableOn_deriv_thetaCuspUniversalGammaPrimitive
    {z : ℂ} (hz : |z.im| < 1) :
    IntegrableOn (fun t : ℝ =>
      deriv (thetaCuspUniversalGammaPrimitive z) t) (Ioi 0) := by
  have hcore := integrableOn_thetaCuspUniversalGammaCore hz
  have hprimitive := integrableOn_thetaCuspUniversalGammaPrimitive hz
  let c : ℂ := 5 / 4 + I * z / 2
  have hcomb :=
    (hcore.const_mul c).sub
      (hprimitive.const_mul (Real.pi : ℂ))
  apply hcomb.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hquarter :
      ((1 / (4 * t) : ℝ) : ℂ) * (t : ℂ) = 1 / 4 := by
    push_cast
    field_simp [ht0.ne']
  have hhalf :
      ((1 / (2 * t) : ℝ) : ℂ) * (t : ℂ) = 1 / 2 := by
    push_cast
    field_simp [ht0.ne']
  simp only [Pi.sub_apply]
  rw [(hasDerivAt_thetaCuspUniversalGammaPrimitive z ht0).deriv]
  dsimp only [c]
  unfold thetaCuspUniversalGammaPrimitive
  rw [hquarter, hhalf]
  ring

/-- Integrated first recurrence. The total derivative contributes only its lower boundary. -/
theorem thetaCuspUniversalGammaPhaseTail_eq_boundary_add_coreTail
    {z : ℂ} (hz : |z.im| < 1) {N : ℝ} (hN : 1 ≤ N) :
    thetaCuspUniversalGammaPhaseTail z N =
      2 * Real.pi * thetaCuspUniversalGammaPrimitive z N +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspUniversalGammaCoreTail z N := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hderivInt :
      IntegrableOn
        (fun t : ℝ => deriv (thetaCuspUniversalGammaPrimitive z) t)
        (Ioi N) :=
    (integrableOn_deriv_thetaCuspUniversalGammaPrimitive hz).mono_set
      (fun t ht => lt_trans hN0 ht)
  have hFTC :
      (∫ t : ℝ in Ioi N,
          deriv (thetaCuspUniversalGammaPrimitive z) t) =
        -thetaCuspUniversalGammaPrimitive z N := by
    have hderiv :
        ∀ t ∈ Ioi N,
          HasDerivAt (thetaCuspUniversalGammaPrimitive z)
            (deriv (thetaCuspUniversalGammaPrimitive z) t) t := by
      intro t ht
      have h :=
        hasDerivAt_thetaCuspUniversalGammaPrimitive z
          (lt_trans hN0 ht)
      rw [h.deriv]
      exact h
    have h := integral_Ioi_of_hasDerivAt_of_tendsto
      (hasDerivAt_thetaCuspUniversalGammaPrimitive z hN0).continuousAt.continuousWithinAt
      hderiv
      hderivInt
      (tendsto_thetaCuspUniversalGammaPrimitive_atTop_zero z)
    simpa only [zero_sub] using h
  unfold thetaCuspUniversalGammaPhaseTail
    thetaCuspUniversalGammaCoreTail
  calc
    (∫ t : ℝ in Ioi N, thetaCuspUniversalGammaPhaseIntegrand z t) =
        ∫ t : ℝ in Ioi N,
          (-2 * Real.pi *
              deriv (thetaCuspUniversalGammaPrimitive z) t +
            Real.pi * (I * z - 1 / 2) *
              thetaCuspUniversalGammaCore z t) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact thetaCuspUniversalGammaPhaseIntegrand_eq_primitiveDerivative
            z (hN.trans (le_of_lt ht))
    _ = -2 * Real.pi *
          (∫ t : ℝ in Ioi N,
            deriv (thetaCuspUniversalGammaPrimitive z) t) +
        Real.pi * (I * z - 1 / 2) *
          (∫ t : ℝ in Ioi N, thetaCuspUniversalGammaCore z t) := by
          rw [integral_add,
            integral_const_mul, integral_const_mul]
          · exact hderivInt.const_mul (-2 * Real.pi)
          · exact
              ((integrableOn_thetaCuspUniversalGammaCore hz).mono_set
                (fun t ht => lt_trans hN0 ht)).const_mul
                (Real.pi * (I * z - 1 / 2))
    _ = 2 * Real.pi * thetaCuspUniversalGammaPrimitive z N +
        Real.pi * (I * z - 1 / 2) *
          (∫ t : ℝ in Ioi N, thetaCuspUniversalGammaCore z t) := by
          rw [hFTC]
          ring

/-- At the moving shell cut, Dirichlet character and Mellin phase cancel exactly. -/
theorem thetaCuspShellGammaPrefactor_mul_primitive_cut
    (z : ℂ) {n : ℕ} (hn : 0 < n) :
    (((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
        spectralTranslationPhase (-Real.log (n : ℝ)) z) *
      thetaCuspUniversalGammaPrimitive z ((n : ℝ) ^ 2) =
        (((n : ℝ) ^ 2 *
          Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogSq :
      Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
    simpa using Real.log_pow (n : ℝ) 2
  have hamp :
      Real.exp (-Real.log (n : ℝ) / 2) *
          Real.exp (Real.log ((n : ℝ) ^ 2) / 4) = 1 := by
    rw [hlogSq, ← Real.exp_add]
    rw [show -Real.log (n : ℝ) / 2 +
        (2 * Real.log (n : ℝ)) / 4 = 0 by ring, Real.exp_zero]
  have hampC :
      ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
          ((Real.exp (Real.log ((n : ℝ) ^ 2) / 4) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, hamp]
    norm_num
  have hphase :
      spectralTranslationPhase (-Real.log (n : ℝ)) z *
          spectralTranslationPhase (Real.log ((n : ℝ) ^ 2) / 2) z = 1 := by
    rw [hlogSq, show (2 : ℝ) * Real.log (n : ℝ) / 2 =
      Real.log (n : ℝ) by ring, ← spectralTranslationPhase_add]
    simp [spectralTranslationPhase]
  unfold thetaCuspUniversalGammaPrimitive thetaCuspUniversalGammaCore
  rw [show
      ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
          spectralTranslationPhase (-Real.log (n : ℝ)) z *
        ((((n : ℝ) ^ 2 : ℝ) : ℂ) *
          (((Real.exp (Real.log ((n : ℝ) ^ 2) / 4) *
            Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ) *
              spectralTranslationPhase (Real.log ((n : ℝ) ^ 2) / 2) z)) =
      ((((n : ℝ) ^ 2 : ℝ) : ℂ) *
        ((Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) : ℂ)) *
          ((((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
            ((Real.exp (Real.log ((n : ℝ) ^ 2) / 4) : ℝ) : ℂ)) *
          (spectralTranslationPhase (-Real.log (n : ℝ)) z *
            spectralTranslationPhase (Real.log ((n : ℝ) ^ 2) / 2) z)) by
        push_cast
        ring,
    hampC, hphase]
  push_cast
  ring

/-- True shell remainder after extracting the universal Gaussian boundary term. -/
def thetaCuspShellGammaCoreRemainder (z : ℂ) (n : ℕ) : ℂ :=
  ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
    spectralTranslationPhase (-Real.log (n : ℝ)) z *
      thetaCuspUniversalGammaCoreTail z ((n : ℝ) ^ 2)

/-- Exact spectral derivative of the shell Gamma remainder.  The two logarithmic insertions
combine into the intrinsic coordinate `log(t / n²) / 2`. -/
def thetaCuspShellGammaCoreRemainderSpectralDerivative
    (z : ℂ) (n : ℕ) : ℂ :=
  (((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
      spectralTranslationPhase (-Real.log (n : ℝ)) z) *
    (thetaCuspUniversalGammaCoreTailSpectralDerivative z
        ((n : ℝ) ^ 2) -
      (((Real.log (n : ℝ) : ℝ) : ℂ) * I) *
        thetaCuspUniversalGammaCoreTail z ((n : ℝ) ^ 2))

theorem hasDerivAt_thetaCuspShellGammaCoreRemainder
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun w => thetaCuspShellGammaCoreRemainder w n)
      (thetaCuspShellGammaCoreRemainderSpectralDerivative z n) z := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    nlinarith
  have hp :=
    (hasDerivAt_spectralTranslationPhase
      (-Real.log (n : ℝ)) z).const_mul
        (((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ))
  have ht :=
    hasDerivAt_thetaCuspUniversalGammaCoreTail hz hn1
  convert hp.mul ht using 1 <;>
    simp [thetaCuspShellGammaCoreRemainder,
      thetaCuspShellGammaCoreRemainderSpectralDerivative] <;> ring

/-- Uniform far-shell bound: all dependence on horizontal frequency disappears from the norm. -/
theorem norm_thetaCuspShellGammaCoreRemainder_le
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    ‖thetaCuspShellGammaCoreRemainder z n‖ ≤
      Real.exp ((z.im - 1 / 2) * Real.log (n : ℝ)) *
        (Real.exp (-(2 * (n : ℝ) ^ 2)) / 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    nlinarith
  unfold thetaCuspShellGammaCoreRemainder
  rw [show
      ((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
          spectralTranslationPhase (-Real.log (n : ℝ)) z *
            thetaCuspUniversalGammaCoreTail z ((n : ℝ) ^ 2) =
        (((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
          spectralTranslationPhase (-Real.log (n : ℝ)) z) *
            thetaCuspUniversalGammaCoreTail z ((n : ℝ) ^ 2) by ring,
    norm_mul, norm_thetaCuspShellGammaDirichletPrefactor]
  exact mul_le_mul_of_nonneg_left
    (norm_thetaCuspUniversalGammaCoreTail_le hz hn1)
    (Real.exp_pos _).le

/-- Exact shell recurrence: spectral dependence is confined to one base incomplete-Gamma
remainder; the extracted boundary is real and independent of `z`. -/
theorem thetaCuspShellPhaseTransform_eq_boundary_add_coreRemainder
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    thetaCuspShellHalfLineTransform
        (fun x => spectralTranslationPhase x z) n =
      (2 * Real.pi * (n : ℝ) ^ 2 *
          Real.exp (-Real.pi * (n : ℝ) ^ 2) : ℝ) +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspShellGammaCoreRemainder z n := by
  rw [thetaCuspShellPhaseTransform_eq_universalGammaTail
    (by exact (abs_lt.mp hz).1) hn,
    thetaCuspUniversalGammaPhaseTail_eq_boundary_add_coreTail hz
      (show (1 : ℝ) ≤ (n : ℝ) ^ 2 by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
        nlinarith)]
  unfold thetaCuspShellGammaCoreRemainder
  rw [show
      (((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
          spectralTranslationPhase (-Real.log (n : ℝ)) z) *
        (2 * Real.pi * thetaCuspUniversalGammaPrimitive z ((n : ℝ) ^ 2) +
          Real.pi * (I * z - 1 / 2) *
            thetaCuspUniversalGammaCoreTail z ((n : ℝ) ^ 2)) =
      2 * Real.pi *
          ((((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
            spectralTranslationPhase (-Real.log (n : ℝ)) z) *
              thetaCuspUniversalGammaPrimitive z ((n : ℝ) ^ 2)) +
        Real.pi * (I * z - 1 / 2) *
          ((((Real.exp (-Real.log (n : ℝ) / 2) : ℝ) : ℂ) *
            spectralTranslationPhase (-Real.log (n : ℝ)) z) *
              thetaCuspUniversalGammaCoreTail z ((n : ℝ) ^ 2)) by ring,
    thetaCuspShellGammaPrefactor_mul_primitive_cut z hn]
  push_cast
  ring

/-- Real Gaussian boundary extracted from one positive spectral branch. -/
def thetaCuspShellGammaBoundary (n : ℕ) : ℝ :=
  2 * Real.pi * (n : ℝ) ^ 2 *
    Real.exp (-Real.pi * (n : ℝ) ^ 2)

theorem thetaCuspShellGammaBoundary_pos
    {n : ℕ} (hn : 0 < n) :
    0 < thetaCuspShellGammaBoundary n := by
  unfold thetaCuspShellGammaBoundary
  positivity

theorem thetaCuspShellPhaseTransform_eq_gammaBoundary_add
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    thetaCuspShellHalfLineTransform
        (fun x => spectralTranslationPhase x z) n =
      thetaCuspShellGammaBoundary n +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspShellGammaCoreRemainder z n := by
  simpa only [thetaCuspShellGammaBoundary] using
    thetaCuspShellPhaseTransform_eq_boundary_add_coreRemainder hz hn

/-- Positive Ward half-density transform behind the base Gamma remainder. -/
def thetaCuspShellWardPhaseTransform (z : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspWardGibbsAtom n x : ℂ) *
      spectralTranslationPhase x z

/-- Literal first spectral moment of the positive Ward half-density. -/
def thetaCuspShellWardPhaseTransformSpectralDerivative
    (z : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspWardGibbsAtom n x : ℂ) *
      (((x : ℂ) * I) * spectralTranslationPhase x z)

/-- The Ward transform is holomorphic in the lower open half-strip, with derivative given by
its literal first spectral moment. -/
theorem hasDerivAt_thetaCuspShellWardPhaseTransform
    {z₀ : ℂ} (hz₀ : -1 < z₀.im) {n : ℕ} (hn : 0 < n) :
    HasDerivAt
      (fun z => thetaCuspShellWardPhaseTransform z n)
      (thetaCuspShellWardPhaseTransformSpectralDerivative z₀ n) z₀ := by
  let ε : ℝ := (1 + z₀.im) / 4
  let L : ℝ := z₀.im - ε
  let c : ℝ := -L
  let d : ℝ := (1 - c) / 2
  let q : ℝ := c + d
  let C : ℝ := 1 / d
  let bound : ℝ → ℝ := fun x =>
    C * (Real.exp (q * x) * thetaCuspWardGibbsAtom n x)
  let F : ℂ → ℝ → ℂ := fun z x =>
    (thetaCuspWardGibbsAtom n x : ℂ) *
      spectralTranslationPhase x z
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (thetaCuspWardGibbsAtom n x : ℂ) *
      (((x : ℂ) * I) * spectralTranslationPhase x z)
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  have hL : -1 < L := by
    dsimp only [L, ε]
    linarith
  have hc : c < 1 := by
    dsimp only [c]
    linarith
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hq : q < 1 := by
    dsimp only [q, d]
    linarith
  have him {z : ℂ} (hz : z ∈ Metric.ball z₀ ε) :
      L < z.im := by
    have hdist : ‖z - z₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have himdiff : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
    have hlower : -‖z - z₀‖ ≤ z.im - z₀.im :=
      (abs_le.mp himdiff).1
    dsimp only [L]
    linarith
  have hbound :
      Integrable bound (volume.restrict (Ioi 0)) := by
    dsimp only [bound]
    simpa only [thetaCuspWardGibbsAtom] using
      (integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
        (X ^ 2) hn hq).const_mul C
  have hFmeas : ∀ z : ℂ,
      AEStronglyMeasurable (F z)
        (volume.restrict (Ioi 0)) := by
    intro z
    have hW : Continuous (thetaCuspWardGibbsAtom n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspWardGibbsAtom n x).continuousAt
    dsimp only [F]
    exact ((Complex.continuous_ofReal.comp hW).mul
      (by
        unfold spectralTranslationPhase
        fun_prop)).aestronglyMeasurable.restrict
  have hF'meas :
      AEStronglyMeasurable (F' z₀)
        (volume.restrict (Ioi 0)) := by
    have hW : Continuous (thetaCuspWardGibbsAtom n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspWardGibbsAtom n x).continuousAt
    dsimp only [F']
    exact ((Complex.continuous_ofReal.comp hW).mul
      (((Complex.continuous_ofReal.comp continuous_id).mul
        continuous_const).mul
        (by
          unfold spectralTranslationPhase
          fun_prop))).aestronglyMeasurable.restrict
  have hdom : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro z hz
    have hx0 : 0 ≤ x := hx.le
    have hzL := him hz
    have hrate : -z.im ≤ c := by
      dsimp only [c]
      linarith
    have hdx0 : 0 ≤ d * x := mul_nonneg hd.le hx0
    have hdxle : d * x ≤ Real.exp (d * x) := by
      exact (le_add_of_nonneg_left zero_le_one).trans
        (by
          simpa only [add_comm] using
            Real.add_one_le_exp (d * x))
    have hxle : x ≤ Real.exp (d * x) / d := by
      apply (le_div_iff₀ hd).2
      simpa only [mul_comm] using hdxle
    have hexp :
        Real.exp (-x * z.im) ≤ Real.exp (c * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hosc :
        x * Real.exp (-x * z.im) ≤
          C * Real.exp (q * x) := by
      calc
        x * Real.exp (-x * z.im) ≤
            x * Real.exp (c * x) := by gcongr
        _ ≤ (Real.exp (d * x) / d) *
            Real.exp (c * x) := by gcongr
        _ = C * Real.exp (q * x) := by
          rw [show Real.exp (d * x) / d * Real.exp (c * x) =
              (1 / d) *
                (Real.exp (d * x) * Real.exp (c * x)) by ring,
            ← Real.exp_add]
          dsimp only [C, q]
          congr 2
          ring
    have hW0 : 0 ≤ thetaCuspWardGibbsAtom n x := by
      rw [thetaCuspWardGibbsAtom_apply]
      positivity
    rw [show ‖F' z x‖ =
        thetaCuspWardGibbsAtom n x *
          (x * Real.exp (-x * z.im)) by
      dsimp only [F']
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hW0, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hx0, norm_I, mul_one,
        norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma]]
    dsimp only [bound]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hosc hW0
  have hFint :
      Integrable (F z₀) (volume.restrict (Ioi 0)) := by
    dsimp only [F]
    simpa only [thetaCuspWardGibbsAtom] using
      integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
        (X ^ 2) hn hz₀
  have hdiff : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z ∈ Metric.ball z₀ ε,
        HasDerivAt (fun z => F z x) (F' z x) z := by
    filter_upwards with x
    intro z _hz
    dsimp only [F, F']
    convert
      (hasDerivAt_spectralTranslationPhase x z).const_mul
        (thetaCuspWardGibbsAtom n x : ℂ) using 1 <;> ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := z₀)
    (s := Metric.ball z₀ ε) (bound := bound)
    (Metric.ball_mem_nhds z₀ hε)
    (Eventually.of_forall hFmeas)
    hFint hF'meas hdom hbound hdiff
  simpa only [thetaCuspShellWardPhaseTransform,
    thetaCuspShellWardPhaseTransformSpectralDerivative, F, F'] using
    hresult.2

theorem tendsto_thetaCuspWardGibbsAtom_mul_phase_atTop_zero
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : -1 < z.im) :
    Tendsto (fun x : ℝ =>
      spectralTranslationPhase x z *
        (thetaCuspWardGibbsAtom n x : ℂ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase :=
    (exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
      (X ^ 2) hn (z := -z.im) (by linarith)).norm
  have hbase' : Tendsto
      (fun x : ℝ =>
        ‖Real.exp (-z.im * x) *
          thetaCuspPolynomialAtom (X ^ 2) n x‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero] using hbase
  apply hbase'.congr'
  filter_upwards with x
  unfold thetaCuspWardGibbsAtom
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma,
    abs_of_pos (Real.exp_pos _)]
  congr 2
  ring

/-- Ward integration by parts gives a second exact recurrence for the same positive shell branch.
Unlike the Gamma recurrence, its remainder is visibly the phase transform of a positive density. -/
theorem thetaCuspShellPhaseTransform_eq_gammaBoundary_add_ward
    {z : ℂ} (hz : -1 < z.im) {n : ℕ} (hn : 0 < n) :
    thetaCuspShellHalfLineTransform
        (fun x => spectralTranslationPhase x z) n =
      thetaCuspShellGammaBoundary n +
        2 * Real.pi * (I * z - 1 / 2) *
          thetaCuspShellWardPhaseTransform z n := by
  let u : ℝ → ℂ := fun x => spectralTranslationPhase x z
  let u' : ℝ → ℂ := fun x =>
    I * z * spectralTranslationPhase x z
  let v : ℝ → ℂ := fun x =>
    (thetaCuspWardGibbsAtom n x : ℂ)
  let v' : ℝ → ℂ := fun x =>
    (thetaCuspPolynomialAtom
      (thetaCuspLogDerivativeStep (X ^ 2)) n x : ℂ)
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u'] using
      hasDerivAt_spectralTranslationPhase_source z x
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    simpa only [v, v', thetaCuspWardGibbsAtom] using
      (hasDerivAt_thetaCuspPolynomialAtom (X ^ 2) n x).ofReal_comp
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    have h :=
      integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
        (thetaCuspLogDerivativeStep (X ^ 2)) hn hz
    apply h.congr
    filter_upwards with x
    dsimp only [u, v', Pi.mul_apply]
    ring
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have h :=
      (integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
        (X ^ 2) hn hz).const_mul (I * z)
    apply h.congr
    filter_upwards with x
    dsimp only [u', v, Pi.mul_apply, thetaCuspWardGibbsAtom]
    ring
  have hzero :
      Tendsto (u * v) (𝓝[>] 0)
        (𝓝 (thetaCuspWardGibbsAtom n 0 : ℂ)) := by
    have hcont : Continuous (u * v) := by
      have hW : Continuous (thetaCuspWardGibbsAtom n) :=
        continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_thetaCuspWardGibbsAtom n x).continuousAt
      dsimp only [u, v]
      have hphase :
          Continuous (fun x : ℝ =>
            spectralTranslationPhase x z) := by
        unfold spectralTranslationPhase
        fun_prop
      exact hphase.mul (Complex.continuous_ofReal.comp hW)
    simpa [u, v, spectralTranslationPhase] using
      (hcont.continuousAt :
        Tendsto (u * v) (𝓝 (0 : ℝ))
          (𝓝 ((u * v) 0))).mono_left inf_le_left
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    simpa only [u, v, Pi.mul_apply, mul_comm] using
      tendsto_thetaCuspWardGibbsAtom_mul_phase_atTop_zero hn hz
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u')
    (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x)
    huv' hu'v hzero hinfty
  have hderiv :
      (∫ x : ℝ in Ioi 0,
        spectralTranslationPhase x z *
          (thetaCuspPolynomialAtom
            (thetaCuspLogDerivativeStep (X ^ 2)) n x : ℂ)) =
      -(thetaCuspWardGibbsAtom n 0 : ℂ) -
        I * z * thetaCuspShellWardPhaseTransform z n := by
    dsimp only [u, u', v, v', Pi.mul_apply] at hibp
    rw [show
      (fun x : ℝ =>
        I * z * spectralTranslationPhase x z *
          (thetaCuspWardGibbsAtom n x : ℂ)) =
      fun x =>
        I * z *
          ((thetaCuspWardGibbsAtom n x : ℂ) *
            spectralTranslationPhase x z) by
        funext x
        ring,
      integral_const_mul] at hibp
    simpa only [thetaCuspShellWardPhaseTransform, zero_sub] using hibp
  unfold thetaCuspShellHalfLineTransform
  rw [show
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          spectralTranslationPhase x z) =
      fun x =>
        -2 * Real.pi *
          (spectralTranslationPhase x z *
            (thetaCuspPolynomialAtom
              (thetaCuspLogDerivativeStep (X ^ 2)) n x : ℂ) +
            (1 / 2 : ℂ) *
              ((thetaCuspWardGibbsAtom n x : ℂ) *
                spectralTranslationPhase x z)) by
        funext x
        rw [thetaCuspSourceTerm_eq_wardGibbs,
          (hasDerivAt_thetaCuspWardGibbsAtom n x).deriv]
        push_cast
        ring,
    integral_const_mul]
  have hWint :=
    integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
      (X ^ 2) hn hz
  have hfirst : IntegrableOn
      (fun x : ℝ =>
        spectralTranslationPhase x z *
          (thetaCuspPolynomialAtom
            (thetaCuspLogDerivativeStep (X ^ 2)) n x : ℂ))
      (Ioi 0) := by
    simpa only [u, v', Pi.mul_apply] using huv'
  have hsecond : IntegrableOn
      (fun x : ℝ =>
        (thetaCuspWardGibbsAtom n x : ℂ) *
          spectralTranslationPhase x z)
      (Ioi 0) := by
    simpa only [thetaCuspWardGibbsAtom] using hWint
  rw [integral_add hfirst
    (hsecond.const_mul (1 / 2 : ℂ)), integral_const_mul, hderiv]
  rw [show
    (∫ a : ℝ in Ioi 0,
      (thetaCuspWardGibbsAtom n a : ℂ) *
        spectralTranslationPhase a z) =
      thetaCuspShellWardPhaseTransform z n by rfl]
  rw [thetaCuspShellGammaBoundary, thetaCuspWardGibbsAtom_zero]
  push_cast
  ring

/-- Away from the single algebraic coefficient zero, the Gamma remainder is exactly twice the
positive Ward half-density transform. -/
theorem thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
    {z : ℂ} (hz : |z.im| < 1)
    (hcoeff : I * z - 1 / 2 ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    thetaCuspShellGammaCoreRemainder z n =
      2 * thetaCuspShellWardPhaseTransform z n := by
  have hgamma :=
    thetaCuspShellPhaseTransform_eq_gammaBoundary_add
      hz hn
  have hward :=
    thetaCuspShellPhaseTransform_eq_gammaBoundary_add_ward
      (abs_lt.mp hz).1 hn
  rw [hgamma] at hward
  have hmul :
      (Real.pi : ℂ) * (I * z - 1 / 2) *
          thetaCuspShellGammaCoreRemainder z n =
        (Real.pi : ℂ) * (I * z - 1 / 2) *
          (2 * thetaCuspShellWardPhaseTransform z n) := by
    linear_combination hward
  exact mul_left_cancel₀
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      hcoeff) hmul

/-- The intrinsic Gamma-remainder derivative is twice the literal first Ward moment.  This removes
the last representation-level ambiguity from directional derivative questions. -/
theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_eq_two_mul_ward
    {z : ℂ} (hz : |z.im| < 1)
    (hcoeff : I * z - 1 / 2 ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    thetaCuspShellGammaCoreRemainderSpectralDerivative z n =
      2 * thetaCuspShellWardPhaseTransformSpectralDerivative z n := by
  let U : Set ℂ :=
    {w | |w.im| < 1 ∧ I * w - 1 / 2 ≠ 0}
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact
      (isOpen_lt Complex.continuous_im.abs continuous_const).inter
        (isOpen_ne.preimage (by fun_prop))
  have hzU : z ∈ U := ⟨hz, hcoeff⟩
  have heq :
      (fun w => thetaCuspShellGammaCoreRemainder w n) =ᶠ[𝓝 z]
        (fun w => 2 * thetaCuspShellWardPhaseTransform w n) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
      hw.1 hw.2 hn
  have hleft :=
    hasDerivAt_thetaCuspShellGammaCoreRemainder hz hn
  have hright :=
    (hasDerivAt_thetaCuspShellWardPhaseTransform
      (abs_lt.mp hz).1 hn).const_mul (2 : ℂ)
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

/-- Positive real density obtained by absorbing a lower-half-plane aperture into the Ward atom. -/
def thetaCuspTiltedWardDensity
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (a * x) * thetaCuspWardGibbsAtom n x

/-- Logarithmic slope of `thetaCuspTiltedWardDensity`. -/
def thetaCuspTiltedWardScore
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a + 5 / 2 -
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)

theorem thetaCuspWardGibbsAtom_step_eq_score
    (n : ℕ) (x : ℝ) :
    thetaCuspPolynomialAtom
        (thetaCuspLogDerivativeStep (X ^ 2)) n x =
      ((5 / 2 : ℝ) -
        2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) *
          thetaCuspWardGibbsAtom n x := by
  have h :=
    (hasDerivAt_thetaCuspWardGibbsAtom n x).deriv
  rw [deriv_thetaCuspWardGibbsAtom_eq_score] at h
  exact h.symm

theorem hasDerivAt_thetaCuspTiltedWardDensity
    (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspTiltedWardDensity a n)
      (thetaCuspTiltedWardScore a n x *
        thetaCuspTiltedWardDensity a n x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    ring
  have hW := hasDerivAt_thetaCuspWardGibbsAtom n x
  convert he.mul hW using 1
  rw [thetaCuspWardGibbsAtom_step_eq_score]
  simp only [thetaCuspTiltedWardDensity,
    thetaCuspTiltedWardScore]
  ring

/-- Exact normalized second derivative of the tilted Ward density. -/
def thetaCuspTiltedWardCurvature
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspTiltedWardScore a n x ^ 2 -
    4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)

theorem hasDerivAt_thetaCuspTiltedWardDensityDerivative
    (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y =>
        thetaCuspTiltedWardScore a n y *
          thetaCuspTiltedWardDensity a n y)
      (thetaCuspTiltedWardCurvature a n x *
        thetaCuspTiltedWardDensity a n x) x := by
  have hscore : HasDerivAt
      (thetaCuspTiltedWardScore a n)
      (-4 * Real.pi * (n : ℝ) ^ 2 *
        Real.exp (2 * x)) x := by
    unfold thetaCuspTiltedWardScore
    have hraw :=
      (Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
      |>.const_mul
        (-2 * Real.pi * (n : ℝ) ^ 2)
      |>.const_add (a + 5 / 2)
    have hraw' : HasDerivAt
        (fun y =>
          a + 5 / 2 +
            (-2 * Real.pi * (n : ℝ) ^ 2) *
              Real.exp (2 * y))
        ((-2 * Real.pi * (n : ℝ) ^ 2) *
          (Real.exp (2 * x) * (2 * 1))) x := by
      simpa only [Function.comp_apply] using hraw
    convert hraw' using 1 <;> ring
  have hdensity :=
    hasDerivAt_thetaCuspTiltedWardDensity a n x
  convert hscore.mul hdensity using 1
  unfold thetaCuspTiltedWardCurvature
  ring

/-- Exact normalized third derivative of the tilted Ward density. -/
def thetaCuspTiltedWardThirdDerivativeCoefficient
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspTiltedWardScore a n x ^ 3 -
    12 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) *
      thetaCuspTiltedWardScore a n x -
    8 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)

theorem hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative
    (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y =>
        thetaCuspTiltedWardCurvature a n y *
          thetaCuspTiltedWardDensity a n y)
      (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x) x := by
  have hscore : HasDerivAt
      (thetaCuspTiltedWardScore a n)
      (-4 * Real.pi * (n : ℝ) ^ 2 *
        Real.exp (2 * x)) x := by
    unfold thetaCuspTiltedWardScore
    have hraw :=
      ((Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
      |>.const_mul
        (-2 * Real.pi * (n : ℝ) ^ 2)
      |>.const_add (a + 5 / 2))
    have hraw' : HasDerivAt
        (fun y =>
          a + 5 / 2 +
            (-2 * Real.pi * (n : ℝ) ^ 2) *
              Real.exp (2 * y))
        ((-2 * Real.pi * (n : ℝ) ^ 2) *
          (Real.exp (2 * x) * (2 * 1))) x := by
      simpa only [Function.comp_apply] using hraw
    convert hraw' using 1 <;> ring
  have htail : HasDerivAt
      (fun y : ℝ =>
        4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * y))
      (8 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) x := by
    have hraw :=
      ((Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
      |>.const_mul
        (4 * Real.pi * (n : ℝ) ^ 2))
    have hraw' : HasDerivAt
        (fun y =>
          (4 * Real.pi * (n : ℝ) ^ 2) *
            Real.exp (2 * y))
        ((4 * Real.pi * (n : ℝ) ^ 2) *
          (Real.exp (2 * x) * (2 * 1))) x := by
      simpa only [Function.comp_apply] using hraw
    convert hraw' using 1 <;> ring
  have hcurvature : HasDerivAt
      (thetaCuspTiltedWardCurvature a n)
      (-8 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) *
          thetaCuspTiltedWardScore a n x -
        8 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) x := by
    unfold thetaCuspTiltedWardCurvature
    convert (hscore.pow 2).sub htail using 1 <;> ring
  have hdensity :=
    hasDerivAt_thetaCuspTiltedWardDensity a n x
  convert hcurvature.mul hdensity using 1
  unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    thetaCuspTiltedWardCurvature
  ring

/-- **Higher-shell third-order alternation.** Throughout the critical aperture the third
derivative coefficient of every shell `n ≥ 2` is strictly negative. -/
theorem thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_two_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x < 0 := by
  let q : ℝ :=
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  let r : ℝ := q - c
  have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hexp : 1 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hq24 : 24 < q := by
    dsimp only [q]
    have hprod :
        (4 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) := by
      calc
        (4 : ℝ) = 4 * 1 := by ring
        _ ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) :=
          mul_le_mul hn4 hexp (by norm_num) (by positivity)
    nlinarith [Real.pi_gt_three]
  have hc3 : c < 3 := by
    dsimp only [c]
    linarith
  have hr21 : 21 < r := by
    dsimp only [r]
    linarith
  have hqr : q < r + 3 := by
    dsimp only [r]
    linarith
  have hr0 : 0 < r := by linarith
  have hrp15 : 0 < r + 15 := by linarith
  have hproduct : 0 < (r - 21) * (r + 15) :=
    mul_pos (by linarith) hrp15
  have hquadratic : 0 < r ^ 2 - 6 * r - 18 := by
    nlinarith
  have hcubic : 6 * r ^ 2 + 18 * r < r ^ 3 := by
    nlinarith [mul_pos hr0 hquadratic]
  have hqrMul : q * r < (r + 3) * r :=
    mul_lt_mul_of_pos_right hqr hr0
  have hqscale : 6 * q * r < 6 * (r + 3) * r := by
    nlinarith
  have hmain : 0 < r ^ 3 - 6 * q * r + 4 * q := by
    have hq0 : 0 < q := by linarith
    nlinarith
  unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    thetaCuspTiltedWardScore
  dsimp only [q, c, r] at hmain
  nlinarith

/-- The ground-shell third-derivative defect is compact: after `x = 1/2`, every positive shell
has the same strict third-order alternation as the higher shells. -/
theorem thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_pos_of_half_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x < 0 := by
  let q : ℝ :=
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  let r : ℝ := q - c
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnR : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    nlinarith
  have htwoX : 1 ≤ 2 * x := by linarith
  have hexpOne : Real.exp 1 ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr htwoX
  have hexpTwo : 2 < Real.exp (2 * x) :=
    Real.exp_one_gt_two.trans_le hexpOne
  have hprod : 2 < (n : ℝ) ^ 2 * Real.exp (2 * x) := by
    nlinarith [Real.exp_pos (2 * x)]
  have hq12 : 12 < q := by
    dsimp only [q]
    nlinarith [Real.pi_gt_three]
  have hc3 : c < 3 := by
    dsimp only [c]
    linarith
  have hr9 : 9 < r := by
    dsimp only [r]
    linarith
  have hqr : q < r + 3 := by
    dsimp only [r]
    linarith
  have hr0 : 0 < r := by linarith
  have hquad : 0 < r ^ 2 - 6 * r - 18 := by
    nlinarith
  have hcubic : 6 * r ^ 2 + 18 * r < r ^ 3 := by
    nlinarith [mul_pos hr0 hquad]
  have hqrMul : q * r < (r + 3) * r :=
    mul_lt_mul_of_pos_right hqr hr0
  have hq0 : 0 < q := by linarith
  have hmain : 0 < r ^ 3 - 6 * q * r + 4 * q := by
    nlinarith
  unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    thetaCuspTiltedWardScore
  dsimp only [q, c, r] at hmain
  nlinarith

/-- Ground-shell third-order coefficient starts strictly positive at the cusp boundary. -/
theorem thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < thetaCuspTiltedWardThirdDerivativeCoefficient a 1 0 := by
  let q : ℝ := 2 * Real.pi
  let c : ℝ := a + 5 / 2
  let r : ℝ := q - c
  have hq6 : 6 < q := by
    dsimp only [q]
    nlinarith [Real.pi_gt_three]
  have hqUpper : q < 63 / 10 := by
    dsimp only [q]
    nlinarith [Real.pi_lt_d2]
  have hcLower : 5 / 2 < c := by
    dsimp only [c]
    linarith
  have hcUpper : c < 3 := by
    dsimp only [c]
    linarith
  have hr3 : 3 < r := by
    dsimp only [r]
    linarith
  have hrUpper : r < 19 / 5 := by
    dsimp only [r]
    linarith
  have hr0 : 0 ≤ r := hr3.le.trans' (by norm_num)
  have hcube : r ^ 3 < (19 / 5 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hrUpper hr0 (by norm_num)
  have hqr : 18 < q * r := by
    calc
      (18 : ℝ) = 6 * 3 := by norm_num
      _ < q * 3 := mul_lt_mul_of_pos_right hq6 (by norm_num)
      _ < q * r := mul_lt_mul_of_pos_left hr3 (by linarith)
  have hmain : r ^ 3 - 6 * q * r + 4 * q < 0 := by
    nlinarith [hcube, hqr, hqUpper]
  unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    thetaCuspTiltedWardScore
  dsimp only [q, c, r] at hmain
  norm_num
  nlinarith

/-- Before the ground third-order score reaches `5`, its coefficient remains strictly positive. -/
theorem thetaCuspTiltedWardThirdDerivativeCoefficient_ground_pos_of_score_le_five
    {a x : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 0 ≤ x)
    (hscore :
      2 * Real.pi * Real.exp (2 * x) - (a + 5 / 2) ≤ 5) :
    0 < thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x := by
  let q : ℝ := 2 * Real.pi * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  let r : ℝ := q - c
  have hexp : 1 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hq6 : 6 < q := by
    dsimp only [q]
    have hprod : 1 ≤ Real.exp (2 * x) := hexp
    nlinarith [Real.pi_gt_three, Real.exp_pos (2 * x)]
  have hcLower : 5 / 2 < c := by
    dsimp only [c]
    linarith
  have hcUpper : c < 3 := by
    dsimp only [c]
    linarith
  have hr3 : 3 < r := by
    dsimp only [r]
    linarith
  have hr5 : r ≤ 5 := by
    dsimp only [r, q, c]
    exact hscore
  have haux : 0 < -r ^ 2 + 3 * r + 20 := by
    have hfactor : 0 ≤ (5 - r) * (r + 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hfirst : 0 ≤
      (r - 3) * (-r ^ 2 + 3 * r + 20) :=
    mul_nonneg (by linarith) haux.le
  have hsecond : 0 <
      (c - 5 / 2) * (6 * r - 4) :=
    mul_pos (by linarith) (by linarith)
  have hmain :
      0 < -r ^ 3 + 6 * (r + c) * r - 4 * (r + c) := by
    have hid :
        -r ^ 3 + 6 * (r + c) * r - 4 * (r + c) =
          50 +
            (r - 3) * (-r ^ 2 + 3 * r + 20) +
            (c - 5 / 2) * (6 * r - 4) := by ring
    rw [hid]
    positivity
  unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    thetaCuspTiltedWardScore
  dsimp only [q, c, r] at hmain
  norm_num
  nlinarith

/-- Once the ground third-order score has reached `5`, its coefficient is strictly decreasing. -/
theorem thetaCuspTiltedWardThirdDerivativeCoefficient_ground_strictAnti_of_five_le_score
    {a x y : ℝ} (ha : a < 1 / 2)
    (hxy : x < y)
    (hxScore :
      5 ≤ 2 * Real.pi * Real.exp (2 * x) - (a + 5 / 2)) :
    thetaCuspTiltedWardThirdDerivativeCoefficient a 1 y <
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x := by
  let c : ℝ := a + 5 / 2
  let qx : ℝ := 2 * Real.pi * Real.exp (2 * x)
  let qy : ℝ := 2 * Real.pi * Real.exp (2 * y)
  let rx : ℝ := qx - c
  let ry : ℝ := qy - c
  have hc : c < 3 := by
    dsimp only [c]
    linarith
  have hq : qx < qy := by
    dsimp only [qx, qy]
    exact mul_lt_mul_of_pos_left
      (Real.exp_lt_exp.mpr (by linarith)) (by positivity)
  have hr : rx < ry := by
    dsimp only [rx, ry]
    linarith
  have hrx : 5 ≤ rx := by
    dsimp only [rx, qx, c]
    exact hxScore
  let ux : ℝ := rx - 5
  let uy : ℝ := ry - 5
  have hux : 0 ≤ ux := by
    dsimp only [ux]
    linarith
  have huy : 0 ≤ uy := by
    dsimp only [uy]
    linarith
  let D : ℝ :=
    ry ^ 2 + rx * ry + rx ^ 2 -
      6 * (rx + ry) - (6 * c - 4)
  have hD : 0 < D := by
    have hid :
        D =
          19 - 6 * c +
            9 * ux + 9 * uy +
              ux ^ 2 + ux * uy + uy ^ 2 := by
      dsimp only [D, ux, uy]
      ring
    rw [hid]
    have hbase : 0 < 19 - 6 * c := by linarith
    positivity
  have hdiff :
      (-ry ^ 3 + 6 * (ry + c) * ry - 4 * (ry + c)) -
          (-rx ^ 3 + 6 * (rx + c) * rx - 4 * (rx + c)) =
        -(ry - rx) * D := by
    dsimp only [D]
    ring
  have hneg : -(ry - rx) * D < 0 := by
    exact mul_neg_of_neg_of_pos (by linarith) hD
  have hpoly :
      -ry ^ 3 + 6 * (ry + c) * ry - 4 * (ry + c) <
        -rx ^ 3 + 6 * (rx + c) * rx - 4 * (rx + c) := by
    nlinarith [hdiff, hneg]
  unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    thetaCuspTiltedWardScore
  dsimp only [c, qx, qy, rx, ry] at hpoly
  norm_num
  nlinarith

/-- The exceptional ground shell has a genuine third-order sign transition inside `(0,1/2)`. -/
theorem exists_thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ x : ℝ, x ∈ Ioo 0 (1 / 2) ∧
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x = 0 := by
  let F : ℝ → ℝ :=
    thetaCuspTiltedWardThirdDerivativeCoefficient a 1
  have hcont : ContinuousOn F (Icc 0 (1 / 2)) := by
    have hF : Continuous F := by
      dsimp only [F]
      unfold thetaCuspTiltedWardThirdDerivativeCoefficient
        thetaCuspTiltedWardScore
      fun_prop
    exact hF.continuousOn
  have hleft : 0 < F 0 := by
    simpa only [F] using
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero_pos
        ha0 ha
  have hright : F (1 / 2) < 0 := by
    dsimp only [F]
    exact
      thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_pos_of_half_le
        ha (by norm_num) (by norm_num)
  obtain ⟨x, hx, hzero⟩ :=
    intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hcont ⟨hright, hleft⟩
  exact ⟨x, hx, hzero⟩

/-- The ground third-order coefficient has exactly one zero in `(0,1/2)`. -/
theorem existsUnique_thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃! x : ℝ, x ∈ Ioo 0 (1 / 2) ∧
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x = 0 := by
  rcases
      exists_thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero
        ha0 ha with ⟨x, hx, hzero⟩
  refine ⟨x, ⟨hx, hzero⟩, ?_⟩
  intro y hy
  by_contra hne
  have hxScore :
      5 < 2 * Real.pi * Real.exp (2 * x) - (a + 5 / 2) := by
    by_contra hnot
    have hpos :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_pos_of_score_le_five
        ha0 ha hx.1.le (le_of_not_gt hnot)
    linarith
  have hyScore :
      5 < 2 * Real.pi * Real.exp (2 * y) - (a + 5 / 2) := by
    by_contra hnot
    have hpos :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_pos_of_score_le_five
        ha0 ha hy.1.1.le (le_of_not_gt hnot)
    linarith [hy.2]
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hlt :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_strictAnti_of_five_le_score
        ha hxy hyScore.le
    linarith [hzero, hy.2]
  · have hlt :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_strictAnti_of_five_le_score
        ha hyx hxScore.le
    linarith [hzero, hy.2]

/-- Exact one-transition law for the exceptional ground third derivative. -/
theorem thetaCuspTiltedWardThirdDerivativeCoefficient_ground_sign_around_zero
    {a tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    (∀ {x : ℝ}, 0 ≤ x → x < tau →
      0 < thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x) ∧
    (∀ {x : ℝ}, tau < x →
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x < 0) := by
  have htauScore :
      5 < 2 * Real.pi * Real.exp (2 * tau) - (a + 5 / 2) := by
    by_contra hnot
    have hpos :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_pos_of_score_le_five
        ha0 ha htau.1.le (le_of_not_gt hnot)
    linarith
  constructor
  · intro x hx0 hxtau
    by_cases hxScore :
        2 * Real.pi * Real.exp (2 * x) - (a + 5 / 2) ≤ 5
    · exact
        thetaCuspTiltedWardThirdDerivativeCoefficient_ground_pos_of_score_le_five
          ha0 ha hx0 hxScore
    · have hlt :=
        thetaCuspTiltedWardThirdDerivativeCoefficient_ground_strictAnti_of_five_le_score
          ha hxtau (le_of_not_ge hxScore)
      linarith
  · intro x htaux
    have hlt :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_strictAnti_of_five_le_score
        ha htaux htauScore.le
    linarith

theorem thetaCuspTiltedWardDensityThirdDerivative_neg_of_pos_of_half_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    deriv
      (fun y =>
        thetaCuspTiltedWardCurvature a n y *
          thetaCuspTiltedWardDensity a n y) x < 0 := by
  rw [(hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative
    a n x).deriv]
  exact mul_neg_of_neg_of_pos
    (thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_pos_of_half_le
      ha hn hx)
    (by
      unfold thetaCuspTiltedWardDensity
      rw [thetaCuspWardGibbsAtom_apply]
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      positivity)

theorem thetaCuspTiltedWardDensityThirdDerivative_neg_of_two_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : 0 ≤ x) :
    deriv
      (fun y =>
        thetaCuspTiltedWardCurvature a n y *
          thetaCuspTiltedWardDensity a n y) x < 0 := by
  rw [(hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative
    a n x).deriv]
  exact mul_neg_of_neg_of_pos
    (thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_two_le
      ha hn hx)
    (by
      unfold thetaCuspTiltedWardDensity
      rw [thetaCuspWardGibbsAtom_apply]
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast
          (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
      positivity)

/-- Every shell except the ground shell has strictly positive tilted Ward curvature throughout
the critical aperture.  Thus all higher-shell tilted Ward densities are strictly convex; any
failure of this extra phase rigidity is confined to `n=1`. -/
theorem thetaCuspTiltedWardCurvature_pos_of_two_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspTiltedWardCurvature a n x := by
  let q : ℝ :=
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hexp : 1 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hq24 : 24 < q := by
    dsimp only [q]
    have hprod :
        (4 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) := by
      calc
        (4 : ℝ) = 4 * 1 := by ring
        _ ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) :=
          mul_le_mul hn4 hexp (by norm_num) (by positivity)
    nlinarith [Real.pi_gt_three]
  have hc3 : c < 3 := by
    dsimp only [c]
    linarith
  have hq3 : 0 < q - 3 := by linarith
  have hqc : 0 < q - c := by linarith
  have hsquare :
      (q - 3) ^ 2 ≤ (q - c) ^ 2 :=
    (sq_le_sq₀ hq3.le hqc.le).2 (by linarith)
  have hq8 : 0 < q - 8 := by linarith
  have hpoly : 0 < q ^ 2 - 8 * q + 9 := by
    have hmul : 0 < q * (q - 8) :=
      mul_pos (by linarith) hq8
    nlinarith
  have hmain : 0 < (q - c) ^ 2 - 2 * q := by
    have hbase :
        q ^ 2 - 8 * q + 9 = (q - 3) ^ 2 - 2 * q := by
      ring
    nlinarith
  unfold thetaCuspTiltedWardCurvature
    thetaCuspTiltedWardScore
  dsimp only [q, c] at hmain
  nlinarith

theorem strictConvexOn_thetaCuspTiltedWardDensity_of_two_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n) :
    StrictConvexOn ℝ (Ici 0)
      (thetaCuspTiltedWardDensity a n) := by
  apply strictConvexOn_of_deriv2_pos'
    (convex_Ici 0)
  · exact
      (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspTiltedWardDensity
          a n x).continuousAt).continuousOn
  · intro x hx
    have hderiv :
        deriv (thetaCuspTiltedWardDensity a n) =
          fun y =>
            thetaCuspTiltedWardScore a n y *
              thetaCuspTiltedWardDensity a n y := by
      funext y
      exact
        (hasDerivAt_thetaCuspTiltedWardDensity
          a n y).deriv
    change 0 <
      deriv (deriv (thetaCuspTiltedWardDensity a n)) x
    rw [hderiv,
      (hasDerivAt_thetaCuspTiltedWardDensityDerivative
        a n x).deriv]
    exact mul_pos
      (thetaCuspTiltedWardCurvature_pos_of_two_le
        ha hn hx)
      (by
        unfold thetaCuspTiltedWardDensity
        rw [thetaCuspWardGibbsAtom_apply]
        have hnR : 0 < (n : ℝ) := by
          exact_mod_cast
            (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
        positivity)

/-- Polynomial recursion for logarithmic differentiation after adding the spectral aperture
weight `exp (a x)`. -/
def thetaCuspTiltedLogDerivativeStep
    (a : ℝ) (P : ℝ[X]) : ℝ[X] :=
  C a * P + thetaCuspLogDerivativeStep P

theorem hasDerivAt_exp_mul_thetaCuspPolynomialAtom
    (a : ℝ) (P : ℝ[X]) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        Real.exp (a * y) * thetaCuspPolynomialAtom P n y)
      (Real.exp (a * x) *
        thetaCuspPolynomialAtom
          (thetaCuspTiltedLogDerivativeStep a P) n x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
    convert (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_id x).const_mul a) using 1
    ring
  have hP := hasDerivAt_thetaCuspPolynomialAtom P n x
  convert he.mul hP using 1
  unfold thetaCuspTiltedLogDerivativeStep thetaCuspPolynomialAtom
  simp only [eval_add, eval_mul, eval_C]
  ring

theorem thetaCuspTiltedWardDensity_eq_polynomial
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspTiltedWardDensity a n x =
      Real.exp (a * x) *
        thetaCuspPolynomialAtom (X ^ 2) n x := by
  rfl

theorem thetaCuspTiltedWardDensityDerivative_eq_polynomial
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspTiltedWardScore a n x *
        thetaCuspTiltedWardDensity a n x =
      Real.exp (a * x) *
        thetaCuspPolynomialAtom
          (thetaCuspTiltedLogDerivativeStep a (X ^ 2)) n x := by
  have hleft :=
    (hasDerivAt_thetaCuspTiltedWardDensity a n x).deriv
  have hright :=
    (hasDerivAt_exp_mul_thetaCuspPolynomialAtom
      a (X ^ 2) n x).deriv
  rw [thetaCuspTiltedWardDensity_eq_polynomial] at hleft
  exact hleft.symm.trans hright

theorem thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspTiltedWardCurvature a n x *
        thetaCuspTiltedWardDensity a n x =
      Real.exp (a * x) *
        thetaCuspPolynomialAtom
          (thetaCuspTiltedLogDerivativeStep a
            (thetaCuspTiltedLogDerivativeStep a (X ^ 2))) n x := by
  have hleft :=
    (hasDerivAt_thetaCuspTiltedWardDensityDerivative a n x).deriv
  have hright :=
    (hasDerivAt_exp_mul_thetaCuspPolynomialAtom
      a (thetaCuspTiltedLogDerivativeStep a (X ^ 2)) n x).deriv
  have heq :
      (fun y =>
        thetaCuspTiltedWardScore a n y *
          thetaCuspTiltedWardDensity a n y) =
      (fun y =>
        Real.exp (a * y) *
          thetaCuspPolynomialAtom
            (thetaCuspTiltedLogDerivativeStep a (X ^ 2)) n y) := by
    funext y
    exact thetaCuspTiltedWardDensityDerivative_eq_polynomial a n y
  rw [heq] at hleft
  exact hleft.symm.trans hright

theorem thetaCuspTiltedWardDensityThirdDerivative_eq_polynomial
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x =
      Real.exp (a * x) *
        thetaCuspPolynomialAtom
          (thetaCuspTiltedLogDerivativeStep a
            (thetaCuspTiltedLogDerivativeStep a
              (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))) n x := by
  have hleft :=
    (hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative
      a n x).deriv
  have hright :=
    (hasDerivAt_exp_mul_thetaCuspPolynomialAtom
      a
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
      n x).deriv
  have heq :
      (fun y =>
        thetaCuspTiltedWardCurvature a n y *
          thetaCuspTiltedWardDensity a n y) =
      (fun y =>
        Real.exp (a * y) *
          thetaCuspPolynomialAtom
            (thetaCuspTiltedLogDerivativeStep a
              (thetaCuspTiltedLogDerivativeStep a (X ^ 2))) n y) := by
    funext y
    exact thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
      a n y
  rw [heq] at hleft
  exact hleft.symm.trans hright

/-- Fourth derivative of the tilted Ward density in the native polynomial-Gaussian coordinate. -/
def thetaCuspTiltedWardDensityFourthDerivative
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (a * x) *
    thetaCuspPolynomialAtom
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a
            (thetaCuspTiltedLogDerivativeStep a (X ^ 2))))) n x

/-- Exact normalized fourth derivative of the tilted Ward density. -/
def thetaCuspTiltedWardFourthDerivativeCoefficient
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardThirdDerivativeCoefficient a n x -
    4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) *
      (3 * thetaCuspTiltedWardScore a n x ^ 2 +
        6 * thetaCuspTiltedWardScore a n x -
        12 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) + 4)

theorem hasDerivAt_thetaCuspTiltedWardThirdDerivativeCoefficient
    (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (thetaCuspTiltedWardThirdDerivativeCoefficient a n)
      (-4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) *
        (3 * thetaCuspTiltedWardScore a n x ^ 2 +
          6 * thetaCuspTiltedWardScore a n x -
          12 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) + 4)) x := by
  let q : ℝ → ℝ := fun y =>
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * y)
  have hscore : HasDerivAt
      (thetaCuspTiltedWardScore a n)
      (-4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) x := by
    unfold thetaCuspTiltedWardScore
    have hraw :=
      ((Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
      |>.const_mul
        (-2 * Real.pi * (n : ℝ) ^ 2)
      |>.const_add (a + 5 / 2))
    have hraw' : HasDerivAt
        (fun y =>
          a + 5 / 2 +
            (-2 * Real.pi * (n : ℝ) ^ 2) *
              Real.exp (2 * y))
        ((-2 * Real.pi * (n : ℝ) ^ 2) *
          (Real.exp (2 * x) * (2 * 1))) x := by
      simpa only [Function.comp_apply] using hraw
    convert hraw' using 1 <;> ring
  have hq : HasDerivAt q
      (4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) x := by
    dsimp only [q]
    have hraw :=
      ((Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
      |>.const_mul
        (2 * Real.pi * (n : ℝ) ^ 2))
    have hraw' : HasDerivAt
        (fun y =>
          (2 * Real.pi * (n : ℝ) ^ 2) *
            Real.exp (2 * y))
        ((2 * Real.pi * (n : ℝ) ^ 2) *
          (Real.exp (2 * x) * (2 * 1))) x := by
      simpa only [Function.comp_apply] using hraw
    convert hraw' using 1 <;> ring
  have hraw :=
    (hscore.pow 3).sub ((hq.mul hscore).const_mul 6)
      |>.sub (hq.const_mul 4)
  convert hraw using 1
  · funext y
    unfold thetaCuspTiltedWardThirdDerivativeCoefficient
    dsimp only [q]
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    ring
  · ring

theorem hasDerivAt_thetaCuspTiltedWardDensityThirdDerivative
    (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y =>
        thetaCuspTiltedWardThirdDerivativeCoefficient a n y *
          thetaCuspTiltedWardDensity a n y)
      (thetaCuspTiltedWardDensityFourthDerivative a n x) x := by
  have hright :=
    hasDerivAt_exp_mul_thetaCuspPolynomialAtom
      a
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a (X ^ 2))))
      n x
  have heq :
      (fun y =>
        thetaCuspTiltedWardThirdDerivativeCoefficient a n y *
          thetaCuspTiltedWardDensity a n y) =
      (fun y =>
        Real.exp (a * y) *
          thetaCuspPolynomialAtom
            (thetaCuspTiltedLogDerivativeStep a
              (thetaCuspTiltedLogDerivativeStep a
                (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))) n y) := by
    funext y
    exact thetaCuspTiltedWardDensityThirdDerivative_eq_polynomial
      a n y
  rw [heq]
  simpa only [thetaCuspTiltedWardDensityFourthDerivative] using hright

theorem thetaCuspTiltedWardDensityFourthDerivative_eq_coefficient
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspTiltedWardDensityFourthDerivative a n x =
      thetaCuspTiltedWardFourthDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x := by
  have hleft :=
    hasDerivAt_thetaCuspTiltedWardDensityThirdDerivative a n x
  have hcoefficient :=
    hasDerivAt_thetaCuspTiltedWardThirdDerivativeCoefficient a n x
  have hdensity :=
    hasDerivAt_thetaCuspTiltedWardDensity a n x
  have hright := hcoefficient.mul hdensity
  have hvalue := hleft.unique hright
  unfold thetaCuspTiltedWardFourthDerivativeCoefficient
  nlinarith

/-- Normalized fourth-order boundary remainder for the exceptional ground shell. -/
def thetaCuspGroundFourthOrderRemainderCoefficient
    (a : ℝ) (x : ℝ) : ℝ :=
  4 * thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x +
    x * thetaCuspTiltedWardFourthDerivativeCoefficient a 1 x

theorem thetaCuspGroundFourthOrderRemainder_eq_coefficient
    (a x : ℝ) :
    4 *
        (thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
          thetaCuspTiltedWardDensity a 1 x) +
      x * thetaCuspTiltedWardDensityFourthDerivative a 1 x =
    thetaCuspGroundFourthOrderRemainderCoefficient a x *
      thetaCuspTiltedWardDensity a 1 x := by
  rw [thetaCuspTiltedWardDensityFourthDerivative_eq_coefficient]
  unfold thetaCuspGroundFourthOrderRemainderCoefficient
  ring

theorem thetaCuspTiltedWardThirdDerivativeCoefficient_derivative_neg_of_five_lt_score
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hscore :
      5 <
        2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) -
          (a + 5 / 2)) :
    -4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) *
        (3 * thetaCuspTiltedWardScore a n x ^ 2 +
          6 * thetaCuspTiltedWardScore a n x -
          12 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) + 4) < 0 := by
  let q : ℝ :=
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  let r : ℝ := q - c
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hc : c < 3 := by
    dsimp only [c]
    linarith
  have hr : 5 < r := by
    dsimp only [r, q, c]
    exact hscore
  have hfirst : 0 < 3 * (r - 5) * (r + 1) := by
    positivity
  have hsecond : 0 < 6 * (3 - c) := by
    positivity
  have hbracket :
      0 < 3 * r ^ 2 - 12 * r - 6 * c + 4 := by
    have hid :
        3 * r ^ 2 - 12 * r - 6 * c + 4 =
          1 + 3 * (r - 5) * (r + 1) + 6 * (3 - c) := by
      ring
    rw [hid]
    positivity
  have hscale :
      0 < 4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) := by
    positivity
  unfold thetaCuspTiltedWardScore
  dsimp only [q, c, r] at hbracket
  have hneg :
      (-4 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) *
          (3 * (a + 5 / 2 -
                2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) ^ 2 +
            6 * (a + 5 / 2 -
                2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)) -
            12 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x) + 4) < 0 := by
    apply mul_neg_of_neg_of_pos
    · linarith
    · nlinarith
  exact hneg

theorem thetaCuspTiltedWardFourthDerivativeCoefficient_ground_neg_at_transition
    {a tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    thetaCuspTiltedWardFourthDerivativeCoefficient a 1 tau < 0 := by
  have htauScore :
      5 < 2 * Real.pi * Real.exp (2 * tau) - (a + 5 / 2) := by
    by_contra hnot
    have hpos :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_ground_pos_of_score_le_five
        ha0 ha htau.1.le (le_of_not_gt hnot)
    linarith
  have hderiv :=
    thetaCuspTiltedWardThirdDerivativeCoefficient_derivative_neg_of_five_lt_score
      ha (n := 1) (by norm_num) (x := tau)
        (by simpa using htauScore)
  unfold thetaCuspTiltedWardFourthDerivativeCoefficient
  rw [htauZero]
  norm_num at hderiv ⊢
  linarith

theorem thetaCuspGroundFourthOrderRemainderCoefficient_zero_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < thetaCuspGroundFourthOrderRemainderCoefficient a 0 := by
  unfold thetaCuspGroundFourthOrderRemainderCoefficient
  norm_num
  nlinarith [
    thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero_pos
      ha0 ha]

theorem thetaCuspGroundFourthOrderRemainderCoefficient_neg_at_transition
    {a tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    thetaCuspGroundFourthOrderRemainderCoefficient a tau < 0 := by
  have hfourth :=
    thetaCuspTiltedWardFourthDerivativeCoefficient_ground_neg_at_transition
      ha0 ha htau htauZero
  unfold thetaCuspGroundFourthOrderRemainderCoefficient
  rw [htauZero]
  norm_num
  exact mul_neg_of_pos_of_neg htau.1 hfourth

theorem thetaCuspGroundFourthOrderRemainderCoefficient_pos_of_two_le
    {a x : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 2 ≤ x) :
    0 < thetaCuspGroundFourthOrderRemainderCoefficient a x := by
  let q : ℝ := 2 * Real.pi * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  let r : ℝ := q - c
  have hcLower : 5 / 2 < c := by
    dsimp only [c]
    linarith
  have hcUpper : c < 3 := by
    dsimp only [c]
    linarith
  have hexpFour : 5 < Real.exp 4 := by
    nlinarith [Real.add_one_lt_exp (by norm_num : (4 : ℝ) ≠ 0)]
  have hexp : 5 < Real.exp (2 * x) := by
    exact hexpFour.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hq30 : 30 < q := by
    dsimp only [q]
    nlinarith [Real.pi_gt_three, Real.exp_pos (2 * x)]
  have hr27 : 27 < r := by
    dsimp only [r]
    linarith
  have hr0 : 0 < r := by linarith
  have hquadProduct : 0 < r * (r - 27) := by
    positivity
  have hquad : 0 < r ^ 2 - 12 * r - 8 := by
    nlinarith
  have hthird :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x =
        -r ^ 3 + 6 * r ^ 2 + (6 * c - 4) * r - 4 * c := by
    unfold thetaCuspTiltedWardThirdDerivativeCoefficient
      thetaCuspTiltedWardScore
    dsimp only [q, c, r]
    norm_num
    ring
  have hfourth :
      thetaCuspTiltedWardFourthDerivativeCoefficient a 1 x =
        r ^ 4 - 12 * r ^ 3 + (28 - 12 * c) * r ^ 2 +
          (40 * c - 8) * r + 12 * c ^ 2 - 8 * c := by
    unfold thetaCuspTiltedWardFourthDerivativeCoefficient
      thetaCuspTiltedWardThirdDerivativeCoefficient
      thetaCuspTiltedWardScore
    dsimp only [q, c, r]
    norm_num
    ring
  have hterm₁ :
      0 < r ^ 2 * (r ^ 2 - 12 * r - 8) := by
    exact mul_pos (sq_pos_of_pos hr0) hquad
  have hterm₂ : 0 < 12 * (3 - c) * r ^ 2 := by
    positivity
  have hterm₃ : 0 < (40 * c - 8) * r := by
    have : 0 < 40 * c - 8 := by linarith
    positivity
  have hterm₄ : 0 < 4 * c * (3 * c - 2) := by
    have hc0 : 0 < c := by linarith
    have : 0 < 3 * c - 2 := by linarith
    positivity
  have hfourthPoly :
      0 < r ^ 4 - 12 * r ^ 3 + (28 - 12 * c) * r ^ 2 +
        (40 * c - 8) * r + 12 * c ^ 2 - 8 * c := by
    have hid :
        r ^ 4 - 12 * r ^ 3 + (28 - 12 * c) * r ^ 2 +
            (40 * c - 8) * r + 12 * c ^ 2 - 8 * c =
          r ^ 2 * (r ^ 2 - 12 * r - 8) +
            12 * (3 - c) * r ^ 2 +
            (40 * c - 8) * r +
            4 * c * (3 * c - 2) := by
      ring
    rw [hid]
    positivity
  have hfourthPos :
      0 < thetaCuspTiltedWardFourthDerivativeCoefficient a 1 x := by
    rw [hfourth]
    exact hfourthPoly
  have hlead : 0 < 2 * r ^ 3 * (r - 14) := by
    have : 0 < r - 14 := by linarith
    positivity
  have hrest₁ : 0 < (80 - 24 * c) * r ^ 2 := by
    have : 0 < 80 - 24 * c := by linarith
    positivity
  have hrest₂ : 0 < (104 * c - 32) * r := by
    have : 0 < 104 * c - 32 := by linarith
    positivity
  have hrest₃ : 0 < 8 * c * (3 * c - 4) := by
    have hc0 : 0 < c := by linarith
    have : 0 < 3 * c - 4 := by linarith
    positivity
  have hcomboPoly :
      0 <
        2 *
            (r ^ 4 - 12 * r ^ 3 + (28 - 12 * c) * r ^ 2 +
              (40 * c - 8) * r + 12 * c ^ 2 - 8 * c) +
          4 * (-r ^ 3 + 6 * r ^ 2 + (6 * c - 4) * r - 4 * c) := by
    have hid :
        2 *
              (r ^ 4 - 12 * r ^ 3 + (28 - 12 * c) * r ^ 2 +
                (40 * c - 8) * r + 12 * c ^ 2 - 8 * c) +
            4 * (-r ^ 3 + 6 * r ^ 2 + (6 * c - 4) * r - 4 * c) =
          2 * r ^ 3 * (r - 14) +
            (80 - 24 * c) * r ^ 2 +
            (104 * c - 32) * r +
            8 * c * (3 * c - 4) := by
      ring
    rw [hid]
    positivity
  have hcombo :
      0 <
        2 * thetaCuspTiltedWardFourthDerivativeCoefficient a 1 x +
          4 * thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x := by
    rw [hfourth, hthird]
    exact hcomboPoly
  have hxmul :
      2 * thetaCuspTiltedWardFourthDerivativeCoefficient a 1 x ≤
        x * thetaCuspTiltedWardFourthDerivativeCoefficient a 1 x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) hfourthPos.le]
  unfold thetaCuspGroundFourthOrderRemainderCoefficient
  linarith

/-- The ground fourth-order boundary remainder has at least two genuine sign transitions:
one before the third-derivative transition and one after it. -/
theorem exists_two_thetaCuspGroundFourthOrderRemainderCoefficient_zeros
    {a tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    ∃ sigma₁ sigma₂ : ℝ,
      sigma₁ ∈ Ioo 0 tau ∧
      sigma₂ ∈ Ioo tau 2 ∧
      thetaCuspGroundFourthOrderRemainderCoefficient a sigma₁ = 0 ∧
      thetaCuspGroundFourthOrderRemainderCoefficient a sigma₂ = 0 := by
  let F : ℝ → ℝ :=
    thetaCuspGroundFourthOrderRemainderCoefficient a
  have hcont : Continuous F := by
    dsimp only [F]
    unfold thetaCuspGroundFourthOrderRemainderCoefficient
      thetaCuspTiltedWardFourthDerivativeCoefficient
      thetaCuspTiltedWardThirdDerivativeCoefficient
      thetaCuspTiltedWardScore
    fun_prop
  have hzeroPos : 0 < F 0 := by
    simpa only [F] using
      thetaCuspGroundFourthOrderRemainderCoefficient_zero_pos ha0 ha
  have htauNeg : F tau < 0 := by
    simpa only [F] using
      thetaCuspGroundFourthOrderRemainderCoefficient_neg_at_transition
        ha0 ha htau htauZero
  have htwoPos : 0 < F 2 := by
    simpa only [F] using
      thetaCuspGroundFourthOrderRemainderCoefficient_pos_of_two_le
        ha0 ha (by norm_num)
  obtain ⟨sigma₁, hsigma₁, hsigma₁Zero⟩ :=
    intermediate_value_Ioo' htau.1.le
      (hcont.continuousOn.mono (by rfl))
      (show (0 : ℝ) ∈ Ioo (F tau) (F 0) from
        ⟨htauNeg, hzeroPos⟩)
  obtain ⟨sigma₂, hsigma₂, hsigma₂Zero⟩ :=
    intermediate_value_Ioo (by linarith [htau.2])
      (hcont.continuousOn.mono (by rfl))
      (show (0 : ℝ) ∈ Ioo (F tau) (F 2) from
        ⟨htauNeg, htwoPos⟩)
  exact
    ⟨sigma₁, sigma₂, hsigma₁, hsigma₂,
      by simpa only [F] using hsigma₁Zero,
      by simpa only [F] using hsigma₂Zero⟩

theorem integrableOn_thetaCuspTiltedWardDensitySecondDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x =>
        thetaCuspTiltedWardCurvature a n x *
          thetaCuspTiltedWardDensity a n x)
      (Ioi 0) := by
  have h :=
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
      hn ha
  exact h.congr (Eventually.of_forall fun x =>
    (thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
      a n x).symm)

theorem integrableOn_thetaCuspTiltedWardDensityThirdDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x =>
        thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x)
      (Ioi 0) := by
  have h :=
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a (X ^ 2))))
      hn ha
  exact h.congr (Eventually.of_forall fun x =>
    (thetaCuspTiltedWardDensityThirdDerivative_eq_polynomial
      a n x).symm)

theorem integrableOn_thetaCuspTiltedWardDensityFourthDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (thetaCuspTiltedWardDensityFourthDerivative a n)
      (Ioi 0) := by
  simpa only [thetaCuspTiltedWardDensityFourthDerivative] using
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a
            (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))))
      hn ha

theorem tendsto_thetaCuspTiltedWardDensityDerivative_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x =>
        thetaCuspTiltedWardScore a n x *
          thetaCuspTiltedWardDensity a n x)
      atTop (𝓝 0) := by
  have h :=
    exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a (X ^ 2))
      hn ha
  exact h.congr' (Eventually.of_forall fun x =>
    (thetaCuspTiltedWardDensityDerivative_eq_polynomial
      a n x).symm)

theorem tendsto_thetaCuspTiltedWardDensitySecondDerivative_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x =>
        thetaCuspTiltedWardCurvature a n x *
          thetaCuspTiltedWardDensity a n x)
      atTop (𝓝 0) := by
  have h :=
    exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
      hn ha
  exact h.congr' (Eventually.of_forall fun x =>
    (thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
      a n x).symm)

theorem integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : a < 1) :
    IntegrableOn
      (fun x : ℝ =>
        x * (Real.exp (a * x) *
          thetaCuspPolynomialAtom P n x))
      (Ioi 0) := by
  let d : ℝ := (1 - a) / 2
  let z : ℝ := a + d
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hz : z < 1 := by
    dsimp only [z, d]
    linarith
  have hbase :=
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      P hn hz
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          (1 / d) *
            (Real.exp (z * x) *
              thetaCuspPolynomialAtom P n x))
        (Ioi 0) :=
    hbase.const_mul (1 / d)
  apply Integrable.mono hmajor
  · have hatom : Continuous (thetaCuspPolynomialAtom P n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom P n x).continuousAt
    exact
      (continuous_id.mul
        ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).mul
          hatom)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hdx : d * x ≤ Real.exp (d * x) := by
      nlinarith [Real.add_one_le_exp (d * x)]
    have hxexp : x ≤ Real.exp (d * x) / d := by
      exact (le_div_iff₀ hd).2 (by simpa [mul_comm] using hdx)
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos hx, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : 0 < 1 / d),
      abs_of_pos (Real.exp_pos _)]
    have hexp :
        Real.exp (z * x) =
          Real.exp (d * x) * Real.exp (a * x) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [z]
      ring
    rw [hexp]
    have hatom0 := abs_nonneg (thetaCuspPolynomialAtom P n x)
    calc
      x * (Real.exp (a * x) *
          |thetaCuspPolynomialAtom P n x|) ≤
        (Real.exp (d * x) / d) *
          (Real.exp (a * x) *
            |thetaCuspPolynomialAtom P n x|) :=
        mul_le_mul_of_nonneg_right hxexp
          (mul_nonneg (Real.exp_pos (a * x)).le hatom0)
      _ = 1 / d *
          (Real.exp (d * x) * Real.exp (a * x) *
            |thetaCuspPolynomialAtom P n x|) := by ring

theorem tendsto_id_mul_exp_mul_thetaCuspPolynomialAtom_atTop_zero_of_lt_one
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : a < 1) :
    Tendsto
      (fun x : ℝ =>
        x * (Real.exp (a * x) *
          thetaCuspPolynomialAtom P n x))
      atTop (𝓝 0) := by
  let d : ℝ := (1 - a) / 2
  let z : ℝ := a + d
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hz : z < 1 := by
    dsimp only [z, d]
    linarith
  have hscale : Tendsto (fun x : ℝ => d * x) atTop atTop :=
    tendsto_id.const_mul_atTop hd
  have hscaled :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hslow :
      Tendsto (fun x : ℝ => x * Real.exp (-(d * x)))
        atTop (𝓝 0) := by
    have hmul := (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => d⁻¹) atTop (𝓝 d⁻¹)).mul hscaled
    convert hmul using 1
    · funext x
      simp only [Function.comp_apply, pow_one]
      rw [mul_assoc d x (Real.exp (-(d * x))),
        ← mul_assoc d⁻¹ d (x * Real.exp (-(d * x))),
        inv_mul_cancel₀ hd.ne', one_mul]
    · simp
  have hfast :=
    exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
      P hn hz
  have hprod := hslow.mul hfast
  convert hprod using 1
  · funext x
    dsimp only [z]
    rw [show Real.exp (a * x) =
        Real.exp (-(d * x)) * Real.exp ((a + d) * x) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring
  · simp

theorem integrableOn_thetaCuspTiltedWardDensity
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (thetaCuspTiltedWardDensity a n) (Ioi 0) := by
  simpa only [thetaCuspTiltedWardDensity,
    thetaCuspWardGibbsAtom] using
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (X ^ 2) hn ha

theorem integrableOn_thetaCuspTiltedWardDensityDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x => thetaCuspTiltedWardScore a n x *
        thetaCuspTiltedWardDensity a n x) (Ioi 0) := by
  have hbase :=
    integrableOn_thetaCuspTiltedWardDensity ha hn
  have hstep :=
    integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspLogDerivativeStep (X ^ 2)) hn ha
  have hsum := (hbase.const_mul a).add hstep
  apply hsum.congr
  filter_upwards with x
  simp only [Pi.add_apply]
  rw [thetaCuspWardGibbsAtom_step_eq_score]
  simp only [Pi.add_apply, thetaCuspTiltedWardDensity,
    thetaCuspTiltedWardScore, thetaCuspWardGibbsAtom]
  ring

theorem tendsto_thetaCuspTiltedWardDensity_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto (thetaCuspTiltedWardDensity a n)
      atTop (𝓝 0) := by
  simpa only [thetaCuspTiltedWardDensity,
    thetaCuspWardGibbsAtom] using
    exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one
      (X ^ 2) hn ha

theorem integrableOn_id_mul_thetaCuspTiltedWardDensity
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x => x * thetaCuspTiltedWardDensity a n x)
      (Ioi 0) := by
  simpa only [thetaCuspTiltedWardDensity,
    thetaCuspWardGibbsAtom] using
    integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (X ^ 2) hn ha

theorem integrableOn_id_mul_thetaCuspTiltedWardDensityDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x => x *
        (thetaCuspTiltedWardScore a n x *
          thetaCuspTiltedWardDensity a n x))
      (Ioi 0) := by
  have h :=
    integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a (X ^ 2)) hn ha
  exact h.congr (Eventually.of_forall fun x => by
    exact congrArg (fun y => x * y)
      (thetaCuspTiltedWardDensityDerivative_eq_polynomial
        a n x).symm)

theorem tendsto_id_mul_thetaCuspTiltedWardDensity_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x => x * thetaCuspTiltedWardDensity a n x)
      atTop (𝓝 0) := by
  simpa only [thetaCuspTiltedWardDensity,
    thetaCuspWardGibbsAtom] using
    tendsto_id_mul_exp_mul_thetaCuspPolynomialAtom_atTop_zero_of_lt_one
      (X ^ 2) hn ha

theorem integrableOn_id_mul_thetaCuspTiltedWardDensitySecondDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x => x *
        (thetaCuspTiltedWardCurvature a n x *
          thetaCuspTiltedWardDensity a n x))
      (Ioi 0) := by
  have h :=
    integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
      hn ha
  exact h.congr (Eventually.of_forall fun x =>
    congrArg (fun y => x * y)
      (thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
        a n x).symm)

theorem integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x => x *
        (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x))
      (Ioi 0) := by
  have h :=
    integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a (X ^ 2))))
      hn ha
  exact h.congr (Eventually.of_forall fun x =>
    congrArg (fun y => x * y)
      (thetaCuspTiltedWardDensityThirdDerivative_eq_polynomial
        a n x).symm)

theorem integrableOn_id_mul_thetaCuspTiltedWardDensityFourthDerivative
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x => x * thetaCuspTiltedWardDensityFourthDerivative a n x)
      (Ioi 0) := by
  simpa only [thetaCuspTiltedWardDensityFourthDerivative] using
    integrableOn_id_mul_exp_mul_thetaCuspPolynomialAtom_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a
            (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))))
      hn ha

theorem tendsto_id_mul_thetaCuspTiltedWardDensityDerivative_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x => x *
        (thetaCuspTiltedWardScore a n x *
          thetaCuspTiltedWardDensity a n x))
      atTop (𝓝 0) := by
  have h :=
    tendsto_id_mul_exp_mul_thetaCuspPolynomialAtom_atTop_zero_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a (X ^ 2))
      hn ha
  exact h.congr' (Eventually.of_forall fun x =>
    congrArg (fun y => x * y)
      (thetaCuspTiltedWardDensityDerivative_eq_polynomial
        a n x).symm)

theorem tendsto_id_mul_thetaCuspTiltedWardDensitySecondDerivative_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x => x *
        (thetaCuspTiltedWardCurvature a n x *
          thetaCuspTiltedWardDensity a n x))
      atTop (𝓝 0) := by
  have h :=
    tendsto_id_mul_exp_mul_thetaCuspPolynomialAtom_atTop_zero_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
      hn ha
  exact h.congr' (Eventually.of_forall fun x =>
    congrArg (fun y => x * y)
      (thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
        a n x).symm)

theorem tendsto_id_mul_thetaCuspTiltedWardDensityThirdDerivative_atTop_zero
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun x => x *
        (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x))
      atTop (𝓝 0) := by
  have h :=
    tendsto_id_mul_exp_mul_thetaCuspPolynomialAtom_atTop_zero_of_lt_one
      (thetaCuspTiltedLogDerivativeStep a
        (thetaCuspTiltedLogDerivativeStep a
          (thetaCuspTiltedLogDerivativeStep a (X ^ 2))))
      hn ha
  exact h.congr' (Eventually.of_forall fun x =>
    congrArg (fun y => x * y)
      (thetaCuspTiltedWardDensityThirdDerivative_eq_polynomial
        a n x).symm)

/-- Throughout the critical aperture, every tilted Ward shell is strictly decreasing on the
positive half-line. -/
theorem thetaCuspTiltedWardScore_neg
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspTiltedWardScore a n x < 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    nlinarith
  have hexp : 1 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod :
      1 ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) :=
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) :=
        mul_le_mul hn1 hexp (by norm_num) (by positivity)
  unfold thetaCuspTiltedWardScore
  nlinarith [Real.pi_gt_three]

theorem thetaCuspTiltedWardDensity_pos
    (a : ℝ) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 < thetaCuspTiltedWardDensity a n x := by
  unfold thetaCuspTiltedWardDensity
  rw [thetaCuspWardGibbsAtom_apply]
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  positivity

/-- Coefficient exposed by integrating the first spectral moment against `1-cos`. -/
def thetaCuspTiltedWardDerivativeRotationCoefficient
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x * (-thetaCuspTiltedWardScore a n x) - 1

/-- Signed density whose positive-kernel integral is the real derivative rotation problem. -/
def thetaCuspTiltedWardDerivativeRotationDensity
    (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -(thetaCuspTiltedWardDensity a n x +
    x * (thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x))

theorem thetaCuspTiltedWardDerivativeRotationDensity_eq
    (a : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspTiltedWardDerivativeRotationDensity a n x =
      thetaCuspTiltedWardDerivativeRotationCoefficient a n x *
        thetaCuspTiltedWardDensity a n x := by
  unfold thetaCuspTiltedWardDerivativeRotationDensity
    thetaCuspTiltedWardDerivativeRotationCoefficient
  ring

theorem hasDerivAt_thetaCuspTiltedWardDerivativeRotationCoefficient
    (a : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (thetaCuspTiltedWardDerivativeRotationCoefficient a n)
      (-thetaCuspTiltedWardScore a n x +
        x * (4 * Real.pi * (n : ℝ) ^ 2 *
          Real.exp (2 * x))) x := by
  have hscore : HasDerivAt
      (thetaCuspTiltedWardScore a n)
      (-4 * Real.pi * (n : ℝ) ^ 2 *
        Real.exp (2 * x)) x := by
    unfold thetaCuspTiltedWardScore
    have hraw :=
      (Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
      |>.const_mul
        (-2 * Real.pi * (n : ℝ) ^ 2)
      |>.const_add (a + 5 / 2)
    have hraw' : HasDerivAt
        (fun y =>
          a + 5 / 2 +
            (-2 * Real.pi * (n : ℝ) ^ 2) *
              Real.exp (2 * y))
        ((-2 * Real.pi * (n : ℝ) ^ 2) *
          (Real.exp (2 * x) * (2 * 1))) x := by
      simpa only [Function.comp_apply] using hraw
    convert hraw' using 1 <;> ring
  unfold thetaCuspTiltedWardDerivativeRotationCoefficient
  convert ((hasDerivAt_id x).mul hscore.neg).sub_const 1
    using 1 <;> simp only [id_eq, Pi.neg_apply] <;> ring

theorem thetaCuspTiltedWardDerivativeRotationCoefficient_deriv_pos
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 ≤ x) :
    0 < deriv
      (thetaCuspTiltedWardDerivativeRotationCoefficient a n) x := by
  rw [(hasDerivAt_thetaCuspTiltedWardDerivativeRotationCoefficient
    a n x).deriv]
  have hs := thetaCuspTiltedWardScore_neg ha hn hx
  have htail : 0 ≤
      x * (4 * Real.pi * (n : ℝ) ^ 2 *
        Real.exp (2 * x)) := by positivity
  linarith

/-- The derivative-rotation coefficient has exactly one possible sign transition on positive
half-line: it is strictly increasing. -/
theorem strictMonoOn_thetaCuspTiltedWardDerivativeRotationCoefficient
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n) :
    StrictMonoOn
      (thetaCuspTiltedWardDerivativeRotationCoefficient a n)
      (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x _hx
    exact
      (hasDerivAt_thetaCuspTiltedWardDerivativeRotationCoefficient
        a n x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici, mem_Ioi] at hx
    exact
      thetaCuspTiltedWardDerivativeRotationCoefficient_deriv_pos
        ha hn hx.le

@[simp] theorem thetaCuspTiltedWardDerivativeRotationCoefficient_zero
    (a : ℝ) (n : ℕ) :
    thetaCuspTiltedWardDerivativeRotationCoefficient a n 0 = -1 := by
  simp [thetaCuspTiltedWardDerivativeRotationCoefficient]

/-- For every higher shell, all possible negative derivative-rotation mass is confined to the
universal boundary layer `x < 1/20`. -/
theorem thetaCuspTiltedWardDerivativeRotationCoefficient_pos_of_one_div_twenty_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : 1 / 20 ≤ x) :
    0 < thetaCuspTiltedWardDerivativeRotationCoefficient a n x := by
  let q : ℝ :=
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  have hx0 : 0 ≤ x := by norm_num at hx ⊢; linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hexp : 1 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod :
      (4 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) := by
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) :=
        mul_le_mul hn4 hexp (by norm_num) (by positivity)
  have hq24 : 24 < q := by
    dsimp only [q]
    nlinarith [Real.pi_gt_three]
  have hc3 : c < 3 := by
    dsimp only [c]
    linarith
  have hgap : 20 < q - c := by linarith
  have hmul : 1 < x * (q - c) := by
    calc
      (1 : ℝ) = (1 / 20 : ℝ) * 20 := by norm_num
      _ ≤ x * 20 := mul_le_mul_of_nonneg_right hx (by norm_num)
      _ < x * (q - c) := mul_lt_mul_of_pos_left hgap hxpos
  unfold thetaCuspTiltedWardDerivativeRotationCoefficient
    thetaCuspTiltedWardScore
  dsimp only [q, c] at hmul
  linarith

/-- For the exceptional ground shell as well, all negative derivative-rotation mass is confined
to the compact boundary layer `x < 1/3`. -/
theorem thetaCuspTiltedWardDerivativeRotationCoefficient_pos_of_one_div_three_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 1 / 3 ≤ x) :
    0 < thetaCuspTiltedWardDerivativeRotationCoefficient a n x := by
  let q : ℝ :=
    2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * x)
  let c : ℝ := a + 5 / 2
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnR : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
    nlinarith
  have hexp : 1 ≤ Real.exp (2 * x) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod :
      1 ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (n : ℝ) ^ 2 * Real.exp (2 * x) :=
        mul_le_mul hn1 hexp (by norm_num) (by positivity)
  have hq6 : 6 < q := by
    dsimp only [q]
    nlinarith [Real.pi_gt_three]
  have hc3 : c < 3 := by
    dsimp only [c]
    linarith
  have hgap : 3 < q - c := by linarith
  have hmul : 1 < x * (q - c) := by
    calc
      (1 : ℝ) = (1 / 3 : ℝ) * 3 := by norm_num
      _ ≤ x * 3 := mul_le_mul_of_nonneg_right hx (by norm_num)
      _ < x * (q - c) := mul_lt_mul_of_pos_left hgap hxpos
  unfold thetaCuspTiltedWardDerivativeRotationCoefficient
    thetaCuspTiltedWardScore
  dsimp only [q, c] at hmul
  linarith

theorem thetaCuspTiltedWardDerivativeRotationDensity_pos_of_one_div_three_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 1 / 3 ≤ x) :
    0 < thetaCuspTiltedWardDerivativeRotationDensity a n x := by
  rw [thetaCuspTiltedWardDerivativeRotationDensity_eq]
  exact mul_pos
    (thetaCuspTiltedWardDerivativeRotationCoefficient_pos_of_one_div_three_le
      ha hn hx)
    (thetaCuspTiltedWardDensity_pos a hn x)

theorem thetaCuspTiltedWardDerivativeRotationDensity_pos_of_one_div_twenty_le
    {a : ℝ} (ha : a < 1 / 2)
    {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : 1 / 20 ≤ x) :
    0 < thetaCuspTiltedWardDerivativeRotationDensity a n x := by
  rw [thetaCuspTiltedWardDerivativeRotationDensity_eq]
  exact mul_pos
    (thetaCuspTiltedWardDerivativeRotationCoefficient_pos_of_one_div_twenty_le
      ha hn hx)
    (thetaCuspTiltedWardDensity_pos a
      (lt_of_lt_of_le (by norm_num) hn) x)

theorem thetaCuspTiltedWardDerivativeRotationDensity_zero_neg
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    thetaCuspTiltedWardDerivativeRotationDensity a n 0 < 0 := by
  rw [thetaCuspTiltedWardDerivativeRotationDensity_eq,
    thetaCuspTiltedWardDerivativeRotationCoefficient_zero]
  have hpos := thetaCuspTiltedWardDensity_pos a hn 0
  nlinarith

/-- Universal third-order kernel generated by three integrations of `u sin u` from the origin. -/
def thirdOrderSineKernel (u : ℝ) : ℝ :=
  u * (2 + Real.cos u) - 3 * Real.sin u

def thirdOrderSineKernelFirstDerivative (u : ℝ) : ℝ :=
  2 - 2 * Real.cos u - u * Real.sin u

def thirdOrderSineKernelSecondDerivative (u : ℝ) : ℝ :=
  Real.sin u - u * Real.cos u

theorem hasDerivAt_thirdOrderSineKernel
    (u : ℝ) :
    HasDerivAt thirdOrderSineKernel
      (thirdOrderSineKernelFirstDerivative u) u := by
  unfold thirdOrderSineKernel thirdOrderSineKernelFirstDerivative
  convert
    ((hasDerivAt_id u).mul
      ((hasDerivAt_const u 2).add (Real.hasDerivAt_cos u))).sub
        ((Real.hasDerivAt_sin u).const_mul 3) using 1 <;>
    simp only [id_eq, Pi.add_apply] <;> ring

theorem hasDerivAt_thirdOrderSineKernelFirstDerivative
    (u : ℝ) :
    HasDerivAt thirdOrderSineKernelFirstDerivative
      (thirdOrderSineKernelSecondDerivative u) u := by
  unfold thirdOrderSineKernelFirstDerivative
    thirdOrderSineKernelSecondDerivative
  convert
    ((hasDerivAt_const u 2).sub
      ((Real.hasDerivAt_cos u).const_mul 2)).sub
        ((hasDerivAt_id u).mul (Real.hasDerivAt_sin u)) using 1 <;>
    simp only [id_eq] <;> ring

theorem hasDerivAt_thirdOrderSineKernelSecondDerivative
    (u : ℝ) :
    HasDerivAt thirdOrderSineKernelSecondDerivative
      (u * Real.sin u) u := by
  unfold thirdOrderSineKernelSecondDerivative
  convert
    (Real.hasDerivAt_sin u).sub
      ((hasDerivAt_id u).mul (Real.hasDerivAt_cos u)) using 1 <;>
    simp only [id_eq] <;> ring

/-- **Universal strict kernel law.** The third-order sine kernel is positive at every positive
argument.  Below `3` this follows from three successive derivative sign propagations; above `3`
the elementary bounds `-1 ≤ cos` and `sin ≤ 1` suffice. -/
theorem thirdOrderSineKernel_pos
    {u : ℝ} (hu : 0 < u) :
    0 < thirdOrderSineKernel u := by
  by_cases hu3 : u ≤ 3
  · have hK2mono :
        StrictMonoOn thirdOrderSineKernelSecondDerivative
          (Icc 0 3) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 3)
      · exact
          (continuous_iff_continuousAt.mpr fun y =>
            (hasDerivAt_thirdOrderSineKernelSecondDerivative
              y).continuousAt).continuousOn
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hasDerivAt_thirdOrderSineKernelSecondDerivative y).deriv]
        exact mul_pos hy.1
          (Real.sin_pos_of_pos_of_lt_pi hy.1
            (lt_trans hy.2 Real.pi_gt_three))
    have hK2pos :
        ∀ {y : ℝ}, 0 < y → y ≤ 3 →
          0 < thirdOrderSineKernelSecondDerivative y := by
      intro y hy0 hy3
      have hmono := hK2mono
        (show (0 : ℝ) ∈ Icc 0 3 by norm_num)
        (show y ∈ Icc 0 3 by exact ⟨hy0.le, hy3⟩)
        hy0
      simpa [thirdOrderSineKernelSecondDerivative] using hmono
    have hK1mono :
        StrictMonoOn thirdOrderSineKernelFirstDerivative
          (Icc 0 3) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 3)
      · exact
          (continuous_iff_continuousAt.mpr fun y =>
            (hasDerivAt_thirdOrderSineKernelFirstDerivative
              y).continuousAt).continuousOn
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hasDerivAt_thirdOrderSineKernelFirstDerivative y).deriv]
        exact hK2pos hy.1 hy.2.le
    have hK1pos :
        ∀ {y : ℝ}, 0 < y → y ≤ 3 →
          0 < thirdOrderSineKernelFirstDerivative y := by
      intro y hy0 hy3
      have hmono := hK1mono
        (show (0 : ℝ) ∈ Icc 0 3 by norm_num)
        (show y ∈ Icc 0 3 by exact ⟨hy0.le, hy3⟩)
        hy0
      simpa [thirdOrderSineKernelFirstDerivative] using hmono
    have hKmono :
        StrictMonoOn thirdOrderSineKernel (Icc 0 3) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 3)
      · exact
          (continuous_iff_continuousAt.mpr fun y =>
            (hasDerivAt_thirdOrderSineKernel y).continuousAt).continuousOn
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hasDerivAt_thirdOrderSineKernel y).deriv]
        exact hK1pos hy.1 hy.2.le
    have hmono := hKmono
      (show (0 : ℝ) ∈ Icc 0 3 by norm_num)
      (show u ∈ Icc 0 3 by exact ⟨hu.le, hu3⟩)
      hu
    simpa [thirdOrderSineKernel] using hmono
  · have hu3' : 3 < u := lt_of_not_ge hu3
    have hcos : 1 ≤ 2 + Real.cos u := by
      nlinarith [neg_one_le_cos u]
    have hmul :
        u ≤ u * (2 + Real.cos u) :=
      by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hcos hu.le
    unfold thirdOrderSineKernel
    nlinarith [Real.sin_le_one u]

/-- **Exact all-shell third-order sine identity.**  Three integrations by parts remove every
boundary term and convert the first sine moment into the universal positive kernel:

`b⁴ ∫ x f(x) sin(bx) dx = -∫ f'''(x) thirdOrderSineKernel(bx) dx`.

No shell-sign assumption enters this identity.  In particular it exposes the ground-shell defect
without mixing it with the already closed higher-shell sign argument. -/
theorem integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
    {a b : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) :
    b ^ 4 * (∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) =
      -∫ x : ℝ in Ioi 0,
        (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x) *
            thirdOrderSineKernel (b * x) := by
  let f₀ : ℝ → ℝ := thetaCuspTiltedWardDensity a n
  let f₁ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x
  let f₂ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardCurvature a n x *
      thetaCuspTiltedWardDensity a n x
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  let k₀ : ℝ → ℝ := fun x => thirdOrderSineKernel (b * x)
  let k₁ : ℝ → ℝ := fun x =>
    b * thirdOrderSineKernelFirstDerivative (b * x)
  let k₂ : ℝ → ℝ := fun x =>
    b ^ 2 * thirdOrderSineKernelSecondDerivative (b * x)
  let k₃ : ℝ → ℝ := fun x =>
    b ^ 4 * x * Real.sin (b * x)
  have hn0 : 0 < n := hn
  have ha1 : a < 1 := ha
  have hf₀ (x : ℝ) : HasDerivAt f₀ (f₁ x) x := by
    simpa only [f₀, f₁] using
      hasDerivAt_thetaCuspTiltedWardDensity a n x
  have hf₁ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    simpa only [f₁, f₂] using
      hasDerivAt_thetaCuspTiltedWardDensityDerivative a n x
  have hf₂ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    simpa only [f₂, f₃] using
      hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative a n x
  have hk₀ (x : ℝ) : HasDerivAt k₀ (k₁ x) x := by
    dsimp only [k₀, k₁]
    convert
      (hasDerivAt_thirdOrderSineKernel (b * x)).comp x
        ((hasDerivAt_id x).const_mul b) using 1 <;>
      (try simp only [Function.comp_apply, id_eq]) <;> ring
  have hk₁ (x : ℝ) : HasDerivAt k₁ (k₂ x) x := by
    dsimp only [k₁, k₂]
    convert
      ((hasDerivAt_thirdOrderSineKernelFirstDerivative
        (b * x)).comp x
          ((hasDerivAt_id x).const_mul b)).const_mul b using 1 <;>
      (try simp only [Function.comp_apply, id_eq]) <;> ring
  have hk₂ (x : ℝ) : HasDerivAt k₂ (k₃ x) x := by
    dsimp only [k₂, k₃]
    convert
      ((hasDerivAt_thirdOrderSineKernelSecondDerivative
        (b * x)).comp x
          ((hasDerivAt_id x).const_mul b)).const_mul (b ^ 2) using 1 <;>
      (try simp only [Function.comp_apply, id_eq]) <;> ring
  have hsinInt :
      ∀ (g : ℝ → ℝ), IntegrableOn g (Ioi 0) →
        IntegrableOn
          (fun x => Real.sin (b * x) * g x) (Ioi 0) := by
    intro g hg
    apply Integrable.bdd_mul hg
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hcosInt :
      ∀ (g : ℝ → ℝ), IntegrableOn g (Ioi 0) →
        IntegrableOn
          (fun x => Real.cos (b * x) * g x) (Ioi 0) := by
    intro g hg
    apply Integrable.bdd_mul hg
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hf₀Int : IntegrableOn f₀ (Ioi 0) := by
    simpa only [f₀] using
      integrableOn_thetaCuspTiltedWardDensity ha1 hn0
  have hxf₀Int : IntegrableOn (fun x => x * f₀ x) (Ioi 0) := by
    simpa only [f₀] using
      integrableOn_id_mul_thetaCuspTiltedWardDensity ha1 hn0
  have hf₁Int : IntegrableOn f₁ (Ioi 0) := by
    simpa only [f₁] using
      integrableOn_thetaCuspTiltedWardDensityDerivative ha1 hn0
  have hxf₁Int : IntegrableOn (fun x => x * f₁ x) (Ioi 0) := by
    simpa only [f₁] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityDerivative ha1 hn0
  have hf₂Int : IntegrableOn f₂ (Ioi 0) := by
    simpa only [f₂] using
      integrableOn_thetaCuspTiltedWardDensitySecondDerivative ha1 hn0
  have hxf₂Int : IntegrableOn (fun x => x * f₂ x) (Ioi 0) := by
    simpa only [f₂] using
      integrableOn_id_mul_thetaCuspTiltedWardDensitySecondDerivative
        ha1 hn0
  have hf₃Int : IntegrableOn f₃ (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_thetaCuspTiltedWardDensityThirdDerivative ha1 hn0
  have hxf₃Int : IntegrableOn (fun x => x * f₃ x) (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative
        ha1 hn0
  have hf₀k₃ : IntegrableOn (f₀ * k₃) (Ioi 0) := by
    have h := (hsinInt (fun x => x * f₀ x) hxf₀Int).const_mul (b ^ 4)
    apply h.congr
    filter_upwards with x
    dsimp only [f₀, k₃, Pi.mul_apply]
    ring
  have hf₁k₂ : IntegrableOn (f₁ * k₂) (Ioi 0) := by
    have hsin := hsinInt f₁ hf₁Int
    have hcos := hcosInt (fun x => x * f₁ x) hxf₁Int
    have h :=
      (hsin.sub (hcos.const_mul b)).const_mul (b ^ 2)
    apply h.congr
    filter_upwards with x
    dsimp only [f₁, k₂, thirdOrderSineKernelSecondDerivative,
      Pi.mul_apply]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    ring
  have hf₂k₁ : IntegrableOn (f₂ * k₁) (Ioi 0) := by
    have hcos := hcosInt f₂ hf₂Int
    have hsin := hsinInt (fun x => x * f₂ x) hxf₂Int
    have h :=
      ((hf₂Int.const_mul 2).sub (hcos.const_mul 2) |>.sub
        (hsin.const_mul b)).const_mul b
    apply h.congr
    filter_upwards with x
    dsimp only [f₂, k₁, thirdOrderSineKernelFirstDerivative,
      Pi.mul_apply]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    ring
  have hf₃k₀ : IntegrableOn (f₃ * k₀) (Ioi 0) := by
    have hxbase := hxf₃Int.const_mul 2
    have hxcos := hcosInt (fun x => x * f₃ x) hxf₃Int
    have hsin := hsinInt f₃ hf₃Int
    have h :=
      ((hxbase.add hxcos).const_mul b).sub (hsin.const_mul 3)
    apply h.congr
    filter_upwards with x
    dsimp only [f₃, k₀, thirdOrderSineKernel, Pi.mul_apply]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    ring
  have hboundedMulZero :
      ∀ (φ g : ℝ → ℝ),
        (∀ x, |φ x| ≤ 1) →
        Tendsto g atTop (𝓝 0) →
        Tendsto (fun x => φ x * g x) atTop (𝓝 0) := by
    intro φ g hφ hg
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ᶠ x : ℝ in atTop,
        ‖φ x * g x‖ ≤ ‖g x‖ :=
      Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (by simpa [Real.norm_eq_abs] using hφ x)
    exact squeeze_zero'
      (Eventually.of_forall fun x => norm_nonneg _) hle
      (by simpa using hg.norm)
  have hsinZero (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0)) :
      Tendsto (fun x => Real.sin (b * x) * g x)
        atTop (𝓝 0) :=
    hboundedMulZero _ _ (fun x => abs_sin_le_one _) hg
  have hcosZero (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0)) :
      Tendsto (fun x => Real.cos (b * x) * g x)
        atTop (𝓝 0) :=
    hboundedMulZero _ _ (fun x => abs_cos_le_one _) hg
  have hf₀Zero : Tendsto f₀ atTop (𝓝 0) := by
    simpa only [f₀] using
      tendsto_thetaCuspTiltedWardDensity_atTop_zero ha1 hn0
  have hxf₀Zero : Tendsto (fun x => x * f₀ x) atTop (𝓝 0) := by
    simpa only [f₀] using
      tendsto_id_mul_thetaCuspTiltedWardDensity_atTop_zero ha1 hn0
  have hf₁Zero : Tendsto f₁ atTop (𝓝 0) := by
    simpa only [f₁] using
      tendsto_thetaCuspTiltedWardDensityDerivative_atTop_zero ha1 hn0
  have hxf₁Zero : Tendsto (fun x => x * f₁ x) atTop (𝓝 0) := by
    simpa only [f₁] using
      tendsto_id_mul_thetaCuspTiltedWardDensityDerivative_atTop_zero
        ha1 hn0
  have hf₂Zero : Tendsto f₂ atTop (𝓝 0) := by
    simpa only [f₂] using
      tendsto_thetaCuspTiltedWardDensitySecondDerivative_atTop_zero
        ha1 hn0
  have hxf₂Zero : Tendsto (fun x => x * f₂ x) atTop (𝓝 0) := by
    simpa only [f₂] using
      tendsto_id_mul_thetaCuspTiltedWardDensitySecondDerivative_atTop_zero
        ha1 hn0
  have hf₀k₂Zero : Tendsto (f₀ * k₂) atTop (𝓝 0) := by
    have h :=
      ((hsinZero f₀ hf₀Zero).sub
        ((hcosZero (fun x => x * f₀ x) hxf₀Zero).const_mul b)).const_mul
          (b ^ 2)
    simpa only [mul_zero, sub_zero] using
      h.congr' (Eventually.of_forall fun x => by
        dsimp only [f₀, k₂, thirdOrderSineKernelSecondDerivative,
          Pi.mul_apply]
        ring)
  have hf₁k₁Zero : Tendsto (f₁ * k₁) atTop (𝓝 0) := by
    have h :=
      (((hf₁Zero.const_mul 2).sub
        ((hcosZero f₁ hf₁Zero).const_mul 2)).sub
          ((hsinZero (fun x => x * f₁ x) hxf₁Zero).const_mul b)).const_mul b
    simpa only [mul_zero, sub_zero, zero_mul] using
      h.congr' (Eventually.of_forall fun x => by
        dsimp only [f₁, k₁, thirdOrderSineKernelFirstDerivative,
          Pi.mul_apply]
        ring)
  have hf₂k₀Zero : Tendsto (f₂ * k₀) atTop (𝓝 0) := by
    have h :=
      ((((hxf₂Zero.const_mul 2).add
        (hcosZero (fun x => x * f₂ x) hxf₂Zero)).const_mul b).sub
          ((hsinZero f₂ hf₂Zero).const_mul 3))
    simpa only [mul_zero, add_zero, sub_zero, zero_mul] using
      h.congr' (Eventually.of_forall fun x => by
        dsimp only [f₂, k₀, thirdOrderSineKernel, Pi.mul_apply]
        ring)
  have hf₀k₂Right : Tendsto (f₀ * k₂) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (f₀ * k₂) := by
      exact
        (continuous_iff_continuousAt.mpr fun x => (hf₀ x).continuousAt).mul
          (continuous_iff_continuousAt.mpr fun x => (hk₂ x).continuousAt)
    simpa [f₀, k₂, thirdOrderSineKernelSecondDerivative] using
      (hcont.continuousAt :
        Tendsto (f₀ * k₂) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hf₁k₁Right : Tendsto (f₁ * k₁) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (f₁ * k₁) := by
      exact
        (continuous_iff_continuousAt.mpr fun x => (hf₁ x).continuousAt).mul
          (continuous_iff_continuousAt.mpr fun x => (hk₁ x).continuousAt)
    simpa [f₁, k₁, thirdOrderSineKernelFirstDerivative] using
      (hcont.continuousAt :
        Tendsto (f₁ * k₁) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hf₂k₀Right : Tendsto (f₂ * k₀) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (f₂ * k₀) := by
      exact
        (continuous_iff_continuousAt.mpr fun x => (hf₂ x).continuousAt).mul
          (continuous_iff_continuousAt.mpr fun x => (hk₀ x).continuousAt)
    simpa [f₂, k₀, thirdOrderSineKernel] using
      (hcont.continuousAt :
        Tendsto (f₂ * k₀) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hibp₀ := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := f₀) (u' := f₁)
    (v := k₂) (v' := k₃)
    (fun x _ => hf₀ x) (fun x _ => hk₂ x)
    hf₀k₃ hf₁k₂ hf₀k₂Right hf₀k₂Zero
  have hibp₁ := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := f₁) (u' := f₂)
    (v := k₁) (v' := k₂)
    (fun x _ => hf₁ x) (fun x _ => hk₁ x)
    hf₁k₂ hf₂k₁ hf₁k₁Right hf₁k₁Zero
  have hibp₂ := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := f₂) (u' := f₃)
    (v := k₀) (v' := k₁)
    (fun x _ => hf₂ x) (fun x _ => hk₀ x)
    hf₂k₁ hf₃k₀ hf₂k₀Right hf₂k₀Zero
  have hidentity :
      b ^ 4 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) =
        -∫ x : ℝ in Ioi 0, f₃ x * k₀ x := by
    have hchain :
        (∫ x : ℝ in Ioi 0, f₀ x * k₃ x) =
          -∫ x : ℝ in Ioi 0, f₃ x * k₀ x := by
      calc
        (∫ x : ℝ in Ioi 0, f₀ x * k₃ x) =
            -∫ x : ℝ in Ioi 0, f₁ x * k₂ x := by
          simpa using hibp₀
        _ = ∫ x : ℝ in Ioi 0, f₂ x * k₁ x := by
          have h : (∫ x : ℝ in Ioi 0, f₁ x * k₂ x) =
              -∫ x : ℝ in Ioi 0, f₂ x * k₁ x := by
            simpa using hibp₁
          rw [h]
          ring
        _ = -∫ x : ℝ in Ioi 0, f₃ x * k₀ x := by
          simpa using hibp₂
    rw [show
        (fun x : ℝ => f₀ x * k₃ x) =
          fun x => b ^ 4 *
            (x * thetaCuspTiltedWardDensity a n x *
              Real.sin (b * x)) by
        funext x
        dsimp only [f₀, k₃]
        ring,
      integral_const_mul] at hchain
    exact hchain
  simpa only [f₃, k₀] using hidentity

/-- The all-shell third-order kernel integrand is absolutely integrable. -/
theorem integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
    {a b : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x : ℝ =>
        (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x) *
            thirdOrderSineKernel (b * x)) (Ioi 0) := by
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  have hf₃Int : IntegrableOn f₃ (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_thetaCuspTiltedWardDensityThirdDerivative ha hn
  have hxf₃Int : IntegrableOn (fun x => x * f₃ x) (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative ha hn
  have hsin : IntegrableOn
      (fun x => Real.sin (b * x) * f₃ x) (Ioi 0) := by
    apply Integrable.bdd_mul hf₃Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hcos : IntegrableOn
      (fun x => Real.cos (b * x) * (x * f₃ x)) (Ioi 0) := by
    apply Integrable.bdd_mul hxf₃Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hInt :=
    (((hxf₃Int.const_mul 2).add hcos).const_mul b).sub
      (hsin.const_mul 3)
  apply hInt.congr
  filter_upwards with x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  dsimp only [f₃, thirdOrderSineKernel]
  ring

/-- **Third-order sine-transform positivity.** Every higher tilted Ward shell has a strictly
positive first sine moment at every positive frequency. -/
theorem integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 2 ≤ n) :
    0 < ∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x) := by
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  let k₀ : ℝ → ℝ := fun x => thirdOrderSineKernel (b * x)
  let h : ℝ → ℝ := fun x => -(f₃ x * k₀ x)
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hf₃Int : IntegrableOn f₃ (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_thetaCuspTiltedWardDensityThirdDerivative
        (by linarith) hn0
  have hxf₃Int : IntegrableOn (fun x => x * f₃ x) (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative
        (by linarith) hn0
  have hsinInt :
      IntegrableOn
        (fun x => Real.sin (b * x) * f₃ x) (Ioi 0) := by
    apply Integrable.bdd_mul hf₃Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hcosInt :
      IntegrableOn
        (fun x => Real.cos (b * x) * (x * f₃ x)) (Ioi 0) := by
    apply Integrable.bdd_mul hxf₃Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hf₃k₀ : IntegrableOn (f₃ * k₀) (Ioi 0) := by
    have hbase := hxf₃Int.const_mul 2
    have hcos := hcosInt
    have hsin := hsinInt
    have hInt :=
      ((hbase.add hcos).const_mul b).sub (hsin.const_mul 3)
    apply hInt.congr
    filter_upwards with x
    dsimp only [f₃, k₀, thirdOrderSineKernel, Pi.mul_apply]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    ring
  have hhInt : IntegrableOn h (Ioi 0) := by
    exact hf₃k₀.neg.congr
      (Eventually.of_forall fun x => by
        dsimp only [h, Pi.neg_apply, Pi.mul_apply])
  have hhnn : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hfneg : f₃ x < 0 := by
      dsimp only [f₃]
      exact mul_neg_of_neg_of_pos
        (thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_two_le
          ha hn hx.le)
        (thetaCuspTiltedWardDensity_pos a hn0 x)
    have hkpos : 0 < k₀ x := by
      dsimp only [k₀]
      exact thirdOrderSineKernel_pos (mul_pos hb hx)
    dsimp only [h]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      hfneg.le hkpos.le)
  have hhpos : 0 < ∫ x : ℝ in Ioi 0, h x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hhnn hhInt).2
    have hhcont : Continuous h := by
      have hf₃cont : Continuous f₃ := by
        dsimp only [f₃]
        unfold thetaCuspTiltedWardThirdDerivativeCoefficient
          thetaCuspTiltedWardScore thetaCuspTiltedWardDensity
          thetaCuspWardGibbsAtom thetaCuspPolynomialAtom
        fun_prop
      have hk₀cont : Continuous k₀ := by
        dsimp only [k₀]
        unfold thirdOrderSineKernel
        fun_prop
      exact (hf₃cont.mul hk₀cont).neg
    have hopen :
        IsOpen (Function.support h ∩ Ioi (0 : ℝ)) :=
      hhcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change h 1 ≠ 0
    have hfneg : f₃ 1 < 0 := by
      dsimp only [f₃]
      exact mul_neg_of_neg_of_pos
        (thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_two_le
          ha hn (by norm_num))
        (thetaCuspTiltedWardDensity_pos a hn0 1)
    have hkpos : 0 < k₀ 1 := by
      dsimp only [k₀]
      exact thirdOrderSineKernel_pos (by simpa using hb)
    dsimp only [h]
    exact ne_of_gt (neg_pos.mpr (mul_neg_of_neg_of_pos hfneg hkpos))
  have hidentity :=
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
      (a := a) (b := b) (n := n) (by linarith) hn0
  have hposScaled :
      0 < b ^ 4 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) := by
    rw [hidentity]
    simpa only [f₃, k₀, h, integral_neg] using hhpos
  exact pos_of_mul_pos_right hposScaled (pow_nonneg hb.le 4)

/-- Every positive shell has a strictly positive third-order contribution after `x = 1/2`.
Thus the only possible ground-shell failure of the third-order proof is compact. -/
theorem integral_Ioi_half_neg_thetaCuspTiltedWardThirdDerivative_mul_kernel_pos
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 0 < n) :
    0 < ∫ x : ℝ in Ioi (1 / 2),
      -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x) *
            thirdOrderSineKernel (b * x)) := by
  let h : ℝ → ℝ := fun x =>
    -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x) *
          thirdOrderSineKernel (b * x))
  have hhInt0 : IntegrableOn h (Ioi 0) := by
    exact
      (integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
        (a := a) (b := b) (n := n) (by linarith) hn).neg.congr
        (Eventually.of_forall fun x => by
          dsimp only [h, Pi.neg_apply])
  have hhInt : IntegrableOn h (Ioi (1 / 2)) :=
    hhInt0.mono_set (Ioi_subset_Ioi (by norm_num))
  have hhnn : ∀ᵐ x ∂(volume.restrict (Ioi (1 / 2))),
      0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hcoeff :
        thetaCuspTiltedWardThirdDerivativeCoefficient a n x < 0 :=
      thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_pos_of_half_le
        ha hn hx.le
    have hdensity : 0 < thetaCuspTiltedWardDensity a n x :=
      thetaCuspTiltedWardDensity_pos a hn x
    have hkernel : 0 < thirdOrderSineKernel (b * x) :=
      thirdOrderSineKernel_pos (mul_pos hb (lt_trans (by norm_num) hx))
    dsimp only [h]
    exact neg_nonneg.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoeff.le hdensity.le)
        hkernel.le)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hhnn hhInt).2
  have hhcont : Continuous h := by
    dsimp only [h]
    unfold thetaCuspTiltedWardThirdDerivativeCoefficient
      thetaCuspTiltedWardScore thetaCuspTiltedWardDensity
      thetaCuspWardGibbsAtom thetaCuspPolynomialAtom
      thirdOrderSineKernel
    fun_prop
  have hopen :
      IsOpen (Function.support h ∩ Ioi (1 / 2)) :=
    hhcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change h 1 ≠ 0
  have hcoeff :
      thetaCuspTiltedWardThirdDerivativeCoefficient a n 1 < 0 :=
    thetaCuspTiltedWardThirdDerivativeCoefficient_neg_of_pos_of_half_le
      ha hn (by norm_num)
  have hdensity : 0 < thetaCuspTiltedWardDensity a n 1 :=
    thetaCuspTiltedWardDensity_pos a hn 1
  have hkernel : 0 < thirdOrderSineKernel (b * 1) :=
    thirdOrderSineKernel_pos (by simpa using hb)
  dsimp only [h]
  exact ne_of_gt
    (neg_pos.mpr (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hcoeff hdensity) hkernel))

/-- Exact third-order compact-defect split.  The second term is strictly positive at positive
frequency; the first term is the complete ground-shell obstruction. -/
theorem thetaCuspTiltedWardThirdOrder_compact_defect_split
    {a b : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) :
    b ^ 4 * (∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) =
      (∫ x : ℝ in Ioc 0 (1 / 2),
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
            thetaCuspTiltedWardDensity a n x) *
              thirdOrderSineKernel (b * x))) +
      ∫ x : ℝ in Ioi (1 / 2),
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
            thetaCuspTiltedWardDensity a n x) *
              thirdOrderSineKernel (b * x)) := by
  let h : ℝ → ℝ := fun x =>
    -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x) *
          thirdOrderSineKernel (b * x))
  have hhInt : IntegrableOn h (Ioi 0) := by
    exact
      (integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
        (a := a) (b := b) (n := n) ha hn).neg.congr
        (Eventually.of_forall fun x => by
          dsimp only [h, Pi.neg_apply])
  rw [
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
      ha hn]
  rw [show
      (fun x : ℝ =>
        thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x *
            thirdOrderSineKernel (b * x)) =
      fun x => -h x by
        funext x
        dsimp only [h]
        ring,
    integral_neg, neg_neg]
  change (∫ x : ℝ in Ioi 0, h x) =
    (∫ x : ℝ in Ioc 0 (1 / 2), h x) +
      ∫ x : ℝ in Ioi (1 / 2), h x
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 2),
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
  · exact hhInt.mono_set Ioc_subset_Ioi_self
  · exact hhInt.mono_set (Ioi_subset_Ioi (by norm_num))

/-- Exact third-order split at an arbitrary positive cut point. -/
theorem thetaCuspTiltedWardThirdOrder_split_at
    {a b tau : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) (htau : 0 < tau) :
    b ^ 4 * (∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) =
      (∫ x : ℝ in Ioc 0 tau,
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
            thetaCuspTiltedWardDensity a n x) *
              thirdOrderSineKernel (b * x))) +
      ∫ x : ℝ in Ioi tau,
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
            thetaCuspTiltedWardDensity a n x) *
              thirdOrderSineKernel (b * x)) := by
  let h : ℝ → ℝ := fun x =>
    -((thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x) *
          thirdOrderSineKernel (b * x))
  have hhInt : IntegrableOn h (Ioi 0) := by
    exact
      (integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
        (a := a) (b := b) (n := n) ha hn).neg.congr
        (Eventually.of_forall fun x => by
          dsimp only [h, Pi.neg_apply])
  rw [
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
      ha hn]
  rw [show
      (fun x : ℝ =>
        thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
          thetaCuspTiltedWardDensity a n x *
            thirdOrderSineKernel (b * x)) =
      fun x => -h x by
        funext x
        dsimp only [h]
        ring,
    integral_neg, neg_neg]
  change (∫ x : ℝ in Ioi 0, h x) =
    (∫ x : ℝ in Ioc 0 tau, h x) +
      ∫ x : ℝ in Ioi tau, h x
  rw [← Set.Ioc_union_Ioi_eq_Ioi htau.le,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
  · exact hhInt.mono_set Ioc_subset_Ioi_self
  · exact hhInt.mono_set (Ioi_subset_Ioi htau.le)

/-- Before the unique ground-shell transition, the third-order contribution is strictly
negative at every positive frequency. -/
theorem integral_Ioc_ground_transition_neg_thetaCuspTiltedWardThirdDerivative_mul_kernel_neg
    {a b tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hb : 0 < b)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    (∫ x : ℝ in Ioc 0 tau,
      -((thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
          thetaCuspTiltedWardDensity a 1 x) *
            thirdOrderSineKernel (b * x))) < 0 := by
  let g : ℝ → ℝ := fun x =>
    (thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
      thetaCuspTiltedWardDensity a 1 x) *
        thirdOrderSineKernel (b * x)
  have hgInt0 : IntegrableOn g (Ioi 0) := by
    simpa only [g] using
      integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
        (a := a) (b := b) (n := 1) (by linarith) (by norm_num)
  have hgInterval : IntervalIntegrable g volume 0 tau := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htau.1.le]
    exact hgInt0.mono_set Ioc_subset_Ioi_self
  have hsign :=
    thetaCuspTiltedWardThirdDerivativeCoefficient_ground_sign_around_zero
      ha0 ha htau htauZero
  have hgpos :
      ∀ x : ℝ, x ∈ Ioo 0 tau → 0 < g x := by
    intro x hx
    have hcoeff :
        0 < thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x :=
      hsign.1 hx.1.le hx.2
    have hdensity : 0 < thetaCuspTiltedWardDensity a 1 x :=
      thetaCuspTiltedWardDensity_pos a (by norm_num) x
    have hkernel : 0 < thirdOrderSineKernel (b * x) :=
      thirdOrderSineKernel_pos (mul_pos hb hx.1)
    dsimp only [g]
    positivity
  have hgIntegral :
      0 < ∫ x : ℝ in Ioc 0 tau, g x := by
    rw [← intervalIntegral.integral_of_le htau.1.le]
    exact
      intervalIntegral.intervalIntegral_pos_of_pos_on
        hgInterval hgpos htau.1
  rw [show
      (fun x : ℝ =>
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
            thetaCuspTiltedWardDensity a 1 x) *
              thirdOrderSineKernel (b * x))) =
        fun x => -g x by
          funext x
          rfl,
    integral_neg]
  exact neg_lt_zero.mpr hgIntegral

/-- After the unique ground-shell transition, the third-order contribution is strictly
positive at every positive frequency. -/
theorem integral_Ioi_ground_transition_neg_thetaCuspTiltedWardThirdDerivative_mul_kernel_pos
    {a b tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hb : 0 < b)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    0 < ∫ x : ℝ in Ioi tau,
      -((thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
          thetaCuspTiltedWardDensity a 1 x) *
            thirdOrderSineKernel (b * x)) := by
  let h : ℝ → ℝ := fun x =>
    -((thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
        thetaCuspTiltedWardDensity a 1 x) *
          thirdOrderSineKernel (b * x))
  have hhInt0 : IntegrableOn h (Ioi 0) := by
    exact
      (integrableOn_thetaCuspTiltedWardThirdDerivative_mul_thirdOrderSineKernel
        (a := a) (b := b) (n := 1) (by linarith) (by norm_num)).neg.congr
        (Eventually.of_forall fun x => by
          dsimp only [h, Pi.neg_apply])
  have hhInt : IntegrableOn h (Ioi tau) :=
    hhInt0.mono_set (Ioi_subset_Ioi htau.1.le)
  have hsign :=
    thetaCuspTiltedWardThirdDerivativeCoefficient_ground_sign_around_zero
      ha0 ha htau htauZero
  have hhnn : ∀ᵐ x ∂(volume.restrict (Ioi tau)),
      0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hcoeff :
        thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x < 0 :=
      hsign.2 hx
    have hdensity : 0 < thetaCuspTiltedWardDensity a 1 x :=
      thetaCuspTiltedWardDensity_pos a (by norm_num) x
    have hx0 : 0 < x := lt_trans htau.1 hx
    have hkernel : 0 < thirdOrderSineKernel (b * x) :=
      thirdOrderSineKernel_pos (mul_pos hb hx0)
    dsimp only [h]
    exact neg_nonneg.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoeff.le hdensity.le)
        hkernel.le)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hhnn hhInt).2
  have hhcont : Continuous h := by
    dsimp only [h]
    unfold thetaCuspTiltedWardThirdDerivativeCoefficient
      thetaCuspTiltedWardScore thetaCuspTiltedWardDensity
      thetaCuspWardGibbsAtom thetaCuspPolynomialAtom
      thirdOrderSineKernel
    fun_prop
  have hopen :
      IsOpen (Function.support h ∩ Ioi tau) :=
    hhcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨tau + 1, ?_, by norm_num⟩
  change h (tau + 1) ≠ 0
  have hcoeff :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 (tau + 1) < 0 :=
    hsign.2 (by linarith)
  have hdensity :
      0 < thetaCuspTiltedWardDensity a 1 (tau + 1) :=
    thetaCuspTiltedWardDensity_pos a (by norm_num) (tau + 1)
  have hkernel :
      0 < thirdOrderSineKernel (b * (tau + 1)) :=
    thirdOrderSineKernel_pos
      (mul_pos hb (by linarith [htau.1]))
  dsimp only [h]
  exact ne_of_gt
    (neg_pos.mpr (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos hcoeff hdensity) hkernel))

/-- The ground shell has exactly one signed third-order defect: one negative compact head and
one positive cofinal tail, separated at a unique point in `(0,1/2)`. -/
theorem existsUnique_thetaCuspTiltedWard_ground_thirdOrder_signed_split
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hb : 0 < b) :
    ∃! tau : ℝ,
      tau ∈ Ioo 0 (1 / 2) ∧
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0 ∧
      (∫ x : ℝ in Ioc 0 tau,
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
            thetaCuspTiltedWardDensity a 1 x) *
              thirdOrderSineKernel (b * x))) < 0 ∧
      0 < ∫ x : ℝ in Ioi tau,
        -((thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
            thetaCuspTiltedWardDensity a 1 x) *
              thirdOrderSineKernel (b * x)) := by
  rcases
      existsUnique_thetaCuspTiltedWardThirdDerivativeCoefficient_ground_zero
        ha0 ha with ⟨tau, ⟨htau, htauZero⟩, htauUnique⟩
  refine ⟨tau, ?_, ?_⟩
  · exact
      ⟨htau, htauZero,
        integral_Ioc_ground_transition_neg_thetaCuspTiltedWardThirdDerivative_mul_kernel_neg
          ha0 ha hb htau htauZero,
        integral_Ioi_ground_transition_neg_thetaCuspTiltedWardThirdDerivative_mul_kernel_pos
          ha0 ha hb htau htauZero⟩
  · intro y hy
    exact htauUnique y ⟨hy.1, hy.2.1⟩

/-- Exact cofinal mass of the tilted Ward second derivative. -/
theorem integral_Ioi_thetaCuspTiltedWardDensitySecondDerivative_eq
    {a tau : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) (htau : 0 ≤ tau) :
    (∫ x : ℝ in Ioi tau,
      thetaCuspTiltedWardCurvature a n x *
        thetaCuspTiltedWardDensity a n x) =
      -(thetaCuspTiltedWardScore a n tau *
        thetaCuspTiltedWardDensity a n tau) := by
  let f₁ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x
  let f₂ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardCurvature a n x *
      thetaCuspTiltedWardDensity a n x
  have hf₁ (x : ℝ) : HasDerivAt f₁ (f₂ x) x := by
    simpa only [f₁, f₂] using
      hasDerivAt_thetaCuspTiltedWardDensityDerivative a n x
  have hf₂Int : IntegrableOn f₂ (Ioi tau) := by
    exact
      (show IntegrableOn f₂ (Ioi 0) by
        simpa only [f₂] using
          integrableOn_thetaCuspTiltedWardDensitySecondDerivative ha hn).mono_set
        (Ioi_subset_Ioi htau)
  have hf₁Zero : Tendsto f₁ atTop (𝓝 0) := by
    simpa only [f₁] using
      tendsto_thetaCuspTiltedWardDensityDerivative_atTop_zero ha hn
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f := f₁) (f' := f₂) (a := tau) (m := 0)
      (hf₁ tau).continuousAt.continuousWithinAt
      (fun x _ => hf₁ x) hf₂Int hf₁Zero
  simpa only [f₁, f₂, zero_sub] using h

/-- Exact cofinal mass of the tilted Ward third derivative. -/
theorem integral_Ioi_thetaCuspTiltedWardDensityThirdDerivative_eq
    {a tau : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) (htau : 0 ≤ tau) :
    (∫ x : ℝ in Ioi tau,
      thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x) =
      -(thetaCuspTiltedWardCurvature a n tau *
        thetaCuspTiltedWardDensity a n tau) := by
  let f₂ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardCurvature a n x *
      thetaCuspTiltedWardDensity a n x
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  have hf₂ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    simpa only [f₂, f₃] using
      hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative a n x
  have hf₃Int : IntegrableOn f₃ (Ioi tau) := by
    exact
      (show IntegrableOn f₃ (Ioi 0) by
        simpa only [f₃] using
          integrableOn_thetaCuspTiltedWardDensityThirdDerivative ha hn).mono_set
        (Ioi_subset_Ioi htau)
  have hf₂Zero : Tendsto f₂ atTop (𝓝 0) := by
    simpa only [f₂] using
      tendsto_thetaCuspTiltedWardDensitySecondDerivative_atTop_zero ha hn
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f := f₂) (f' := f₃) (a := tau) (m := 0)
      (hf₂ tau).continuousAt.continuousWithinAt
      (fun x _ => hf₂ x) hf₃Int hf₂Zero
  simpa only [f₂, f₃, zero_sub] using h

/-- Exact cofinal first moment of the tilted Ward third derivative. -/
theorem integral_Ioi_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
    {a tau : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) (htau : 0 ≤ tau) :
    (∫ x : ℝ in Ioi tau,
      x * (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x)) =
      -(tau *
          (thetaCuspTiltedWardCurvature a n tau *
            thetaCuspTiltedWardDensity a n tau)) +
        thetaCuspTiltedWardScore a n tau *
          thetaCuspTiltedWardDensity a n tau := by
  let f₁ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x
  let f₂ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardCurvature a n x *
      thetaCuspTiltedWardDensity a n x
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  let F : ℝ → ℝ := fun x => x * f₂ x
  let F' : ℝ → ℝ := fun x => f₂ x + x * f₃ x
  have hf₂ (x : ℝ) : HasDerivAt f₂ (f₃ x) x := by
    simpa only [f₂, f₃] using
      hasDerivAt_thetaCuspTiltedWardDensitySecondDerivative a n x
  have hF (x : ℝ) : HasDerivAt F (F' x) x := by
    simpa only [F, F', one_mul, id_eq, mul_comm] using
      (hasDerivAt_id x).mul (hf₂ x)
  have hf₂Int : IntegrableOn f₂ (Ioi tau) := by
    exact
      (show IntegrableOn f₂ (Ioi 0) by
        simpa only [f₂] using
          integrableOn_thetaCuspTiltedWardDensitySecondDerivative ha hn).mono_set
        (Ioi_subset_Ioi htau)
  have hxf₃Int :
      IntegrableOn (fun x => x * f₃ x) (Ioi tau) := by
    exact
      (show IntegrableOn (fun x => x * f₃ x) (Ioi 0) by
        simpa only [f₃] using
          integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative
            ha hn).mono_set
        (Ioi_subset_Ioi htau)
  have hF'Int : IntegrableOn F' (Ioi tau) := by
    exact hf₂Int.add hxf₃Int
  have hFZero : Tendsto F atTop (𝓝 0) := by
    simpa only [F, f₂] using
      tendsto_id_mul_thetaCuspTiltedWardDensitySecondDerivative_atTop_zero
        ha hn
  have hfundamental :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f := F) (f' := F') (a := tau) (m := 0)
      (hF tau).continuousAt.continuousWithinAt
      (fun x _ => hF x) hF'Int hFZero
  have hf₂Value :=
    integral_Ioi_thetaCuspTiltedWardDensitySecondDerivative_eq
      (a := a) (tau := tau) (n := n) ha hn htau
  have hsplit :
      (∫ x : ℝ in Ioi tau, F' x) =
        (∫ x : ℝ in Ioi tau, f₂ x) +
          ∫ x : ℝ in Ioi tau, x * f₃ x := by
    exact integral_add hf₂Int hxf₃Int
  rw [hsplit] at hfundamental
  simp only [F, F', f₁, f₂, f₃, zero_sub] at hfundamental hf₂Value ⊢
  linarith

/-- Exact compact mass before a positive cut point. -/
theorem integral_Ioc_thetaCuspTiltedWardDensityThirdDerivative_eq
    {a tau : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) (htau : 0 < tau) :
    (∫ x : ℝ in Ioc 0 tau,
      thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x) =
      thetaCuspTiltedWardCurvature a n tau *
          thetaCuspTiltedWardDensity a n tau -
        thetaCuspTiltedWardCurvature a n 0 *
          thetaCuspTiltedWardDensity a n 0 := by
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  have hf₃Int : IntegrableOn f₃ (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_thetaCuspTiltedWardDensityThirdDerivative ha hn
  have hsplit :
      (∫ x : ℝ in Ioi 0, f₃ x) =
        (∫ x : ℝ in Ioc 0 tau, f₃ x) +
          ∫ x : ℝ in Ioi tau, f₃ x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi htau.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hf₃Int.mono_set Ioc_subset_Ioi_self
    · exact hf₃Int.mono_set (Ioi_subset_Ioi htau.le)
  have htotal :=
    integral_Ioi_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := 0) (n := n) ha hn (by norm_num)
  have htail :=
    integral_Ioi_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := tau) (n := n) ha hn htau.le
  simp only [f₃] at hsplit
  linarith

/-- Exact compact first moment before a positive cut point. -/
theorem integral_Ioc_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
    {a tau : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) (htau : 0 < tau) :
    (∫ x : ℝ in Ioc 0 tau,
      x * (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
        thetaCuspTiltedWardDensity a n x)) =
      thetaCuspTiltedWardScore a n 0 *
          thetaCuspTiltedWardDensity a n 0 +
        tau *
          (thetaCuspTiltedWardCurvature a n tau *
            thetaCuspTiltedWardDensity a n tau) -
        thetaCuspTiltedWardScore a n tau *
          thetaCuspTiltedWardDensity a n tau := by
  let xf₃ : ℝ → ℝ := fun x =>
    x * (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x)
  have hxf₃Int : IntegrableOn xf₃ (Ioi 0) := by
    simpa only [xf₃] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative ha hn
  have hsplit :
      (∫ x : ℝ in Ioi 0, xf₃ x) =
        (∫ x : ℝ in Ioc 0 tau, xf₃ x) +
          ∫ x : ℝ in Ioi tau, xf₃ x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi htau.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hxf₃Int.mono_set Ioc_subset_Ioi_self
    · exact hxf₃Int.mono_set (Ioi_subset_Ioi htau.le)
  have htotal :=
    integral_Ioi_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := 0) (n := n) ha hn (by norm_num)
  have htail :=
    integral_Ioi_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := tau) (n := n) ha hn htau.le
  simp only [xf₃] at hsplit
  norm_num at htotal
  linarith

/-- Exact total variation of the ground third derivative, expressed only through boundary data
at its unique sign transition. -/
theorem integral_Ioi_abs_ground_thetaCuspTiltedWardDensityThirdDerivative_eq
    {a tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    (∫ x : ℝ in Ioi 0,
      |thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
        thetaCuspTiltedWardDensity a 1 x|) =
      2 * (thetaCuspTiltedWardCurvature a 1 tau *
          thetaCuspTiltedWardDensity a 1 tau) -
        thetaCuspTiltedWardCurvature a 1 0 *
          thetaCuspTiltedWardDensity a 1 0 := by
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
      thetaCuspTiltedWardDensity a 1 x
  have hf₃Int : IntegrableOn f₃ (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_thetaCuspTiltedWardDensityThirdDerivative
        (a := a) (n := 1) (by linarith) (by norm_num)
  have habsInt : IntegrableOn (fun x => |f₃ x|) (Ioi 0) :=
    hf₃Int.abs
  have hsplit :
      (∫ x : ℝ in Ioi 0, |f₃ x|) =
        (∫ x : ℝ in Ioc 0 tau, |f₃ x|) +
          ∫ x : ℝ in Ioi tau, |f₃ x| := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi htau.1.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact habsInt.mono_set Ioc_subset_Ioi_self
    · exact habsInt.mono_set (Ioi_subset_Ioi htau.1.le)
  have hsign :=
    thetaCuspTiltedWardThirdDerivativeCoefficient_ground_sign_around_zero
      ha0 ha htau htauZero
  have hhead :
      (∫ x : ℝ in Ioc 0 tau, |f₃ x|) =
        ∫ x : ℝ in Ioc 0 tau, f₃ x := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    rcases eq_or_lt_of_le hx.2 with hxtau | hxtau
    · subst x
      simp only [f₃, htauZero, zero_mul, abs_zero]
    · have hcoeff :
          0 < thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x :=
        hsign.1 hx.1.le hxtau
      have hdensity : 0 < thetaCuspTiltedWardDensity a 1 x :=
        thetaCuspTiltedWardDensity_pos a (by norm_num) x
      exact abs_of_pos (mul_pos hcoeff hdensity)
  have htail :
      (∫ x : ℝ in Ioi tau, |f₃ x|) =
        -(∫ x : ℝ in Ioi tau, f₃ x) := by
    rw [← integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hcoeff :
        thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x < 0 :=
      hsign.2 hx
    have hdensity : 0 < thetaCuspTiltedWardDensity a 1 x :=
      thetaCuspTiltedWardDensity_pos a (by norm_num) x
    exact abs_of_neg (mul_neg_of_neg_of_pos hcoeff hdensity)
  have hheadValue :=
    integral_Ioc_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := tau) (n := 1)
      (by linarith) (by norm_num) htau.1
  have htailValue :=
    integral_Ioi_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := tau) (n := 1)
      (by linarith) (by norm_num) htau.1.le
  simp only [f₃] at hsplit hhead htail
  rw [hhead, htail] at hsplit
  linarith

/-- Exact first absolute moment of the ground third derivative, again reduced to transition-point
boundary data. -/
theorem integral_Ioi_id_mul_abs_ground_thetaCuspTiltedWardDensityThirdDerivative_eq
    {a tau : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (htau : tau ∈ Ioo 0 (1 / 2))
    (htauZero :
      thetaCuspTiltedWardThirdDerivativeCoefficient a 1 tau = 0) :
    (∫ x : ℝ in Ioi 0,
      x * |thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
        thetaCuspTiltedWardDensity a 1 x|) =
      thetaCuspTiltedWardScore a 1 0 *
          thetaCuspTiltedWardDensity a 1 0 +
        2 * tau *
          (thetaCuspTiltedWardCurvature a 1 tau *
            thetaCuspTiltedWardDensity a 1 tau) -
        2 * (thetaCuspTiltedWardScore a 1 tau *
          thetaCuspTiltedWardDensity a 1 tau) := by
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
      thetaCuspTiltedWardDensity a 1 x
  let g : ℝ → ℝ := fun x => x * |f₃ x|
  have hxf₃Int :
      IntegrableOn (fun x => x * f₃ x) (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative
        (a := a) (n := 1) (by linarith) (by norm_num)
  have hgInt : IntegrableOn g (Ioi 0) := by
    have habs := hxf₃Int.abs
    apply habs.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [g]
    rw [abs_mul, abs_of_pos hx]
  have hsplit :
      (∫ x : ℝ in Ioi 0, g x) =
        (∫ x : ℝ in Ioc 0 tau, g x) +
          ∫ x : ℝ in Ioi tau, g x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi htau.1.le,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
    · exact hgInt.mono_set Ioc_subset_Ioi_self
    · exact hgInt.mono_set (Ioi_subset_Ioi htau.1.le)
  have hsign :=
    thetaCuspTiltedWardThirdDerivativeCoefficient_ground_sign_around_zero
      ha0 ha htau htauZero
  have hhead :
      (∫ x : ℝ in Ioc 0 tau, g x) =
        ∫ x : ℝ in Ioc 0 tau, x * f₃ x := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only [g]
    rcases eq_or_lt_of_le hx.2 with hxtau | hxtau
    · subst x
      simp only [f₃, htauZero, zero_mul, abs_zero, mul_zero]
    · have hcoeff :
          0 < thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x :=
        hsign.1 hx.1.le hxtau
      have hdensity : 0 < thetaCuspTiltedWardDensity a 1 x :=
        thetaCuspTiltedWardDensity_pos a (by norm_num) x
      rw [abs_of_pos (mul_pos hcoeff hdensity)]
  have htail :
      (∫ x : ℝ in Ioi tau, g x) =
        -(∫ x : ℝ in Ioi tau, x * f₃ x) := by
    rw [← integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [g]
    have hcoeff :
        thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x < 0 :=
      hsign.2 hx
    have hdensity : 0 < thetaCuspTiltedWardDensity a 1 x :=
      thetaCuspTiltedWardDensity_pos a (by norm_num) x
    rw [abs_of_neg (mul_neg_of_neg_of_pos hcoeff hdensity)]
    ring
  have hheadValue :=
    integral_Ioc_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := tau) (n := 1)
      (by linarith) (by norm_num) htau.1
  have htailValue :=
    integral_Ioi_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := tau) (n := 1)
      (by linarith) (by norm_num) htau.1.le
  simp only [g, f₃] at hsplit hhead htail
  rw [hhead, htail] at hsplit
  linarith

/-- **Fourth-order boundary identity.**  The ground-shell high-frequency sign has the exact
boundary main term `-2 b f'(0)`; every remaining oscillation is the sine transform of the
integrable fourth derivative of `x f`. -/
theorem integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_fourthOrderBoundary_identity
    {a b : ℝ} (ha : a < 1)
    {n : ℕ} (hn : 0 < n) :
    b ^ 4 * (∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) =
      -2 * b *
          (thetaCuspTiltedWardScore a n 0 *
            thetaCuspTiltedWardDensity a n 0) +
        ∫ x : ℝ in Ioi 0,
          (4 *
              (thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
                thetaCuspTiltedWardDensity a n x) +
            x * thetaCuspTiltedWardDensityFourthDerivative a n x) *
              Real.sin (b * x) := by
  let f₁ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x
  let f₃ : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardThirdDerivativeCoefficient a n x *
      thetaCuspTiltedWardDensity a n x
  let f₄ : ℝ → ℝ :=
    thetaCuspTiltedWardDensityFourthDerivative a n
  let u : ℝ → ℝ := fun x => x * f₃ x
  let u' : ℝ → ℝ := fun x => f₃ x + x * f₄ x
  let v : ℝ → ℝ := fun x => Real.sin (b * x)
  let v' : ℝ → ℝ := fun x => b * Real.cos (b * x)
  have hf₃ (x : ℝ) : HasDerivAt f₃ (f₄ x) x := by
    simpa only [f₃, f₄] using
      hasDerivAt_thetaCuspTiltedWardDensityThirdDerivative a n x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    simpa only [u, u', one_mul, id_eq, mul_comm] using
      (hasDerivAt_id x).mul (hf₃ x)
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp only [v, v']
    convert (Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1 <;>
      (try simp only [Function.comp_apply, id_eq]) <;> ring
  have hf₃Int : IntegrableOn f₃ (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_thetaCuspTiltedWardDensityThirdDerivative ha hn
  have hxf₃Int : IntegrableOn (fun x => x * f₃ x) (Ioi 0) := by
    simpa only [f₃] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityThirdDerivative
        ha hn
  have hxf₄Int : IntegrableOn (fun x => x * f₄ x) (Ioi 0) := by
    simpa only [f₄] using
      integrableOn_id_mul_thetaCuspTiltedWardDensityFourthDerivative
        ha hn
  have hsinF₃Int :
      IntegrableOn (fun x => f₃ x * Real.sin (b * x)) (Ioi 0) := by
    apply Integrable.mul_bdd hf₃Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hsinXF₄Int :
      IntegrableOn (fun x => (x * f₄ x) * Real.sin (b * x)) (Ioi 0) := by
    apply Integrable.mul_bdd hxf₄Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hcosXF₃Int :
      IntegrableOn (fun x => (x * f₃ x) * Real.cos (b * x)) (Ioi 0) := by
    apply Integrable.mul_bdd hxf₃Int
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    have h := hcosXF₃Int.const_mul b
    apply h.congr
    filter_upwards with x
    dsimp only [u, v', Pi.mul_apply]
    ring
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have h := hsinF₃Int.add hsinXF₄Int
    apply h.congr
    filter_upwards with x
    dsimp only [u', v, Pi.mul_apply, Pi.add_apply]
    ring
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (u * v) := by
      have hucont : Continuous u := by
        exact continuous_id.mul
          (continuous_iff_continuousAt.mpr fun x => (hf₃ x).continuousAt)
      have hvcont : Continuous v := by
        dsimp only [v]
        fun_prop
      exact hucont.mul hvcont
    have h :
        Tendsto (u * v) (𝓝 (0 : ℝ)) (𝓝 ((u * v) 0)) :=
      hcont.continuousAt
    have h' :
        Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 ((u * v) 0)) :=
      h.mono_left inf_le_left
    simpa [u, v] using h'
  have huZero : Tendsto u atTop (𝓝 0) := by
    simpa only [u, f₃] using
      tendsto_id_mul_thetaCuspTiltedWardDensityThirdDerivative_atTop_zero
        ha hn
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ᶠ x : ℝ in atTop,
        ‖(u * v) x‖ ≤ ‖u x‖ := by
      filter_upwards with x
      rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
      exact
        mul_le_of_le_one_right (abs_nonneg (u x)) (abs_sin_le_one _)
    exact squeeze_zero'
      (Eventually.of_forall fun x => norm_nonneg _) hle
      (by simpa using huZero.norm)
  have hibp :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (u := u) (u' := u')
      (v := v) (v' := v')
      (fun x _ => hu x) (fun x _ => hv x)
      huv' hu'v hzero hinfty
  have huvValue :
      (∫ x : ℝ in Ioi 0,
        (f₃ x + x * f₄ x) * Real.sin (b * x)) =
        (∫ x : ℝ in Ioi 0, f₃ x * Real.sin (b * x)) +
          ∫ x : ℝ in Ioi 0,
            (x * f₄ x) * Real.sin (b * x) := by
    rw [show
        (fun x : ℝ =>
          (f₃ x + x * f₄ x) * Real.sin (b * x)) =
        fun x =>
          f₃ x * Real.sin (b * x) +
            (x * f₄ x) * Real.sin (b * x) by
          funext x
          ring,
      integral_add hsinF₃Int hsinXF₄Int]
  have hibpValue :
      b * (∫ x : ℝ in Ioi 0,
        x * f₃ x * Real.cos (b * x)) =
        -((∫ x : ℝ in Ioi 0,
            f₃ x * Real.sin (b * x)) +
          ∫ x : ℝ in Ioi 0,
            (x * f₄ x) * Real.sin (b * x)) := by
    rw [show
        (fun x : ℝ => u x * v' x) =
          fun x => b * (x * f₃ x * Real.cos (b * x)) by
            funext x
            dsimp only [u, v']
            ring,
      integral_const_mul] at hibp
    rw [huvValue] at hibp
    simpa only [u', v, Pi.mul_apply, neg_zero, zero_sub] using hibp
  have hmoment :=
    integral_Ioi_id_mul_thetaCuspTiltedWardDensityThirdDerivative_eq
      (a := a) (tau := 0) (n := n) ha hn (by norm_num)
  have hmomentValue :
      (∫ x : ℝ in Ioi 0, x * f₃ x) = f₁ 0 := by
    simpa only [f₁, f₃, zero_mul, neg_zero, zero_add] using hmoment
  have hdecomp :
      (∫ x : ℝ in Ioi 0,
        f₃ x * thirdOrderSineKernel (b * x)) =
        2 * b * (∫ x : ℝ in Ioi 0, x * f₃ x) +
          b * (∫ x : ℝ in Ioi 0,
            x * f₃ x * Real.cos (b * x)) -
          3 * (∫ x : ℝ in Ioi 0,
            f₃ x * Real.sin (b * x)) := by
    have hA : IntegrableOn
        (fun x => 2 * b * (x * f₃ x)) (Ioi 0) :=
      hxf₃Int.const_mul (2 * b)
    have hB : IntegrableOn
        (fun x => b * (x * f₃ x * Real.cos (b * x))) (Ioi 0) :=
      hcosXF₃Int.const_mul b
    have hC : IntegrableOn
        (fun x => 3 * (f₃ x * Real.sin (b * x))) (Ioi 0) :=
      hsinF₃Int.const_mul 3
    calc
      (∫ x : ℝ in Ioi 0,
          f₃ x * thirdOrderSineKernel (b * x)) =
          ∫ x : ℝ in Ioi 0,
            (2 * b * (x * f₃ x) +
              b * (x * f₃ x * Real.cos (b * x))) -
              3 * (f₃ x * Real.sin (b * x)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _
        unfold thirdOrderSineKernel
        ring
      _ =
          (∫ x : ℝ in Ioi 0,
            2 * b * (x * f₃ x) +
              b * (x * f₃ x * Real.cos (b * x))) -
          ∫ x : ℝ in Ioi 0,
            3 * (f₃ x * Real.sin (b * x)) :=
        integral_sub (hA.add hB) hC
      _ =
          ((∫ x : ℝ in Ioi 0, 2 * b * (x * f₃ x)) +
            ∫ x : ℝ in Ioi 0,
              b * (x * f₃ x * Real.cos (b * x))) -
          ∫ x : ℝ in Ioi 0,
            3 * (f₃ x * Real.sin (b * x)) := by
        rw [integral_add hA hB]
      _ =
          2 * b * (∫ x : ℝ in Ioi 0, x * f₃ x) +
            b * (∫ x : ℝ in Ioi 0,
              x * f₃ x * Real.cos (b * x)) -
            3 * (∫ x : ℝ in Ioi 0,
              f₃ x * Real.sin (b * x)) := by
        rw [integral_const_mul, integral_const_mul,
          integral_const_mul]
  have hremainder :
      (∫ x : ℝ in Ioi 0,
        (4 * f₃ x + x * f₄ x) * Real.sin (b * x)) =
        4 * (∫ x : ℝ in Ioi 0,
          f₃ x * Real.sin (b * x)) +
        ∫ x : ℝ in Ioi 0,
          (x * f₄ x) * Real.sin (b * x) := by
    rw [show
        (fun x : ℝ =>
          (4 * f₃ x + x * f₄ x) * Real.sin (b * x)) =
        fun x =>
          4 * (f₃ x * Real.sin (b * x)) +
            (x * f₄ x) * Real.sin (b * x) by
          funext x
          ring,
      integral_add (hsinF₃Int.const_mul 4) hsinXF₄Int,
      integral_const_mul]
  have hthird :=
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
      (a := a) (b := b) (n := n) ha hn
  simp only [f₁, f₃, f₄] at hmomentValue hdecomp hibpValue hremainder ⊢
  rw [hthird]
  rw [hdecomp, hmomentValue, hibpValue, hremainder]
  ring

/-- Explicit nonoscillatory fourth-order threshold for the exceptional ground shell. -/
noncomputable def thetaCuspGroundFourthOrderThreshold (a : ℝ) : ℝ :=
  (∫ x : ℝ in Ioi 0,
    |4 *
        (thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
          thetaCuspTiltedWardDensity a 1 x) +
      x * thetaCuspTiltedWardDensityFourthDerivative a 1 x|) /
    (-2 *
      (thetaCuspTiltedWardScore a 1 0 *
        thetaCuspTiltedWardDensity a 1 0))

/-- Explicit analytic high-frequency threshold for the exceptional ground shell.  Closing
`B(a) ≤ 218/25` is now a nonoscillatory `L¹` estimate. -/
theorem integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_fourthOrderBudget
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hbudget : thetaCuspGroundFourthOrderThreshold a < b) :
    0 < ∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a 1 x *
        Real.sin (b * x) := by
  let r : ℝ → ℝ := fun x =>
    4 *
        (thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
          thetaCuspTiltedWardDensity a 1 x) +
      x * thetaCuspTiltedWardDensityFourthDerivative a 1 x
  have hf₃Int :
      IntegrableOn
        (fun x =>
          thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
            thetaCuspTiltedWardDensity a 1 x) (Ioi 0) :=
    integrableOn_thetaCuspTiltedWardDensityThirdDerivative
      (by linarith) (by norm_num)
  have hxf₄Int :
      IntegrableOn
        (fun x => x *
          thetaCuspTiltedWardDensityFourthDerivative a 1 x) (Ioi 0) :=
    integrableOn_id_mul_thetaCuspTiltedWardDensityFourthDerivative
      (by linarith) (by norm_num)
  have hrInt : IntegrableOn r (Ioi 0) := by
    exact (hf₃Int.const_mul 4).add hxf₄Int
  have habsInt : IntegrableOn (fun x => |r x|) (Ioi 0) :=
    hrInt.abs
  have hsinInt :
      IntegrableOn (fun x => r x * Real.sin (b * x)) (Ioi 0) := by
    apply Integrable.mul_bdd hrInt
    · exact (by
        fun_prop : Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hscore :
      thetaCuspTiltedWardScore a 1 0 < 0 :=
    thetaCuspTiltedWardScore_neg ha (by norm_num) (by norm_num)
  have hdensity :
      0 < thetaCuspTiltedWardDensity a 1 0 :=
    thetaCuspTiltedWardDensity_pos a (by norm_num) 0
  have hdenom :
      0 < -2 *
        (thetaCuspTiltedWardScore a 1 0 *
          thetaCuspTiltedWardDensity a 1 0) := by
    have hprod :
        thetaCuspTiltedWardScore a 1 0 *
          thetaCuspTiltedWardDensity a 1 0 < 0 :=
      mul_neg_of_neg_of_pos hscore hdensity
    linarith
  have habsNonneg :
      0 ≤ ∫ x : ℝ in Ioi 0, |r x| :=
    integral_nonneg fun x => abs_nonneg _
  have hb : 0 < b := by
    have hratio :
        0 ≤ (∫ x : ℝ in Ioi 0, |r x|) /
          (-2 *
            (thetaCuspTiltedWardScore a 1 0 *
              thetaCuspTiltedWardDensity a 1 0)) :=
      div_nonneg habsNonneg hdenom.le
    have hthreshold :
        (∫ x : ℝ in Ioi 0, |r x|) /
            (-2 *
              (thetaCuspTiltedWardScore a 1 0 *
                thetaCuspTiltedWardDensity a 1 0)) < b := by
      simpa only [r, thetaCuspGroundFourthOrderThreshold] using hbudget
    linarith
  have hmain :
      (∫ x : ℝ in Ioi 0, |r x|) <
        -2 * b *
          (thetaCuspTiltedWardScore a 1 0 *
            thetaCuspTiltedWardDensity a 1 0) := by
    have h :=
      (div_lt_iff₀ hdenom).mp
        (show
          (∫ x : ℝ in Ioi 0, |r x|) /
              (-2 *
                (thetaCuspTiltedWardScore a 1 0 *
                  thetaCuspTiltedWardDensity a 1 0)) < b by
            simpa only [r, thetaCuspGroundFourthOrderThreshold] using hbudget)
    nlinarith
  have hlower :
      -(∫ x : ℝ in Ioi 0, |r x|) ≤
        ∫ x : ℝ in Ioi 0, r x * Real.sin (b * x) := by
    rw [← integral_neg]
    apply integral_mono_ae habsInt.neg hsinInt
    filter_upwards with x
    have habsMul :
        |r x * Real.sin (b * x)| ≤ |r x| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
    exact le_trans (neg_le_neg habsMul) (neg_abs_le _)
  have hidentity :=
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_fourthOrderBoundary_identity
      (a := a) (b := b) (n := 1) (by linarith) (by norm_num)
  have hscaled :
      0 < b ^ 4 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a 1 x *
          Real.sin (b * x)) := by
    rw [hidentity]
    dsimp only [r] at hlower
    linarith
  exact pos_of_mul_pos_right hscaled (pow_nonneg hb.le 4)

theorem integrableOn_thetaCuspTiltedWardDerivativeRotationDensity
    {a : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (thetaCuspTiltedWardDerivativeRotationDensity a n)
      (Ioi 0) := by
  have hf :=
    integrableOn_thetaCuspTiltedWardDensity ha hn
  have hxf' :=
    integrableOn_id_mul_thetaCuspTiltedWardDensityDerivative
      ha hn
  unfold thetaCuspTiltedWardDerivativeRotationDensity
  exact (hf.add hxf').neg

/-- Exact positive-kernel reduction of the real spectral-derivative direction.  The conjectural
sign is now a competition between a unique negative boundary layer and a positive tail. -/
theorem integral_thetaCuspTiltedWardDerivativeRotationDensity_mul_one_sub_cos
    {a b : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    b * (∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) =
      ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x)) := by
  let u : ℝ → ℝ := fun x => 1 - Real.cos (b * x)
  let u' : ℝ → ℝ := fun x => b * Real.sin (b * x)
  let v : ℝ → ℝ := fun x =>
    x * thetaCuspTiltedWardDensity a n x
  let v' : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardDensity a n x +
      x * (thetaCuspTiltedWardScore a n x *
        thetaCuspTiltedWardDensity a n x)
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    dsimp only [u, u']
    convert (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) |>.neg.const_add 1 using 1
    ring
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    dsimp only [v, v']
    convert (hasDerivAt_id x).mul
      (hasDerivAt_thetaCuspTiltedWardDensity a n x) using 1
    simp only [id_eq]
    ring
  have hvInt : IntegrableOn v (Ioi 0) := by
    simpa only [v] using
      integrableOn_id_mul_thetaCuspTiltedWardDensity ha hn
  have hv'Int : IntegrableOn v' (Ioi 0) := by
    have hf :=
      integrableOn_thetaCuspTiltedWardDensity ha hn
    have hxf' :=
      integrableOn_id_mul_thetaCuspTiltedWardDensityDerivative
        ha hn
    simpa only [v'] using hf.add hxf'
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    have hcos : IntegrableOn
        (fun x => Real.cos (b * x) * v' x) (Ioi 0) := by
      apply Integrable.bdd_mul hv'Int
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_cos_le_one _
    rw [show (u * v') = v' -
        (fun x => Real.cos (b * x) * v' x) by
      funext x
      dsimp only [u, Pi.mul_apply, Pi.sub_apply]
      ring]
    exact hv'Int.sub hcos
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have hsin : IntegrableOn
        (fun x => Real.sin (b * x) * v x) (Ioi 0) := by
      apply Integrable.bdd_mul hvInt
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_sin_le_one _
    rw [show (u' * v) =
        fun x => b * (Real.sin (b * x) * v x) by
      funext x
      dsimp only [u', Pi.mul_apply]
      ring]
    exact hsin.const_mul b
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (u * v) := by
      have hvcont : Continuous v :=
        continuous_iff_continuousAt.mpr fun x =>
          (hv x).continuousAt
      dsimp only [u]
      exact
        (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).mul hvcont
    simpa [u, v] using
      (hcont.continuousAt :
        Tendsto (u * v) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have hv0 : Tendsto v atTop (𝓝 0) := by
      simpa only [v] using
        tendsto_id_mul_thetaCuspTiltedWardDensity_atTop_zero
          ha hn
    have hcos0 :
        Tendsto (fun x => Real.cos (b * x) * v x)
          atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hle : ∀ᶠ x : ℝ in atTop,
          ‖Real.cos (b * x) * v x‖ ≤ ‖v x‖ :=
        Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (by simpa using abs_cos_le_one (b * x))
      exact squeeze_zero'
        (Eventually.of_forall fun x => norm_nonneg _) hle
        (by simpa using hv0.norm)
    simpa only [sub_zero] using hv0.sub hcos0
      |>.congr' (Eventually.of_forall fun x => by
        dsimp only [u, Pi.mul_apply]
        ring)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u')
    (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x)
    huv' hu'v hzero hinfty
  rw [show
      (fun x : ℝ => u' x * v x) =
        fun x => b *
          (x * thetaCuspTiltedWardDensity a n x *
            Real.sin (b * x)) by
    funext x
    dsimp only [u', v]
    ring,
    integral_const_mul] at hibp
  rw [show
      (fun x : ℝ => u x * v' x) =
        fun x =>
          -thetaCuspTiltedWardDerivativeRotationDensity a n x *
            (1 - Real.cos (b * x)) by
    funext x
    dsimp only [u, v']
    unfold thetaCuspTiltedWardDerivativeRotationDensity
    ring,
    show
      (fun x : ℝ =>
        -thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x))) =
      (fun x =>
        -(thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x)))) by
        funext x
        ring,
    integral_neg] at hibp
  linarith

/-- The universal tail beyond `x = 1/3` contributes strictly positively to the derivative
rotation transform of every positive shell. -/
theorem integral_Ioi_one_div_three_thetaCuspTiltedWardDerivativeRotationDensity_pos
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 0 < n) :
    0 < ∫ x : ℝ in Ioi (1 / 3),
      thetaCuspTiltedWardDerivativeRotationDensity a n x *
        (1 - Real.cos (b * x)) := by
  let h : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardDerivativeRotationDensity a n x *
      (1 - Real.cos (b * x))
  have hrot :=
    integrableOn_thetaCuspTiltedWardDerivativeRotationDensity
      (a := a) (by linarith) hn
  have hcos : IntegrableOn
      (fun x => Real.cos (b * x) *
        thetaCuspTiltedWardDerivativeRotationDensity a n x)
      (Ioi 0) := by
    apply Integrable.bdd_mul hrot
    · exact (by
        fun_prop :
        Continuous
          (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hhInt0 : IntegrableOn h (Ioi 0) := by
    rw [show h =
        thetaCuspTiltedWardDerivativeRotationDensity a n -
          fun x => Real.cos (b * x) *
            thetaCuspTiltedWardDerivativeRotationDensity a n x by
      funext x
      dsimp only [h, Pi.sub_apply]
      ring]
    exact hrot.sub hcos
  have hhInt : IntegrableOn h (Ioi (1 / 3)) :=
    hhInt0.mono_set (Ioi_subset_Ioi (by norm_num))
  have hhnn : ∀ᵐ x ∂(volume.restrict (Ioi (1 / 3))),
      0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hrotPos :
        0 < thetaCuspTiltedWardDerivativeRotationDensity a n x :=
      thetaCuspTiltedWardDerivativeRotationDensity_pos_of_one_div_three_le
        ha hn hx.le
    exact mul_nonneg hrotPos.le
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hhcont : Continuous h := by
    dsimp only [h]
    unfold thetaCuspTiltedWardDerivativeRotationDensity
      thetaCuspTiltedWardScore thetaCuspTiltedWardDensity
      thetaCuspWardGibbsAtom thetaCuspPolynomialAtom
    fun_prop
  apply (setIntegral_pos_iff_support_of_nonneg_ae hhnn hhInt).2
  have hopen :
      IsOpen (Function.support h ∩ Ioi (1 / 3)) :=
    hhcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  let x₁ : ℝ := 1 / 3 + Real.pi / b
  by_cases hk₁ : 1 - Real.cos (b * x₁) = 0
  · let x₂ : ℝ := 1 / 3 + Real.pi / (2 * b)
    refine ⟨x₂, ?_, ?_⟩
    · change h x₂ ≠ 0
      have hphase₁ : b * x₁ = b / 3 + Real.pi := by
        dsimp only [x₁]
        field_simp
      have hcost : Real.cos (b / 3) = -1 := by
        rw [hphase₁, Real.cos_add, Real.cos_pi,
          Real.sin_pi] at hk₁
        linarith
      have hsint : Real.sin (b / 3) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq (b / 3)]
      have hphase₂ : b * x₂ = b / 3 + Real.pi / 2 := by
        dsimp only [x₂]
        field_simp
      have hk₂ : 1 - Real.cos (b * x₂) = 1 := by
        rw [hphase₂, Real.cos_add, Real.cos_pi_div_two,
          Real.sin_pi_div_two, hcost, hsint]
        ring
      have hx₂ : 1 / 3 ≤ x₂ := by
        dsimp only [x₂]
        have hdiv : 0 < Real.pi / (2 * b) := by positivity
        linarith
      have hrotPos :
          0 < thetaCuspTiltedWardDerivativeRotationDensity a n x₂ :=
        thetaCuspTiltedWardDerivativeRotationDensity_pos_of_one_div_three_le
          ha hn hx₂
      dsimp only [h]
      rw [hk₂]
      exact (by simpa using hrotPos.ne')
    · change (1 / 3 : ℝ) < 1 / 3 + Real.pi / (2 * b)
      have hdiv : 0 < Real.pi / (2 * b) := by positivity
      exact lt_add_of_pos_right _ hdiv
  · refine ⟨x₁, ?_, ?_⟩
    · change h x₁ ≠ 0
      have hx₁ : 1 / 3 ≤ x₁ := by
        dsimp only [x₁]
        have hdiv : 0 < Real.pi / b := div_pos Real.pi_pos hb
        linarith
      have hrotPos :
          0 < thetaCuspTiltedWardDerivativeRotationDensity a n x₁ :=
        thetaCuspTiltedWardDerivativeRotationDensity_pos_of_one_div_three_le
          ha hn hx₁
      dsimp only [h]
      exact mul_ne_zero hrotPos.ne' hk₁
    · change (1 / 3 : ℝ) < 1 / 3 + Real.pi / b
      have hdiv : 0 < Real.pi / b := div_pos Real.pi_pos hb
      exact lt_add_of_pos_right _ hdiv

/-- Exact compact-defect split.  For every positive shell, derivative rotation is the sum of one
compact head on `(0,1/3]` and a tail that is strictly positive at positive frequency. -/
theorem thetaCuspTiltedWardDerivativeRotation_compact_defect_split
    {a b : ℝ} (ha : a < 1) {n : ℕ} (hn : 0 < n) :
    b * (∫ x : ℝ in Ioi 0,
      x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) =
      (∫ x : ℝ in Ioc 0 (1 / 3),
        thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x))) +
      ∫ x : ℝ in Ioi (1 / 3),
        thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x)) := by
  let h : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardDerivativeRotationDensity a n x *
      (1 - Real.cos (b * x))
  have hrot :=
    integrableOn_thetaCuspTiltedWardDerivativeRotationDensity
      (a := a) ha hn
  have hcos : IntegrableOn
      (fun x => Real.cos (b * x) *
        thetaCuspTiltedWardDerivativeRotationDensity a n x)
      (Ioi 0) := by
    apply Integrable.bdd_mul hrot
    · exact (by
        fun_prop :
        Continuous
          (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hhInt : IntegrableOn h (Ioi 0) := by
    rw [show h =
        thetaCuspTiltedWardDerivativeRotationDensity a n -
          fun x => Real.cos (b * x) *
            thetaCuspTiltedWardDerivativeRotationDensity a n x by
      funext x
      dsimp only [h, Pi.sub_apply]
      ring]
    exact hrot.sub hcos
  rw [integral_thetaCuspTiltedWardDerivativeRotationDensity_mul_one_sub_cos
    ha hn]
  change (∫ x : ℝ in Ioi 0, h x) =
    (∫ x : ℝ in Ioc 0 (1 / 3), h x) +
      ∫ x : ℝ in Ioi (1 / 3), h x
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1 / 3),
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi]
  · exact hhInt.mono_set Ioc_subset_Ioi_self
  · exact hhInt.mono_set (Ioi_subset_Ioi (by norm_num))

/-- **Strict monotone-sine phase law.**  Every positive Ward shell has strictly positive sine
transform at every positive frequency, uniformly throughout the critical aperture. -/
theorem integral_thetaCuspTiltedWardDensity_mul_sin_pos
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 0 < n) :
    0 < ∫ x : ℝ in Ioi 0,
      thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x) := by
  let u : ℝ → ℝ := fun x => 1 - Real.cos (b * x)
  let u' : ℝ → ℝ := fun x => b * Real.sin (b * x)
  let v : ℝ → ℝ := thetaCuspTiltedWardDensity a n
  let v' : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    dsimp only [u, u']
    convert (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) |>.neg.const_add 1 using 1
    ring
  have hv (x : ℝ) : HasDerivAt v (v' x) x := by
    simpa only [v, v'] using
      hasDerivAt_thetaCuspTiltedWardDensity a n x
  have hvInt : IntegrableOn v (Ioi 0) :=
    integrableOn_thetaCuspTiltedWardDensity
      (by linarith) hn
  have hv'Int : IntegrableOn v' (Ioi 0) :=
    integrableOn_thetaCuspTiltedWardDensityDerivative
      (by linarith) hn
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    have hcos : IntegrableOn
        (fun x => Real.cos (b * x) * v' x) (Ioi 0) := by
      apply Integrable.bdd_mul hv'Int
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_cos_le_one _
    rw [show (u * v') = v' -
        (fun x => Real.cos (b * x) * v' x) by
      funext x
      dsimp only [u, Pi.mul_apply, Pi.sub_apply]
      ring]
    exact hv'Int.sub hcos
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have hsin : IntegrableOn
        (fun x => Real.sin (b * x) * v x) (Ioi 0) := by
      apply Integrable.bdd_mul hvInt
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_sin_le_one _
    rw [show (u' * v) =
        fun x => b * (Real.sin (b * x) * v x) by
      funext x
      dsimp only [u', Pi.mul_apply]
      ring]
    exact hsin.const_mul b
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (u * v) := by
      have hvcont : Continuous v :=
        continuous_iff_continuousAt.mpr fun x =>
          (hv x).continuousAt
      dsimp only [u]
      exact
        (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).mul hvcont
    simpa [u, v] using
      (hcont.continuousAt :
        Tendsto (u * v) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have hv0 : Tendsto v atTop (𝓝 0) := by
      simpa only [v] using
        tendsto_thetaCuspTiltedWardDensity_atTop_zero
          (by linarith) hn
    have hcos0 :
        Tendsto (fun x => Real.cos (b * x) * v x)
          atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hle : ∀ᶠ x : ℝ in atTop,
          ‖Real.cos (b * x) * v x‖ ≤ ‖v x‖ :=
        Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (by simpa using abs_cos_le_one (b * x))
      exact squeeze_zero'
        (Eventually.of_forall fun x => norm_nonneg _) hle
        (by simpa using hv0.norm)
    simpa only [sub_zero] using hv0.sub hcos0
      |>.congr' (Eventually.of_forall fun x => by
        dsimp only [u, Pi.mul_apply]
        ring)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u')
    (v := v) (v' := v')
    (fun x _ => hu x) (fun x _ => hv x)
    huv' hu'v hzero hinfty
  let h : ℝ → ℝ := fun x =>
    (-v' x) * (1 - Real.cos (b * x))
  have hhInt : IntegrableOn h (Ioi 0) := by
    apply huv'.neg.congr
    filter_upwards with x
    dsimp only [h, u, Pi.mul_apply, Pi.neg_apply]
    ring
  have hidentity :
      b * (∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) =
      ∫ x : ℝ in Ioi 0, h x := by
    rw [show
      (fun x : ℝ => u' x * v x) =
        fun x => b *
          (thetaCuspTiltedWardDensity a n x *
            Real.sin (b * x)) by
      funext x
      dsimp only [u', v]
      ring,
      integral_const_mul] at hibp
    rw [show
      (fun x : ℝ => u x * v' x) =
        fun x => -h x by
      funext x
      dsimp only [u, h]
      ring,
      integral_neg] at hibp
    linarith
  have hhnn : ∀ᵐ x ∂(volume.restrict (Ioi 0)),
      0 ≤ h x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hvneg : v' x < 0 := by
      dsimp only [v']
      exact mul_neg_of_neg_of_pos
        (thetaCuspTiltedWardScore_neg ha hn hx.le)
        (thetaCuspTiltedWardDensity_pos a hn x)
    exact mul_nonneg (neg_nonneg.mpr hvneg.le)
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hhpos : 0 < ∫ x : ℝ in Ioi 0, h x := by
    apply
      (setIntegral_pos_iff_support_of_nonneg_ae hhnn hhInt).2
    have hhcont : Continuous h := by
      have hvcont : Continuous v :=
        continuous_iff_continuousAt.mpr fun x =>
          (hv x).continuousAt
      have hscore :
          Continuous (thetaCuspTiltedWardScore a n) := by
        unfold thetaCuspTiltedWardScore
        fun_prop
      have hv'cont : Continuous v' := by
        dsimp only [v']
        exact hscore.mul hvcont
      dsimp only [h]
      exact hv'cont.neg.mul
        (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))
    have hopen :
        IsOpen (Function.support h ∩ Ioi (0 : ℝ)) :=
      hhcont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨Real.pi / b, ?_, div_pos Real.pi_pos hb⟩
    change h (Real.pi / b) ≠ 0
    have hx0 : 0 ≤ Real.pi / b :=
      (div_pos Real.pi_pos hb).le
    have hvneg : v' (Real.pi / b) < 0 := by
      dsimp only [v']
      exact mul_neg_of_neg_of_pos
        (thetaCuspTiltedWardScore_neg ha hn hx0)
        (thetaCuspTiltedWardDensity_pos a hn _)
    have harg : b * (Real.pi / b) = Real.pi := by
      field_simp
    dsimp only [h]
    rw [harg, Real.cos_pi]
    exact ne_of_gt
      (mul_pos (neg_pos.mpr hvneg) (by norm_num))
  nlinarith [hidentity, hhpos]

/-- **Strict convex-cosine phase law.** Every higher tilted Ward shell has strictly positive
cosine transform at every positive frequency throughout the critical aperture. -/
theorem integral_thetaCuspTiltedWardDensity_mul_cos_pos_of_two_le
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 2 ≤ n) :
    0 < ∫ x : ℝ in Ioi 0,
      thetaCuspTiltedWardDensity a n x *
        Real.cos (b * x) := by
  let f : ℝ → ℝ := thetaCuspTiltedWardDensity a n
  let f' : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardScore a n x *
      thetaCuspTiltedWardDensity a n x
  let f'' : ℝ → ℝ := fun x =>
    thetaCuspTiltedWardCurvature a n x *
      thetaCuspTiltedWardDensity a n x
  let s : ℝ → ℝ := fun x => Real.sin (b * x)
  let s' : ℝ → ℝ := fun x => b * Real.cos (b * x)
  let u : ℝ → ℝ := fun x => 1 - Real.cos (b * x)
  let u' : ℝ → ℝ := fun x => b * Real.sin (b * x)
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    simpa only [f, f'] using
      hasDerivAt_thetaCuspTiltedWardDensity a n x
  have hf' (x : ℝ) : HasDerivAt f' (f'' x) x := by
    simpa only [f', f''] using
      hasDerivAt_thetaCuspTiltedWardDensityDerivative a n x
  have hs (x : ℝ) : HasDerivAt s (s' x) x := by
    dsimp only [s, s']
    convert (Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) using 1
    ring
  have hu (x : ℝ) : HasDerivAt u (u' x) x := by
    dsimp only [u, u']
    convert (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b) |>.neg.const_add 1 using 1
    ring
  have hfInt : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      integrableOn_thetaCuspTiltedWardDensity
        (by linarith) hn0
  have hf'Int : IntegrableOn f' (Ioi 0) := by
    simpa only [f'] using
      integrableOn_thetaCuspTiltedWardDensityDerivative
        (by linarith) hn0
  have hf''Int : IntegrableOn f'' (Ioi 0) := by
    simpa only [f''] using
      integrableOn_thetaCuspTiltedWardDensitySecondDerivative
        (by linarith) hn0
  have hsf' : IntegrableOn (s * f') (Ioi 0) := by
    apply Integrable.bdd_mul hf'Int
    · exact (by
        fun_prop :
        Continuous
          (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_sin_le_one _
  have hs'f : IntegrableOn (s' * f) (Ioi 0) := by
    have hcos : IntegrableOn
        (fun x => Real.cos (b * x) * f x) (Ioi 0) := by
      apply Integrable.bdd_mul hfInt
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_cos_le_one _
    rw [show (s' * f) =
        fun x => b * (Real.cos (b * x) * f x) by
      funext x
      dsimp only [s', Pi.mul_apply]
      ring]
    exact hcos.const_mul b
  have hsf_zero : Tendsto (s * f) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (s * f) := by
      have hfcont : Continuous f :=
        continuous_iff_continuousAt.mpr fun x =>
          (hf x).continuousAt
      dsimp only [s]
      exact
        (Real.continuous_sin.comp
          (continuous_const.mul continuous_id)).mul hfcont
    simpa [s, f] using
      (hcont.continuousAt :
        Tendsto (s * f) (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have hsf_atTop : Tendsto (s * f) atTop (𝓝 0) := by
    have hf0 : Tendsto f atTop (𝓝 0) := by
      simpa only [f] using
        tendsto_thetaCuspTiltedWardDensity_atTop_zero
          (by linarith) hn0
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ᶠ x : ℝ in atTop,
        ‖s x * f x‖ ≤ ‖f x‖ :=
      Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (by
            dsimp only [s]
            simpa using abs_sin_le_one (b * x))
    exact squeeze_zero'
      (Eventually.of_forall fun x => norm_nonneg _) hle
      (by simpa using hf0.norm)
  have hibp1 := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := s) (u' := s')
    (v := f) (v' := f')
    (fun x _ => hs x) (fun x _ => hf x)
    hsf' hs'f hsf_zero hsf_atTop
  let h₁ : ℝ → ℝ := fun x => (-f' x) * Real.sin (b * x)
  have hh₁Int : IntegrableOn h₁ (Ioi 0) := by
    apply hsf'.neg.congr
    filter_upwards with x
    dsimp only [h₁, s, Pi.mul_apply, Pi.neg_apply]
    ring
  have hidentity₁ :
      b * (∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity a n x *
          Real.cos (b * x)) =
      ∫ x : ℝ in Ioi 0, h₁ x := by
    rw [show
      (fun x : ℝ => s' x * f x) =
        fun x => b *
          (thetaCuspTiltedWardDensity a n x *
            Real.cos (b * x)) by
      funext x
      dsimp only [s', f]
      ring,
      integral_const_mul] at hibp1
    rw [show
      (fun x : ℝ => s x * f' x) =
        fun x => -h₁ x by
      funext x
      dsimp only [s, h₁]
      ring,
      integral_neg] at hibp1
    linarith
  have huf'' : IntegrableOn (u * f'') (Ioi 0) := by
    have hcos : IntegrableOn
        (fun x => Real.cos (b * x) * f'' x) (Ioi 0) := by
      apply Integrable.bdd_mul hf''Int
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_cos_le_one _
    rw [show (u * f'') = f'' -
        (fun x => Real.cos (b * x) * f'' x) by
      funext x
      dsimp only [u, Pi.mul_apply, Pi.sub_apply]
      ring]
    exact hf''Int.sub hcos
  have hu'f' : IntegrableOn (u' * f') (Ioi 0) := by
    have hsin : IntegrableOn
        (fun x => Real.sin (b * x) * f' x) (Ioi 0) := by
      apply Integrable.bdd_mul hf'Int
      · exact (by
          fun_prop :
          Continuous
            (fun x : ℝ => Real.sin (b * x))).aestronglyMeasurable.restrict
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact abs_sin_le_one _
    rw [show (u' * f') =
        fun x => b * (Real.sin (b * x) * f' x) by
      funext x
      dsimp only [u', Pi.mul_apply]
      ring]
    exact hsin.const_mul b
  have huf'_zero : Tendsto (u * f') (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (u * f') := by
      have hf'cont : Continuous f' :=
        continuous_iff_continuousAt.mpr fun x =>
          (hf' x).continuousAt
      dsimp only [u]
      exact
        (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).mul hf'cont
    simpa [u, f'] using
      (hcont.continuousAt :
        Tendsto (u * f') (𝓝 (0 : ℝ)) _).mono_left inf_le_left
  have huf'_atTop : Tendsto (u * f') atTop (𝓝 0) := by
    have hf'0 : Tendsto f' atTop (𝓝 0) := by
      simpa only [f'] using
        tendsto_thetaCuspTiltedWardDensityDerivative_atTop_zero
          (by linarith) hn0
    have hcos0 :
        Tendsto (fun x => Real.cos (b * x) * f' x)
          atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hle : ∀ᶠ x : ℝ in atTop,
          ‖Real.cos (b * x) * f' x‖ ≤ ‖f' x‖ :=
        Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (by simpa using abs_cos_le_one (b * x))
      exact squeeze_zero'
        (Eventually.of_forall fun x => norm_nonneg _) hle
        (by simpa using hf'0.norm)
    simpa only [sub_zero] using hf'0.sub hcos0
      |>.congr' (Eventually.of_forall fun x => by
        dsimp only [u, Pi.mul_apply]
        ring)
  have hibp2 := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := u) (u' := u')
    (v := f') (v' := f'')
    (fun x _ => hu x) (fun x _ => hf' x)
    huf'' hu'f' huf'_zero huf'_atTop
  let h₂ : ℝ → ℝ := fun x =>
    f'' x * (1 - Real.cos (b * x))
  have hh₂Int : IntegrableOn h₂ (Ioi 0) := by
    apply huf''.congr
    filter_upwards with x
    dsimp only [h₂, u, Pi.mul_apply]
    ring
  have hidentity₂ :
      b * (∫ x : ℝ in Ioi 0, h₁ x) =
      ∫ x : ℝ in Ioi 0, h₂ x := by
    rw [show
      (fun x : ℝ => u' x * f' x) =
        fun x => -b * h₁ x by
      funext x
      dsimp only [u', h₁]
      ring,
      integral_const_mul] at hibp2
    rw [show
      (fun x : ℝ => u x * f'' x) = h₂ by
      funext x
      dsimp only [u, h₂]
      ring] at hibp2
    linarith
  have hh₂nn : ∀ᵐ x ∂(volume.restrict (Ioi 0)),
      0 ≤ h₂ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hf''pos : 0 < f'' x := by
      dsimp only [f'']
      exact mul_pos
        (thetaCuspTiltedWardCurvature_pos_of_two_le
          ha hn hx.le)
        (thetaCuspTiltedWardDensity_pos a hn0 x)
    exact mul_nonneg hf''pos.le
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hh₂pos : 0 < ∫ x : ℝ in Ioi 0, h₂ x := by
    apply
      (setIntegral_pos_iff_support_of_nonneg_ae hh₂nn hh₂Int).2
    have hh₂cont : Continuous h₂ := by
      have hf''cont : Continuous f'' :=
        by
          rw [show f'' =
              fun x =>
                Real.exp (a * x) *
                  thetaCuspPolynomialAtom
                    (thetaCuspTiltedLogDerivativeStep a
                      (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
                    n x by
            funext x
            exact
              thetaCuspTiltedWardDensitySecondDerivative_eq_polynomial
                a n x]
          exact continuous_iff_continuousAt.mpr fun x =>
            (hasDerivAt_exp_mul_thetaCuspPolynomialAtom
              a
              (thetaCuspTiltedLogDerivativeStep a
                (thetaCuspTiltedLogDerivativeStep a (X ^ 2)))
              n x).continuousAt
      dsimp only [h₂]
      exact hf''cont.mul
        (continuous_const.sub (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))
    have hopen :
        IsOpen (Function.support h₂ ∩ Ioi (0 : ℝ)) :=
      hh₂cont.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨Real.pi / b, ?_, div_pos Real.pi_pos hb⟩
    change h₂ (Real.pi / b) ≠ 0
    have hx0 : 0 ≤ Real.pi / b :=
      (div_pos Real.pi_pos hb).le
    have hf''pos : 0 < f'' (Real.pi / b) := by
      dsimp only [f'']
      exact mul_pos
        (thetaCuspTiltedWardCurvature_pos_of_two_le
          ha hn hx0)
        (thetaCuspTiltedWardDensity_pos a hn0 _)
    have harg : b * (Real.pi / b) = Real.pi := by
      field_simp
    dsimp only [h₂]
    rw [harg, Real.cos_pi]
    exact ne_of_gt
      (mul_pos hf''pos (by norm_num))
  have hbh₁ : 0 < b * (∫ x : ℝ in Ioi 0, h₁ x) := by
    rw [hidentity₂]
    exact hh₂pos
  have hh₁pos : 0 < ∫ x : ℝ in Ioi 0, h₁ x := by
    rcases mul_pos_iff.mp hbh₁ with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hb.le hneg.1).elim
  have hbcos : 0 < b * (∫ x : ℝ in Ioi 0,
      thetaCuspTiltedWardDensity a n x *
        Real.cos (b * x)) := by
    rw [hidentity₁]
    exact hh₁pos
  rcases mul_pos_iff.mp hbcos with hpos | hneg
  · exact hpos.2
  · exact (not_lt_of_ge hb.le hneg.1).elim

/-- At a tilted spectral point, the literal Ward first moment is integrable as a complex
half-line function. -/
theorem integrableOn_thetaCuspWard_phaseSpectralDerivative_tilted
    {a : ℝ} (ha : a < 1) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn
      (fun x : ℝ =>
        (thetaCuspWardGibbsAtom n x : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I)))
      (Ioi 0) := by
  have hmajor :=
    integrableOn_id_mul_thetaCuspTiltedWardDensity ha hn
  apply Integrable.mono hmajor
  · have hW : Continuous (thetaCuspWardGibbsAtom n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspWardGibbsAtom n x).continuousAt
    exact ((Complex.continuous_ofReal.comp hW).mul
      (((Complex.continuous_ofReal.comp continuous_id).mul
        continuous_const).mul
        (by
          unfold spectralTranslationPhase
          fun_prop))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hW0 : 0 ≤ thetaCuspWardGibbsAtom n x := by
      rw [thetaCuspWardGibbsAtom_apply]
      positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hW0, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx0, norm_I, mul_one,
      norm_spectralTranslationPhase_eq_exp_neg_mul_im_gamma]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    have hd0 : 0 ≤ thetaCuspTiltedWardDensity a n x :=
      (thetaCuspTiltedWardDensity_pos a hn x).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0,
      abs_of_nonneg hd0]
    unfold thetaCuspTiltedWardDensity
    rw [show -x * -(a + 0) = a * x by ring]
    ring_nf
    exact le_rfl

theorem thetaCuspWard_phase_im_pointwise
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    ((thetaCuspWardGibbsAtom n x : ℂ) *
      spectralTranslationPhase x
        ((b : ℂ) - (a : ℂ) * I)).im =
      thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x) := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  unfold spectralTranslationPhase
  have hexp :
      ((x : ℂ) * I) * ((b : ℂ) - (a : ℂ) * I) =
        (a * x : ℝ) + (b * x : ℝ) * I := by
    calc
      ((x : ℂ) * I) * ((b : ℂ) - (a : ℂ) * I) =
          ((x * b : ℝ) : ℂ) * I -
            ((x * a : ℝ) : ℂ) * (I * I) := by
        push_cast
        ring
      _ = (a * x : ℝ) + (b * x : ℝ) * I := by
        rw [I_mul_I]
        push_cast
        ring
  rw [hexp, Complex.exp_im]
  simp only [add_re, ofReal_re, mul_re, mul_im,
    ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, mul_one, add_im, zero_add,
    thetaCuspTiltedWardDensity]
  ring

theorem thetaCuspWard_phase_re_pointwise
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    ((thetaCuspWardGibbsAtom n x : ℂ) *
      spectralTranslationPhase x
        ((b : ℂ) - (a : ℂ) * I)).re =
      thetaCuspTiltedWardDensity a n x *
        Real.cos (b * x) := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  unfold spectralTranslationPhase
  have hexp :
      ((x : ℂ) * I) * ((b : ℂ) - (a : ℂ) * I) =
        (a * x : ℝ) + (b * x : ℝ) * I := by
    calc
      ((x : ℂ) * I) * ((b : ℂ) - (a : ℂ) * I) =
          ((x * b : ℝ) : ℂ) * I -
            ((x * a : ℝ) : ℂ) * (I * I) := by
        push_cast
        ring
      _ = (a * x : ℝ) + (b * x : ℝ) * I := by
        rw [I_mul_I]
        push_cast
        ring
  rw [hexp, Complex.exp_re]
  simp only [add_re, ofReal_re, mul_re, mul_im,
    ofReal_im, I_re, I_im, mul_zero, zero_mul,
    sub_zero, mul_one, add_im, zero_add,
    thetaCuspTiltedWardDensity]
  ring

/-- The real direction of the literal Ward spectral derivative is the negative tilted sine first
moment. -/
theorem thetaCuspWard_phaseSpectralDerivative_re_pointwise
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    ((thetaCuspWardGibbsAtom n x : ℂ) *
      (((x : ℂ) * I) *
        spectralTranslationPhase x
          ((b : ℂ) - (a : ℂ) * I))).re =
      -(x * thetaCuspTiltedWardDensity a n x *
        Real.sin (b * x)) := by
  rw [show
      (thetaCuspWardGibbsAtom n x : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I)) =
        ((x : ℂ) * I) *
          ((thetaCuspWardGibbsAtom n x : ℂ) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I)) by ring,
    Complex.mul_re]
  have hre : (((x : ℂ) * I)).re = 0 := by
    simp [Complex.mul_re]
  have him : (((x : ℂ) * I)).im = x := by
    simp [Complex.mul_im]
  rw [hre, him, zero_mul, zero_sub]
  rw [thetaCuspWard_phase_im_pointwise]
  ring

/-- The transverse direction of the literal Ward spectral derivative is the tilted cosine first
moment. -/
theorem thetaCuspWard_phaseSpectralDerivative_im_pointwise
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    ((thetaCuspWardGibbsAtom n x : ℂ) *
      (((x : ℂ) * I) *
        spectralTranslationPhase x
          ((b : ℂ) - (a : ℂ) * I))).im =
      x * thetaCuspTiltedWardDensity a n x *
        Real.cos (b * x) := by
  rw [show
      (thetaCuspWardGibbsAtom n x : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I)) =
        ((x : ℂ) * I) *
          ((thetaCuspWardGibbsAtom n x : ℂ) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I)) by ring,
    Complex.mul_im]
  have hre : (((x : ℂ) * I)).re = 0 := by
    simp [Complex.mul_re]
  have him : (((x : ℂ) * I)).im = x := by
    simp [Complex.mul_im]
  rw [hre, him, zero_mul, zero_add]
  rw [thetaCuspWard_phase_re_pointwise]
  ring

theorem thetaCuspShellWardPhaseTransform_im_eq_sine
    {a : ℝ} (ha : a < 1) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellWardPhaseTransform
      ((b : ℂ) - (a : ℂ) * I) n).im =
      ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x) := by
  have hz :
      -1 < (((b : ℂ) - (a : ℂ) * I)).im := by
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    linarith
  have hInt :=
    integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
      (X ^ 2) hn hz
  unfold thetaCuspShellWardPhaseTransform
    thetaCuspWardGibbsAtom
  calc
    (∫ x : ℝ in Ioi 0,
      (thetaCuspPolynomialAtom (X ^ 2) n x : ℂ) *
        spectralTranslationPhase x
          ((b : ℂ) - (a : ℂ) * I)).im =
      ∫ x : ℝ in Ioi 0,
        ((thetaCuspPolynomialAtom (X ^ 2) n x : ℂ) *
          spectralTranslationPhase x
            ((b : ℂ) - (a : ℂ) * I)).im :=
      (integral_im hInt).symm
    _ = ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x) := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [thetaCuspWardGibbsAtom] using
        thetaCuspWard_phase_im_pointwise a b n x

theorem thetaCuspShellWardPhaseTransform_re_eq_cosine
    {a : ℝ} (ha : a < 1) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellWardPhaseTransform
      ((b : ℂ) - (a : ℂ) * I) n).re =
      ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity a n x *
          Real.cos (b * x) := by
  have hz :
      -1 < (((b : ℂ) - (a : ℂ) * I)).im := by
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    linarith
  have hInt :=
    integrableOn_thetaCuspPolynomialAtom_mul_phase_of_neg_one_lt_im
      (X ^ 2) hn hz
  unfold thetaCuspShellWardPhaseTransform
    thetaCuspWardGibbsAtom
  calc
    (∫ x : ℝ in Ioi 0,
      (thetaCuspPolynomialAtom (X ^ 2) n x : ℂ) *
        spectralTranslationPhase x
          ((b : ℂ) - (a : ℂ) * I)).re =
      ∫ x : ℝ in Ioi 0,
        ((thetaCuspPolynomialAtom (X ^ 2) n x : ℂ) *
          spectralTranslationPhase x
            ((b : ℂ) - (a : ℂ) * I)).re :=
      (integral_re hInt).symm
    _ = ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity a n x *
          Real.cos (b * x) := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [thetaCuspWardGibbsAtom] using
        thetaCuspWard_phase_re_pointwise a b n x

/-- Exact real-coordinate formula for the Ward spectral derivative. -/
theorem thetaCuspShellWardPhaseTransformSpectralDerivative_re_eq
    {a : ℝ} (ha : a < 1) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellWardPhaseTransformSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re =
      -∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x) := by
  have hInt :=
    integrableOn_thetaCuspWard_phaseSpectralDerivative_tilted
      ha b hn
  unfold thetaCuspShellWardPhaseTransformSpectralDerivative
  calc
    (∫ x : ℝ in Ioi 0,
      (thetaCuspWardGibbsAtom n x : ℂ) *
        (((x : ℂ) * I) *
          spectralTranslationPhase x
            ((b : ℂ) - (a : ℂ) * I))).re =
      ∫ x : ℝ in Ioi 0,
        ((thetaCuspWardGibbsAtom n x : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I))).re :=
      (integral_re hInt).symm
    _ = -∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      exact thetaCuspWard_phaseSpectralDerivative_re_pointwise
        a b n x

/-- Exact transverse-coordinate formula for the Ward spectral derivative. -/
theorem thetaCuspShellWardPhaseTransformSpectralDerivative_im_eq
    {a : ℝ} (ha : a < 1) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellWardPhaseTransformSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).im =
      ∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.cos (b * x) := by
  have hInt :=
    integrableOn_thetaCuspWard_phaseSpectralDerivative_tilted
      ha b hn
  unfold thetaCuspShellWardPhaseTransformSpectralDerivative
  calc
    (∫ x : ℝ in Ioi 0,
      (thetaCuspWardGibbsAtom n x : ℂ) *
        (((x : ℂ) * I) *
          spectralTranslationPhase x
            ((b : ℂ) - (a : ℂ) * I))).im =
      ∫ x : ℝ in Ioi 0,
        ((thetaCuspWardGibbsAtom n x : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x
              ((b : ℂ) - (a : ℂ) * I))).im :=
      (integral_im hInt).symm
    _ = ∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.cos (b * x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact thetaCuspWard_phaseSpectralDerivative_im_pointwise
        a b n x

theorem thetaCuspShellWardPhaseTransform_im_pos
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 0 < n) :
    0 < (thetaCuspShellWardPhaseTransform
      ((b : ℂ) - (a : ℂ) * I) n).im := by
  rw [thetaCuspShellWardPhaseTransform_im_eq_sine
    (by linarith) b hn]
  exact integral_thetaCuspTiltedWardDensity_mul_sin_pos
    ha hb hn

/-- Strict first-quadrant phase law for every higher Ward shell. -/
theorem thetaCuspShellWardPhaseTransform_re_pos_of_two_le
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 2 ≤ n) :
    0 < (thetaCuspShellWardPhaseTransform
      ((b : ℂ) - (a : ℂ) * I) n).re := by
  rw [thetaCuspShellWardPhaseTransform_re_eq_cosine
    (by linarith) b (lt_of_lt_of_le (by norm_num) hn)]
  exact integral_thetaCuspTiltedWardDensity_mul_cos_pos_of_two_le
    ha hb hn

/-- The Ward sector law extends to the full shifted upper quadrant on which the Gamma remainder
is defined.  The lower aperture bound is exactly what keeps the Gamma representation in its
open strip. -/
theorem thetaCuspShellGammaCoreRemainder_im_pos_of_neg_one_lt
    {a b : ℝ} (haLower : -1 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    0 < (thetaCuspShellGammaCoreRemainder
      ((b : ℂ) - (a : ℂ) * I) n).im := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp only [z]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    rw [abs_neg]
    rw [abs_lt]
    constructor <;> linarith
  have hcoeff : I * z - 1 / 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [z] at him
    simp [Complex.mul_im, Complex.mul_re] at him
    linarith
  rw [thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
    hz hcoeff hn]
  rw [show
    (2 * thetaCuspShellWardPhaseTransform z n).im =
      2 * (thetaCuspShellWardPhaseTransform z n).im by
    simp [Complex.mul_im]]
  dsimp only [z]
  exact mul_pos (by norm_num)
    (thetaCuspShellWardPhaseTransform_im_pos ha hb hn)

/-- **Uniform Gamma-remainder sector law.**  In the entire open critical aperture and at every
positive frequency, every positive-shell incomplete-Gamma remainder lies strictly in the upper
half-plane. -/
theorem thetaCuspShellGammaCoreRemainder_im_pos
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    0 < (thetaCuspShellGammaCoreRemainder
      ((b : ℂ) - (a : ℂ) * I) n).im :=
  thetaCuspShellGammaCoreRemainder_im_pos_of_neg_one_lt
    (by linarith) ha hb hn

/-- **Higher-shell open-quadrant law.** In the critical aperture every incomplete-Gamma
remainder except the ground shell lies in the strict first quadrant at positive frequency. -/
theorem thetaCuspShellGammaCoreRemainder_re_pos_of_two_le_of_neg_one_lt
    {a b : ℝ} (haLower : -1 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    0 < (thetaCuspShellGammaCoreRemainder
      ((b : ℂ) - (a : ℂ) * I) n).re := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp only [z]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    rw [abs_neg, abs_lt]
    exact ⟨by simpa using haLower, by linarith⟩
  have hcoeff : I * z - 1 / 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [z] at him
    simp [Complex.mul_im, Complex.mul_re] at him
    linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
    hz hcoeff hn0]
  rw [show
    (2 * thetaCuspShellWardPhaseTransform z n).re =
      2 * (thetaCuspShellWardPhaseTransform z n).re by
    simp [Complex.mul_re]]
  dsimp only [z]
  exact mul_pos (by norm_num)
    (thetaCuspShellWardPhaseTransform_re_pos_of_two_le
      ha hb hn)

theorem thetaCuspShellGammaCoreRemainder_re_pos_of_two_le
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    0 < (thetaCuspShellGammaCoreRemainder
      ((b : ℂ) - (a : ℂ) * I) n).re :=
  thetaCuspShellGammaCoreRemainder_re_pos_of_two_le_of_neg_one_lt
    (by linarith) ha hb hn

/-- Exact directional derivative coordinate for the Gamma remainder.  Its real part is minus twice
the tilted Ward sine first moment. -/
theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq_of_neg_one_lt_of_ne
    {a b : ℝ} (haLower : -1 < a) (ha : a < 1 / 2)
    (hb : b ≠ 0) {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re =
      -2 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp only [z]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    rw [abs_neg, abs_lt]
    exact ⟨by simpa using haLower, by linarith⟩
  have hcoeff : I * z - 1 / 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [z] at him
    simp [Complex.mul_im, Complex.mul_re] at him
    exact hb (by linarith)
  rw [
    thetaCuspShellGammaCoreRemainderSpectralDerivative_eq_two_mul_ward
      hz hcoeff hn]
  rw [show
    (2 *
      thetaCuspShellWardPhaseTransformSpectralDerivative z n).re =
        2 *
          (thetaCuspShellWardPhaseTransformSpectralDerivative z n).re by
    simp [Complex.mul_re]]
  dsimp only [z]
  rw [thetaCuspShellWardPhaseTransformSpectralDerivative_re_eq
    (by linarith) b hn]
  ring

/-- Exact transverse derivative coordinate for the Gamma remainder. -/
theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_im_eq_of_neg_one_lt_of_ne
    {a b : ℝ} (haLower : -1 < a) (ha : a < 1 / 2)
    (hb : b ≠ 0) {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).im =
      2 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.cos (b * x)) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp only [z]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one]
    rw [abs_neg, abs_lt]
    exact ⟨by simpa using haLower, by linarith⟩
  have hcoeff : I * z - 1 / 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [z] at him
    simp [Complex.mul_im, Complex.mul_re] at him
    exact hb (by linarith)
  rw [
    thetaCuspShellGammaCoreRemainderSpectralDerivative_eq_two_mul_ward
      hz hcoeff hn]
  rw [show
    (2 *
      thetaCuspShellWardPhaseTransformSpectralDerivative z n).im =
        2 *
          (thetaCuspShellWardPhaseTransformSpectralDerivative z n).im by
    simp [Complex.mul_im]]
  dsimp only [z]
  rw [thetaCuspShellWardPhaseTransformSpectralDerivative_im_eq
    (by linarith) b hn]

theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq_of_neg_one_lt
    {a b : ℝ} (haLower : -1 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re =
      -2 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) :=
  thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq_of_neg_one_lt_of_ne
    haLower ha hb.ne' hn

theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re =
      -2 * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) :=
  thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq_of_neg_one_lt
    (by linarith) ha hb hn

/-- **Exact derivative-rotation identity for the Gamma remainder.**  The sign
`Re Rₙ' < 0` is equivalent to positivity of an explicit positive-kernel transform of the
one-transition rotation density. -/
theorem neg_half_mul_frequency_mul_thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    -(b / 2) *
        (thetaCuspShellGammaCoreRemainderSpectralDerivative
          ((b : ℂ) - (a : ℂ) * I) n).re =
      ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x)) := by
  rw [
    thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq
      ha0 ha hb hn]
  calc
    -(b / 2) *
        (-2 * (∫ x : ℝ in Ioi 0,
          x * thetaCuspTiltedWardDensity a n x *
            Real.sin (b * x))) =
      b * (∫ x : ℝ in Ioi 0,
        x * thetaCuspTiltedWardDensity a n x *
          Real.sin (b * x)) := by ring
    _ = ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDerivativeRotationDensity a n x *
          (1 - Real.cos (b * x)) :=
      integral_thetaCuspTiltedWardDerivativeRotationDensity_mul_one_sub_cos
        (by linarith) hn

/-- **Closed higher-shell derivative-rotation law.** In the critical aperture the real part of
every higher-shell Gamma-remainder derivative is strictly negative at every positive frequency. -/
theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_re_neg_of_two_le
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re < 0 := by
  rw [thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq
    ha0 ha hb (lt_of_lt_of_le (by norm_num) hn)]
  exact mul_neg_of_neg_of_pos (by norm_num)
    (integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
      ha hb hn)

/-- Ground-shell horizontal derivative direction above the explicit fourth-order threshold. -/
theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_re_neg_of_ground_fourthOrderBudget
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hbudget : thetaCuspGroundFourthOrderThreshold a < b) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) 1).re < 0 := by
  have hmoment :=
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_fourthOrderBudget
      ha0 ha hbudget
  have hb : 0 < b := by
    have hscore :
        thetaCuspTiltedWardScore a 1 0 < 0 :=
      thetaCuspTiltedWardScore_neg ha (by norm_num) (by norm_num)
    have hdensity :
        0 < thetaCuspTiltedWardDensity a 1 0 :=
      thetaCuspTiltedWardDensity_pos a (by norm_num) 0
    have hdenom :
        0 < -2 *
          (thetaCuspTiltedWardScore a 1 0 *
            thetaCuspTiltedWardDensity a 1 0) := by
      have hprod :
          thetaCuspTiltedWardScore a 1 0 *
            thetaCuspTiltedWardDensity a 1 0 < 0 :=
        mul_neg_of_neg_of_pos hscore hdensity
      linarith
    have hnum :
        0 ≤ ∫ x : ℝ in Ioi 0,
          |4 *
              (thetaCuspTiltedWardThirdDerivativeCoefficient a 1 x *
                thetaCuspTiltedWardDensity a 1 x) +
            x * thetaCuspTiltedWardDensityFourthDerivative a 1 x| :=
      integral_nonneg fun x => abs_nonneg _
    have hthreshold :
        0 ≤ thetaCuspGroundFourthOrderThreshold a := by
      unfold thetaCuspGroundFourthOrderThreshold
      exact div_nonneg hnum hdenom.le
    linarith
  rw [thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq
    ha0 ha hb (by norm_num)]
  exact mul_neg_of_neg_of_pos (by norm_num) hmoment

theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_re_neg_of_two_le_of_neg_one_lt
    {a b : ℝ} (haLower : -1 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re < 0 := by
  rw [
    thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq_of_neg_one_lt
      haLower ha hb (lt_of_lt_of_le (by norm_num) hn)]
  exact mul_neg_of_neg_of_pos (by norm_num)
    (integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
      ha hb hn)

/-- The reflected higher-shell remainder remains in the right half-plane. -/
theorem thetaCuspShellGammaCoreRemainder_reflected_re_pos_of_two_le
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    0 < (thetaCuspShellGammaCoreRemainder
      (-((b : ℂ) - (a : ℂ) * I)) n).re := by
  have hreflect :
      -((b : ℂ) - (a : ℂ) * I) =
        ((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hreflect]
  let z : ℂ := ((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp only [z]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one, neg_neg]
    rw [abs_lt]
    constructor <;> linarith
  have hcoeff : I * z - 1 / 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [z] at him
    simp [Complex.mul_im, Complex.mul_re] at him
    linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  rw [thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
    hz hcoeff hn0]
  have hcos :
      0 < ∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity (-a) n x *
          Real.cos ((-b) * x) := by
    simpa only [neg_mul, Real.cos_neg] using
      (integral_thetaCuspTiltedWardDensity_mul_cos_pos_of_two_le
        (a := -a) (b := b) (by linarith) hb hn)
  have hW :
      0 < (thetaCuspShellWardPhaseTransform
        (((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I) n).re := by
    rw [thetaCuspShellWardPhaseTransform_re_eq_cosine
      (a := -a) (b := -b) (by linarith) hn0]
    exact hcos
  dsimp only [z]
  norm_num [Complex.mul_re]
  convert hW using 1 <;> push_cast <;> ring

/-- The reflected higher-shell remainder lies in the lower half-plane. -/
theorem thetaCuspShellGammaCoreRemainder_reflected_im_neg
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    (thetaCuspShellGammaCoreRemainder
      (-((b : ℂ) - (a : ℂ) * I)) n).im < 0 := by
  have hreflect :
      -((b : ℂ) - (a : ℂ) * I) =
        ((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hreflect]
  let z : ℂ := ((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp only [z]
    simp only [sub_im, ofReal_im, mul_im, ofReal_re,
      I_re, I_im, zero_sub, zero_mul, mul_one, neg_neg]
    rw [abs_lt]
    constructor <;> linarith
  have hcoeff : I * z - 1 / 2 ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    dsimp only [z] at him
    simp [Complex.mul_im, Complex.mul_re] at him
    linarith
  rw [thetaCuspShellGammaCoreRemainder_eq_two_mul_ward
    hz hcoeff hn]
  have hsine :
      (∫ x : ℝ in Ioi 0,
        thetaCuspTiltedWardDensity (-a) n x *
          Real.sin ((-b) * x)) < 0 := by
    rw [show
      (fun x : ℝ =>
        thetaCuspTiltedWardDensity (-a) n x *
          Real.sin ((-b) * x)) =
      fun x =>
        -(thetaCuspTiltedWardDensity (-a) n x *
          Real.sin (b * x)) by
        funext x
        rw [neg_mul, Real.sin_neg]
        ring,
      integral_neg]
    exact neg_lt_zero.mpr
      (integral_thetaCuspTiltedWardDensity_mul_sin_pos
        (a := -a) (b := b) (by linarith) hb hn)
  have hW :
      (thetaCuspShellWardPhaseTransform
        (((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I) n).im < 0 := by
    rw [thetaCuspShellWardPhaseTransform_im_eq_sine
      (a := -a) (b := -b) (by linarith) hn]
    exact hsine
  dsimp only [z]
  have hW' :
      (thetaCuspShellWardPhaseTransform
        (-(b : ℂ) + (a : ℂ) * I) n).im < 0 := by
    convert hW using 1 <;> push_cast <;> ring
  norm_num [Complex.mul_im]
  nlinarith

/-- The reflected higher-shell spectral derivative points strictly right. -/
theorem thetaCuspShellGammaCoreRemainderSpectralDerivative_reflected_re_pos_of_two_le
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    0 < (thetaCuspShellGammaCoreRemainderSpectralDerivative
      (-((b : ℂ) - (a : ℂ) * I)) n).re := by
  have hreflect :
      -((b : ℂ) - (a : ℂ) * I) =
        ((-b : ℝ) : ℂ) - ((-a : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hreflect,
    thetaCuspShellGammaCoreRemainderSpectralDerivative_re_eq_of_neg_one_lt_of_ne
      (a := -a) (b := -b) (by linarith) (by linarith)
      (neg_ne_zero.mpr hb.ne') (lt_of_lt_of_le (by norm_num) hn)]
  have hmoment :=
    integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
      (a := -a) (b := b) (by linarith) hb hn
  rw [show
      (fun x : ℝ =>
        x * thetaCuspTiltedWardDensity (-a) n x *
          Real.sin ((-b) * x)) =
      fun x =>
        -(x * thetaCuspTiltedWardDensity (-a) n x *
          Real.sin (b * x)) by
        funext x
        rw [neg_mul, Real.sin_neg]
        ring,
    integral_neg]
  nlinarith

/-- **Four-direction higher-shell cone.**  At a critical-aperture positive frequency, the
unreflected remainder is in quadrant I and points left, while its reflected partner is in
quadrant IV and points right. -/
theorem thetaCuspHigherShellGammaFourDirectionalCone
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 0 < b) {n : ℕ} (hn : 2 ≤ n) :
    0 < (thetaCuspShellGammaCoreRemainder
        ((b : ℂ) - (a : ℂ) * I) n).re ∧
    0 < (thetaCuspShellGammaCoreRemainder
        ((b : ℂ) - (a : ℂ) * I) n).im ∧
    (thetaCuspShellGammaCoreRemainderSpectralDerivative
        ((b : ℂ) - (a : ℂ) * I) n).re < 0 ∧
    0 < (thetaCuspShellGammaCoreRemainder
        (-((b : ℂ) - (a : ℂ) * I)) n).re ∧
    (thetaCuspShellGammaCoreRemainder
        (-((b : ℂ) - (a : ℂ) * I)) n).im < 0 ∧
    0 < (thetaCuspShellGammaCoreRemainderSpectralDerivative
        (-((b : ℂ) - (a : ℂ) * I)) n).re := by
  refine ⟨
    thetaCuspShellGammaCoreRemainder_re_pos_of_two_le ha0 ha hb hn,
    thetaCuspShellGammaCoreRemainder_im_pos ha0 ha hb
      (lt_of_lt_of_le (by norm_num) hn),
    thetaCuspShellGammaCoreRemainderSpectralDerivative_re_neg_of_two_le
      ha0 ha hb hn,
    thetaCuspShellGammaCoreRemainder_reflected_re_pos_of_two_le
      ha0 ha hb hn,
    thetaCuspShellGammaCoreRemainder_reflected_im_neg
      ha0 ha hb (lt_of_lt_of_le (by norm_num) hn),
    thetaCuspShellGammaCoreRemainderSpectralDerivative_reflected_re_pos_of_two_le
      ha0 ha hb hn⟩

/-- The signed one-transition rotation density nevertheless has a strictly positive transform
against `1-cos` for every higher shell and every positive frequency. -/
theorem integral_thetaCuspTiltedWardDerivativeRotationDensity_mul_one_sub_cos_pos_of_two_le
    {a b : ℝ} (ha : a < 1 / 2) (hb : 0 < b)
    {n : ℕ} (hn : 2 ≤ n) :
    0 < ∫ x : ℝ in Ioi 0,
      thetaCuspTiltedWardDerivativeRotationDensity a n x *
        (1 - Real.cos (b * x)) := by
  rw [←
    integral_thetaCuspTiltedWardDerivativeRotationDensity_mul_one_sub_cos
      (by linarith) (lt_of_lt_of_le (by norm_num) hn)]
  exact mul_pos hb
    (integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
      ha hb hn)

/-- Cayley transform centered at a point of the open upper half-plane. -/
def upperHalfPlaneCayleyAt (c w : ℂ) : ℂ :=
  (w - c) / (w - (starRingEnd ℂ) c)

theorem norm_upperHalfPlaneCayleyAt_le_one
    {c w : ℂ} (hc : 0 < c.im) (hw : 0 < w.im) :
    ‖upperHalfPlaneCayleyAt c w‖ ≤ 1 := by
  have hden : w - (starRingEnd ℂ) c ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [sub_im, conj_im, sub_neg_eq_add] at him
    norm_num at him
    linarith
  rw [upperHalfPlaneCayleyAt, norm_div,
    div_le_one (norm_pos_iff.mpr hden)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, conj_re, sub_im, conj_im]
  nlinarith

/-- Local Schwarz--Pick estimate requiring only a Euclidean ball mapped into the upper half-plane.
This deliberately exposes the factor `2`: the globally sharp half-plane metric is unnecessary
for the shell application. -/
theorem upperHalfPlane_local_derivative_bound
    {f : ℂ → ℂ} {u f' : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hpos : ∀ v ∈ Metric.ball u r, 0 < (f v).im)
    (hdiff : DifferentiableOn ℂ f (Metric.ball u r))
    (hderiv : HasDerivAt f f' u) :
    r * ‖f'‖ ≤ 2 * (f u).im := by
  let c : ℂ := f u
  let g : ℂ → ℂ := fun v =>
    upperHalfPlaneCayleyAt c (f v)
  have hu : u ∈ Metric.ball u r :=
    Metric.mem_ball_self hr
  have hc : 0 < c.im := hpos u hu
  have hden (v : ℂ) (hv : v ∈ Metric.ball u r) :
      f v - (starRingEnd ℂ) c ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [sub_im, conj_im, sub_neg_eq_add] at him
    norm_num at him
    have hvpos := hpos v hv
    linarith
  have hgdiff :
      DifferentiableOn ℂ g (Metric.ball u r) := by
    intro v hv
    dsimp only [g, upperHalfPlaneCayleyAt]
    exact ((hdiff v hv).sub_const c).div
      ((hdiff v hv).sub_const ((starRingEnd ℂ) c))
      (hden v hv)
  have hmaps :
      MapsTo g (Metric.ball u r)
        (Metric.closedBall (g u) 1) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hgu : g u = 0 := by
      dsimp only [g, upperHalfPlaneCayleyAt, c]
      simp only [sub_self, zero_div]
    rw [hgu, sub_zero]
    exact norm_upperHalfPlaneCayleyAt_le_one
      hc (hpos v hv)
  have hschwarz :=
    Complex.norm_deriv_le_div_of_mapsTo_ball
      hgdiff hmaps hr
  have hcg : HasDerivAt g
      (f' / (c - (starRingEnd ℂ) c)) u := by
    have hnum := hderiv.sub_const c
    have hdenDeriv :=
      hderiv.sub_const ((starRingEnd ℂ) c)
    convert hnum.div hdenDeriv (hden u hu) using 1
    · dsimp only [c]
      simp only [sub_self, zero_mul, sub_zero]
      field_simp [hden u hu]
  rw [hcg.deriv] at hschwarz
  have hcden :
      ‖c - (starRingEnd ℂ) c‖ = 2 * c.im := by
    rw [show c - (starRingEnd ℂ) c =
        (2 * c.im : ℝ) * I by
      apply Complex.ext <;> simp <;> ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hc),
      norm_I, mul_one]
  rw [norm_div, hcden] at hschwarz
  have hc2 : 0 < 2 * c.im :=
    mul_pos (by norm_num) hc
  have hbound : ‖f'‖ ≤ (2 * c.im) / r := by
    apply (le_div_iff₀ hr).2
    have hcross :=
      (div_le_div_iff₀ hc2 hr).mp hschwarz
    simpa only [one_mul] using hcross
  rw [show c.im = (f u).im by rfl] at hbound
  have hcross := (le_div_iff₀ hr).mp hbound
  simpa only [mul_comm] using hcross

/-- Shifted Gamma remainder maps the open first quadrant into the upper half-plane. -/
theorem thetaCuspShellGammaCoreRemainder_shift_im_pos
    {u : ℂ} (hre : 0 < u.re) (him : 0 < u.im)
    (him1 : u.im < 1) {n : ℕ} (hn : 0 < n) :
    0 < (thetaCuspShellGammaCoreRemainder
      (u - I / 2) n).im := by
  have hz :
      u - I / 2 =
        ((u.re : ℝ) : ℂ) -
          (((1 / 2 : ℝ) - u.im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.div_re]
    · simp [Complex.mul_im, Complex.div_im]
  rw [hz]
  exact thetaCuspShellGammaCoreRemainder_im_pos_of_neg_one_lt
    (by linarith) (by linarith) hre hn

/-- **Ward--Schwarz derivative cone.**  The positive-density sector law plus holomorphy forces
a quantitative joint bound on the incomplete-Gamma remainder and its spectral derivative.
This is uniform in shell number and uses no asymptotic expansion. -/
theorem norm_thetaCuspShellGammaCoreRemainderSpectralDerivative_le_im
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hbradius : 1 / 2 - a < b)
    {n : ℕ} (hn : 0 < n) :
    (1 / 2 - a) *
        ‖thetaCuspShellGammaCoreRemainderSpectralDerivative
          ((b : ℂ) - (a : ℂ) * I) n‖ ≤
      2 * (thetaCuspShellGammaCoreRemainder
        ((b : ℂ) - (a : ℂ) * I) n).im := by
  let r : ℝ := 1 / 2 - a
  let u : ℂ := (b : ℂ) + (r : ℂ) * I
  let f : ℂ → ℂ := fun v =>
    thetaCuspShellGammaCoreRemainder
      (v - I / 2) n
  let f' : ℂ :=
    thetaCuspShellGammaCoreRemainderSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hrb : r < b := by
    simpa only [r] using hbradius
  have hrtwo : 2 * r < 1 := by
    dsimp only [r]
    linarith
  have hub : u - I / 2 =
      (b : ℂ) - (a : ℂ) * I := by
    dsimp only [u, r]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hball (v : ℂ) (hv : v ∈ Metric.ball u r) :
      0 < v.re ∧ 0 < v.im ∧ v.im < 1 := by
    have hdist : ‖v - u‖ < r := by
      simpa only [mem_ball_iff_norm] using hv
    have hrele : |v.re - u.re| ≤ ‖v - u‖ := by
      simpa only [Complex.sub_re] using
        Complex.abs_re_le_norm (v - u)
    have himle : |v.im - u.im| ≤ ‖v - u‖ := by
      simpa only [Complex.sub_im] using
        Complex.abs_im_le_norm (v - u)
    have hreLower := (abs_le.mp hrele).1
    have himLower := (abs_le.mp himle).1
    have himUpper := (abs_le.mp himle).2
    have hure : u.re = b := by simp [u]
    have huim : u.im = r := by simp [u]
    rw [hure] at hreLower
    rw [huim] at himLower himUpper
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  have hpos : ∀ v ∈ Metric.ball u r,
      0 < (f v).im := by
    intro v hv
    rcases hball v hv with ⟨hvre, hvim, hvim1⟩
    exact thetaCuspShellGammaCoreRemainder_shift_im_pos
      hvre hvim hvim1 hn
  have hdiff :
      DifferentiableOn ℂ f (Metric.ball u r) := by
    intro v hv
    rcases hball v hv with ⟨_hvre, hvim, hvim1⟩
    have hzstrip : |(v - I / 2).im| < 1 := by
      have himshift :
          (v - I / 2).im = v.im - 1 / 2 := by
        simp [Complex.div_im]
      rw [himshift]
      rw [abs_lt]
      constructor <;> linarith
    have hshift : HasDerivAt
        (fun w : ℂ => w - I / 2) 1 v := by
      convert (hasDerivAt_id v).sub_const (I / 2)
        using 1 <;> ring
    simpa only [Function.comp_apply] using
      ((hasDerivAt_thetaCuspShellGammaCoreRemainder
        hzstrip hn).comp v hshift).differentiableAt.differentiableWithinAt
  have hderiv : HasDerivAt f f' u := by
    have hzstrip :
        |(((b : ℂ) - (a : ℂ) * I).im)| < 1 := by
      simp only [sub_im, ofReal_im, mul_im, ofReal_re,
        I_re, I_im, zero_sub, zero_mul, mul_one]
      rw [abs_neg]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    have hshift : HasDerivAt
        (fun w : ℂ => w - I / 2) 1 u := by
      convert (hasDerivAt_id u).sub_const (I / 2)
        using 1 <;> ring
    have hzstripU : |(u - I / 2).im| < 1 := by
      rw [hub]
      exact hzstrip
    have hcomp :=
      (hasDerivAt_thetaCuspShellGammaCoreRemainder
        hzstripU hn).comp u hshift
    simpa only [f, f', Function.comp_apply, hub,
      mul_one] using hcomp
  have hbound :=
    upperHalfPlane_local_derivative_bound
      hr hpos hdiff hderiv
  simpa only [r, f, f', hub] using hbound

/-- The Ward--Schwarz derivative cone applies automatically on the unresolved Hedenmalm
high-frequency region. -/
theorem norm_thetaCuspShellGammaCoreRemainderSpectralDerivative_le_im_highFrequency
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hb : 218 / 25 < b)
    {n : ℕ} (hn : 0 < n) :
    (1 / 2 - a) *
        ‖thetaCuspShellGammaCoreRemainderSpectralDerivative
          ((b : ℂ) - (a : ℂ) * I) n‖ ≤
      2 * (thetaCuspShellGammaCoreRemainder
        ((b : ℂ) - (a : ℂ) * I) n).im := by
  exact
    norm_thetaCuspShellGammaCoreRemainderSpectralDerivative_le_im
      ha0 ha (by norm_num at hb ⊢; linarith) hn

/-- The actual even shell value is two real Gaussian boundaries plus the two reflected base
incomplete-Gamma remainders. -/
theorem thetaCuspShellEvenPhaseValue_eq_gammaRemainders
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    thetaCuspShellEvenPhaseValue z n =
      2 * thetaCuspShellGammaBoundary n +
        Real.pi * (I * z - 1 / 2) *
          thetaCuspShellGammaCoreRemainder z n +
        Real.pi * (I * (-z) - 1 / 2) *
          thetaCuspShellGammaCoreRemainder (-z) n := by
  have hplus :
      IntegrableOn
        (fun x : ℝ =>
          (thetaCuspSourceTerm x n : ℂ) *
            spectralTranslationPhase x z) (Ioi 0) :=
    integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im
      hn (abs_lt.mp hz).1
  have hminus :
      IntegrableOn
        (fun x : ℝ =>
          (thetaCuspSourceTerm x n : ℂ) *
            spectralTranslationPhase x (-z)) (Ioi 0) := by
    apply integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im hn
    simpa only [neg_im] using (neg_lt_neg (abs_lt.mp hz).2)
  have hsplit :
      thetaCuspShellEvenPhaseValue z n =
        thetaCuspShellHalfLineTransform
            (fun x => spectralTranslationPhase x z) n +
          thetaCuspShellHalfLineTransform
            (fun x => spectralTranslationPhase x (-z)) n := by
    unfold thetaCuspShellEvenPhaseValue thetaCuspShellHalfLineTransform
      thetaCuspTailSecondDensityEvenPhase
    rw [show
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          (spectralTranslationPhase x z +
            spectralTranslationPhase x (-z))) =
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          spectralTranslationPhase x z) +
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          spectralTranslationPhase x (-z)) by
        funext x
        simp only [Pi.add_apply]
        ring]
    simpa only [Pi.add_apply] using integral_add hplus hminus
  rw [hsplit,
    thetaCuspShellPhaseTransform_eq_gammaBoundary_add hz hn,
    thetaCuspShellPhaseTransform_eq_gammaBoundary_add
      (z := -z) (by simpa only [neg_im, abs_neg] using hz) hn]
  push_cast
  ring

/-- The existing shell spectral-derivative value is the actual derivative of the existing shell
value.  This closes the analytic connector needed by the Hedenmalm shell current. -/
theorem hasDerivAt_thetaCuspShellEvenPhaseValue
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun w => thetaCuspShellEvenPhaseValue w n)
      (thetaCuspShellEvenPhaseSpectralDerivativeValue z n) z := by
  let S : ℂ → ℂ := fun w =>
    thetaCuspShellHalfLineTransform
      (fun x => spectralTranslationPhase x w) n
  let D : ℂ → ℂ := fun w =>
    thetaCuspShellHalfLineTransform
      (fun x => ((x : ℂ) * I) *
        spectralTranslationPhase x w) n
  have hplus : HasDerivAt S (D z) z := by
    simpa only [S, D] using
      hasDerivAt_thetaCuspShellPhaseTransform
        (z₀ := z) (abs_lt.mp hz).1 hn
  have hminusBase : HasDerivAt S (D (-z)) (-z) := by
    simpa only [S, D] using
      hasDerivAt_thetaCuspShellPhaseTransform
        (z₀ := -z) (by
          simpa only [neg_im] using
            neg_lt_neg (abs_lt.mp hz).2) hn
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
    convert (hasDerivAt_id z).neg using 1 <;> ring
  have hsum :
      HasDerivAt (fun w => S w + S (-w))
        (D z - D (-z)) z := by
    convert hplus.add (hminusBase.comp z hneg) using 1 <;> ring
  have hD :
      thetaCuspShellEvenPhaseSpectralDerivativeValue z n =
        D z - D (-z) := by
    have hDplus :=
      integrableOn_thetaCuspSourceTerm_mul_phaseSpectralDerivative
        hz n
    have hDminus :=
      integrableOn_thetaCuspSourceTerm_mul_phaseSpectralDerivative
        (z := -z) (by
          simpa only [neg_im, abs_neg] using hz) n
    unfold thetaCuspShellEvenPhaseSpectralDerivativeValue
      thetaCuspTailSecondDensityEvenPhaseSpectralDerivative
      thetaCuspShellHalfLineTransform
    dsimp only [D]
    rw [show
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          ((x : ℂ) * I *
            (spectralTranslationPhase x z -
              spectralTranslationPhase x (-z)))) =
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x z)) -
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          (((x : ℂ) * I) *
            spectralTranslationPhase x (-z))) by
        funext x
        simp only [Pi.sub_apply]
        ring]
    simpa only [Pi.sub_apply, thetaCuspShellHalfLineTransform] using
      integral_sub hDplus hDminus
  rw [hD]
  apply hsum.congr_of_eventuallyEq
  have hmem : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact abs_lt.mp hz
  filter_upwards
    [isOpen_thetaCuspFourierLaplaceStrip.mem_nhds hmem] with w hw
  have hwabs : |w.im| < 1 := by
    rw [thetaCuspFourierLaplaceStrip] at hw
    exact abs_lt.mpr hw
  have hwplus :
      IntegrableOn
        (fun x : ℝ =>
          (thetaCuspSourceTerm x n : ℂ) *
            spectralTranslationPhase x w) (Ioi 0) :=
    integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im
      hn (abs_lt.mp hwabs).1
  have hwminus :
      IntegrableOn
        (fun x : ℝ =>
          (thetaCuspSourceTerm x n : ℂ) *
            spectralTranslationPhase x (-w)) (Ioi 0) := by
    apply
      integrableOn_thetaCuspSourceTerm_mul_phase_of_neg_one_lt_im
        hn
    simpa only [neg_im] using neg_lt_neg (abs_lt.mp hwabs).2
  unfold thetaCuspShellEvenPhaseValue
    thetaCuspTailSecondDensityEvenPhase
    thetaCuspShellHalfLineTransform
  dsimp only [S]
  rw [show
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          (spectralTranslationPhase x w +
            spectralTranslationPhase x (-w))) =
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          spectralTranslationPhase x w) +
      (fun x : ℝ =>
        (thetaCuspSourceTerm x n : ℂ) *
          spectralTranslationPhase x (-w)) by
        funext x
        simp only [Pi.add_apply]
        ring]
  simpa only [Pi.add_apply] using integral_add hwplus hwminus

/-- Explicit Gamma-coordinate derivative of one actual even shell. -/
def thetaCuspShellEvenGammaSpectralDerivative
    (z : ℂ) (n : ℕ) : ℂ :=
  Real.pi *
      (I * thetaCuspShellGammaCoreRemainder z n +
        (I * z - 1 / 2) *
          thetaCuspShellGammaCoreRemainderSpectralDerivative z n) -
    Real.pi *
      (I * thetaCuspShellGammaCoreRemainder (-z) n +
        (I * (-z) - 1 / 2) *
          thetaCuspShellGammaCoreRemainderSpectralDerivative (-z) n)

/-- Exact real component of the actual reflected shell derivative.  The only components not
fixed by the higher-shell quadrant/rotation theorems are the two transverse imaginary
derivatives. -/
theorem thetaCuspShellEvenGammaSpectralDerivative_re_at_tilt
    (a b : ℝ) (n : ℕ) :
    (thetaCuspShellEvenGammaSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).re =
      Real.pi *
        (-(thetaCuspShellGammaCoreRemainder
              ((b : ℂ) - (a : ℂ) * I) n).im +
          (a - 1 / 2) *
            (thetaCuspShellGammaCoreRemainderSpectralDerivative
              ((b : ℂ) - (a : ℂ) * I) n).re -
          b *
            (thetaCuspShellGammaCoreRemainderSpectralDerivative
              ((b : ℂ) - (a : ℂ) * I) n).im +
          (thetaCuspShellGammaCoreRemainder
              (-((b : ℂ) - (a : ℂ) * I)) n).im +
          (a + 1 / 2) *
            (thetaCuspShellGammaCoreRemainderSpectralDerivative
              (-((b : ℂ) - (a : ℂ) * I)) n).re -
          b *
            (thetaCuspShellGammaCoreRemainderSpectralDerivative
              (-((b : ℂ) - (a : ℂ) * I)) n).im) := by
  simp [thetaCuspShellEvenGammaSpectralDerivative,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Exact imaginary component of the actual reflected shell derivative. -/
theorem thetaCuspShellEvenGammaSpectralDerivative_im_at_tilt
    (a b : ℝ) (n : ℕ) :
    (thetaCuspShellEvenGammaSpectralDerivative
      ((b : ℂ) - (a : ℂ) * I) n).im =
      Real.pi *
        ((thetaCuspShellGammaCoreRemainder
              ((b : ℂ) - (a : ℂ) * I) n).re -
          (thetaCuspShellGammaCoreRemainder
              (-((b : ℂ) - (a : ℂ) * I)) n).re +
          b *
            ((thetaCuspShellGammaCoreRemainderSpectralDerivative
                ((b : ℂ) - (a : ℂ) * I) n).re +
              (thetaCuspShellGammaCoreRemainderSpectralDerivative
                (-((b : ℂ) - (a : ℂ) * I)) n).re) +
          (a - 1 / 2) *
            (thetaCuspShellGammaCoreRemainderSpectralDerivative
              ((b : ℂ) - (a : ℂ) * I) n).im +
          (a + 1 / 2) *
            (thetaCuspShellGammaCoreRemainderSpectralDerivative
              (-((b : ℂ) - (a : ℂ) * I)) n).im) := by
  simp [thetaCuspShellEvenGammaSpectralDerivative,
    Complex.mul_re, Complex.mul_im]
  ring

/-- **Actual-current Gamma derivative law.**  The derivative used by the corpus Hedenmalm current
is exactly the reflected incomplete-Gamma remainder derivative.  Both extracted Gaussian
boundaries disappear because they are spectrally constant. -/
theorem thetaCuspShellEvenPhaseSpectralDerivativeValue_eq_gamma
    {z : ℂ} (hz : |z.im| < 1) {n : ℕ} (hn : 0 < n) :
    thetaCuspShellEvenPhaseSpectralDerivativeValue z n =
      thetaCuspShellEvenGammaSpectralDerivative z n := by
  have hleft :=
    hasDerivAt_thetaCuspShellEvenPhaseValue hz hn
  have hRplus :=
    hasDerivAt_thetaCuspShellGammaCoreRemainder hz hn
  have hRminusBase :=
    hasDerivAt_thetaCuspShellGammaCoreRemainder
      (z := -z) (by simpa only [neg_im, abs_neg] using hz) hn
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
    convert (hasDerivAt_id z).neg using 1 <;> ring
  have hRminus :=
    hRminusBase.comp z hneg
  have hcplus :
      HasDerivAt (fun w : ℂ => I * w - 1 / 2) I z := by
    convert ((hasDerivAt_id z).const_mul I).sub_const
      (1 / 2 : ℂ) using 1 <;> ring
  have hcminus :
      HasDerivAt (fun w : ℂ => I * (-w) - 1 / 2) (-I) z := by
    convert (hneg.const_mul I).sub_const (1 / 2 : ℂ)
      using 1 <;> ring
  have hright :
      HasDerivAt
        (fun w : ℂ =>
          2 * (thetaCuspShellGammaBoundary n : ℂ) +
            Real.pi * (I * w - 1 / 2) *
              thetaCuspShellGammaCoreRemainder w n +
            Real.pi * (I * (-w) - 1 / 2) *
              thetaCuspShellGammaCoreRemainder (-w) n)
        (thetaCuspShellEvenGammaSpectralDerivative z n) z := by
    have hconst :
        HasDerivAt
          (fun _w : ℂ =>
            2 * (thetaCuspShellGammaBoundary n : ℂ)) 0 z :=
      hasDerivAt_const z _
    have hp :=
      (hcplus.mul hRplus).const_mul (Real.pi : ℂ)
    have hm :=
      (hcminus.mul hRminus).const_mul (Real.pi : ℂ)
    convert hconst.add (hp.add hm) using 1
    · funext w
      simp [thetaCuspShellEvenGammaSpectralDerivative]
      ring
    · simp [thetaCuspShellEvenGammaSpectralDerivative]
      ring
  have hmem : z ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact abs_lt.mp hz
  have heq :
      (fun w => thetaCuspShellEvenPhaseValue w n) =ᶠ[nhds z]
      (fun w : ℂ =>
        2 * (thetaCuspShellGammaBoundary n : ℂ) +
          Real.pi * (I * w - 1 / 2) *
            thetaCuspShellGammaCoreRemainder w n +
          Real.pi * (I * (-w) - 1 / 2) *
            thetaCuspShellGammaCoreRemainder (-w) n) := by
    filter_upwards
      [isOpen_thetaCuspFourierLaplaceStrip.mem_nhds hmem] with w hw
    have hwabs : |w.im| < 1 := by
      rw [thetaCuspFourierLaplaceStrip] at hw
      exact abs_lt.mpr hw
    exact thetaCuspShellEvenPhaseValue_eq_gammaRemainders
      hwabs hn
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

/-- One ordered shell-pair contribution to the actual Hedenmalm current, entirely in the
incomplete-Gamma remainder coordinate. -/
theorem thetaCuspShellPairHedenmalmCurrent_eq_gamma
    {z : ℂ} (hz : |z.im| < 1)
    {q : ℕ × ℕ} (hq1 : 0 < q.1) (hq2 : 0 < q.2) :
    thetaCuspShellPairHedenmalmCurrent z q =
      2 * (thetaCuspShellEvenGammaSpectralDerivative z q.1 *
        (starRingEnd ℂ)
          (2 * thetaCuspShellGammaBoundary q.2 +
            Real.pi * (I * z - 1 / 2) *
              thetaCuspShellGammaCoreRemainder z q.2 +
            Real.pi * (I * (-z) - 1 / 2) *
              thetaCuspShellGammaCoreRemainder (-z) q.2)).im := by
  rw [thetaCuspShellPairHedenmalmCurrent,
    thetaCuspShellEvenPhaseSpectralDerivativeValue_eq_gamma hz hq1,
    thetaCuspShellEvenPhaseValue_eq_gammaRemainders hz hq2]

end

end RHTower
