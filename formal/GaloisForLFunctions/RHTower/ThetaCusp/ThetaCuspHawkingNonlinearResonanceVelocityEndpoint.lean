import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingNonlinearDivisorTransportEndpoint
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# Exact nonlinear Hawking resonance velocity

This endpoint differentiates the actual Davies--Fulling theta-mirror eikonal susceptibility in
joint complex background coupling and complex total frequency. At every simple Xi resonance, the
complex implicit-function theorem produces a local nonlinear resonance branch with exact velocity

`i * M₂(a,w) / XiC'(w + i a)`.

No sign or simplicity premise is globalized. The closed classification says every spectral point
is nonresonant, a degenerate Xi zero, or admits this source-faithful branch. Real and imaginary
velocity components isolate the remaining orientation producer as the phase of `M₂ / XiC'`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal SchwartzMap

noncomputable section

namespace RHTower

open HedenmalmThetaSource

def thetaCuspHawkingComplexNonlinearPhase (a : ℝ) (p : ℂ × ℂ) (x : ℝ) : ℂ :=
  -Complex.I * p.2 * (x : ℂ) +
    -Complex.I * p.1 * (thetaCuspTiltedSource a x : ℂ)

def thetaCuspHawkingComplexNonlinearCarrierIntegrand (a : ℝ) (p : ℂ × ℂ) (x : ℝ) : ℂ :=
  Complex.exp (thetaCuspHawkingComplexNonlinearPhase a p x) *
    (-Complex.I * (thetaCuspTiltedSource a x : ℂ))

def thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand (a : ℝ) (p : ℂ × ℂ) (x : ℝ) :
    (ℂ × ℂ) →L[ℂ] ℂ :=
  (-Complex.I * (thetaCuspTiltedSource a x : ℂ)) •
    Complex.exp (thetaCuspHawkingComplexNonlinearPhase a p x) •
      (((-Complex.I * (x : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ) +
        ((-Complex.I * (thetaCuspTiltedSource a x : ℂ)) •
          ContinuousLinearMap.fst ℂ ℂ ℂ))

private theorem hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrierIntegrand (a : ℝ) (p : ℂ × ℂ) (x : ℝ) :
    HasFDerivAt (fun q : ℂ × ℂ => thetaCuspHawkingComplexNonlinearCarrierIntegrand a q x)
      (thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a p x) p := by
  have hz : HasFDerivAt
      (fun q : ℂ × ℂ => -Complex.I * q.2 * (x : ℂ))
      ((-Complex.I * (x : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
    have hsnd : HasFDerivAt (fun q : ℂ × ℂ => q.2)
        (ContinuousLinearMap.snd ℂ ℂ ℂ) p := hasFDerivAt_snd
    have hraw := (hsnd.const_mul (-Complex.I)).mul_const (x : ℂ)
    exact hraw.congr_fderiv (by
      rw [smul_smul]
      congr 1
      ring)
  have ht : HasFDerivAt
      (fun q : ℂ × ℂ => -Complex.I * q.1 *
        (thetaCuspTiltedSource a x : ℂ))
      ((-Complex.I * (thetaCuspTiltedSource a x : ℂ)) •
        ContinuousLinearMap.fst ℂ ℂ ℂ) p := by
    have hfst : HasFDerivAt (fun q : ℂ × ℂ => q.1)
        (ContinuousLinearMap.fst ℂ ℂ ℂ) p := hasFDerivAt_fst
    have hraw := (hfst.const_mul (-Complex.I)).mul_const
      (thetaCuspTiltedSource a x : ℂ)
    exact hraw.congr_fderiv (by
      rw [smul_smul]
      congr 1
      ring)
  have h := (hz.add ht).cexp.mul_const
    (-Complex.I * (thetaCuspTiltedSource a x : ℂ))
  simpa only [thetaCuspHawkingComplexNonlinearCarrierIntegrand, thetaCuspHawkingComplexNonlinearPhase, thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand, Pi.add_apply] using h

def thetaCuspHawkingComplexNonlinearCarrier (a : ℝ) (tau z : ℂ) : ℂ :=
  ∫ x : ℝ, thetaCuspHawkingComplexNonlinearCarrierIntegrand a (tau, z) x

def thetaCuspHawkingComplexNonlinearCarrierFDeriv (a : ℝ) (p : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  ∫ x : ℝ, thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a p x

private def thetaCuspHawkingComplexNonlinearSourceBound (a : ℝ) (ha : |a| < 1) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (thetaCuspTiltedSchwartzReal a ha)

private theorem thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspTiltedSource a x ∈ Set.Icc 0 (thetaCuspHawkingComplexNonlinearSourceBound a ha) := by
  constructor
  · unfold thetaCuspTiltedSource
    exact (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)).le
  · let source : SchwartzMap ℝ ℝ := thetaCuspTiltedSchwartzReal a ha
    have hpos : 0 < thetaCuspTiltedSource a x := by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
    have hnorm := SchwartzMap.norm_le_seminorm ℝ source x
    simpa [source, thetaCuspHawkingComplexNonlinearSourceBound, Real.norm_eq_abs, abs_of_pos hpos] using hnorm

private theorem norm_thetaCuspHawkingComplexNonlinearCarrierIntegrand (a : ℝ) (p : ℂ × ℂ) (x : ℝ) :
    ‖thetaCuspHawkingComplexNonlinearCarrierIntegrand a p x‖ =
      Real.exp (p.2.im * x + p.1.im * thetaCuspTiltedSource a x) *
        thetaCuspTiltedSource a x := by
  rw [thetaCuspHawkingComplexNonlinearCarrierIntegrand, norm_mul, Complex.norm_exp, norm_mul, norm_neg, norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hk : 0 < thetaCuspTiltedSource a x := by
    unfold thetaCuspTiltedSource
    exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
  rw [abs_of_pos hk]
  congr 2
  simp [thetaCuspHawkingComplexNonlinearPhase, Complex.mul_re]

private def thetaCuspHawkingComplexNonlinearCarrierLocalMajorant
    (a : ℝ) (ha : |a| < 1) (p₀ : ℂ × ℂ) (x : ℝ) : ℝ :=
  Real.exp ((|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha) *
    (Real.exp ((|p₀.2.im| + 1 + |a|) * |x|) * thetaCuspFullSource x)

private def thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant
    (a : ℝ) (ha : |a| < 1) (p₀ : ℂ × ℂ) (x : ℝ) : ℝ :=
  Real.exp ((|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha) *
    (thetaCuspHawkingComplexNonlinearSourceBound a ha *
        (Real.exp ((|p₀.2.im| + 1 + |a|) * |x|) * thetaCuspFullSource x) +
      |x| * Real.exp ((|p₀.2.im| + 1 + |a|) * |x|) *
        thetaCuspFullSource x)

private theorem integrable_thetaCuspHawkingComplexNonlinearCarrierLocalMajorant
    (a : ℝ) (ha : |a| < 1) (p₀ : ℂ × ℂ) :
    Integrable (thetaCuspHawkingComplexNonlinearCarrierLocalMajorant a ha p₀) := by
  exact (integrable_exp_abs_mul_thetaCuspFullSource
    (|p₀.2.im| + 1 + |a|)).const_mul
      (Real.exp ((|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha))

private theorem integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant
    (a : ℝ) (ha : |a| < 1) (p₀ : ℂ × ℂ) :
    Integrable (thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p₀) := by
  have h0 := (integrable_exp_abs_mul_thetaCuspFullSource
    (|p₀.2.im| + 1 + |a|)).const_mul (thetaCuspHawkingComplexNonlinearSourceBound a ha)
  have h1 := integrable_abs_mul_exp_abs_mul_thetaCuspFullSource
    (|p₀.2.im| + 1 + |a|)
  exact (h0.add h1).const_mul
    (Real.exp ((|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha))

private theorem norm_thetaCuspHawkingComplexNonlinearCarrierIntegrand_le
    (a : ℝ) (ha : |a| < 1) (p₀ p : ℂ × ℂ) (x : ℝ)
    (hp : p ∈ Metric.ball p₀ 1) :
    ‖thetaCuspHawkingComplexNonlinearCarrierIntegrand a p x‖ ≤ thetaCuspHawkingComplexNonlinearCarrierLocalMajorant a ha p₀ x := by
  have hdist : ‖p - p₀‖ < 1 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hp
  have htDiff : |p.1.im - p₀.1.im| ≤ ‖p - p₀‖ := by
    calc
      |p.1.im - p₀.1.im| ≤ ‖p.1 - p₀.1‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (p.1 - p₀.1)
      _ ≤ ‖p - p₀‖ := by
        simpa only [Prod.fst_sub] using norm_fst_le (p - p₀)
  have hzDiff : |p.2.im - p₀.2.im| ≤ ‖p - p₀‖ := by
    calc
      |p.2.im - p₀.2.im| ≤ ‖p.2 - p₀.2‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (p.2 - p₀.2)
      _ ≤ ‖p - p₀‖ := by
        simpa only [Prod.snd_sub] using norm_snd_le (p - p₀)
  have ht : |p.1.im| ≤ |p₀.1.im| + 1 := by
    calc
      |p.1.im| = |p₀.1.im + (p.1.im - p₀.1.im)| := by ring_nf
      _ ≤ |p₀.1.im| + |p.1.im - p₀.1.im| := abs_add_le _ _
      _ ≤ |p₀.1.im| + 1 := by linarith
  have hz : |p.2.im| ≤ |p₀.2.im| + 1 := by
    calc
      |p.2.im| = |p₀.2.im + (p.2.im - p₀.2.im)| := by ring_nf
      _ ≤ |p₀.2.im| + |p.2.im - p₀.2.im| := abs_add_le _ _
      _ ≤ |p₀.2.im| + 1 := by linarith
  have hk0 := (thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound a ha x).1
  have hkM := (thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound a ha x).2
  have hzx : p.2.im * x ≤ |p.2.im| * |x| := by
    simpa [abs_mul] using le_abs_self (p.2.im * x)
  have htk : p.1.im * thetaCuspTiltedSource a x ≤
      |p.1.im| * thetaCuspTiltedSource a x :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hk0
  have hax : a * x ≤ |a| * |x| := by
    simpa [abs_mul] using le_abs_self (a * x)
  have hexp :
      p.2.im * x + p.1.im * thetaCuspTiltedSource a x + a * x ≤
        (|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha +
          (|p₀.2.im| + 1 + |a|) * |x| := by
    calc
      p.2.im * x + p.1.im * thetaCuspTiltedSource a x + a * x ≤
          |p.2.im| * |x| + |p.1.im| * thetaCuspTiltedSource a x +
            |a| * |x| := add_le_add (add_le_add hzx htk) hax
      _ ≤ (|p₀.2.im| + 1) * |x| +
            (|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha + |a| * |x| := by
        gcongr
      _ = (|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha +
          (|p₀.2.im| + 1 + |a|) * |x| := by ring
  rw [norm_thetaCuspHawkingComplexNonlinearCarrierIntegrand, thetaCuspTiltedSource]
  dsimp only [thetaCuspHawkingComplexNonlinearCarrierLocalMajorant]
  calc
      Real.exp (p.2.im * x + p.1.im *
        (Real.exp (a * x) * thetaCuspFullSource x)) *
        (Real.exp (a * x) * thetaCuspFullSource x) =
      Real.exp (p.2.im * x + p.1.im * thetaCuspTiltedSource a x + a * x) *
        thetaCuspFullSource x := by
          simp only [Real.exp_add, thetaCuspTiltedSource]
          ring
    _ ≤ Real.exp ((|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha +
          (|p₀.2.im| + 1 + |a|) * |x|) * thetaCuspFullSource x := by
      gcongr
      exact (thetaCuspFullSource_pos x).le
    _ = Real.exp ((|p₀.1.im| + 1) * thetaCuspHawkingComplexNonlinearSourceBound a ha) *
        (Real.exp ((|p₀.2.im| + 1 + |a|) * |x|) *
          thetaCuspFullSource x) := by rw [Real.exp_add]; ring

private theorem norm_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand_le
    (a : ℝ) (ha : |a| < 1) (p₀ p : ℂ × ℂ) (x : ℝ)
    (hp : p ∈ Metric.ball p₀ 1) :
    ‖thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a p x‖ ≤ thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p₀ x := by
  have hk0 := (thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound a ha x).1
  have hkM := (thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound a ha x).2
  have hkpos : 0 < thetaCuspTiltedSource a x := by
    unfold thetaCuspTiltedSource
    exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)
  have hraw : ‖thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a p x‖ ≤
      (thetaCuspTiltedSource a x + |x|) * ‖thetaCuspHawkingComplexNonlinearCarrierIntegrand a p x‖ := by
    rw [thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand, thetaCuspHawkingComplexNonlinearCarrierIntegrand, norm_smul, norm_smul, norm_mul,
      norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hkpos]
    calc
      thetaCuspTiltedSource a x * (‖Complex.exp (thetaCuspHawkingComplexNonlinearPhase a p x)‖ *
          ‖(-Complex.I * (x : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ +
            (-Complex.I * (thetaCuspTiltedSource a x : ℂ)) •
              ContinuousLinearMap.fst ℂ ℂ ℂ‖) ≤
        thetaCuspTiltedSource a x * (‖Complex.exp (thetaCuspHawkingComplexNonlinearPhase a p x)‖ *
          (‖(-Complex.I * (x : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ‖ +
            ‖(-Complex.I * (thetaCuspTiltedSource a x : ℂ)) •
              ContinuousLinearMap.fst ℂ ℂ ℂ‖)) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ thetaCuspTiltedSource a x * (‖Complex.exp (thetaCuspHawkingComplexNonlinearPhase a p x)‖ *
          (|x| + thetaCuspTiltedSource a x)) := by
        gcongr
        · calc
            ‖(-Complex.I * (x : ℂ)) • ContinuousLinearMap.snd ℂ ℂ ℂ‖ ≤
                ‖-Complex.I * (x : ℂ)‖ *
                  ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ := by rw [norm_smul]
            _ ≤ |x| := by
              rw [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real,
                Real.norm_eq_abs]
              calc
                |x| * ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ ≤ |x| * 1 :=
                  mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ) (abs_nonneg x)
                _ = |x| := mul_one _
        · calc
            ‖(-Complex.I * (thetaCuspTiltedSource a x : ℂ)) •
                ContinuousLinearMap.fst ℂ ℂ ℂ‖ ≤
              ‖-Complex.I * (thetaCuspTiltedSource a x : ℂ)‖ *
                ‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ := by rw [norm_smul]
            _ ≤ thetaCuspTiltedSource a x := by
              rw [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos hkpos]
              calc
                thetaCuspTiltedSource a x *
                    ‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ ≤
                  thetaCuspTiltedSource a x * 1 := mul_le_mul_of_nonneg_left
                    (ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ) hk0
                _ = thetaCuspTiltedSource a x := mul_one _
      _ = (thetaCuspTiltedSource a x + |x|) *
          (‖Complex.exp (thetaCuspHawkingComplexNonlinearPhase a p x) *
            (-Complex.I * (thetaCuspTiltedSource a x : ℂ))‖) := by
        rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hkpos]
        ring
  calc
    ‖thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a p x‖ ≤
        (thetaCuspTiltedSource a x + |x|) * ‖thetaCuspHawkingComplexNonlinearCarrierIntegrand a p x‖ := hraw
    _ ≤ (thetaCuspHawkingComplexNonlinearSourceBound a ha + |x|) * thetaCuspHawkingComplexNonlinearCarrierLocalMajorant a ha p₀ x := by
      exact mul_le_mul (add_le_add hkM le_rfl)
        (norm_thetaCuspHawkingComplexNonlinearCarrierIntegrand_le a ha p₀ p x hp) (norm_nonneg _)
        (add_nonneg (hk0.trans hkM) (abs_nonneg x))
    _ = thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p₀ x := by
      simp only [thetaCuspHawkingComplexNonlinearCarrierLocalMajorant, thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant]
      ring

private theorem integrable_thetaCuspHawkingComplexNonlinearCarrierIntegrand
    (a : ℝ) (ha : |a| < 1) (p : ℂ × ℂ) :
    Integrable (thetaCuspHawkingComplexNonlinearCarrierIntegrand a p) := by
  apply Integrable.mono (integrable_thetaCuspHawkingComplexNonlinearCarrierLocalMajorant a ha p)
  · apply Continuous.aestronglyMeasurable
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    unfold thetaCuspHawkingComplexNonlinearCarrierIntegrand thetaCuspHawkingComplexNonlinearPhase
    fun_prop
  · filter_upwards with x
    have hmajor : 0 ≤ thetaCuspHawkingComplexNonlinearCarrierLocalMajorant a ha p x := by
      unfold thetaCuspHawkingComplexNonlinearCarrierLocalMajorant
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos x).le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor] using
      norm_thetaCuspHawkingComplexNonlinearCarrierIntegrand_le a ha p p x (Metric.mem_ball_self one_pos)

private theorem integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand
    (a : ℝ) (ha : |a| < 1) (p : ℂ × ℂ) :
    Integrable (thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a p) := by
  apply Integrable.mono (integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p)
  · apply Continuous.aestronglyMeasurable
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    unfold thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand thetaCuspHawkingComplexNonlinearPhase
    fun_prop
  · filter_upwards with x
    have hM0 : 0 ≤ thetaCuspHawkingComplexNonlinearSourceBound a ha :=
      (thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound a ha 0).1.trans (thetaCuspTiltedSource_mem_Icc_complexNonlinearSourceBound a ha 0).2
    have hmajor : 0 ≤ thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p x := by
      unfold thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg
        (mul_nonneg hM0
          (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos x).le))
        (mul_nonneg
          (mul_nonneg (abs_nonneg x) (Real.exp_pos _).le)
          (thetaCuspFullSource_pos x).le))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor] using
      norm_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand_le a ha p p x (Metric.mem_ball_self one_pos)

theorem hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrier
    (a : ℝ) (ha : |a| < 1) (p : ℂ × ℂ) :
    HasFDerivAt (fun q : ℂ × ℂ => thetaCuspHawkingComplexNonlinearCarrier a q.1 q.2) (thetaCuspHawkingComplexNonlinearCarrierFDeriv a p) p := by
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q x => thetaCuspHawkingComplexNonlinearCarrierIntegrand a q x)
    (F' := fun q x => thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a q x)
    (x₀ := p) (s := Metric.ball p 1) (bound := thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p)
    (Metric.ball_mem_nhds p one_pos)
    (Filter.Eventually.of_forall fun _ => by
      apply Continuous.aestronglyMeasurable
      have hk : Continuous (thetaCuspTiltedSource a) :=
        (contDiff_thetaCuspTiltedSource a).continuous
      unfold thetaCuspHawkingComplexNonlinearCarrierIntegrand thetaCuspHawkingComplexNonlinearPhase
      fun_prop)
    (integrable_thetaCuspHawkingComplexNonlinearCarrierIntegrand a ha p)
    (integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a ha p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x q hq =>
      norm_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand_le a ha p q x hq)
    (integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p)
    (Filter.Eventually.of_forall fun x q _ => hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrierIntegrand a q x)
  simpa only [thetaCuspHawkingComplexNonlinearCarrier, thetaCuspHawkingComplexNonlinearCarrierFDeriv] using h

private theorem thetaCuspHawkingComplexNonlinearCarrierFDeriv_continuousOn
    (a : ℝ) (ha : |a| < 1) (p₀ : ℂ × ℂ) :
    ContinuousOn (thetaCuspHawkingComplexNonlinearCarrierFDeriv a) (Metric.ball p₀ 1) := by
  apply MeasureTheory.continuousOn_of_dominated
      (bound := thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p₀)
  · intro p _
    exact (integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a ha p).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun x =>
      norm_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand_le a ha p₀ p x hp
  · exact integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivLocalMajorant a ha p₀
  · filter_upwards with x
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    unfold thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand thetaCuspHawkingComplexNonlinearPhase
    fun_prop

theorem contDiffAt_thetaCuspHawkingComplexNonlinearCarrier
    (a : ℝ) (ha : |a| < 1) (p₀ : ℂ × ℂ) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => thetaCuspHawkingComplexNonlinearCarrier a p.1 p.2) p₀ := by
  rw [contDiffAt_one_iff]
  exact ⟨thetaCuspHawkingComplexNonlinearCarrierFDeriv a, Metric.ball p₀ 1, Metric.ball_mem_nhds p₀ one_pos,
    thetaCuspHawkingComplexNonlinearCarrierFDeriv_continuousOn a ha p₀, fun p _ => hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrier a ha p⟩

theorem thetaCuspHawkingComplexNonlinearCarrier_ofReal
    (a t : ℝ) (z : ℂ) :
    thetaCuspHawkingComplexNonlinearCarrier a (t : ℂ) z = thetaCuspHawkingNonlinearCarrier a t z := by
  unfold thetaCuspHawkingComplexNonlinearCarrier thetaCuspHawkingNonlinearCarrier
  apply integral_congr_ae
  filter_upwards with x
  rw [thetaCuspHawkingComplexNonlinearCarrierIntegrand, thetaCuspHawkingComplexNonlinearPhase, thetaCuspHawkingNonlinearCarrierIntegrand,
    ← Complex.exp_add]

theorem thetaCuspHawkingComplexNonlinearCarrier_zero_eq_XiC (a : ℝ) (z : ℂ) :
    thetaCuspHawkingComplexNonlinearCarrier a 0 z = -Complex.I * XiC (z + (a : ℂ) * Complex.I) := by
  calc
    thetaCuspHawkingComplexNonlinearCarrier a 0 z = thetaCuspHawkingNonlinearCarrier a 0 z := by
      simpa using thetaCuspHawkingComplexNonlinearCarrier_ofReal a 0 z
    _ = -Complex.I * XiC (z + (a : ℂ) * Complex.I) :=
      thetaCuspHawkingNonlinearCarrier_zero_eq_XiC a z

def thetaCuspHawkingSecondCouplingMoment (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) *
    (thetaCuspTiltedSource a x : ℂ) ^ 2

theorem thetaCuspHawkingComplexNonlinearCarrierFDeriv_partial_coupling
    (a : ℝ) (ha : |a| < 1) (w : ℂ) :
    thetaCuspHawkingComplexNonlinearCarrierFDeriv a (0, w) (1, 0) = -thetaCuspHawkingSecondCouplingMoment a w := by
  rw [thetaCuspHawkingComplexNonlinearCarrierFDeriv, ContinuousLinearMap.integral_apply
    (integrable_thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand a ha (0, w))]
  unfold thetaCuspHawkingSecondCouplingMoment
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  simp [thetaCuspHawkingComplexNonlinearCarrierFDerivIntegrand, thetaCuspHawkingComplexNonlinearPhase]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem thetaCuspHawkingComplexNonlinearCarrierFDeriv_partial_frequency
    (a : ℝ) (ha : |a| < 1) (w : ℂ) :
    thetaCuspHawkingComplexNonlinearCarrierFDeriv a (0, w) (0, 1) =
      -Complex.I * deriv XiC (w + (a : ℂ) * Complex.I) := by
  let f : ℂ × ℂ → ℂ := fun p => thetaCuspHawkingComplexNonlinearCarrier a p.1 p.2
  have hpair : HasFDerivAt (fun z : ℂ => ((0 : ℂ), z))
      (ContinuousLinearMap.inr ℂ ℂ ℂ) w := by
    fun_prop
  have hslice : HasDerivAt (fun z : ℂ => thetaCuspHawkingComplexNonlinearCarrier a 0 z)
      (thetaCuspHawkingComplexNonlinearCarrierFDeriv a (0, w) (0, 1)) w := by
    have hcomp := (hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrier a ha (0, w)).comp w hpair
    have hraw : HasDerivAt
        ((fun q : ℂ × ℂ => thetaCuspHawkingComplexNonlinearCarrier a q.1 q.2) ∘
          fun z : ℂ => ((0 : ℂ), z))
        (thetaCuspHawkingComplexNonlinearCarrierFDeriv a (0, w) (0, 1)) w := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using hcomp.hasDerivAt
    exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hXiBase : HasDerivAt XiC
      (deriv XiC (w + (a : ℂ) * Complex.I))
      (w + (a : ℂ) * Complex.I) :=
    XiC_differentiable.differentiableAt.hasDerivAt
  have hshift : HasDerivAt (fun z : ℂ => z + (a : ℂ) * Complex.I) 1 w := by
    simpa using (hasDerivAt_id w).add_const ((a : ℂ) * Complex.I)
  have hRhs : HasDerivAt
      (fun z : ℂ => -Complex.I * XiC (z + (a : ℂ) * Complex.I))
      (-Complex.I * deriv XiC (w + (a : ℂ) * Complex.I)) w := by
    simpa using (hXiBase.comp w hshift).const_mul (-Complex.I)
  have hXi : HasDerivAt (fun z : ℂ => thetaCuspHawkingComplexNonlinearCarrier a 0 z)
      (-Complex.I * deriv XiC (w + (a : ℂ) * Complex.I)) w :=
    hRhs.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => thetaCuspHawkingComplexNonlinearCarrier_zero_eq_XiC a z)
  exact hslice.unique hXi

theorem exists_thetaCuspHawkingComplexNonlinearCarrier_simpleResonanceBranch
    (alpha : ℂ) (halpha : XiC alpha = 0)
    (hsimple : deriv XiC alpha ≠ 0) :
    ∃ gamma : ℂ → ℂ,
      ContDiffAt ℂ 1 gamma 0 ∧
      gamma 0 = (alpha.re : ℂ) ∧
      (∀ᶠ tau in 𝓝 (0 : ℂ),
        thetaCuspHawkingComplexNonlinearCarrier alpha.im tau (gamma tau) = 0) ∧
      HasDerivAt gamma
        (Complex.I * thetaCuspHawkingSecondCouplingMoment alpha.im (alpha.re : ℂ) /
          deriv XiC alpha) 0 := by
  have ha : |alpha.im| < 1 := abs_im_lt_one_of_XiC_eq_zero halpha
  have hdecomp : (alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I = alpha :=
    Complex.re_add_im alpha
  let f : ℂ × ℂ → ℂ := fun p => thetaCuspHawkingComplexNonlinearCarrier alpha.im p.1 p.2
  let p₀ : ℂ × ℂ := (0, (alpha.re : ℂ))
  have hc1 : ContDiffAt ℂ 1 f p₀ := by
    exact contDiffAt_thetaCuspHawkingComplexNonlinearCarrier alpha.im ha p₀
  have hfd : fderiv ℂ f p₀ = thetaCuspHawkingComplexNonlinearCarrierFDeriv alpha.im p₀ := by
    exact (hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrier alpha.im ha p₀).fderiv
  have hpartial : (fderiv ℂ f p₀) (0, 1) =
      -Complex.I * deriv XiC alpha := by
    rw [hfd]
    simpa only [p₀, hdecomp] using
      thetaCuspHawkingComplexNonlinearCarrierFDeriv_partial_frequency alpha.im ha (alpha.re : ℂ)
  have hpartial_ne : (fderiv ℂ f p₀) (0, 1) ≠ 0 := by
    rw [hpartial]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hsimple
  have if₂ : (fderiv ℂ f p₀ ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using hpartial_ne)
  have hOne : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  let gamma : ℂ → ℂ := hc1.implicitFunction hOne if₂
  have hgamma0 : gamma 0 = (alpha.re : ℂ) := by
    exact hc1.implicitFunction_apply_self hOne if₂
  have hcenter : f p₀ = 0 := by
    dsimp only [f, p₀]
    rw [thetaCuspHawkingComplexNonlinearCarrier_zero_eq_XiC, hdecomp, halpha, mul_zero]
  have hzero : ∀ᶠ tau in 𝓝 (0 : ℂ),
      thetaCuspHawkingComplexNonlinearCarrier alpha.im tau (gamma tau) = 0 := by
    filter_upwards [hc1.eventually_apply_implicitFunction hOne if₂] with tau htau
    simpa only [f, p₀, gamma, hcenter] using htau
  have hgammaC1 : ContDiffAt ℂ 1 gamma 0 :=
    hc1.contDiffAt_implicitFunction hOne if₂
  let v : ℂ := deriv gamma 0
  have hgammaDeriv : HasDerivAt gamma v 0 := by
    exact (hgammaC1.differentiableAt one_ne_zero).hasDerivAt
  have hpair : HasDerivAt (fun tau : ℂ => (tau, gamma tau))
      ((1 : ℂ), v) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk hgammaDeriv
  have houter : HasFDerivAt
      (fun p : ℂ × ℂ => thetaCuspHawkingComplexNonlinearCarrier alpha.im p.1 p.2)
      (thetaCuspHawkingComplexNonlinearCarrierFDeriv alpha.im p₀) ((0 : ℂ), gamma 0) := by
    simpa only [p₀, hgamma0] using hasFDerivAt_thetaCuspHawkingComplexNonlinearCarrier alpha.im ha p₀
  have hcompRaw := houter.comp 0 hpair.hasFDerivAt
  have hcomp : HasDerivAt
      (fun tau : ℂ => thetaCuspHawkingComplexNonlinearCarrier alpha.im tau (gamma tau))
      (thetaCuspHawkingComplexNonlinearCarrierFDeriv alpha.im p₀ (1, v)) 0 := by
    have hraw : HasDerivAt
        ((fun p : ℂ × ℂ => thetaCuspHawkingComplexNonlinearCarrier alpha.im p.1 p.2) ∘
          fun tau : ℂ => (tau, gamma tau))
        (thetaCuspHawkingComplexNonlinearCarrierFDeriv alpha.im p₀ (1, v)) 0 := by
      exact hcompRaw.hasDerivAt.congr_deriv (by simp)
    exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hcompZero : HasDerivAt
      (fun tau : ℂ => thetaCuspHawkingComplexNonlinearCarrier alpha.im tau (gamma tau)) 0 0 :=
    (hasDerivAt_const (x := (0 : ℂ)) (c := (0 : ℂ))).congr_of_eventuallyEq hzero
  have heqD : thetaCuspHawkingComplexNonlinearCarrierFDeriv alpha.im p₀ (1, v) = 0 := hcomp.unique hcompZero
  have hvec : ((1, v) : ℂ × ℂ) = (1, 0) + v • (0, 1) := by
    ext <;> simp
  have heq :
      -thetaCuspHawkingSecondCouplingMoment alpha.im (alpha.re : ℂ) +
        v * (-Complex.I * deriv XiC alpha) = 0 := by
    rw [hvec, map_add, map_smul, thetaCuspHawkingComplexNonlinearCarrierFDeriv_partial_coupling alpha.im ha,
      thetaCuspHawkingComplexNonlinearCarrierFDeriv_partial_frequency alpha.im ha] at heqD
    simpa only [p₀, smul_eq_mul, hdecomp] using heqD
  have hterm : v * (-Complex.I * deriv XiC alpha) =
      thetaCuspHawkingSecondCouplingMoment alpha.im (alpha.re : ℂ) := by
    linear_combination heq
  have hv : v = Complex.I * thetaCuspHawkingSecondCouplingMoment alpha.im (alpha.re : ℂ) /
      deriv XiC alpha := by
    apply (eq_div_iff hsimple).2
    calc
      v * deriv XiC alpha =
          Complex.I * (v * (-Complex.I * deriv XiC alpha)) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = Complex.I * thetaCuspHawkingSecondCouplingMoment alpha.im (alpha.re : ℂ) := by rw [hterm]
  refine ⟨gamma, hgammaC1, hgamma0, hzero, ?_⟩
  exact hgammaDeriv.congr_deriv hv

/-- Every spectral point is nonresonant, a degenerate Xi resonance, or carries the exact
source-faithful nonlinear Hawking resonance branch and its first-coupling velocity. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_classification (alpha : ℂ) :
    XiC alpha ≠ 0 ∨ deriv XiC alpha = 0 ∨
      ∃ gamma : ℂ → ℂ,
        ContDiffAt ℂ 1 gamma 0 ∧
        gamma 0 = (alpha.re : ℂ) ∧
        (∀ᶠ tau in 𝓝 (0 : ℂ),
          thetaCuspHawkingComplexNonlinearCarrier alpha.im tau (gamma tau) = 0) ∧
        HasDerivAt gamma
          (Complex.I * thetaCuspHawkingSecondCouplingMoment alpha.im (alpha.re : ℂ) /
            deriv XiC alpha) 0 := by
  by_cases halpha : XiC alpha = 0
  · by_cases hsimple : deriv XiC alpha = 0
    · exact Or.inr (Or.inl hsimple)
    · exact Or.inr (Or.inr
        (exists_thetaCuspHawkingComplexNonlinearCarrier_simpleResonanceBranch alpha halpha hsimple))
  · exact Or.inl halpha

theorem thetaCuspHawkingNonlinearResonanceVelocity_re (a : ℝ) (w : ℂ) :
    (Complex.I * thetaCuspHawkingSecondCouplingMoment a w / deriv XiC (w + (a : ℂ) * Complex.I)).re =
      -(thetaCuspHawkingSecondCouplingMoment a w / deriv XiC (w + (a : ℂ) * Complex.I)).im := by
  have hrewrite : Complex.I * thetaCuspHawkingSecondCouplingMoment a w /
      deriv XiC (w + (a : ℂ) * Complex.I) =
      Complex.I * (thetaCuspHawkingSecondCouplingMoment a w /
        deriv XiC (w + (a : ℂ) * Complex.I)) := by ring
  rw [hrewrite]
  simp [Complex.mul_re]

theorem thetaCuspHawkingNonlinearResonanceVelocity_im (a : ℝ) (w : ℂ) :
    (Complex.I * thetaCuspHawkingSecondCouplingMoment a w / deriv XiC (w + (a : ℂ) * Complex.I)).im =
      (thetaCuspHawkingSecondCouplingMoment a w / deriv XiC (w + (a : ℂ) * Complex.I)).re := by
  have hrewrite : Complex.I * thetaCuspHawkingSecondCouplingMoment a w /
      deriv XiC (w + (a : ℂ) * Complex.I) =
      Complex.I * (thetaCuspHawkingSecondCouplingMoment a w /
        deriv XiC (w + (a : ℂ) * Complex.I)) := by ring
  rw [hrewrite]
  simp [Complex.mul_im]

end RHTower
