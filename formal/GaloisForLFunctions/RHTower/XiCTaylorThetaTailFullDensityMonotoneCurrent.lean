import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMonotonePacketAnisotropic
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberGlobalCurrent
import GaloisForLFunctions.HTGeometry.MultiplicativeCenteredDivisorOrientation

/-!
# Full-density monotone completion and aggregate arithmetic current

The complete positive-half-line theta density is strictly decreasing.  Its negative derivative
therefore supplies a positive completion of the *full* Fourier--Laplace transform, not merely one
prime ladder or one product fibre.  Two exact integrations by parts identify that completion and
its spectral derivative.  The positive-completion contraction then controls the full current by
the squared norm of the final aggregate value.

Via the exact product-fibre reassembly theorem, this is also a bound on the absolutely convergent
sum of every actual Hermitian product-fibre current.  Individual fibres may have positive current;
the theorem records the cross-fibre cancellation forced by the continuous archimedean density.

This does not replace the finite Taylor core by the untruncated transform.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Negative derivative of the full canonical density is strictly positive on the positive
half-line. -/
theorem neg_thetaCuspTailSecondDensityDerivative_pos
    {t : ℝ} (ht : 0 ≤ t) :
    0 < -(4 * thetaCuspTailDerivative 3 t) := by
  exact neg_pos.mpr (mul_neg_of_pos_of_neg (by norm_num)
    (thetaCuspTailDerivative_three_neg ht))

theorem integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_one_sub_phase
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ =>
      ((-(4 * thetaCuspTailDerivative 3 t) : ℝ) : ℂ) *
        (1 - spectralTranslationPhase t z)) (Ioi 0) := by
  let h : ℝ → ℝ := fun t => -(4 * thetaCuspTailDerivative 3 t)
  have hhReal : IntegrableOn h (Ioi 0) := by
    have hbase := (integrableOn_pow_mul_thetaCuspTailDerivative 0 3).const_mul 4
    have hderiv : IntegrableOn (fun t : ℝ => 4 * thetaCuspTailDerivative 3 t)
        (Ioi 0) := by
      simpa only [pow_zero, one_mul] using hbase
    simpa only [h] using hderiv.neg
  have hh : Integrable (fun t => (h t : ℂ)) (volume.restrict (Ioi 0)) :=
    hhReal.ofReal
  have hmajor : Integrable (fun t => (2 : ℂ) * (h t : ℂ))
      (volume.restrict (Ioi 0)) := hh.const_mul 2
  apply Integrable.mono hmajor
  · have hphase : Continuous (fun t : ℝ =>
        1 - spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact hh.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hhnon : 0 ≤ h t :=
      (neg_thetaCuspTailSecondDensityDerivative_pos ht.le).le
    have hinline : 0 ≤ -(4 * thetaCuspTailDerivative 3 t) := by
      simpa only [h] using hhnon
    have hp := norm_spectralTranslationPhase_le_one ht.le hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hinline]
    change h t * ‖1 - spectralTranslationPhase t z‖ ≤
      ‖(2 : ℂ) * (h t : ℂ)‖
    calc
      h t * ‖1 - spectralTranslationPhase t z‖ ≤ h t * 2 := by
        apply mul_le_mul_of_nonneg_left _ hhnon
        calc
          ‖1 - spectralTranslationPhase t z‖ ≤
              ‖(1 : ℂ)‖ + ‖spectralTranslationPhase t z‖ := norm_sub_le _ _
          _ ≤ 2 := by norm_num; linarith
      _ = ‖(2 : ℂ) * (h t : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
        rw [abs_of_nonneg hhnon]
        ring

theorem integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_phaseDerivative
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ =>
      ((-(4 * thetaCuspTailDerivative 3 t) : ℝ) : ℂ) *
        (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0) := by
  let h : ℝ → ℝ := fun t => -(4 * thetaCuspTailDerivative 3 t)
  have hthReal : IntegrableOn (fun t : ℝ => t * h t) (Ioi 0) := by
    have hbase := (integrableOn_pow_mul_thetaCuspTailDerivative 1 3).const_mul 4
    have hderiv : IntegrableOn
        (fun t : ℝ => t * (4 * thetaCuspTailDerivative 3 t)) (Ioi 0) := by
      simpa only [pow_one, mul_assoc, mul_left_comm, mul_comm] using hbase
    have hneg := hderiv.neg
    simpa only [h, Pi.neg_apply, mul_neg] using hneg
  have hth : Integrable (fun t => ((t * h t : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := hthReal.ofReal
  apply Integrable.mono hth
  · have hhReal : IntegrableOn h (Ioi 0) := by
      have hbase := (integrableOn_pow_mul_thetaCuspTailDerivative 0 3).const_mul 4
      have hderiv : IntegrableOn (fun t : ℝ => 4 * thetaCuspTailDerivative 3 t)
          (Ioi 0) := by
        simpa only [pow_zero, one_mul] using hbase
      simpa only [h] using hderiv.neg
    have hh : Integrable (fun t => (h t : ℂ)) (volume.restrict (Ioi 0)) :=
      hhReal.ofReal
    have hphase : Continuous (fun t : ℝ =>
        -((t : ℂ) * I) * spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact hh.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hh0 : 0 ≤ h t :=
      (neg_thetaCuspTailSecondDensityDerivative_pos ht0).le
    have hinline : 0 ≤ -(4 * thetaCuspTailDerivative 3 t) := by
      simpa only [h] using hh0
    have hp := norm_spectralTranslationPhase_le_one ht0 hz
    rw [norm_mul, norm_mul, norm_neg, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
      abs_of_nonneg ht0]
    rw [abs_of_nonneg hinline, abs_of_nonneg (mul_nonneg ht0 hh0)]
    change h t * (t * ‖spectralTranslationPhase t z‖) ≤
      t * h t
    calc
      h t * (t * ‖spectralTranslationPhase t z‖) =
          (t * h t) * ‖spectralTranslationPhase t z‖ := by ring
      _ ≤ (t * h t) * 1 :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg ht0 hh0)
      _ = t * h t := by ring

/-- First exact integration by parts: positive completion equals `-i z` times the full one-sided
theta-density transform. -/
theorem positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_eq
    {z : ℂ} (hz : 0 ≤ z.im) :
    positiveTailCompletion
        (fun t => -(4 * thetaCuspTailDerivative 3 t)) z =
      -I * z * thetaCuspTailSecondDensityPhaseValue z := by
  let g : ℝ → ℝ := thetaCuspTailSecondDensity
  let g' : ℝ → ℝ := fun t => 4 * thetaCuspTailDerivative 3 t
  let p : ℝ → ℂ := fun t => spectralTranslationPhase t z
  let p' : ℝ → ℂ := fun t => I * z * spectralTranslationPhase t z
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    simpa only [g, g'] using hasDerivAt_thetaCuspTailSecondDensity_fromAtoms t
  have hp (t : ℝ) : HasDerivAt p (p' t) t :=
    hasDerivAt_spectralTranslationPhase_source z t
  have hg'int : IntegrableOn g' (Ioi 0) := by
    have hbase := (integrableOn_pow_mul_thetaCuspTailDerivative 0 3).const_mul 4
    simpa only [g', pow_zero, one_mul] using hbase
  have hgint : IntegrableOn g (Ioi 0) := by
    simpa only [g, pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspTailSecondDensity 0
  have hp_mul_g' : IntegrableOn (p * fun t => (g' t : ℂ)) (Ioi 0) := by
    have h := integrableOn_ofReal_mul_spectralTranslationPhase hg'int hz
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, p]
    ring
  have hp'_mul_g : IntegrableOn (p' * fun t => (g t : ℂ)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ =>
        (I * z) * ((g t : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
      (integrableOn_ofReal_mul_spectralTranslationPhase hgint hz).const_mul (I * z)
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, p']
    ring
  have hgzero : Tendsto (fun t : ℝ => (g t : ℂ))
      (𝓝[>] 0) (nhds (g 0 : ℂ)) :=
    (hg 0).ofReal_comp.continuousAt.tendsto.mono_left inf_le_left
  have hgtop : Tendsto (fun t : ℝ => (g t : ℂ)) atTop (nhds 0) := by
    have h := (thetaCuspTailDerivative_tendsto_atTop_zero 2).const_mul 4
    simpa only [g, thetaCuspTailSecondDensity, ofReal_mul, ofReal_ofNat,
      ofReal_zero, mul_zero] using h.ofReal
  have hmass := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (g 0 : ℂ)) (b' := (0 : ℂ))
    (u := fun _ : ℝ => (1 : ℂ)) (u' := fun _ : ℝ => 0)
    (v := fun t : ℝ => (g t : ℂ)) (v' := fun t : ℝ => (g' t : ℂ))
    (fun t _ht => hasDerivAt_const t 1)
    (fun t _ht => (hg t).ofReal_comp)
    (by
      change IntegrableOn (fun t : ℝ => (1 : ℂ) * (g' t : ℂ)) (Ioi 0)
      simpa using hg'int.ofReal)
    (by
      have hzero : IntegrableOn (fun _t : ℝ => (0 : ℂ)) (Ioi 0) :=
        integrableOn_zero
      apply hzero.congr_fun _ measurableSet_Ioi
      intro t _ht
      simp only [Pi.mul_apply, zero_mul])
    (by
      change Tendsto (fun t : ℝ => (1 : ℂ) * (g t : ℂ))
        (𝓝[>] 0) (nhds (g 0 : ℂ))
      simpa using hgzero)
    (by
      change Tendsto (fun t : ℝ => (1 : ℂ) * (g t : ℂ)) atTop (nhds 0)
      simpa using hgtop)
  have hmass' : (∫ t : ℝ in Ioi 0, (g' t : ℂ)) = -(g 0 : ℂ) := by
    simpa only [one_mul, zero_mul, integral_zero, sub_zero, zero_sub] using hmass
  have hpgtop : Tendsto (fun t : ℝ => p t * (g t : ℂ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      (by simpa using hgtop.norm)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [norm_mul]
    have hpNorm : ‖p t‖ ≤ 1 := by
      simpa only [p] using norm_spectralTranslationPhase_le_one ht hz
    calc
      ‖p t‖ * ‖(g t : ℂ)‖ ≤ 1 * ‖(g t : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hpNorm (norm_nonneg _)
      _ = ‖(g t : ℂ)‖ := by ring
      _ = |g t| := by simp only [Complex.norm_real, Real.norm_eq_abs]
  have hpgzero : Tendsto (fun t : ℝ => p t * (g t : ℂ))
      (𝓝[>] 0) (nhds (g 0 : ℂ)) := by
    have h := (hp 0).continuousAt.mul (hg 0).ofReal_comp.continuousAt
    simpa [p, spectralTranslationPhase] using h.tendsto.mono_left inf_le_left
  have hphase := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (g 0 : ℂ)) (b' := (0 : ℂ))
    (u := p) (u' := p')
    (v := fun t : ℝ => (g t : ℂ)) (v' := fun t : ℝ => (g' t : ℂ))
    (fun t _ht => hp t) (fun t _ht => (hg t).ofReal_comp)
    hp_mul_g' hp'_mul_g hpgzero hpgtop
  have hphase' :
      (∫ t : ℝ in Ioi 0, (g' t : ℂ) * p t) =
        -(g 0 : ℂ) - (I * z) *
          (∫ t : ℝ in Ioi 0, (g t : ℂ) * p t) := by
    rw [show (fun t : ℝ => (g' t : ℂ) * p t) = p * fun t => (g' t : ℂ) by
      funext t; simp only [Pi.mul_apply]; ring]
    rw [show (fun t : ℝ => p' t * (g t : ℂ)) =
        fun t => (I * z) * ((g t : ℂ) * p t) by
      funext t; simp only [p']; ring,
      integral_const_mul] at hphase
    simpa only [zero_sub] using hphase
  unfold positiveTailCompletion
  rw [show (fun t : ℝ =>
      ((-(4 * thetaCuspTailDerivative 3 t) : ℝ) : ℂ) *
        (1 - spectralTranslationPhase t z)) =
      fun t => -(g' t : ℂ) + (g' t : ℂ) * p t by
    funext t
    dsimp only [g', p]
    push_cast
    ring]
  rw [integral_add]
  · rw [integral_neg, hmass', hphase']
    dsimp only [g, p, thetaCuspTailSecondDensityPhaseValue]
    ring
  · exact hg'int.ofReal.neg
  · exact hp_mul_g'.congr_fun (fun t _ht => by simp only [Pi.mul_apply]; ring)
      measurableSet_Ioi

/-- Second exact integration by parts: derivative of the positive completion is the covariant
combination of full transform and its spectral derivative. -/
theorem positiveTailCompletionDerivative_neg_thetaCuspTailSecondDensityDerivative_eq
    {z : ℂ} (hz : 0 ≤ z.im) :
    positiveTailCompletionDerivative
        (fun t => -(4 * thetaCuspTailDerivative 3 t)) z =
      -I * (thetaCuspTailSecondDensityPhaseValue z +
        z * thetaCuspTailSecondDensityPhaseDerivative z) := by
  let g : ℝ → ℝ := thetaCuspTailSecondDensity
  let g' : ℝ → ℝ := fun t => 4 * thetaCuspTailDerivative 3 t
  let q : ℝ → ℂ := fun t =>
    -((t : ℂ) * I) * spectralTranslationPhase t z
  let q' : ℝ → ℂ := fun t =>
    -I * spectralTranslationPhase t z +
      (t : ℂ) * z * spectralTranslationPhase t z
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    simpa only [g, g'] using hasDerivAt_thetaCuspTailSecondDensity_fromAtoms t
  have hq (t : ℝ) : HasDerivAt q (q' t) t := by
    have hlin : HasDerivAt (fun u : ℝ => -((u : ℂ) * I)) (-I) t := by
      convert ((Complex.ofRealCLM.hasDerivAt.mul_const I).neg) using 1
      simp [Complex.ofRealCLM_apply]
    have hp := hasDerivAt_spectralTranslationPhase_source z t
    convert hlin.mul hp using 1
    dsimp only [q, q']
    ring_nf
    rw [I_sq]
    ring
  have hg'int : IntegrableOn g' (Ioi 0) := by
    have hbase := (integrableOn_pow_mul_thetaCuspTailDerivative 0 3).const_mul 4
    simpa only [g', pow_zero, one_mul] using hbase
  have ht_g'int : IntegrableOn (fun t : ℝ => t * g' t) (Ioi 0) := by
    have hbase := (integrableOn_pow_mul_thetaCuspTailDerivative 1 3).const_mul 4
    simpa only [g', pow_one, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hgint : IntegrableOn g (Ioi 0) := by
    simpa only [g, pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspTailSecondDensity 0
  have ht_gint : IntegrableOn (fun t : ℝ => t * g t) (Ioi 0) := by
    have hbase := integrableOn_pow_mul_thetaCuspTailSecondDensity 1
    apply hbase.congr_fun _ measurableSet_Ioi
    intro t _ht
    dsimp only [g]
    simp only [pow_one]
  have hq_mul_g' : IntegrableOn (q * fun t => (g' t : ℂ)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ =>
        (-I) * (((t * g' t : ℝ) : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
      (integrableOn_ofReal_mul_spectralTranslationPhase ht_g'int hz).const_mul (-I)
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, q]
    push_cast
    ring
  have hq'_mul_g : IntegrableOn (q' * fun t => (g t : ℂ)) (Ioi 0) := by
    have h0 := (integrableOn_ofReal_mul_spectralTranslationPhase hgint hz).const_mul (-I)
    have h1 := (integrableOn_ofReal_mul_spectralTranslationPhase ht_gint hz).const_mul z
    have h : IntegrableOn (fun t : ℝ =>
        (-I) * ((g t : ℂ) * spectralTranslationPhase t z) +
          z * (((t * g t : ℝ) : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
      h0.add h1
    apply h.congr_fun _ measurableSet_Ioi
    intro t _ht
    simp only [Pi.mul_apply, q']
    push_cast
    ring
  have hqgzero : Tendsto (fun t : ℝ => q t * (g t : ℂ))
      (𝓝[>] 0) (nhds 0) := by
    have hcont := (hq 0).continuousAt.mul (hg 0).ofReal_comp.continuousAt
    convert hcont.tendsto.mono_left inf_le_left using 1
    simp [Pi.mul_apply, q, spectralTranslationPhase]
  have hqgtop : Tendsto (fun t : ℝ => q t * (g t : ℂ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun t : ℝ => ((t * g t : ℝ) : ℂ)) atTop (nhds 0) := by
      have h := (pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero 1 2).const_mul 4
      have hreal : Tendsto (fun t : ℝ => t * g t) atTop (nhds 0) := by
        convert h using 1
        · funext t
          dsimp only [g, thetaCuspTailSecondDensity]
          simp only [pow_one]
          ring
        · simp
      exact hreal.ofReal
    have hmajorNorm : Tendsto (fun t : ℝ => ‖((t * g t : ℝ) : ℂ)‖)
        atTop (nhds 0) := by
      simpa using hmajor.norm
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_
      hmajorNorm
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    dsimp only [q]
    rw [norm_mul, norm_mul, norm_neg, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, norm_I]
    have hp := norm_spectralTranslationPhase_le_one ht hz
    calc
      t * 1 * ‖spectralTranslationPhase t z‖ * |g t| ≤
          t * 1 * 1 * |g t| := by gcongr
      _ = ‖((t * g t : ℝ) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg ht, mul_one]
      _ = |t * g t| := by simp only [Complex.norm_real, Real.norm_eq_abs]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℂ)) (b' := (0 : ℂ))
    (u := q) (u' := q')
    (v := fun t : ℝ => (g t : ℂ)) (v' := fun t : ℝ => (g' t : ℂ))
    (fun t _ht => hq t) (fun t _ht => (hg t).ofReal_comp)
    hq_mul_g' hq'_mul_g hqgzero hqgtop
  have hqintegral :
      (∫ t : ℝ in Ioi 0, (g' t : ℂ) * q t) =
        I * (∫ t : ℝ in Ioi 0,
          (g t : ℂ) * spectralTranslationPhase t z) -
          z * (∫ t : ℝ in Ioi 0,
            (g t : ℂ) * ((t : ℂ) * spectralTranslationPhase t z)) := by
    rw [show (fun t : ℝ => (g' t : ℂ) * q t) = q * fun t => (g' t : ℂ) by
      funext t; simp only [Pi.mul_apply]; ring]
    rw [show (fun t : ℝ => q' t * (g t : ℂ)) =
        fun t => (-I) * ((g t : ℂ) * spectralTranslationPhase t z) +
          z * ((g t : ℂ) * ((t : ℂ) * spectralTranslationPhase t z)) by
      funext t
      simp only [q']
      ring,
      integral_add, integral_const_mul, integral_const_mul] at hibp
    · calc
        _ = 0 - 0 -
            ((-I) * (∫ t : ℝ in Ioi 0,
                (g t : ℂ) * spectralTranslationPhase t z) +
              z * (∫ t : ℝ in Ioi 0,
                (g t : ℂ) * ((t : ℂ) * spectralTranslationPhase t z))) := hibp
        _ = _ := by ring
    · exact (integrableOn_ofReal_mul_spectralTranslationPhase hgint hz).const_mul (-I)
    · have h : IntegrableOn (fun t : ℝ =>
          z * (((t * g t : ℝ) : ℂ) * spectralTranslationPhase t z)) (Ioi 0) :=
        (integrableOn_ofReal_mul_spectralTranslationPhase ht_gint hz).const_mul z
      apply h.congr_fun _ measurableSet_Ioi
      intro t _ht
      push_cast
      ring
  unfold positiveTailCompletionDerivative
  rw [show (fun t : ℝ =>
      ((-(4 * thetaCuspTailDerivative 3 t) : ℝ) : ℂ) *
        (-((t : ℂ) * I) * spectralTranslationPhase t z)) =
      fun t => -(g' t : ℂ) * q t by
    funext t
    dsimp only [g', q]
    push_cast
    ring,
    show (fun t => -(g' t : ℂ) * q t) = fun t => -((g' t : ℂ) * q t) by
      funext t; ring,
    integral_neg, hqintegral]
  dsimp only [g]
  unfold thetaCuspTailSecondDensityPhaseValue thetaCuspTailSecondDensityPhaseDerivative
  rw [show (fun t : ℝ =>
      (thetaCuspTailSecondDensity t : ℂ) *
        ((t : ℂ) * I * spectralTranslationPhase t z)) =
      fun t => I *
        ((thetaCuspTailSecondDensity t : ℂ) *
          ((t : ℂ) * spectralTranslationPhase t z)) by
    funext t; ring,
    integral_const_mul]
  ring_nf
  rw [I_sq]
  ring

theorem positiveTailCompletion_fullDensityIntegrand_re_pos
    {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : 0 < t) :
    0 < ((((-(4 * thetaCuspTailDerivative 3 t) : ℝ) : ℂ) *
      (1 - spectralTranslationPhase t z)).re) := by
  have hh := neg_thetaCuspTailSecondDensityDerivative_pos ht.le
  have hphase : (spectralTranslationPhase t z).re < 1 := by
    calc
      (spectralTranslationPhase t z).re ≤
          ‖spectralTranslationPhase t z‖ := Complex.re_le_norm _
      _ = Real.exp (-t * z.im) :=
        RHTower.norm_spectralTranslationPhase_eq_exp_neg_mul_im t z
      _ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_re, one_re]
  simpa only [sub_zero] using mul_pos hh (sub_pos.mpr hphase)

/-- Full positive completion lies strictly in the right half-plane. -/
theorem positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_re_pos
    {z : ℂ} (hz : 0 < z.im) :
    0 < (positiveTailCompletion
      (fun t : ℝ => -(4 * thetaCuspTailDerivative 3 t)) z).re := by
  let h : ℝ → ℝ := fun t => -(4 * thetaCuspTailDerivative 3 t)
  let f : ℝ → ℂ := fun t =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have hf : Integrable f mu := by
    simpa only [f, h, mu] using
      integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_one_sub_phase hz.le
  have hfre : Integrable (fun t => (f t).re) mu := hf.re
  have hnonneg : 0 ≤ᵐ[mu] fun t => (f t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (positiveTailCompletion_fullDensityIntegrand_re_pos hz ht).le
  have hsupp : Ioi (0 : ℝ) ⊆ Function.support (fun t => (f t).re) := by
    intro t ht
    exact Function.mem_support.mpr
      (ne_of_gt (positiveTailCompletion_fullDensityIntegrand_re_pos hz ht))
  have hmuPos : 0 < mu (Ioi (0 : ℝ)) := by
    simp [mu]
  have hsuppPos : 0 < mu (Function.support (fun t => (f t).re)) :=
    lt_of_lt_of_le hmuPos (measure_mono hsupp)
  have hintPos : 0 < ∫ t, (f t).re ∂mu :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hfre).2 hsuppPos
  have hre : (∫ t, (f t).re ∂mu) = (∫ t, f t ∂mu).re :=
    integral_re hf
  rw [hre] at hintPos
  simpa only [positiveTailCompletion, f, h, mu] using hintPos

/-- The complete positive-half-line theta-density transform is zero-free in the open upper
half-plane. -/
theorem thetaCuspTailSecondDensityPhaseValue_ne_zero
    {z : ℂ} (hz : 0 < z.im) :
    thetaCuspTailSecondDensityPhaseValue z ≠ 0 := by
  have hpos :=
    positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_re_pos hz
  have hcompletion :=
    positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_eq hz.le
  intro hzero
  rw [hzero, mul_zero] at hcompletion
  rw [hcompletion] at hpos
  simp only [zero_re, lt_self_iff_false] at hpos

/-- Strong full-density contraction: the norm of the spectral derivative, rather than only one
oriented current, is controlled by the norm of the final aggregate value. -/
theorem norm_thetaCuspTailSecondDensityPhaseDerivative_le_two_div_im
    {z : ℂ} (hz : 0 < z.im) :
    ‖thetaCuspTailSecondDensityPhaseDerivative z‖ ≤
      (2 / z.im) * ‖thetaCuspTailSecondDensityPhaseValue z‖ := by
  let h : ℝ → ℝ := fun t => -(4 * thetaCuspTailDerivative 3 t)
  apply norm_derivative_le_two_div_im_of_completion_contraction hz
    (G := positiveTailCompletion h z)
    (G' := positiveTailCompletionDerivative h z)
  · simpa only [h] using
      positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_eq hz.le
  · simpa only [h] using
      positiveTailCompletionDerivative_neg_thetaCuspTailSecondDensityDerivative_eq hz.le
  · calc
      ‖positiveTailCompletionDerivative h z‖ ≤
          (positiveTailCompletion h z).re / z.im :=
        norm_positiveTailCompletionDerivative_le_re_div hz
          (fun t ht =>
            (neg_thetaCuspTailSecondDensityDerivative_pos ht.le).le)
          (by simpa only [h] using
            integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_one_sub_phase hz.le)
          (by simpa only [h] using
            integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_phaseDerivative hz.le)
      _ ≤ ‖positiveTailCompletion h z‖ / z.im :=
        (div_le_div_iff_of_pos_right hz).2 (Complex.re_le_norm _)

/-- Zero-freeness upgrades the aggregate contraction to a logarithmic-derivative disk. -/
theorem norm_thetaCuspTailSecondDensityPhaseDerivative_div_value_le_two_div_im
    {z : ℂ} (hz : 0 < z.im) :
    ‖thetaCuspTailSecondDensityPhaseDerivative z /
        thetaCuspTailSecondDensityPhaseValue z‖ ≤ 2 / z.im := by
  have hne := thetaCuspTailSecondDensityPhaseValue_ne_zero hz
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hne)).2
  simpa only [mul_comm] using
    norm_thetaCuspTailSecondDensityPhaseDerivative_le_two_div_im hz

/-- Absolute full-density current contraction.  This controls all internal arithmetic crosses
after recombination, rather than estimating product fibres separately. -/
theorem abs_thetaCuspTailSecondDensityPhase_current_le_two_div_im
    {z : ℂ} (hz : 0 < z.im) :
    |(thetaCuspTailSecondDensityPhaseDerivative z *
        (starRingEnd ℂ) (thetaCuspTailSecondDensityPhaseValue z)).im| ≤
      (2 / z.im) * Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) := by
  let h : ℝ → ℝ := fun t => -(4 * thetaCuspTailDerivative 3 t)
  apply abs_orientedCurrent_le_two_div_im_of_positiveTailCompletion
    (h := h) hz
  · intro t ht
    exact (neg_thetaCuspTailSecondDensityDerivative_pos ht.le).le
  · simpa only [h] using
      integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_one_sub_phase hz.le
  · simpa only [h] using
      integrableOn_neg_thetaCuspTailSecondDensityDerivative_mul_phaseDerivative hz.le
  · simpa only [h] using
      positiveTailCompletion_neg_thetaCuspTailSecondDensityDerivative_eq hz.le
  · simpa only [h] using
      positiveTailCompletionDerivative_neg_thetaCuspTailSecondDensityDerivative_eq hz.le

/-- **Aggregate arithmetic seam contraction.**  The absolutely convergent sum of the actual
Hermitian product-fibre currents obeys the monotone full-density budget.  Positive local fibres,
including prime-cube faces, are cancelled only after the complete source is recombined. -/
theorem abs_tsum_thetaProductFiberActualPhaseCurrent_le_two_div_im
    {z : ℂ} (hz : 0 < z.im) :
    |∑' k : ℕ, thetaProductFiberActualPhaseCurrent k z| ≤
      (2 / z.im) * Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) := by
  rw [← thetaCuspTailSecondDensityPhase_current_eq_tsum_productFiberActualPhaseCurrent hz.le]
  exact abs_thetaCuspTailSecondDensityPhase_current_le_two_div_im hz

/-- Canonical transfer from the zero-free full one-sided density channel to the final odd Xi
Taylor section. -/
def xiCTaylorFullDensityTransferValue (d : ℕ) (z : ℂ) : ℂ :=
  (xiCTaylorPolynomial (2 * d + 3)).eval z /
    thetaCuspTailSecondDensityPhaseValue z

/-- Quotient-rule derivative of the canonical full-density transfer. -/
def xiCTaylorFullDensityTransferDerivative (d : ℕ) (z : ℂ) : ℂ :=
  ((xiCTaylorPolynomial (2 * d + 3)).derivative.eval z *
      thetaCuspTailSecondDensityPhaseValue z -
    (xiCTaylorPolynomial (2 * d + 3)).eval z *
      thetaCuspTailSecondDensityPhaseDerivative z) /
    thetaCuspTailSecondDensityPhaseValue z ^ 2

/-- Oriented current carried only by transfer from full density to finite Taylor truncation. -/
def xiCTaylorFullDensityTransferCurrent (d : ℕ) (z : ℂ) : ℝ :=
  (xiCTaylorFullDensityTransferDerivative d z *
    (starRingEnd ℂ) (xiCTaylorFullDensityTransferValue d z)).im

theorem xiCTaylorFullDensityTransferValue_mul_phaseValue
    (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    xiCTaylorFullDensityTransferValue d z *
        thetaCuspTailSecondDensityPhaseValue z =
      (xiCTaylorPolynomial (2 * d + 3)).eval z := by
  unfold xiCTaylorFullDensityTransferValue
  exact div_mul_cancel₀ _ (thetaCuspTailSecondDensityPhaseValue_ne_zero hz)

theorem normSq_xiCTaylorFullDensityTransferValue_mul_phaseValue
    (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
        Complex.normSq (xiCTaylorFullDensityTransferValue d z) =
      Complex.normSq ((xiCTaylorPolynomial (2 * d + 3)).eval z) := by
  rw [← xiCTaylorFullDensityTransferValue_mul_phaseValue d hz]
  simp only [Complex.normSq_apply, map_mul]
  ring

theorem xiCTaylorFullDensityTransfer_derivative_connection
    (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    xiCTaylorFullDensityTransferDerivative d z *
          thetaCuspTailSecondDensityPhaseValue z +
        xiCTaylorFullDensityTransferValue d z *
          thetaCuspTailSecondDensityPhaseDerivative z =
      (xiCTaylorPolynomial (2 * d + 3)).derivative.eval z := by
  have hne := thetaCuspTailSecondDensityPhaseValue_ne_zero hz
  unfold xiCTaylorFullDensityTransferDerivative xiCTaylorFullDensityTransferValue
  field_simp [hne]
  ring

/-- **Exact frontier factorization.**  Final Taylor current is the zero-free full-density current
plus one transfer current, with complementary squared-modulus weights.  No denominator estimate
or nonvanishing assumption on the Taylor section is used. -/
theorem xiCTaylor_orientedCurrent_eq_fullDensity_add_transfer
    (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    orientedPolynomialCurrent (xiCTaylorPolynomial (2 * d + 3)) z =
      Complex.normSq (xiCTaylorFullDensityTransferValue d z) *
          (thetaCuspTailSecondDensityPhaseDerivative z *
            (starRingEnd ℂ) (thetaCuspTailSecondDensityPhaseValue z)).im +
        Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
          xiCTaylorFullDensityTransferCurrent d z := by
  have hvalue := xiCTaylorFullDensityTransferValue_mul_phaseValue d hz
  have hderivative := xiCTaylorFullDensityTransfer_derivative_connection d hz
  have hproduct :=
    GaloisForLFunctions.HTGeometry.orientedPhaseCurrent_mul_identity
    (xiCTaylorFullDensityTransferValue d z)
    (xiCTaylorFullDensityTransferDerivative d z)
    (thetaCuspTailSecondDensityPhaseValue z)
    (thetaCuspTailSecondDensityPhaseDerivative z)
  rw [hvalue, hderivative] at hproduct
  simpa only [orientedPolynomialCurrent, xiCTaylorFullDensityTransferCurrent, add_comm]
    using hproduct

/-- Unconditional frontier bound with final Taylor norm preserved.  Full-density arithmetic current
is completely discharged; every remaining positive contribution is carried by the canonical
finite-truncation transfer current. -/
theorem xiCTaylor_orientedCurrent_le_fullDensity_budget_add_transfer
    (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    orientedPolynomialCurrent (xiCTaylorPolynomial (2 * d + 3)) z ≤
      (2 / z.im) *
          Complex.normSq ((xiCTaylorPolynomial (2 * d + 3)).eval z) +
        Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
          xiCTaylorFullDensityTransferCurrent d z := by
  rw [xiCTaylor_orientedCurrent_eq_fullDensity_add_transfer d hz]
  have hcurrent :
      (thetaCuspTailSecondDensityPhaseDerivative z *
          (starRingEnd ℂ) (thetaCuspTailSecondDensityPhaseValue z)).im ≤
        (2 / z.im) * Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) :=
    le_trans (le_abs_self _)
      (abs_thetaCuspTailSecondDensityPhase_current_le_two_div_im hz)
  have hfactor :
      Complex.normSq (xiCTaylorFullDensityTransferValue d z) *
          Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) =
        Complex.normSq ((xiCTaylorPolynomial (2 * d + 3)).eval z) := by
    rw [← xiCTaylorFullDensityTransferValue_mul_phaseValue d hz]
    simp only [Complex.normSq_apply, map_mul]
  calc
    Complex.normSq (xiCTaylorFullDensityTransferValue d z) *
          (thetaCuspTailSecondDensityPhaseDerivative z *
            (starRingEnd ℂ) (thetaCuspTailSecondDensityPhaseValue z)).im +
        Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
          xiCTaylorFullDensityTransferCurrent d z ≤
      Complex.normSq (xiCTaylorFullDensityTransferValue d z) *
          ((2 / z.im) * Complex.normSq (thetaCuspTailSecondDensityPhaseValue z)) +
        Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
          xiCTaylorFullDensityTransferCurrent d z := by
      have hmul := mul_le_mul_of_nonneg_left hcurrent
        (Complex.normSq_nonneg (xiCTaylorFullDensityTransferValue d z))
      simpa only [add_comm] using add_le_add_right hmul
        (Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
          xiCTaylorFullDensityTransferCurrent d z)
    _ = (2 / z.im) *
          Complex.normSq ((xiCTaylorPolynomial (2 * d + 3)).eval z) +
        Complex.normSq (thetaCuspTailSecondDensityPhaseValue z) *
          xiCTaylorFullDensityTransferCurrent d z := by
      rw [← hfactor]
      ring

/-- Exact remaining source obligation after the full-density aggregate current is discharged.
Unlike earlier seam predicates, this retains the norm of the final odd Xi Taylor section because
`P = transfer * fullDensity` exactly. -/
def XiCTaylorFullDensityTransferCurrentSublinearUpper (D : ℕ → ℕ) : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        xiCTaylorFullDensityTransferCurrent
            (D (xiCTaylorAnisotropicScheduleStage sigma n))
            (xiCTaylorAnisotropicCenteredPoint sigma n) <
          (epsilon * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              (xiCTaylorFullDensityTransferValue
                (D (xiCTaylorAnisotropicScheduleStage sigma n))
                (xiCTaylorAnisotropicCenteredPoint sigma n))

/-- **RH connector.**  Sublinear current for the sole canonical transfer factor proves RH.  The
full-density term contributes only `O(1)` normalized current along every anisotropic mesh and is
absorbed into an arbitrary positive linear budget. -/
theorem riemannHypothesis_of_xiCTaylorFullDensityTransferCurrentSublinearUpper
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (htransfer : XiCTaylorFullDensityTransferCurrentSublinearUpper D) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiCTaylorAnisotropicOrientedCoefficientSublinearUpper
    hD.1
  intro sigma hsigmaPos hsigmaHalf epsilon hepsilon
  let eta : ℝ := (xiCTaylorCenteredPoint sigma).im
  have heta : 0 < eta := by
    dsimp only [eta, xiCTaylorCenteredPoint]
    rw [mul_im]
    simp only [sub_re, neg_re, I_re, neg_im, I_im]
    norm_num
    linarith
  have himTend : Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds eta) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have himLower : ∀ᶠ n : ℕ in atTop,
      eta / 2 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    himTend.eventually (eventually_gt_nhds (by linarith))
  have hnat : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  have hscale : ∀ᶠ n : ℕ in atTop,
      4 / eta < delta * (((n + 1 : ℕ) : ℝ)) := by
    have hgrow := hnat.atTop_mul_const hdelta
    have hevent := hgrow.eventually_gt_atTop (4 / eta)
    simpa only [mul_comm] using hevent
  have htransferEventually :=
    htransfer sigma hsigmaPos hsigmaHalf delta hdelta
  filter_upwards [himLower, hscale, htransferEventually] with n him hscaled htrans
  let d : ℕ := D (xiCTaylorAnisotropicScheduleStage sigma n)
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (2 * d + 3)
  let F : ℂ := thetaCuspTailSecondDensityPhaseValue z
  let T : ℂ := xiCTaylorFullDensityTransferValue d z
  have hz : 0 < z.im := (half_pos heta).trans him
  have hFpos : 0 < Complex.normSq F := by
    rw [Complex.normSq_pos]
    exact thetaCuspTailSecondDensityPhaseValue_ne_zero hz
  have hcoefficient : 2 / z.im ≤ delta * (((n + 1 : ℕ) : ℝ)) := by
    calc
      2 / z.im ≤ 2 / (eta / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (half_pos heta) him.le
      _ = 4 / eta := by field_simp; ring
      _ ≤ delta * (((n + 1 : ℕ) : ℝ)) := hscaled.le
  have hfactor : Complex.normSq F * Complex.normSq T =
      Complex.normSq (P.eval z) := by
    simpa only [F, T, P] using
      normSq_xiCTaylorFullDensityTransferValue_mul_phaseValue d hz
  have hbase :
      (2 / z.im) * Complex.normSq (P.eval z) ≤
        (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) :=
    mul_le_mul_of_nonneg_right hcoefficient (Complex.normSq_nonneg _)
  have htrans' : Complex.normSq F *
        xiCTaylorFullDensityTransferCurrent d z <
      (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) := by
    have hmul := mul_lt_mul_of_pos_left htrans hFpos
    dsimp only [d, z] at hmul ⊢
    rw [show Complex.normSq F *
          ((delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq T) =
        (delta * (((n + 1 : ℕ) : ℝ))) *
          (Complex.normSq F * Complex.normSq T) by ring,
      hfactor] at hmul
    exact hmul
  have hfrontier :=
    xiCTaylor_orientedCurrent_le_fullDensity_budget_add_transfer d hz
  change orientedPolynomialCurrent P z <
    (epsilon * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z)
  calc
    orientedPolynomialCurrent P z ≤
        (2 / z.im) * Complex.normSq (P.eval z) +
          Complex.normSq F * xiCTaylorFullDensityTransferCurrent d z := by
      simpa only [P, F] using hfrontier
    _ < (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) +
        (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) :=
      add_lt_add_of_le_of_lt hbase htrans'
    _ = (epsilon * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) := by
      dsimp only [delta]
      ring

/-- Under RH the canonical transfer current is sublinear.  Together with the forward connector,
this shows that no RH content remains in the zero-free full-density base: it is concentrated
exactly in the finite-truncation transfer factor. -/
theorem xiCTaylorFullDensityTransferCurrentSublinearUpper_of_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hRH : RiemannHypothesis) :
    XiCTaylorFullDensityTransferCurrentSublinearUpper D := by
  have hcoefficient :=
    xiCTaylorAnisotropicOrientedCoefficientSublinearUpper_of_riemannHypothesis
      hD.1 hRH
  intro sigma hsigmaPos hsigmaHalf epsilon hepsilon
  let eta : ℝ := (xiCTaylorCenteredPoint sigma).im
  have heta : 0 < eta := by
    dsimp only [eta, xiCTaylorCenteredPoint]
    rw [mul_im]
    simp only [sub_re, neg_re, I_re, neg_im, I_im]
    norm_num
    linarith
  have himTend : Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds eta) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have himLower : ∀ᶠ n : ℕ in atTop,
      eta / 2 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    himTend.eventually (eventually_gt_nhds (by linarith))
  have hnat : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  have hscale : ∀ᶠ n : ℕ in atTop,
      4 / eta < delta * (((n + 1 : ℕ) : ℝ)) := by
    have hgrow := hnat.atTop_mul_const hdelta
    have hevent := hgrow.eventually_gt_atTop (4 / eta)
    simpa only [mul_comm] using hevent
  have hcoefficientEventually :=
    hcoefficient sigma hsigmaPos hsigmaHalf delta hdelta
  filter_upwards [himLower, hscale, hcoefficientEventually] with n him hscaled hP
  let d : ℕ := D (xiCTaylorAnisotropicScheduleStage sigma n)
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let P : Polynomial ℂ := xiCTaylorPolynomial (2 * d + 3)
  let F : ℂ := thetaCuspTailSecondDensityPhaseValue z
  let Df : ℂ := thetaCuspTailSecondDensityPhaseDerivative z
  let T : ℂ := xiCTaylorFullDensityTransferValue d z
  let Jf : ℝ := (Df * (starRingEnd ℂ) F).im
  let Jt : ℝ := xiCTaylorFullDensityTransferCurrent d z
  have hz : 0 < z.im := (half_pos heta).trans him
  have hFpos : 0 < Complex.normSq F := by
    rw [Complex.normSq_pos]
    exact thetaCuspTailSecondDensityPhaseValue_ne_zero hz
  have hfactor : Complex.normSq F * Complex.normSq T =
      Complex.normSq (P.eval z) := by
    simpa only [F, T, P] using
      normSq_xiCTaylorFullDensityTransferValue_mul_phaseValue d hz
  have hcoefficientBase : 2 / z.im ≤
      delta * (((n + 1 : ℕ) : ℝ)) := by
    calc
      2 / z.im ≤ 2 / (eta / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (half_pos heta) him.le
      _ = 4 / eta := by field_simp; ring
      _ ≤ delta * (((n + 1 : ℕ) : ℝ)) := hscaled.le
  have hbase :
      (2 / z.im) * Complex.normSq (P.eval z) ≤
        (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) :=
    mul_le_mul_of_nonneg_right hcoefficientBase (Complex.normSq_nonneg _)
  have habs : |Jf| ≤ (2 / z.im) * Complex.normSq F := by
    simpa only [Jf, Df, F] using
      abs_thetaCuspTailSecondDensityPhase_current_le_two_div_im hz
  have hnegativeBase : -(Complex.normSq T * Jf) ≤
      (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) := by
    calc
      -(Complex.normSq T * Jf) = Complex.normSq T * (-Jf) := by ring
      _ ≤ Complex.normSq T * |Jf| :=
        mul_le_mul_of_nonneg_left (neg_le_abs Jf) (Complex.normSq_nonneg _)
      _ ≤ Complex.normSq T *
          ((2 / z.im) * Complex.normSq F) :=
        mul_le_mul_of_nonneg_left habs (Complex.normSq_nonneg _)
      _ = (2 / z.im) * Complex.normSq (P.eval z) := by
        rw [← hfactor]
        ring
      _ ≤ (delta * (((n + 1 : ℕ) : ℝ))) *
          Complex.normSq (P.eval z) := hbase
  have hidentity :=
    xiCTaylor_orientedCurrent_eq_fullDensity_add_transfer d hz
  have hP' : orientedPolynomialCurrent P z <
      (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) := by
    simpa only [P, d, z, xiCTaylorOddDegreeSchedule] using hP
  have htransferMul : Complex.normSq F * Jt <
      (epsilon * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) := by
    have heq : Complex.normSq F * Jt =
        orientedPolynomialCurrent P z - Complex.normSq T * Jf := by
      dsimp only [P, F, T, Df, Jf, Jt] at hidentity ⊢
      linarith
    rw [heq]
    calc
      orientedPolynomialCurrent P z - Complex.normSq T * Jf <
          (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) +
            (delta * (((n + 1 : ℕ) : ℝ))) * Complex.normSq (P.eval z) := by
        linarith
      _ = (epsilon * (((n + 1 : ℕ) : ℝ))) *
          Complex.normSq (P.eval z) := by
        dsimp only [delta]
        ring
  have hmul : Complex.normSq F * Jt <
      Complex.normSq F *
        ((epsilon * (((n + 1 : ℕ) : ℝ))) * Complex.normSq T) := by
    calc
      Complex.normSq F * Jt <
          (epsilon * (((n + 1 : ℕ) : ℝ))) *
            Complex.normSq (P.eval z) := htransferMul
      _ = Complex.normSq F *
          ((epsilon * (((n + 1 : ℕ) : ℝ))) * Complex.normSq T) := by
        rw [← hfactor]
        ring
  exact (mul_lt_mul_iff_of_pos_left hFpos).mp hmul

/-- New exact RH-equivalent frontier: sublinear current of the canonical transfer from the
zero-free full theta-density channel to finite odd Xi Taylor sections. -/
theorem xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D) :
    XiCTaylorFullDensityTransferCurrentSublinearUpper D ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiCTaylorFullDensityTransferCurrentSublinearUpper hD
  · exact xiCTaylorFullDensityTransferCurrentSublinearUpper_of_riemannHypothesis hD

/-- Existence of an admissible odd schedule with sublinear full-density transfer current is exactly
RH; no schedule is supplied by the caller. -/
theorem exists_xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis :
    (∃ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D ∧
      XiCTaylorFullDensityTransferCurrentSublinearUpper D) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨D, hD, htransfer⟩
    exact
      (xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis hD).1
        htransfer
  · intro hRH
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact ⟨D, hD,
      (xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis hD).2 hRH⟩

/-- Uniform sublinearity over every admissible odd schedule is exactly RH. -/
theorem forall_xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis :
    (∀ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D →
      XiCTaylorFullDensityTransferCurrentSublinearUpper D) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact
      (xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis hD).1
        (hall D hD)
  · intro hRH D hD
    exact
      (xiCTaylorFullDensityTransferCurrentSublinearUpper_iff_riemannHypothesis hD).2 hRH

end

end RHTower
