import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexFiniteChebyshevSample
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeGlobalNyquistCurrentExchange
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaKelvinLaplaceDetailedBalance

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set
open GaloisForLFunctions

noncomputable section

namespace RHTower

def routeUPolarSpectralPoint : ℂ := Complex.I / 2

def routeUPolarCayleyCoordinate (k : ℕ) : ℝ :=
  let a := routeUHardEdgeMass (k : ℝ)
  (a ^ 2 + 1 / 4) / (a ^ 2 - 1 / 4)

def routeUPolarFourierSample (n : ℕ) (g : SchwartzMap ℝ ℝ) : ℝ :=
  (routeUComplexPositiveFourierExtension n (routeURealEvenAmplitude g)
    routeUPolarSpectralPoint).re

theorem routeUHardEdgeMass_natCast_eq (k : ℕ) :
    routeUHardEdgeMass (k : ℝ) = (k : ℝ) + 1 := by
  rw [routeUHardEdgeMass, abs_of_nonneg (Nat.cast_nonneg k)]
  ring

theorem routeUPolarCayleyCoordinate_eq_xiHardEdgeCayleyCoordinate (k : ℕ) :
    (routeUPolarCayleyCoordinate k : ℂ) =
      xiHardEdgeCayleyCoordinate (routeUHardEdgeMass (k : ℝ) : ℂ)
        routeUPolarSpectralPoint := by
  rw [routeUPolarCayleyCoordinate, routeUPolarSpectralPoint,
    xiHardEdgeCayleyCoordinate]
  push_cast
  have hsquare : (Complex.I / 2) ^ 2 = -(1 / 4 : ℂ) := by
    rw [div_pow, Complex.I_sq]
    norm_num
  rw [hsquare]
  ring

theorem routeUHardEdgeMass_add_I_mul_polar_ne_zero (r : ℝ) :
    (routeUHardEdgeMass r : ℂ) + Complex.I * routeUPolarSpectralPoint ≠ 0 := by
  rw [routeUPolarSpectralPoint]
  have ha1 : 1 ≤ routeUHardEdgeMass r := by simp [routeUHardEdgeMass]
  rw [show (routeUHardEdgeMass r : ℂ) + Complex.I * (Complex.I / 2) =
      ((routeUHardEdgeMass r - 1 / 2 : ℝ) : ℂ) by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

theorem routeUHardEdgeMass_sub_I_mul_polar_ne_zero (r : ℝ) :
    (routeUHardEdgeMass r : ℂ) - Complex.I * routeUPolarSpectralPoint ≠ 0 := by
  rw [routeUPolarSpectralPoint]
  have ha := routeUHardEdgeMass_pos r
  rw [show (routeUHardEdgeMass r : ℂ) - Complex.I * (Complex.I / 2) =
      ((routeUHardEdgeMass r + 1 / 2 : ℝ) : ℂ) by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

theorem routeUPolarPhase_re_zero (r : ℝ) :
    (routeUComplexHardEdgePhase r routeUPolarSpectralPoint).re = 0 := by
  let a : ℝ := routeUHardEdgeMass r
  have ha : 0 < a := routeUHardEdgeMass_pos r
  have hnum : 0 < 1 - 1 / (2 * a) := by
    have ha1 : 1 ≤ a := by simp [a, routeUHardEdgeMass]
    apply sub_pos.mpr
    rw [div_lt_one (by positivity : 0 < 2 * a)]
    linarith
  have hden : 0 < 1 + 1 / (2 * a) := by positivity
  have hratio :
      (1 + (routeUPolarSpectralPoint / (a : ℂ)) * Complex.I) /
          (1 - (routeUPolarSpectralPoint / (a : ℂ)) * Complex.I) =
        (((1 - 1 / (2 * a)) / (1 + 1 / (2 * a)) : ℝ) : ℂ) := by
    rw [routeUPolarSpectralPoint]
    push_cast
    field_simp [ha.ne']
    rw [Complex.I_sq]
    ring
  rw [routeUComplexHardEdgePhase, Complex.arctan]
  change ((a : ℂ) * (-Complex.I / 2 * Complex.log
    ((1 + (routeUPolarSpectralPoint / (a : ℂ)) * Complex.I) /
      (1 - (routeUPolarSpectralPoint / (a : ℂ)) * Complex.I)))).re = 0
  rw [hratio, ← Complex.ofReal_log (div_nonneg hnum.le hden.le)]
  simp [Complex.mul_re, Complex.mul_im]

theorem routeUPolarPhase_im_abs_le_one (r : ℝ) :
    |(routeUComplexHardEdgePhase r routeUPolarSpectralPoint).im| ≤ 1 := by
  let a : ℝ := routeUHardEdgeMass r
  let w : ℂ := routeUPolarSpectralPoint / (a : ℂ)
  have ha : 1 ≤ a := by simp [a, routeUHardEdgeMass]
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hwi : |w.im| = 1 / (2 * a) := by
    dsimp only [w]
    rw [routeUPolarSpectralPoint, Complex.div_im]
    simp [Complex.normSq_apply]
    rw [abs_of_pos (by positivity : 0 < (2 : ℝ)⁻¹ * a / (a * a))]
    field_simp [hapos.ne']
  have hwle : |w.im| ≤ 1 / 2 := by
    rw [hwi]
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).2
    nlinarith
  have hwone : |w.im| < 1 := hwle.trans_lt (by norm_num)
  have hatan := abs_complex_arctan_im_le_of_abs_im_lt_one hwone
  rw [routeUComplexHardEdgePhase]
  change |((a : ℂ) * Complex.arctan w).im| ≤ 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [abs_mul, abs_of_pos hapos]
  calc
    a * |(Complex.arctan w).im| ≤ a * (|w.im| / (1 - |w.im|)) := by gcongr
    _ = a / (2 * a - 1) := by
      rw [hwi]
      field_simp [hapos.ne']
    _ ≤ 1 := by
      apply (div_le_one (by linarith : 0 < 2 * a - 1)).2
      linarith

def routeUPolarAntipodalPhase (r : ℝ) : ℂ :=
  routeUComplexHardEdgePhase r routeUPolarSpectralPoint +
    (routeUHardEdgeAliasPeriod r / 2 : ℝ)

theorem routeUPolarAntipodalPhase_re (r : ℝ) :
    (routeUPolarAntipodalPhase r).re = routeUHardEdgeAliasPeriod r / 2 := by
  rw [routeUPolarAntipodalPhase, Complex.add_re, Complex.ofReal_re,
    routeUPolarPhase_re_zero, zero_add]

theorem routeUPolarAntipodalPhase_im_abs_le_one (r : ℝ) :
    |(routeUPolarAntipodalPhase r).im| ≤ 1 := by
  rw [routeUPolarAntipodalPhase, Complex.add_im, Complex.ofReal_im, add_zero]
  exact routeUPolarPhase_im_abs_le_one r

theorem routeUPolarShiftedPhase_pair_eq_two_chebyshev_neg
    (r : ℝ) (m : ℕ) :
    Complex.exp
        (Complex.I * routeUPolarAntipodalPhase r *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) +
      Complex.exp
        (Complex.I * routeUPolarAntipodalPhase r *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) =
      2 * evalRealPolynomial (Polynomial.Chebyshev.T ℝ (m : ℤ))
        (-(xiHardEdgeCayleyCoordinate (routeUHardEdgeMass r : ℂ)
          routeUPolarSpectralPoint)) := by
  have hbase := routeUComplexHardEdgePhase_pair_eq_two_chebyshev_general
    r routeUPolarSpectralPoint
      (routeUHardEdgeMass_add_I_mul_polar_ne_zero r)
      (routeUHardEdgeMass_sub_I_mul_polar_ne_zero r) m
  have hmesh := routeUHardEdgeMesh_mul_aliasPeriod r
  have hmeshC : (routeUHardEdgeMesh r : ℂ) *
      (routeUHardEdgeAliasPeriod r : ℂ) = 2 * Real.pi := by
    exact_mod_cast hmesh
  have hpos : Complex.exp
      (Complex.I * routeUPolarAntipodalPhase r *
        (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) =
      (-1 : ℂ) ^ m * Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ)) := by
    rw [show Complex.I * routeUPolarAntipodalPhase r *
        (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ) =
      ((m : ℂ) * (Real.pi * Complex.I)) +
        Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
          (((routeUHardEdgeMesh r) * (m : ℝ) : ℝ) : ℂ) by
      rw [routeUPolarAntipodalPhase]
      push_cast
      calc
        Complex.I *
              (routeUComplexHardEdgePhase r routeUPolarSpectralPoint +
                (routeUHardEdgeAliasPeriod r : ℂ) / 2) *
              ((routeUHardEdgeMesh r : ℂ) * (m : ℂ)) =
            (m : ℂ) *
                (Complex.I * ((routeUHardEdgeMesh r : ℂ) *
                  (routeUHardEdgeAliasPeriod r : ℂ)) / 2) +
              Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
                ((routeUHardEdgeMesh r : ℂ) * (m : ℂ)) := by ring
        _ = (m : ℂ) * (Real.pi * Complex.I) +
              Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
                ((routeUHardEdgeMesh r : ℂ) * (m : ℂ)) := by rw [hmeshC]; ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have hneg : Complex.exp
      (Complex.I * routeUPolarAntipodalPhase r *
        (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) =
      (-1 : ℂ) ^ m * Complex.exp
        (Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ)) := by
    rw [show Complex.I * routeUPolarAntipodalPhase r *
        (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ) =
      ((m : ℂ) * (-(Real.pi * Complex.I))) +
        Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
          (((routeUHardEdgeMesh r) * (-(m : ℝ)) : ℝ) : ℂ) by
      rw [routeUPolarAntipodalPhase]
      push_cast
      calc
        Complex.I *
              (routeUComplexHardEdgePhase r routeUPolarSpectralPoint +
                (routeUHardEdgeAliasPeriod r : ℂ) / 2) *
              ((routeUHardEdgeMesh r : ℂ) * -(m : ℂ)) =
            (m : ℂ) *
                (-(Complex.I * ((routeUHardEdgeMesh r : ℂ) *
                  (routeUHardEdgeAliasPeriod r : ℂ)) / 2)) +
              Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
                ((routeUHardEdgeMesh r : ℂ) * -(m : ℂ)) := by ring
        _ = (m : ℂ) * (-(Real.pi * Complex.I)) +
              Complex.I * routeUComplexHardEdgePhase r routeUPolarSpectralPoint *
                ((routeUHardEdgeMesh r : ℂ) * -(m : ℂ)) := by rw [hmeshC]; ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    simp
  rw [hpos, hneg, ← mul_add, hbase]
  simp only [evalRealPolynomial, Polynomial.Chebyshev.map_T]
  rw [Polynomial.Chebyshev.T_eval_neg]
  rw [Int.cast_negOnePow_natCast]
  ac_rfl

def routeUPolarDirectPacketSample
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : ℝ :=
  (routeUExplicitFiniteChebyshevPacket n k g).eval
    (routeUPolarCayleyCoordinate k)

def routeUPolarAntipodalPacketSample
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : ℝ :=
  (routeUExplicitFiniteChebyshevPacket n k g).eval
    (-(routeUPolarCayleyCoordinate k))

theorem routeUPolarDirectPacketSample_eq_periodization
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    (routeUPolarDirectPacketSample n g k : ℂ) =
      routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) (k : ℝ)
        (routeUComplexHardEdgePhase (k : ℝ) routeUPolarSpectralPoint) := by
  have h := routeUComplexHardEdgePeriodizationAt_phase_eq_eval_finiteChebyshevPacket
    n g (k : ℝ) (routeUExplicitFiniteChebyshevCutoff n k)
      (routeURealEvenCompactApproximation_eq_zero_of_explicitCutoff n k · g)
      routeUPolarSpectralPoint
      (routeUHardEdgeMass_add_I_mul_polar_ne_zero (k : ℝ))
      (routeUHardEdgeMass_sub_I_mul_polar_ne_zero (k : ℝ))
  rw [← routeUPolarCayleyCoordinate_eq_xiHardEdgeCayleyCoordinate k] at h
  simp only [evalRealPolynomial_ofReal] at h
  simpa only [routeUPolarDirectPacketSample,
    routeUExplicitFiniteChebyshevPacket] using h.symm

theorem routeUPolarAntipodalPacketSample_eq_periodization
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    (routeUPolarAntipodalPacketSample n g k : ℂ) =
      routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) (k : ℝ)
        (routeUPolarAntipodalPhase (k : ℝ)) := by
  have h := routeUComplexHardEdgePeriodizationAt_eq_eval_finiteChebyshevPacket_of_pair
    n g (k : ℝ) (routeUExplicitFiniteChebyshevCutoff n k)
      (routeURealEvenCompactApproximation_eq_zero_of_explicitCutoff n k · g)
      (routeUPolarAntipodalPhase (k : ℝ))
      (-(xiHardEdgeCayleyCoordinate (routeUHardEdgeMass (k : ℝ) : ℂ)
        routeUPolarSpectralPoint))
      (routeUPolarShiftedPhase_pair_eq_two_chebyshev_neg (k : ℝ))
  rw [← routeUPolarCayleyCoordinate_eq_xiHardEdgeCayleyCoordinate k] at h
  have hnegCast : -(routeUPolarCayleyCoordinate k : ℂ) =
      ((-(routeUPolarCayleyCoordinate k) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hnegCast] at h
  simp only [evalRealPolynomial_ofReal] at h
  simpa only [routeUPolarAntipodalPacketSample,
    routeUExplicitFiniteChebyshevPacket] using h.symm

theorem tendsto_routeUHardEdgeAliasPeriod_natCast :
    Tendsto (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ)) atTop atTop := by
  have hmul := Tendsto.const_mul_atTop Real.pi_pos
    tendsto_routeUHardEdgeMass_natCast_atTop
  simpa only [routeUHardEdgeAliasPeriod] using hmul

theorem tendsto_routeUHardEdgeAliasPeriod_natCast_pow_four :
    Tendsto (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ) ^ 4) atTop atTop := by
  exact (tendsto_pow_atTop (n := 4) (by norm_num)).comp
    tendsto_routeUHardEdgeAliasPeriod_natCast

theorem tendsto_routeUPolarDirectPeriodization
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun k : ℕ =>
      routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) (k : ℝ)
        (routeUComplexHardEdgePhase (k : ℝ) routeUPolarSpectralPoint))
      atTop
      (nhds (routeUComplexPositiveFourierExtension n (routeURealEvenAmplitude g)
        routeUPolarSpectralPoint)) := by
  let f := routeURealEvenAmplitude g
  let z : ℕ → ℂ := fun k =>
    routeUComplexHardEdgePhase (k : ℝ) routeUPolarSpectralPoint
  let C : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  have hz : Tendsto z atTop (nhds routeUPolarSpectralPoint) :=
    tendsto_routeUComplexHardEdgePhase_natCast routeUPolarSpectralPoint
  have hzIm : ∀ k, |(z k).im| ≤ 1 := fun k =>
    routeUPolarPhase_im_abs_le_one (k : ℝ)
  have hcentral : Tendsto
      (fun k : ℕ => routeUComplexPositiveFourierExtension n f (z k)) atTop
      (nhds (routeUComplexPositiveFourierExtension n f routeUPolarSpectralPoint)) :=
    tendsto_routeUComplexPositiveFourierExtension_of_tendsto
      n f z routeUPolarSpectralPoint hz hzIm
  have hbound : Tendsto
      (fun k : ℕ => C / routeUHardEdgeAliasPeriod (k : ℝ) ^ 4)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_routeUHardEdgeAliasPeriod_natCast_pow_four
  have htail : Tendsto
      (fun k : ℕ => routeUComplexHardEdgeAliasTail n f (k : ℝ) (z k))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hbound
    exact Eventually.of_forall fun k => by
      have hzRe : |(z k).re| ≤ routeUHardEdgeAliasPeriod (k : ℝ) / 2 := by
        rw [show (z k).re = 0 by exact routeUPolarPhase_re_zero (k : ℝ)]
        simp only [abs_zero]
        exact div_nonneg (routeUHardEdgeAliasPeriod_pos (k : ℝ)).le (by norm_num)
      simpa only [C,
        GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent] using
        (norm_routeUComplexHardEdgeAliasTail_uniform_le n f (k : ℝ) (z k)
          (hzIm k) hzRe 1)
  have hsum := hcentral.add htail
  simpa only [add_zero, f, z] using hsum.congr'
    (Eventually.of_forall fun k => by
      have hzRe :
          |(routeUComplexHardEdgePhase (k : ℝ) routeUPolarSpectralPoint).re| ≤
            routeUHardEdgeAliasPeriod (k : ℝ) / 2 := by
        rw [routeUPolarPhase_re_zero]
        simp only [abs_zero]
        exact div_nonneg (routeUHardEdgeAliasPeriod_pos (k : ℝ)).le (by norm_num)
      exact (routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
        n (routeURealEvenAmplitude g) (k : ℝ)
          (routeUComplexHardEdgePhase (k : ℝ) routeUPolarSpectralPoint) hzRe).symm)

theorem tendsto_routeUPolarDirectPacketSample
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (routeUPolarDirectPacketSample n g) atTop
      (nhds (routeUPolarFourierSample n g)) := by
  have hcomplex : Tendsto
      (fun k : ℕ => (routeUPolarDirectPacketSample n g k : ℂ)) atTop
      (nhds (routeUComplexPositiveFourierExtension n (routeURealEvenAmplitude g)
        routeUPolarSpectralPoint)) :=
    (tendsto_routeUPolarDirectPeriodization n g).congr'
      (Eventually.of_forall fun k =>
        (routeUPolarDirectPacketSample_eq_periodization n g k).symm)
  have hre := (Complex.reCLM.continuous.tendsto _).comp hcomplex
  change Tendsto (routeUPolarDirectPacketSample n g) atTop
    (nhds (routeUPolarFourierSample n g)) at hre
  exact hre

theorem norm_routeUPolarAntipodalPeriodization_le
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    ‖routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) (k : ℝ)
        (routeUPolarAntipodalPhase (k : ℝ))‖ ≤
      (routeUComplexTiltUniformDecay n (routeURealEvenAmplitude g) 2 *
          (4 * Real.pi) ^ 4 +
        routeUComplexHardEdgeUniformAliasTailConstant n
          (routeURealEvenAmplitude g) 1) /
        routeUHardEdgeAliasPeriod (k : ℝ) ^ 4 := by
  let f := routeURealEvenAmplitude g
  let z := routeUPolarAntipodalPhase (k : ℝ)
  let L := routeUHardEdgeAliasPeriod (k : ℝ)
  let C := routeUComplexTiltUniformDecay n f 2 * (4 * Real.pi) ^ 4
  let D := routeUComplexHardEdgeUniformAliasTailConstant n f 1
  have hzIm : |z.im| ≤ 1 := routeUPolarAntipodalPhase_im_abs_le_one (k : ℝ)
  have hzReEq : |z.re| = L / 2 := by
    rw [show z.re = L / 2 by exact routeUPolarAntipodalPhase_re (k : ℝ)]
    rw [abs_of_nonneg]
    exact div_nonneg (routeUHardEdgeAliasPeriod_pos (k : ℝ)).le (by norm_num)
  have hzRe : |z.re| ≤ L / 2 := hzReEq.le
  have hzOuter : L / 2 ≤ |z.re| := hzReEq.ge
  have hcentral : ‖routeUComplexPositiveFourierExtension n f z‖ ≤ C / L ^ 4 := by
    simpa only [C, L, f, z] using
      norm_routeUComplexPositiveFourierExtension_outer_le
        n f (k : ℝ) z hzIm hzOuter
  have htail : ‖routeUComplexHardEdgeAliasTail n f (k : ℝ) z‖ ≤ D / L ^ 4 := by
    simpa only [D, L,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent] using
      norm_routeUComplexHardEdgeAliasTail_uniform_le n f (k : ℝ) z hzIm hzRe 1
  rw [routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail n f (k : ℝ) z hzRe]
  calc
    ‖routeUComplexPositiveFourierExtension n f z +
        routeUComplexHardEdgeAliasTail n f (k : ℝ) z‖ ≤
      ‖routeUComplexPositiveFourierExtension n f z‖ +
        ‖routeUComplexHardEdgeAliasTail n f (k : ℝ) z‖ := norm_add_le _ _
    _ ≤ C / L ^ 4 + D / L ^ 4 := add_le_add hcentral htail
    _ = (C + D) / L ^ 4 := by ring
    _ = _ := rfl

theorem tendsto_routeUPolarAntipodalPeriodization_zero
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun k : ℕ =>
      routeUComplexHardEdgePeriodizationAt n (routeURealEvenAmplitude g) (k : ℝ)
        (routeUPolarAntipodalPhase (k : ℝ))) atTop (nhds 0) := by
  let C : ℝ := routeUComplexTiltUniformDecay n (routeURealEvenAmplitude g) 2 *
      (4 * Real.pi) ^ 4 +
    routeUComplexHardEdgeUniformAliasTailConstant n (routeURealEvenAmplitude g) 1
  have hbound : Tendsto
      (fun k : ℕ => C / routeUHardEdgeAliasPeriod (k : ℝ) ^ 4)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_routeUHardEdgeAliasPeriod_natCast_pow_four
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hbound
  exact Eventually.of_forall fun k => by
    simpa only [C] using norm_routeUPolarAntipodalPeriodization_le n g k

theorem tendsto_routeUPolarAntipodalPacketSample_zero
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (routeUPolarAntipodalPacketSample n g) atTop (nhds 0) := by
  have hcomplex : Tendsto
      (fun k : ℕ => (routeUPolarAntipodalPacketSample n g k : ℂ)) atTop
      (nhds 0) :=
    (tendsto_routeUPolarAntipodalPeriodization_zero n g).congr'
      (Eventually.of_forall fun k =>
        (routeUPolarAntipodalPacketSample_eq_periodization n g k).symm)
  have hre := (Complex.reCLM.continuous.tendsto _).comp hcomplex
  change Tendsto (routeUPolarAntipodalPacketSample n g) atTop (nhds 0) at hre
  exact hre

def routeUPolarNormalizedCrossCapital
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : ℝ :=
  let a := routeUHardEdgeMass (k : ℝ)
  (routeUPolarDirectPacketSample n g k ^ 2 -
      routeUPolarAntipodalPacketSample n g k ^ 2) /
    (2 * (a ^ 2 - 1 / 4))

theorem tendsto_routeUPolarMassFactor_half :
    Tendsto (fun k : ℕ =>
      routeUHardEdgeMass (k : ℝ) ^ 2 /
        (2 * (routeUHardEdgeMass (k : ℝ) ^ 2 - 1 / 4)))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hmassSq : Tendsto
      (fun k : ℕ => routeUHardEdgeMass (k : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp
      tendsto_routeUHardEdgeMass_natCast_atTop
  have hquarter : Tendsto
      (fun k : ℕ => (1 / 4 : ℝ) / routeUHardEdgeMass (k : ℝ) ^ 2)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hmassSq
  have hden : Tendsto (fun k : ℕ =>
      2 * (1 - (1 / 4 : ℝ) / routeUHardEdgeMass (k : ℝ) ^ 2))
      atTop (nhds 2) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hquarter) using 1 <;> norm_num
  have hraw : Tendsto (fun k : ℕ =>
      1 / (2 * (1 - (1 / 4 : ℝ) / routeUHardEdgeMass (k : ℝ) ^ 2)))
      atTop (nhds (1 / 2 : ℝ)) := by
    exact tendsto_const_nhds.div hden (by norm_num)
  refine hraw.congr' (Eventually.of_forall fun k => ?_)
  have ha0 : routeUHardEdgeMass (k : ℝ) ≠ 0 :=
    (routeUHardEdgeMass_pos (k : ℝ)).ne'
  field_simp [ha0]

theorem tendsto_routeUPolarNormalizedCrossCapital_valuation_two
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun k : ℕ =>
      routeUHardEdgeMass (k : ℝ) ^ 2 *
        routeUPolarNormalizedCrossCapital n g k)
      atTop (nhds (routeUPolarFourierSample n g ^ 2 / 2)) := by
  have hdiff : Tendsto (fun k : ℕ =>
      routeUPolarDirectPacketSample n g k ^ 2 -
        routeUPolarAntipodalPacketSample n g k ^ 2)
      atTop (nhds (routeUPolarFourierSample n g ^ 2)) := by
    have h := (tendsto_routeUPolarDirectPacketSample n g).pow 2 |>.sub
      ((tendsto_routeUPolarAntipodalPacketSample_zero n g).pow 2)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h
  have hmul := tendsto_routeUPolarMassFactor_half.mul hdiff
  have hfinal : Tendsto (fun k : ℕ =>
      routeUHardEdgeMass (k : ℝ) ^ 2 *
        routeUPolarNormalizedCrossCapital n g k)
      atTop (nhds ((1 / 2 : ℝ) * routeUPolarFourierSample n g ^ 2)) := by
    refine hmul.congr' (Eventually.of_forall fun k => ?_)
    change routeUHardEdgeMass (k : ℝ) ^ 2 /
          (2 * (routeUHardEdgeMass (k : ℝ) ^ 2 - 1 / 4)) *
            (routeUPolarDirectPacketSample n g k ^ 2 -
              routeUPolarAntipodalPacketSample n g k ^ 2) =
      routeUHardEdgeMass (k : ℝ) ^ 2 *
        ((routeUPolarDirectPacketSample n g k ^ 2 -
            routeUPolarAntipodalPacketSample n g k ^ 2) /
          (2 * (routeUHardEdgeMass (k : ℝ) ^ 2 - 1 / 4)))
    ring
  rw [show routeUPolarFourierSample n g ^ 2 / 2 =
      (1 / 2 : ℝ) * routeUPolarFourierSample n g ^ 2 by ring]
  exact hfinal

theorem tendsto_routeUPolarNormalizedCrossCapital_zero
    (n : ℕ) (g : SchwartzMap ℝ ℝ) :
    Tendsto (routeUPolarNormalizedCrossCapital n g) atTop (nhds 0) := by
  have hmassSq : Tendsto
      (fun k : ℕ => routeUHardEdgeMass (k : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp
      tendsto_routeUHardEdgeMass_natCast_atTop
  have hinv : Tendsto
      (fun k : ℕ => (1 : ℝ) / routeUHardEdgeMass (k : ℝ) ^ 2)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hmassSq
  have hmul := hinv.mul
    (tendsto_routeUPolarNormalizedCrossCapital_valuation_two n g)
  simpa only [zero_mul] using hmul.congr'
    (Eventually.of_forall fun k => by
      have ha0 : routeUHardEdgeMass (k : ℝ) ≠ 0 :=
        (routeUHardEdgeMass_pos (k : ℝ)).ne'
      field_simp [ha0])

private theorem routeUPolarIntegral_pow_mul_exp_neg_mul_Ioi
    (m : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ m * Real.exp (-(c * t))) =
      m.factorial / c ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (m : ℝ) + 1) (r := c) (by positivity) hc
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  rw [h, Real.Gamma_nat_eq_factorial]
  rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  simp only [one_div, inv_pow]
  ring

def routeUHardEdgeFilteredPolarCrossCapital (a : ℝ) (P : Polynomial ℝ) : ℝ :=
  let d := routeUHardEdgeKelvinDegree a P
  let Qe := routeUHardEdgeKelvinEvenReversedPolynomial a P
  let Qo := routeUHardEdgeKelvinOddReversedPolynomial a P
  ∫ t in Ioi (0 : ℝ),
    t ^ (2 * d) * Real.exp (-(a ^ 2 * t)) *
      (2 * Real.pi * Qe.eval (-(1 / 4 : ℝ)) *
        Qo.eval (-(1 / 4 : ℝ)) * Real.exp (t / 4))

theorem eval_routeUHardEdgeEvenChannel_mul_oddChannel
    (P : Polynomial ℝ) (x : ℝ) :
    (routeUHardEdgeEvenChannel P).eval x *
        (routeUHardEdgeOddChannel P).eval x =
      (P.eval x ^ 2 - P.eval (-x) ^ 2) / 4 := by
  rw [routeUHardEdgeEvenChannel, routeUHardEdgeOddChannel]
  simp only [Polynomial.eval_smul, Polynomial.eval_add, Polynomial.eval_sub,
    eval_routeUHardEdgeAntipodalPolynomial, smul_eq_mul]
  ring

theorem routeUHardEdgeFilteredPolarCrossCapital_eq
    {a : ℝ} (ha : 1 / 2 < a) (P : Polynomial ℝ) :
    routeUHardEdgeFilteredPolarCrossCapital a P =
      Real.pi * ((2 * routeUHardEdgeKelvinDegree a P).factorial : ℝ) *
        ((P.eval ((a ^ 2 + 1 / 4) / (a ^ 2 - 1 / 4))) ^ 2 -
          (P.eval (-((a ^ 2 + 1 / 4) / (a ^ 2 - 1 / 4)))) ^ 2) /
            (2 * (a ^ 2 - 1 / 4)) := by
  let d := routeUHardEdgeKelvinDegree a P
  let E := routeUHardEdgeEvenChannel P
  let O := routeUHardEdgeOddChannel P
  let Qe := routeUHardEdgeKelvinEvenReversedPolynomial a P
  let Qo := routeUHardEdgeKelvinOddReversedPolynomial a P
  let c : ℝ := a ^ 2 - 1 / 4
  let z : ℝ := (a ^ 2 + 1 / 4) / c
  have hc : 0 < c := by
    dsimp only [c]
    nlinarith [sq_nonneg (a - 1 / 2)]
  have hW : a ^ 2 + (-(1 / 4 : ℝ)) ≠ 0 := by
    change c ≠ 0
    exact hc.ne'
  have hQe : Qe.eval (-(1 / 4 : ℝ)) = c ^ d * E.eval z := by
    have h := eval_routeUHardEdgeCommonLeftReversedPolynomial
      a E O (W := -(1 / 4 : ℝ)) hW
    simpa only [Qe, E, O, d, routeUHardEdgeKelvinEvenReversedPolynomial,
      routeUHardEdgeKelvinDegree, c, z, sub_eq_add_neg, sub_neg_eq_add,
      neg_neg] using h
  have hQo : Qo.eval (-(1 / 4 : ℝ)) = c ^ d * O.eval z := by
    have h := eval_routeUHardEdgeCommonRightReversedPolynomial
      a E O (W := -(1 / 4 : ℝ)) hW
    simpa only [Qo, E, O, d, routeUHardEdgeKelvinOddReversedPolynomial,
      routeUHardEdgeKelvinDegree, c, z, sub_eq_add_neg, sub_neg_eq_add,
      neg_neg] using h
  have hQprod : Qe.eval (-(1 / 4 : ℝ)) * Qo.eval (-(1 / 4 : ℝ)) =
      c ^ (2 * d) * (P.eval z ^ 2 - P.eval (-z) ^ 2) / 4 := by
    rw [hQe, hQo]
    change c ^ d * E.eval z * (c ^ d * O.eval z) = _
    have hEO : E.eval z * O.eval z =
        (P.eval z ^ 2 - P.eval (-z) ^ 2) / 4 := by
      simpa only [E, O] using eval_routeUHardEdgeEvenChannel_mul_oddChannel P z
    calc
      c ^ d * E.eval z * (c ^ d * O.eval z) =
          c ^ (2 * d) * (E.eval z * O.eval z) := by
        rw [show 2 * d = d + d by omega, pow_add]
        ring
      _ = _ := by rw [hEO]; ring
  have hfun : (fun t : ℝ =>
      t ^ (2 * d) * Real.exp (-(a ^ 2 * t)) *
        (2 * Real.pi * Qe.eval (-(1 / 4 : ℝ)) *
          Qo.eval (-(1 / 4 : ℝ)) * Real.exp (t / 4))) =
      fun t : ℝ =>
        (2 * Real.pi * Qe.eval (-(1 / 4 : ℝ)) *
          Qo.eval (-(1 / 4 : ℝ))) *
            (t ^ (2 * d) * Real.exp (-(c * t))) := by
    funext t
    have hexp : Real.exp (-(a ^ 2 * t)) * Real.exp (t / 4) =
        Real.exp (-(c * t)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [c]
      ring
    rw [← hexp]
    ring
  rw [routeUHardEdgeFilteredPolarCrossCapital]
  change (∫ t in Ioi (0 : ℝ),
      t ^ (2 * d) * Real.exp (-(a ^ 2 * t)) *
        (2 * Real.pi * Qe.eval (-(1 / 4 : ℝ)) *
          Qo.eval (-(1 / 4 : ℝ)) * Real.exp (t / 4))) = _
  rw [hfun, integral_const_mul,
    routeUPolarIntegral_pow_mul_exp_neg_mul_Ioi (2 * d) hc]
  rw [show 2 * Real.pi * Qe.eval (-(1 / 4 : ℝ)) *
      Qo.eval (-(1 / 4 : ℝ)) *
        (((2 * d).factorial : ℝ) / c ^ (2 * d + 1)) =
      2 * Real.pi *
        (Qe.eval (-(1 / 4 : ℝ)) * Qo.eval (-(1 / 4 : ℝ))) *
          (((2 * d).factorial : ℝ) / c ^ (2 * d + 1)) by ring,
    hQprod]
  change 2 * Real.pi *
      (c ^ (2 * d) * (P.eval z ^ 2 - P.eval (-z) ^ 2) / 4) *
        (((2 * d).factorial : ℝ) / c ^ (2 * d + 1)) =
    Real.pi * ((2 * d).factorial : ℝ) *
      (P.eval z ^ 2 - P.eval (-z) ^ 2) / (2 * c)
  rw [show 2 * d + 1 = (2 * d) + 1 by omega, pow_succ]
  field_simp [hc.ne']
  ring

def routeUExplicitFilteredPolarCrossCapital
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) : ℝ :=
  routeUHardEdgeFilteredPolarCrossCapital (routeUHardEdgeMass (k : ℝ))
    (routeUExplicitFiniteChebyshevPacket n k g)

theorem routeUExplicitFilteredPolarCrossCapital_eq_normalized
    (n : ℕ) (g : SchwartzMap ℝ ℝ) (k : ℕ) :
    routeUExplicitFilteredPolarCrossCapital n g k =
      Real.pi *
        ((2 * routeUHardEdgeKelvinDegree (routeUHardEdgeMass (k : ℝ))
          (routeUExplicitFiniteChebyshevPacket n k g)).factorial : ℝ) *
        routeUPolarNormalizedCrossCapital n g k := by
  rw [routeUExplicitFilteredPolarCrossCapital,
    routeUHardEdgeFilteredPolarCrossCapital_eq
      (P := routeUExplicitFiniteChebyshevPacket n k g)
      (by
        have h : 1 ≤ routeUHardEdgeMass (k : ℝ) := by simp [routeUHardEdgeMass]
        linarith)]
  simp only [routeUPolarNormalizedCrossCapital,
    routeUPolarDirectPacketSample, routeUPolarAntipodalPacketSample,
    routeUPolarCayleyCoordinate]
  ring

end RHTower
