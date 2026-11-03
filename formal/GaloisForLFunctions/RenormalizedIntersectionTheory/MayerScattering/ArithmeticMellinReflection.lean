import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.ResonantCoreEndpointBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoreZeroMoment
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.HTGeometry.CausalFourierBridge
import GaloisForLFunctions.HTGeometry.AtomlessPhaseFormation
import GaloisForLFunctions.RHTower.L2FourierConjugation
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

/-!
# Arithmetic reflection of physical Mellin profiles

The normalized theta fields reflect through one arithmetic phase on the imaginary Mellin axis.
The phase is unimodular independently of the spectral parameter. Fourier transport realizes
an antiunitary on logarithmic Haar space and exchanges the actual resonant fields.
Cauchy averaging contributes a separate, explicit reflection multiplier.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerCoreMellin MayerCoreZeroMoment

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The arithmetic reflection phase, with the removable completed-zeta singularity filled. -/
def mayerArithmeticMellinPhase (t : ℝ) : ℂ :=
  (((t : ℂ) * I + 1) / ((t : ℂ) * I - 1)) *
    _root_.RHTower.xi ((t : ℂ) * I) / _root_.RHTower.xi (-((t : ℂ) * I))

private theorem xi_imaginary_ne_zero (t : ℝ) :
    _root_.RHTower.xi ((t : ℂ) * I) ≠ 0 := by
  intro hz
  have hp := (_root_.RHTower.xi_zero_re_mem_open_unit hz).1
  simp at hp

private theorem imaginary_sub_one_ne_zero (t : ℝ) : (t : ℂ) * I - 1 ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  norm_num at he

private theorem imaginary_conj (t : ℝ) : conj ((t : ℂ) * I) = -((t : ℂ) * I) := by
  simp

/-- The arithmetic factor is a phase at every real frequency. -/
theorem norm_mayerArithmeticMellinPhase (t : ℝ) : ‖mayerArithmeticMellinPhase t‖ = 1 := by
  have hξ : ‖_root_.RHTower.xi (-((t : ℂ) * I))‖ =
      ‖_root_.RHTower.xi ((t : ℂ) * I)‖ := by
    rw [← imaginary_conj, _root_.RHTower.xi_conj, Complex.norm_conj]
  have hp : ‖(t : ℂ) * I + 1‖ = ‖(t : ℂ) * I - 1‖ := by
    rw [← Complex.norm_conj ((t : ℂ) * I + 1)]
    simp only [map_add, map_one, imaginary_conj]
    rw [show -((t : ℂ) * I) + 1 = -((t : ℂ) * I - 1) by ring, norm_neg]
  rw [mayerArithmeticMellinPhase, norm_div, norm_mul, norm_div, hp,
    div_self (norm_ne_zero_iff.mpr (imaginary_sub_one_ne_zero t)), one_mul, hξ,
    div_self (norm_ne_zero_iff.mpr (xi_imaginary_ne_zero t))]

/-- The phase is continuous, including at zero frequency. -/
theorem continuous_mayerArithmeticMellinPhase : Continuous mayerArithmeticMellinPhase := by
  have hx : Continuous (fun t : ℝ => _root_.RHTower.xi ((t : ℂ) * I)) :=
    (show Differentiable ℂ _root_.RHTower.xi from _root_.RHTower.xi_differentiable).continuous.comp (by fun_prop)
  have hxn : Continuous (fun t : ℝ => _root_.RHTower.xi (-((t : ℂ) * I))) :=
    (show Differentiable ℂ _root_.RHTower.xi from _root_.RHTower.xi_differentiable).continuous.comp (by fun_prop)
  have hxn0 (t : ℝ) : _root_.RHTower.xi (-((t : ℂ) * I)) ≠ 0 := by
    simpa only [Complex.ofReal_neg, neg_mul] using xi_imaginary_ne_zero (-t)
  exact (((show Continuous (fun t : ℝ => (t : ℂ) * I + 1) by fun_prop).div
    (show Continuous (fun t : ℝ => (t : ℂ) * I - 1) by fun_prop)
      imaginary_sub_one_ne_zero).mul hx).div hxn hxn0

/-- The literal Mellin profile of the Gamma-normalized physical theta field. -/
def mayerFieldMellin (s : upperMayerResonances) (t : ℝ) : ℂ :=
  Gammaℝ (2 * s.1) * mellin (fieldCore (2 * s.1)) ((t : ℂ) * I)

private theorem gammaR_zeta_eq_xi_quotient {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    Gammaℝ z * riemannZeta z = 2 * _root_.RHTower.xi z / (z * (z - 1)) := by
  have hzne0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hz0
  have hΛ : Gammaℝ z * riemannZeta z = completedRiemannZeta z := by
    rw [riemannZeta_def_of_ne_zero hzne0]
    field_simp [hG]
  rw [hΛ, _root_.RHTower.xi_eq_half_mul hzne0 hz1]
  field_simp [mul_ne_zero hzne0 (sub_ne_zero.mpr hz1)]

private theorem fieldMellin_cleared_narrow (s : upperMayerResonances) {u : ℂ}
    (hu0 : 0 < u.re) (hu1 : u.re < 2 * s.1.re) :
    (Gammaℝ (2 * s.1) * u * (u - 1) * (2 * s.1 - u) * (2 * s.1 - u - 1)) *
      mellin (fieldCore (2 * s.1)) u =
      4 * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) := by
  have hu2 : u.re < 1 := by linarith only [hu1, s.2.2.2.1]
  have hwu0 : 0 < (2 * s.1 - u).re := by simp; linarith only [hu1]
  have hwu1 : (2 * s.1 - u).re < 1 := by simp; linarith only [hu0, s.2.2.2.1]
  have hu_ne0 : u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hu0; exact lt_irrefl 0 hu0
  have hu_ne1 : u ≠ 1 := by intro h; rw [h, Complex.one_re] at hu2; exact lt_irrefl 1 hu2
  have hwu_ne0 : 2 * s.1 - u ≠ 0 := by intro h; rw [h, Complex.zero_re] at hwu0; exact lt_irrefl 0 hwu0
  have hwu_ne1 : 2 * s.1 - u ≠ 1 := by intro h; rw [h, Complex.one_re] at hwu1; exact lt_irrefl 1 hwu1
  have hG : Gammaℝ (2 * s.1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [s.2.2.1])
  have hm := core_hasMellin_gammaR hu0 hu2 hwu0 hwu1
    (show 0 < (2 * s.1).im by simp; linarith only [s.2.1])
  rw [hm.2]
  have he : Gammaℝ u * Gammaℝ (2 * s.1 - u) / Gammaℝ (2 * s.1) *
      riemannZeta u * riemannZeta (2 * s.1 - u) =
      (Gammaℝ u * riemannZeta u) * (Gammaℝ (2 * s.1 - u) * riemannZeta (2 * s.1 - u)) /
        Gammaℝ (2 * s.1) := by ring
  rw [he, gammaR_zeta_eq_xi_quotient hu0 hu_ne1, gammaR_zeta_eq_xi_quotient hwu0 hwu_ne1]
  field_simp [hG, hu_ne0, sub_ne_zero.mpr hu_ne1, hwu_ne0, sub_ne_zero.mpr hwu_ne1]
  ring

private theorem fieldMellin_continuousAt_imaginary (s : upperMayerResonances) (t : ℝ) :
    ContinuousAt (mellin (fieldCore (2 * s.1))) ((t : ℂ) * I) := by
  have hz := (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  exact (core_zero_mellin_differentiableAt
    (by simp; linarith only [s.2.2.1]) (by simp; linarith only [s.2.2.2.1])
    (by simp; linarith only [s.2.1]) hz
    (by simp; linarith only [s.2.2.2.1]) (by simp)).continuousAt

/-- Continuation to the imaginary axis is justified by the enlarged physical Mellin strip. -/
private theorem fieldMellin_cleared_imaginary (s : upperMayerResonances) (t : ℝ) :
    let u : ℂ := (t : ℂ) * I
    (Gammaℝ (2 * s.1) * u * (u - 1) * (2 * s.1 - u) * (2 * s.1 - u - 1)) *
      mellin (fieldCore (2 * s.1)) u =
      4 * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) := by
  let u : ℂ := (t : ℂ) * I
  let F : ℂ → ℂ := fun z =>
    (Gammaℝ (2 * s.1) * z * (z - 1) * (2 * s.1 - z) * (2 * s.1 - z - 1)) *
      mellin (fieldCore (2 * s.1)) z
  let G : ℂ → ℂ := fun z => 4 * _root_.RHTower.xi z * _root_.RHTower.xi (2 * s.1 - z)
  have hF : ContinuousAt F u :=
    (show ContinuousAt (fun z : ℂ =>
      Gammaℝ (2 * s.1) * z * (z - 1) * (2 * s.1 - z) * (2 * s.1 - z - 1)) u by
        fun_prop).mul (fieldMellin_continuousAt_imaginary s t)
  have hG : ContinuousAt G u := by
    exact ((continuousAt_const.mul (_root_.RHTower.xi_differentiable u).continuousAt).mul
      ((_root_.RHTower.xi_differentiable (2 * s.1 - u)).continuousAt.comp
        (show ContinuousAt (fun z : ℂ => 2 * s.1 - z) u by fun_prop)))
  have hc : Tendsto (fun a : ℝ => (a : ℂ) + u) (𝓝[>] (0 : ℝ)) (𝓝 u) := by
    have hc₀ : Continuous (fun a : ℝ => (a : ℂ) + u) := by fun_prop
    simpa only [Complex.ofReal_zero, zero_add] using
      (hc₀.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have he : (fun a : ℝ => F ((a : ℂ) + u)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun a : ℝ => G ((a : ℂ) + u)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds s.2.2.1).filter_mono nhdsWithin_le_nhds] with a ha ha1
    change 0 < a at ha
    apply fieldMellin_cleared_narrow s
    · simpa [u] using ha
    · simp only [u, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
      linarith only [ha1, s.2.2.1]
  exact tendsto_nhds_unique ((hF.tendsto.comp hc).congr' he) (hG.tendsto.comp hc)



private theorem fieldMellin_poleProduct_ne_zero (s : upperMayerResonances) {t : ℝ}
    (ht : t ≠ 0) :
    ((t : ℂ) * I) * ((t : ℂ) * I - 1) * (2 * s.1 - (t : ℂ) * I) *
      (2 * s.1 - (t : ℂ) * I - 1) ≠ 0 := by
  have h0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have hw : 2 * s.1 - (t : ℂ) * I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith only [he, s.2.2.1]
  have hw1 : 2 * s.1 - (t : ℂ) * I - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith only [he, s.2.2.2.1]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 (imaginary_sub_one_ne_zero t)) hw) hw1

private theorem mayerFieldMellin_eq_xi_quotient (s : upperMayerResonances) {t : ℝ}
    (ht : t ≠ 0) :
    mayerFieldMellin s t =
      4 * _root_.RHTower.xi ((t : ℂ) * I) * _root_.RHTower.xi (2 * s.1 - (t : ℂ) * I) /
        (((t : ℂ) * I) * ((t : ℂ) * I - 1) * (2 * s.1 - (t : ℂ) * I) *
          (2 * s.1 - (t : ℂ) * I - 1)) := by
  apply (eq_div_iff (fieldMellin_poleProduct_ne_zero s ht)).mpr
  have he := fieldMellin_cleared_imaginary s t
  dsimp only at he
  unfold mayerFieldMellin
  convert he using 1
  ring

/-- Every normalized physical field has a continuous imaginary-axis Mellin profile. -/
theorem continuous_mayerFieldMellin (s : upperMayerResonances) : Continuous (mayerFieldMellin s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hm : ContinuousAt (fun y : ℝ => mellin (fieldCore (2 * s.1)) ((y : ℂ) * I)) t :=
    (fieldMellin_continuousAt_imaginary s t).comp (f := fun y : ℝ => (y : ℂ) * I)
      (show ContinuousAt (fun y : ℝ => (y : ℂ) * I) t by fun_prop)
  exact continuousAt_const.mul hm

private theorem mayerFieldMellin_reflect_ne_zero (s : upperMayerResonances) {t : ℝ}
    (ht : t ≠ 0) :
    mayerFieldMellin (reflectUpperResonance s) t =
      mayerArithmeticMellinPhase t * conj (mayerFieldMellin s t) := by
  have hwref : 2 * (reflectUpperResonance s).1 = 1 - conj (2 * s.1) := by
    simp only [reflectUpperResonance_coe, riemannMayerReflect, map_mul, map_ofNat]
    ring
  have hxi : _root_.RHTower.xi (1 - conj (2 * s.1) - (t : ℂ) * I) =
      _root_.RHTower.xi (conj (2 * s.1) + (t : ℂ) * I) := by
    rw [show 1 - conj (2 * s.1) - (t : ℂ) * I =
      1 - (conj (2 * s.1) + (t : ℂ) * I) by ring, _root_.RHTower.xi_one_sub]
  have h0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have h1 := imaginary_sub_one_ne_zero t
  have hm1 : (t : ℂ) * I + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
  have hw : conj (2 * s.1) + (t : ℂ) * I ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith only [he, s.2.2.1]
  have hw1 : conj (2 * s.1) + (t : ℂ) * I - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith only [he, s.2.2.2.1]
  have hxn : _root_.RHTower.xi (-((t : ℂ) * I)) ≠ 0 := by
    simpa only [Complex.ofReal_neg, neg_mul] using xi_imaginary_ne_zero (-t)
  rw [mayerFieldMellin_eq_xi_quotient (reflectUpperResonance s) ht,
    mayerFieldMellin_eq_xi_quotient s ht, hwref, hxi]
  simp only [mayerArithmeticMellinPhase, map_div₀, map_mul, map_sub, map_ofNat,
    map_one, ← _root_.RHTower.xi_conj, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, sub_neg_eq_add]
  simp only [map_mul, map_ofNat] at hw hw1
  rw [show 1 - 2 * conj s.1 - (t : ℂ) * I =
      -(2 * conj s.1 + (t : ℂ) * I - 1) by ring,
    show -(2 * conj s.1 + (t : ℂ) * I - 1) - 1 =
      -(2 * conj s.1 + (t : ℂ) * I) by ring,
    show -((t : ℂ) * I) - 1 = -((t : ℂ) * I + 1) by ring]
  field_simp [h0, h1, hm1, hw, hw1, hxn]

/-- Spectral reflection of the actual normalized theta fields is conjugation times one
unimodular arithmetic phase. The zero-frequency identity follows by continuity. -/
theorem mayerFieldMellin_reflect (s : upperMayerResonances) (t : ℝ) :
    mayerFieldMellin (reflectUpperResonance s) t =
      mayerArithmeticMellinPhase t * conj (mayerFieldMellin s t) := by
  by_cases ht : t = 0
  · subst t
    have hleft := (continuous_mayerFieldMellin (reflectUpperResonance s)).continuousAt (x := (0 : ℝ))
    have hright := (continuous_mayerArithmeticMellinPhase.mul
      (Complex.continuous_conj.comp (continuous_mayerFieldMellin s))).continuousAt (x := (0 : ℝ))
    have he : (fun t : ℝ => mayerFieldMellin (reflectUpperResonance s) t)
        =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun t => mayerArithmeticMellinPhase t * conj (mayerFieldMellin s t)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact mayerFieldMellin_reflect_ne_zero s (by simpa only [mem_compl_iff, mem_singleton_iff] using ht)
    exact tendsto_nhds_unique
      ((hleft.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
      (hright.tendsto.mono_left nhdsWithin_le_nhds)
  · exact mayerFieldMellin_reflect_ne_zero s ht



/-- The Gamma-normalized physical field in logarithmic Haar coordinates. -/
def mayerFieldLog (s : upperMayerResonances) (v : ℝ) : ℂ :=
  Gammaℝ (2 * s.1) * fieldCore (2 * s.1) (Real.exp (-v))

private theorem normalized_field_outgoing_bound (s : upperMayerResonances) {a : ℝ}
    (ha : 0 < a) :
    ‖Gammaℝ (2 * s.1) * fieldCore (2 * s.1) a‖ ≤
      (2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re)) / a := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have hw1 : (2 * s.1).re < 1 := by simp; linarith only [s.2.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hz := (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  have hb := fieldCore_resonant_endpoint_bound hw hw1 him hz ha
  have hG : ‖Gammaℝ (2 * s.1)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hw)
  rw [norm_mul]
  calc
    _ ≤ ‖Gammaℝ (2 * s.1)‖ *
        ((2 / (Real.pi * (2 * s.1).re) + 1 / (1 - (2 * s.1).re)) /
          (‖Gammaℝ (2 * s.1)‖ * a)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; field_simp

/-- Zero-specific decay at both ends makes each normalized field globally bounded. -/
private theorem mayerFieldLog_bound (s : upperMayerResonances) (v : ℝ) :
    ‖mayerFieldLog s v‖ ≤ 2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re) := by
  let C : ℝ := 2 / (Real.pi * (2 * s.1.re)) + 1 / (1 - 2 * s.1.re)
  have hC : 0 ≤ C := by
    have hr := s.2.2.1
    have hr1 : 0 < 1 - 2 * s.1.re := by linarith only [s.2.2.2.1]
    dsimp [C]
    positivity
  let a : ℝ := Real.exp (-v)
  have ha : 0 < a := Real.exp_pos _
  change ‖Gammaℝ (2 * s.1) * fieldCore (2 * s.1) a‖ ≤ C
  by_cases ha1 : 1 ≤ a
  · exact (normalized_field_outgoing_bound s ha).trans (div_le_self hC ha1)
  · have hsmall : a ≤ 1 := (not_le.mp ha1).le
    have hrec := fieldCore_reciprocity
      (show 0 < (2 * s.1).re by simp; linarith only [s.2.2.1])
      (show 0 < (2 * s.1).im by simp; linarith only [s.2.1]) ha
    rw [hrec, show Gammaℝ (2 * s.1) *
        ((a : ℂ) ^ (-(2 * s.1)) * fieldCore (2 * s.1) (1 / a)) =
        (a : ℂ) ^ (-(2 * s.1)) * (Gammaℝ (2 * s.1) * fieldCore (2 * s.1) (1 / a)) by ring,
      norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
    have hexp : (-(2 * s.1)).re = -(2 * s.1.re) := by simp
    rw [hexp]
    calc
      _ ≤ a ^ (-(2 * s.1.re)) * (C / (1 / a)) :=
        mul_le_mul_of_nonneg_left (normalized_field_outgoing_bound s (one_div_pos.mpr ha))
          (Real.rpow_nonneg ha.le _)
      _ = C * a ^ (1 - 2 * s.1.re) := by
        rw [div_div_eq_mul_div, div_one]
        calc
          _ = C * (a ^ (-(2 * s.1.re)) * a ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
          _ = _ := by rw [← Real.rpow_add ha]; congr 2; ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one ha.le hsmall (by linarith only [s.2.2.2.1])) hC
      _ = C := mul_one C

/-- The normalized field is integrable in logarithmic Haar coordinates. -/
theorem mayerFieldLog_integrable (s : upperMayerResonances) : Integrable (mayerFieldLog s) := by
  have hm := (core_zero_hasMellin_zero
    (show 0 < (2 * s.1).re by simp; linarith only [s.2.2.1])
    (show (2 * s.1).re < 1 by simp; linarith only [s.2.2.2.1])
    (show 0 < (2 * s.1).im by simp; linarith only [s.2.1])
    ((isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2)).1
  have hi := _root_.RHTower.integrable_logMellinPullback_of_mellinConvergent
    (fieldCore (2 * s.1)) 0 hm
  simp only [neg_zero, zero_mul, Real.exp_zero, one_smul] at hi
  exact hi.const_mul _

/-- This is a concrete physical `L²` field, with no spectral admission premise. -/
theorem mayerFieldLog_memLp (s : upperMayerResonances) : MemLp (mayerFieldLog s) 2 :=
  _root_.RHTower.memLp_two_of_integrable_of_norm_le (mayerFieldLog_integrable s)
    (mayerFieldLog_bound s)

/-- The actual normalized field as an element of logarithmic Haar `L²`. -/
def mayerFieldLogColumn (s : upperMayerResonances) : Lp ℂ 2 (volume : Measure ℝ) :=
  (mayerFieldLog_memLp s).toLp (mayerFieldLog s)


open scoped FourierTransform

/-- The logarithmic Fourier transform is the literal imaginary-axis Mellin profile. -/
theorem fourier_mayerFieldLog (s : upperMayerResonances) (ξ : ℝ) :
    𝓕 (mayerFieldLog s) ξ = mayerFieldMellin s (2 * Real.pi * ξ) := by
  rw [mayerFieldMellin, mellin_eq_fourier]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, neg_zero, Real.exp_zero, one_smul,
    Complex.mul_im, mul_one, add_zero]
  rw [show 2 * Real.pi * ξ / (2 * Real.pi) = ξ by field_simp]
  change 𝓕 (fun v : ℝ => Gammaℝ (2 * s.1) * fieldCore (2 * s.1) (Real.exp (-v))) ξ = _
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with v
  simp only [Circle.smul_def, smul_eq_mul]
  ring

private def mayerFrequencyPhaseUnitary :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  HTGeometry.unimodularMulUnitary
    (continuous_mayerArithmeticMellinPhase.comp (show Continuous (fun t : ℝ => 2 * Real.pi * t) by
      fun_prop)).measurable
    (fun t => norm_mayerArithmeticMellinPhase (2 * Real.pi * t))

private def mayerFrequencyReflection (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) := mayerFrequencyPhaseUnitary (star f)

private theorem mayerFrequencyReflection_coeFn (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (mayerFrequencyReflection f : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerArithmeticMellinPhase (2 * Real.pi * ξ) * conj (f ξ) := by
  have h := HTGeometry.unimodularMulUnitary_coeFn
    (continuous_mayerArithmeticMellinPhase.comp (show Continuous (fun t : ℝ => 2 * Real.pi * t) by
      fun_prop)).measurable
    (fun t => norm_mayerArithmeticMellinPhase (2 * Real.pi * t)) (star f)
  filter_upwards [h, Lp.coeFn_star f] with ξ hξ hs
  change mayerFrequencyReflection f ξ = _ at hξ
  rw [hξ, hs]
  rfl

private theorem mayerFrequencyReflection_norm (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mayerFrequencyReflection f‖ = ‖f‖ := by
  exact (mayerFrequencyPhaseUnitary.norm_map (star f)).trans (_root_.RHTower.norm_lpStar f)

private theorem mayerFrequencyReflection_involutive (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFrequencyReflection (mayerFrequencyReflection f) = f := by
  apply Lp.ext
  filter_upwards [mayerFrequencyReflection_coeFn (mayerFrequencyReflection f),
    mayerFrequencyReflection_coeFn f] with ξ h1 h2
  rw [h1, h2, map_mul, starRingEnd_self_apply, ← mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mayerArithmeticMellinPhase]
  simp

private theorem mayerFrequencyReflection_add (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFrequencyReflection (f + g) = mayerFrequencyReflection f + mayerFrequencyReflection g := by
  apply Lp.ext
  filter_upwards [mayerFrequencyReflection_coeFn (f + g),
    mayerFrequencyReflection_coeFn f, mayerFrequencyReflection_coeFn g,
    Lp.coeFn_add f g, Lp.coeFn_add (mayerFrequencyReflection f) (mayerFrequencyReflection g)]
      with ξ h h1 h2 ha hb
  simp only [h, ha, hb, h1, h2, Pi.add_apply, map_add, mul_add]

private theorem mayerFrequencyReflection_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFrequencyReflection (c • f) = conj c • mayerFrequencyReflection f := by
  apply Lp.ext
  filter_upwards [mayerFrequencyReflection_coeFn (c • f), mayerFrequencyReflection_coeFn f,
    Lp.coeFn_smul c f, Lp.coeFn_smul (conj c) (mayerFrequencyReflection f)] with ξ h h1 ha hb
  simp only [h, ha, hb, h1, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- The source-defined arithmetic reflection on logarithmic Haar `L²`: Fourier conjugation
multiplied by the completed-zeta phase, then inverse Fourier transform. -/
def mayerFieldReflection (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (mayerFrequencyReflection ((Lp.fourierTransformₗᵢ ℝ ℂ) f))

/-- Arithmetic reflection preserves the physical Haar norm on its entire `L²` domain. -/
theorem norm_mayerFieldReflection (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mayerFieldReflection f‖ = ‖f‖ := by
  rw [mayerFieldReflection, (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map,
    mayerFrequencyReflection_norm, (Lp.fourierTransformₗᵢ ℝ ℂ).norm_map]

/-- Applying the physical reflection twice gives the original field. -/
theorem mayerFieldReflection_involutive (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFieldReflection (mayerFieldReflection f) = f := by
  unfold mayerFieldReflection
  rw [LinearIsometryEquiv.apply_symm_apply, mayerFrequencyReflection_involutive,
    LinearIsometryEquiv.symm_apply_apply]

/-- Physical reflection is additive. -/
theorem mayerFieldReflection_add (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFieldReflection (f + g) = mayerFieldReflection f + mayerFieldReflection g := by
  simp only [mayerFieldReflection, map_add, mayerFrequencyReflection_add]

/-- Physical reflection is conjugate-linear. -/
theorem mayerFieldReflection_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFieldReflection (c • f) = conj c • mayerFieldReflection f := by
  simp only [mayerFieldReflection, map_smul, mayerFrequencyReflection_smul]

private theorem fourier_mayerFieldLogColumn_coeFn (s : upperMayerResonances) :
    (((Lp.fourierTransformₗᵢ ℝ ℂ) (mayerFieldLogColumn s)) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerFieldMellin s (2 * Real.pi * ξ) := by
  have hcoe : (mayerFieldLogColumn s : ℝ → ℂ) =ᵐ[volume] mayerFieldLog s :=
    (mayerFieldLog_memLp s).coeFn_toLp
  have hint : Integrable (mayerFieldLogColumn s : ℝ → ℂ) :=
    (mayerFieldLog_integrable s).congr hcoe.symm
  refine (HTGeometry.coeFn_fourierTransform_eq_fourierIntegral (mayerFieldLogColumn s) hint).trans ?_
  filter_upwards with ξ
  exact (Real.fourier_congr_ae hcoe ξ).trans (fourier_mayerFieldLog s ξ)

/-- The arithmetic antiunitary exchanges the actual resonant theta fields with their spectral
reflections. Both sides are concrete, unconditionally admitted physical `L²` functions. -/
theorem mayerFieldReflection_column (s : upperMayerResonances) :
    mayerFieldReflection (mayerFieldLogColumn s) = mayerFieldLogColumn (reflectUpperResonance s) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  rw [mayerFieldReflection, LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [mayerFrequencyReflection_coeFn ((Lp.fourierTransformₗᵢ ℝ ℂ) (mayerFieldLogColumn s)),
    fourier_mayerFieldLogColumn_coeFn s,
    fourier_mayerFieldLogColumn_coeFn (reflectUpperResonance s)] with ξ h h1 h2
  rw [h, h1, h2, mayerFieldMellin_reflect]


open MayerCauchyMellinSymbol MayerQuadraticCone MayerEpsteinHeightMeasurability

/-- The multiplier from the normalized theta field to the actual Cauchy-averaged PM core. -/
def mayerCoreMellinFactor (s : ℂ) (t : ℝ) : ℂ :=
  symbol (2 * s) ((t : ℂ) * I) / Gammaℝ (2 * s)

/-- The extra reflection factor introduced by Cauchy averaging. -/
def mayerCoreReflectionFactor (s : ℂ) (t : ℝ) : ℂ :=
  mayerCoreMellinFactor (riemannMayerReflect s) t / conj (mayerCoreMellinFactor s t)

private theorem mayerCoreMellinFactor_ne_zero (s : upperMayerResonances) (t : ℝ) :
    mayerCoreMellinFactor s t ≠ 0 := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  exact div_ne_zero
    (symbol_ne_zero hw (by simp) (by simp; linarith only [s.2.2.1]))
    (Complex.Gammaℝ_ne_zero_of_re_pos hw)

/-- Cauchy convolution gives the literal imaginary-axis Mellin transform, including convergence. -/
theorem mayerPeriodCore_hasMellin_imaginary (s : upperMayerResonances) (t : ℝ) :
    HasMellin (mayerPeriodCore s.1) ((t : ℂ) * I)
      (mayerCoreMellinFactor s t * mayerFieldMellin s t) := by
  have hw : 0 < (2 * s.1).re := by simp; linarith only [s.2.2.1]
  have hw1 : (2 * s.1).re < 1 := by simp; linarith only [s.2.2.2.1]
  have him : 0 < (2 * s.1).im := by simp; linarith only [s.2.1]
  have hz := (isMayerScatteringResonance_iff_zeta_zero s.2.2.1 s.2.2.2.1).mp s.2.2
  have hker := cauchyKernel_hasMellin hw
    (show -1 < ((t : ℂ) * I).re by simp)
    (show ((t : ℂ) * I).re < (2 * s.1).re + 1 by simp; linarith only [s.2.2.1])
  have hfield := MayerZeroMellinStrip.core_zero_mellinConvergent hw hw1 him hz
    (show (2 * s.1).re - 1 < ((t : ℂ) * I).re by simp; linarith only [s.2.2.2.1])
    (show ((t : ℂ) * I).re < 1 by simp)
  have hkm : Measurable (cauchyKernel (2 * s.1)) := by
    unfold cauchyKernel cauchyWeight
    fun_prop
  have hfm : Measurable (fieldCore (2 * s.1)) := by
    have hwne0 : 2 * s.1 ≠ 0 := by intro h; rw [h, Complex.zero_im] at him; exact lt_irrefl 0 him
    have hwne2 : 2 * s.1 ≠ 2 := by intro h; rw [h] at him; norm_num at him
    have he := measurable_epsteinField hwne0 hwne2
    unfold fieldCore scatteringPowers
    fun_prop
  have h := _root_.RHTower.hasMellin_positiveMellinConvolution hkm hfm hker.1 hfield
  rw [hker.2] at h
  have he : symbol (2 * s.1) ((t : ℂ) * I) * mellin (fieldCore (2 * s.1)) ((t : ℂ) * I) =
      mayerCoreMellinFactor s t * mayerFieldMellin s t := by
    unfold mayerCoreMellinFactor mayerFieldMellin
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hw]
  rw [he] at h
  exact h

/-- Spectral reflection of the actual averaged cores retains its extra Cauchy multiplier. -/
theorem mayerPeriodCore_mellin_reflect (s : upperMayerResonances) (t : ℝ) :
    mellin (mayerPeriodCore (reflectUpperResonance s).1) ((t : ℂ) * I) =
      mayerCoreReflectionFactor s t * mayerArithmeticMellinPhase t *
        conj (mellin (mayerPeriodCore s.1) ((t : ℂ) * I)) := by
  rw [(mayerPeriodCore_hasMellin_imaginary (reflectUpperResonance s) t).2,
    (mayerPeriodCore_hasMellin_imaginary s t).2, mayerFieldMellin_reflect]
  unfold mayerCoreReflectionFactor
  rw [map_mul, reflectUpperResonance_coe]
  have hn : conj (mayerCoreMellinFactor s t) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (mayerCoreMellinFactor_ne_zero s t)
  field_simp [hn]



#print axioms norm_mayerArithmeticMellinPhase
#print axioms mayerFieldMellin_reflect
#print axioms mayerFieldLog_integrable
#print axioms mayerFieldLog_memLp
#print axioms norm_mayerFieldReflection
#print axioms mayerFieldReflection_involutive
#print axioms mayerFieldReflection_add
#print axioms mayerFieldReflection_smul
#print axioms mayerFieldReflection_column
#print axioms mayerPeriodCore_hasMellin_imaginary
#print axioms mayerPeriodCore_mellin_reflect

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
