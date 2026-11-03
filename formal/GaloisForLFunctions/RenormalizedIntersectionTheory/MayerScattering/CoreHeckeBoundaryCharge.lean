import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.WholeHaarHeckeWindowAdmission
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeScatteringBoundaryCorrection
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.ResonantCoreEndpointBounds
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCoresHaveFiniteHeckeCuspEnergy
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The retained Hecke boundary charge of a resonant Mayer core

The actual source Hecke image has a nonzero lower-cusp trace at every upper resonance.
Evaluation recovers its exact value. Removing this unique boundary coefficient restores
whole-axis Haar square integrability, including at critical-line resonances.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerScatteringState MayerScatteringMellin MayerScatteringPeriod MayerScatteringCore
open MayerQuadraticCone

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Evaluation at the inversion-fixed point recovers the scattering coefficient. -/
theorem mayerPeriodCore_one_eq {s : ℂ} (hs : s ∈ upperMayerResonances) :
    mayerPeriodCore s 1 = (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * (2 * s - 3) := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs.2.1]
  have hw2 : 2 * s ≠ 2 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith only [hi, hs.1]
  have hden : 2 * s - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith only [hi, hs.1]
  have hp : periodValue (2 * s) 1 = 2 * riemannZeta (2 * s - 1) := by
    calc
      _ = plane (state (2 * s)) 0 := by
        simp only [periodValue, Complex.ofReal_one, sub_self]
      _ = (state (2 * s)).1 zeroPoint := plane_eq (state (2 * s)) zeroPoint
      _ = _ := state_zero hw hw2
  rw [mayerPeriodCore_eq_periodValue_sub_boundary hs (by norm_num [periodSegment]), hp]
  simp only [scatteringPowers, Complex.ofReal_one, Complex.one_cpow]
  field_simp [hden]; ring

/-- The first-prime value retains both the scattering normalization and its Hecke correction. -/
theorem mayerPeriodCore_two_eq {s : ℂ} (hs : s ∈ upperMayerResonances) :
    mayerPeriodCore s 2 = riemannZeta (2 * s - 1) / (2 * s - 1) *
      (2 * s - 2 - 4 * (2 : ℂ) ^ (-(2 * s))) := by
  have hden : 2 * s - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith only [hi, hs.1]
  have hz : riemannZeta (2 * s) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero hs.2.1 hs.2.2.1).mp hs.2
  have hc : mayerPeriodCore s 1 = 2 * riemannZeta (2 * s - 1) -
      2 * (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) := by
    rw [mayerPeriodCore_one_eq hs]
    field_simp [hden]; ring
  have hinv := lewisModularInversion_mayerPeriodCore hs.2.1 hs.1
    (a := 2) (by norm_num)
  change (2 : ℂ) ^ (-(2 * s)) * mayerPeriodCore s (2 : ℝ)⁻¹ =
    mayerPeriodCore s 2 at hinv
  have hh := hecke_mayerPeriodCore_at_one hs.2.1 hs.1
  rw [hz, mul_zero, zero_add, lewisHeckeT2] at hh
  norm_num only [mul_one, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Complex.ofReal_ofNat, one_div] at hh
  simp only [one_div] at hh
  rw [hinv] at hh
  have hlin : 2 * mayerPeriodCore s 2 =
      2 * riemannZeta (2 * s - 1) -
        (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) *
          (1 + 4 * (2 : ℂ) ^ (-(2 * s))) := by
    linear_combination hh + hc
  calc
    _ = riemannZeta (2 * s - 1) -
        (riemannZeta (2 * s - 1) / (2 * s - 1)) *
          (1 + 4 * (2 : ℂ) ^ (-(2 * s))) := by linear_combination hlin / 2
    _ = _ := by field_simp [hden]; ring

private theorem first_prime_core_factor_ne_zero {w : ℂ} (hw : 0 < w.re)
    (hi : 0 < w.im) : w - 2 - 4 * (2 : ℂ) ^ (-w) ≠ 0 := by
  intro hz
  have he : w - 2 = 4 * (2 : ℂ) ^ (-w) := sub_eq_zero.mp hz
  have hq : ‖(2 : ℂ) ^ (-w)‖ = (2 : ℝ) ^ (-w.re) := by
    change ‖((2 : ℝ) : ℂ) ^ (-w)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    rfl
  have hq1 : (2 : ℝ) ^ (-w.re) < 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
        (neg_neg_of_pos hw)
  have hg : w.im < 4 := by
    have hb := Complex.im_le_norm (w - 2)
    simp only [Complex.sub_im, Complex.im_ofNat, sub_zero] at hb
    rw [he, norm_mul, hq] at hb
    norm_num only [Complex.sub_im, Complex.im_ofNat, sub_zero, Complex.norm_ofNat] at hb
    linarith only [hb, hq1]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hphase : w.im * Real.log 2 < Real.pi := by
    have hmul := mul_lt_mul_of_pos_right hg hlog
    linarith only [hmul, Real.log_two_lt_d9, Real.pi_gt_three]
  have hsin := Real.sin_pos_of_pos_of_lt_pi (mul_pos hi hlog) hphase
  have him : ((2 : ℂ) ^ (-w)).im < 0 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      GaloisForLFunctions.HTGeometry.ofReal_cpow_im (by norm_num)]
    simp only [Complex.neg_im, neg_mul, Real.sin_neg, Complex.neg_re]
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (by norm_num) _) (neg_neg_of_pos hsin)
  have hei := congrArg Complex.im he
  norm_num only [Complex.sub_im, Complex.im_ofNat, sub_zero,
    Complex.mul_im, Complex.re_ofNat, zero_mul, add_zero] at hei
  linarith only [hi, him, hei]

/-- Every upper-resonant core has a nonzero first-prime value. -/
theorem mayerPeriodCore_two_ne_zero {s : ℂ} (hs : s ∈ upperMayerResonances) :
    mayerPeriodCore s 2 ≠ 0 := by
  rw [mayerPeriodCore_two_eq hs]
  have hw : 0 < (2 * s).re := by simp; linarith only [hs.2.1]
  have hw1 : (2 * s).re < 1 := by simp; linarith only [hs.2.2.1]
  have hden : 2 * s - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hr, hs.2.2.1]
  exact mul_ne_zero (div_ne_zero
    (MayerScatteringMultiplicity.shifted_zeta_ne_zero hw hw1) hden)
    (first_prime_core_factor_ne_zero hw (by simp; linarith only [hs.1]))

private theorem core_differentiable_two {s : ℂ} (hs : s ∈ upperMayerResonances) :
    DifferentiableAt ℝ (mayerPeriodCore s) 2 := by
  have hP : DifferentiableAt ℂ (plane (state (2 * s))) 1 :=
    (differentiableOn_plane _).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by norm_num [MayerCutoff.inner]))
  have hp : DifferentiableAt ℝ (periodValue (2 * s)) 2 := by
    unfold periodValue
    have hP' : DifferentiableAt ℂ (plane (state (2 * s))) ((2 : ℂ) - 1) := by
      simpa only [show (2 : ℂ) - 1 = 1 by norm_num] using hP
    exact (hP'.restrictScalars ℝ).comp 2 (by fun_prop)
  let F : ℝ → ℂ := fun a => periodValue (2 * s) a -
    (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * scatteringPowers (2 * s) a
  have hF : DifferentiableAt ℝ F 2 := by
    dsimp only [F]
    unfold scatteringPowers
    fun_prop (disch := norm_num)
  apply hF.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (2 : ℝ) ∈ Ioo 1 3 by norm_num)] with a ha
  exact mayerPeriodCore_eq_periodValue_sub_boundary hs
    (show a ∈ periodSegment by constructor <;> linarith only [ha.1, ha.2])

private theorem core_differentiable_half {s : ℂ} (hs : s ∈ upperMayerResonances) :
    DifferentiableAt ℝ (mayerPeriodCore s) (1 / 2) := by
  have hi : DifferentiableAt ℝ (fun a : ℝ => a⁻¹) (1 / 2) := by fun_prop (disch := norm_num)
  have hc : DifferentiableAt ℝ (mayerPeriodCore s) ((1 / 2 : ℝ)⁻¹) := by
    norm_num only [one_div, inv_inv]
    exact core_differentiable_two hs
  have hF : DifferentiableAt ℝ (fun a : ℝ =>
      (a : ℂ) ^ (-(2 * s)) * mayerPeriodCore s a⁻¹) (1 / 2) := by
    have hcomp := hc.comp (1 / 2) hi
    have hp : DifferentiableAt ℝ (fun a : ℝ => (a : ℂ) ^ (-(2 * s))) (1 / 2) := by
      have hr : -(2 * s) ≠ 0 := by
        intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith only [hh, hs.2.1]
      exact (hasDerivAt_ofReal_cpow_const (by norm_num : (1 / 2 : ℝ) ≠ 0) hr).differentiableAt
    exact hp.mul hcomp
  apply hF.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with a ha
  exact (lewisModularInversion_mayerPeriodCore hs.2.1 hs.1 ha).symm

private theorem shifted_core_linear_bound {s : ℂ} (hs : s ∈ upperMayerResonances) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ a ∈ Ioo 0 δ,
      ‖(2 : ℂ) ^ (-(2 * s)) * mayerPeriodCore s ((a + 1) / 2) -
        mayerPeriodCore s 2‖ ≤ C * a := by
  let g : ℝ → ℂ := fun a => (2 : ℂ) ^ (-(2 * s)) * mayerPeriodCore s ((a + 1) / 2)
  have hψ : DifferentiableAt ℝ (mayerPeriodCore s) ((fun a : ℝ => (a + 1) / 2) 0) := by
    simpa using core_differentiable_half hs
  have hg : DifferentiableAt ℝ g 0 :=
    (hψ.comp 0 (by fun_prop)).const_mul _
  have hg0 : g 0 = mayerPeriodCore s 2 := by
    have h := lewisModularInversion_mayerPeriodCore hs.2.1 hs.1 (a := 2) (by norm_num)
    change (2 : ℂ) ^ (-(2 * s)) * mayerPeriodCore s (2 : ℝ)⁻¹ = mayerPeriodCore s 2 at h
    simpa only [g, zero_add, one_div] using h
  obtain ⟨C, hC, hb⟩ := hg.isBigO_sub.exists_pos
  have he : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖g a - mayerPeriodCore s 2‖ ≤ C * a := by
    filter_upwards [hb.bound.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hp
    have ha0 : 0 < a := hp
    simpa only [hg0, sub_zero, Real.norm_eq_abs, abs_of_pos ha0] using ha
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨C, δ, hC, hδ, fun a ha => hbound ha⟩

/-- Removing the exact Hecke trace exposes the resonant power decay at the lower cusp. -/
theorem hecke_mayerPeriodCore_sub_trace_bound (s : upperMayerResonances) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ a ∈ Ioo 0 δ,
      ‖lewisHeckeT2 s.1 (mayerPeriodCore s.1) a - mayerPeriodCore s.1 2‖ ≤
        C * a ^ (1 - 2 * s.1.re) := by
  obtain ⟨K, N, hK, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  let B := K * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)
  let β := 1 - 2 * s.1.re
  have hy : 0 < s.1.im := s.2.1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hβ : 0 < β := by dsimp only [β]; linarith only [s.2.2.2.1]
  have hβ1 : β ≤ 1 := by dsimp only [β]; linarith only [s.2.2.1]
  have hsmall (x : ℝ) (hx : 0 < x) : ‖mayerPeriodCore s.1 x‖ ≤ B * x ^ β :=
    (hb s x hx).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hB)
  obtain ⟨L, δ, hL, hδ, hshift⟩ := shifted_core_linear_bound s.2
  refine ⟨2 * B * (2 : ℝ) ^ β + B + L, min δ 1, by positivity,
    lt_min hδ zero_lt_one, fun a ha => ?_⟩
  have ha0 : 0 < a := ha.1
  have ha1 : a < 1 := ha.2.trans_le (min_le_right _ _)
  have hp : 0 ≤ a ^ β := (Real.rpow_pos_of_pos ha0 _).le
  have ht : (2 * a) ^ β = (2 : ℝ) ^ β * a ^ β := Real.mul_rpow (by norm_num) ha0.le
  have hq : ‖(2 : ℂ) ^ (-(2 * s.1))‖ ≤ 1 := by
    change ‖((2 : ℝ) : ℂ) ^ (-(2 * s.1))‖ ≤ 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by simp; linarith only [s.2.2.1])
  have hw : ‖((a + 1 : ℝ) : ℂ) ^ (-(2 * s.1))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [ha0])
      (by simp; linarith only [s.2.2.1])
  have hfirst : ‖mayerPeriodCore s.1 (2 * a)‖ ≤ (B * 2 ^ β) * a ^ β := by
    simpa only [ht, mul_assoc] using hsmall (2 * a) (by positivity)
  have hhalf : ‖(2 : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 (a / 2)‖ ≤ B * a ^ β := by
    rw [norm_mul]
    calc
      _ ≤ 1 * (B * (a / 2) ^ β) := mul_le_mul hq (hsmall _ (by positivity))
        (norm_nonneg _) zero_le_one
      _ ≤ B * a ^ β := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by linarith only [ha0]) hβ.le) hB
  have hr : ‖((a + 1 : ℝ) : ℂ) ^ (-(2 * s.1)) *
      mayerPeriodCore s.1 (2 * a / (a + 1))‖ ≤ (B * 2 ^ β) * a ^ β := by
    rw [norm_mul]
    calc
      _ ≤ 1 * (B * (2 * a / (a + 1)) ^ β) :=
        mul_le_mul hw (hsmall _ (by positivity)) (norm_nonneg _) zero_le_one
      _ ≤ B * (2 * a) ^ β := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity)
            (div_le_self (by positivity) (by linarith only [ha0])) hβ.le) hB
      _ = _ := by rw [ht]; ring
  have hlin : a ≤ a ^ β := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge ha0 ha1.le hβ1
  have hsh : ‖(2 : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 ((a + 1) / 2) -
      mayerPeriodCore s.1 2‖ ≤ L * a ^ β :=
    (hshift a ⟨ha0, ha.2.trans_le (min_le_left _ _)⟩).trans
      (mul_le_mul_of_nonneg_left hlin hL.le)
  have he : lewisHeckeT2 s.1 (mayerPeriodCore s.1) a - mayerPeriodCore s.1 2 =
      (mayerPeriodCore s.1 (2 * a) +
        (2 : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 (a / 2)) +
      (((a + 1 : ℝ) : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 (2 * a / (a + 1)) +
        ((2 : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 ((a + 1) / 2) -
          mayerPeriodCore s.1 2)) := by unfold lewisHeckeT2; ring
  rw [he]
  calc
    _ ≤ (‖mayerPeriodCore s.1 (2 * a)‖ +
        ‖(2 : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 (a / 2)‖) +
      (‖((a + 1 : ℝ) : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 (2 * a / (a + 1))‖ +
        ‖(2 : ℂ) ^ (-(2 * s.1)) * mayerPeriodCore s.1 ((a + 1) / 2) -
          mayerPeriodCore s.1 2‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ ((B * 2 ^ β) * a ^ β + B * a ^ β) +
      ((B * 2 ^ β) * a ^ β + L * a ^ β) :=
      add_le_add (add_le_add hfirst hhalf) (add_le_add hr hsh)
    _ = _ := by ring

private theorem whole_haar_of_local_power_bound {f : ℝ → ℂ}
    (hf : Measurable f) (hupper : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioi 1))
    {D : ℝ} (hb : ∀ a > 0, ‖f a‖ ≤ D) {β : ℝ} (hβ : 0 < β)
    {C δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ a ∈ Ioo 0 δ, ‖f a‖ ≤ C * a ^ β) :
    IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioi 0) := by
  let e := min δ 1
  have he : 0 < e := lt_min hδ zero_lt_one
  have hp : IntegrableOn (fun a : ℝ => a ^ (2 * β - 1)) (Ioo 0 e) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff he).mpr (by linarith only [hβ])
  have hi0 : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Ioo 0 e) := by
    apply (hp.const_mul (C ^ 2)).mono'
      ((hf.norm.pow_const 2).div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    have hfa := hlow a ⟨ha.1, ha.2.trans_le (min_le_left δ 1)⟩
    change ‖(‖f a‖ ^ 2 / a : ℝ)‖ ≤ C ^ 2 * a ^ (2 * β - 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha.1.le)]
    have hpow : a ^ (2 * β - 1) * a = (a ^ β) ^ 2 := by
      calc
        _ = a ^ (2 * β - 1) * a ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = a ^ (β * 2) := by rw [← Real.rpow_add ha.1]; congr 1; ring
        _ = _ := by rw [Real.rpow_mul ha.1.le, Real.rpow_two]
    apply (div_le_iff₀ ha.1).mpr
    calc
      ‖f a‖ ^ 2 ≤ (C * a ^ β) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfa 2
      _ = (C ^ 2 * a ^ (2 * β - 1)) * a := by rw [mul_assoc, hpow, mul_pow]
  have him : IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 / a) (Icc e 1) := by
    have hc : IntegrableOn (fun _ : ℝ => D ^ 2 / e) (Icc e 1) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    apply hc.mono' ((hf.norm.pow_const 2).div measurable_id).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    have ha0 : 0 < a := he.trans_le ha.1
    change ‖(‖f a‖ ^ 2 / a : ℝ)‖ ≤ D ^ 2 / e
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) ha0.le)]
    calc
      ‖f a‖ ^ 2 / a ≤ D ^ 2 / a :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb a ha0) 2) ha0.le
      _ ≤ D ^ 2 / e := div_le_div_of_nonneg_left (sq_nonneg _) he ha.1
  apply ((hi0.union him).union hupper).mono_set
  intro a ha
  by_cases hlt : a < e
  · exact Or.inl (Or.inl ⟨ha, hlt⟩)
  · by_cases ha1 : a ≤ 1
    · exact Or.inl (Or.inr ⟨le_of_not_gt hlt, ha1⟩)
    · exact Or.inr (lt_of_not_ge ha1)

/-- The exact lower-cusp trace is retained separately from the square-integrable Hecke remainder. -/
def mayerHeckeBoundaryRemainder (s : ℂ) (a : ℝ) : ℂ :=
  lewisHeckeT2 s (mayerPeriodCore s) a -
    (Ioo (0 : ℝ) 1).indicator (fun _ => mayerPeriodCore s 2) a

/-- Subtracting one explicit boundary channel restores whole-axis Haar energy. -/
theorem mayerHeckeBoundaryRemainder_finite_whole_haar (s : upperMayerResonances) :
    IntegrableOn (fun a : ℝ => ‖mayerHeckeBoundaryRemainder s.1 a‖ ^ 2 / a) (Ioi 0) := by
  have hmψ := mayerPeriodCore_measurable s.2.1
  have hmT : Measurable (lewisHeckeT2 s.1 (mayerPeriodCore s.1)) := by
    unfold lewisHeckeT2
    fun_prop
  have hmi : Measurable ((Ioo (0 : ℝ) 1).indicator (fun _ => mayerPeriodCore s.1 2)) :=
    measurable_const.indicator measurableSet_Ioo
  have hmf : Measurable (mayerHeckeBoundaryRemainder s.1) := hmT.sub hmi
  have hu : IntegrableOn (fun a : ℝ => ‖mayerHeckeBoundaryRemainder s.1 a‖ ^ 2 / a) (Ioi 1) := by
    have ht := (lewisHeckeWord_mayerPeriodCore_finite_cusp_energy
      s.2.2.1 s.2.2.2.1 s.2.1 [LewisHeckePrime.two]).1
    apply ht.congr_fun _ measurableSet_Ioi
    intro a ha
    have hnot : a ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_ge ha.le) h.2
    simp only [mayerHeckeBoundaryRemainder, indicator_of_notMem hnot, sub_zero, lewisHeckeWord]
  obtain ⟨D, hD, hdecay⟩ := lewisHeckeWord_mayerPeriodCore_decay
    s.2.2.1 s.2.2.2.1 s.2.1 [LewisHeckePrime.two]
  have hb : ∀ a > 0, ‖mayerHeckeBoundaryRemainder s.1 a‖ ≤ D + ‖mayerPeriodCore s.1 2‖ := by
    intro a ha
    have hpow : (1 + a) ^ (-(2 * s.1.re)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [ha])
        (by linarith only [s.2.2.1])
    have ht : ‖lewisHeckeT2 s.1 (mayerPeriodCore s.1) a‖ ≤ D :=
      (hdecay a ha).trans ((mul_le_mul_of_nonneg_left hpow hD).trans_eq (mul_one D))
    have hi : ‖(Ioo (0 : ℝ) 1).indicator (fun _ => mayerPeriodCore s.1 2) a‖ ≤
        ‖mayerPeriodCore s.1 2‖ := by
      by_cases hm : a ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hm]
      · rw [indicator_of_notMem hm, norm_zero]
        exact norm_nonneg _
    exact (norm_sub_le _ _).trans (add_le_add ht hi)
  obtain ⟨C, δ, _, hδ, hlo⟩ := hecke_mayerPeriodCore_sub_trace_bound s
  apply whole_haar_of_local_power_bound (C := C) hmf hu hb
    (show 0 < 1 - 2 * s.1.re by linarith only [s.2.2.2.1]) (lt_min hδ zero_lt_one)
  intro a ha
  rw [mayerHeckeBoundaryRemainder,
    indicator_of_mem (show a ∈ Ioo (0 : ℝ) 1 from ⟨ha.1, ha.2.trans_le (min_le_right _ _)⟩)]
  exact hlo a ⟨ha.1, ha.2.trans_le (min_le_left _ _)⟩

/-- The lower-cusp limit is the nonzero first-prime core value. -/
theorem tendsto_hecke_mayerPeriodCore_lower (s : upperMayerResonances) :
    Tendsto (lewisHeckeT2 s.1 (mayerPeriodCore s.1)) (𝓝[>] 0)
      (𝓝 (mayerPeriodCore s.1 2)) := by
  obtain ⟨C, δ, _, hδ, hb⟩ := hecke_mayerPeriodCore_sub_trace_bound s
  have hβ : 0 < 1 - 2 * s.1.re := by linarith only [s.2.2.2.1]
  have hp : Tendsto (fun a : ℝ => a ^ (1 - 2 * s.1.re)) (𝓝[>] 0) (𝓝 0) := by
    have hc := Real.continuousAt_rpow_const 0 (1 - 2 * s.1.re) (Or.inr hβ.le)
    have hh := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [Real.zero_rpow hβ.ne'] at hh
  have he : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      ‖lewisHeckeT2 s.1 (mayerPeriodCore s.1) a - mayerPeriodCore s.1 2‖ ≤
        C * a ^ (1 - 2 * s.1.re) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨δ, hδ, fun a ha => hb a ha⟩
  have hz : Tendsto (fun a : ℝ =>
      lewisHeckeT2 s.1 (mayerPeriodCore s.1) a - mayerPeriodCore s.1 2)
      (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero_norm' he (by simpa only [mul_zero] using hp.const_mul C)
  simpa only [sub_add_cancel, zero_add] using hz.add_const (mayerPeriodCore s.1 2)

/-- Exactly one boundary coefficient makes the actual Hecke image Haar-square-integrable. -/
theorem hecke_mayerPeriodCore_boundary_charge_iff (s : upperMayerResonances) (c : ℂ) :
    IntegrableOn (fun a : ℝ =>
      ‖lewisHeckeT2 s.1 (mayerPeriodCore s.1) a -
        (Ioo (0 : ℝ) 1).indicator (fun _ => c) a‖ ^ 2 / a) (Ioi 0) ↔
      c = mayerPeriodCore s.1 2 := by
  constructor
  · intro hi
    have he : (fun a : ℝ => lewisHeckeT2 s.1 (mayerPeriodCore s.1) a -
        (Ioo (0 : ℝ) 1).indicator (fun _ => c) a) =ᶠ[𝓝[>] 0]
        (fun a : ℝ => lewisHeckeT2 s.1 (mayerPeriodCore s.1) a - c) := by
      apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
      refine ⟨1, (show (0 : ℝ) < 1 by norm_num), fun a ha => ?_⟩
      change lewisHeckeT2 s.1 (mayerPeriodCore s.1) a -
        (Ioo (0 : ℝ) 1).indicator (fun _ => c) a =
          lewisHeckeT2 s.1 (mayerPeriodCore s.1) a - c
      rw [indicator_of_mem ha]
    have hl := (tendsto_congr' he).mpr ((tendsto_hecke_mayerPeriodCore_lower s).sub_const c)
    have hz := haarSquareIntegrable_zero_trace hl zero_lt_one
      (hi.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1))
    exact (sub_eq_zero.mp hz).symm
  · rintro rfl
    exact mayerHeckeBoundaryRemainder_finite_whole_haar s

/-- Raw source Hecke transport leaves whole-axis Haar space at every upper resonance,
including critical-line resonances. The unique retained boundary channel is essential. -/
theorem hecke_mayerPeriodCore_not_finite_whole_haar (s : upperMayerResonances) :
    ¬ IntegrableOn (fun a : ℝ => ‖lewisHeckeT2 s.1 (mayerPeriodCore s.1) a‖ ^ 2 / a) (Ioi 0) := by
  intro hi
  have hz := haarSquareIntegrable_zero_trace (tendsto_hecke_mayerPeriodCore_lower s) zero_lt_one
    (hi.mono_set (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1))
  exact mayerPeriodCore_two_ne_zero s.2 hz

#print axioms mayerPeriodCore_one_eq
#print axioms mayerPeriodCore_two_eq
#print axioms mayerPeriodCore_two_ne_zero
#print axioms hecke_mayerPeriodCore_sub_trace_bound
#print axioms mayerHeckeBoundaryRemainder_finite_whole_haar
#print axioms tendsto_hecke_mayerPeriodCore_lower
#print axioms hecke_mayerPeriodCore_boundary_charge_iff
#print axioms hecke_mayerPeriodCore_not_finite_whole_haar

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
