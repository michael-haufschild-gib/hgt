import GaloisForLFunctions.RHTower.CCMConnesConsaniFourierTruncation
import GaloisForLFunctions.RHTower.CCMBVMuntzSummation
import GaloisForLFunctions.RHTower.DeningerMeyerPoissonMellinFactorization

/-!
# Rapid bounded-variation Muntz factorization

Connes--Consani's `fouriertruncated1` class is not compactly supported.  This file extends the
compact-source BV Muntz theorem to that literal class.  Bounded variation and the zero integral
control the arithmetic sum at the origin; rapid decay controls both the source and its arithmetic
sum at infinity.  Consequently both Mellin transforms are holomorphic on `Re(s) > 0`, and the
absolute-convergence identity on `Re(s) > 1` continues across the punctured right half-plane.

The resulting critical-line annihilation removes the smooth-even-germ hypothesis from
`scalingact(iii)`: that hypothesis is useful for the paper's explicit mollification proof, but is
not needed for membership in the closed Meyer source.
-/

open Complex Filter MeasureTheory Set Topology Asymptotics
open scoped FourierTransform
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The literal arithmetic sum vanishes on nonpositive scales. -/
theorem ccmFourierTruncatedPoissonValue_zero_of_nonpos
    (f : CCMFourierTruncatedInput) {u : ℝ} (hu : u ≤ 0) :
    ccmFourierTruncatedPoissonValue f u = 0 := by
  have hzero : (fun n : ℕ => f (u * ((n : ℝ) + 1))) = fun _ => 0 := by
    funext n
    exact f.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hu (by positivity))
  rw [ccmFourierTruncatedPoissonValue, hzero, tsum_zero]

/-- The BV cancellation bound holds on the entire real line after zero extension. -/
theorem abs_ccmFourierTruncatedPoissonValue_le_variation_all
    (f : CCMFourierTruncatedInput) (u : ℝ) :
    |ccmFourierTruncatedPoissonValue f u| ≤
      ccmFourierTruncatedVariation f := by
  rcases le_or_gt u 0 with hu | hu
  · rw [ccmFourierTruncatedPoissonValue_zero_of_nonpos f hu, abs_zero]
    exact ccmFourierTruncatedVariation_nonneg f
  · exact abs_ccmFourierTruncatedPoissonValue_le_variation f hu

/-- Natural-power rapid decay implies arbitrary real-power decay for the complexified source. -/
theorem CCMFourierTruncatedInput.isBigO_atTop
    (f : CCMFourierTruncatedInput) (a : ℝ) :
    (fun x : ℝ => ((f x : ℝ) : ℂ)) =O[atTop]
      fun x : ℝ => x ^ (-a) := by
  let N : ℕ := ⌈max a 0⌉₊
  have haN : a ≤ (N : ℝ) :=
    (le_max_left a 0).trans (Nat.le_ceil (max a 0))
  obtain ⟨C, hC, hdecay⟩ := f.rapidDecay N
  refine (Asymptotics.IsBigOWith.of_bound (c := C) ?_).isBigO
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := one_pos.trans_le hx
  have hbound := hdecay hx
  have hrpow : x ^ (-(N : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg haN)
  have hrewrite : C / x ^ N = C * x ^ (-(N : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg hxpos.le]
  rw [Complex.norm_real, Real.norm_eq_abs,
    show ‖x ^ (-a)‖ = x ^ (-a) by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]]
  exact hbound.trans_eq hrewrite |>.trans
    (mul_le_mul_of_nonneg_left hrpow hC)

/-- The arithmetic sum also has arbitrary real-power decay at positive infinity. -/
theorem ccmFourierTruncatedPoissonValue_isBigO_atTop
    (f : CCMFourierTruncatedInput) (a : ℝ) :
    (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) =O[atTop]
      fun x : ℝ => x ^ (-a) := by
  let N : ℕ := ⌈max a 2⌉₊
  have haN : a ≤ (N : ℝ) :=
    (le_max_left a 2).trans (Nat.le_ceil (max a 2))
  have hN : 2 ≤ N := by
    exact_mod_cast (le_max_right a 2).trans (Nat.le_ceil (max a 2))
  obtain ⟨D, hD, hdecay⟩ :=
    ccmFourierTruncatedPoisson_rapidDecay f N hN
  refine (Asymptotics.IsBigOWith.of_bound (c := D) ?_).isBigO
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := one_pos.trans_le hx
  have hbound := hdecay hx
  have hrpow : x ^ (-(N : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg haN)
  have hrewrite : D / x ^ N = D * x ^ (-(N : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast,
      ← Real.rpow_neg hxpos.le]
  rw [Complex.norm_real, Real.norm_eq_abs,
    show ‖x ^ (-a)‖ = x ^ (-a) by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hxpos.le _)]]
  exact hbound.trans_eq hrewrite |>.trans
    (mul_le_mul_of_nonneg_left hrpow hD)

/-- The literal source Mellin transform converges on the full right half-plane. -/
theorem CCMFourierTruncatedInput.mellinConvergent
    (f : CCMFourierTruncatedInput) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => ((f x : ℝ) : ℂ)) s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((GaloisForLFunctions.RHTower.locallyIntegrable_ofReal_of_bound
      f.measurable (fun x => abs_ccmFourierTruncatedInput_le_variation f x)).locallyIntegrableOn _)
    (f.isBigO_atTop (s.re + 1)) (by linarith) ?_ hs
  exact GaloisForLFunctions.RHTower.isBigO_zero_of_bound
    (fun x => abs_ccmFourierTruncatedInput_le_variation f x)

/-- The arithmetic-sum Mellin transform converges on the full right half-plane. -/
theorem mellinConvergent_ccmFourierTruncatedPoissonValue
    (f : CCMFourierTruncatedInput) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent
      (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((GaloisForLFunctions.RHTower.locallyIntegrable_ofReal_of_bound
      (measurable_ccmFourierTruncatedPoissonValue f)
      (abs_ccmFourierTruncatedPoissonValue_le_variation_all f)).locallyIntegrableOn _)
    (ccmFourierTruncatedPoissonValue_isBigO_atTop f (s.re + 1))
    (by linarith) ?_ hs
  exact GaloisForLFunctions.RHTower.isBigO_zero_of_bound
    (abs_ccmFourierTruncatedPoissonValue_le_variation_all f)

theorem differentiableAt_mellin_ccmFourierTruncatedInput
    (f : CCMFourierTruncatedInput) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun x : ℝ => ((f x : ℝ) : ℂ))) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((GaloisForLFunctions.RHTower.locallyIntegrable_ofReal_of_bound
      f.measurable (fun x => abs_ccmFourierTruncatedInput_le_variation f x)).locallyIntegrableOn _)
    (f.isBigO_atTop (s.re + 1)) (by linarith) ?_ hs
  exact GaloisForLFunctions.RHTower.isBigO_zero_of_bound
    (fun x => abs_ccmFourierTruncatedInput_le_variation f x)

theorem differentiableAt_mellin_ccmFourierTruncatedPoissonValue
    (f : CCMFourierTruncatedInput) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (mellin (fun x : ℝ =>
        ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ))) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((GaloisForLFunctions.RHTower.locallyIntegrable_ofReal_of_bound
      (measurable_ccmFourierTruncatedPoissonValue f)
      (abs_ccmFourierTruncatedPoissonValue_le_variation_all f)).locallyIntegrableOn _)
    (ccmFourierTruncatedPoissonValue_isBigO_atTop f (s.re + 1))
    (by linarith) ?_ hs
  exact GaloisForLFunctions.RHTower.isBigO_zero_of_bound
    (abs_ccmFourierTruncatedPoissonValue_le_variation_all f)

/-- The real CCM arithmetic sum is the generic complex Meyer sum, pointwise. -/
theorem deningerMeyerSum_ccmFourierTruncatedInput
    (f : CCMFourierTruncatedInput) (x : ℝ) :
    deningerMeyerSum (fun t : ℝ => ((f t : ℝ) : ℂ)) x =
      ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ) := by
  rw [deningerMeyerSum, ccmFourierTruncatedPoissonValue,
    Complex.ofReal_tsum]
  exact tsum_congr fun n => by rw [mul_comm]

/-- Muntz factorization in its half-plane of absolute convergence for the literal rapid BV
source. -/
theorem mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul
    (f : CCMFourierTruncatedInput) {s : ℂ} (hs : 1 < s.re) :
    mellin
        (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) s =
      riemannZeta s * mellin (fun x : ℝ => ((f x : ℝ) : ℂ)) s := by
  have hsumfun :
      (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) =
        deningerMeyerSum (fun x : ℝ => ((f x : ℝ) : ℂ)) := by
    funext x
    exact (deningerMeyerSum_ccmFourierTruncatedInput f x).symm
  rw [hsumfun]
  apply mellin_deningerMeyerSum hs
  · exact (Complex.measurable_ofReal.comp f.measurable).aestronglyMeasurable.restrict
  · have hconv := f.mellinConvergent (lt_trans zero_lt_one hs)
    have hnorm := (mellin_convergent_iff_norm
      (subset_refl _) measurableSet_Ioi
      (Complex.measurable_ofReal.comp f.measurable).aestronglyMeasurable.restrict).mp hconv
    simpa using hnorm

/-- **Rapid BV Muntz factorization.**  The exact zeta multiplier identity holds throughout the
punctured right half-plane. -/
theorem mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul_of_re_pos
    (f : CCMFourierTruncatedInput) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    mellin
        (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) s =
      riemannZeta s * mellin (fun x : ℝ => ((f x : ℝ) : ℂ)) s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  let F : ℂ → ℂ := fun z =>
    mellin (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) z
  let G : ℂ → ℂ := fun z =>
    riemannZeta z * mellin (fun x : ℝ => ((f x : ℝ) : ℂ)) z
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hFan : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (differentiableAt_mellin_ccmFourierTruncatedPoissonValue f hz.1).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact ((differentiableAt_riemannZeta hz.2).mul
      (differentiableAt_mellin_ccmFourierTruncatedInput f hz.1)).differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ U := by
    exact ⟨by simp, by simp⟩
  have hevent : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hhalf : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hhalf] with z hz
    exact mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul f hz
  have hEqOn : Set.EqOn F G U :=
    hFan.eqOn_of_preconnected_of_eventuallyEq hGan
      isPreconnected_halfplane_punctured h2mem hevent
  exact hEqOn ⟨hs0, hs1⟩

/-- Every positive-half-plane zeta zero annihilates the Mellin transform of the literal rapid BV
arithmetic sum. -/
theorem mellin_ccmFourierTruncatedPoissonValue_eq_zero_of_zeta_zero
    (f : CCMFourierTruncatedInput) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1) (hζ : riemannZeta ρ = 0) :
    mellin
      (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)) ρ = 0 := by
  rw [mellin_ccmFourierTruncatedPoissonValue_eq_zeta_mul_of_re_pos
    f hρ0 hρ1, hζ, zero_mul]

/-- Reflection changes the sign of the Fourier frequency. -/
theorem fourier_ccm_comp_neg (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun t : ℝ => g (-t)) ξ = 𝓕 g (-ξ) := by
  rw [← Real.fourierInv_eq_fourier_comp_neg g]
  exact Real.fourierInv_eq_fourier_neg g ξ

/-- The paper's half-density log boundary is the exact critical-line Mellin transform of its
arithmetic sum, with mathlib's `2*pi` Fourier normalization. -/
theorem fourier_ccmFourierTruncatedLogBoundary_eq_mellin
    (f : CCMFourierTruncatedInput) (ξ : ℝ) :
    𝓕 (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ)) ξ =
      mellin
        (fun x : ℝ => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ))
        ((1 / 2 : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  let A : ℝ → ℂ := fun x => ((ccmFourierTruncatedPoissonValue f x : ℝ) : ℂ)
  let B : ℝ → ℂ := fun t => (ccmFourierTruncatedLogBoundary f t : ℂ)
  have hsource : logMellinLineSource A (1 / 2) = fun t : ℝ => B (-t) := by
    funext t
    rw [logMellinLineSource]
    change (Real.exp (-(1 / 2 : ℝ) * t) : ℂ) *
        (ccmFourierTruncatedPoissonValue f (Real.exp (-t)) : ℂ) =
      (ccmFourierTruncatedE f (Real.exp (-t)) : ℂ)
    rw [ccmFourierTruncatedE, Complex.ofReal_mul, ← Real.exp_half]
    congr 2
    ring
  have hline := mellin_line_eq_fourier_logMellinLineSource
    A (1 / 2) (-2 * Real.pi * ξ)
  have hfreq : (-2 * Real.pi * ξ) / (2 * Real.pi) = -ξ := by
    field_simp
  rw [hfreq, hsource, fourier_ccm_comp_neg, neg_neg] at hline
  change mellin A
      (((1 / 2 : ℝ) : ℂ) + ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) =
    𝓕 B ξ at hline
  have hpoint :
      (((1 / 2 : ℝ) : ℂ) + ((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) =
        (1 / 2 : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hpoint] at hline
  exact hline.symm

/-- Every critical-line zeta zero annihilates the exact Fourier coefficient of the rough
half-density boundary. -/
theorem fourier_ccmFourierTruncatedLogBoundary_eq_zero_of_zeta_zero
    (f : CCMFourierTruncatedInput) (ξ : ℝ)
    (hζ : riemannZeta
      ((1 / 2 : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) = 0) :
    𝓕 (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ)) ξ = 0 := by
  rw [fourier_ccmFourierTruncatedLogBoundary_eq_mellin]
  apply mellin_ccmFourierTruncatedPoissonValue_eq_zero_of_zeta_zero f
  · simp
  · intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  · exact hζ

end

end RHTower
