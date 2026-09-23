import GaloisForLFunctions.RHTower.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.HedenmalmWeightedAdjointCore
import GaloisForLFunctions.RHTower.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket

/-!
# Theta source in the genuine spherical EKG cubic tail

`[LITERATURE]` Bizoń--Chmaj--Rostworowski, arXiv:0812.4333, expand the spherically
symmetric Einstein--massless-Klein--Gordon system in three spatial dimensions as

`phi = epsilon phi₁ + epsilon³ phi₃ + ...`,
`m = epsilon² m₂ + ...`, `beta = epsilon² beta₂ + ...`.

The second-order Einstein variables obey

`m₂' = 4 pi r² (phidot₁² + phi₁'²)`,
`betadot₂` and `beta₂'` are sourced by the same positive quadratic stress energy,

and the first nonlinear scalar field satisfies the genuine backreaction equation

`Box phi₃ = 2 beta₂ phiddot₁ + betadot₂ phidot₁ + beta₂' phi₁'`.

For an outgoing generator `a`, their timelike-infinity cubic coefficient is

`Gamma₀ = -32 pi ∫ a(s) I₁⁰(s) ds`,
`I₁⁰(s) = ∫_s^infinity a'(u)² du`.

Compact support may be replaced by sufficient falloff; the completed theta source is Schwartz
with every exponential derivative moment.  This file inserts the literal theta source
`a = thetaCuspFullSource` into that coefficient functional.  It proves, without a sign
hypothesis, that the ordered derivative-energy mass is strictly positive and hence
`Gamma₀ < 0`.

`[PHYSICAL NO-GO]` This is actual EKG backreaction, not a KMS/CCR label.  It disproves the
claim that passivity or positive stress energy generically excludes negative cubic response.
It does not identify this scalar tail coefficient with the three-shell determinant in
`ThetaCuspHawkingBackreactionCubicCompletionEndpoint`; that identification would be an additional
dynamical incidence theorem.

`[SCOPE]` The literature formula is the small-data, spherical, subcritical EKG tail about
Minkowski spacetime.  Lean formalizes the coefficient functional and its theta-specific sign,
not the PDE asymptotic derivation.  No Schwarzschild horizon or Teukolsky mode is claimed here.
In spherical symmetry there is no radiative gravitational Teukolsky sector.

`[OPEN CORE]` Derive the renormalized Schwarzschild-exterior cubic coefficient after subtracting
the linear Price tail, including the radial Jost/greybody kernel, and determine whether its sign
survives.  For nonspherical perturbations, do the same with the second-order Teukolsky source.
Until that coefficient-level incidence is proved, KMS/passivity and canonical Cayley completion
remain conditional and cannot carry an RH implication.
-/

open MeasureTheory Set Filter Topology
open intervalIntegral

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Positive quadratic derivative-energy density entering the spherical EKG memory kernel. -/
def thetaCuspEKGDerivativeEnergyDensity (u : ℝ) : ℝ :=
  sourceDeriv u ^ (2 : ℕ)

/-- BCR ordered memory `I₁⁰(s) = ∫_s^∞ a'(u)² du` for the completed theta source. -/
def thetaCuspEKGCumulativeDerivativeEnergy (s : ℝ) : ℝ :=
  ∫ u in Ioi s, thetaCuspEKGDerivativeEnergyDensity u

/-- Ordered theta/Einstein coupling mass in the BCR timelike cubic coefficient. -/
def thetaCuspEKGCubicTailMass : ℝ :=
  ∫ s : ℝ, thetaCuspFullSource s * thetaCuspEKGCumulativeDerivativeEnergy s

/-- Literal three-dimensional BCR coefficient `Gamma₀ = -32 pi ∫ a I₁⁰`. -/
def thetaCuspEKGCubicTailCoefficient : ℝ :=
  (-32 * Real.pi) * thetaCuspEKGCubicTailMass

theorem continuous_thetaCuspEKGDerivativeEnergyDensity :
    Continuous thetaCuspEKGDerivativeEnergyDensity := by
  exact continuous_sourceDeriv.pow 2

theorem integrable_abs_thetaCuspEKGSourceDeriv :
    Integrable (fun x : ℝ => |sourceDeriv x|) := by
  have h := integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 1 0
  simpa [sourceDeriv, iteratedDeriv_one] using h

theorem abs_thetaCuspEKGSourceDeriv_le (x : ℝ) :
    |sourceDeriv x| ≤ thetaCuspDerivativeExpConstant 1 := by
  have h := weighted_iteratedDeriv_thetaCuspFullSource_le 0 1 x
  simpa [sourceDeriv, iteratedDeriv_one, Real.norm_eq_abs] using h

theorem integrable_thetaCuspEKGDerivativeEnergyDensity :
    Integrable thetaCuspEKGDerivativeEnergyDensity := by
  have hmajor := integrable_abs_thetaCuspEKGSourceDeriv.const_mul
    (thetaCuspDerivativeExpConstant 1)
  apply Integrable.mono hmajor
  · exact continuous_thetaCuspEKGDerivativeEnergyDensity.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hC := thetaCuspDerivativeExpConstant_nonneg 1
    have hdx := abs_thetaCuspEKGSourceDeriv_le x
    change abs (sourceDeriv x ^ (2 : ℕ)) ≤
      abs (thetaCuspDerivativeExpConstant 1 * abs (sourceDeriv x))
    calc
      |sourceDeriv x ^ (2 : ℕ)| = |sourceDeriv x| * |sourceDeriv x| := by
        rw [abs_pow]
        ring
      _ ≤ thetaCuspDerivativeExpConstant 1 * |sourceDeriv x| :=
        mul_le_mul_of_nonneg_right hdx (abs_nonneg _)
      _ = abs (thetaCuspDerivativeExpConstant 1 * abs (sourceDeriv x)) := by
        rw [abs_mul, abs_of_nonneg hC, abs_abs]

/-- The theta packet is not dynamically trivial: its derivative is nonzero at some positive
retarded time.  Strict reflected-product cooling supplies endpoint separation; the mean-value
theorem supplies the derivative point. -/
theorem exists_thetaCuspEKGSourceDeriv_ne_zero :
    ∃ c ∈ Ioo (0 : ℝ) 1, sourceDeriv c ≠ 0 := by
  have hprod := strictAntiOn_thetaCuspFullSource_mul_reflect 0
    (show (0 : ℝ) ∈ Ici 0 by simp) (show (1 : ℝ) ∈ Ici 0 by simp) zero_lt_one
  have hne : thetaCuspFullSource 1 ≠ thetaCuspFullSource 0 := by
    intro h
    simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at hprod
    rw [h] at hprod
    exact lt_irrefl _ hprod
  obtain ⟨c, hc, hder⟩ := exists_deriv_eq_slope thetaCuspFullSource zero_lt_one
    contDiff_thetaCuspFullSource.continuous.continuousOn
    (contDiff_thetaCuspFullSource.differentiable (by simp)).differentiableOn
  refine ⟨c, hc, ?_⟩
  rw [sourceDeriv, hder]
  norm_num
  exact sub_ne_zero.mpr hne

theorem continuous_thetaCuspEKGCumulativeDerivativeEnergy :
    Continuous thetaCuspEKGCumulativeDerivativeEnergy := by
  let q := thetaCuspEKGDerivativeEnergyDensity
  have hq : Integrable q := integrable_thetaCuspEKGDerivativeEnergyDensity
  have hrepr : thetaCuspEKGCumulativeDerivativeEnergy = fun s : ℝ =>
      (∫ u in Ioi 0, q u) - ∫ u in (0 : ℝ)..s, q u := by
    funext s
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi'
      (hq.integrableOn : IntegrableOn q (Ioi 0))
      (hq.integrableOn : IntegrableOn q (Ioi s))
    dsimp [thetaCuspEKGCumulativeDerivativeEnergy]
    change (∫ u in Ioi s, q u) = _
    linarith
  rw [hrepr]
  exact continuous_const.sub (hq.continuous_primitive 0)

theorem thetaCuspEKGCumulativeDerivativeEnergy_nonneg (s : ℝ) :
    0 ≤ thetaCuspEKGCumulativeDerivativeEnergy s := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u _
  exact sq_nonneg _

theorem thetaCuspEKGCumulativeDerivativeEnergy_le_total (s : ℝ) :
    thetaCuspEKGCumulativeDerivativeEnergy s ≤
      ∫ u : ℝ, thetaCuspEKGDerivativeEnergyDensity u := by
  unfold thetaCuspEKGCumulativeDerivativeEnergy
  simpa only [Measure.restrict_univ] using
    (setIntegral_mono_set integrable_thetaCuspEKGDerivativeEnergyDensity.integrableOn
      (Filter.Eventually.of_forall fun u => sq_nonneg (sourceDeriv u))
      (Set.subset_univ (Ioi s)).eventuallyLE)

theorem exists_thetaCuspEKGCumulativeDerivativeEnergy_pos :
    ∃ s : ℝ, 0 < thetaCuspEKGCumulativeDerivativeEnergy s := by
  obtain ⟨c, hc, hdc⟩ := exists_thetaCuspEKGSourceDeriv_ne_zero
  let s := c - 1
  refine ⟨s, ?_⟩
  unfold thetaCuspEKGCumulativeDerivativeEnergy
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun u => sq_nonneg (sourceDeriv u))
    integrable_thetaCuspEKGDerivativeEnergyDensity.integrableOn).2
  have hopen : IsOpen
      (Function.support thetaCuspEKGDerivativeEnergyDensity ∩ Ioi s) :=
    continuous_thetaCuspEKGDerivativeEnergyDensity.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨c, ?_, ?_⟩
  · change sourceDeriv c ^ (2 : ℕ) ≠ 0
    exact pow_ne_zero 2 hdc
  · norm_num [s]

theorem integrable_thetaCuspEKGCubicTailDensity :
    Integrable (fun s : ℝ =>
      thetaCuspFullSource s * thetaCuspEKGCumulativeDerivativeEnergy s) := by
  let D := ∫ u : ℝ, thetaCuspEKGDerivativeEnergyDensity u
  have hD : 0 ≤ D := integral_nonneg fun u => sq_nonneg (sourceDeriv u)
  have hmajor := integrable_thetaCuspFullSource.mul_const D
  apply Integrable.mono hmajor
  · exact (contDiff_thetaCuspFullSource.continuous.mul
      continuous_thetaCuspEKGCumulativeDerivativeEnergy).aestronglyMeasurable
  · filter_upwards with s
    have hsource := thetaCuspFullSource_pos s
    have hE := thetaCuspEKGCumulativeDerivativeEnergy_nonneg s
    have hEle := thetaCuspEKGCumulativeDerivativeEnergy_le_total s
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsource.le hE),
      abs_of_nonneg (mul_nonneg hsource.le hD)]
    exact mul_le_mul_of_nonneg_left hEle hsource.le

/-- The ordered theta/Einstein derivative-energy coupling has strictly positive mass. -/
theorem thetaCuspEKGCubicTailMass_pos :
    0 < thetaCuspEKGCubicTailMass := by
  obtain ⟨s, hs⟩ := exists_thetaCuspEKGCumulativeDerivativeEnergy_pos
  unfold thetaCuspEKGCubicTailMass
  apply integral_pos_of_integrable_nonneg_nonzero
    (contDiff_thetaCuspFullSource.continuous.mul
      continuous_thetaCuspEKGCumulativeDerivativeEnergy)
    integrable_thetaCuspEKGCubicTailDensity
    (fun x => mul_nonneg (thetaCuspFullSource_pos x).le
      (thetaCuspEKGCumulativeDerivativeEnergy_nonneg x))
  exact (mul_pos (thetaCuspFullSource_pos s) hs).ne'

/-- **Actual spherical EKG orientation is negative.**  The BCR cubic coefficient of the literal
completed theta packet lies in the negative chamber. -/
theorem thetaCuspEKGCubicTailCoefficient_neg :
    thetaCuspEKGCubicTailCoefficient < 0 := by
  unfold thetaCuspEKGCubicTailCoefficient
  have hpos : 0 < 32 * Real.pi * thetaCuspEKGCubicTailMass :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) thetaCuspEKGCubicTailMass_pos
  linarith

/-- Consequently no unconditional nonnegativity/passivity law can hold for this genuine EKG
cubic observable. -/
theorem not_thetaCuspEKGCubicTailCoefficient_nonneg :
    ¬ 0 ≤ thetaCuspEKGCubicTailCoefficient :=
  not_le_of_gt thetaCuspEKGCubicTailCoefficient_neg

end RHTower
