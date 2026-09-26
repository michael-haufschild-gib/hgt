import GaloisForLFunctions.RHTower.ThetaPrimeScalingRigidity

/-!
# Exact prime--Gamma quadratic scaling identity

The positive full prime-link energy expands into its two source marginals
minus twice the real cross pairing. For the actual theta source, adding
the equations at opposite coordinates identifies the diagonal marginal
with the symmetric Gamma/pole source. The resulting arithmetic inequality
is sharp: equality holds exactly for constant scaling profiles.

The Gamma expression here is a diagonal weight obtained by applying the
source operator to the fixed theta kernel. It is not an identification
with that nonlocal operator on arbitrary test functions or with an
RH-equivalent spectral form.
-/

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate

namespace RHTower.ThetaSourceWard

def thetaPrimeProfileSquare (chi : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ((‖chi x‖ ^ 2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (chi.continuous.norm.pow 2)) (‖chi‖ ^ 2)
    (fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (chi.norm_coe_le_norm x) 2)

theorem thetaPrimeProfileSquare_apply (chi : ℝ →ᵇ ℂ) (x : ℝ) :
    thetaPrimeProfileSquare chi x = ((‖chi x‖ ^ 2 : ℝ) : ℂ) := rfl

theorem integrable_thetaPrimeProfilePairing (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun x : ℝ => chi x * ((T.k x : ℂ) * fullPrimeSource S x)) :=
  (integrable_thetaPrimePairing S T).bdd_mul chi.continuous.aestronglyMeasurable
    (Eventually.of_forall chi.norm_coe_le_norm)

theorem integrable_thetaPrimeProfileReflectedPairing (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun x : ℝ => chi x * ((S.k x : ℂ) * fullPrimeSource T (-x))) := by
  simpa only [S.even'] using (integrable_thetaPrimePairing T S).comp_neg.bdd_mul
    chi.continuous.aestronglyMeasurable (Eventually.of_forall chi.norm_coe_le_norm)

theorem integrable_thetaPrimeSquare_source (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun p : ℕ × ℝ => ‖chi p.2‖ ^ 2 * (thetaPrimeLinkDensity S T p).re)
      thetaPrimeLinkMeasure := by
  simpa only [RCLike.re_to_complex, thetaPrimeProfileSquare_apply, Complex.re_ofReal_mul] using
    (integrable_thetaPrimeLink_sourceTest S T (thetaPrimeProfileSquare chi)).re

theorem integrable_thetaPrimeSquare_target (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun p : ℕ × ℝ =>
      ‖chi (p.2 + Real.log p.1)‖ ^ 2 * (thetaPrimeLinkDensity S T p).re)
      thetaPrimeLinkMeasure := by
  simpa only [RCLike.re_to_complex, thetaPrimeProfileSquare_apply, Complex.re_ofReal_mul] using
    (integrable_thetaPrimeLink_targetTest S T (thetaPrimeProfileSquare chi)).re

theorem integrable_thetaPrimeSquare_sourceMarginal (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun x : ℝ => ‖chi x‖ ^ 2 * ((T.k x : ℂ) * fullPrimeSource S x).re) := by
  simpa only [RCLike.re_to_complex, thetaPrimeProfileSquare_apply, Complex.re_ofReal_mul] using
    (integrable_thetaPrimeProfilePairing S T (thetaPrimeProfileSquare chi)).re

theorem integrable_thetaPrimeSquare_targetMarginal (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun x : ℝ => ‖chi x‖ ^ 2 * ((S.k x : ℂ) * fullPrimeSource T (-x)).re) := by
  simpa only [RCLike.re_to_complex, thetaPrimeProfileSquare_apply, Complex.re_ofReal_mul] using
    (integrable_thetaPrimeProfileReflectedPairing S T (thetaPrimeProfileSquare chi)).re

theorem integral_thetaPrimeSquare_source (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    (∫ p, ‖chi p.2‖ ^ 2 * (thetaPrimeLinkDensity S T p).re ∂thetaPrimeLinkMeasure) =
      ∫ x : ℝ, ‖chi x‖ ^ 2 * ((T.k x : ℂ) * fullPrimeSource S x).re := by
  have h := congrArg Complex.re (integral_thetaPrimeLink_sourceTest S T (thetaPrimeProfileSquare chi))
  have h₁ := integral_re (integrable_thetaPrimeLink_sourceTest S T (thetaPrimeProfileSquare chi))
  have h₂ := integral_re (integrable_thetaPrimeProfilePairing S T (thetaPrimeProfileSquare chi))
  simp only [RCLike.re_to_complex] at h₁ h₂
  rw [← h₁, ← h₂] at h
  simpa only [thetaPrimeProfileSquare_apply, Complex.re_ofReal_mul] using h

theorem integral_thetaPrimeSquare_target (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    (∫ p, ‖chi (p.2 + Real.log p.1)‖ ^ 2 * (thetaPrimeLinkDensity S T p).re
      ∂thetaPrimeLinkMeasure) =
      ∫ x : ℝ, ‖chi x‖ ^ 2 * ((S.k x : ℂ) * fullPrimeSource T (-x)).re := by
  have he : (∫ x : ℝ, thetaPrimeProfileSquare chi (-x) * ((S.k x : ℂ) * fullPrimeSource T x)) =
      ∫ x : ℝ, thetaPrimeProfileSquare chi x * ((S.k x : ℂ) * fullPrimeSource T (-x)) := by
    simpa only [S.even', neg_neg] using integral_neg_eq_self
      (fun x : ℝ => thetaPrimeProfileSquare chi x * ((S.k x : ℂ) * fullPrimeSource T (-x))) volume
  have h := congrArg Complex.re
    ((integral_thetaPrimeLink_targetTest S T (thetaPrimeProfileSquare chi)).trans he)
  have h₁ := integral_re (integrable_thetaPrimeLink_targetTest S T (thetaPrimeProfileSquare chi))
  have h₂ := integral_re (integrable_thetaPrimeProfileReflectedPairing S T (thetaPrimeProfileSquare chi))
  simp only [RCLike.re_to_complex] at h₁ h₂
  rw [← h₁, ← h₂] at h
  simpa only [thetaPrimeProfileSquare_apply, Complex.re_ofReal_mul] using h

def thetaPrimeScalingCrossDensity (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (p : ℕ × ℝ) : ℝ :=
  (chi (p.2 + Real.log p.1) * conj (chi p.2)).re * (thetaPrimeLinkDensity S T p).re

def thetaPrimeScalingCross (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) : ℝ :=
  ∫ p, thetaPrimeScalingCrossDensity S T chi p ∂thetaPrimeLinkMeasure

theorem integrable_thetaPrimeScalingCrossDensity (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (thetaPrimeScalingCrossDensity S T chi) thetaPrimeLinkMeasure := by
  have hl : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
  have hc := Complex.continuous_re.comp
    ((chi.continuous.comp (continuous_snd.add (hl.comp continuous_fst))).mul
      (Complex.continuous_conj.comp (chi.continuous.comp continuous_snd)))
  apply (integrable_thetaPrimeLinkDensity S T).re.bdd_mul hc.aestronglyMeasurable (c := ‖chi‖ ^ 2)
  filter_upwards with p
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ‖chi (p.2 + Real.log p.1) * conj (chi p.2)‖ := Complex.abs_re_le_norm _
    _ = ‖chi (p.2 + Real.log p.1)‖ * ‖chi p.2‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ ‖chi‖ ^ 2 := by
      simpa only [pow_two] using mul_le_mul (chi.norm_coe_le_norm _)
        (chi.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg chi)

def thetaPrimeScalingDiagonal (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) : ℝ :=
  ∫ x : ℝ, ‖chi x‖ ^ 2 *
    ((T.k x : ℂ) * fullPrimeSource S x + (S.k x : ℂ) * fullPrimeSource T (-x)).re

theorem thetaPrimeScalingDiagonal_eq_marginals (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    thetaPrimeScalingDiagonal S T chi =
      (∫ p, ‖chi p.2‖ ^ 2 * (thetaPrimeLinkDensity S T p).re ∂thetaPrimeLinkMeasure) +
      ∫ p, ‖chi (p.2 + Real.log p.1)‖ ^ 2 * (thetaPrimeLinkDensity S T p).re
        ∂thetaPrimeLinkMeasure := by
  rw [integral_thetaPrimeSquare_source, integral_thetaPrimeSquare_target,
    ← integral_add (integrable_thetaPrimeSquare_sourceMarginal S T chi)
      (integrable_thetaPrimeSquare_targetMarginal S T chi)]
  unfold thetaPrimeScalingDiagonal
  simp only [Complex.add_re, mul_add]

/-- The full weighted prime jump energy is the diagonal marginal minus the cross pairing. -/
theorem thetaPrimeScalingEnergy_eq_diagonal_sub_cross (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    thetaPrimeScalingEnergy S T chi =
      thetaPrimeScalingDiagonal S T chi - 2 * thetaPrimeScalingCross S T chi := by
  have he : thetaPrimeScalingEnergy S T chi =
      ∫ p, ((‖chi p.2‖ ^ 2 * (thetaPrimeLinkDensity S T p).re +
        ‖chi (p.2 + Real.log p.1)‖ ^ 2 * (thetaPrimeLinkDensity S T p).re) -
        2 * thetaPrimeScalingCrossDensity S T chi p) ∂thetaPrimeLinkMeasure := by
    apply integral_congr_ae
    filter_upwards with p
    simp only [thetaPrimeScalingEnergyDensity, thetaPrimeProfileIncrement,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_sub, thetaPrimeScalingCrossDensity]
    ring
  have hsum : Integrable (fun p : ℕ × ℝ =>
      ‖chi p.2‖ ^ 2 * (thetaPrimeLinkDensity S T p).re +
      ‖chi (p.2 + Real.log p.1)‖ ^ 2 * (thetaPrimeLinkDensity S T p).re) thetaPrimeLinkMeasure :=
    (integrable_thetaPrimeSquare_source S T chi).add (integrable_thetaPrimeSquare_target S T chi)
  rw [he, integral_sub hsum
      ((integrable_thetaPrimeScalingCrossDensity S T chi).const_mul 2),
    integral_add (integrable_thetaPrimeSquare_source S T chi)
      (integrable_thetaPrimeSquare_target S T chi), integral_const_mul,
    ← thetaPrimeScalingDiagonal_eq_marginals]
  rfl

/-- The even source equation cancels multiplication by the source coordinate. -/
theorem completeTheta_primeShift_symmetric_balance (x : ℝ) :
    fullPrimeSource thetaCuspTiltSource x + fullPrimeSource thetaCuspTiltSource (-x) =
      thetaArchimedeanShiftSource x + thetaArchimedeanShiftSource (-x) -
        2 * archConstant * (thetaCuspFullSource x : ℂ) := by
  have hp := complete_theta_source_equation x
  have hm := complete_theta_source_equation (-x)
  rw [thetaCuspFullSource_neg, Complex.ofReal_neg] at hm
  unfold thetaArchimedeanShiftSource
  linear_combination -hp - hm

def thetaPrimeGammaScalingDiagonal (chi : ℝ →ᵇ ℂ) : ℝ :=
  ∫ x : ℝ, ‖chi x‖ ^ 2 * ((thetaCuspFullSource x : ℂ) *
    (thetaArchimedeanShiftSource x + thetaArchimedeanShiftSource (-x) -
      2 * archConstant * (thetaCuspFullSource x : ℂ))).re

theorem thetaPrimeGammaScalingDiagonal_eq (chi : ℝ →ᵇ ℂ) :
    thetaPrimeGammaScalingDiagonal chi =
      thetaPrimeScalingDiagonal thetaCuspTiltSource thetaCuspTiltSource chi := by
  unfold thetaPrimeGammaScalingDiagonal thetaPrimeScalingDiagonal
  simp only [thetaCuspTiltSource_k, ← mul_add, completeTheta_primeShift_symmetric_balance]

/-- Exact prime--Gamma quadratic identity with every prime power and both pole channels. -/
theorem thetaPrimeGammaScaling_identity (chi : ℝ →ᵇ ℂ) :
    thetaPrimeGammaScalingDiagonal chi -
      2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi =
        thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource chi := by
  rw [thetaPrimeGammaScalingDiagonal_eq, thetaPrimeScalingEnergy_eq_diagonal_sub_cross]

theorem thetaPrimeGammaScaling_cross_le_diagonal (chi : ℝ →ᵇ ℂ) :
    2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi ≤
      thetaPrimeGammaScalingDiagonal chi := by
  have h := thetaPrimeScalingEnergy_nonneg thetaCuspTiltSource thetaCuspTiltSource chi
  rw [← thetaPrimeGammaScaling_identity] at h
  exact sub_nonneg.mp h

/-- Equality in the arithmetic bound is precisely global reciprocal scaling. -/
theorem thetaPrimeGammaScaling_equality_iff (chi : ℝ →ᵇ ℂ) :
    thetaPrimeGammaScalingDiagonal chi =
      2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi ↔
        chi = BoundedContinuousFunction.const ℝ (chi 0) := by
  rw [← sub_eq_zero, thetaPrimeGammaScaling_identity, thetaPrimeScalingEnergy_eq_zero_iff]

theorem thetaPrimeGammaScaling_strict_iff (chi : ℝ →ᵇ ℂ) :
    2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource chi <
      thetaPrimeGammaScalingDiagonal chi ↔
        chi ≠ BoundedContinuousFunction.const ℝ (chi 0) := by
  rw [← sub_pos, thetaPrimeGammaScaling_identity, thetaPrimeScalingEnergy_pos_iff]

end RHTower.ThetaSourceWard
