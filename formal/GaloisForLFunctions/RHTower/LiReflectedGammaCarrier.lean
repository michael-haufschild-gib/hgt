import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary
import GaloisForLFunctions.HTGeometry.FixedModulusRealRootednessNonselection
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranch

/-!
# Reflected-Gamma Li carrier

This module constructs the card's completed arithmetic-progression carrier.  It proves entirety,
the exact simple critical-line divisor, functional-equation and Schwarz symmetries, classical exact
entire order one, and hypertranscendence off the integral opposite-shift boundary.
-/

open Complex Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Bottcher

noncomputable section

open scoped UnivMeroFieldInstances

/-- Opposite-slope reciprocal-Gamma product before rotation to the centered critical coordinate. -/
def reflectedGammaOppositeCarrier (alpha : ℝ) (z : ℂ) : ℂ :=
  reciprocalGammaEntire (z + (alpha : ℂ)) *
    reciprocalGammaEntire (-z + (alpha : ℂ))

theorem reflectedGammaOppositeCarrier_analyticOnNhd (alpha : ℝ) :
    AnalyticOnNhd ℂ (reflectedGammaOppositeCarrier alpha) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  unfold reflectedGammaOppositeCarrier
  apply Differentiable.mul
  · exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp (by fun_prop)
  · exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp (by fun_prop)

theorem analyticMeroElement_reflectedGammaOppositeCarrier (alpha : ℝ) :
    analyticMeroElement (reflectedGammaOppositeCarrier alpha)
        (reflectedGammaOppositeCarrier_analyticOnNhd alpha) =
      (gammaOppositeShiftProductMero (alpha : ℂ) (alpha : ℂ))⁻¹ := by
  rw [gammaOppositeShiftProductMero, gammaShiftMero, gammaNegativeShiftMero]
  rw [mul_inv_rev, inv_inv, inv_inv]
  rw [analyticMeroElement]
  change algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (reciprocalGammaShiftAnalytic (alpha : ℂ) *
        reciprocalGammaNegativeShiftAnalytic (alpha : ℂ)) = _
  rw [map_mul]
  exact mul_comm _ _

set_option maxHeartbeats 800000 in
theorem reflectedGammaOppositeCarrier_hypertranscendental
    {alpha : ℝ} (hsep : ∀ k : ℤ, (2 * alpha : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (reflectedGammaOppositeCarrier alpha) := by
  intro hDA
  have hfield :=
    differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (reflectedGammaOppositeCarrier_analyticOnNhd alpha) hDA
  rw [analyticMeroElement_reflectedGammaOppositeCarrier alpha] at hfield
  have hbase : HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftProductMero (alpha : ℂ) (alpha : ℂ)) :=
    (hypertranscendentalOver_gammaOppositeShiftProductMero_iff_nonintegerSum
      (alpha : ℂ) (alpha : ℂ)).2 (by
        intro k hk
        apply hsep k
        simpa [two_mul] using hk)
  have hinv : HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftProductMero (alpha : ℂ) (alpha : ℂ))⁻¹ :=
    (HTGeometry.hypertranscendentalOver_inv_iff
      (F := RatFunc ℂ)
      (x := gammaOppositeShiftProductMero (alpha : ℂ) (alpha : ℂ))).2 hbase
  exact hinv hfield

theorem reflectedGammaCarrier_hypertranscendental
    {alpha : ℝ} (hsep : ∀ k : ℤ, (2 * alpha : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (reflectedGammaCarrier alpha) := by
  have hscale := (hypertranscendental_comp_const_mul_iff_uncond
      (f := reflectedGammaOppositeCarrier alpha) (c := I) I_ne_zero).2
      (reflectedGammaOppositeCarrier_hypertranscendental hsep)
  have heq : (fun z => reflectedGammaOppositeCarrier alpha (I * z)) =
      reflectedGammaCarrier alpha := by
    funext z
    simp only [reflectedGammaOppositeCarrier, reflectedGammaCarrier]
    congr 1 <;> ring_nf
  rw [heq] at hscale
  exact hscale

/-- Uncentered reflected-Gamma Li carrier from card equation (13). -/
def liReflectedGammaCarrier (alpha : ℝ) (s : ℂ) : ℂ :=
  reflectedGammaCarrier alpha (s - (1 / 2 : ℂ))

theorem liReflectedGammaCarrier_analyticOnNhd (alpha : ℝ) :
    AnalyticOnNhd ℂ (liReflectedGammaCarrier alpha) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mp
    (reflectedGammaCarrier_analyticOnNhd alpha)).comp (by fun_prop)

theorem liReflectedGammaCarrier_eq_zero_iff {alpha : ℝ} {s : ℂ} :
    liReflectedGammaCarrier alpha s = 0 ↔
      (∃ n : ℕ, s = (1 / 2 : ℂ) + I * ((n : ℂ) + (alpha : ℂ))) ∨
        ∃ n : ℕ, s = (1 / 2 : ℂ) - I * ((n : ℂ) + (alpha : ℂ)) := by
  rw [liReflectedGammaCarrier, reflectedGammaCarrier_eq_zero_iff]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · left
      exact ⟨n, by linear_combination hn⟩
    · right
      exact ⟨n, by linear_combination hn⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · left
      exact ⟨n, by linear_combination hn⟩
    · right
      exact ⟨n, by linear_combination hn⟩

theorem liReflectedGammaCarrier_zero_re_eq_half
    {alpha : ℝ} {s : ℂ} (hs : liReflectedGammaCarrier alpha s = 0) :
    s.re = 1 / 2 := by
  rcases liReflectedGammaCarrier_eq_zero_iff.mp hs with ⟨n, rfl⟩ | ⟨n, rfl⟩ <;> simp

theorem liReflectedGammaCarrier_one_sub (alpha : ℝ) (s : ℂ) :
    liReflectedGammaCarrier alpha (1 - s) = liReflectedGammaCarrier alpha s := by
  rw [liReflectedGammaCarrier, liReflectedGammaCarrier]
  convert reflectedGammaCarrier_neg alpha (s - (1 / 2 : ℂ)) using 1 <;> ring

theorem liReflectedGammaCarrier_conj (alpha : ℝ) (s : ℂ) :
    liReflectedGammaCarrier alpha (starRingEnd ℂ s) =
      starRingEnd ℂ (liReflectedGammaCarrier alpha s) := by
  rw [liReflectedGammaCarrier, liReflectedGammaCarrier]
  have harg : (starRingEnd ℂ) s - (1 / 2 : ℂ) =
      (starRingEnd ℂ) (s - (1 / 2 : ℂ)) := by
    rw [map_sub]
    congr 1
    simpa using (map_ratCast (starRingEnd ℂ) (1 / 2 : ℚ)).symm
  rw [harg, reflectedGammaCarrier_conj]

theorem liReflectedGammaCarrier_orderOneEnvelope (alpha : ℝ) :
    OrderOneEnvelope (liReflectedGammaCarrier alpha) := by
  have h := (reflectedGammaCarrier_orderOneEnvelope alpha).comp_affine
    1 (-(1 / 2 : ℂ))
  exact h.congr fun s => by
    simp only [liReflectedGammaCarrier]
    congr 1
    ring

theorem liReflectedGammaCarrier_ne_zero_half {alpha : ℝ} (halpha : 0 < alpha) :
    liReflectedGammaCarrier alpha (1 / 2 : ℂ) ≠ 0 := by
  simpa [liReflectedGammaCarrier] using reflectedGammaCarrier_ne_zero_zero halpha

theorem liReflectedGammaCarrier_zero_arithmeticProgression (alpha : ℝ) (n : ℕ) :
    liReflectedGammaCarrier alpha
      ((1 / 2 : ℂ) + I * (alpha : ℂ) + n • I) = 0 := by
  rw [liReflectedGammaCarrier_eq_zero_iff]
  left
  refine ⟨n, ?_⟩
  simp only [nsmul_eq_mul]
  ring

theorem liReflectedGammaCarrier_not_minimalExponentialType
    {alpha : ℝ} (halpha : 0 < alpha) :
    ¬ HasMinimalExponentialType (liReflectedGammaCarrier alpha) := by
  intro hmin
  exact hmin.no_arithmeticProgression_zeros
    (liReflectedGammaCarrier_ne_zero_half halpha) I_ne_zero
    (liReflectedGammaCarrier_zero_arithmeticProgression alpha)

theorem liReflectedGammaCarrier_hasExactEntireOrderOne
    {alpha : ℝ} (halpha : 0 < alpha) :
    HasExactEntireOrderOne (liReflectedGammaCarrier alpha) := by
  refine ⟨?_, liReflectedGammaCarrier_orderOneEnvelope alpha,
    liReflectedGammaCarrier_not_minimalExponentialType halpha⟩
  exact Complex.analyticOnNhd_univ_iff_differentiable.mp
    (liReflectedGammaCarrier_analyticOnNhd alpha)

theorem liReflectedGammaCarrier_hypertranscendental
    {alpha : ℝ} (hsep : ∀ k : ℤ, (2 * alpha : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (liReflectedGammaCarrier alpha) := by
  have h := (hypertranscendental_comp_add_const_iff
      (f := reflectedGammaCarrier alpha) (-(1 / 2 : ℂ))).2
      (reflectedGammaCarrier_hypertranscendental hsep)
  have heq : (fun z => reflectedGammaCarrier alpha (z + -(1 / 2 : ℂ))) =
      liReflectedGammaCarrier alpha := by
    funext z
    simp only [liReflectedGammaCarrier]
    congr 1
  rw [heq] at h
  exact h

private theorem reciprocalGammaEntire_ne_zero_of_pos_real
    {x : ℝ} (hx : 0 < x) : reciprocalGammaEntire (x : ℂ) ≠ 0 := by
  unfold reciprocalGammaEntire
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) m]

private theorem reflectedGammaCarrier_deriv_upper_ne_zero
    {alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) :
    deriv (reflectedGammaCarrier alpha)
      (I * ((n : ℂ) + (alpha : ℂ))) ≠ 0 := by
  let z0 : ℂ := I * ((n : ℂ) + (alpha : ℂ))
  let c : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  have huval : (alpha : ℂ) + I * z0 = -(n : ℂ) := by
    dsimp [z0]
    rw [← mul_assoc, I_mul_I]
    ring
  have hvval : (alpha : ℂ) - I * z0 = (n : ℂ) + 2 * (alpha : ℂ) := by
    dsimp [z0]
    rw [← mul_assoc, I_mul_I]
    ring
  have huinner : HasDerivAt (fun z : ℂ => (alpha : ℂ) + I * z) I z0 := by
    have hmul : HasDerivAt (fun z : ℂ => I * z) I z0 := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z0).const_mul I
    exact hmul.const_add (alpha : ℂ)
  have hvinner : HasDerivAt (fun z : ℂ => (alpha : ℂ) - I * z) (-I) z0 := by
    have hmul : HasDerivAt (fun z : ℂ => I * z) I z0 := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z0).const_mul I
    exact hmul.const_sub (alpha : ℂ)
  have hrecip : HasDerivAt reciprocalGammaEntire c (-(n : ℂ)) := by
    change HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) c (-(n : ℂ))
    simpa [c] using hasDerivAt_oneDivGamma_neg_nat n
  rw [← huval] at hrecip
  have hfirst := hrecip.comp z0 huinner
  have hsecondDiff : DifferentiableAt ℂ reciprocalGammaEntire
      ((alpha : ℂ) - I * z0) :=
    (contDiff_reciprocalGammaEntire.differentiable (by simp)) _
  have hsecond := hsecondDiff.hasDerivAt.comp z0 hvinner
  have hprod := hfirst.mul hsecond
  have hfun :
      ((reciprocalGammaEntire ∘ fun z : ℂ => (alpha : ℂ) + I * z) *
        (reciprocalGammaEntire ∘ fun z : ℂ => (alpha : ℂ) - I * z)) =
        reflectedGammaCarrier alpha := by
    funext z
    rfl
  rw [hfun] at hprod
  have hzero : reciprocalGammaEntire ((alpha : ℂ) + I * z0) = 0 := by
    rw [huval]
    unfold reciprocalGammaEntire
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
  have hderiv : deriv (reflectedGammaCarrier alpha) z0 =
      (c * I) * reciprocalGammaEntire ((alpha : ℂ) - I * z0) := by
    simpa only [Function.comp_apply, hzero, zero_mul, add_zero] using hprod.deriv
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)
  have hsecond0 : reciprocalGammaEntire ((alpha : ℂ) - I * z0) ≠ 0 := by
    rw [hvval]
    have h := reciprocalGammaEntire_ne_zero_of_pos_real
      (x := (n : ℝ) + 2 * alpha) (by positivity)
    convert h using 1 <;> push_cast <;> ring
  rw [hderiv]
  exact mul_ne_zero (mul_ne_zero hc I_ne_zero) hsecond0

theorem liReflectedGammaCarrier_deriv_upper_ne_zero
    {alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) :
    deriv (liReflectedGammaCarrier alpha)
      ((1 / 2 : ℂ) + I * ((n : ℂ) + (alpha : ℂ))) ≠ 0 := by
  let s0 : ℂ := (1 / 2 : ℂ) + I * ((n : ℂ) + (alpha : ℂ))
  have hval : s0 - (1 / 2 : ℂ) = I * ((n : ℂ) + (alpha : ℂ)) := by
    dsimp [s0]
    ring
  have hinner : HasDerivAt (fun s : ℂ => s - (1 / 2 : ℂ)) 1 s0 := by
    simpa only [id_eq] using (hasDerivAt_id s0).sub_const (1 / 2 : ℂ)
  have hout : DifferentiableAt ℂ (reflectedGammaCarrier alpha)
      (s0 - (1 / 2 : ℂ)) :=
    (reflectedGammaCarrier_analyticOnNhd alpha _ (Set.mem_univ _)).differentiableAt
  have hcomp := hout.hasDerivAt.comp s0 hinner
  have hfun : (reflectedGammaCarrier alpha ∘ fun s : ℂ => s - (1 / 2 : ℂ)) =
      liReflectedGammaCarrier alpha := by
    funext s
    rfl
  rw [hfun] at hcomp
  have hderiv : deriv (liReflectedGammaCarrier alpha)
      s0 =
        deriv (reflectedGammaCarrier alpha) (I * ((n : ℂ) + (alpha : ℂ))) := by
    simpa only [mul_one, hval] using hcomp.deriv
  change deriv (liReflectedGammaCarrier alpha) s0 ≠ 0
  rw [hderiv]
  exact reflectedGammaCarrier_deriv_upper_ne_zero halpha n

theorem liReflectedGammaCarrier_deriv_lower_ne_zero
    {alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) :
    deriv (liReflectedGammaCarrier alpha)
      ((1 / 2 : ℂ) - I * ((n : ℂ) + (alpha : ℂ))) ≠ 0 := by
  let sMinus : ℂ := (1 / 2 : ℂ) - I * ((n : ℂ) + (alpha : ℂ))
  let sPlus : ℂ := (1 / 2 : ℂ) + I * ((n : ℂ) + (alpha : ℂ))
  have hreflect : 1 - sMinus = sPlus := by
    dsimp [sMinus, sPlus]
    ring
  have hinner : HasDerivAt (fun s : ℂ => 1 - s) (-1) sMinus := by
    simpa only [id_eq] using (hasDerivAt_id sMinus).const_sub (1 : ℂ)
  have hout : DifferentiableAt ℂ (liReflectedGammaCarrier alpha) (1 - sMinus) :=
    (liReflectedGammaCarrier_analyticOnNhd alpha _ (Set.mem_univ _)).differentiableAt
  have hcomp := hout.hasDerivAt.comp sMinus hinner
  have hfun : (liReflectedGammaCarrier alpha ∘ fun s : ℂ => 1 - s) =
      liReflectedGammaCarrier alpha := by
    funext s
    exact liReflectedGammaCarrier_one_sub alpha s
  rw [hfun] at hcomp
  have hderiv : deriv (liReflectedGammaCarrier alpha) sMinus =
      -deriv (liReflectedGammaCarrier alpha) sPlus := by
    simpa only [hreflect, mul_neg, mul_one] using hcomp.deriv
  rw [hderiv, neg_ne_zero]
  exact liReflectedGammaCarrier_deriv_upper_ne_zero halpha n

/-- Every zero of the completed reflected-Gamma carrier is simple. -/
theorem liReflectedGammaCarrier_deriv_ne_zero_of_eq_zero
    {alpha : ℝ} (halpha : 0 < alpha) {s : ℂ}
    (hs : liReflectedGammaCarrier alpha s = 0) :
    deriv (liReflectedGammaCarrier alpha) s ≠ 0 := by
  rcases liReflectedGammaCarrier_eq_zero_iff.mp hs with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact liReflectedGammaCarrier_deriv_upper_ne_zero halpha n
  · exact liReflectedGammaCarrier_deriv_lower_ne_zero halpha n

end
end RHTower
