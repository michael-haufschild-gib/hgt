import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixMomentNeutralIndexAmplification
import GaloisForLFunctions.RHTower.XiHorizontalCollisionTwoPrimeCesaroCarrier
import GaloisForLFunctions.RHTower.GaussHodgePencilSourcing
import GaloisForLFunctions.RHTower.GaussHodgeCoherenceBudget

/-!
# Gamma-six amplification as a flowed two-prime source coefficient

This module fuses three previously separate carriers before scalarization:

* the Gauss--Hodge holomorphic scale flow;
* the coefficient-faithful Gamma-six moment-neutral amplifier;
* the fixed-prime `(2,3)` horizontal Cesaro clock.

Flow only one member of a line-reflected pair from `p` to `p * 6^m`.  The resulting literal
coefficient factors exactly as

`horizontalPrimePhase(p, Im rho) * burnolPrimeCharacter(6, rho)^m`.

Thus the two-prime phase still recovers the ordinate, while squared norm is exactly
`6^(m * (2 Re rho - 1))`.  After the Gamma-six critical multiplicity factor `5`, the two
reflected source masses are definitionally the existing forward and reflected complete-shell
traces.  Their product is `25`, equality at one complete shell is critical-line placement, and
subexponential growth for every Xi multiplicity copy is equivalent to RH.

This is an unconditional source-to-amplifier identification, not the missing producer.  The
remaining analytic gate is now explicit: bound this *bilinear reflected* flowed coefficient from
completed prime--Gamma data.  A one-variable flowed zero current controls its first factor but
does not by itself control the retained reflected factor.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Gamma-six holomorphic flow mode on one retained Xi multiplicity copy. -/
def sourceHorizontalGammaSixFlowMode (q : XiZeroCopy) : ℂ :=
  burnolPrimeCharacter 6 (q.1 : ℂ)

theorem norm_sourceHorizontalGammaSixFlowMode (q : XiZeroCopy) :
    ‖sourceHorizontalGammaSixFlowMode q‖ =
      (6 : ℝ) ^ (primeDepthBVWoldXiCenteredRate q.1 / 2) := by
  rw [sourceHorizontalGammaSixFlowMode,
    norm_burnolPrimeCharacter (by norm_num : (0 : ℝ) < 6)]
  congr 1
  rw [primeDepthBVWoldXiCenteredRate]
  ring

/-- Generalized FE scale-flow identity at the Gamma-six clock. -/
theorem burnolPrimeCharacter_mul_gammaSixFlow_pow
    {p : ℝ} (hp : 0 < p) (s : ℂ) (m : ℕ) :
    burnolPrimeCharacter p s * burnolPrimeCharacter 6 s ^ m =
      burnolPrimeCharacter (p * (6 : ℝ) ^ m) s := by
  have h6m : (0 : ℝ) < (6 : ℝ) ^ m := pow_pos (by norm_num) _
  have hprod : 0 < p * (6 : ℝ) ^ m := mul_pos hp h6m
  rw [burnolPrimeCharacter_eq_exp p hp,
    burnolPrimeCharacter_eq_exp 6 (by norm_num),
    burnolPrimeCharacter_eq_exp _ hprod,
    ← Complex.exp_nat_mul, ← Complex.exp_add,
    Real.log_mul hp.ne' h6m.ne', Real.log_pow]
  congr 1
  push_cast
  ring

/-- Flowed coefficient on one orientation, paired with the unchanged reflected prime character. -/
def sourceHorizontalGammaSixFlowedReflectedCoefficient
    (p : ℝ) (q : XiZeroCopy) (m : ℕ) : ℂ :=
  burnolPrimeCharacter (p * (6 : ℝ) ^ m) (q.1 : ℂ) *
    burnolPrimeCharacter p (lineReflect (q.1 : ℂ))

/-- Exact factorization into retained ordinate phase and Gamma-six horizontal flow. -/
theorem sourceHorizontalGammaSixFlowedReflectedCoefficient_eq_phase_mul_mode_pow
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) (m : ℕ) :
    sourceHorizontalGammaSixFlowedReflectedCoefficient p q m =
      HTGeometry.phaseClockValue (Real.log p) (2 * (q.1 : ℂ).im) *
        sourceHorizontalGammaSixFlowMode q ^ m := by
  rw [sourceHorizontalGammaSixFlowedReflectedCoefficient,
    sourceHorizontalGammaSixFlowMode,
    ← burnolPrimeCharacter_mul_gammaSixFlow_pow hp]
  rw [mul_assoc, mul_comm (burnolPrimeCharacter 6 (q.1 : ℂ) ^ m),
    ← mul_assoc,
    burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase hp]

/-- Prime phase is moment-neutral; squared norm is the complete horizontal growth signal. -/
theorem norm_sq_sourceHorizontalGammaSixFlowedReflectedCoefficient
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) (m : ℕ) :
    ‖sourceHorizontalGammaSixFlowedReflectedCoefficient p q m‖ ^ 2 =
      (6 : ℝ) ^ ((m : ℝ) * primeDepthBVWoldXiCenteredRate q.1) := by
  rw [sourceHorizontalGammaSixFlowedReflectedCoefficient_eq_phase_mul_mode_pow hp,
    norm_mul, HTGeometry.norm_phaseClockValue, one_mul, norm_pow,
    norm_sourceHorizontalGammaSixFlowMode, sq]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
  congr 1
  ring

/-- Squared flowed mass is exactly the conjugate-pair diagonal of the holomorphic squared
explicit-formula kernel at scale `6^m`.  This is the precise bilinear source landing. -/
theorem ofReal_norm_sq_sourceHorizontalGammaSixFlowedReflectedCoefficient_eq_conjugatePairKernel
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) (m : ℕ) :
    ((‖sourceHorizontalGammaSixFlowedReflectedCoefficient p q m‖ ^ 2 : ℝ) : ℂ) =
      burnolPrimeCharacter ((6 : ℝ) ^ m) (q.1 : ℂ) *
        burnolPrimeCharacter ((6 : ℝ) ^ m)
          (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ) := by
  have h6m : (0 : ℝ) < (6 : ℝ) ^ m := pow_pos (by norm_num) _
  rw [norm_sq_sourceHorizontalGammaSixFlowedReflectedCoefficient hp,
    hermitianSample_eq_conjugatePair_product h6m]
  congr 1
  rw [← Real.rpow_natCast (6 : ℝ) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  congr 1

theorem sourceHorizontalGammaSixFlowMode_ne_zero (q : XiZeroCopy) :
    sourceHorizontalGammaSixFlowMode q ≠ 0 := by
  rw [sourceHorizontalGammaSixFlowMode,
    burnolPrimeCharacter_eq_exp 6 (by norm_num)]
  exact Complex.exp_ne_zero _

/-- Divide out only the explicit common Gamma-six flow, leaving the original `(2,3)` clocks. -/
def sourceHorizontalGammaSixFlowedNormalizedPhasePair
    (q : XiZeroCopy) (m : ℕ) : ℂ × ℂ :=
  (sourceHorizontalGammaSixFlowedReflectedCoefficient 2 q m /
      sourceHorizontalGammaSixFlowMode q ^ m,
    sourceHorizontalGammaSixFlowedReflectedCoefficient 3 q m /
      sourceHorizontalGammaSixFlowMode q ^ m)

theorem sourceHorizontalGammaSixFlowedNormalizedPhasePair_eq
    (q : XiZeroCopy) (m : ℕ) :
    sourceHorizontalGammaSixFlowedNormalizedPhasePair q m =
      (xiHorizontalPrimePhase 2 (q.1 : ℂ).im,
        xiHorizontalPrimePhase 3 (q.1 : ℂ).im) := by
  rw [sourceHorizontalGammaSixFlowedNormalizedPhasePair,
    sourceHorizontalGammaSixFlowedReflectedCoefficient_eq_phase_mul_mode_pow
      (by norm_num),
    sourceHorizontalGammaSixFlowedReflectedCoefficient_eq_phase_mul_mode_pow
      (by norm_num)]
  have hpow : sourceHorizontalGammaSixFlowMode q ^ m ≠ 0 :=
    pow_ne_zero _ (sourceHorizontalGammaSixFlowMode_ne_zero q)
  ext <;> simp only [xiHorizontalPrimePhase] <;> field_simp <;> norm_num

/-- Flow does not erase ordinate separation supplied by the fixed labels `(2,3)`. -/
theorem sourceHorizontalGammaSixFlowedNormalizedPhasePair_ordinate_injective
    {q r : XiZeroCopy} {m n : ℕ}
    (h : sourceHorizontalGammaSixFlowedNormalizedPhasePair q m =
      sourceHorizontalGammaSixFlowedNormalizedPhasePair r n) :
    (q.1 : ℂ).im = (r.1 : ℂ).im := by
  rw [sourceHorizontalGammaSixFlowedNormalizedPhasePair_eq,
    sourceHorizontalGammaSixFlowedNormalizedPhasePair_eq] at h
  exact xiHorizontalPrimePhase_pair_injective h

/-- Critical Gamma-six multiplicity applied to one flowed orientation. -/
def sourceHorizontalGammaSixFlowedForwardShellMass
    (p : ℝ) (q : XiZeroCopy) (m : ℕ) : ℝ :=
  5 * ‖sourceHorizontalGammaSixFlowedReflectedCoefficient p q m‖ ^ 2

/-- The forward shell mass is five times the real conjugate-pair kernel diagonal. -/
theorem sourceHorizontalGammaSixFlowedForwardShellMass_eq_conjugatePairKernel_re
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) (m : ℕ) :
    sourceHorizontalGammaSixFlowedForwardShellMass p q m =
      5 * (burnolPrimeCharacter ((6 : ℝ) ^ m) (q.1 : ℂ) *
        burnolPrimeCharacter ((6 : ℝ) ^ m)
          (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ)).re := by
  rw [sourceHorizontalGammaSixFlowedForwardShellMass]
  have h := congrArg Complex.re
    (ofReal_norm_sq_sourceHorizontalGammaSixFlowedReflectedCoefficient_eq_conjugatePairKernel
      hp q m)
  have hreal : ‖sourceHorizontalGammaSixFlowedReflectedCoefficient p q m‖ ^ 2 =
      (burnolPrimeCharacter ((6 : ℝ) ^ m) (q.1 : ℂ) *
        burnolPrimeCharacter ((6 : ℝ) ^ m)
          (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ)).re := by
    change (((‖sourceHorizontalGammaSixFlowedReflectedCoefficient p q m‖ ^ 2 : ℝ) : ℂ)).re = _ at h
    rw [Complex.ofReal_re] at h
    exact h
  rw [hreal]

/-- Same source coefficient evaluated on the retained line-reflected orientation. -/
def sourceHorizontalGammaSixFlowedReflectedShellMass
    (p : ℝ) (q : XiZeroCopy) (m : ℕ) : ℝ :=
  5 * ‖sourceHorizontalGammaSixFlowedReflectedCoefficient p
    (xiZeroCopyLineConjEquiv q) m‖ ^ 2

/-- Flowed source mass is exactly the existing forward complete-shell trace. -/
theorem sourceHorizontalGammaSixFlowedForwardShellMass_eq
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) {m : ℕ} (hm : 3 ≤ m) :
    sourceHorizontalGammaSixFlowedForwardShellMass p q m =
      deningerGammaSixForwardShellTraceMass
        (primeDepthBVWoldXiCenteredRate q.1) m := by
  rw [sourceHorizontalGammaSixFlowedForwardShellMass,
    norm_sq_sourceHorizontalGammaSixFlowedReflectedCoefficient hp,
    deningerGammaSixForwardShellTraceMass_eq hm]

/-- Reflected flowed source mass is exactly the reciprocal complete-shell trace. -/
theorem sourceHorizontalGammaSixFlowedReflectedShellMass_eq
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) {m : ℕ} (hm : 3 ≤ m) :
    sourceHorizontalGammaSixFlowedReflectedShellMass p q m =
      deningerGammaSixReflectedShellTraceMass
        (primeDepthBVWoldXiCenteredRate q.1) m := by
  rw [sourceHorizontalGammaSixFlowedReflectedShellMass,
    norm_sq_sourceHorizontalGammaSixFlowedReflectedCoefficient hp,
    deningerGammaSixReflectedShellTraceMass_eq hm]
  rw [show primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
    -primeDepthBVWoldXiCenteredRate q.1 by
      exact primeDepthBVWoldXiCenteredRate_reflection q.1]
  congr 1
  ring_nf

/-- Moment neutrality survives source identification: opposite shell masses multiply to `25`. -/
theorem sourceHorizontalGammaSixFlowedShellMass_product
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) {m : ℕ} (hm : 3 ≤ m) :
    sourceHorizontalGammaSixFlowedForwardShellMass p q m *
      sourceHorizontalGammaSixFlowedReflectedShellMass p q m = 25 := by
  rw [sourceHorizontalGammaSixFlowedForwardShellMass_eq hp q hm,
    sourceHorizontalGammaSixFlowedReflectedShellMass_eq hp q hm,
    deningerGammaSixShellTraceMass_mul_reflected hm]

/-- Equality of the two literal flowed source orientations at one shell detects the line. -/
theorem sourceHorizontalGammaSixFlowedShellMass_eq_iff
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) {m : ℕ} (hm : 3 ≤ m) :
    sourceHorizontalGammaSixFlowedForwardShellMass p q m =
        sourceHorizontalGammaSixFlowedReflectedShellMass p q m ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalGammaSixFlowedForwardShellMass_eq hp q hm,
    sourceHorizontalGammaSixFlowedReflectedShellMass_eq hp q hm,
    deningerGammaSixForwardShellTraceMass_eq_reflected_iff hm,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Unoriented source trace before either reflection orientation is discarded. -/
def sourceHorizontalGammaSixFlowedTwoOrientationShellMass
    (p : ℝ) (q : XiZeroCopy) (m : ℕ) : ℝ :=
  max (sourceHorizontalGammaSixFlowedForwardShellMass p q m)
    (sourceHorizontalGammaSixFlowedReflectedShellMass p q m)

theorem sourceHorizontalGammaSixFlowedTwoOrientationShellMass_eq
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) {m : ℕ} (hm : 3 ≤ m) :
    sourceHorizontalGammaSixFlowedTwoOrientationShellMass p q m =
      deningerGammaSixTwoOrientationShellTraceMass
        (primeDepthBVWoldXiCenteredRate q.1) m := by
  rw [sourceHorizontalGammaSixFlowedTwoOrientationShellMass,
    deningerGammaSixTwoOrientationShellTraceMass,
    sourceHorizontalGammaSixFlowedForwardShellMass_eq hp q hm,
    sourceHorizontalGammaSixFlowedReflectedShellMass_eq hp q hm]

/-- Exact analytic producer condition on the flowed bilinear source coefficient. -/
def SourceHorizontalGammaSixFlowedTraceSubexponential
    (p : ℝ) (q : XiZeroCopy) : Prop :=
  ∀ r : ℝ, 1 < r →
    Tendsto
      (fun m : ℕ =>
        sourceHorizontalGammaSixFlowedTwoOrientationShellMass p q m / r ^ m)
      atTop (nhds 0)

/-- Source-flow trace condition at any positive label is precisely line placement. -/
theorem sourceHorizontalGammaSixFlowedTraceSubexponential_iff
    {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    SourceHorizontalGammaSixFlowedTraceSubexponential p q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have heq (r : ℝ) :
      (fun m : ℕ =>
          sourceHorizontalGammaSixFlowedTwoOrientationShellMass p q m / r ^ m) =ᶠ[atTop]
        (fun m : ℕ => deningerGammaSixTwoOrientationShellTraceMass
          (primeDepthBVWoldXiCenteredRate q.1) m / r ^ m) := by
    filter_upwards [eventually_ge_atTop 3] with m hm
    rw [sourceHorizontalGammaSixFlowedTwoOrientationShellMass_eq hp q hm]
  rw [← deningerXiGammaSixMomentNeutralTraceSubexponential_iff q]
  constructor
  · intro h r hr
    exact Tendsto.congr' (heq r) (h r hr)
  · intro h r hr
    exact Tendsto.congr' (heq r).symm (h r hr)

/-- Global flowed-source trace condition on every retained Xi multiplicity copy. -/
def SourceHorizontalGammaSixAllFlowedTracesSubexponential : Prop :=
  ∀ q : XiZeroCopy,
    SourceHorizontalGammaSixFlowedTraceSubexponential 2 q

/-- Frankenstein endpoint: the explicit flowed two-prime/Gamma-six source trace closes RH iff
its still-missing bilinear source estimate proves subexponential growth. -/
theorem sourceHorizontalGammaSixAllFlowedTracesSubexponential_iff_riemannHypothesis :
    SourceHorizontalGammaSixAllFlowedTracesSubexponential ↔ RiemannHypothesis := by
  rw [← deningerXiGammaSixAllMomentNeutralTracesSubexponential_iff_riemannHypothesis]
  unfold SourceHorizontalGammaSixAllFlowedTracesSubexponential
    DeningerXiGammaSixAllMomentNeutralTracesSubexponential
  refine forall_congr' fun q => ?_
  rw [sourceHorizontalGammaSixFlowedTraceSubexponential_iff (by norm_num),
    deningerXiGammaSixMomentNeutralTraceSubexponential_iff]

end

end RHTower
