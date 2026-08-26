import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTotalThirdOrderCokernelSchurSection

/-!
# Gauge-fixed BM causal convolution and QNM cokernel

For causal BM seeds `p_n` and `m_k`, multiplication by either seed shifts the Laplace frequency of
the corresponding quadratic response. Both shifted quadratic denominators and the direct cubic
denominator equal `omega - Omega_{++-}`. Consequently the complete convolved Einstein--Teukolsky
source is one Cauchy multiplier times the total cubic Schur source.

At a negative-branch BM QNM, the full boundary Jost function has a simple zero. If the convolved
angular cokernel numerator is regular there, its Laurent residue is the total target-shifted Schur
section divided by the common causal detuning and the exact Jost derivative. Both divisors are
nonzero on every Xi fibre, so QNM excitation vanishes exactly when the total angular cokernel does.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- Laplace transform multiplier of `1_{t >= 0} exp(-I source t)` at `target`. -/
def d4BMCausalRetardedTurnOnMultiplier (target source : ℂ) : ℂ :=
  Complex.I / (target - source)

theorem d4BMCausalRetardedTurnOnMultiplier_ne_zero
    {target source : ℂ} (h : target ≠ source) :
    d4BMCausalRetardedTurnOnMultiplier target source ≠ 0 := by
  exact div_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr h)

/-- Exact detuning of a negative-branch BM QNM from a local `++-` source. -/
theorem d4BMCausalQNMMinus_sub_plusPlusMinusFrequency
    (n k N : ℕ) (chi : ℂ) :
    d4BMCausalQNMMinus N chi -
        d4BMCausalPlusPlusMinusFrequency n k chi =
      -2 * chi + Complex.I *
        (4 * (n : ℂ) + 2 * (k : ℂ) - 2 * (N : ℂ) + 3) := by
  simp [d4BMCausalQNMMinus, d4BMCausalPlusPlusMinusFrequency,
    d4BMCausalQNMPlus, d4BMCausalDecay]
  ring

/-- Xi-specialized causal multiplier at the negative-branch target QNM. -/
def d4BMXiCausalRetardedTurnOnMultiplierMinus
    (n k N : ℕ) (q : XiZeroCopy) : ℂ :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  d4BMCausalRetardedTurnOnMultiplier
    (d4BMCausalQNMMinus N chi)
    (d4BMCausalPlusPlusMinusFrequency n k chi)

theorem d4BMXiCausalRetardedTurnOnMultiplierMinus_ne_zero
    (n k N : ℕ) (q : XiZeroCopy) :
    d4BMXiCausalRetardedTurnOnMultiplierMinus n k N q ≠ 0 := by
  apply d4BMCausalRetardedTurnOnMultiplier_ne_zero
  exact (d4BMCausalPlusPlusMinusFrequency_ne_qnmMinus_of_re_ne_zero n k N _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)).symm

/-- Multiplying a mixed quadratic response by `p_n` shifts its denominator to the cubic one. -/
theorem d4BMCausal_shiftedPlusMinusDenominator
    (target chi : ℂ) (n k : ℕ) :
    (target - d4BMCausalQNMPlus n chi) -
        d4BMCausalPlusMinusFrequency n k chi =
      target - d4BMCausalPlusPlusMinusFrequency n k chi := by
  simp [d4BMCausalPlusMinusFrequency, d4BMCausalPlusPlusMinusFrequency]
  ring

/-- Multiplying a second-harmonic response by `m_k` shifts its denominator to the cubic one. -/
theorem d4BMCausal_shiftedPlusPlusDenominator
    (target chi : ℂ) (n k : ℕ) :
    (target - d4BMCausalQNMMinus k chi) -
        d4BMCausalPlusPlusFrequency n chi =
      target - d4BMCausalPlusPlusMinusFrequency n k chi := by
  simp [d4BMCausalPlusPlusFrequency, d4BMCausalPlusPlusMinusFrequency]
  ring

/-- The causal normal form agrees with the full BM negative-branch QNM normalization. -/
theorem d4BMXiCausalQNMMinus_eq_topologicalBlackHoleQNMMinus
    (N : ℕ) (q : XiZeroCopy) :
    d4BMCausalQNMMinus N (d4BMXiMixedHorizonAngularMomentum q) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) := by
  simp [d4BMCausalQNMMinus, d4BMXiMixedHorizonAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus, d4BMCausalDecay,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay]

/-- Complete causal convolution at one output frequency. The supplied response maps are evaluated
at the two shifted quadratic frequencies. -/
def d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSourceAt
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : Y →ₗ[ℂ] X) (p m : X)
    (target chi : ℂ) (n k : ℕ) : Y :=
  B p ((Complex.I /
      ((target - d4BMCausalQNMPlus n chi) -
        d4BMCausalPlusMinusFrequency n k chi)) •
      d4GaugeFixedTeukolskyRetardedPlusMinusResponse B Rpm p m) +
    B m ((Complex.I /
      ((target - d4BMCausalQNMMinus k chi) -
        d4BMCausalPlusPlusFrequency n chi)) •
      d4GaugeFixedTeukolskyRetardedPlusPlusResponse B Rpp p) +
    (Complex.I /
      (target - d4BMCausalPlusPlusMinusFrequency n k chi)) •
      d4GaugeFixedTeukolskyDirectPlusPlusMinusResidual C p m

/-- The three causal histories combine into one multiplier times the total Schur source. -/
theorem d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSourceAt_eq_schurSource
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : Y →ₗ[ℂ] X) (p m : X)
    (target chi : ℂ) (n k : ℕ) :
    d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSourceAt
        B C Rpp Rpm p m target chi n k =
      (Complex.I /
        (target - d4BMCausalPlusPlusMinusFrequency n k chi)) •
        d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource B C Rpp Rpm p m := by
  rw [d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSourceAt,
    d4BMCausal_shiftedPlusMinusDenominator,
    d4BMCausal_shiftedPlusPlusDenominator]
  simp only [map_smul]
  rw [d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource]
  module

/-- Complete convolved source with frequency-dependent augmented quadratic response maps. -/
def d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSource
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (chi omega : ℂ) (n k : ℕ) : Y :=
  d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSourceAt B C
    (Rpp (omega - d4BMCausalQNMMinus k chi))
    (Rpm (omega - d4BMCausalQNMPlus n chi))
    p m omega chi n k

theorem d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSource_eq_schurSource
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (chi omega : ℂ) (n k : ℕ) :
    d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSource
        B C Rpp Rpm p m chi omega n k =
      (Complex.I /
        (omega - d4BMCausalPlusPlusMinusFrequency n k chi)) •
        d4GaugeFixedTeukolskyTotalPlusPlusMinusSchurSource B C
          (Rpp (omega - d4BMCausalQNMMinus k chi))
          (Rpm (omega - d4BMCausalQNMPlus n chi)) p m := by
  exact d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSourceAt_eq_schurSource
    B C _ _ p m omega chi n k

/-- Adjoint angular Green projection of the complete convolved source. -/
def d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (chi omega : ℂ) (n k : ℕ) : ℂ :=
  ell (d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSource
    B C Rpp Rpm p m chi omega n k)

/-- The projected causal convolution retains only the total target-shifted Schur section. -/
theorem d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator_eq_totalSection
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (chi omega : ℂ) (n k : ℕ) :
    d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator
        ell B C Rpp Rpm p m chi omega n k =
      (Complex.I /
        (omega - d4BMCausalPlusPlusMinusFrequency n k chi)) *
        d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection ell B C
          (Rpp (omega - d4BMCausalQNMMinus k chi))
          (Rpm (omega - d4BMCausalQNMPlus n chi)) p m := by
  rw [d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator,
    d4BMGaugeFixedEinsteinTeukolskyCausalConvolvedSource_eq_schurSource,
    map_smul]
  rfl

/-- Full frequency response obtained by dividing the total angular numerator by the physical BM
boundary Jost determinant. -/
def d4BMGaugeFixedEinsteinTeukolskyTotalFrequencyResponse
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (chi z omega : ℂ) (n k : ℕ) : ℂ :=
  d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator
      ell B C Rpp Rpm p m chi omega n k /
    d4GravitationalHypergeometricBoundaryJost omega z

/-- Exact Laurent coefficient of the full target-shifted `++-` source at a negative BM QNM. -/
def d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (n k N : ℕ) (q : XiZeroCopy) : ℂ :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
  (Complex.I /
      (target - d4BMCausalPlusPlusMinusFrequency n k chi)) *
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection ell B C
      (Rpp (target - d4BMCausalQNMMinus k chi))
      (Rpm (target - d4BMCausalQNMPlus n chi)) p m /
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus N (xiSpectralPoint q)

/-- A regular complete causal numerator has the preceding coefficient as its genuine simple-pole
residue. Regularity excludes an additional intermediate-response pole at the final target. -/
theorem d4BMGaugeFixedEinsteinTeukolskyTotalFrequencyResponse_tendsto_residueMinus
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (n k N : ℕ) (q : XiZeroCopy)
    (hregular : ContinuousAt
      (fun omega => d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator
        ell B C Rpp Rpm p m (d4BMXiMixedHorizonAngularMomentum q) omega n k)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q))) :
    Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)) *
          d4BMGaugeFixedEinsteinTeukolskyTotalFrequencyResponse
            ell B C Rpp Rpm p m (d4BMXiMixedHorizonAngularMomentum q)
              (xiSpectralPoint q) omega n k)
      (nhdsWithin
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q))
        {thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)}ᶜ)
      (nhds (d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus
        ell B C Rpp Rpm p m n k N q)) := by
  let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
  let D : ℂ → ℂ := fun omega =>
    d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q)
  let Num : ℂ → ℂ := fun omega =>
    d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator
      ell B C Rpp Rpm p m (d4BMXiMixedHorizonAngularMomentum q) omega n k
  have hD : HasDerivAt D
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus N (xiSpectralPoint q)) target := by
    simpa [D, target] using
      d4FundamentalQNMCrossBranchBoundaryJost_hasDerivAt_qnmMinus_xi N q
  have hD0 : D target = 0 := by
    simp [D, target, d4GravitationalHypergeometricBoundaryJost,
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost,
      thetaCuspHawkingHypergeometricJost,
      thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hlim := tendsto_residue_of_simple_zero hD hD0
    (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero N q)
    (by simpa [Num, target] using hregular)
  simpa [target, D, Num, d4BMGaugeFixedEinsteinTeukolskyTotalFrequencyResponse,
    d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus,
    d4BMGaugeFixedEinsteinTeukolskyAngularCokernelNumerator_eq_totalSection]
    using hlim

/-- Temporal detuning and the simple BM Jost pole neither create nor erase a total angular
cokernel. -/
theorem d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus_eq_zero_iff
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (n k N : ℕ) (q : XiZeroCopy) :
    d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus
        ell B C Rpp Rpm p m n k N q = 0 ↔
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection ell B C
        (Rpp (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) -
          d4BMCausalQNMMinus k (d4BMXiMixedHorizonAngularMomentum q)))
        (Rpm (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) -
          d4BMCausalQNMPlus n (d4BMXiMixedHorizonAngularMomentum q))) p m = 0 := by
  have htarget :
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) =
        d4BMCausalQNMMinus N (d4BMXiMixedHorizonAngularMomentum q) :=
    (d4BMXiCausalQNMMinus_eq_topologicalBlackHoleQNMMinus N q).symm
  have hfreq :
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) -
        d4BMCausalPlusPlusMinusFrequency n k (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
    rw [htarget]
    exact sub_ne_zero.mpr
      (d4BMCausalPlusPlusMinusFrequency_ne_qnmMinus_of_re_ne_zero n k N _
        (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)).symm
  have hmult :
      Complex.I /
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) -
          d4BMCausalPlusPlusMinusFrequency n k (d4BMXiMixedHorizonAngularMomentum q)) ≠ 0 :=
    div_ne_zero Complex.I_ne_zero hfreq
  simp [d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus, hmult,
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero]

/-- QNM time-domain coefficient for the inverse-Laplace convention with contour factor `-I`. -/
def d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMExcitationMinus
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (n k N : ℕ) (q : XiZeroCopy) : ℂ :=
  -Complex.I *
    d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus
      ell B C Rpp Rpm p m n k N q

theorem d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMExcitationMinus_eq
    {X Y : Type*}
    [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ell : Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (C : X →ₗ[ℂ] X →ₗ[ℂ] X →ₗ[ℂ] Y)
    (Rpp Rpm : ℂ → Y →ₗ[ℂ] X) (p m : X)
    (n k N : ℕ) (q : XiZeroCopy) :
    let chi := d4BMXiMixedHorizonAngularMomentum q
    let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
    d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMExcitationMinus
        ell B C Rpp Rpm p m n k N q =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection ell B C
        (Rpp (target - d4BMCausalQNMMinus k chi))
        (Rpm (target - d4BMCausalQNMPlus n chi)) p m /
        ((target - d4BMCausalPlusPlusMinusFrequency n k chi) *
          d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus N (xiSpectralPoint q)) := by
  dsimp only
  rw [d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMExcitationMinus,
    d4BMXiGaugeFixedEinsteinTeukolskyTotalQNMCokernelResidueMinus]
  simp only [div_eq_mul_inv]
  rw [mul_inv_rev]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end RHTower
