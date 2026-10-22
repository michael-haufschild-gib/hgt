import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTotalRenormalizedAngularPeriod
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGaugeFixedCausalQNMCokernel

/-!
# Total-period incidence at the Birmingham--Mokhtari QNM pole

The renormalized Einstein--Teukolsky angular period is inserted into the exact causal BM frequency
response.  Its temporal denominator is regular at every negative-branch target, while the physical
boundary Jost determinant has a simple zero with nonzero derivative.  The positive optical part of
the period therefore gives a nonzero Laurent residue and a nonzero nonlinear pole velocity for
every nonzero theta seed.

Functional-equation reflection and Schwarz conjugation yield two incident partner poles.  Their
frequency separation is

`-I * (Re rho - 1/2)`.

Consequently an off-line divisor cannot be erased by the total angular numerator or by an
intermediate-response collision: it produces a resolved two-pole sector.  This is the alternative
to an RH-selecting nonlinear boundary law.  Causal decay alone does not exclude the doublet.

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- Exact causal BM response with the total renormalized angular period as its cokernel numerator. -/
def d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
    (n k : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) (omega : ℂ) : ℂ :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  (Complex.I /
      (omega - d4BMCausalPlusPlusMinusFrequency n k chi)) *
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
      conservativeFinitePart amplitude orthogonalMixing q /
    d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q)

/-- Laurent coefficient at a negative-branch BM QNM after causal convolution. -/
def d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  let chi := d4BMXiMixedHorizonAngularMomentum q
  let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
  (Complex.I /
      (target - d4BMCausalPlusPlusMinusFrequency n k chi)) *
    d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
      conservativeFinitePart amplitude orthogonalMixing q /
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus N (xiSpectralPoint q)

/-- Nonzero theta data excite every negative-branch BM descendant through the total period. -/
theorem d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus_ne_zero
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
      n k N conservativeFinitePart amplitude orthogonalMixing q ≠ 0 := by
  have htarget :
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) =
        d4BMCausalQNMMinus N (d4BMXiMixedHorizonAngularMomentum q) :=
    (d4BMXiCausalQNMMinus_eq_topologicalBlackHoleQNMMinus N q).symm
  have hfreq :
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q) -
        d4BMCausalPlusPlusMinusFrequency n k
          (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
    rw [htarget]
    exact sub_ne_zero.mpr
      (d4BMCausalPlusPlusMinusFrequency_ne_qnmMinus_of_re_ne_zero n k N _
        (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)).symm
  unfold d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
  exact div_ne_zero
    (mul_ne_zero (div_ne_zero Complex.I_ne_zero hfreq)
      (d4BMXiGaugeFixedTotalRenormalizedAngularPeriod_ne_zero
        conservativeFinitePart ha orthogonalMixing q))
    (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero N q)

/-- Negative-branch partner clocks carry the opposite orientation of the plus-branch tilt. -/
theorem d4BMXiReflected_sub_conjugateQNMMinus_eq_neg_tilt
    (N : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMMinus N
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) -
        thetaCuspHawkingTopologicalBlackHoleQNMMinus N
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      -Complex.I * ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) := by
  rw [xiSpectralPoint_reflect, xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay, xiSpectralPoint]
  push_cast
  apply Complex.ext
  · simp
  · simp
    ring

/-- Reflected and Schwarz-conjugated negative-branch poles coalesce exactly on the critical line. -/
theorem d4BMXiReflectedQNMMinus_eq_conjugateQNMMinus_iff
    (N : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMMinus N
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
        thetaCuspHawkingTopologicalBlackHoleQNMMinus N
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hsub :
        thetaCuspHawkingTopologicalBlackHoleQNMMinus N
              (xiSpectralPoint (xiZeroCopyReflectEquiv q)) -
            thetaCuspHawkingTopologicalBlackHoleQNMMinus N
              (xiSpectralPoint (xiZeroCopyConjEquiv q)) = 0 := sub_eq_zero.mpr h
    rw [d4BMXiReflected_sub_conjugateQNMMinus_eq_neg_tilt] at hsub
    have him := congrArg Complex.im hsub
    simp at him
    linarith
  · intro hline
    apply sub_eq_zero.mp
    rw [d4BMXiReflected_sub_conjugateQNMMinus_eq_neg_tilt, hline]
    norm_num

/-- The total-period response has the displayed genuine simple-pole residue. -/
theorem d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus_tendsto_residue
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)) *
          d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
            n k conservativeFinitePart amplitude orthogonalMixing q omega)
      (nhdsWithin
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q))
        {thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)}ᶜ)
      (nhds (d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
        n k N conservativeFinitePart amplitude orthogonalMixing q)) := by
  let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
  let source := d4BMCausalPlusPlusMinusFrequency n k
    (d4BMXiMixedHorizonAngularMomentum q)
  let D : ℂ → ℂ := fun omega =>
    d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q)
  let Num : ℂ → ℂ := fun omega =>
    (Complex.I / (omega - source)) *
      d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q
  have htarget : target =
      d4BMCausalQNMMinus N (d4BMXiMixedHorizonAngularMomentum q) := by
    exact (d4BMXiCausalQNMMinus_eq_topologicalBlackHoleQNMMinus N q).symm
  have hfreq : target - source ≠ 0 := by
    rw [htarget]
    exact sub_ne_zero.mpr
      (d4BMCausalPlusPlusMinusFrequency_ne_qnmMinus_of_re_ne_zero n k N _
        (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)).symm
  have hD : HasDerivAt D
      (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus N (xiSpectralPoint q))
      target := by
    simpa [D, target] using
      d4FundamentalQNMCrossBranchBoundaryJost_hasDerivAt_qnmMinus_xi N q
  have hD0 : D target = 0 := by
    simp [D, target, d4GravitationalHypergeometricBoundaryJost,
      thetaCuspHawkingHypergeometricPhysicalBoundaryJost,
      thetaCuspHawkingHypergeometricJost,
      thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  have hNum : ContinuousAt Num target := by
    dsimp [Num]
    fun_prop
  have hlim := tendsto_residue_of_simple_zero hD hD0
    (d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero N q)
    hNum
  simpa [target, source, D, Num,
    d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus,
    d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus] using hlim

/-- Nonzero residue makes the BM target a nonremovable pole of the total-period response. -/
theorem d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus_not_continuousAt
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    ¬ ContinuousAt
      (d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
        n k conservativeFinitePart amplitude orthogonalMixing q)
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)) := by
  intro hcont
  let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
  let F := nhdsWithin target {target}ᶜ
  have hfactor : Tendsto (fun omega : ℂ => omega - target) F (nhds 0) := by
    have hid : Tendsto (fun omega : ℂ => omega) F (nhds target) :=
      tendsto_id.mono_left inf_le_left
    have hconst : Tendsto (fun _ : ℂ => target) F (nhds target) :=
      tendsto_const_nhds
    simpa using hid.sub hconst
  have hresponse : Tendsto
      (d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
        n k conservativeFinitePart amplitude orthogonalMixing q)
      F
      (nhds (d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
        n k conservativeFinitePart amplitude orthogonalMixing q target)) :=
    hcont.tendsto.mono_left inf_le_left
  have hzero : Tendsto
      (fun omega : ℂ => (omega - target) *
        d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
          n k conservativeFinitePart amplitude orthogonalMixing q omega)
      F (nhds 0) := by
    simpa using hfactor.mul hresponse
  have hres : Tendsto
      (fun omega : ℂ => (omega - target) *
        d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus
          n k conservativeFinitePart amplitude orthogonalMixing q omega)
      F
      (nhds (d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
        n k N conservativeFinitePart amplitude orthogonalMixing q)) := by
    simpa [target, F] using
      d4BMXiGaugeFixedTotalPeriodFrequencyResponseMinus_tendsto_residue
        n k N conservativeFinitePart amplitude orthogonalMixing q
  have heq :
      d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
        n k N conservativeFinitePart amplitude orthogonalMixing q = 0 :=
    tendsto_nhds_unique hres hzero
  exact (d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus_ne_zero
    n k N conservativeFinitePart ha orthogonalMixing q) heq

/-- First nonlinear velocity of the simple BM pole under the total retarded cokernel source. -/
def d4BMXiGaugeFixedTotalPeriodPoleVelocityMinus
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  -d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
    n k N conservativeFinitePart amplitude orthogonalMixing q

/-- Fredholm identity determining the pole velocity from the complete causal angular numerator. -/
theorem d4BMXiGaugeFixedTotalPeriodTargetNumerator_eq_neg_velocity_mul_jostDerivative
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    let chi := d4BMXiMixedHorizonAngularMomentum q
    let target := thetaCuspHawkingTopologicalBlackHoleQNMMinus N (xiSpectralPoint q)
    (Complex.I /
        (target - d4BMCausalPlusPlusMinusFrequency n k chi)) *
      d4BMXiGaugeFixedTotalRenormalizedAngularPeriod
        conservativeFinitePart amplitude orthogonalMixing q =
      -d4BMXiGaugeFixedTotalPeriodPoleVelocityMinus
          n k N conservativeFinitePart amplitude orthogonalMixing q *
        d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus
          N (xiSpectralPoint q) := by
  dsimp only
  rw [d4BMXiGaugeFixedTotalPeriodPoleVelocityMinus,
    d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus]
  have hD :=
    d4FundamentalQNMCrossBranchBoundaryJostDerivativeMinus_xi_ne_zero N q
  field_simp

theorem d4BMXiGaugeFixedTotalPeriodPoleVelocityMinus_ne_zero
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ)
    (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalPeriodPoleVelocityMinus
      n k N conservativeFinitePart amplitude orthogonalMixing q ≠ 0 := by
  exact neg_ne_zero.mpr
    (d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus_ne_zero
      n k N conservativeFinitePart ha orthogonalMixing q)

/-- Off-line theta data force two bright, frequency-resolved FE--Schwarz partner poles. -/
theorem d4BMXiGaugeFixedTotalPeriodPartnerPoleDoublet
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (conjugateMixing reflectedMixing : ℂ) (q : XiZeroCopy) :
    d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
          n k N conservativeFinitePart amplitude conjugateMixing
          (xiZeroCopyConjEquiv q) ≠ 0 ∧
      d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus
          n k N conservativeFinitePart amplitude reflectedMixing
          (xiZeroCopyReflectEquiv q) ≠ 0 ∧
      ((q.1 : ℂ).re ≠ 1 / 2 →
        thetaCuspHawkingTopologicalBlackHoleQNMMinus N
            (xiSpectralPoint (xiZeroCopyReflectEquiv q)) ≠
          thetaCuspHawkingTopologicalBlackHoleQNMMinus N
            (xiSpectralPoint (xiZeroCopyConjEquiv q))) := by
  refine
    ⟨d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus_ne_zero
        n k N conservativeFinitePart ha conjugateMixing _,
      d4BMXiGaugeFixedTotalPeriodQNMCokernelResidueMinus_ne_zero
        n k N conservativeFinitePart ha reflectedMixing _, ?_⟩
  exact fun hoff hfreq =>
    hoff ((d4BMXiReflectedQNMMinus_eq_conjugateQNMMinus_iff N q).mp hfreq)

end

end RHTower
