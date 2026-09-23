import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAnalyticBackreactionDoubletStability
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy

open Complex Set Filter Topology

namespace RHTower

noncomputable section

universe u

/-- Difference of the reflected and conjugated nonlinear pole branches. -/
def d4BMXiGaugeFixedPartnerPoleSeparation
    (reflectedPole conjugatePole : ℂ → ℂ) (coupling : ℂ) : ℂ :=
  reflectedPole coupling - conjugatePole coupling

/-- Squared pole separation, invariant under exchange of the two branches. -/
def d4BMXiGaugeFixedPartnerPoleDiscriminant
    (reflectedPole conjugatePole : ℂ → ℂ) (coupling : ℂ) : ℂ :=
  d4BMXiGaugeFixedPartnerPoleSeparation
      reflectedPole conjugatePole coupling ^ (2 : ℕ)

/-- An injective full radiation record cannot collapse an off-line FE--Schwarz partner pair. -/
theorem d4BMXiOffLinePartnerRadiation_ne_of_injective
    {Radiation : Type u} (radiationMap : XiZeroCopy → Radiation)
    (hinjective : Function.Injective radiationMap) (N : ℕ) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    radiationMap (xiZeroCopyReflectEquiv q) ≠
      radiationMap (xiZeroCopyConjEquiv q) := by
  intro hcollapse
  have hcopy : xiZeroCopyReflectEquiv q = xiZeroCopyConjEquiv q :=
    hinjective hcollapse
  apply hoff
  apply (d4BMXiReflectedQNMMinus_eq_conjugateQNMMinus_iff N q).mp
  rw [hcopy]

/-- Collapsing an off-line FE--Schwarz pair forces information loss in the radiation map. -/
theorem d4BMXiOffLinePartnerRadiationCollapse_not_injective
    {Radiation : Type u} (radiationMap : XiZeroCopy → Radiation)
    (N : ℕ) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hcollapse : radiationMap (xiZeroCopyReflectEquiv q) =
      radiationMap (xiZeroCopyConjEquiv q)) :
    ¬Function.Injective radiationMap := by
  intro hinjective
  exact d4BMXiOffLinePartnerRadiation_ne_of_injective
    radiationMap hinjective N q hoff hcollapse

theorem d4BMXiGaugeFixedPartnerPoleDiscriminant_hasDerivAt
    {reflectedPole conjugatePole : ℂ → ℂ}
    {reflectedTarget conjugateTarget reflectedVelocity conjugateVelocity : ℂ}
    (hreflected : HasDerivAt reflectedPole reflectedVelocity 0)
    (hconjugate : HasDerivAt conjugatePole conjugateVelocity 0)
    (hreflected0 : reflectedPole 0 = reflectedTarget)
    (hconjugate0 : conjugatePole 0 = conjugateTarget) :
    HasDerivAt
      (d4BMXiGaugeFixedPartnerPoleDiscriminant reflectedPole conjugatePole)
      (2 * (reflectedTarget - conjugateTarget) *
        (reflectedVelocity - conjugateVelocity)) 0 := by
  unfold d4BMXiGaugeFixedPartnerPoleDiscriminant
    d4BMXiGaugeFixedPartnerPoleSeparation
  have hseparation : HasDerivAt
      (fun coupling => reflectedPole coupling - conjugatePole coupling)
      (reflectedVelocity - conjugateVelocity) 0 :=
    hreflected.sub hconjugate
  convert hseparation.pow 2 using 1 <;> try rfl
  rw [hreflected0, hconjugate0]
  ring

/-- First variation of the BM partner discriminant. Its tilt factor is fixed, while its
velocity-difference factor is not constrained by optical positivity. -/
theorem d4BMXiGaugeFixedPartnerPoleDiscriminant_hasDerivAt_eq_tilt
    {reflectedPole conjugatePole : ℂ → ℂ}
    {reflectedVelocity conjugateVelocity : ℂ}
    (N : ℕ) (q : XiZeroCopy)
    (hreflected : HasDerivAt reflectedPole reflectedVelocity 0)
    (hconjugate : HasDerivAt conjugatePole conjugateVelocity 0)
    (hreflected0 : reflectedPole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
    (hconjugate0 : conjugatePole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyConjEquiv q))) :
    HasDerivAt
      (d4BMXiGaugeFixedPartnerPoleDiscriminant reflectedPole conjugatePole)
      (2 * (-Complex.I * ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ))) *
        (reflectedVelocity - conjugateVelocity)) 0 := by
  convert d4BMXiGaugeFixedPartnerPoleDiscriminant_hasDerivAt
    hreflected hconjugate hreflected0 hconjugate0 using 1
  rw [d4BMXiReflected_sub_conjugateQNMMinus_eq_neg_tilt]

/-- At a coincident pole, unequal branch velocities give the exact quadratic opening coefficient. -/
theorem d4BMXiGaugeFixedPartnerPoleDiscriminant_div_sq_tendsto
    {reflectedPole conjugatePole : ℂ → ℂ}
    {reflectedVelocity conjugateVelocity : ℂ}
    (hreflected : HasDerivAt reflectedPole reflectedVelocity 0)
    (hconjugate : HasDerivAt conjugatePole conjugateVelocity 0)
    (hcoincident : reflectedPole 0 = conjugatePole 0) :
    Tendsto
      (fun coupling =>
        d4BMXiGaugeFixedPartnerPoleDiscriminant
          reflectedPole conjugatePole coupling / coupling ^ (2 : ℕ))
      (𝓝[≠] 0) (𝓝 ((reflectedVelocity - conjugateVelocity) ^ (2 : ℕ))) := by
  have hseparation : HasDerivAt
      (fun coupling => reflectedPole coupling - conjugatePole coupling)
      (reflectedVelocity - conjugateVelocity) 0 :=
    hreflected.sub hconjugate
  have hsquare := hseparation.tendsto_slope_zero.pow 2
  apply hsquare.congr'
  filter_upwards [self_mem_nhdsWithin] with coupling hcoupling
  have hcoupling0 : coupling ≠ 0 := by simpa using hcoupling
  simp only [zero_add, d4BMXiGaugeFixedPartnerPoleDiscriminant,
    d4BMXiGaugeFixedPartnerPoleSeparation, hcoincident, sub_self, sub_zero,
    smul_eq_mul]
  field_simp [hcoupling0]

/-- At a critical-line collision, the squared partner separation has no linear opening. -/
theorem d4BMXiGaugeFixedPartnerPoleDiscriminant_hasDerivAt_zero_of_re_eq_half
    {reflectedPole conjugatePole : ℂ → ℂ}
    {reflectedVelocity conjugateVelocity : ℂ}
    (N : ℕ) (q : XiZeroCopy)
    (hreflected : HasDerivAt reflectedPole reflectedVelocity 0)
    (hconjugate : HasDerivAt conjugatePole conjugateVelocity 0)
    (hreflected0 : reflectedPole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
    (hconjugate0 : conjugatePole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyConjEquiv q)))
    (hline : (q.1 : ℂ).re = 1 / 2) :
    HasDerivAt
      (d4BMXiGaugeFixedPartnerPoleDiscriminant reflectedPole conjugatePole) 0 0 := by
  convert d4BMXiGaugeFixedPartnerPoleDiscriminant_hasDerivAt_eq_tilt
    N q hreflected hconjugate hreflected0 hconjugate0 using 1
  rw [hline]
  norm_num

/-- If critical-line partner velocities differ, their squared separation opens at exactly second
order with coefficient equal to the squared velocity difference. -/
theorem d4BMXiGaugeFixedPartnerPoleDiscriminant_div_sq_tendsto_of_re_eq_half
    {reflectedPole conjugatePole : ℂ → ℂ}
    {reflectedVelocity conjugateVelocity : ℂ}
    (N : ℕ) (q : XiZeroCopy)
    (hreflected : HasDerivAt reflectedPole reflectedVelocity 0)
    (hconjugate : HasDerivAt conjugatePole conjugateVelocity 0)
    (hreflected0 : reflectedPole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
    (hconjugate0 : conjugatePole 0 =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyConjEquiv q)))
    (hline : (q.1 : ℂ).re = 1 / 2) :
    Tendsto
      (fun coupling =>
        d4BMXiGaugeFixedPartnerPoleDiscriminant
          reflectedPole conjugatePole coupling / coupling ^ (2 : ℕ))
      (𝓝[≠] 0) (𝓝 ((reflectedVelocity - conjugateVelocity) ^ (2 : ℕ))) := by
  apply d4BMXiGaugeFixedPartnerPoleDiscriminant_div_sq_tendsto
    hreflected hconjugate
  rw [hreflected0, hconjugate0]
  exact (d4BMXiReflectedQNMMinus_eq_conjugateQNMMinus_iff N q).mpr hline

/-- A symmetry-compatible all-order response gives the two critical copies one common pole germ. -/
theorem exists_d4BMXiGaugeFixedTotalPeriodAllOrderCommonPartnerPoleBranchMinus_of_re_eq_half
    (higher : ℂ × ℂ → ℂ)
    (n k N : ℕ) (conservativeFinitePart : ℝ)
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hhigher : AnalyticAt ℂ higher
      (0, thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyReflectEquiv q))))
    (hline : (q.1 : ℂ).re = 1 / 2) :
    ∃ pole : ℂ → ℂ,
      AnalyticAt ℂ pole 0 ∧
      pole 0 = thetaCuspHawkingTopologicalBlackHoleQNMMinus N
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) ∧
      (∀ᶠ coupling : ℂ in 𝓝 0,
        d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostMinus higher
          n k conservativeFinitePart amplitude orthogonalMixing
          (xiZeroCopyReflectEquiv q) coupling (pole coupling) = 0) ∧
      (∀ᶠ coupling : ℂ in 𝓝 0,
        d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostMinus higher
          n k conservativeFinitePart amplitude orthogonalMixing
          (xiZeroCopyConjEquiv q) coupling (pole coupling) = 0) := by
  have hcopy : xiZeroCopyReflectEquiv q = xiZeroCopyConjEquiv q :=
    xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half q (by
      simpa [deningerDivisorThetaEigen] using hline)
  obtain ⟨pole, hpole, hpole0, hroot⟩ :=
    exists_d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostPoleBranchMinus
      higher n k N conservativeFinitePart amplitude orthogonalMixing
        (xiZeroCopyReflectEquiv q) hhigher
  refine ⟨pole, hpole, hpole0, hroot, ?_⟩
  simpa [hcopy] using hroot

end

end RHTower
