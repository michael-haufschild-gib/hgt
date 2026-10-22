import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBUnboundedSelfAdjointAngularForcingNoGo
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Bounded dissipative reflected-forcing no-go

The exact reduced doubled-weight Einstein--Teukolsky source is nonzero on every tilted Xi fibre.
Complex conjugation sends its angular parameter to the opposite open half-plane.  This module proves
that no bounded passive linear boundary dynamics can extinguish this reflected source pair.

For a bounded dissipative operator `A`, every upper-half-plane shift `A - z` is injective,
bounded below, has closed range, and has dense range; hence it is surjective.  The dual statement
holds for bounded antidissipative operators in the lower half-plane.  Every nonzero source
therefore has a unique nonzero forced response satisfying

`|Im z| * ||x|| <= ||source||`.

Applying the two resolvent laws to a divisor copy and its Schwarz-conjugate copy shows that the
exact Teukolsky sources on both members of every hypothetical off-critical-line orbit respond in
the matching passive half-planes.  Thus bounded nonnormal dissipative retarded/advanced boundary
exclusion cannot convert the exact source incidence into universal source extinction and cannot
close the HB-to-RH chain.

Strongest positive survivor: any viable boundary exclusion must be unbounded and domain-sensitive,
nonlinear, or change the reflected half-plane orientation.

`[NEW] [HB ROUTE KILL] [BOUNDED DISSIPATIVE] [NONNORMAL] [RESOLVENT]
[REFLECTED TEUKOLSKY SOURCE] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open scoped InnerProductSpace

def IsBoundedDissipative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) : Prop :=
  ∀ x : H, (⟪x, A x⟫_ℂ).im ≤ 0

def IsBoundedAntidissipative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) : Prop :=
  ∀ x : H, 0 ≤ (⟪x, A x⟫_ℂ).im

def boundedShiftedMap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  A - z • ContinuousLinearMap.id ℂ H

@[simp] theorem boundedShiftedMap_apply {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (z : ℂ) (x : H) :
    boundedShiftedMap A z x = A x - z • x := rfl

theorem boundedDissipative_shift_norm_lower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsBoundedDissipative A)
    (z : ℂ) (x : H) :
    z.im * ‖x‖ ≤ ‖boundedShiftedMap A z x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have him :
      (⟪x, boundedShiftedMap A z x⟫_ℂ).im =
        (⟪x, A x⟫_ℂ).im - z.im * ‖x‖ ^ 2 := by
    simp [boundedShiftedMap, pow_two, Complex.mul_im]
  have hraw :
      z.im * ‖x‖ ^ 2 ≤ -(⟪x, boundedShiftedMap A z x⟫_ℂ).im := by
    rw [him]
    linarith [hA x]
  have habs :
      -(⟪x, boundedShiftedMap A z x⟫_ℂ).im ≤
        |(⟪x, boundedShiftedMap A z x⟫_ℂ).im| := neg_le_abs _
  have himnorm :
      |(⟪x, boundedShiftedMap A z x⟫_ℂ).im| ≤
        ‖⟪x, boundedShiftedMap A z x⟫_ℂ‖ :=
    Complex.abs_im_le_norm _
  have hcs :
      ‖⟪x, boundedShiftedMap A z x⟫_ℂ‖ ≤
        ‖x‖ * ‖boundedShiftedMap A z x‖ := norm_inner_le_norm _ _
  have htotal : z.im * ‖x‖ ^ 2 ≤ ‖x‖ * ‖boundedShiftedMap A z x‖ :=
    hraw.trans (habs.trans (himnorm.trans hcs))
  nlinarith

theorem boundedDissipative_shift_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsBoundedDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    Function.Injective (boundedShiftedMap A z) := by
  intro x y hxy
  have hzero : boundedShiftedMap A z (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hbound := boundedDissipative_shift_norm_lower A hA z (x - y)
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem boundedDissipative_shift_range_orthogonal_eq_bot
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsBoundedDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    (LinearMap.range (boundedShiftedMap A z).toLinearMap)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hperp : ⟪boundedShiftedMap A z y, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ y).1 hy _ ⟨y, rfl⟩
  have hperp' : ⟪y, boundedShiftedMap A z y⟫_ℂ = 0 := by
    have hc := congrArg (starRingEnd ℂ) hperp
    simpa [inner_conj_symm, mul_comm] using hc
  have him : (⟪y, A y⟫_ℂ).im - z.im * ‖y‖ ^ 2 = 0 := by
    simpa [boundedShiftedMap, pow_two, Complex.mul_im] using congrArg Complex.im hperp'
  have hsq : ‖y‖ ^ 2 = 0 := by
    nlinarith [hA y, sq_nonneg ‖y‖]
  have hnorm : ‖y‖ = 0 := sq_eq_zero_iff.mp hsq
  exact norm_eq_zero.mp hnorm

theorem boundedDissipative_shift_range_closed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsBoundedDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    IsClosed (Set.range (boundedShiftedMap A z)) := by
  let K : NNReal := ⟨z.im⁻¹, le_of_lt (inv_pos.mpr hz)⟩
  have hanti : AntilipschitzWith K (boundedShiftedMap A z) := by
    refine AddMonoidHomClass.antilipschitz_of_bound (boundedShiftedMap A z) fun x => ?_
    have h := boundedDissipative_shift_norm_lower A hA z x
    change ‖x‖ ≤ z.im⁻¹ * ‖boundedShiftedMap A z x‖
    rw [le_inv_mul_iff₀ hz]
    exact h
  exact hanti.isClosed_range (boundedShiftedMap A z).uniformContinuous

theorem boundedDissipative_shift_surjective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsBoundedDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    Function.Surjective (boundedShiftedMap A z) := by
  have hclosed : IsClosed
      ((LinearMap.range (boundedShiftedMap A z).toLinearMap : Submodule ℂ H) : Set H) := by
    change IsClosed (Set.range (boundedShiftedMap A z))
    exact boundedDissipative_shift_range_closed A hA z hz
  have htop := Submodule.topologicalClosure_eq_top_iff.2
    (boundedDissipative_shift_range_orthogonal_eq_bot A hA z hz)
  have hself : (LinearMap.range (boundedShiftedMap A z).toLinearMap).topologicalClosure =
      LinearMap.range (boundedShiftedMap A z).toLinearMap :=
    SetLike.coe_injective hclosed.closure_eq
  rw [hself] at htop
  exact LinearMap.range_eq_top.1 htop

theorem boundedAntidissipative_shift_norm_lower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsBoundedAntidissipative A)
    (z : ℂ) (x : H) :
    (-z.im) * ‖x‖ ≤ ‖boundedShiftedMap A z x‖ := by
  by_cases hx : x = 0
  · subst x
    simp
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have him :
      (⟪x, boundedShiftedMap A z x⟫_ℂ).im =
        (⟪x, A x⟫_ℂ).im - z.im * ‖x‖ ^ 2 := by
    simp [boundedShiftedMap, pow_two, Complex.mul_im]
  have hraw :
      (-z.im) * ‖x‖ ^ 2 ≤ (⟪x, boundedShiftedMap A z x⟫_ℂ).im := by
    rw [him]
    linarith [hA x]
  have habs :
      (⟪x, boundedShiftedMap A z x⟫_ℂ).im ≤
        |(⟪x, boundedShiftedMap A z x⟫_ℂ).im| := le_abs_self _
  have himnorm :
      |(⟪x, boundedShiftedMap A z x⟫_ℂ).im| ≤
        ‖⟪x, boundedShiftedMap A z x⟫_ℂ‖ :=
    Complex.abs_im_le_norm _
  have hcs :
      ‖⟪x, boundedShiftedMap A z x⟫_ℂ‖ ≤
        ‖x‖ * ‖boundedShiftedMap A z x‖ := norm_inner_le_norm _ _
  have htotal : (-z.im) * ‖x‖ ^ 2 ≤ ‖x‖ * ‖boundedShiftedMap A z x‖ :=
    hraw.trans (habs.trans (himnorm.trans hcs))
  nlinarith

theorem boundedAntidissipative_shift_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsBoundedAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    Function.Injective (boundedShiftedMap A z) := by
  intro x y hxy
  have hzero : boundedShiftedMap A z (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hbound := boundedAntidissipative_shift_norm_lower A hA z (x - y)
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem boundedAntidissipative_shift_range_orthogonal_eq_bot
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsBoundedAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    (LinearMap.range (boundedShiftedMap A z).toLinearMap)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hperp : ⟪boundedShiftedMap A z y, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ y).1 hy _ ⟨y, rfl⟩
  have hperp' : ⟪y, boundedShiftedMap A z y⟫_ℂ = 0 := by
    have hc := congrArg (starRingEnd ℂ) hperp
    simpa [inner_conj_symm, mul_comm] using hc
  have him : (⟪y, A y⟫_ℂ).im - z.im * ‖y‖ ^ 2 = 0 := by
    simpa [boundedShiftedMap, pow_two, Complex.mul_im] using congrArg Complex.im hperp'
  have hsq : ‖y‖ ^ 2 = 0 := by
    nlinarith [hA y, sq_nonneg ‖y‖]
  have hnorm : ‖y‖ = 0 := sq_eq_zero_iff.mp hsq
  exact norm_eq_zero.mp hnorm

theorem boundedAntidissipative_shift_range_closed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsBoundedAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    IsClosed (Set.range (boundedShiftedMap A z)) := by
  let K : NNReal := ⟨(-z.im)⁻¹, le_of_lt (inv_pos.mpr (neg_pos.mpr hz))⟩
  have hanti : AntilipschitzWith K (boundedShiftedMap A z) := by
    refine AddMonoidHomClass.antilipschitz_of_bound (boundedShiftedMap A z) fun x => ?_
    have h := boundedAntidissipative_shift_norm_lower A hA z x
    change ‖x‖ ≤ (-z.im)⁻¹ * ‖boundedShiftedMap A z x‖
    rw [le_inv_mul_iff₀ (neg_pos.mpr hz)]
    exact h
  exact hanti.isClosed_range (boundedShiftedMap A z).uniformContinuous

theorem boundedAntidissipative_shift_surjective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsBoundedAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    Function.Surjective (boundedShiftedMap A z) := by
  have hclosed : IsClosed
      ((LinearMap.range (boundedShiftedMap A z).toLinearMap : Submodule ℂ H) : Set H) := by
    change IsClosed (Set.range (boundedShiftedMap A z))
    exact boundedAntidissipative_shift_range_closed A hA z hz
  have htop := Submodule.topologicalClosure_eq_top_iff.2
    (boundedAntidissipative_shift_range_orthogonal_eq_bot A hA z hz)
  have hself : (LinearMap.range (boundedShiftedMap A z).toLinearMap).topologicalClosure =
      LinearMap.range (boundedShiftedMap A z).toLinearMap :=
    SetLike.coe_injective hclosed.closure_eq
  rw [hself] at htop
  exact LinearMap.range_eq_top.1 htop

/-- A source is in the resolvent range with a unique nonzero response and the half-plane bound. -/
def HasUniqueBoundedShiftedResponse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (z : ℂ) (source : H) : Prop :=
  ∃! x : H,
    boundedShiftedMap A z x = source ∧ x ≠ 0 ∧
      |z.im| * ‖x‖ ≤ ‖source‖

theorem boundedDissipative_hasUniqueBoundedShiftedResponse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsBoundedDissipative A)
    (z : ℂ) (hz : 0 < z.im) (source : H) (hsource : source ≠ 0) :
    HasUniqueBoundedShiftedResponse A z source := by
  obtain ⟨x, hx⟩ := boundedDissipative_shift_surjective A hA z hz source
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hsource
    rw [← hx, hxzero, map_zero]
  have hbound : |z.im| * ‖x‖ ≤ ‖source‖ := by
    rw [abs_of_pos hz]
    simpa [hx] using boundedDissipative_shift_norm_lower A hA z x
  refine ⟨x, ⟨hx, hxne, hbound⟩, ?_⟩
  intro y hy
  exact boundedDissipative_shift_injective A hA z hz (hy.1.trans hx.symm)

theorem boundedAntidissipative_hasUniqueBoundedShiftedResponse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsBoundedAntidissipative A)
    (z : ℂ) (hz : z.im < 0) (source : H) (hsource : source ≠ 0) :
    HasUniqueBoundedShiftedResponse A z source := by
  obtain ⟨x, hx⟩ := boundedAntidissipative_shift_surjective A hA z hz source
  have hxne : x ≠ 0 := by
    intro hxzero
    apply hsource
    rw [← hx, hxzero, map_zero]
  have hbound : |z.im| * ‖x‖ ≤ ‖source‖ := by
    rw [abs_of_neg hz]
    simpa [hx] using boundedAntidissipative_shift_norm_lower A hA z x
  refine ⟨x, ⟨hx, hxne, hbound⟩, ?_⟩
  intro y hy
  exact boundedAntidissipative_shift_injective A hA z hz (hy.1.trans hx.symm)

theorem d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_copyConj_im
    (q : XiZeroCopy) :
    (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
      (xiSpectralPoint (xiZeroCopyConjEquiv q))).im =
      -(d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
        (xiSpectralPoint q)).im := by
  rw [d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
    xiSpectralPoint_copyConj,
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq]
  simp [pow_two, Complex.mul_im]
  ring

theorem xiZeroCopyConjEquiv_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (((xiZeroCopyConjEquiv q).1 : ℂ).re) ≠ 1 / 2 := by
  change ((starRingEnd ℂ) (q.1 : ℂ)).re ≠ 1 / 2
  simpa using htilt

/-- The exact source at a divisor and its Schwarz copy is forced into the matching passive
half-plane resolvents. -/
def D4HBBoundedDissipativeReflectedSourcePairResponds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (upper lower : H →L[ℂ] H) (amplitude mixed anti : ℂ)
    (profile : H) (q : XiZeroCopy) : Prop :=
  let qstar := xiZeroCopyConjEquiv q
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let lambdaStar :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint qstar)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  let sourceStar := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile qstar
  (0 < lambda.im ∧
      HasUniqueBoundedShiftedResponse upper lambda source ∧
      HasUniqueBoundedShiftedResponse lower lambdaStar sourceStar) ∨
    (lambda.im < 0 ∧
      HasUniqueBoundedShiftedResponse lower lambda source ∧
      HasUniqueBoundedShiftedResponse upper lambdaStar sourceStar)

theorem d4ThetaReducedSecondOrderChiralTeukolskySource_boundedDissipative_reflectedPair_responds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (upper lower : H →L[ℂ] H)
    (hupper : IsBoundedDissipative upper)
    (hlower : IsBoundedAntidissipative lower)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ)
    (profile : H) (hprofile : profile ≠ 0)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    D4HBBoundedDissipativeReflectedSourcePairResponds
      upper lower amplitude mixed anti profile q := by
  let qstar := xiZeroCopyConjEquiv q
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let lambdaStar :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint qstar)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  let sourceStar := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile qstar
  have htiltStar : (qstar.1 : ℂ).re ≠ 1 / 2 := by
    exact xiZeroCopyConjEquiv_tilt q htilt
  have hlambda : lambda.im ≠ 0 := by
    exact d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt q htilt
  have hreflect : lambdaStar.im = -lambda.im := by
    exact d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_copyConj_im q
  have hsource : source ≠ 0 := by
    exact d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile q htilt
  have hsourceStar : sourceStar ≠ 0 := by
    exact d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile qstar htiltStar
  change (0 < lambda.im ∧
      HasUniqueBoundedShiftedResponse upper lambda source ∧
      HasUniqueBoundedShiftedResponse lower lambdaStar sourceStar) ∨
    (lambda.im < 0 ∧
      HasUniqueBoundedShiftedResponse lower lambda source ∧
      HasUniqueBoundedShiftedResponse upper lambdaStar sourceStar)
  rcases lt_or_gt_of_ne hlambda with hneg | hpos
  · right
    refine ⟨hneg,
      boundedAntidissipative_hasUniqueBoundedShiftedResponse
        lower hlower lambda hneg source hsource, ?_⟩
    apply boundedDissipative_hasUniqueBoundedShiftedResponse
      upper hupper lambdaStar
    · linarith
    · exact hsourceStar
  · left
    refine ⟨hpos,
      boundedDissipative_hasUniqueBoundedShiftedResponse
        upper hupper lambda hpos source hsource, ?_⟩
    apply boundedAntidissipative_hasUniqueBoundedShiftedResponse
      lower hlower lambdaStar
    · linarith
    · exact hsourceStar

/-- Closed route-class certificate: bounded passive reflected boundary dynamics cannot extinguish
the exact doubled-weight source on any hypothetical off-wall Xi orbit. -/
def D4HBBoundedDissipativeReflectedForcingExclusionRouteKilled : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (upper lower : H →L[ℂ] H)
    (amplitude mixed anti : ℂ) (profile : H),
      IsBoundedDissipative upper →
      IsBoundedAntidissipative lower →
      amplitude ≠ 0 → profile ≠ 0 →
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
        D4HBBoundedDissipativeReflectedSourcePairResponds
          upper lower amplitude mixed anti profile q

theorem d4HBBoundedDissipativeReflectedForcingExclusionRouteKilled :
    D4HBBoundedDissipativeReflectedForcingExclusionRouteKilled := by
  intro H _ _ _ upper lower amplitude mixed anti profile
    hupper hlower ha hprofile q htilt
  exact d4ThetaReducedSecondOrderChiralTeukolskySource_boundedDissipative_reflectedPair_responds
    upper lower hupper hlower ha mixed anti profile hprofile q htilt

end

end RHTower

