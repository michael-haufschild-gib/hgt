import GaloisForLFunctions.RHTower.ThetaCuspHawkingReducedSecondOrderChiralTeukolskyGradeIncidence
import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent

/-!
# Unbounded self-adjoint angular forcing no-go

The exact reduced second-order chiral Einstein--Teukolsky source is nonzero precisely on tilted Xi
fibres.  Earlier angular endpoints noted that its doubled cusp weight then has a nonreal de-aliased
angular eigenvalue.  This module closes the strongest remaining self-adjoint exclusion loophole:
genuine unbounded differential operators, arbitrary self-adjoint boundary domains, and
infinite-dimensional one-sector carriers.

For every self-adjoint partially defined angular operator `A` and every tilted fibre, the nonreal
parameter lies in the resolvent of `A`.  Consequently the exact sourced equation

`(A - lambda(q)) x = source(q)`

has a unique nonzero solution.  It obeys the sharp general resolvent estimate

`|Im lambda(q)| * ||x|| <= ||source(q)||`.

Self-adjointness does exclude a nonzero solution of the *homogeneous* eigen-equation
`A x = lambda(q) x`; it does not exclude the forced HC62 equation.  Thus spectral reality cannot
turn the actual tilted source into extinction and cannot supply the shared HB/FZZ-P/PW-B/RBH Ward
producer.  A survivor must prove source-specific zero projection/no-forcing, convert the physical
equation to a homogeneous mode equation, or use genuinely non-self-adjoint causal/scattering
boundary data.

`[NEW] [HB ROUTE KILL] [UNBOUNDED SELF-ADJOINT] [RESOLVENT] [TEUKOLSKY]
[FOUR-ROUTE WARD] [LEAN-PROVED]`
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A tilted Xi fibre gives a genuinely nonreal doubled chiral angular parameter. -/
theorem d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
      (xiSpectralPoint q)).im ≠ 0 := by
  intro him
  have heq :
      d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q) =
        d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue (xiSpectralPoint q) := by
    rw [d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
      d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_eq]
  rw [heq] at him
  have hspectral :=
    (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q).1 him
  rw [xiSpectralPoint_im_eq] at hspectral
  apply htilt
  linarith

/-- Every self-adjoint angular operator admits one and only one response to the exact HC62 source
at a tilted fibre.  No boundedness, compactness, locality, or finite-dimensionality is assumed. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskySource_selfAdjoint_forcedSolution_unique
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (amplitude mixed anti : ℂ) (profile : H) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃! x : A.domain,
      shiftedMap A
          (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)) x =
        d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
          amplitude mixed anti profile q := by
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  have hlambda : lambda.im ≠ 0 := by
    exact d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt q htilt
  obtain ⟨x, hx⟩ := surjective_shiftedMap hA hlambda source
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact injective_shiftedMap hA hlambda (hy.trans hx.symm)

/-- With nonzero Einstein seed and angular profile, the unique forced response is nonzero and
satisfies the self-adjoint imaginary-part resolvent estimate. -/
theorem d4ThetaReducedSecondOrderChiralTeukolskySource_selfAdjoint_forcedSolution_nonzero_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ)
    (profile : H) (hprofile : profile ≠ 0) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃! x : A.domain,
      shiftedMap A
          (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)) x =
          d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
            amplitude mixed anti profile q ∧
        (x : H) ≠ 0 ∧
        |(d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
            (xiSpectralPoint q)).im| * ‖(x : H)‖ ≤
          ‖d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
            amplitude mixed anti profile q‖ := by
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  have hlambda : lambda.im ≠ 0 := by
    exact d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt q htilt
  have hsource : source ≠ 0 := by
    exact d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile q htilt
  obtain ⟨x, hx⟩ := surjective_shiftedMap hA hlambda source
  have hxne : (x : H) ≠ 0 := by
    intro hxzero
    apply hsource
    have hshiftzero : shiftedMap A lambda x = 0 := by
      have hxsub : x = 0 := Subtype.ext hxzero
      rw [hxsub]
      simp
    exact hx.symm.trans hshiftzero
  have hbound : |lambda.im| * ‖(x : H)‖ ≤ ‖source‖ := by
    have h := norm_sub_smul_lower_bound hA lambda x
    change |lambda.im| * ‖(x : H)‖ ≤ ‖shiftedMap A lambda x‖ at h
    rwa [hx] at h
  refine ⟨x, ⟨hx, hxne, hbound⟩, ?_⟩
  intro y hy
  exact injective_shiftedMap hA hlambda (hy.1.trans hx.symm)

/-- Closed route class: self-adjoint angular reality excludes the tilted coefficient only from a
homogeneous eigen-equation, while the exact reduced Einstein--Teukolsky source has a unique
nonzero forced solution with the imaginary-part resolvent bound. -/
def D4HBUnboundedSelfAdjointAngularForcingExclusionRouteKilled : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ (A : H →ₗ.[ℂ] H), IsSelfAdjoint A →
    ∀ (amplitude : ℂ), amplitude ≠ 0 → ∀ (mixed anti : ℂ),
    ∀ (profile : H), profile ≠ 0 → ∀ (q : XiZeroCopy),
    (q.1 : ℂ).re ≠ 1 / 2 →
      (∀ x : A.domain,
        A x = d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
            (xiSpectralPoint q) • (x : H) →
          (x : H) = 0) ∧
      ∃! x : A.domain,
        shiftedMap A
            (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)) x =
            d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
              amplitude mixed anti profile q ∧
          (x : H) ≠ 0 ∧
          |(d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
              (xiSpectralPoint q)).im| * ‖(x : H)‖ ≤
            ‖d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
              amplitude mixed anti profile q‖

/-- Premise-free certificate killing arbitrary unbounded self-adjoint angular exclusion as the
missing producer for the shared HB/FZZ-P/PW-B/RBH Ward endpoint. -/
theorem d4HBUnboundedSelfAdjointAngularForcingExclusionRouteKilled :
    D4HBUnboundedSelfAdjointAngularForcingExclusionRouteKilled := by
  intro H _ _ _ A hA amplitude ha mixed anti profile hprofile q htilt
  have hlambda :
      (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
        (xiSpectralPoint q)).im ≠ 0 :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt q htilt
  constructor
  · intro x hx
    exact no_nonreal_eigenvector hA hlambda x hx
  · exact
      d4ThetaReducedSecondOrderChiralTeukolskySource_selfAdjoint_forcedSolution_nonzero_bound
        A hA ha mixed anti profile hprofile q htilt

end

end RHTower
