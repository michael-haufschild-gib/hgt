import GaloisForLFunctions.RHTower.DeningerArithmeticFiniteJetInterpolation
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous finite Xi-jet sections

Finite Hermite interpolation is not merely existential.  After flattening a finite packet of
multiplicity-bounded Xi jets to one finite coordinate type, the observation map is a surjective
linear map onto a finite-dimensional complex space.  Its canonical linear splitting is therefore
continuous.

This supplies finite Hermite representatives depending continuously and linearly on their jet
data.  Combined with local Taylor peeling, it is the finite-dimensional continuity input for
`[DAC_LOCAL_QUOTIENT_OPENNESS]`.
-/

namespace RHTower

noncomputable section

/-- Flattened coordinate type for all multiplicity-bounded jets in a finite Xi packet. -/
abbrev DeningerArithmeticFiniteJetCoordinate
    (S : Finset XiDivisorSupport) :=
  (rho : ↥S) × DeningerArithmeticJetIndex rho.1

/-- Finite complex jet-value space attached to `S`. -/
abbrev DeningerArithmeticFiniteJetValues
    (S : Finset XiDivisorSupport) :=
  DeningerArithmeticFiniteJetCoordinate S → ℂ

/-- Continuous restriction of the full jet observation to a finite flattened packet. -/
def deningerCompactOpenFiniteJets
    (S : Finset XiDivisorSupport) :
    DeningerCompactOpenEntire →L[ℂ]
      DeningerArithmeticFiniteJetValues S :=
  ContinuousLinearMap.pi fun idx =>
    deningerCompactOpenJet
      (xiSpectralPointSupport idx.1.1) idx.2

@[simp]
theorem deningerCompactOpenFiniteJets_apply
    (S : Finset XiDivisorSupport)
    (F : DeningerCompactOpenEntire)
    (idx : DeningerArithmeticFiniteJetCoordinate S) :
    deningerCompactOpenFiniteJets S F idx =
      deningerCompactOpenJet
        (xiSpectralPointSupport idx.1.1) idx.2 F :=
  rfl

/-- Finite Hermite interpolation makes every finite flattened Xi-jet observation surjective. -/
theorem deningerCompactOpenFiniteJets_surjective
    (S : Finset XiDivisorSupport) :
    Function.Surjective
      (deningerCompactOpenFiniteJets S) := by
  intro target
  obtain ⟨F, hF⟩ :=
    exists_deningerCompactOpenPolynomial_finiteXiScalarJets
      S (fun rho k => target ⟨rho, k⟩)
  refine ⟨F, ?_⟩
  funext idx
  exact hF idx.1 idx.2

/-- Chosen entire source realizing one standard finite jet coordinate. -/
def deningerCompactOpenFiniteJetBasisSource
    (S : Finset XiDivisorSupport)
    (idx : DeningerArithmeticFiniteJetCoordinate S) :
    DeningerCompactOpenEntire :=
  Classical.choose
    (deningerCompactOpenFiniteJets_surjective S
      (Pi.single idx 1))

@[simp]
theorem deningerCompactOpenFiniteJets_basisSource
    (S : Finset XiDivisorSupport)
    (idx : DeningerArithmeticFiniteJetCoordinate S) :
    deningerCompactOpenFiniteJets S
        (deningerCompactOpenFiniteJetBasisSource S idx) =
      Pi.single idx 1 :=
  Classical.choose_spec
    (deningerCompactOpenFiniteJets_surjective S
      (Pi.single idx 1))

/--
Continuous linear finite Hermite section.

It is the finite sum of coordinate projections followed by scalar multiplication of the chosen
standard-coordinate sources, so continuity is explicit and does not rely on an open mapping
theorem.
-/
def deningerCompactOpenFiniteJetSection
    (S : Finset XiDivisorSupport) :
    DeningerArithmeticFiniteJetValues S →L[ℂ]
      DeningerCompactOpenEntire :=
  ∑ idx : DeningerArithmeticFiniteJetCoordinate S,
    (ContinuousLinearMap.toSpanSingleton ℂ
      (deningerCompactOpenFiniteJetBasisSource S idx)).comp
        (ContinuousLinearMap.proj idx)

@[simp]
theorem deningerCompactOpenFiniteJets_section
    (S : Finset XiDivisorSupport)
    (target : DeningerArithmeticFiniteJetValues S) :
    deningerCompactOpenFiniteJets S
        (deningerCompactOpenFiniteJetSection S target) =
      target := by
  classical
  calc
    deningerCompactOpenFiniteJets S
        (deningerCompactOpenFiniteJetSection S target) =
        ∑ idx : DeningerArithmeticFiniteJetCoordinate S,
          target idx •
            deningerCompactOpenFiniteJets S
              (deningerCompactOpenFiniteJetBasisSource
                S idx) := by
      rw [deningerCompactOpenFiniteJetSection,
        ContinuousLinearMap.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro idx hidx
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.toSpanSingleton_apply,
        map_smul]
    _ = ∑ idx : DeningerArithmeticFiniteJetCoordinate S,
          target idx • Pi.single idx 1 := by
      apply Finset.sum_congr rfl
      intro idx hidx
      rw [deningerCompactOpenFiniteJets_basisSource]
    _ = target := by
      funext idx
      rw [Finset.sum_apply,
        Finset.sum_eq_single idx]
      · simp
      · intro j hj hne
        simp [hne]
      · intro hnot
        exact (hnot (Finset.mem_univ idx)).elim

/-- Canonical finite-jet representative of an entire source. -/
def deningerCompactOpenFiniteJetRepresentative
    (S : Finset XiDivisorSupport) :
    DeningerCompactOpenEntire →L[ℂ]
      DeningerCompactOpenEntire :=
  (deningerCompactOpenFiniteJetSection S).comp
    (deningerCompactOpenFiniteJets S)

/-- The canonical representative has exactly the same finite jet packet as its source. -/
@[simp]
theorem deningerCompactOpenFiniteJets_representative
    (S : Finset XiDivisorSupport)
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenFiniteJets S
        (deningerCompactOpenFiniteJetRepresentative S F) =
      deningerCompactOpenFiniteJets S F :=
  deningerCompactOpenFiniteJets_section S
    (deningerCompactOpenFiniteJets S F)

end

end RHTower
