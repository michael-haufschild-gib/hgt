import GaloisForLFunctions.RHTower.EulerSquarefreeWickRegularOrbitFlux
import GaloisForLFunctions.RHTower.Artin.ArtinFiniteAbelianFourier

/-!
# Genuine-Artin positivity obstruction for Euler--Wick

The four-sector EWQ logarithmic carrier is the virtual character

`1 + χ₃χ₄ - χ₃ - χ₄`.

It has degree zero at the gauge identity but value four at the doubly nontrivial residue class.
This module proves the exact obstruction hidden by the virtual Artin notation: no genuine
finite-dimensional complex representation has this character.  Consequently the EWQ cross-ratio
cannot acquire positivity or holomorphy from an actual Artin/Hilbert carrier.  Its negative
marginal multiplicities are essential, not missing representation-theoretic infrastructure.

The result closes the genuine-character branch of the completed Xi landing problem.  A surviving
EWQ construction must remain virtual/Krein or introduce a new non-Artin positive completion which
retains the vacuum coordinate independently.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- A genuine character of a finite abelian group whose degree is zero vanishes identically. -/
theorem genuineCharacter_eq_zero_of_one_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (theta : GenuineCharacter G) (hone : theta.val 1 = 0) :
    theta.val = 0 := by
  letI : Finite (LinearCharacter G) :=
    RHTower.deningerCharacterGroup_finite
  letI : Fintype (LinearCharacter G) := Fintype.ofFinite _
  have hfourier := finiteAbelian_genuine_fourier_integral theta
  have hsumC :
      (∑ chi : LinearCharacter G,
        (genuineMultiplicity G (linearGenuineCharacter G chi) theta : ℂ)) = 0 := by
    have h := congrFun hfourier 1
    simpa [RHTower.deningerCharacterFn_apply, hone] using h.symm
  have hsumN :
      (∑ chi : LinearCharacter G,
        genuineMultiplicity G (linearGenuineCharacter G chi) theta) = 0 := by
    exact_mod_cast hsumC
  have hcoeff : ∀ chi : LinearCharacter G,
      genuineMultiplicity G (linearGenuineCharacter G chi) theta = 0 := by
    intro chi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hsumN chi
      (Finset.mem_univ chi)
  rw [hfourier]
  simp [hcoeff]

/-- EWQ's literal rank-two virtual Artin interaction character. -/
def ewqArtinInteractionCharacter (w : QuadraticResidueGaugeSpace) : ℂ :=
  1 + quadraticCharacterThreeUnit w.1 * quadraticCharacterFourUnit w.2 -
    quadraticCharacterThreeUnit w.1 - quadraticCharacterFourUnit w.2

/-- The virtual interaction has degree zero at the residue-gauge identity. -/
theorem ewqArtinInteractionCharacter_one :
    ewqArtinInteractionCharacter (1 : QuadraticResidueGaugeSpace) = 0 := by
  simp [ewqArtinInteractionCharacter, quadraticCharacterThreeUnit,
    quadraticCharacterFourUnit]

/-- Yet the same virtual character has value four on the joint nontrivial class. -/
theorem ewqArtinInteractionCharacter_neg_neg :
    ewqArtinInteractionCharacter
      ((-1 : (ZMod 3)ˣ), (-1 : (ZMod 4)ˣ)) = 4 := by
  norm_num [ewqArtinInteractionCharacter]

/-- The character is exactly the already constructed odd-depth EWQ Euler coefficient. -/
theorem ewqArtinInteractionCharacter_eq_virtualDepthOne
    (w : QuadraticResidueGaugeSpace) :
    ewqArtinInteractionCharacter w =
      quadraticResidueVirtualEulerDepthCoefficient 1
        ⟨w, Set.mem_univ w⟩ := by
  simp [ewqArtinInteractionCharacter,
    quadraticResidueVirtualEulerDepthCoefficient]

/-- **Genuine-Artin no-go.** The EWQ interaction is not a genuine character. -/
theorem ewqArtinInteractionCharacter_not_genuine :
    ewqArtinInteractionCharacter ∉
      GaloisForLFunctions.genuineCharacterMonoid QuadraticResidueGaugeSpace := by
  intro h
  let theta : GenuineCharacter QuadraticResidueGaugeSpace :=
    ⟨ewqArtinInteractionCharacter, h⟩
  have hz := genuineCharacter_eq_zero_of_one_eq_zero theta
    ewqArtinInteractionCharacter_one
  have hneg : ewqArtinInteractionCharacter
      ((-1 : (ZMod 3)ˣ), (-1 : (ZMod 4)ˣ)) = 0 := by
    simpa [theta] using congrFun hz
      ((-1 : (ZMod 3)ˣ), (-1 : (ZMod 4)ˣ))
  rw [ewqArtinInteractionCharacter_neg_neg] at hneg
  norm_num at hneg

/-- No finite-dimensional object in the concrete Artin category realizes the EWQ character. -/
theorem ewqArtinInteractionCharacter_not_fdRepCharacter :
    ¬ ∃ V : FDRep ℂ QuadraticResidueGaugeSpace,
      V.character = ewqArtinInteractionCharacter := by
  rintro ⟨V, hV⟩
  apply ewqArtinInteractionCharacter_not_genuine
  apply AddSubmonoid.subset_closure
  exact ⟨V, hV⟩

/-- Universe-polymorphic form: no finite-dimensional representation has the EWQ character. -/
theorem ewqArtinInteractionCharacter_ne_representationCharacter
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ QuadraticResidueGaugeSpace V) :
    rho.character ≠ ewqArtinInteractionCharacter := by
  intro h
  apply ewqArtinInteractionCharacter_not_genuine
  rw [← h]
  apply AddSubmonoid.subset_closure
  exact representation_character_mem_fdCharacterSet QuadraticResidueGaugeSpace rho

end GaloisForLFunctions.RHTower
