import GaloisForLFunctions.HTGeometry.CoordinateSpectrumRelationTransfer
import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw
import GaloisForLFunctions.HTGeometry.CrossLayerLiftParityRigidity
import GaloisForLFunctions.HTGeometry.AllLayerEndpointSimultaneousResponse

/-!
# The local Hamiltonians of one leaf extension escape every constant real relation

Adjoining one new local factor to an architecture whose spectrum is maximally projective and whose
parent site carries a connected nonbipartite Hermitian probe family produces, inside the enlarged
architecture's own local Hamiltonian space, a full local-extension slice: the new onsite terms and
the single new edge.  That slice escapes every prescribed constant real relation among the energies,
and the escape transports to the physical carrier through the spectral basis.

## Main results

* `exists_codedIntegerLayerShift_injective` — one coded shift makes the product spectrum simple.
* `leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations` — the escape property of the
  enlarged local Hamiltonian space.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **One coded layer shift makes the whole product spectrum simple.**  This is the response law
with no prescribed channels. -/
theorem exists_codedIntegerLayerShift_injective
    {I ρ : Type*} [Fintype I] [DecidableEq I] [Fintype ρ] [DecidableEq ρ]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy) (anchor : ρ) :
    ∃ n : ℕ,
      Function.Injective
        (layeredEnergy
          (fun i => (energy i : ℂ))
          (fun r => (codedIntegerLayerShift anchor n r : ℂ))) := by
  obtain ⟨n, hinj, -⟩ :=
    exists_codedIntegerLayerShift_all_responses_ne_zero
      (J := Empty) energy hmax anchor (fun q => q.elim) (fun q => q.elim)
      (0 : Matrix I I ℂ) (fun q => q.elim) (fun q => q.elim) (fun q => q.elim) (fun q => q.elim)
      (fun q => q.elim) (fun q => q.elim) (fun q => q.elim) (fun q => q.elim)
  exact ⟨n, hinj⟩

/-- **The enlarged local Hamiltonian space escapes every constant real relation.**  The escaping
witness is one point of the new-onsite-plus-new-edge slice, transported to the physical carrier by
the spectral basis tensored with the identity on the new factor. -/
theorem leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations
    {Physical Observer State η : Type u}
    [Fintype Physical] [DecidableEq Physical]
    [Fintype Observer] [DecidableEq Observer]
    [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype η]
    (T : RootedTensorTree Physical Observer) (root : Observer)
    (ρ : Type u) [Fintype ρ] [DecidableEq ρ] (hcard : 2 ≤ Fintype.card ρ)
    (energy : State → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (basis : Matrix Physical State ℂ)
    (hbasisL : basisᴴ * basis = (1 : Matrix State State ℂ))
    (hbasisR : basis * basisᴴ = (1 : Matrix Physical Physical ℂ))
    (hamiltonian : Matrix Physical Physical ℂ)
    (hlocal : T.IsLocalHamiltonian hamiltonian)
    (hcoord : basisᴴ * hamiltonian * basis = Matrix.diagonal (fun i => (energy i : ℂ)))
    (physicalProbe : η → Matrix Physical Physical ℂ)
    (hprobeOneSite : ∀ i, T.IsOneSite root (physicalProbe i))
    (spectralProbe : η → Matrix State State ℂ)
    (hprobeCoord : ∀ i, spectralProbe i = basisᴴ * physicalProbe i * basis)
    (hprobeHermitian : ∀ i, (spectralProbe i).IsHermitian)
    (hprobeConn : (transitionFamilySupportGraph spectralProbe).Preconnected)
    (hprobeNonbip : ¬ (transitionFamilySupportGraph spectralProbe).IsBipartite) :
    SpectrumEscapesAffineRelations
      ((RootedTensorTree.leaf T ρ root).hermitianLocalHamiltonianSubmodule :
        Set (Matrix (Physical × ρ) (Physical × ρ) ℂ)) := by
  classical
  haveI : Nonempty ρ := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by omega) hcard)
  obtain ⟨coefficient, hAHermitian, -, hAconn, hAnonbip⟩ :=
    exists_hermitianTransition_good_of_family_good
      spectralProbe hprobeHermitian hprobeConn hprobeNonbip
  set attachment : Matrix State State ℂ :=
    realMatrixFamilyCombination spectralProbe coefficient with hattachment
  set parentPhysical : Matrix Physical Physical ℂ :=
    realMatrixFamilyCombination physicalProbe coefficient with hparent
  have hparentCoord : basisᴴ * parentPhysical * basis = attachment := by
    rw [hattachment, hparent]
    exact
      (realMatrixFamilyCombination_coordinate basis physicalProbe spectralProbe coefficient
        hprobeCoord).symm
  let anchor : ρ := Classical.arbitrary ρ
  obtain ⟨n, hsimple⟩ := exists_codedIntegerLayerShift_injective energy hmax anchor
  have hlift :
      (crossLayerLiftGraph (transitionSupportGraph attachment) ρ).Preconnected :=
    crossLayerLiftGraph_preconnected_of_two_le_card _ hcard hAconn hAnonbip
  have hslice :=
    hermitianLocalExtensionSlice_spectrumEscapesAffineRelations
      (ρ := ρ) energy hmax (codedIntegerLayerShift anchor n) attachment hAHermitian hsimple hlift
  set B : Matrix (Physical × ρ) (State × ρ) ℂ := tensorIdentityBasis (ρ := ρ) basis with hB
  have hBL : Bᴴ * B = (1 : Matrix (State × ρ) (State × ρ) ℂ) :=
    star_tensorIdentityBasis_mul_self basis hbasisL
  have hBR : B * Bᴴ = (1 : Matrix (Physical × ρ) (Physical × ρ) ℂ) :=
    tensorIdentityBasis_mul_star_self basis hbasisR
  refine SpectrumEscapesAffineRelations.ofCoordinate hBL hBR hslice ?_
  rintro M ⟨q, rfl⟩
  set p := realLocalExtensionParameter (localExtensionSliceParameter q) with hp
  have hMcoord :
      Bᴴ * physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2 * B =
        hermitianLocalExtensionSliceMatrix energy attachment q :=
    tensorIdentityBasis_coordinate_physicalLeafHamiltonian basis hamiltonian parentPhysical
      (fun i => (energy i : ℂ)) p.1 attachment p.2 hbasisL hcoord hparentCoord
  have hNconj :
      physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2 =
        B * hermitianLocalExtensionSliceMatrix energy attachment q * Bᴴ := by
    rw [← hMcoord]
    calc physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2
        = (B * Bᴴ) * physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2 * (B * Bᴴ) := by
          rw [hBR, Matrix.one_mul, Matrix.mul_one]
      _ = B * (Bᴴ * physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2 * B) * Bᴴ := by
          simp [Matrix.mul_assoc]
  have hMHermitian :
      (hermitianLocalExtensionSliceMatrix energy attachment q).IsHermitian :=
    hermitianLocalExtensionSliceMatrix_isHermitian energy attachment hAHermitian q
  have hNHermitian :
      (physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2).IsHermitian := by
    rw [hNconj, Matrix.IsHermitian]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show (hermitianLocalExtensionSliceMatrix energy attachment q)ᴴ
        = hermitianLocalExtensionSliceMatrix energy attachment q from hMHermitian]
    simp [Matrix.mul_assoc]
  refine ⟨physicalLeafHamiltonian hamiltonian parentPhysical p.1 p.2, ?_, hMcoord⟩
  refine (RootedTensorTree.leaf T ρ root).mem_hermitianLocalHamiltonianSubmodule ?_ hNHermitian
  exact T.isLocalHamiltonian_physicalLeafHamiltonian root hamiltonian parentPhysical p.1 p.2
    hlocal
    (T.isOneSite_realMatrixFamilyCombination root physicalProbe coefficient hprobeOneSite)

end

end GaloisForLFunctions.HTGeometry
