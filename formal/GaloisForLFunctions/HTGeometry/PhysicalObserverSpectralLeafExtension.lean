import GaloisForLFunctions.HTGeometry.PhysicalObserverSpectralRealization
import GaloisForLFunctions.HTGeometry.CompleteObserverSpectralSeed

/-!
# Physical-local observer spectral leaf extension

The abstract spectral leaf theorem is lifted back to one fixed tensor
realization.  Every old observer probe remains an old-factor probe, the new
observer probes act on the new factor, and the Hamiltonian changes by one
onsite term plus one parent--leaf interaction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Matrix Kronecker BigOperators

universe u

/-- Physical probes before the final leaf eigenbasis change.  Old observers
use an originating physical probe on the previous tensor carrier; the new
observer acts only on the newly adjoined factor. -/
def physicalLeafExtendedProbeFamily
    {X : GoodObserverSpectralSystem.{u}}
    [Fintype X.State] [DecidableEq X.State]
    (R : X.PhysicalRealization)
    [DecidableEq R.PhysicalState]
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ]
    (G : X.Observer → SimpleGraph X.State)
    (attachment : Matrix X.State X.State ℂ)
    (anchor : ρ)
    (oldProbe :
      ∀ s,
        Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
          Matrix X.State X.State ℂ)
    (oldOrigin :
      ∀ s p, ∃ i : X.Probe s,
        oldProbe s p = X.transition s i)
    (newProbe :
      Sum (TransitionSupportEdge attachment × ρ)
          (NonanchorLayer anchor) →
        Matrix ρ ρ ℂ) :
    ∀ s : LeafExtendedObserver X.Observer,
      LeafExtendedProbeIndex G attachment anchor s →
        Matrix (R.PhysicalState × ρ)
          (R.PhysicalState × ρ) ℂ
  | Sum.inl s, q =>
      layerMatrixCoupling
        (R.physicalProbe s
          (Classical.choose (oldOrigin s q)))
        (1 : Matrix ρ ρ ℂ)
  | Sum.inr _, q =>
      layerMatrixCoupling
        (1 : Matrix R.PhysicalState R.PhysicalState ℂ)
        (newProbe q)

/-- Before the new leaf eigenbasis is applied, every physical probe has
exactly the chart probe as its spectral coordinate matrix. -/
theorem tensorIdentityBasis_coordinate_physicalLeafExtendedProbeFamily
    {X : GoodObserverSpectralSystem.{u}}
    [Fintype X.State] [DecidableEq X.State]
    (R : X.PhysicalRealization)
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ]
    (G : X.Observer → SimpleGraph X.State)
    (attachment : Matrix X.State X.State ℂ)
    (anchor : ρ)
    (oldProbe :
      ∀ s,
        Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
          Matrix X.State X.State ℂ)
    (oldOrigin :
      ∀ s p, ∃ i : X.Probe s,
        oldProbe s p = X.transition s i)
    (newProbe :
      Sum (TransitionSupportEdge attachment × ρ)
          (NonanchorLayer anchor) →
        Matrix ρ ρ ℂ) :
    letI : Fintype R.PhysicalState := R.physicalFintype
    letI : DecidableEq R.PhysicalState :=
      R.physicalDecidableEq
    ∀ s q,
      (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ *
          physicalLeafExtendedProbeFamily
            R G attachment anchor oldProbe oldOrigin
              newProbe s q *
          tensorIdentityBasis (ρ := ρ) R.basis =
        leafExtendedPhysicalProbeFamily
          G attachment anchor oldProbe newProbe s q := by
  letI : Fintype R.PhysicalState := R.physicalFintype
  letI : DecidableEq R.PhysicalState :=
    R.physicalDecidableEq
  intro s q
  cases s with
  | inl s =>
      let i : X.Probe s :=
        Classical.choose (oldOrigin s q)
      have hi :
          oldProbe s q = X.transition s i :=
        Classical.choose_spec (oldOrigin s q)
      have hcoordinate :
          R.basisᴴ * R.physicalProbe s i * R.basis =
            oldProbe s q := by
        calc
          R.basisᴴ * R.physicalProbe s i * R.basis =
              X.transition s i :=
            (R.transition_eq_coordinate s i).symm
          _ = oldProbe s q := hi.symm
      simpa [physicalLeafExtendedProbeFamily,
        leafExtendedPhysicalProbeFamily, i] using
        tensorIdentityBasis_coordinate_layer
          R.basis (R.physicalProbe s i)
          (oldProbe s q) (1 : Matrix ρ ρ ℂ)
          hcoordinate
  | inr _ =>
      have hcoordinate :
          R.basisᴴ *
              (1 : Matrix R.PhysicalState
                R.PhysicalState ℂ) *
              R.basis =
            (1 : Matrix X.State X.State ℂ) := by
        simpa [Matrix.mul_assoc] using
          R.star_basis_mul_basis
      simpa [physicalLeafExtendedProbeFamily,
        leafExtendedPhysicalProbeFamily] using
        tensorIdentityBasis_coordinate_layer
          R.basis
          (1 : Matrix R.PhysicalState
            R.PhysicalState ℂ)
          (1 : Matrix X.State X.State ℂ)
          (newProbe q) hcoordinate

/-- After composing with the exact leaf eigenbasis, every returned
observer matrix is still the coordinate matrix of its one-factor physical
probe. -/
theorem physicalLeafSpectralBasis_coordinate_probeFamily
    {X : GoodObserverSpectralSystem.{u}}
    [Fintype X.State] [DecidableEq X.State]
    (R : X.PhysicalRealization)
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ]
    {energy : X.State → ℂ} {shift : ρ → ℂ}
    {attachment : Matrix X.State X.State ℂ}
    (G : X.Observer → SimpleGraph X.State)
    (anchor : ρ)
    (C : LocalExtensionEigenbranchChart
      energy shift attachment)
    (oldProbe :
      ∀ s,
        Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
          Matrix X.State X.State ℂ)
    (oldOrigin :
      ∀ s p, ∃ i : X.Probe s,
        oldProbe s p = X.transition s i)
    (newProbe :
      Sum (TransitionSupportEdge attachment × ρ)
          (NonanchorLayer anchor) →
        Matrix ρ ρ ℂ)
    {p : (ρ → ℂ) × Matrix ρ ρ ℂ}
    (hH :
      (localExtensionMatrix
        energy p.1 attachment p.2).IsHermitian)
    (e : (X.State × ρ) ≃ (X.State × ρ)) :
    letI : Fintype R.PhysicalState := R.physicalFintype
    letI : DecidableEq R.PhysicalState :=
      R.physicalDecidableEq
    ∀ s q,
      (physicalLeafSpectralBasis R.basis
          (C.unitaryEigenvectorMatrix hH e))ᴴ *
          physicalLeafExtendedProbeFamily
            R G attachment anchor oldProbe oldOrigin
              newProbe s q *
          physicalLeafSpectralBasis R.basis
            (C.unitaryEigenvectorMatrix hH e) =
        unitaryLeafExtendedProbeMatrixFamily
          G anchor C oldProbe newProbe hH e s q := by
  letI : Fintype R.PhysicalState := R.physicalFintype
  letI : DecidableEq R.PhysicalState :=
    R.physicalDecidableEq
  intro s q
  rw [conjTranspose_physicalLeafSpectralBasis,
    physicalLeafSpectralBasis]
  calc
    (C.unitaryEigenvectorMatrix hH e)ᴴ *
          (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ *
          physicalLeafExtendedProbeFamily
            R G attachment anchor oldProbe oldOrigin
              newProbe s q *
          (tensorIdentityBasis (ρ := ρ) R.basis *
            C.unitaryEigenvectorMatrix hH e) =
        (C.unitaryEigenvectorMatrix hH e)ᴴ *
          (((tensorIdentityBasis (ρ := ρ) R.basis)ᴴ *
            physicalLeafExtendedProbeFamily
              R G attachment anchor oldProbe oldOrigin
                newProbe s q *
            tensorIdentityBasis (ρ := ρ) R.basis) *
            C.unitaryEigenvectorMatrix hH e) := by
      simp only [Matrix.mul_assoc]
    _ =
        (C.unitaryEigenvectorMatrix hH e)ᴴ *
          (leafExtendedPhysicalProbeFamily
            G attachment anchor oldProbe newProbe s q *
            C.unitaryEigenvectorMatrix hH e) := by
      rw [tensorIdentityBasis_coordinate_physicalLeafExtendedProbeFamily
        R G attachment anchor oldProbe oldOrigin newProbe s q]
    _ =
        unitaryLeafExtendedProbeMatrixFamily
          G anchor C oldProbe newProbe hH e s q := by
      simp [unitaryLeafExtendedProbeMatrixFamily,
        LocalExtensionEigenbranchChart.unitaryProbeMatrixFamily,
        LocalExtensionEigenbranchChart.unitaryProbeMatrix,
        Matrix.star_eq_conjTranspose,
        Matrix.mul_assoc]

/-- **Physical-local exact leaf-extension law.**  Maximal projective rank
and every observer's transition connectivity can be extended while the
Hamiltonian changes by exactly one onsite term and one two-factor
parent--leaf interaction.  The returned spectral matrices are exact
coordinates of probes acting on only the inherited factor or the new
factor. -/
theorem
    exists_maximallyProjective_physicalLocalGoodObserverFamily_leafExtension
    (X : GoodObserverSpectralSystem.{u})
    (R :
      @GoodObserverSpectralSystem.PhysicalRealization
        X X.stateFintype X.stateDecidableEq)
    (root : X.Observer)
    (ρ : Type u) [Fintype ρ] [DecidableEq ρ]
    (anchor other : ρ) (hother : other ≠ anchor)
    (hcard : 2 ≤ Fintype.card ρ) :
    letI : Fintype X.State := X.stateFintype
    letI : DecidableEq X.State := X.stateDecidableEq
    letI : ∀ s, Fintype (X.Probe s) :=
      X.probeFintype
    letI : Fintype R.PhysicalState := R.physicalFintype
    letI : DecidableEq R.PhysicalState :=
      R.physicalDecidableEq
    ∃ coefficient : X.Probe root → ℝ,
      let parentPhysical :=
        realMatrixFamilyCombination
          (R.physicalProbe root) coefficient
      ∃ attachment : Matrix X.State X.State ℂ,
        attachment =
            realMatrixFamilyCombination
              (X.transition root) coefficient ∧
        ∃ n : ℕ,
          let shift : ρ → ℂ :=
            fun r =>
              (codedIntegerLayerShift anchor n r : ℂ)
          let G : X.Observer → SimpleGraph X.State :=
            fun s =>
              transitionFamilySupportGraph
                (X.transition s)
          ∃ C : LocalExtensionEigenbranchChart
              (fun i => (X.energy i : ℂ))
                shift attachment,
            ∃ oldProbe :
                ∀ s : X.Observer,
                  Sum (GraphEdge (G s))
                    (NonanchorLayer anchor) →
                    Matrix X.State X.State ℂ,
              ∃ oldOrigin :
                  ∀ s p, ∃ i : X.Probe s,
                    oldProbe s p = X.transition s i,
              ∃ newProbe :
                  Sum
                    (TransitionSupportEdge attachment × ρ)
                    (NonanchorLayer anchor) →
                    Matrix ρ ρ ℂ,
                ∃ q :
                    Fin
                      (localExtensionSliceParameterCount ρ) →
                      ℝ,
                  let p :=
                    realLocalExtensionParameter
                      (localExtensionSliceParameter q)
                  ∃ hH :
                      (localExtensionMatrix
                        (fun i => (X.energy i : ℂ))
                        p.1 attachment p.2).IsHermitian,
                    ∃ e :
                        (X.State × ρ) ≃
                          (X.State × ρ),
                      let nextEnergy :=
                        C.realBranchEnergy
                          (fun i => (X.energy i : ℂ))
                          shift attachment p
                      let nextTransition :=
                        unitaryLeafExtendedProbeMatrixFamily
                          G anchor C oldProbe newProbe hH e
                      let V :=
                        C.unitaryEigenvectorMatrix hH e
                      let basis :=
                        physicalLeafSpectralBasis R.basis V
                      let physicalHamiltonian :=
                        physicalLeafHamiltonian
                          R.hamiltonian parentPhysical
                          p.1 p.2
                      let physicalProbe :=
                        physicalLeafExtendedProbeFamily
                          R G attachment anchor oldProbe
                            oldOrigin newProbe
                      (∀ i,
                        nextEnergy i =
                          hH.eigenvalues (e i)) ∧
                      localExtensionMatrix
                          (fun i => (X.energy i : ℂ))
                          p.1 attachment p.2 =
                        V *
                          Matrix.diagonal
                            (fun i => (nextEnergy i : ℂ)) *
                          Vᴴ ∧
                      MaximallyProjectiveEnergy nextEnergy ∧
                      HermitianObserverFamilyGood
                        nextTransition ∧
                      basisᴴ * basis =
                        (1 :
                          Matrix (X.State × ρ)
                            (X.State × ρ) ℂ) ∧
                      basis * basisᴴ =
                        (1 :
                          Matrix
                            (R.PhysicalState × ρ)
                            (R.PhysicalState × ρ) ℂ) ∧
                      physicalHamiltonian =
                        basis *
                          Matrix.diagonal
                            (fun i => (nextEnergy i : ℂ)) *
                          basisᴴ ∧
                      ∀ s probe,
                        nextTransition s probe =
                          basisᴴ *
                            physicalProbe s probe *
                          basis := by
  letI : Fintype X.State := X.stateFintype
  letI : DecidableEq X.State := X.stateDecidableEq
  letI : Fintype R.PhysicalState := R.physicalFintype
  letI : DecidableEq R.PhysicalState :=
    R.physicalDecidableEq
  letI : Nonempty X.State := X.stateNonempty
  letI : Nontrivial X.State := X.stateNontrivial
  letI : Fintype X.Observer := X.observerFintype
  letI : DecidableEq X.Observer :=
    X.observerDecidableEq
  letI : Nonempty X.Observer := X.observerNonempty
  letI : ∀ s, Fintype (X.Probe s) :=
    X.probeFintype
  letI : ∀ s, DecidableEq (X.Probe s) :=
    X.probeDecidableEq
  letI : Nontrivial ρ :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨attachment, ⟨coefficient, hattachment⟩,
      n, C, oldProbe, holdOrigin, newProbe, q,
      hH, e, he, hdiagonal, hmax, hgood⟩ :=
    exists_maximallyProjective_unitaryGoodObserverFamily_leafExtension
      X.energy X.energy_maximallyProjective
      X.transition X.observerFamily_good root
      anchor other hother hcard
  let parentPhysical :=
    realMatrixFamilyCombination
      (R.physicalProbe root) coefficient
  let shift : ρ → ℂ :=
    fun r =>
      (codedIntegerLayerShift anchor n r : ℂ)
  let G : X.Observer → SimpleGraph X.State :=
    fun s =>
      transitionFamilySupportGraph (X.transition s)
  let p : (ρ → ℂ) × Matrix ρ ρ ℂ :=
    realLocalExtensionParameter
      (localExtensionSliceParameter q)
  let nextEnergy :=
    C.realBranchEnergy
      (fun i => (X.energy i : ℂ))
      shift attachment p
  let nextTransition :=
    unitaryLeafExtendedProbeMatrixFamily
      G anchor C oldProbe newProbe hH e
  let V := C.unitaryEigenvectorMatrix hH e
  let basis :=
    physicalLeafSpectralBasis R.basis V
  let physicalHamiltonian :=
    physicalLeafHamiltonian R.hamiltonian
      parentPhysical p.1 p.2
  let physicalProbe :=
    physicalLeafExtendedProbeFamily
      R G attachment anchor oldProbe holdOrigin newProbe
  have hparentCoordinate :
      R.basisᴴ * parentPhysical * R.basis =
        attachment := by
    calc
      R.basisᴴ * parentPhysical * R.basis =
          realMatrixFamilyCombination
            (X.transition root) coefficient := by
        symm
        exact realMatrixFamilyCombination_coordinate
          R.basis (R.physicalProbe root)
          (X.transition root) coefficient
          (R.transition_eq_coordinate root)
      _ = attachment := hattachment.symm
  have hphysicalCoordinate :
      (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ *
          physicalHamiltonian *
          tensorIdentityBasis (ρ := ρ) R.basis =
        localExtensionMatrix
          (fun i => (X.energy i : ℂ))
          p.1 attachment p.2 := by
    exact
      tensorIdentityBasis_coordinate_physicalLeafHamiltonian
        R.basis R.hamiltonian parentPhysical
        (fun i => (X.energy i : ℂ))
        p.1 attachment p.2
        R.star_basis_mul_basis
        R.hamiltonian_coordinate
        hparentCoordinate
  have hTensorLeft :
      (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ *
          tensorIdentityBasis (ρ := ρ) R.basis =
        (1 :
          Matrix (X.State × ρ) (X.State × ρ) ℂ) :=
    star_tensorIdentityBasis_mul_self
      R.basis R.star_basis_mul_basis
  have hTensorRight :
      tensorIdentityBasis (ρ := ρ) R.basis *
          (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ =
        (1 :
          Matrix (R.PhysicalState × ρ)
            (R.PhysicalState × ρ) ℂ) :=
    tensorIdentityBasis_mul_star_self
      R.basis R.basis_mul_star_basis
  have hVLeft :
      Vᴴ * V =
        (1 :
          Matrix (X.State × ρ)
            (X.State × ρ) ℂ) := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      C.star_unitaryEigenvectorMatrix_mul_self hH e
  have hVRight :
      V * Vᴴ =
        (1 :
          Matrix (X.State × ρ)
            (X.State × ρ) ℂ) := by
    simpa [V, Matrix.star_eq_conjTranspose] using
      C.unitaryEigenvectorMatrix_mul_star_self hH e
  have hbasisLeft :
      basisᴴ * basis =
        (1 :
          Matrix (X.State × ρ)
            (X.State × ρ) ℂ) := by
    exact physicalLeafSpectralBasis_star_mul_self
      R.basis V R.star_basis_mul_basis hVLeft
  have hbasisRight :
      basis * basisᴴ =
        (1 :
          Matrix (R.PhysicalState × ρ)
            (R.PhysicalState × ρ) ℂ) := by
    exact physicalLeafSpectralBasis_mul_star_self
      R.basis V R.basis_mul_star_basis hVRight
  have hphysicalRecover :
      physicalHamiltonian =
        tensorIdentityBasis (ρ := ρ) R.basis *
          localExtensionMatrix
            (fun i => (X.energy i : ℂ))
            p.1 attachment p.2 *
          (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ := by
    calc
      physicalHamiltonian =
          (1 :
            Matrix (R.PhysicalState × ρ)
              (R.PhysicalState × ρ) ℂ) *
            physicalHamiltonian *
            (1 :
              Matrix (R.PhysicalState × ρ)
                (R.PhysicalState × ρ) ℂ) := by
        simp
      _ =
          (tensorIdentityBasis (ρ := ρ) R.basis *
              (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ) *
            physicalHamiltonian *
            (tensorIdentityBasis (ρ := ρ) R.basis *
              (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ) := by
        rw [hTensorRight]
      _ =
          tensorIdentityBasis (ρ := ρ) R.basis *
            ((tensorIdentityBasis (ρ := ρ) R.basis)ᴴ *
              physicalHamiltonian *
              tensorIdentityBasis (ρ := ρ) R.basis) *
            (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ =
          tensorIdentityBasis (ρ := ρ) R.basis *
            localExtensionMatrix
              (fun i => (X.energy i : ℂ))
              p.1 attachment p.2 *
            (tensorIdentityBasis (ρ := ρ) R.basis)ᴴ := by
        rw [hphysicalCoordinate]
  have hdiagonal' :
      localExtensionMatrix
          (fun i => (X.energy i : ℂ))
          p.1 attachment p.2 =
        V *
          Matrix.diagonal
            (fun i => (nextEnergy i : ℂ)) *
          Vᴴ := by
    simpa [V, nextEnergy,
      Matrix.star_eq_conjTranspose] using hdiagonal
  have hphysicalDiagonal :
      physicalHamiltonian =
        basis *
          Matrix.diagonal
            (fun i => (nextEnergy i : ℂ)) *
          basisᴴ := by
    rw [hphysicalRecover, hdiagonal']
    simp [basis, V, physicalLeafSpectralBasis,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hprobeCoordinate :
      ∀ s probe,
        nextTransition s probe =
          basisᴴ * physicalProbe s probe * basis := by
    intro s probe
    symm
    exact physicalLeafSpectralBasis_coordinate_probeFamily
      R G anchor C oldProbe holdOrigin newProbe hH e s probe
  exact ⟨coefficient, attachment, hattachment,
    n, C, oldProbe, holdOrigin, newProbe, q,
    hH, e, he, hdiagonal', hmax, hgood,
    hbasisLeft, hbasisRight,
    hphysicalDiagonal, hprobeCoordinate⟩

/-- A good spectral system together with one exact physical realization. -/
structure PhysicallyRealizedGoodObserverSpectralSystem where
  spectral : GoodObserverSpectralSystem.{u}
  realization :
    @GoodObserverSpectralSystem.PhysicalRealization
      spectral spectral.stateFintype spectral.stateDecidableEq

/-- A parent choice at every successive leaf attachment.  Unlike a bare
dimension list, this retains the complete rooted-tree growth history. -/
def ObserverLeafSchedule
    (S : Type u) : List ℕ → Type (u + 1)
  | [] => PUnit
  | _ :: tailDimensions =>
      S ×
        ObserverLeafSchedule
          (LeafExtendedObserver S) tailDimensions

/-- **Arbitrary rooted-tree physical growth.**  Every finite sequence of
local dimensions and every choice of an existing parent at each step has a
physically realized maximally projective system.  Each recursive step is
the exact onsite-plus-parent--leaf construction proved above. -/
theorem exists_physicallyRealized_leafSchedule
    (X : GoodObserverSpectralSystem.{u})
    (R :
      @GoodObserverSpectralSystem.PhysicalRealization
        X X.stateFintype X.stateDecidableEq)
    (dimensions : List ℕ)
    (hdimensions :
      ∀ q ∈ dimensions, 2 ≤ q)
    (schedule :
      ObserverLeafSchedule X.Observer dimensions) :
    ∃ Z : PhysicallyRealizedGoodObserverSpectralSystem.{u},
      Z.spectral.stateCard =
        X.stateCard * dimensions.prod ∧
      Z.spectral.observerCard =
        X.observerCard + dimensions.length := by
  cases dimensions with
  | nil =>
      let Z : PhysicallyRealizedGoodObserverSpectralSystem.{u} :=
        { spectral := X
          realization := R }
      exact ⟨Z, by simp [Z], by simp [Z]⟩
  | cons q tailDimensions =>
      change
        X.Observer ×
          ObserverLeafSchedule
            (LeafExtendedObserver X.Observer)
              tailDimensions at schedule
      obtain ⟨root, tailSchedule⟩ := schedule
      have hq : 2 ≤ q :=
        hdimensions q (by simp)
      have htailDimensions :
          ∀ r ∈ tailDimensions, 2 ≤ r := by
        intro r hr
        exact hdimensions r (by simp [hr])
      let Local : Type u := ULift.{u} (Fin q)
      let anchorFin : Fin q :=
        ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hq⟩
      let otherFin : Fin q := ⟨1, hq⟩
      let anchor : Local := ULift.up anchorFin
      let other : Local := ULift.up otherFin
      have hotherFin : otherFin ≠ anchorFin := by
        intro h
        have := congrArg Fin.val h
        simp [otherFin, anchorFin] at this
      have hother : other ≠ anchor := by
        intro h
        exact hotherFin (ULift.up_injective h)
      have hLocalCard : Fintype.card Local = q := by
        simp [Local]
      letI : Nontrivial Local :=
        Fintype.one_lt_card_iff_nontrivial.mp
          (by
            simpa [hLocalCard] using
              (lt_of_lt_of_le (by decide : 1 < 2) hq))
      letI : Fintype X.State := X.stateFintype
      letI : DecidableEq X.State :=
        X.stateDecidableEq
      letI : Nonempty X.State := X.stateNonempty
      letI : Nontrivial X.State := X.stateNontrivial
      letI : Fintype X.Observer := X.observerFintype
      letI : DecidableEq X.Observer :=
        X.observerDecidableEq
      letI : Nonempty X.Observer := X.observerNonempty
      letI : ∀ s, Fintype (X.Probe s) :=
        X.probeFintype
      letI : ∀ s, DecidableEq (X.Probe s) :=
        X.probeDecidableEq
      letI : Fintype R.PhysicalState :=
        R.physicalFintype
      letI : DecidableEq R.PhysicalState :=
        R.physicalDecidableEq
      obtain ⟨coefficient, attachment, hattachment,
          n, C, oldProbe, holdOrigin, newProbe, parameter,
          hH, e, he, hdiagonal, hmax, hgood,
          hbasisLeft, hbasisRight,
          hphysicalDiagonal, hprobeCoordinate⟩ :=
        exists_maximallyProjective_physicalLocalGoodObserverFamily_leafExtension
          X R root Local anchor other hother
            (by simpa [hLocalCard] using hq)
      let parentPhysical :=
        realMatrixFamilyCombination
          (R.physicalProbe root) coefficient
      let shift : Local → ℂ :=
        fun r =>
          (codedIntegerLayerShift anchor n r : ℂ)
      let G : X.Observer → SimpleGraph X.State :=
        fun s =>
          transitionFamilySupportGraph (X.transition s)
      let p : (Local → ℂ) × Matrix Local Local ℂ :=
        realLocalExtensionParameter
          (localExtensionSliceParameter parameter)
      let nextEnergy : X.State × Local → ℝ :=
        C.realBranchEnergy
          (fun i => (X.energy i : ℂ))
          shift attachment p
      let nextTransition :
          ∀ s : LeafExtendedObserver X.Observer,
            LeafExtendedProbeIndex
                G attachment anchor s →
              Matrix (X.State × Local)
                (X.State × Local) ℂ :=
        unitaryLeafExtendedProbeMatrixFamily
          G anchor C oldProbe newProbe hH e
      let V := C.unitaryEigenvectorMatrix hH e
      let basis :=
        physicalLeafSpectralBasis R.basis V
      let physicalHamiltonian :=
        physicalLeafHamiltonian R.hamiltonian
          parentPhysical p.1 p.2
      let physicalProbe :=
        physicalLeafExtendedProbeFamily
          R G attachment anchor oldProbe holdOrigin newProbe
      let Y : GoodObserverSpectralSystem.{u} :=
        { State := X.State × Local
          Observer := LeafExtendedObserver X.Observer
          Probe :=
            LeafExtendedProbeIndex G attachment anchor
          stateFintype := inferInstance
          stateDecidableEq := inferInstance
          stateNonempty := inferInstance
          stateNontrivial := inferInstance
          observerFintype := inferInstance
          observerDecidableEq := inferInstance
          observerNonempty := inferInstance
          probeFintype :=
            fun s =>
              leafExtendedProbeIndexFintype
                G attachment anchor s
          probeDecidableEq :=
            fun s =>
              leafExtendedProbeIndexDecidableEq
                G attachment anchor s
          energy := nextEnergy
          energy_maximallyProjective := hmax
          transition := nextTransition
          observerFamily_good := hgood }
      let RY :
          @GoodObserverSpectralSystem.PhysicalRealization
            Y Y.stateFintype Y.stateDecidableEq :=
        { PhysicalState := R.PhysicalState × Local
          physicalFintype := inferInstance
          physicalDecidableEq := inferInstance
          basis := basis
          star_basis_mul_basis := hbasisLeft
          basis_mul_star_basis := hbasisRight
          hamiltonian := physicalHamiltonian
          hamiltonian_eq_diagonal :=
            hphysicalDiagonal
          physicalProbe := physicalProbe
          transition_eq_coordinate :=
            hprobeCoordinate }
      obtain ⟨Z, hZstate, hZobserver⟩ :=
        exists_physicallyRealized_leafSchedule
          Y RY tailDimensions htailDimensions tailSchedule
      refine ⟨Z, ?_, ?_⟩
      · rw [hZstate]
        have hYstate :
            Y.stateCard =
              X.stateCard * q := by
          simp [Y, GoodObserverSpectralSystem.stateCard,
            hLocalCard]
        rw [hYstate]
        simp only [List.prod_cons]
        ac_rfl
      · rw [hZobserver]
        have hYobserver :
            Y.observerCard =
              X.observerCard + 1 := by
          simp [Y, GoodObserverSpectralSystem.observerCard]
        rw [hYobserver]
        simp only [List.length_cons]
        omega
termination_by dimensions.length

/-- Every local carrier of dimension at least three has a one-site
physically realized seed: the identity basis, a diagonal maximally
projective onsite Hamiltonian, and the full finite Hermitian probe family. -/
theorem exists_physicallyRealized_completeOneSiteSeed
    (I : Type u) [Fintype I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I) :
    ∃ Z : PhysicallyRealizedGoodObserverSpectralSystem.{u},
      Z.spectral.stateCard = Fintype.card I ∧
      Z.spectral.observerCard = 1 := by
  obtain ⟨X, hstate, hobserver⟩ :=
    exists_completeObserverSpectralSystem I PUnit hcard
  letI : Fintype X.State := X.stateFintype
  letI : DecidableEq X.State := X.stateDecidableEq
  let R :
      @GoodObserverSpectralSystem.PhysicalRealization
        X X.stateFintype X.stateDecidableEq :=
    { PhysicalState := X.State
      physicalFintype := X.stateFintype
      physicalDecidableEq := X.stateDecidableEq
      basis := 1
      star_basis_mul_basis := by
        simp
      basis_mul_star_basis := by
        simp
      hamiltonian :=
        Matrix.diagonal
          (fun i => (X.energy i : ℂ))
      hamiltonian_eq_diagonal := by
        simp
      physicalProbe := X.transition
      transition_eq_coordinate := by
        intro s q
        simp }
  exact ⟨⟨X, R⟩, hstate,
    by simpa using hobserver⟩

/-- Any rooted-tree schedule grown from a local dimension at least three
has an exact physical realization and the full finite recurrence law. -/
theorem exists_completeOneSiteSeed_physicalLeafSchedule_with_fullRecurrence
    (I : Type u) [Fintype I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I) :
    ∃ Base :
        PhysicallyRealizedGoodObserverSpectralSystem.{u},
      Base.spectral.stateCard = Fintype.card I ∧
      Base.spectral.observerCard = 1 ∧
      ∀ (dimensions : List ℕ)
        (_hdimensions :
          ∀ q ∈ dimensions, 2 ≤ q)
        (_schedule :
          ObserverLeafSchedule
            Base.spectral.Observer dimensions),
        ∃ Z :
            PhysicallyRealizedGoodObserverSpectralSystem.{u},
          Z.spectral.stateCard =
              Fintype.card I * dimensions.prod ∧
          Z.spectral.observerCard =
              1 + dimensions.length ∧
          Z.spectral.HasFiniteEntropyPlateauFuture := by
  obtain ⟨Base, hBaseState, hBaseObserver⟩ :=
    exists_physicallyRealized_completeOneSiteSeed I hcard
  refine ⟨Base, hBaseState, hBaseObserver, ?_⟩
  intro dimensions hdimensions schedule
  obtain ⟨Z, hZstate, hZobserver⟩ :=
    exists_physicallyRealized_leafSchedule
      Base.spectral Base.realization
      dimensions hdimensions schedule
  refine ⟨Z, ?_, ?_, Z.spectral.hasFiniteEntropyPlateauFuture⟩
  · simpa [hBaseState] using hZstate
  · simpa [hBaseObserver] using hZobserver

end

end GaloisForLFunctions.HTGeometry
