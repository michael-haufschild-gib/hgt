import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ClosedTrivialityLocus
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeOpenTriviality

/-! The triviality locus of a normalized bundle on an abelian square is clopen over
an affine base with perfect section models. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.LineBundleSections GlobalTheory.AbLaw.Seesaw

namespace GlobalTheory.AbLaw.Cube

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  {L : LB (A ⊗ A).left}

/-- Triviality on the two axes makes the field-fibre triviality locus open as well as closed. -/
theorem isClopen_fieldFibreTriviality
    (hA : IsAbelianScheme A) (hL : L.IsLB)
    (P : PerfectSections (A ⊗ A).hom L) (Q : PerfectSections (A ⊗ A).hom (dual L))
    (h₁ : ∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) :
    IsClopen (fieldFibreTriviality (A ⊗ A).hom L) := by
  let f := (A ⊗ A).hom
  have h := hA.tensor hA
  haveI := h.proper
  haveI := h.smooth
  haveI := h.geomConnected
  haveI : GeometricallyIntegral f := geometricallyIntegral_of_quasiCompact_of_smooth_of_geometricallyConnected f
  refine ⟨isClosed_triviality_locus hL P Q, isOpen_iff_forall_mem_open.mpr ?_⟩
  intro x hx
  obtain ⟨K, _, α, Y, π, g, hker, H, ht⟩ := hx
  obtain ⟨r, hr, T, hT⟩ := trivial_on_basicOpen_of_trivial_fibre hA hL P h₁ h₂ α H ht
  let U := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  refine ⟨PrimeSpectrum.basicOpen r, ?_, (PrimeSpectrum.basicOpen r).isOpen, ?_⟩
  · intro y hy
    let k := y.asIdeal.ResidueField
    let β := algebraMap R k
    let b := Spec.map (CommRingCat.ofHom β)
    let Z := pullback f b
    let π' := pullback.fst f b
    let g' := pullback.snd f b
    have hβ : RingHom.ker β = y.asIdeal := Ideal.ker_algebraMap_residueField _
    have hu : IsUnit (β r) := by
      apply Ne.isUnit
      change r ∉ RingHom.ker β
      rwa [hβ]
    have hsub : Set.range π' ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      have e : f (π' z) = b (g' z) :=
        congrArg (fun m : Z ⟶ Spec (CommRingCat.of R) => m z) pullback.condition
      have hm : π' z ∈ U := by
        change r ∉ (f (π' z)).asIdeal
        rw [e]
        change β r ∉ (g' z).asIdeal
        exact fun m => (g' z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ m hu)
      exact ⟨⟨π' z, hm⟩, rfl⟩
    let j := IsOpenImmersion.lift U.ι π' hsub
    have hj : j ≫ U.ι = π' := IsOpenImmersion.lift_fac U.ι π' hsub
    have ht' : ∃ t : (L.pull π').Gen, t.IsGen := by
      rw [← hj]
      exact ⟨_, hT.pullGen (fun _ : PUnit => U.ι) (fun _ => 1) j⟩
    exact ⟨k, inferInstance, β, Z, π', g', hβ, IsPullback.of_hasPullback _ _, ht'⟩
  · change r ∉ x.asIdeal
    rwa [← hker]

end GlobalTheory.AbLaw.Cube
