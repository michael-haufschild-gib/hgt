import GaloisForLFunctions.HTGeometry.FacetOrbitShift

/-!
# Quasi-Abelian facet-palette necessity

This module gives the exact checked interface between the finite Stanley--Reisner facet geometry
and the classical Capocasa--Catanese period theorem.  The project proves the integral facet-orbit
palette collision-free.  The analytic parent is represented by explicit quotient, discreteness,
noncompactness, incidence, and positive Hermitian-integrality certificates; it is not installed as
an axiom.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- Extend an integral exponent on one facet by zero outside that facet. -/
def facetExponentExtend
    {α : Type*} [DecidableEq α] (F : Finset α) (n : F → ℤ) : α → ℤ :=
  fun v => if hv : v ∈ F then n ⟨v, hv⟩ else 0

/-- Zero extension loses no integral facet coordinate. -/
theorem facetExponentExtend_injective
    {α : Type*} [DecidableEq α] (F : Finset α) :
    Function.Injective (facetExponentExtend F) := by
  intro n m h
  funext v
  have hv := congrFun h v.1
  simpa [facetExponentExtend, v.2] using hv

/-- All facets together with their complete integral exponent lattices. -/
abbrev FacetIntegralOrbitIndex
    {α : Type*} (facets : Finset (Finset α)) :=
  Σ F : facets, F.1 → ℤ

/-- The checked complex shift of one facet and one integral exponent on that facet. -/
def facetIntegralOrbitShift
    {α : Type*} [Fintype α] [DecidableEq α]
    (facets : Finset (Finset α)) (omega : α → ℝ) :
    FacetIntegralOrbitIndex facets → ℂ :=
  fun q => facetOrbitShift facets omega
    (q.1, facetExponentExtend q.1.1 q.2)

/-- Rationally independent vertex weights make the complete facet-integral palette injective. -/
theorem facetIntegralOrbitShift_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (facets : Finset (Finset α)) (omega : α → ℝ)
    (homega : LinearIndependent ℚ omega) :
    Function.Injective (facetIntegralOrbitShift facets omega) := by
  have hembed : Function.Injective
      (fun q : FacetIntegralOrbitIndex facets =>
        (q.1, facetExponentExtend q.1.1 q.2)) := by
    rintro ⟨F, n⟩ ⟨G, m⟩ h
    have hFG : F = G := congrArg Prod.fst h
    subst G
    have hnm : n = m := facetExponentExtend_injective F.1 (congrArg Prod.snd h)
    subst m
    rfl
  exact (facetOrbitShift_injective facets omega homega).comp hembed

/-- A literal certificate for the noncompact quasi-Abelian quotient attached to one facet.
`W` is the vector space after dividing by the identity component of the full period group;
`Gamma` is its discrete period lattice and `X` its quotient. -/
structure QuasiAbelianFacetCertificate
    (α : Type*) [DecidableEq α] (F : Finset α) where
  X : Type
  [topologyX : TopologicalSpace X]
  W : Type
  [addCommGroupW : AddCommGroup W]
  [moduleW : Module ℂ W]
  [topologyW : TopologicalSpace W]
  Gamma : AddSubgroup W
  [gammaDiscrete : DiscreteTopology Gamma]
  gammaClosed : IsClosed (Gamma : Set W)
  quotientMap : W → X
  quotientMap_surjective : Function.Surjective quotientMap
  quotientMap_eq_iff : ∀ x y, quotientMap x = quotientMap y ↔ x - y ∈ Gamma
  quotient_noncompact : ¬ @IsCompact X topologyX Set.univ
  vertexClass : α → W
  vertex_incidence : ∀ v, vertexClass v ∈ Gamma ↔ v ∉ F
  H : W → W → ℂ
  H_add_left : ∀ x y z, H (x + y) z = H x z + H y z
  H_smul_left : ∀ a x y, H (a • x) y = a * H x y
  H_hermitian : ∀ x y, H y x = star (H x y)
  H_positive : ∀ x, x ≠ 0 → 0 < (H x x).re
  H_integral_imaginary : ∀ x : Gamma, ∀ y : Gamma,
    ∃ n : ℤ, (H x y).im = n

/-- Integral facet lattice map into the certified period quotient. -/
def QuasiAbelianFacetCertificate.latticeClass
    {α : Type*} [DecidableEq α] {F : Finset α}
    (C : QuasiAbelianFacetCertificate α F) (n : F → ℤ) : C.X :=
  by
    letI := C.addCommGroupW
    letI := C.moduleW
    exact C.quotientMap (∑ v : F, (n v) • C.vertexClass v.1)

/-- The positive Hermitian-integrality clause of the generalized Riemann relations, with the
certificate's vector-space instances installed locally. -/
def QuasiAbelianFacetCertificate.HasGeneralizedRiemannRelations
    {α : Type*} [DecidableEq α] {F : Finset α}
    (C : QuasiAbelianFacetCertificate α F) : Prop := by
  letI := C.addCommGroupW
  letI := C.moduleW
  exact (∀ x, x ≠ 0 → 0 < (C.H x x).re) ∧
    (∀ x : C.Gamma, ∀ y : C.Gamma, ∃ n : ℤ, (C.H x y).im = n)

/-- Exact named analytic input supplied by full-period extraction and the
Capocasa--Catanese necessary direction.  Equality in a quotient lattice class may only occur when
the corresponding structural translations collide. -/
structure QuasiAbelianFacetPaletteInput
    (α : Type*) [Fintype α] [DecidableEq α]
    (facets : Finset (Finset α)) (omega : α → ℝ) where
  certificate : ∀ F : facets, QuasiAbelianFacetCertificate α F.1
  latticeClass_eq_implies_shift_eq : ∀ (F : facets) (n m : F.1 → ℤ),
    (certificate F).latticeClass n = (certificate F).latticeClass m →
      facetIntegralOrbitShift facets omega ⟨F, n⟩ =
        facetIntegralOrbitShift facets omega ⟨F, m⟩

/-- **Quasi-Abelian facet-palette necessity.** Every facet certificate has exact complement
incidence, a noncompact period quotient, a positive Hermitian form integral on its discrete period
lattice, and an injective complete integral facet orbit. -/
theorem quasiAbelianFacetPalette_necessity
    {α : Type*} [Fintype α] [DecidableEq α]
    (facets : Finset (Finset α)) (omega : α → ℝ)
    (homega : LinearIndependent ℚ omega)
    (input : QuasiAbelianFacetPaletteInput α facets omega) :
    ∀ F : facets,
      Function.Injective (input.certificate F).latticeClass ∧
      (∀ v, (input.certificate F).vertexClass v ∈
        (input.certificate F).Gamma ↔ v ∉ F.1) ∧
      (¬ @IsCompact (input.certificate F).X
        (input.certificate F).topologyX Set.univ) ∧
      (input.certificate F).HasGeneralizedRiemannRelations := by
  intro F
  have hshift := facetIntegralOrbitShift_injective facets omega homega
  have hlattice : Function.Injective (input.certificate F).latticeClass := by
    intro n m hnm
    have hs := input.latticeClass_eq_implies_shift_eq F n m hnm
    have hp : (⟨F, n⟩ : FacetIntegralOrbitIndex facets) = ⟨F, m⟩ := hshift hs
    cases hp
    rfl
  refine ⟨hlattice, (input.certificate F).vertex_incidence,
    (input.certificate F).quotient_noncompact, ?_⟩
  dsimp [QuasiAbelianFacetCertificate.HasGeneralizedRiemannRelations]
  letI := (input.certificate F).addCommGroupW
  letI := (input.certificate F).moduleW
  exact ⟨(input.certificate F).H_positive,
    (input.certificate F).H_integral_imaginary⟩

/-- Least-dimension consequence of the extraction theorem: if every full HT realization yields a
quasi-Abelian palette in the same ambient dimension, then `qaDim ≤ htDim`. -/
theorem quasiAbelianDimension_le_hypertranscendenceDimension
    (FullHTRealizable QuasiAbelianPaletteRealizable : ℕ → Prop)
    (qaDim htDim : ℕ)
    (hht : FullHTRealizable htDim)
    (hextract : ∀ d, FullHTRealizable d → QuasiAbelianPaletteRealizable d)
    (hqaLeast : ∀ d, QuasiAbelianPaletteRealizable d → qaDim ≤ d) :
    qaDim ≤ htDim :=
  hqaLeast htDim (hextract htDim hht)

end

end GaloisForLFunctions.HTGeometry
