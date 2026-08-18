import GaloisForLFunctions.HTGeometry.ActiveQuasiAbelianPalette
import GaloisForLFunctions.HTGeometry.QuasiAbelianFacetPaletteCompletion

/-!
# Forgetting the active clause

An active quasi-Abelian palette is a quasi-Abelian palette with two extra pieces of data: the
maximal compact complex shadow together with the quotient by it, and faithfulness of the integral
facet lattice in that quotient.  Forgetting them produces a literal facet certificate whose
integral lattice class is still injective, because injectivity after a further quotient implies
injectivity before it.

Hence every ambient dimension admitting an active palette admits a quasi-Abelian palette, and the
intrinsic dimensions satisfy `qaDim ≤ aqaDim`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The facet certificate underlying an active facet presentation: the same period lattice,
quotient, incidence and Hermitian data, with the compact shadow and the active quotient
forgotten. -/
def ActiveQuasiAbelianFacetPresentation.toQuasiAbelianFacetCertificate
    {alpha : Type} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a) :
    QuasiAbelianFacetCertificate alpha F where
  X := P.X
  topologyX := P.topologyX
  W := Fin d → ℂ
  Gamma := P.Gamma
  gammaDiscrete := P.gammaDiscrete
  gammaClosed := P.gammaClosed
  quotientMap := fun w => P.quotientMap w
  quotientMap_surjective := P.quotientMap_surjective
  quotientMap_eq_iff := P.quotientMap_eq_iff
  quotient_noncompact := P.quotient_noncompact
  vertexClass := a
  vertex_incidence := P.vertex_incidence
  H := P.H
  H_add_left := P.H_add_left
  H_smul_left := P.H_smul_left
  H_hermitian := P.H_hermitian
  H_positive := P.H_positive
  H_integral_imaginary := P.H_integral_imaginary

/-- The certificate's lattice class is the active presentation's period class. -/
theorem ActiveQuasiAbelianFacetPresentation.latticeClass_toQuasiAbelianFacetCertificate
    {alpha : Type} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a) (n : F → ℤ) :
    P.toQuasiAbelianFacetCertificate.latticeClass n =
      P.quotientMap (facetLatticeVector a F n) := rfl

/-- **Active faithfulness implies ambient faithfulness.**  The lattice class of the forgotten
certificate is still injective. -/
theorem ActiveQuasiAbelianFacetPresentation.latticeClass_injective
    {alpha : Type} [DecidableEq alpha] {F : Finset alpha}
    {d : ℕ} {a : alpha → Fin d → ℂ}
    (P : ActiveQuasiAbelianFacetPresentation alpha F d a) :
    Function.Injective P.toQuasiAbelianFacetCertificate.latticeClass := by
  intro n k hnk
  apply P.activeFaithful
  show P.activeQuotient (P.quotientMap (facetLatticeVector a F n)) =
    P.activeQuotient (P.quotientMap (facetLatticeVector a F k))
  exact congrArg P.activeQuotient hnk

/-- A quasi-Abelian palette: one facet certificate with injective integral lattice class for every
facet of the complex. -/
structure QuasiAbelianPalette
    (alpha : Type) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha)) (d : ℕ) where
  /-- The translation vector attached to each vertex. -/
  vertex : alpha → Fin d → ℂ
  /-- The vertex vectors are rationally independent. -/
  vertex_independent : LinearIndependent ℚ vertex
  /-- The facet certificate. -/
  certificate : ∀ F : facets, QuasiAbelianFacetCertificate alpha F.1
  /-- Its integral lattice class is injective. -/
  certificate_latticeClass_injective :
    ∀ F : facets, Function.Injective (certificate F).latticeClass

/-- Forgetting the active clause of every facet. -/
def ActiveQuasiAbelianPalette.toQuasiAbelianPalette
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    {facets : Finset (Finset alpha)} {d : ℕ}
    (P : ActiveQuasiAbelianPalette alpha facets d) :
    QuasiAbelianPalette alpha facets d where
  vertex := P.vertex
  vertex_independent := P.vertex_independent
  certificate := fun F => (P.facet F).toQuasiAbelianFacetCertificate
  certificate_latticeClass_injective := fun F => (P.facet F).latticeClass_injective

/-- Quasi-Abelian palette realizability in ambient dimension `d`. -/
def QuasiAbelianPaletteRealizable
    (alpha : Type) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha)) (d : ℕ) : Prop :=
  Nonempty (QuasiAbelianPalette alpha facets d)

/-- Intrinsic quasi-Abelian palette dimension. -/
def quasiAbelianPaletteDimension
    (alpha : Type) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha)) : ℕ :=
  sInf {d | QuasiAbelianPaletteRealizable alpha facets d}

/-- Every active palette dimension is a quasi-Abelian palette dimension. -/
theorem quasiAbelianPaletteRealizable_of_activeQuasiAbelianPaletteRealizable
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    {facets : Finset (Finset alpha)} {d : ℕ}
    (h : ActiveQuasiAbelianPaletteRealizable.{0} alpha facets d) :
    QuasiAbelianPaletteRealizable alpha facets d :=
  ⟨h.some.toQuasiAbelianPalette⟩

/-- **Inequality (6): `qaDim ≤ aqaDim`.**  The active clause is an extra requirement, so its least
realization dimension is at least the quasi-Abelian one. -/
theorem quasiAbelianPaletteDimension_le_activeQuasiAbelianPaletteDimension
    (alpha : Type) [Fintype alpha] [DecidableEq alpha]
    (facets : Finset (Finset alpha))
    (hne : {d | ActiveQuasiAbelianPaletteRealizable.{0} alpha facets d}.Nonempty) :
    quasiAbelianPaletteDimension alpha facets ≤
      activeQuasiAbelianPaletteDimension.{0} alpha facets := by
  have hmem := Nat.sInf_mem hne
  exact Nat.sInf_le (quasiAbelianPaletteRealizable_of_activeQuasiAbelianPaletteRealizable hmem)

end

end GaloisForLFunctions.HTGeometry
