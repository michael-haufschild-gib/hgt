import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisSup
import GaloisForLFunctions.HTGeometry.ConstHomologyMono

/-!
# Mayer--Vietoris with an injectivity hypothesis on the intersection

The vanishing statement extracted from the Mayer--Vietoris sequence of two subcomplexes needs, in
degree `i`, that the two pieces have no homology there and that the connecting map out of degree `i`
is zero.  The connecting map is zero as soon as the map from the homology of the intersection to the
homology of the two pieces is injective in the next degree down — a strictly weaker demand than the
vanishing of that homology, and the only form available in the bottom degree, where the homology of
a nonempty intersection never vanishes.

Injectivity is supplied by contractibility of the intersection: a homologically constant simplicial
set is a homology retract of everything it maps into.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u w

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (X : SSet.{w}) (R : C) (A B : X.Subcomplex)

/-- Injectivity on one of the two components suffices for injectivity into the biproduct. -/
theorem mono_homologyMap_mvChainFst_of_right (j : ℕ)
    (h : Mono (SSet.homologyMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R j)) :
    Mono (HomologicalComplex.homologyMap (mvChainFst X R A B) j) := by
  have hcomp : HomologicalComplex.homologyMap (mvChainFst X R A B) j
      ≫ HomologicalComplex.homologyMap
        (biprod.snd : (A : SSet.{w}).chainComplex R ⊞ (B : SSet.{w}).chainComplex R ⟶ _) j
      = SSet.homologyMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R j := by
    rw [← HomologicalComplex.homologyMap_comp, mvChainFst, biprod.lift_snd]
  have : Mono (HomologicalComplex.homologyMap (mvChainFst X R A B) j
      ≫ HomologicalComplex.homologyMap
        (biprod.snd : (A : SSet.{w}).chainComplex R ⊞ (B : SSet.{w}).chainComplex R ⟶ _) j) := by
    rw [hcomp]
    exact h
  exact mono_of_mono (HomologicalComplex.homologyMap (mvChainFst X R A B) j)
    (HomologicalComplex.homologyMap
      (biprod.snd : (A : SSet.{w}).chainComplex R ⊞ (B : SSet.{w}).chainComplex R ⟶ _) j)

/-- **Vanishing from Mayer--Vietoris under injectivity on the intersection.**  The two pieces have no
homology in degree `i`, and the homology of the intersection injects into that of the two pieces one
degree down; then the union has no homology in degree `i`. -/
theorem isZero_homology_of_mayerVietoris_sup_mono (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hA : Limits.IsZero (((A : SSet.{w}).chainComplex R).homology i))
    (hB : Limits.IsZero (((B : SSet.{w}).chainComplex R).homology i))
    (hmono : Mono (HomologicalComplex.homologyMap (mvChainFst X R A B) j)) :
    Limits.IsZero ((((A ⊔ B : X.Subcomplex) : SSet.{w}).chainComplex R).homology i) := by
  have hS := mvSupChainShortExact X R A B
  have hδ : hS.δ i j hij = 0 := (hS.homology_exact₁ i j hij).mono_g_iff.1 hmono
  exact (hS.homology_exact₃ i j hij).isZero_X₂
    ((isZero_homology_biprod _ _ i hA hB).eq_zero_of_src _) hδ

/-- **Vanishing from Mayer--Vietoris over a contractible intersection.**  If the intersection is
homologically constant at one of its vertices, the union inherits the vanishing of the two pieces,
in every degree that has a predecessor — including degree one, where the intersection itself has
nonvanishing homology. -/
theorem isZero_homology_of_mayerVietoris_sup_of_const (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hA : Limits.IsZero (((A : SSet.{w}).chainComplex R).homology i))
    (hB : Limits.IsZero (((B : SSet.{w}).chainComplex R).homology i))
    (p : ((A ⊓ B : X.Subcomplex) : SSet.{w}) _⦋0⦌)
    (hconst : SSet.homologyMap (SSet.const (X := ((A ⊓ B : X.Subcomplex) : SSet.{w}))
      (Y := ((A ⊓ B : X.Subcomplex) : SSet.{w})) p) R j = 𝟙 _) :
    Limits.IsZero ((((A ⊔ B : X.Subcomplex) : SSet.{w}).chainComplex R).homology i) :=
  isZero_homology_of_mayerVietoris_sup_mono X R A B i j hij hA hB
    (mono_homologyMap_mvChainFst_of_right X R A B j
      (mono_homologyMap_of_homologyMap_const_id _ p R j hconst))

end

end GaloisForLFunctions.HTGeometry
