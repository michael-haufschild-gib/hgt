import GaloisForLFunctions.HTGeometry.NerveSubcomplex
import GaloisForLFunctions.HTGeometry.SimplicialMayerVietoris
import GaloisForLFunctions.HTGeometry.NerveHomotopy

/-!
# Mayer--Vietoris for an order complex, cut at a minimal element

Removing a minimal element of a poset cuts its order complex into the star of that element, which is
contractible, and the full subcomplex on the complement.  The two meet in the link.  So the homology
of the order complex is controlled by the complement and the link alone — the induction step of a
Solomon--Tits argument.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u c

variable {P : Type u} [PartialOrder P]

/-- The elements above a minimal element form a poset with a least element. -/
instance starOrderBot (p : P) : OrderBot ({q : P | p ≤ q} : Type u) where
  bot := ⟨p, le_rfl⟩
  bot_le q := q.2

/-- **The star of a point is contractible.** -/
theorem isZero_homology_star (p : P) {C : Type c} [Category.{v} C] [Limits.HasCoproducts.{u} C]
    [Preadditive C] [CategoryWithHomology C] (R : C) (i : ℕ) (hi : 1 ≤ i) :
    Limits.IsZero (((nerveSubcomplex {q : P | p ≤ q} : SSet.{u})).homology R i) :=
  Limits.IsZero.of_iso (isZero_homology_of_orderBot R i hi)
    (nerveSubcomplexHomologyIso _ R i)

/-- **Cutting an order complex at a minimal element.**  If the complement of a minimal element has no
homology in degree `i`, and the link none in degree `i - 1`, then the whole order complex has none in
degree `i`.

The star contributes nothing because it has a least element; this is where minimality is used, both
to make the two pieces cover and to make the star a cone. -/
theorem isZero_homology_nerve_of_minimal (p : P) (hmin : ∀ q, q ≤ p → q = p)
    {C : Type c} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
    (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) (hi : 1 ≤ i)
    (hcompl : Limits.IsZero (((nerveSubcomplex {q : P | q ≠ p} : SSet.{u})).homology R i))
    (hlink : Limits.IsZero
      (((nerveSubcomplex ({q : P | p ≤ q} ∩ {q : P | q ≠ p}) : SSet.{u})).homology R j)) :
    Limits.IsZero (((nerve P).chainComplex R).homology i) := by
  refine isZero_homology_of_mayerVietoris (nerve P) R (nerveSubcomplex {q : P | p ≤ q})
    (nerveSubcomplex {q : P | q ≠ p}) (nerveSubcomplex_star_sup_compl p hmin) i j hij
    (isZero_homology_star p R i hi) hcompl ?_
  rw [← nerveSubcomplex_inter]
  exact hlink

/-- **The link, described as the elements strictly above a minimal element.** -/
theorem star_inter_compl_eq (p : P) :
    ({q : P | p ≤ q} ∩ {q : P | q ≠ p}) = {q : P | p < q} := by
  ext q
  exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨le_of_lt h, ne_of_gt h⟩⟩

/-- **Cutting at a minimal element, with the link named.** -/
theorem isZero_homology_nerve_of_minimal' (p : P) (hmin : ∀ q, q ≤ p → q = p)
    {C : Type c} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
    (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) (hi : 1 ≤ i)
    (hcompl : Limits.IsZero (((nerveSubcomplex {q : P | q ≠ p} : SSet.{u})).homology R i))
    (hlink : Limits.IsZero (((nerveSubcomplex {q : P | p < q} : SSet.{u})).homology R j)) :
    Limits.IsZero (((nerve P).chainComplex R).homology i) :=
  isZero_homology_nerve_of_minimal p hmin R i j hij hi hcompl
    (by rw [star_inter_compl_eq p]; exact hlink)

/-- **Cutting at a minimal element, with an injectivity hypothesis in place of acyclicity of the
link.**  In degree one the link is connected rather than acyclic, and what the vanishing needs is
that its homology injects into the homology of the two pieces — the content of the reduced
statement, expressed without an augmented complex. -/
theorem isZero_homology_nerve_of_minimal_mono (p : P) (hmin : ∀ q, q ≤ p → q = p)
    {C : Type c} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
    (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) (hi : 1 ≤ i)
    (hcompl : Limits.IsZero (((nerveSubcomplex {q : P | q ≠ p} : SSet.{u})).homology R i))
    (hmono : Mono (HomologicalComplex.homologyMap
      (mvChainShortComplex (nerve P) R (nerveSubcomplex {q : P | p ≤ q})
        (nerveSubcomplex {q : P | q ≠ p})).f j)) :
    Limits.IsZero (((nerve P).chainComplex R).homology i) :=
  isZero_homology_of_mayerVietoris_mono (nerve P) R (nerveSubcomplex {q : P | p ≤ q})
    (nerveSubcomplex {q : P | q ≠ p}) (nerveSubcomplex_star_sup_compl p hmin) i j hij
    (isZero_homology_star p R i hi) hcompl hmono

end GaloisForLFunctions.HTGeometry
