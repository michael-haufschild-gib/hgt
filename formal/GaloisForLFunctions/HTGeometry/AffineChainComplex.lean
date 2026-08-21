import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# The affine chain complex of a set, and the cone operator

For a set `K`, the tuples `Fin (n+1) → K` form a simplicial set — the codiscrete one — whose free
`R`-module simplicial object has, as its alternating face map complex, the complex of affine chains
on `K`: formal `R`-combinations of `(n+1)`-tuples of points, with the usual alternating boundary.

Prepending a fixed point `b` to every tuple is the **cone operator**.  Its defining identity

  `∂ (b ∗ c) + b ∗ (∂ c) = c − ε(c) · b`

holds because the zeroth face of a cone is the original simplex and the higher faces of a cone are
the cones of the faces.  This is the elementary engine behind barycentric subdivision: the
subdivision operator and the chain homotopy exhibiting it as homotopic to the identity are both
built by coning, and the boundary identity is what makes the induction close.
-/

open CategoryTheory Simplicial AlgebraicTopology Opposite

namespace GaloisForLFunctions.HTGeometry

universe u

variable (R : Type u) [CommRing R] (K : Type u)

/-- The free `R`-module simplicial object on the codiscrete simplicial set of a type: the
`n`-simplices are formal `R`-combinations of `(n+1)`-tuples of points. -/
noncomputable def affSimplicial : SimplicialObject (ModuleCat.{u} R) where
  obj n := ModuleCat.of R ((Fin (n.unop.len + 1) → K) →₀ R)
  map f := ModuleCat.ofHom
    (Finsupp.lmapDomain R R (fun v => v ∘ (SimplexCategory.Hom.toOrderHom f.unop)))
  map_id := by
    intro n
    ext v
    simp [Finsupp.lmapDomain]
  map_comp := by
    intro a b c f g
    ext v
    simp [Finsupp.lmapDomain]
    rfl

/-- The affine chain complex of `K` with coefficients in `R`. -/
noncomputable def affChainComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  (AlternatingFaceMapComplex.obj (affSimplicial R K))

theorem affChainComplex_X (n : ℕ) :
    (affChainComplex R K).X n = ModuleCat.of R ((Fin (n + 1) → K) →₀ R) := rfl

/-- The `i`-th face of an affine simplex omits the `i`-th vertex. -/
theorem affSimplicial_δ {n : ℕ} (i : Fin (n + 2)) (v : Fin (n + 2) → K) :
    (affSimplicial R K).δ i (Finsupp.single v (1 : R))
      = Finsupp.single (v ∘ i.succAbove) (1 : R) := by
  show Finsupp.mapDomain (fun w : Fin (n + 2) → K =>
      w ∘ (SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i))) (Finsupp.single v 1)
    = Finsupp.single (v ∘ i.succAbove) (1 : R)
  rw [Finsupp.mapDomain_single]
  congr 1

/-- The boundary of an affine simplex is the alternating sum of its faces. -/
theorem d_single {n : ℕ} (v : Fin (n + 2) → K) :
    ((affChainComplex R K).d (n + 1) n).hom (Finsupp.single v (1 : R))
      = ∑ i : Fin (n + 2), Finsupp.single (v ∘ i.succAbove) ((-1 : R) ^ (i : ℕ)) := by
  show ((AlternatingFaceMapComplex.obj (affSimplicial R K)).d (n + 1) n).hom _ = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  show ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (affSimplicial R K).δ i :
      (affSimplicial R K) _⦋n + 1⦌ ⟶ (affSimplicial R K) _⦋n⦌)).hom (Finsupp.single v 1) = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, affSimplicial_δ]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ((-1 : ℤ) ^ (i : ℕ)) • (Finsupp.single (v ∘ i.succAbove) (1 : R))
      = Finsupp.single (v ∘ i.succAbove) ((-1 : R) ^ (i : ℕ))
  rw [Finsupp.smul_single]
  congr 1
  simp

/-! ## The cone operator -/

/-- Prepending a fixed point to every tuple: the cone operator on affine chains. -/
noncomputable def coneMap (b : K) (n : ℕ) :
    (affChainComplex R K).X n ⟶ (affChainComplex R K).X (n + 1) :=
  ModuleCat.ofHom (Finsupp.lmapDomain R R (fun v : Fin (n + 1) → K => Fin.cons b v))

theorem coneMap_single (b : K) (n : ℕ) (v : Fin (n + 1) → K) :
    (coneMap R K b n).hom (Finsupp.single v (1 : R))
      = Finsupp.single (Fin.cons b v) (1 : R) := by
  show Finsupp.mapDomain
      (fun w : Fin (n + 1) → K => (Fin.cons b w : Fin (n + 2) → K)) (Finsupp.single v 1) = _
  rw [Finsupp.mapDomain_single]

/-- The zeroth face of a cone is the original simplex. -/
theorem cons_comp_succAbove_zero {n : ℕ} (b : K) (v : Fin (n + 1) → K) :
    (Fin.cons b v : Fin (n + 2) → K) ∘ (0 : Fin (n + 2)).succAbove = v := by
  funext k
  simp

/-- The higher faces of a cone are the cones of the faces. -/
theorem cons_comp_succAbove_succ {n : ℕ} (b : K) (v : Fin (n + 2) → K) (j : Fin (n + 2)) :
    (Fin.cons b v : Fin (n + 3) → K) ∘ (j.succ).succAbove = Fin.cons b (v ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · simp
  · intro m
    simp [Fin.succ_succAbove_succ]

end GaloisForLFunctions.HTGeometry
