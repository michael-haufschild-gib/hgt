import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The normalized augmented simplex contraction

Each monomial block in coordinate-facet descent is the augmented chain complex of a nonempty
full simplex.  This module records that fact in the normalized, nondegenerate model: the standard
simplex on `n + 1` vertices is homotopy equivalent to its augmentation point.  Consequently its
normalized chain complex is exact in every positive degree.

The construction uses the extra degeneracy of the standard simplex and the canonical homotopy
equivalence between the alternating and normalized complexes.  Thus it is the full all-degree
contraction, rather than only an Euler-characteristic or degree-zero calculation.
-/

open CategoryTheory CategoryTheory.Limits Simplicial
open AlgebraicTopology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The standard simplex on `n + 1` vertices, augmented to a point and linearized over `k`. -/
noncomputable def standardSimplexAugmentedModule (n : ℕ) :
    SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
      (sigmaConst.obj (ModuleCat.of k k))).obj
    (SSet.Augmented.stdSimplex.obj (SimplexCategory.mk n))

/-- The initial-vertex extra degeneracy survives linearization over `k`. -/
noncomputable def standardSimplexExtraDegeneracy (n : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (standardSimplexAugmentedModule k n) :=
  SimplicialObject.Augmented.ExtraDegeneracy.map
    (SSet.Augmented.StandardSimplex.extraDegeneracy (SimplexCategory.mk n))
    (sigmaConst.obj (ModuleCat.of k k))

/-- The unnormalized alternating simplex complex contracts to its augmentation point. -/
noncomputable def standardSimplexChainHomotopyEquivPoint (n : ℕ) :
    HomotopyEquiv
      ((SSet.stdSimplex.obj (SimplexCategory.mk n)).chainComplex (ModuleCat.of k k))
      ((ChainComplex.single₀ (ModuleCat k)).obj
        (SimplicialObject.Augmented.point.obj
          (standardSimplexAugmentedModule k n))) :=
  SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
    (standardSimplexExtraDegeneracy k n)

/-- **Full normalized augmented-simplex contraction.**

The normalized complex is the direct sum over nondegenerate simplices, hence over strictly
increasing vertex packets in the standard simplex.  It is homotopy equivalent to the single
augmentation object in degree zero. -/
noncomputable def standardSimplexNormalizedHomotopyEquivPoint (n : ℕ) :
    HomotopyEquiv
      ((SSet.stdSimplex.obj (SimplexCategory.mk n)).normalizedChainComplex
        (ModuleCat.of k k))
      ((ChainComplex.single₀ (ModuleCat k)).obj
        (SimplicialObject.Augmented.point.obj
          (standardSimplexAugmentedModule k n))) :=
  (SSet.homotopyEquivNormalizedChainComplex
      (SSet.stdSimplex.obj (SimplexCategory.mk n)) (ModuleCat.of k k)).symm.trans
    (standardSimplexChainHomotopyEquivPoint k n)

/-- Every positive degree of the normalized full-simplex complex is exact. -/
theorem standardSimplexNormalized_exactAt_succ (n q : ℕ) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk n)).normalizedChainComplex
      (ModuleCat.of k k)).ExactAt (q + 1) := by
  let e := standardSimplexNormalizedHomotopyEquivPoint k n
  letI : QuasiIso e.hom := e.quasiIso_hom
  rw [exactAt_iff_of_quasiIsoAt e.hom (q + 1)]
  exact HomologicalComplex.ExactAt.of_isZero
    (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 _ (q + 1) (by omega))

end

end GaloisForLFunctions.HTGeometry
