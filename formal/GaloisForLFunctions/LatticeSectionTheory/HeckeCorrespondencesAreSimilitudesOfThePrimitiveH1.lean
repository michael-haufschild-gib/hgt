import GaloisForLFunctions.LatticeSectionTheory.TheKunnethRiemannRoch
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface

/-!
# Hecke correspondences are similitudes of the primitive `h¹`

The Hecke correspondence `T_a = √a · ψ_a` of the scaling surface (ACS) fixes the fibre degree
`x · H`, multiplies `x · V` by `a`, and multiplies the intersection form and the
Castelnuovo–Severi defect by `a`. In the language of sections:

* **On the pole plane** (`kunnethH0_heckeCorrespondence`). `T_a` sends the bidegree `(b₁, b₂)` to
  `(b₁, a b₂)`: the boost by `½ log a` followed by the scaling by `√a`. The Künneth count of
  `T_a x` is `h⁰_ℤ(x·H) h⁰_ℤ(a x·V)`.
* **On the primitive part** (`primitiveH1_heckeCorrespondence`). The primitive `h¹` is multiplied
  by `a`: `h¹_prim(T_a x) = a h¹_prim(x)`, and so is the Euler characteristic
  (`eulerChar_heckeCorrespondence`). `T_a` is a similitude of ratio `a` — the degree of the
  correspondence — exactly as `deg(φ ∘ ψ) = deg φ · deg ψ` for isogenies.

So the effectivity of a Hecke correspondence is its degree: it rescales the primitive `h¹`
without changing its sign, and it acts on the Künneth part as a boost. The sign of the primitive
`h¹` is invariant under the whole Hecke monoid; no Hecke operator produces it.
-/

noncomputable section

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry

/-- The primitive `h¹` of the Künneth count: `h⁰ + h² − χ − h¹_K`. -/
def primitiveH1 {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E) (x : E) : ℝ :=
  kunnethH0 S x + kunnethH0 S (0 - x) - eulerChar S 0 0 x - kunnethH1 S x

theorem primitiveH1_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E) (x : E) :
    primitiveH1 S x = S.defect x x / 2 :=
  kunneth_h1_sub_eq_half_defect S x

/-- **Hecke on the pole plane**: `T_a` sends the bidegree `(b₁, b₂)` to `(b₁, a b₂)`. -/
theorem kunnethH0_heckeCorrespondence {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    kunnethH0 scalingSurface (heckeCorrespondence a x) =
      arithH0 (scalingSurface.pair x scalingSurface.H) *
        arithH0 (a * scalingSurface.pair x scalingSurface.V) := by
  rw [kunnethH0, pair_heckeCorrespondence_H ha, pair_heckeCorrespondence_V ha]

/-- **Hecke on the primitive part**: `h¹_prim(T_a x) = a · h¹_prim(x)`. -/
theorem primitiveH1_heckeCorrespondence {a : ℝ} (ha : 0 ≤ a) (x : ScalingCycle) :
    primitiveH1 scalingSurface (heckeCorrespondence a x) = a * primitiveH1 scalingSurface x := by
  rw [primitiveH1_eq, primitiveH1_eq, defect_heckeCorrespondence ha]; ring

/-- `T_a` multiplies the Euler characteristic by `a`. -/
theorem eulerChar_heckeCorrespondence {a : ℝ} (ha : 0 ≤ a) (x : ScalingCycle) :
    eulerChar scalingSurface 0 0 (heckeCorrespondence a x) = a * eulerChar scalingSurface 0 0 x := by
  simp only [eulerChar, sub_zero, add_zero, pair_heckeCorrespondence ha]; ring

/-- **The sign of the primitive `h¹` is Hecke-invariant**: for `a > 0`, `h¹_prim(T_a x) ≥ 0` iff
`h¹_prim(x) ≥ 0`. -/
theorem primitiveH1_heckeCorrespondence_nonneg_iff {a : ℝ} (ha : 0 < a) (x : ScalingCycle) :
    0 ≤ primitiveH1 scalingSurface (heckeCorrespondence a x) ↔ 0 ≤ primitiveH1 scalingSurface x := by
  rw [primitiveH1_heckeCorrespondence ha.le]
  exact mul_nonneg_iff_of_pos_left ha

end GaloisForLFunctions.LatticeSectionTheory
