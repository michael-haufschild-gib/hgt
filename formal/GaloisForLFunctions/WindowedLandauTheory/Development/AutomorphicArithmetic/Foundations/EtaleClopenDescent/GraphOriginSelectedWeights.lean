import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphWeightsAtFixedOrigin
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphLocalDifferenceIdeal
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers

/-! The (d) selected homogeneous minors on the origin chart become
the differences of its affine coordinates under the two pullbacks. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct Matrix

namespace GlobalTheory.WH

variable {k F E L κ : Type} [Field k] [Field F] [Field E] [Field L] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

def graphOriginSelection : Fin d ↪o κ ⊕ₗ DiagonalIndex d :=
  (diagonalIndexEmbedding 0).trans joinedRight

theorem graphAffineWeight_at_origin_selected (j : Fin d) :
    graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0)
      (graphOriginSelection (κ := κ) j) =
        algebraMap F L (x j.succ / x 0) - j₂ (algebraMap F E (x j.succ / x 0)) := by
  have he : graphOriginSelection (κ := κ) j = toLex (Sum.inr (toLex (j.succ, 0))) := by
    change toLex (Sum.inr (toLex ((0 : Fin (d + 1)).succAbove j, 0))) = _
    rw [Fin.zero_succAbove]
  have h1 := graph_normalizedMinor h j₂ 0 0 n z 0 0 j.succ 0
  rw [he, graphAffineWeight, h1]
  rw [div_self ((map_ne_zero _).mpr (h.ne 0)), div_self ((map_ne_zero _).mpr
    ((map_ne_zero _).mpr (h.ne 0))), mul_one, one_mul]
  simp only [map_div₀]

variable (hL : IsFinCover k L x) [IsReduced ((rB k L x {0}) ⧸ originIdeal k L x)]

include hL in
/-- Under transversality, the selected graph weights generate the
kernel of the evaluation at the fixed origin fibre point. -/
theorem exists_graphOrigin_localWeights (hz : NormalizedDiagonalEquations h n z)
    (f : OriginFibrePoint k L x) (hf : IsFix (rB k L x {0}) f.1 j₂ (rB k E x {0}))
    (M : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : rB k L x {0}) (g : Fin d → rB k L x {0}), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * M m l)
    (hdet : (1 - M).det ≠ 0) :
    let R := loc (rB k L x {0}) f.1
    ∃ w : κ ⊕ₗ DiagonalIndex d → R,
      (∀ l, (w l : L) = graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) l) ∧
      Ideal.span (Set.range fun j => w (graphOriginSelection j)) =
        RingHom.ker (locEval (rB k L x {0}) f.1).toRingHom := by
  intro R
  let B := rB k L x {0}
  let r (l : κ ⊕ₗ DiagonalIndex d) := graphAffineWeight h j₂ (n := n) (z := z) (i := 0) (j := 0) l
  have hw (l : κ ⊕ₗ DiagonalIndex d) : r l ∈ R :=
    ((val_iff_loc B f.1 (r l) 0).mp (val_graphAffineWeight_at_fixedOrigin h j₂ hz f hf l)).1
  let w (l : κ ⊕ₗ DiagonalIndex d) : R := ⟨r l, hw l⟩
  refine ⟨w, fun _ => rfl, ?_⟩
  obtain ⟨A, hA, ha⟩ := exists_localRows_of_cleared f _ M hrow
  refine hL.span_localDifferenceCoordinates f A hA hdet (fun j => w (graphOriginSelection j)) ?_
  intro j
  change r (graphOriginSelection j) = _
  dsimp only [r]
  rw [graphAffineWeight_at_origin_selected, ha]
  rfl

end GlobalTheory.WH
