import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedKoszulComponent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalLocalClass
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The determinant of the selected origin equations is a product
of their nonzero diagonal entries after expanding at the first row. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S M : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup M] [Module k M] {d : ℕ} (T : WeightedChartSystem k d S M)

/-- The chosen origin minor is the product of the coordinate
entries paired with the right denominator. -/
theorem orderedMinor_originSelection :
    orderedMinor T.minorRows
      (uni ({0} : Finset (Fin (d + 1))) (selectedIndices (diagonalIndexEmbedding 0))) =
      ∏ j : Fin d, (T.X j.succ : S) * (T.Y 0 : S) := by
  let K := Fin (d + 1) ⊕ₗ DiagonalIndex d
  let L : Finset K := uni {0} (selectedIndices (diagonalIndexEmbedding 0))
  let f : Fin (d + 1) → K := Fin.cases (toLex (Sum.inl 0))
    (fun i => toLex (Sum.inr (diagonalIndexEmbedding 0 i)))
  have hf : StrictMono f := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j => exact Sum.Lex.inl_lt_inr _ _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Nat.not_lt_zero _ hij).elim
      | succ j =>
        exact (joinedRight (ι := Fin (d + 1))).strictMono
          ((diagonalIndexEmbedding 0).strictMono (show i < j from Nat.lt_of_succ_lt_succ hij))
  have hmem (i : Fin (d + 1)) : f i ∈ L := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Finset.mem_map.mpr ⟨Sum.inl 0, by simp, rfl⟩
    · refine Finset.mem_map.mpr ⟨Sum.inr (diagonalIndexEmbedding 0 j), ?_, rfl⟩
      have hj : diagonalIndexEmbedding 0 j ∈ selectedIndices (diagonalIndexEmbedding 0) :=
        Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
      simpa using hj
  have hc : L.card = d + 1 := by
    change (uni ({0} : Finset (Fin (d + 1))) (selectedIndices (diagonalIndexEmbedding 0))).card = _
    rw [card_uni, Finset.card_singleton, selectedIndices, Finset.card_map, Finset.card_univ,
      Fintype.card_fin, Nat.add_comm]
  have hrow : (fun j => f j) = L.orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc hmem hf
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) S := Matrix.of fun i j => T.minorRows (f i) j
  change orderedMinor T.minorRows L = _
  rw [orderedMinor, dif_pos hc, ← hrow]
  change A.det = _
  have h₀ (j : Fin (d + 1)) : A 0 j = if j = 0 then 1 else 0 := by
    change (Pi.single (0 : Fin (d + 1)) 1 : Fin (d + 1) → S) j = _
    rw [Pi.single_apply]
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · have hsucc : (0 : Fin (d + 1)).succAbove = Fin.succ := funext Fin.zero_succAbove
    rw [h₀, if_pos rfl, Fin.val_zero, pow_zero, one_mul, one_mul, hsucc]
    have hA : A.submatrix Fin.succ Fin.succ =
        Matrix.diagonal (fun j : Fin d => (T.X j.succ : S) * (T.Y 0 : S)) := by
      have he (i : Fin d) : diagonalIndexEmbedding 0 i = toLex (i.succ, 0) := by
        change toLex ((0 : Fin (d + 1)).succAbove i, 0) = _
        rw [Fin.zero_succAbove]
      apply Matrix.ext
      intro i j
      change T.minorRows (toLex (Sum.inr (diagonalIndexEmbedding 0 i))) j.succ = _
      simp only [he, minorRows, ofLex_toLex, Sum.elim_inr, Fin.succ_ne_zero,
        if_false, sub_zero, Fin.succ_inj, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst j
        simp only [if_true]
      · rw [if_neg (Ne.symm hij), if_neg hij]
    rw [hA, Matrix.det_diagonal]
  · intro j _ hj
    rw [h₀, if_neg hj, mul_zero, zero_mul]
  · exact fun h => (h (Finset.mem_univ 0)).elim

end GlobalTheory.WH.WeightedChartSystem
