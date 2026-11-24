import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechMinorCocycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination

/-! Ordered minors for the homogeneous equations of the projective
diagonal and their coordinate-row specializations. -/

noncomputable section

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] {d : ℕ} (T : WeightedChartSystem k d S E)

/-- Coordinate rows together with the two nonzero entries of each
homogeneous diagonal equation. -/
def minorRows (t : Fin (d + 1) ⊕ₗ DiagonalIndex d) : Fin (d + 1) → S :=
  Sum.elim (fun i => Pi.single i 1)
    (fun l m => (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
      if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0) (ofLex t)

private lemma mem_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ)
    (t : β ⊕ₗ κ) : t ∈ uni I J ↔ (∃ i ∈ I, t = toLex (Sum.inl i)) ∨ ∃ l ∈ J, t = toLex (Sum.inr l) := by
  simp only [uni, Finset.mem_map, Finset.mem_disjSum, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨Sum.inl i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
    · exact ⟨Sum.inr l, Or.inr ⟨l, hl, rfl⟩, rfl⟩

private lemma orderedMinor_eq {κ : Type} [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (s : Finset κ)
    (f : Fin p → κ) (hc : s.card = p) (hs : ∀ x, f x ∈ s) (hf : StrictMono f) :
    orderedMinor ρ s = (Matrix.of fun a b => ρ (f a) b).det := by
  unfold orderedMinor
  rw [dif_pos hc, ← Finset.orderEmbOfFin_unique hc hs hf]

private lemma rowMu_inr (l : DiagonalIndex d) (m : Fin (d + 1)) : T.minorRows (toLex (Sum.inr l)) m =
    (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
      if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0 := rfl

private lemma rowMu_inl (i m : Fin (d + 1)) : T.minorRows (toLex (Sum.inl i)) m =
    (Pi.single i 1 : Fin (d + 1) → S) m := rfl

theorem sum_minorRows_eq_weight (t : Fin (d + 1) ⊕ₗ DiagonalIndex d) :
    ∑ b, T.minorRows t b * (1 : Fin (d + 1) → S) b = Sum.elim (fun _ => (1 : S)) T.homogeneousMinor (ofLex t) := by
  obtain ⟨t, rfl⟩ := toLex.surjective t
  rcases t with i | l
  · simp [rowMu_inl]
  · simp only [rowMu_inr, Pi.one_apply, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl

private lemma rowMu_null (l : DiagonalIndex d) :
    ∑ m, T.minorRows (toLex (Sum.inr l)) m * ((T.Y m * (T.X m)⁻¹ : Sˣ) : S) = 0 := by
  simp only [rowMu_inr, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Units.val_mul]
  have h1 : ((T.X (ofLex l).1 : Sˣ) : S) * (((T.X (ofLex l).1)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  have h2 : ((T.X (ofLex l).2 : Sˣ) : S) * (((T.X (ofLex l).2)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  linear_combination ((T.Y (ofLex l).1 : S) * (T.Y (ofLex l).2 : S)) * (h1 - h2)

/-- A minor with rows only from the homogeneous equations vanishes. -/
theorem orderedMinor_left (L : Finset (DiagonalIndex d)) : orderedMinor T.minorRows (uni ∅ L) = 0 := by
  unfold orderedMinor
  split_ifs with h
  · set A : Matrix (Fin (d + 1)) (Fin (d + 1)) S :=
      Matrix.of fun a b => T.minorRows ((uni ∅ L).orderEmbOfFin h a) b with hA
    have hAv : A.mulVec (fun m => ((T.Y m * (T.X m)⁻¹ : Sˣ) : S)) = 0 := by
      funext a
      have hmem : (uni ∅ L).orderEmbOfFin h a ∈ uni ∅ L := Finset.orderEmbOfFin_mem _ _ _
      rw [mem_uni] at hmem
      rcases hmem with ⟨i, hi, _⟩ | ⟨l, _, hl⟩
      · simp at hi
      · simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, hl, Pi.zero_apply]
        exact rowMu_null T l
    have h0 := congrArg A.adjugate.mulVec hAv
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h0
    have h1 := congrFun h0 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    exact (Units.mul_left_eq_zero (T.Y 0 * (T.X 0)⁻¹)).1 h1
  · rfl

/-- The ordered minor of all coordinate rows is one. -/
theorem orderedMinor_univ : orderedMinor T.minorRows (uni Finset.univ ∅) = 1 := by
  rw [orderedMinor_eq T.minorRows _ (fun a => toLex (Sum.inl a)) (by simp [card_uni])
    (fun x => (mem_uni _ _ _).2 (Or.inl ⟨x, Finset.mem_univ _, rfl⟩))
    (fun a b h => Sum.Lex.inl_strictMono h)]
  have : (Matrix.of fun a b => T.minorRows (toLex (Sum.inl a)) b) = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) S) := by
    ext a b
    simp [rowMu_inl, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]

/-- The origin minor is triangular in the standard coordinate order. -/
theorem orderedMinor_top : orderedMinor T.minorRows (uni {0} (Finset.univ.map (diagonalIndexEmbedding 0).toEmbedding)) =
    (∏ l : Fin d, (T.X l.succ : S)) * (T.Y 0 : S) ^ d := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ DiagonalIndex d :=
    Fin.cons (toLex (Sum.inl 0)) fun l => toLex (Sum.inr (diagonalIndexEmbedding 0 l))
  have hf0 : f 0 = toLex (Sum.inl 0) := rfl
  have hfs : ∀ l : Fin d, f l.succ = toLex (Sum.inr (diagonalIndexEmbedding 0 l)) := fun _ => rfl
  have hmono : StrictMono f := by
    intro a b h
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ b => rw [hf0, hfs]; exact Sum.Lex.inl_lt_inr _ _
    | succ a =>
      induction b using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ b =>
        rw [hfs, hfs]
        exact Sum.Lex.inr_strictMono ((diagonalIndexEmbedding 0).strictMono (Fin.succ_lt_succ_iff.1 h))
  have hmem : ∀ x, f x ∈ uni {0} (Finset.univ.map (diagonalIndexEmbedding 0).toEmbedding) := by
    intro x
    induction x using Fin.cases with
    | zero => exact (mem_uni _ _ _).2 (Or.inl ⟨0, by simp, rfl⟩)
    | succ l => exact (mem_uni _ _ _).2 (Or.inr ⟨diagonalIndexEmbedding 0 l, by simp, rfl⟩)
  rw [orderedMinor_eq T.minorRows _ f (by simp [card_uni, add_comm]) hmem hmono]
  have hrow : ∀ (l : Fin d) (m : Fin (d + 1)), T.minorRows (f l.succ) m =
      (if m = l.succ then (T.X m * T.Y 0 : S) else 0) -
        if m = 0 then (T.X m * T.Y l.succ : S) else 0 := by
    intro l m
    have e1 : (ofLex (diagonalIndexEmbedding (0 : Fin (d + 1)) l)).1 = l.succ := by simp [diagonalIndexEmbedding]
    have e2 : (ofLex (diagonalIndexEmbedding (0 : Fin (d + 1)) l)).2 = 0 := rfl
    rw [hfs, rowMu_inr, e1, e2]
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp only [Matrix.of_apply, hf0, rowMu_inl, Pi.single_eq_same, one_mul, hrow]
    simp [Finset.prod_mul_distrib, Fin.succ_ne_zero]
  · intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.of_apply]
    induction i using Fin.cases with
    | zero =>
      rw [hf0, rowMu_inl]
      simp [(Fin.pos_iff_ne_zero.1 hij')]
    | succ l =>
      rw [hrow]
      have h1 : j ≠ l.succ := ne_of_gt hij'
      have h2 : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [h1, h2]

/-- Acting by the ordered row minors gives a cocycle for the
homogeneous diagonal weights and the coordinate weights one. -/
theorem wd_orderedChartMinor_eq_zero (m : E) :
    wd (fun t : Fin (d + 1) ⊕ₗ DiagonalIndex d =>
      T.act (Sum.elim (fun _ => 1) T.homogeneousMinor (ofLex t)))
      (fun s => T.act (orderedMinor T.minorRows s) m) = 0 := by
  have h := wd_orderedMinor_eq_zero T.act T.minorRows (fun _ => 1) m
  have hweights : (fun t => T.act (∑ b, T.minorRows t b * (1 : S))) =
      (fun t : Fin (d + 1) ⊕ₗ DiagonalIndex d =>
        T.act (Sum.elim (fun _ => 1) T.homogeneousMinor (ofLex t))) := by
    funext t
    exact congrArg T.act (sum_minorRows_eq_weight T t)
  rwa [hweights] at h

end GlobalTheory.WH.WeightedChartSystem
