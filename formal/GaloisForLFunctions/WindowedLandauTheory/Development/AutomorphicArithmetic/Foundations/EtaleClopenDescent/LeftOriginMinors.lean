import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechMinorCocycle
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge

/-! The rows for the left origin equations have one coordinate each.
Their ordered minors form a cocycle and factor by the selected
homogeneous coordinates. -/

noncomputable section

namespace GlobalTheory.WH

variable {R : Type} [CommRing R]

/-- Scaling the rows of an ordered minor multiplies the determinant by
the product of the row factors on its index set. -/
theorem orderedMinor_mul_rows {κ : Type} [LinearOrder κ] {p : ℕ}
    (a : κ → R) (ρ : κ → Fin p → R) (s : Finset κ) :
    orderedMinor (fun i j => a i * ρ i j) s = (∏ i ∈ s, a i) * orderedMinor ρ s := by
  by_cases h : s.card = p
  · let e := s.orderEmbOfFin h
    have hp : (∏ i : Fin p, a (e i)) = ∏ i ∈ s, a i := by
      conv_rhs => rw [← Finset.map_orderEmbOfFin_univ s h]
      rw [Finset.prod_map]
      rfl
    simp only [orderedMinor, dif_pos h]
    rw [← hp, ← Matrix.det_diagonal, ← Matrix.det_mul]
    apply congrArg Matrix.det
    ext i j
    simp only [Matrix.of_apply, Matrix.diagonal_mul, e]
  · simp only [orderedMinor, dif_neg h, mul_zero]

variable {d : ℕ}

/-- The chart row at i and the origin equation for i are supported
on the same coordinate column. The origin has its own chart row. -/
abbrev leftOriginRowIndex (l : Fin (d + 1) ⊕ₗ Fin d) : Fin (d + 1) :=
  Sum.elim id Fin.succ (ofLex l)

abbrev leftOriginRowFactor (X : Fin (d + 1) → R) (l : Fin (d + 1) ⊕ₗ Fin d) : R :=
  Sum.elim (fun _ => 1) (fun i => X i.succ) (ofLex l)

/-- Row matrix for the chart differentials and the left origin
equations, with zeros outside their designated coordinate. -/
def leftOriginRows (X : Fin (d + 1) → R) (l : Fin (d + 1) ⊕ₗ Fin d)
    (i : Fin (d + 1)) : R :=
  leftOriginRowFactor X l * (if leftOriginRowIndex l = i then 1 else 0)

theorem leftOriginRows_sum (X : Fin (d + 1) → R) (l : Fin (d + 1) ⊕ₗ Fin d) :
    ∑ i, leftOriginRows X l i = leftOriginRowFactor X l := by
  classical
  rw [Finset.sum_eq_single (leftOriginRowIndex l)]
  · simp only [leftOriginRows, if_true, mul_one]
  · intro i _ hi
    rw [leftOriginRows, if_neg hi.symm, mul_zero]
  · exact fun h => False.elim (h (Finset.mem_univ _))

theorem wd_leftOriginMinors_eq_zero {k E : Type} [Field k] [Algebra k R]
    [AddCommGroup E] [Module k E] (act : R →ₐ[k] Module.End k E)
    (X : Fin (d + 1) → R) (v : E) :
    wd (fun i => act (leftOriginRowFactor X i))
      (fun L => act (orderedMinor (leftOriginRows X) L) v) = 0 := by
  simpa only [mul_one, leftOriginRows_sum] using
    wd_orderedMinor_eq_zero act (leftOriginRows X) (fun _ => 1) v

/-- On a joined subset, the factors for the left chart rows are one. -/
theorem orderedMinor_leftOriginRows_factor {k : Type} [Field k] [Algebra k R]
    (X : Fin (d + 1) → R) (I : Finset (Fin (d + 1))) (L : Finset (Fin d)) :
    orderedMinor (leftOriginRows X) (uni I L) =
      (∏ i ∈ L, X i.succ) * algebraMap k R
        (orderedMinor (fun l i => if leftOriginRowIndex l = i then 1 else 0) (uni I L)) := by
  have hp : (∏ l ∈ uni I L, leftOriginRowFactor X l) = ∏ i ∈ L, X i.succ := by
    rw [uni, Finset.prod_map, Finset.prod_disjSum]
    simp only [Equiv.coe_toEmbedding, leftOriginRowFactor, ofLex_toLex, Sum.elim_inl,
      Sum.elim_inr, Finset.prod_const_one, one_mul]
  unfold leftOriginRows
  rw [orderedMinor_mul_rows, hp, map_orderedMinor]
  congr 1
  congr 1
  funext i j
  split_ifs <;> simp

/-- A nonzero origin minor uses the left chart at zero and one
coordinate weight for each omitted chart. -/
theorem leftOriginMinor_support (X : Fin (d + 1) → R)
    (I : Finset (Fin (d + 1))) (L : Finset (Fin d))
    (h : orderedMinor (leftOriginRows X) (uni I L) ≠ 0) :
    0 ∈ I ∧ L.map ⟨Fin.succ, Fin.succ_injective d⟩ = Iᶜ := by
  classical
  have hcard : (uni I L).card = d + 1 := by
    by_contra hn
    exact h (by simp only [orderedMinor, dif_neg hn])
  let e := (uni I L).orderEmbOfFin hcard
  have hne : (Matrix.of fun a b => leftOriginRows X (e a) b).det ≠ 0 := by
    simpa only [orderedMinor, dif_pos hcard, e] using h
  have hhit (i : Fin (d + 1)) : ∃ l ∈ uni I L, leftOriginRowIndex l = i := by
    by_contra hn
    push Not at hn
    apply hne (Matrix.det_eq_zero_of_column_eq_zero i fun a => ?_)
    simp only [Matrix.of_apply, leftOriginRows,
      if_neg (hn (e a) (Finset.orderEmbOfFin_mem _ _ _)), mul_zero]
  have hcover (i : Fin (d + 1)) (hi : i ∉ I) : ∃ j ∈ L, j.succ = i := by
    obtain ⟨t, ht, hti⟩ := hhit i
    rcases ht₀ : ofLex t with a | a
    · have ht' : t = toLex (Sum.inl a) := (toLex_ofLex t).symm.trans (congrArg toLex ht₀)
      subst t
      have ha : a ∈ I := by simpa [uni] using ht
      exact (hi (hti ▸ ha)).elim
    · have ht' : t = toLex (Sum.inr a) := (toLex_ofLex t).symm.trans (congrArg toLex ht₀)
      subst t
      exact ⟨a, by simpa [uni] using ht, hti⟩
  refine ⟨by
    by_contra h0
    obtain ⟨i, _, hi⟩ := hcover 0 h0
    exact Fin.succ_ne_zero i hi, ?_⟩
  let f : Fin d ↪ Fin (d + 1) := ⟨Fin.succ, Fin.succ_injective d⟩
  have hp : Iᶜ ⊆ L.map f := by
    intro i hi
    obtain ⟨j, hj, hj'⟩ := hcover i (Finset.mem_compl.mp hi)
    exact Finset.mem_map.mpr ⟨j, hj, hj'⟩
  have hs : (L.map f).card ≤ Iᶜ.card := by
    rw [Finset.card_map, Finset.card_compl, Fintype.card_fin]
    rw [card_uni] at hcard
    omega
  exact (Finset.eq_of_subset_of_card_le hp hs).symm

private theorem leftOriginMinor_eq_prod (X : Fin (d + 1) → R)
    (s : Finset (Fin (d + 1) ⊕ₗ Fin d)) (hs : s.card = d + 1)
    (f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d)
    (hmem : ∀ a, f a ∈ s) (hf : StrictMono f) (hidx : ∀ a, leftOriginRowIndex (f a) = a) :
    orderedMinor (leftOriginRows X) s = ∏ a, leftOriginRowFactor X (f a) := by
  have he : ∀ a, s.orderEmbOfFin hs a = f a :=
    fun a => (congrFun (Finset.orderEmbOfFin_unique hs hmem hf) a).symm
  rw [orderedMinor, dif_pos hs]
  simp only [he, leftOriginRows, hidx]
  rw [show (Matrix.of fun i j => leftOriginRowFactor X (f i) * (if i = j then 1 else 0)) =
      Matrix.diagonal (fun i => leftOriginRowFactor X (f i)) from ?_]
  · exact Matrix.det_diagonal
  · ext i j
    by_cases h : i = j <;> simp [h]

theorem leftOriginMinor_chartOnly (X : Fin (d + 1) → R) :
    orderedMinor (leftOriginRows X) (uni Finset.univ ∅) = 1 := by
  rw [leftOriginMinor_eq_prod X _ (by simp only [card_uni, Finset.card_univ, Fintype.card_fin,
    Finset.card_empty, add_zero]) (fun a => toLex (Sum.inl a))
      (fun _ => by simp [uni]) Sum.Lex.inl_strictMono (fun _ => rfl)]
  simp [leftOriginRowFactor]

theorem leftOriginMinor_originOnly (X : Fin (d + 1) → R) :
    orderedMinor (leftOriginRows X) (uni {0} Finset.univ) = ∏ l : Fin d, X l.succ := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Fin d :=
    Fin.cases (toLex (Sum.inl 0)) (fun l => toLex (Sum.inr l))
  have hmem (a : Fin (d + 1)) : f a ∈ uni {0} Finset.univ := by
    cases a using Fin.cases <;> simp [f, uni]
  have hf : StrictMono f := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact (lt_irrefl _ hab).elim
      | succ l => exact Sum.Lex.inl_lt_inr _ _
    | succ i =>
      cases b using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hab).elim
      | succ l => exact Sum.Lex.inr_strictMono (Fin.succ_lt_succ_iff.mp hab)
  have hidx (a : Fin (d + 1)) : leftOriginRowIndex (f a) = a := by
    cases a using Fin.cases <;> rfl
  have hs : (uni ({0} : Finset (Fin (d + 1))) (Finset.univ : Finset (Fin d))).card = d + 1 := by
    rw [card_uni, Finset.card_singleton, Finset.card_univ, Fintype.card_fin, add_comm]
  rw [leftOriginMinor_eq_prod X _ hs f hmem hf hidx, Fin.prod_univ_succ]
  simp [f, leftOriginRowFactor]

end GlobalTheory.WH
