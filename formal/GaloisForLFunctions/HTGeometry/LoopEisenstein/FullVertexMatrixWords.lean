import GaloisForLFunctions.HTGeometry.LoopEisenstein.VertexParabolics
import GaloisForLFunctions.HTGeometry.LoopEisenstein.MatrixLaurentLeading

/-!
# Laurent boundaries of alternating full vertex matrices

Constant reduction controls the leading matrix at the standard vertex.
At the adjacent vertex only the upper-right residue can occur in degree
minus one. Alternating non-Iwahori factors preserve a nonzero extreme
coefficient even when every factor has infinitely many positive terms.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable (F : Type*) [Field F]

/-- The two full power-series vertex embeddings into Laurent matrices. -/
def vertexMatrixEmbedding (i : Bool) : PowerSeriesSL2 F →* SL2 (LaurentSeries F) :=
  if i then (sl2Rescale (laurentXUnit F)⁻¹).comp (powerSeriesSL2Map F)
  else powerSeriesSL2Map F

def vertexMatrixWord (L : List (Bool × PowerSeriesSL2 F)) : SL2 (LaurentSeries F) :=
  (L.map (fun p => vertexMatrixEmbedding F p.1 p.2)).prod

/-- The residue which detects departure from the common Iwahori. -/
def vertexBoundary (p : Bool × PowerSeriesSL2 F) : F :=
  if p.1 then PowerSeries.constantCoeff (p.2 0 1)
  else PowerSeries.constantCoeff (p.2 1 0)

@[simp] theorem vertexMatrixWord_nil : vertexMatrixWord F [] = 1 := rfl

@[simp] theorem vertexMatrixWord_cons (p : Bool × PowerSeriesSL2 F)
    (L : List (Bool × PowerSeriesSL2 F)) :
    vertexMatrixWord F (p :: L) = vertexMatrixEmbedding F p.1 p.2 * vertexMatrixWord F L := rfl

private theorem hasLeadAt_powerSeries_zero (p : PowerSeries F) :
    HasLeadAt (p : LaurentSeries F) 0 (PowerSeries.constantCoeff p) := by
  constructor
  · intro k hk
    rw [PowerSeries.coeff_coe, if_pos hk]
  · rw [PowerSeries.coeff_coe]
    simp only [lt_self_iff_false, if_false, Int.natAbs_zero,
      PowerSeries.coeff_zero_eq_constantCoeff]

theorem vertexMatrixEmbedding_false_hasLeadAt (p : PowerSeriesSL2 F) :
    MatrixHasLeadAt F (vertexMatrixEmbedding F false p) 0 (powerSeriesReduction F p) :=
  fun i j => hasLeadAt_powerSeries_zero F (p i j)

theorem vertexMatrixEmbedding_true_hasLeadAt (p : PowerSeriesSL2 F) :
    MatrixHasLeadAt F (vertexMatrixEmbedding F true p) (-1)
      (topRowMatrix F 0 (PowerSeries.constantCoeff (p 0 1))) := by
  have hx : (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) =
      HahnSeries.single (-1 : ℤ) (1 : F) := by
    rw [Units.val_inv_eq_inv_val, coe_laurentXUnit, HahnSeries.inv_single, inv_one]
  intro i j
  fin_cases i <;> fin_cases j
  · exact (hasLeadAt_powerSeries_zero F (p 0 0)).mono (by omega)
  · change HasLeadAt
      ((((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        (p 0 1 : LaurentSeries F)) (-1) (PowerSeries.constantCoeff (p 0 1))
    rw [hx]
    simpa only [add_zero, one_mul] using
      (hasLeadAt_laurent_single F (-1) 1).mul (hasLeadAt_powerSeries_zero F (p 0 1))
  · change HasLeadAt
      (((((laurentXUnit F)⁻¹)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        (p 1 0 : LaurentSeries F)) (-1) 0
    rw [inv_inv, coe_laurentXUnit]
    have h := (hasLeadAt_laurent_single F 1 1).mul (hasLeadAt_powerSeries_zero F (p 1 0))
    exact h.mono (by omega)
  · exact (hasLeadAt_powerSeries_zero F (p 1 1)).mono (by omega)

private theorem affine_vertex_head_boundary_aux (n : ℕ) :
    ∀ (a : PowerSeriesSL2 F) (L : List (Bool × PowerSeriesSL2 F)), L.length = n →
      (∀ p ∈ (true, a) :: L, vertexBoundary F p ≠ 0) →
      List.IsChain (fun p q : Bool × PowerSeriesSL2 F => p.1 ≠ q.1) ((true, a) :: L) →
      ∃ m : ℕ, 0 < m ∧ ∃ u v : F, (u ≠ 0 ∨ v ≠ 0) ∧
        MatrixHasLeadAt F (vertexMatrixWord F ((true, a) :: L)) (-(m : ℤ))
          (topRowMatrix F u v) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a L hlen hred halt
    have ha : PowerSeries.constantCoeff (a 0 1) ≠ 0 := hred (true, a) List.mem_cons_self
    cases L with
    | nil =>
      refine ⟨1, by omega, 0, PowerSeries.constantCoeff (a 0 1), Or.inr ha, ?_⟩
      change MatrixHasLeadAt F _ (-1) _
      simpa only [vertexMatrixWord_cons, vertexMatrixWord_nil, mul_one] using
        vertexMatrixEmbedding_true_hasLeadAt F a
    | cons p tail =>
      rcases p with ⟨i, c⟩
      cases i with
      | true =>
        exact False.elim ((List.isChain_cons.1 halt).1 (true, c) (by simp) rfl)
      | false =>
        have hc : powerSeriesReduction F c 1 0 ≠ 0 := hred (false, c) (by simp)
        have hAC := MatrixHasLeadAt.mul F (vertexMatrixEmbedding_true_hasLeadAt F a)
          (vertexMatrixEmbedding_false_hasLeadAt F c)
        cases tail with
        | nil =>
          refine ⟨1, by omega,
            PowerSeries.constantCoeff (a 0 1) * powerSeriesReduction F c 1 0,
            PowerSeries.constantCoeff (a 0 1) * powerSeriesReduction F c 1 1,
            Or.inl (mul_ne_zero ha hc), ?_⟩
          change MatrixHasLeadAt F _ (-1) _
          rw [add_zero, topRowMatrix_zero_mul] at hAC
          simpa only [vertexMatrixWord_cons, vertexMatrixWord_nil, mul_one,
            Matrix.SpecialLinearGroup.coe_mul] using hAC
        | cons q rest =>
          rcases q with ⟨j, b⟩
          cases j with
          | false =>
            exact False.elim ((List.isChain_cons.1 halt.tail).1 (false, b) (by simp) rfl)
          | true =>
            have hr : ∀ p ∈ (true, b) :: rest, vertexBoundary F p ≠ 0 := by
              intro p hp
              exact hred p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
            have hlt : rest.length < n := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨m, hm, u, v, huv, hB⟩ := ih rest.length hlt b rest rfl hr halt.tail.tail
            refine ⟨m + 1, by omega,
              PowerSeries.constantCoeff (a 0 1) * powerSeriesReduction F c 1 0 * u,
              PowerSeries.constantCoeff (a 0 1) * powerSeriesReduction F c 1 0 * v, ?_, ?_⟩
            · rcases huv with hu | hv
              · exact Or.inl (mul_ne_zero (mul_ne_zero ha hc) hu)
              · exact Or.inr (mul_ne_zero (mul_ne_zero ha hc) hv)
            · have hp := MatrixHasLeadAt.mul F hAC hB
              rw [show (-1 : ℤ) + 0 + -(m : ℤ) = -((m + 1 : ℕ) : ℤ) by omega,
                topRowMatrix_zero_mul_topRow] at hp
              simpa only [vertexMatrixWord_cons, Matrix.SpecialLinearGroup.coe_mul,
                mul_assoc] using hp

/-- A reduced affine-headed word has a nonzero top row in negative degree. -/
theorem affine_vertex_head_boundary (a : PowerSeriesSL2 F)
    (L : List (Bool × PowerSeriesSL2 F))
    (hred : ∀ p ∈ (true, a) :: L, vertexBoundary F p ≠ 0)
    (halt : List.IsChain (fun p q : Bool × PowerSeriesSL2 F => p.1 ≠ q.1) ((true, a) :: L)) :
    ∃ m : ℕ, 0 < m ∧ ∃ u v : F, (u ≠ 0 ∨ v ≠ 0) ∧
      MatrixHasLeadAt F (vertexMatrixWord F ((true, a) :: L)) (-(m : ℤ))
        (topRowMatrix F u v) :=
  affine_vertex_head_boundary_aux F L.length a L rfl hred halt

private theorem powerSeries_nontriangular_not_mem_iwahori (p : PowerSeriesSL2 F)
    (hc : PowerSeries.constantCoeff (p 1 0) ≠ 0) :
    powerSeriesSL2Map F p ∉ laurentIwahori F := by
  rintro ⟨q, hq, he⟩
  have hqp : q = p := powerSeriesSL2Map_injective F he
  subst q
  exact hc ((mem_iwahoriMatrices F p).mp hq)

/-- The distinguished residue exactly detects membership in the common Iwahori. -/
theorem vertexMatrixEmbedding_mem_iwahori_iff (i : Bool) (p : PowerSeriesSL2 F) :
    vertexMatrixEmbedding F i p ∈ laurentIwahori F ↔ vertexBoundary F (i, p) = 0 := by
  cases i with
  | false =>
    change powerSeriesSL2Map F p ∈ laurentIwahori F ↔
      PowerSeries.constantCoeff (p 1 0) = 0
    constructor
    · intro hp
      by_contra hc
      exact powerSeries_nontriangular_not_mem_iwahori F p hc hp
    · intro hc
      exact ⟨p, (mem_iwahoriMatrices F p).mpr hc, rfl⟩
  | true =>
    change sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F p) ∈ laurentIwahori F ↔
      PowerSeries.constantCoeff (p 0 1) = 0
    constructor
    · intro hp
      by_contra hb
      exact not_mem_laurentIwahori_of_negative_lead F
        (vertexMatrixEmbedding_true_hasLeadAt F p) (by omega)
        (topRowMatrix_ne_zero F (Or.inr hb)) hp
    · exact affineShift_mem_laurentIwahori F p

/-- Full completed vertex factors obey the same alternating boundary obstruction as simple factors. -/
theorem alternating_vertexMatrixWord_not_mem_iwahori (L : List (Bool × PowerSeriesSL2 F))
    (hne : L ≠ []) (hred : ∀ p ∈ L, vertexBoundary F p ≠ 0)
    (halt : List.IsChain (fun p q : Bool × PowerSeriesSL2 F => p.1 ≠ q.1) L) :
    vertexMatrixWord F L ∉ laurentIwahori F := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons p tail =>
    rcases p with ⟨i, a⟩
    cases i with
    | true =>
      obtain ⟨m, hm, u, v, huv, hlead⟩ := affine_vertex_head_boundary F a tail hred halt
      exact not_mem_laurentIwahori_of_negative_lead F hlead (by omega)
        (topRowMatrix_ne_zero F huv)
    | false =>
      cases tail with
      | nil =>
        rw [vertexMatrixWord_cons, vertexMatrixWord_nil, mul_one]
        exact powerSeries_nontriangular_not_mem_iwahori F a (hred (false, a) List.mem_cons_self)
      | cons q rest =>
        rcases q with ⟨j, b⟩
        cases j with
        | false =>
          exact False.elim ((List.isChain_cons.1 halt).1 (false, b) (by simp) rfl)
        | true =>
          have hr : ∀ p ∈ (true, b) :: rest, vertexBoundary F p ≠ 0 := by
            intro p hp
            exact hred p (List.mem_cons_of_mem _ hp)
          obtain ⟨m, hm, u, v, huv, hlead⟩ := affine_vertex_head_boundary F b rest hr halt.tail
          have hp := MatrixHasLeadAt.mul F (vertexMatrixEmbedding_false_hasLeadAt F a) hlead
          rw [zero_add] at hp
          have hg : MatrixHasLeadAt F (vertexMatrixWord F ((false, a) :: (true, b) :: rest))
              (-(m : ℤ)) ((powerSeriesReduction F a : Matrix (Fin 2) (Fin 2) F) *
                topRowMatrix F u v) := by
            simpa only [vertexMatrixWord_cons, Matrix.SpecialLinearGroup.coe_mul] using hp
          exact not_mem_laurentIwahori_of_negative_lead F hg (by omega)
            (sl2_mul_matrix_ne_zero F _ (topRowMatrix_ne_zero F huv))

/-- Alternating full vertex matrices outside the common subgroup cannot return to it. -/
theorem alternating_full_vertex_word_not_mem_iwahori (L : List (Bool × PowerSeriesSL2 F))
    (hne : L ≠ [])
    (hred : ∀ p ∈ L, vertexMatrixEmbedding F p.1 p.2 ∉ laurentIwahori F)
    (halt : List.IsChain (fun p q : Bool × PowerSeriesSL2 F => p.1 ≠ q.1) L) :
    vertexMatrixWord F L ∉ laurentIwahori F :=
  alternating_vertexMatrixWord_not_mem_iwahori F L hne
    (fun p hp hz => hred p hp ((vertexMatrixEmbedding_mem_iwahori_iff F p.1 p.2).mpr hz)) halt

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.alternating_vertexMatrixWord_not_mem_iwahori
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.alternating_full_vertex_word_not_mem_iwahori
