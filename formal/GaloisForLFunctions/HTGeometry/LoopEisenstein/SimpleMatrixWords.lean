import GaloisForLFunctions.HTGeometry.LoopEisenstein.SimpleRankOneEmbeddings
import GaloisForLFunctions.HTGeometry.LoopEisenstein.MatrixLaurentLeading

/-!
# Lowest coefficients of alternating simple matrices

Every affine factor contributes one negative degree. Between two such
factors, the lower-left entry of the intervening finite matrix multiplies
the boundary coefficient. A nonempty alternating word with nonzero source
lower-left entries therefore cannot lie in the Iwahori.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- Matrix projections of the two oriented simple rank-one embeddings. -/
def simpleMatrixEmbedding (i : Bool) : SL2 F →* SL2 (LaurentSeries F) :=
  if i then (affineConstantSL2Map F).comp (sl2Swap F) else constantLaurentSL2Map F

/-- Evaluate a finite word in the two matrix embeddings. -/
def simpleMatrixWord (L : List (Bool × SL2 F)) : SL2 (LaurentSeries F) :=
  (L.map (fun p => simpleMatrixEmbedding F p.1 p.2)).prod

@[simp] theorem simpleMatrixWord_nil : simpleMatrixWord F [] = 1 := rfl

@[simp] theorem simpleMatrixWord_cons (p : Bool × SL2 F) (L : List (Bool × SL2 F)) :
    simpleMatrixWord F (p :: L) = simpleMatrixEmbedding F p.1 p.2 * simpleMatrixWord F L := rfl

theorem simpleMatrixEmbedding_false_hasLeadAt (g : SL2 F) :
    MatrixHasLeadAt F (simpleMatrixEmbedding F false g) 0 g :=
  constantLaurentSL2Map_hasLeadAt F g

theorem simpleMatrixEmbedding_true_hasLeadAt (g : SL2 F) :
    MatrixHasLeadAt F (simpleMatrixEmbedding F true g) (-1) (topRowMatrix F 0 (g 1 0)) := by
  have h := affineConstantSL2Map_hasLeadAt F (sl2Swap F g)
  have he : (sl2Swap F g) 0 1 = g 1 0 := by rw [coe_sl2Swap]
  rw [he] at h
  exact h

private theorem affine_head_boundary_aux (n : ℕ) :
    ∀ (a : SL2 F) (L : List (Bool × SL2 F)), L.length = n →
      (∀ p ∈ (true, a) :: L, p.2 1 0 ≠ 0) →
      List.IsChain (fun p q : Bool × SL2 F => p.1 ≠ q.1) ((true, a) :: L) →
      ∃ m : ℕ, 0 < m ∧ ∃ u v : F, (u ≠ 0 ∨ v ≠ 0) ∧
        MatrixHasLeadAt F (simpleMatrixWord F ((true, a) :: L)) (-(m : ℤ))
          (topRowMatrix F u v) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a L hlen hred halt
    have ha : a 1 0 ≠ 0 := hred (true, a) List.mem_cons_self
    cases L with
    | nil =>
      refine ⟨1, by omega, 0, a 1 0, Or.inr ha, ?_⟩
      simpa only [simpleMatrixWord_cons, simpleMatrixWord_nil, mul_one] using
        simpleMatrixEmbedding_true_hasLeadAt F a
    | cons p tail =>
      rcases p with ⟨i, c⟩
      cases i with
      | true =>
        exact False.elim ((List.isChain_cons.1 halt).1 (true, c) (by simp) rfl)
      | false =>
        have hc : c 1 0 ≠ 0 := hred (false, c) (by simp)
        have hAC := MatrixHasLeadAt.mul F (simpleMatrixEmbedding_true_hasLeadAt F a)
          (simpleMatrixEmbedding_false_hasLeadAt F c)
        cases tail with
        | nil =>
          refine ⟨1, by omega, a 1 0 * c 1 0, a 1 0 * c 1 1,
            Or.inl (mul_ne_zero ha hc), ?_⟩
          rw [add_zero, topRowMatrix_zero_mul] at hAC
          simpa only [simpleMatrixWord_cons, simpleMatrixWord_nil, mul_one,
            Matrix.SpecialLinearGroup.coe_mul] using hAC
        | cons q rest =>
          rcases q with ⟨j, b⟩
          cases j with
          | false =>
            exact False.elim ((List.isChain_cons.1 halt.tail).1 (false, b) (by simp) rfl)
          | true =>
            have hr : ∀ p ∈ (true, b) :: rest, p.2 1 0 ≠ 0 := by
              intro p hp
              exact hred p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
            have hlt : rest.length < n := by
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨m, hm, u, v, huv, hB⟩ := ih rest.length hlt b rest rfl hr halt.tail.tail
            refine ⟨m + 1, by omega, a 1 0 * c 1 0 * u, a 1 0 * c 1 0 * v, ?_, ?_⟩
            · rcases huv with hu | hv
              · exact Or.inl (mul_ne_zero (mul_ne_zero ha hc) hu)
              · exact Or.inr (mul_ne_zero (mul_ne_zero ha hc) hv)
            · have hp := MatrixHasLeadAt.mul F hAC hB
              rw [show (-1 : ℤ) + 0 + -(m : ℤ) = -((m + 1 : ℕ) : ℤ) by omega,
                topRowMatrix_zero_mul_topRow] at hp
              simpa only [simpleMatrixWord_cons, Matrix.SpecialLinearGroup.coe_mul,
                mul_assoc] using hp

/-- An affine-headed alternating word has a nonzero top-row boundary in negative degree. -/
theorem affine_head_boundary (a : SL2 F) (L : List (Bool × SL2 F))
    (hred : ∀ p ∈ (true, a) :: L, p.2 1 0 ≠ 0)
    (halt : List.IsChain (fun p q : Bool × SL2 F => p.1 ≠ q.1) ((true, a) :: L)) :
    ∃ m : ℕ, 0 < m ∧ ∃ u v : F, (u ≠ 0 ∨ v ≠ 0) ∧
      MatrixHasLeadAt F (simpleMatrixWord F ((true, a) :: L)) (-(m : ℤ))
        (topRowMatrix F u v) :=
  affine_head_boundary_aux F L.length a L rfl hred halt

private theorem constant_nontriangular_not_mem_iwahori (g : SL2 F) (hc : g 1 0 ≠ 0) :
    constantLaurentSL2Map F g ∉ laurentIwahori F := by
  intro hg
  have hv := ((mem_laurentIwahori F _).1 hg).2
  change laurentValuation F ((PowerSeries.C (g 1 0) : PowerSeries F) : LaurentSeries F) < 1 at hv
  apply hc
  simpa only [PowerSeries.constantCoeff_C] using
    (valuation_powerSeries_lt_one_iff F (PowerSeries.C (g 1 0))).1 hv

/-- Alternation and nontriangularity force a word outside the actual matrix Iwahori. -/
theorem alternating_simpleMatrixWord_not_mem_iwahori (L : List (Bool × SL2 F))
    (hne : L ≠ []) (hred : ∀ p ∈ L, p.2 1 0 ≠ 0)
    (halt : List.IsChain (fun p q : Bool × SL2 F => p.1 ≠ q.1) L) :
    simpleMatrixWord F L ∉ laurentIwahori F := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons p tail =>
    rcases p with ⟨i, a⟩
    cases i with
    | true =>
      obtain ⟨m, hm, u, v, huv, hlead⟩ := affine_head_boundary F a tail hred halt
      exact not_mem_laurentIwahori_of_negative_lead F hlead (by omega)
        (topRowMatrix_ne_zero F huv)
    | false =>
      cases tail with
      | nil =>
        simpa only [simpleMatrixWord_cons, simpleMatrixWord_nil, mul_one] using
          constant_nontriangular_not_mem_iwahori F a (hred (false, a) List.mem_cons_self)
      | cons q rest =>
        rcases q with ⟨j, b⟩
        cases j with
        | false =>
          exact False.elim ((List.isChain_cons.1 halt).1 (false, b) (by simp) rfl)
        | true =>
          have hr : ∀ p ∈ (true, b) :: rest, p.2 1 0 ≠ 0 := by
            intro p hp
            exact hred p (List.mem_cons_of_mem _ hp)
          obtain ⟨m, hm, u, v, huv, hlead⟩ := affine_head_boundary F b rest hr halt.tail
          have hp := MatrixHasLeadAt.mul F (simpleMatrixEmbedding_false_hasLeadAt F a) hlead
          rw [zero_add] at hp
          have hg : MatrixHasLeadAt F (simpleMatrixWord F ((false, a) :: (true, b) :: rest))
              (-(m : ℤ)) ((a : Matrix (Fin 2) (Fin 2) F) * topRowMatrix F u v) := by
            simpa only [simpleMatrixWord_cons, Matrix.SpecialLinearGroup.coe_mul] using hp
          exact not_mem_laurentIwahori_of_negative_lead F hg (by omega)
            (sl2_mul_matrix_ne_zero F a (topRowMatrix_ne_zero F huv))

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
