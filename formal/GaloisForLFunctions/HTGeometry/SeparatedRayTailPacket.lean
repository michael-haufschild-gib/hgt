import GaloisForLFunctions.HTGeometry.FiniteEvaluationPacket
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Separated-ray packets from finite-ray quotient independence

The ordinary evaluation-packet theorem may select several coordinates on the same ray.  That is
insufficient for prime derivations, whose Jacobian rows must use distinct prime directions.  This
file proves the missing transversal statement: if every nonzero coefficient combination remains
active on infinitely many rays, then a full-rank packet can be chosen outside any finite forbidden
set with pairwise distinct ray labels.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-- Linear independence modulo profiles supported on finitely many rays. -/
def RayTailCoefficientIndependent
    {I P E : Type*} [Fintype I] (a : I -> P -> E -> ℂ) : Prop :=
  ∀ c : I -> ℂ,
    {p | ∃ e, ∑ i, c i * a i p e ≠ 0}.Finite -> c = 0

/-- After deleting finitely many rays, the restricted coordinate functions remain linearly
independent. -/
theorem RayTailCoefficientIndependent.restricted_linearIndependent
    {I P E : Type*} [Fintype I]
    (a : I -> P -> E -> ℂ) (h : RayTailCoefficientIndependent a)
    (forbidden : Set P) (hforbidden : forbidden.Finite) :
    LinearIndependent ℂ
      (fun i => fun z : {z : P × E // z.1 ∉ forbidden} => a i z.1.1 z.1.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc0 : c = 0 := h c (hforbidden.subset (by
    intro p hp
    by_contra hpforbidden
    obtain ⟨e, he⟩ := hp
    have hpoint := congrFun hc (⟨(p, e), hpforbidden⟩ :
      {z : P × E // z.1 ∉ forbidden})
    apply he
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hpoint))
  exact fun i => congrFun hc0 i

/-- Evaluation rows outside any finite ray set span the complete finite coefficient space. -/
theorem RayTailCoefficientIndependent.span_restricted_evaluationRows_eq_top
    {I P E : Type*} [Fintype I] [DecidableEq I]
    (a : I -> P -> E -> ℂ) (h : RayTailCoefficientIndependent a)
    (forbidden : Set P) (hforbidden : forbidden.Finite) :
    Submodule.span ℂ
      (Set.range fun z : {z : P × E // z.1 ∉ forbidden} =>
        fun i => a i z.1.1 z.1.2) = ⊤ := by
  exact span_evaluationVectors_eq_top
    (fun i => fun z : {z : P × E // z.1 ∉ forbidden} => a i z.1.1 z.1.2)
    (h.restricted_linearIndependent a forbidden hforbidden)

/-- **Separated-ray packet theorem.**  Finite-ray quotient independence supplies a square
full-rank evaluation packet outside any prescribed finite ray set, and the selected rows have
pairwise distinct ray labels. -/
theorem RayTailCoefficientIndependent.exists_separated_fullRank_packet_avoiding
    {I P E : Type*} [Fintype I] [DecidableEq I]
    (a : I -> P -> E -> ℂ) (h : RayTailCoefficientIndependent a)
    (forbidden : Set P) (hforbidden : forbidden.Finite) :
    ∃ (q : I -> P) (e : I -> E),
      Function.Injective q ∧
      (∀ i, q i ∉ forbidden) ∧
      IsUnit (Matrix.of (fun row col => a col (q row) (e row)) : Matrix I I ℂ) := by
  classical
  let n := Fintype.card I
  have select : ∀ k : Nat, k ≤ n ->
      ∃ (q : Fin k -> P) (e : Fin k -> E),
        Function.Injective q ∧
        (∀ i, q i ∉ forbidden) ∧
        LinearIndependent ℂ (fun row => fun col : I => a col (q row) (e row)) := by
    intro k hk
    induction k with
    | zero =>
        refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, linearIndependent_empty_type⟩
        · exact Function.injective_of_subsingleton _
        · intro i
          exact Fin.elim0 i
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        obtain ⟨q, e, hq, havoid, hLI⟩ := ih (Nat.le_of_lt hklt)
        let used : Set P := Set.range q
        have hused : used.Finite := Set.finite_range q
        let blocked : Set P := forbidden ∪ used
        have hblocked : blocked.Finite := hforbidden.union hused
        let X := {z : P × E // z.1 ∉ blocked}
        let available : X -> (I -> ℂ) := fun z => fun i => a i z.1.1 z.1.2
        have hspan : Submodule.span ℂ (Set.range available) = ⊤ := by
          simpa only [X, available] using
            h.span_restricted_evaluationRows_eq_top a blocked hblocked
        let chosen : Fin k -> (I -> ℂ) :=
          fun row => fun col => a col (q row) (e row)
        let S : Submodule ℂ (I -> ℂ) :=
          Submodule.span ℂ (Set.range chosen)
        have hS_ne_top : S ≠ ⊤ := by
          intro htop
          have hfin : Module.finrank ℂ S = k := by
            simpa [S, chosen] using finrank_span_eq_card hLI
          have hambient : Module.finrank ℂ (I -> ℂ) = k := by
            rw [← finrank_top ℂ (I -> ℂ), ← htop]
            exact hfin
          have hcard : n = k := by
            dsimp [n]
            simpa using hambient
          exact (Nat.ne_of_lt hklt) hcard.symm
        have hexists : ∃ z : X, available z ∉ S := by
          by_contra hz
          have hall : ∀ z : X, available z ∈ S := fun z =>
            not_not.mp (not_exists.mp hz z)
          have hle : Submodule.span ℂ (Set.range available) ≤ S :=
            Submodule.span_le.mpr (by
              rintro _ ⟨z, rfl⟩
              exact hall z)
          rw [hspan] at hle
          exact hS_ne_top (top_unique hle)
        obtain ⟨z, hz⟩ := hexists
        let q' : Fin (k + 1) -> P :=
          Fin.snoc q z.1.1
        let e' : Fin (k + 1) -> E :=
          Fin.snoc e z.1.2
        have hq' : Function.Injective q' := by
          intro i j hij
          induction i using Fin.lastCases with
          | last =>
              induction j using Fin.lastCases with
              | last => rfl
              | cast j =>
                  exfalso
                  apply z.2
                  apply Set.mem_union_right forbidden
                  exact ⟨j, by simpa [q'] using hij.symm⟩
          | cast i =>
              induction j using Fin.lastCases with
              | last =>
                  exfalso
                  apply z.2
                  apply Set.mem_union_right forbidden
                  exact ⟨i, by simpa [q'] using hij⟩
              | cast j =>
                  have hij' : i = j := hq (by simpa [q'] using hij)
                  subst j
                  rfl
        have havoid' : ∀ i, q' i ∉ forbidden := by
          intro i
          induction i using Fin.lastCases with
          | last =>
              intro hi
              apply z.2
              apply Set.mem_union_left used
              simpa [q'] using hi
          | cast i =>
              simpa [q'] using havoid i
        have hrows :
            (fun row : Fin (k + 1) => fun col : I =>
              a col (q' row) (e' row)) =
              Fin.snoc chosen (available z) := by
          funext row
          induction row using Fin.lastCases with
          | last => simp [q', e', available]
          | cast row => simp [q', e', chosen]
        have hLI' : LinearIndependent ℂ
            (fun row : Fin (k + 1) => fun col : I =>
              a col (q' row) (e' row)) := by
          rw [hrows]
          exact hLI.finSnoc hz
        exact ⟨q', e', hq', havoid', hLI'⟩
  obtain ⟨q0, e0, hq0, havoid0, hLI0⟩ := select n le_rfl
  let idx : I ≃ Fin n := Fintype.equivFin I
  let q : I -> P := fun i => q0 (idx i)
  let e : I -> E := fun i => e0 (idx i)
  have hq : Function.Injective q := hq0.comp idx.injective
  have havoid : ∀ i, q i ∉ forbidden := fun i => havoid0 (idx i)
  have hLI : LinearIndependent ℂ
      (fun row : I => fun col : I => a col (q row) (e row)) := by
    exact hLI0.comp idx idx.injective
  refine ⟨q, e, hq, havoid, ?_⟩
  rw [← Matrix.linearIndependent_rows_iff_isUnit]
  simpa [Matrix.row_apply] using hLI

end

end GaloisForLFunctions.HTGeometry
