import GaloisForLFunctions.HTGeometry.PPMatrixRankFormula

/-!
# Consequences of the periodic-pencil matrix-rank formula

The central equality `ppDim_eq_matrixCost` is proved in `PPMatrixRankFormula`.  This module closes
the remaining existence statements from the card: PP-admissible matrices exist for every finite
facet system, the natural-number matrix cost is attained, and the rational-kernel correction is
always a single bit.
-/


namespace GaloisForLFunctions

open scoped Matrix Classical

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
theorem exists_ppAdmissible (faces : A → Finset V) :
    ∃ M : A → V → ℂ, PPAdmissible faces M := by
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  let ν : V → ℕ := fun v => ((Fintype.equivFin V) v : ℕ)
  have hν : Function.Injective ν :=
    Fin.val_injective.comp (Fintype.equivFin V).injective
  let M : A → V → ℂ := fun B v => if v ∈ faces B then τ ^ (ν v + 1) else 0
  refine ⟨M, ?_⟩
  intro B
  constructor
  · intro v hv
    exact ⟨0, by simp [M, hv]⟩
  · let μ : Option (faces B) → ℕ := fun i => i.elim 0 (fun v => ν (v : V) + 1)
    have hμ : Function.Injective μ := by
      intro i j hij
      cases i with
      | none =>
          cases j with
          | none => rfl
          | some j => simp [μ] at hij
      | some i =>
          cases j with
          | none => simp [μ] at hij
          | some j =>
              apply congrArg some
              apply Subtype.ext
              apply hν
              simp only [μ, Option.elim_some] at hij
              omega
    have hlin := transcendental_pow_comp_linearIndependent hτ hμ
    convert hlin using 1
    funext i
    cases i with
    | none => simp [μ]
    | some i => simp [μ, M]

omit [Fintype A] [DecidableEq A] in
theorem matrixCost_attained (faces : A → Finset V) :
    ∃ M : A → V → ℂ, PPAdmissible faces M ∧
      matrixCost faces = (Matrix.of M).rank + epsQ M := by
  obtain ⟨M, hM⟩ := exists_ppAdmissible faces
  have hne : {n | ∃ M : A → V → ℂ, PPAdmissible faces M ∧
      n = (Matrix.of M).rank + epsQ M}.Nonempty :=
    ⟨(Matrix.of M).rank + epsQ M, M, hM, rfl⟩
  obtain ⟨M', hM', hval⟩ := Nat.sInf_mem hne
  refine ⟨M', hM', ?_⟩
  simpa [matrixCost] using hval

omit [Fintype A] [DecidableEq V] [DecidableEq A] in
theorem epsQ_le_one (M : A → V → ℂ) : epsQ M ≤ 1 := by
  unfold epsQ
  split_ifs <;> omega

omit [Fintype A] [DecidableEq A] in
theorem ppDim_le_card (faces : A → Finset V) : ppDim faces ≤ Fintype.card V := by
  obtain ⟨M, hM⟩ := exists_ppAdmissible faces
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let a : V → Fin (Fintype.card V) → ℂ :=
    fun v => (Pi.single (e v) (1 : ℂ) : Fin (Fintype.card V) → ℂ)
  let U : A → Fin (Fintype.card V) → ℂ := fun B i => M B (e.symm i)
  have ha : LinearIndependent ℚ a := by
    have hC : LinearIndependent ℂ (fun v : V =>
        (Pi.single (e v) (1 : ℂ) : Fin (Fintype.card V) → ℂ)) := by
      have hb := (Pi.basisFun ℂ (Fin (Fintype.card V))).linearIndependent.comp e e.injective
      simpa [Function.comp_def, Pi.basisFun_apply] using hb
    have hCq := hC.restrict_scalars (R := ℚ) (by
      intro p q hpq
      have hpc : (p : ℂ) = (q : ℂ) := by simpa [Rat.smul_one_eq_cast] using hpq
      exact_mod_cast hpc)
    simpa [a] using hCq
  apply Nat.sInf_le
  refine ⟨a, ha, U, ?_⟩
  have heval : (fun B v => ∑ i, U B i * a v i) = M := by
    funext B v
    simp [U, a, Pi.single_apply, e]
  rw [heval]
  exact hM

omit [DecidableEq A] in
theorem matrixCost_le_card (faces : A → Finset V) : matrixCost faces ≤ Fintype.card V := by
  rw [← ppDim_eq_matrixCost]
  exact ppDim_le_card faces

end GaloisForLFunctions
