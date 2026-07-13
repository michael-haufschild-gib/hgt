import Mathlib
import GaloisForLFunctions.MatrixRankFactor
import GaloisForLFunctions.ComplexTranscendental
import GaloisForLFunctions.WedgeRealization

/-!
# Periodic-pencil dimension as matrix rank plus a rational-kernel bit

For a facet system `faces : A → Finset V`, a facet-evaluation matrix `M` is *PP-admissible* when
off each facet its entries are integers and, on each facet, `{1} ∪ {M B v : v ∈ faces B}` is
`ℚ`-linearly independent.  The rational-kernel bit `epsQ M` is `1` exactly when `M` has a nonzero
rational kernel vector.  This module sets up these notions and proves the central bridge:
for a factored matrix `M = U·a` with `U`-columns `ℂ`-independent, `epsQ M = 0` iff the coordinate
map `a` is `ℚ`-linearly independent.
-/

namespace GaloisForLFunctions

open scoped Matrix Classical

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- `M` is periodic-pencil-admissible for the facet system `faces`. -/
def PPAdmissible (faces : A → Finset V) (M : A → V → ℂ) : Prop :=
  ∀ B : A, (∀ v, v ∉ faces B → ∃ z : ℤ, M B v = (z : ℂ)) ∧
    LinearIndependent ℚ (fun i : Option (faces B) => i.elim (1 : ℂ) (fun v => M B (v : V)))

/-- The rational-kernel bit: `1` iff `M` has a nonzero rational kernel vector. -/
noncomputable def epsQ (M : A → V → ℂ) : ℕ :=
  if ∃ q : V → ℚ, q ≠ 0 ∧ ∀ B, ∑ v, (q v : ℂ) * M B v = 0 then 1 else 0

/-- Matrix cost of a facet system: `min (rank M + epsQ M)` over admissible `M`. -/
noncomputable def matrixCost (faces : A → Finset V) : ℕ :=
  sInf {n | ∃ M : A → V → ℂ, PPAdmissible faces M ∧ n = (Matrix.of M).rank + epsQ M}

/-- Periodic-pencil dimension: least `d` admitting a `ℚ`-independent translation config in `ℂ^d`
whose induced facet-evaluation matrix is admissible. -/
noncomputable def ppDim (faces : A → Finset V) : ℕ :=
  sInf {d | ∃ (a : V → Fin d → ℂ), LinearIndependent ℚ a ∧
    ∃ (U : A → Fin d → ℂ), PPAdmissible faces (fun B v => ∑ i, U B i * a v i)}

/-- Applying a `ℚ`-scaled sum of `ℂ^r`-vectors coordinatewise turns `ℚ`-smul into cast-mul. -/
theorem smul_apply_sum {r : ℕ} (a : V → Fin r → ℂ) (q : V → ℚ) (i : Fin r) :
    (∑ v, (q v) • a v) i = ∑ v, (q v : ℂ) * a v i := by
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ => by rw [Pi.smul_apply, Rat.smul_def]

/-- **The rational-kernel bit reads off `ℚ`-independence of the coordinate map.**  For a factored
matrix `M = U·a` with `ℂ`-independent `U`-columns, `epsQ M = 0` iff `a` is `ℚ`-linearly independent. -/
theorem epsQ_eq_zero_iff {r : ℕ} (a : V → Fin r → ℂ) (U : A → Fin r → ℂ)
    (hU : LinearIndependent ℂ (fun i : Fin r => (fun B => U B i : A → ℂ))) :
    epsQ (fun B v => ∑ i, U B i * a v i) = 0 ↔ LinearIndependent ℚ a := by
  rw [Fintype.linearIndependent_iff, epsQ]
  constructor
  · intro h g hg
    have hnP : ¬ ∃ q : V → ℚ, q ≠ 0 ∧
        ∀ B, ∑ v, (q v : ℂ) * (∑ i, U B i * a v i) = 0 := by
      intro hP; rw [if_pos hP] at h; exact one_ne_zero h
    by_contra hg0
    apply hnP
    refine ⟨g, fun heq => hg0 (fun i => congrFun heq i), ?_⟩
    apply (qkernel_bridge a U hU g).mpr
    intro i
    have hgi := congrFun hg i
    rw [smul_apply_sum] at hgi
    simpa using hgi
  · intro h
    apply if_neg
    rintro ⟨q, hqne, hqc⟩
    apply hqne
    have hsum : ∑ w, (q w) • a w = 0 := by
      funext i; rw [smul_apply_sum]
      exact (qkernel_bridge a U hU q).mp hqc i
    funext v
    exact h q hsum v

/-- A matrix whose rank equals its number of columns has `ℂ`-independent columns. -/
theorem cols_linIndep_of_rank_eq {d : ℕ} (Um : Matrix A (Fin d) ℂ) (h : Um.rank = d) :
    LinearIndependent ℂ (fun i : Fin d => (fun B => Um B i : A → ℂ)) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hcol : (fun i : Fin d => (fun B => Um B i : A → ℂ)) = Um.col := rfl
  rw [Set.finrank, hcol, ← Matrix.rank_eq_finrank_span_cols, h, Fintype.card_fin]

/-- **Pencil → matrix.**  A `ℚ`-independent translation config in `ℂ^d` has facet-evaluation cost
`rank + epsQ ≤ d`: the rank is bounded by the column count, and at full rank `d` the coordinate
independence forces `epsQ = 0`. -/
theorem config_to_cost {d : ℕ} (a : V → Fin d → ℂ) (U : A → Fin d → ℂ)
    (ha : LinearIndependent ℚ a) :
    (Matrix.of (fun B v => ∑ i, U B i * a v i)).rank
      + epsQ (fun B v => ∑ i, U B i * a v i) ≤ d := by
  have hMfac : (Matrix.of (fun B v => ∑ i, U B i * a v i))
      = Matrix.of U * Matrix.of (fun i v => a v i) := by
    ext B v; simp [Matrix.mul_apply, Matrix.of_apply]
  have hrankU : (Matrix.of U).rank ≤ d := by simpa using (Matrix.of U).rank_le_card_width
  have hrankM : (Matrix.of (fun B v => ∑ i, U B i * a v i)).rank ≤ (Matrix.of U).rank := by
    rw [hMfac]; exact Matrix.rank_mul_le_left _ _
  rcases eq_or_lt_of_le (le_trans hrankM hrankU) with heq | hlt
  · have hUrankd : (Matrix.of U).rank = d := by omega
    have hUli := cols_linIndep_of_rank_eq (Matrix.of U) hUrankd
    have heps : epsQ (fun B v => ∑ i, U B i * a v i) = 0 := (epsQ_eq_zero_iff a U hUli).mpr ha
    omega
  · have heps1 : epsQ (fun B v => ∑ i, U B i * a v i) ≤ 1 := by rw [epsQ]; split_ifs <;> omega
    omega

/-- **Matrix → pencil.**  Every admissible facet-evaluation matrix `M` is realized by a
`ℚ`-independent translation config of dimension `rank M + epsQ M`: factor `M = U·a`; when
`epsQ M = 0` the columns of `a` are already `ℚ`-independent, and when `epsQ M = 1` one extra
transcendental coordinate `τ^{ν v}` makes them so. -/
theorem M_to_config (faces : A → Finset V) (M : A → V → ℂ) (hM : PPAdmissible faces M) :
    ppDim faces ≤ (Matrix.of M).rank + epsQ M := by
  obtain ⟨a, U, hfac, hU⟩ := rank_factor (Matrix.of M)
  have haM : (fun B v => ∑ i, U B i * a v i) = M := by
    funext B v; have hf := hfac B v; rw [Matrix.of_apply] at hf; exact hf.symm
  by_cases hε : epsQ M = 0
  · have ha : LinearIndependent ℚ a := (epsQ_eq_zero_iff a U hU).mp (by rw [haM]; exact hε)
    have hle : ppDim faces ≤ (Matrix.of M).rank := Nat.sInf_le ⟨a, ha, U, by rw [haM]; exact hM⟩
    omega
  · obtain ⟨τ, hτ⟩ := exists_transcendental_complex
    have hνinj : Function.Injective (fun v : V => ((Fintype.equivFin V) v : ℕ)) :=
      Fin.val_injective.comp (Fintype.equivFin V).injective
    have hle : ppDim faces ≤ (Matrix.of M).rank + 1 := by
      apply Nat.sInf_le
      refine ⟨fun v => Fin.snoc (a v) (τ ^ ((Fintype.equivFin V) v : ℕ)),
        ?_, fun B => Fin.snoc (U B) 0, ?_⟩
      · rw [Fintype.linearIndependent_iff]; intro q hq
        have hlast : ∑ v, (q v) • (τ ^ ((Fintype.equivFin V) v : ℕ)) = 0 := by
          have hc := congrFun hq (Fin.last (Matrix.of M).rank)
          rw [Finset.sum_apply] at hc; simpa using hc
        exact transcendental_pow_combination_eq_zero hτ hνinj q hlast
      · have heq : (fun B v => ∑ i, (Fin.snoc (U B) 0 : Fin _ → ℂ) i
            * (Fin.snoc (a v) (τ ^ ((Fintype.equivFin V) v : ℕ)) : Fin _ → ℂ) i) = M := by
          funext B v; rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
          have hf := hfac B v; rw [Matrix.of_apply] at hf; exact hf.symm
        rw [heq]; exact hM
    have hepsval : epsQ M = 0 ∨ epsQ M = 1 := by unfold epsQ; split_ifs <;> simp
    omega

/-- **Periodic-pencil dimension equals matrix rank plus the rational-kernel bit.**
`ppDim Δ = min over admissible M of (rank M + epsQ M)`. -/
theorem ppDim_eq_matrixCost (faces : A → Finset V) : ppDim faces = matrixCost faces := by
  apply le_antisymm
  · rcases Set.eq_empty_or_nonempty
      {n | ∃ M : A → V → ℂ, PPAdmissible faces M ∧ n = (Matrix.of M).rank + epsQ M} with he | hne
    · rw [matrixCost, he, Nat.sInf_empty, Nat.le_zero, ppDim, Nat.sInf_eq_zero]
      right
      rw [Set.eq_empty_iff_forall_notMem]
      rintro d ⟨a, ha, U, hPP⟩
      rw [Set.eq_empty_iff_forall_notMem] at he
      exact he _ ⟨_, hPP, rfl⟩
    · obtain ⟨M, hPP, hval⟩ := Nat.sInf_mem hne
      calc ppDim faces ≤ (Matrix.of M).rank + epsQ M := M_to_config faces M hPP
        _ = matrixCost faces := hval.symm
  · rcases Set.eq_empty_or_nonempty
      {d | ∃ (a : V → Fin d → ℂ), LinearIndependent ℚ a ∧
        ∃ (U : A → Fin d → ℂ), PPAdmissible faces (fun B v => ∑ i, U B i * a v i)} with he | hne
    · rw [ppDim, he, Nat.sInf_empty, Nat.le_zero, matrixCost, Nat.sInf_eq_zero]
      right
      rw [Set.eq_empty_iff_forall_notMem]
      rintro n ⟨M, hPP, hval⟩
      rw [Set.eq_empty_iff_forall_notMem] at he
      obtain ⟨a, U, hfac, hU⟩ := rank_factor (Matrix.of M)
      have haM : (fun B v => ∑ i, U B i * a v i) = M := by
        funext B v; have hf := hfac B v; rw [Matrix.of_apply] at hf; exact hf.symm
      by_cases hε : epsQ M = 0
      · exact he _ ⟨a, (epsQ_eq_zero_iff a U hU).mp (by rw [haM]; exact hε), U,
          by rw [haM]; exact hPP⟩
      · obtain ⟨τ, hτ⟩ := exists_transcendental_complex
        have hνinj : Function.Injective (fun v : V => ((Fintype.equivFin V) v : ℕ)) :=
          Fin.val_injective.comp (Fintype.equivFin V).injective
        refine he _ ⟨fun v => Fin.snoc (a v) (τ ^ ((Fintype.equivFin V) v : ℕ)), ?_,
          fun B => Fin.snoc (U B) 0, ?_⟩
        · rw [Fintype.linearIndependent_iff]; intro q hq
          have hlast : ∑ v, (q v) • (τ ^ ((Fintype.equivFin V) v : ℕ)) = 0 := by
            have hc := congrFun hq (Fin.last (Matrix.of M).rank)
            rw [Finset.sum_apply] at hc; simpa using hc
          exact transcendental_pow_combination_eq_zero hτ hνinj q hlast
        · have heq : (fun B v => ∑ i, (Fin.snoc (U B) 0 : Fin _ → ℂ) i
              * (Fin.snoc (a v) (τ ^ ((Fintype.equivFin V) v : ℕ)) : Fin _ → ℂ) i) = M := by
            funext B v; rw [Fin.sum_univ_castSucc]
            simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
            have hf := hfac B v; rw [Matrix.of_apply] at hf; exact hf.symm
          rw [heq]; exact hPP
    · obtain ⟨a, ha, U, hPP⟩ := Nat.sInf_mem hne
      calc matrixCost faces
          ≤ (Matrix.of (fun B v => ∑ i, U B i * a v i)).rank
            + epsQ (fun B v => ∑ i, U B i * a v i) := Nat.sInf_le ⟨_, hPP, rfl⟩
        _ ≤ ppDim faces := config_to_cost a U ha

end GaloisForLFunctions
