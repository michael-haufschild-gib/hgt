import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.NonidentityPauliWordCount
import GaloisForLFunctions.HTGeometry.PauliCountOrderBounds

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype τ] [DecidableEq τ]

/-- Relabelling qubit sites preserves Pauli support weight. -/
theorem finitePauliWeight_comp_equiv_symm (e : σ ≃ τ)
    (P : σ → Option (Fin 3)) :
    finitePauliWeight (fun t => P (e.symm t)) = finitePauliWeight P := by
  let supportEquiv : {s : σ // P s ≠ none} ≃
      {t : τ // P (e.symm t) ≠ none} :=
    { toFun := fun s => ⟨e s.1, by simpa using s.2⟩
      invFun := fun t => ⟨e.symm t.1, t.2⟩
      left_inv := fun s => by apply Subtype.ext; simp
      right_inv := fun t => by apply Subtype.ext; simp }
  rw [finitePauliWeight, finitePauliWeight]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr supportEquiv.symm

/-- Site relabelling equivalence of bounded-weight Pauli dictionaries. -/
def finiteQLocalPauliLabelEquiv (e : σ ≃ τ) (q : ℕ) :
    FiniteQLocalPauliLabel σ q ≃ FiniteQLocalPauliLabel τ q where
  toFun P := ⟨fun t => P.1 (e.symm t), by
    rw [finitePauliWeight_comp_equiv_symm e P.1]
    exact P.2⟩
  invFun Q := ⟨fun s => Q.1 (e s), by
    have h := finitePauliWeight_comp_equiv_symm e.symm Q.1
    simpa using h.trans_le Q.2⟩
  left_inv P := by ext s; simp
  right_inv Q := by ext t; simp

/-- The weight-at-most-`q` Pauli dictionary consists of identity plus all bounded nonidentity
words. -/
theorem card_finiteQLocalPauliLabel (n q : ℕ) :
    Fintype.card (FiniteQLocalPauliLabel (Fin n) q) =
      Quantum.nonidentityPauliWeightCount n q + 1 := by
  classical
  rw [Fintype.card_subtype]
  have hset :
      Finset.univ.filter
          (fun P : Fin n → Option (Fin 3) => finitePauliWeight P ≤ q) =
        insert (pauliIdentityLabel n) (nonidentityPauliWords n q) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, mem_nonidentityPauliWords]
    have hweight : finitePauliWeight P = pauliWeight P := rfl
    rw [hweight]
    constructor
    · intro hle
      by_cases hz : pauliWeight P = 0
      · left
        funext i
        by_contra hi
        have hi' : P i ≠ none := by
          simpa [pauliIdentityLabel] using hi
        have himem : i ∈ Finset.univ.filter fun s : Fin n => P s ≠ none := by
          simp [hi']
        have : 0 < pauliWeight P := by
          rw [pauliWeight]
          exact Finset.card_pos.mpr ⟨i, himem⟩
        omega
      · right
        exact ⟨Nat.one_le_iff_ne_zero.mpr hz, hle⟩
    · rintro (hP | ⟨-, hle⟩)
      · subst P
        simp [pauliWeight, pauliIdentityLabel]
      · exact hle
  rw [hset, Finset.card_insert_of_notMem]
  · rw [card_nonidentityPauliWords]
  · rw [mem_nonidentityPauliWords]
    simp [pauliWeight, pauliIdentityLabel]

/-- Bounded-weight Pauli dictionary cardinality depends only on qubit count. -/
theorem card_finiteQLocalPauliLabel_eq_count (σ : Type*) [Fintype σ]
    [DecidableEq σ] (q : ℕ) :
    Fintype.card (FiniteQLocalPauliLabel σ q) =
      Quantum.nonidentityPauliWeightCount (Fintype.card σ) q + 1 := by
  rw [← card_finiteQLocalPauliLabel (Fintype.card σ) q]
  exact Fintype.card_congr
    (finiteQLocalPauliLabelEquiv (Fintype.equivFin σ) q)

/-- For two-local Pauli sectors, fixed local observer multiplicity is eventually smaller than
Hilbert dimension plus one. -/
theorem eventually_twoLocalPauli_separator :
    ∀ᶠ n : ℕ in atTop,
      Fintype.card (FiniteQLocalPauliLabel (Fin n) 2) * 3 ^ 2 < 2 ^ n + 1 := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (2 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hsmall := hlim.eventually_lt_const (show (0 : ℝ) < 1 / 324 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop 4] with n hn hnlarge
  have hnpos : 1 ≤ n := by omega
  have hcount := Quantum.nonidentityPauliWeightCount_le n 2 hnpos
  rw [card_finiteQLocalPauliLabel]
  have hpolyR : (((Quantum.nonidentityPauliWeightCount n 2 + 1) * 3 ^ 2 : ℕ) : ℝ) <
      ((2 ^ n + 1 : ℕ) : ℝ) := by
    have hcountR : (Quantum.nonidentityPauliWeightCount n 2 : ℝ) ≤
        (18 : ℝ) * (n : ℝ) ^ 2 := by
      exact_mod_cast hcount
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hnratio : (n : ℝ) ^ 2 < (2 : ℝ) ^ n / 324 := by
      calc
        (n : ℝ) ^ 2 < (1 / 324 : ℝ) * (2 : ℝ) ^ n :=
          (div_lt_iff₀ hpowpos).mp hn
        _ = (2 : ℝ) ^ n / 324 := by ring
    have hpowLarge : (16 : ℝ) ≤ (2 : ℝ) ^ n := by
      have hnat : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnlarge
      norm_num at hnat ⊢
      exact_mod_cast hnat
    norm_num at hcountR ⊢
    nlinarith
  exact_mod_cast hpolyR


end

end GaloisForLFunctions.HTGeometry
