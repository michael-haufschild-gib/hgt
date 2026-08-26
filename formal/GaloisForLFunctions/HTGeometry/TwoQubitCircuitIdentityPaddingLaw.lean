import GaloisForLFunctions.RHTower.ContinuousExactCircuitSameDrawCubicLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open Matrix Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def TwoQubitArchitecture.padOne
    {n R : ℕ} (a b : Fin n) (hab : a ≠ b)
    (A : TwoQubitArchitecture n R) : TwoQubitArchitecture n (R + 1) where
  sites := Fin.lastCases (a, b) A.sites
  distinct := by
    intro k
    refine Fin.lastCases ?_ (fun r => ?_) k
    · simpa using hab
    · simpa using A.distinct r

def TwoQubitArchitecture.padOneGates
    {R : ℕ} (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    Fin (R + 1) → Matrix.specialUnitaryGroup (Bool × Bool) ℂ :=
  Fin.lastCases 1 gates

theorem TwoQubitArchitecture.padOne_contraction
    {n R : ℕ} (a b : Fin n) (hab : a ≠ b)
    (A : TwoQubitArchitecture n R)
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    (A.padOne a b hab).contraction (TwoQubitArchitecture.padOneGates gates) =
      A.contraction gates := by
  unfold TwoQubitArchitecture.contraction
  rw [List.ofFn_succ']
  have hlast : (A.padOne a b hab).gateLift (Fin.last R)
      (TwoQubitArchitecture.padOneGates gates (Fin.last R)) = 1 := by
    apply Subtype.ext
    simp only [TwoQubitArchitecture.gateLift, TwoQubitArchitecture.padOne,
      TwoQubitArchitecture.padOneGates, Fin.lastCases_last]
    unfold twoQubitLift specialUnitaryAsUnitary Quantum.tensorGate
    change Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab).symm
        ((1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) ⊗ₖ
          (1 : Matrix ({q : Fin n // q ≠ a ∧ q ≠ b} → Bool)
            ({q : Fin n // q ≠ a ∧ q ≠ b} → Bool) ℂ)) = 1
    rw [Matrix.one_kronecker_one, map_one]
  rw [hlast, List.concat_eq_append, List.reverse_concat, List.prod_cons, one_mul]
  congr 2
  rw [List.ofFn_inj]
  funext i
  simp [TwoQubitArchitecture.padOne, TwoQubitArchitecture.padOneGates,
    TwoQubitArchitecture.gateLift]

/-- One identity gate pads an exact circuit without changing its endpoint. -/
theorem circuitImageExact_subset_succ
    {n R : ℕ} (hn : 2 ≤ n) :
    TwoQubitArchitecture.circuitImageExact n R ⊆
      TwoQubitArchitecture.circuitImageExact n (R + 1) := by
  intro U hU
  rw [TwoQubitArchitecture.circuitImageExact] at hU ⊢
  simp only [Set.mem_iUnion, Set.mem_range] at hU ⊢
  obtain ⟨A, gates, rfl⟩ := hU
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    norm_num [a, b] at this
  exact ⟨A.padOne a b hab, TwoQubitArchitecture.padOneGates gates,
    A.padOne_contraction a b hab gates⟩

/-- Arbitrarily many identity gates pad an exact circuit without changing its endpoint. -/
theorem circuitImageExact_subset_add_right
    {n R : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    TwoQubitArchitecture.circuitImageExact n R ⊆
      TwoQubitArchitecture.circuitImageExact n (R + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          (circuitImageExact_subset_succ (n := n) (R := R + k) hn))

/-- On a register with two sites, every circuit of cost at most `s` is
literally an exact-`s` circuit after identity padding. -/
theorem circuitImageAtMost_subset_exact
    {n s : ℕ} (hn : 2 ≤ n) :
    TwoQubitArchitecture.circuitImageAtMost n s ⊆
      TwoQubitArchitecture.circuitImageExact n s := by
  intro U hU
  rw [TwoQubitArchitecture.circuitImageAtMost] at hU
  simp only [Set.mem_iUnion] at hU
  obtain ⟨R, hUR⟩ := hU
  have hR : R.1 ≤ s := Nat.le_of_lt_succ R.2
  have hpad := circuitImageExact_subset_add_right (R := R.1) hn (s - R.1) hUR
  simpa [Nat.add_sub_of_le hR] using hpad

end

end GaloisForLFunctions.HTGeometry
