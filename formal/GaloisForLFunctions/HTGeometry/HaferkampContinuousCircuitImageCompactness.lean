import GaloisForLFunctions.HTGeometry.HaferkampExactCircuitComplexity
import GaloisForLFunctions.HTGeometry.TwoQubitGateParametrisation

/-!
# Compactness of the complete continuous two-qubit circuit image

For every finite gate budget, this file keeps all continuous `SU(4)` gate
parameters and all architectures.  Their complete operator image is compact.
Consequently, exclusion from the exact image automatically has a strictly
positive operator-norm margin.  This is the bridge from exact algebraic
circuit obstructions to fixed-error circuit complexity; no finite gate
dictionary or discretisation is used.
-/

open Matrix TopologicalSpace
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Forgetting determinant one is continuous. -/
theorem continuous_specialUnitaryAsUnitary :
    Continuous specialUnitaryAsUnitary := by
  exact continuous_induced_rng.2 continuous_subtype_val

/-- Tensoring a finite unitary with an identity gate is continuous. -/
theorem continuous_tensorGate_right_one
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] :
    Continuous (fun U : Matrix.unitaryGroup α ℂ =>
      Quantum.tensorGate U (1 : Matrix.unitaryGroup β ℂ)) := by
  refine continuous_induced_rng.2 ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_finiteUnitaryEntry i.1 j.1).mul continuous_const

/-- A local `SU(4)` gate varies continuously after lifting to any two
distinct register sites. -/
theorem continuous_twoQubitLift
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b) :
    Continuous (twoQubitLift a b hab) := by
  exact (continuous_unitaryGroupReindex (splitTwoQubitConfig a b hab).symm).comp
    (continuous_tensorGate_right_one.comp continuous_specialUnitaryAsUnitary)

/-- The architecture lift is a two-qubit gate in the polynomial-circuit
semantics used by the exceptional-time theorem. -/
theorem twoQubitLift_isTwoQubitGate
    {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    TwoQubitCircuit.IsTwoQubitGate a b
      (twoQubitLift a b hab U :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  refine ⟨(U : Matrix (Bool × Bool) (Bool × Bool) ℂ), ?_⟩
  intro x y
  unfold twoQubitLift
  rw [unitaryGroupReindex_coe]
  change
    (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) (x a, x b) (y a, y b) *
      (1 : Matrix ({q : Fin n // q ≠ a ∧ q ≠ b} → Bool)
        ({q : Fin n // q ≠ a ∧ q ≠ b} → Bool) ℂ)
          (fun q => x q.1) (fun q => y q.1) = _
  rw [Matrix.one_apply]
  by_cases hrest : ∀ c, c ≠ a → c ≠ b → x c = y c
  · rw [if_pos hrest]
    have heq : (fun q : {q : Fin n // q ≠ a ∧ q ≠ b} => x q.1) =
        fun q => y q.1 := by
      funext q
      exact hrest q.1 q.2.1 q.2.2
    simp [heq]
  · rw [if_neg hrest]
    have hne : (fun q : {q : Fin n // q ≠ a ∧ q ≠ b} => x q.1) ≠
        fun q => y q.1 := by
      intro heq
      apply hrest
      intro c hca hcb
      exact congrFun heq ⟨c, hca, hcb⟩
    simp [hne]

/-- Enumerating a finite family in reversed `Fin` order is literal list
reversal. -/
theorem ofFn_comp_finRev {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i => f (Fin.rev i)) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_ofFn, List.getElem_reverse]
    congr 2
    simp [Fin.rev]
    omega

namespace TwoQubitArchitecture

/-- Finite registers and finite word lengths admit only finitely many ordered
two-site architectures. -/
noncomputable instance finiteArchitecture {n R : ℕ} :
    Finite (TwoQubitArchitecture n R) :=
  Finite.of_injective TwoQubitArchitecture.sites (by
    intro A B h
    cases A with
    | mk As Ad =>
      cases B with
      | mk Bs Bd =>
        simp only at h
        subst Bs
        rfl)

theorem continuous_gateLift {n R : ℕ}
    (A : TwoQubitArchitecture n R) (r : Fin R) :
    Continuous (A.gateLift r) :=
  continuous_twoQubitLift _ _ _

/-- Ordered local-gate product along a list of architecture locations. -/
def word {n R : ℕ} (A : TwoQubitArchitecture n R) :
    List (Fin R) →
      (Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) →
        Matrix.unitaryGroup (Fin n → Bool) ℂ
  | [], _ => 1
  | r :: rs, gates => A.gateLift r (gates r) * word A rs gates

theorem continuous_word {n R : ℕ}
    (A : TwoQubitArchitecture n R) (rs : List (Fin R)) :
    Continuous (word A rs) := by
  induction rs with
  | nil => exact continuous_const
  | cons r rs ih =>
      exact ((A.continuous_gateLift r).comp (continuous_apply r)).mul ih

theorem word_eq_prod {n R : ℕ}
    (A : TwoQubitArchitecture n R) (rs : List (Fin R))
    (gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    word A rs gates = (rs.map fun r => A.gateLift r (gates r)).prod := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [word, List.map_cons, List.prod_cons, ih]

/-- The full architecture contraction is continuous in every `SU(4)` gate
parameter. -/
theorem continuous_contraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) :
    Continuous A.contraction := by
  have h := A.continuous_word
    (List.ofFn (fun r : Fin R => r)).reverse
  convert h using 1
  funext gates
  rw [A.word_eq_prod]
  simp only [List.map_reverse, List.map_ofFn]
  rfl

/-- Complete continuous endpoint image of one architecture is compact. -/
theorem isCompact_range_contraction {n R : ℕ}
    (A : TwoQubitArchitecture n R) :
    IsCompact (Set.range A.contraction) := by
  have hrange : Set.range A.contraction = A.contraction '' Set.univ := by
    ext U
    simp
  rw [hrange]
  exact isCompact_univ.image A.continuous_contraction

/-- Complete continuous circuit image at one exact gate count, including all
architectures. -/
def circuitImageExact (n R : ℕ) :
    Set (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
  ⋃ A : TwoQubitArchitecture n R, Set.range A.contraction

theorem isCompact_circuitImageExact (n R : ℕ) :
    IsCompact (circuitImageExact n R) := by
  apply isCompact_iUnion
  intro A
  exact A.isCompact_range_contraction

/-- Complete continuous circuit image with gate count at most `s`. -/
def circuitImageAtMost (n s : ℕ) :
    Set (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
  ⋃ R : Fin (s + 1), circuitImageExact n R

theorem isCompact_circuitImageAtMost (n s : ℕ) :
    IsCompact (circuitImageAtMost n s) := by
  apply isCompact_iUnion
  intro R
  exact isCompact_circuitImageExact n R

/-- Membership is literal existence of a continuous two-qubit circuit within
the budget. -/
theorem mem_circuitImageAtMost_iff
    {n s : ℕ} {U : Matrix.unitaryGroup (Fin n → Bool) ℂ} :
    U ∈ circuitImageAtMost n s ↔
      ∃ C : TwoQubitCircuit n, C.gateCount ≤ s ∧ C.eval = U := by
  constructor
  · intro hU
    rw [circuitImageAtMost] at hU
    simp only [Set.mem_iUnion] at hU
    obtain ⟨R, hR⟩ := hU
    rw [circuitImageExact] at hR
    simp only [Set.mem_iUnion, Set.mem_range] at hR
    obtain ⟨A, gates, hgate⟩ := hR
    exact ⟨⟨R, A, gates⟩, Nat.le_of_lt_succ R.2, hgate⟩
  · rintro ⟨C, hC, rfl⟩
    rw [circuitImageAtMost]
    simp only [Set.mem_iUnion]
    let R : Fin (s + 1) := ⟨C.gateCount, Nat.lt_succ_iff.mpr hC⟩
    refine ⟨R, ?_⟩
    rw [circuitImageExact]
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨C.architecture, C.gates, rfl⟩

/-- Matrix-valued circuit image, carrying operator-norm metric. -/
def circuitMatrixImageAtMost (n s : ℕ) :
    Set (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
  (fun U : Matrix.unitaryGroup (Fin n → Bool) ℂ =>
    (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) ''
      circuitImageAtMost n s

theorem isCompact_circuitMatrixImageAtMost (n s : ℕ) :
    IsCompact (circuitMatrixImageAtMost n s) :=
  (isCompact_circuitImageAtMost n s).image continuous_subtype_val

/-- Exact exclusion from every continuous circuit in the budget has a
strictly positive operator-norm margin. -/
theorem exists_pos_norm_sub_of_not_mem_circuitMatrixImageAtMost
    {n s : ℕ} {U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hU : U ∉ circuitMatrixImageAtMost n s) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ V ∈ circuitMatrixImageAtMost n s,
      ε ≤ ‖U - V‖ := by
  let ε := Metric.infDist U (circuitMatrixImageAtMost n s)
  have hne : (circuitMatrixImageAtMost n s).Nonempty := by
    let A : TwoQubitArchitecture n 0 := ⟨Fin.elim0, fun r => Fin.elim0 r⟩
    refine ⟨(A.contraction Fin.elim0 :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ), ?_⟩
    rw [circuitMatrixImageAtMost]
    refine ⟨A.contraction Fin.elim0, ?_, rfl⟩
    rw [circuitImageAtMost]
    simp only [Set.mem_iUnion]
    refine ⟨⟨0, Nat.zero_lt_succ s⟩, ?_⟩
    rw [circuitImageExact]
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨A, Fin.elim0, rfl⟩
  have hε : 0 < ε :=
    ((isCompact_circuitMatrixImageAtMost n s).isClosed.notMem_iff_infDist_pos hne).mp hU
  refine ⟨ε, hε, ?_⟩
  intro V hV
  simpa [dist_eq_norm, norm_sub_rev] using
    (Metric.infDist_le_dist_of_mem (x := U) hV)

/-- Operational form: if no budget-`s` continuous circuit implements a
unitary exactly, then one common positive error excludes every such circuit. -/
theorem exists_positive_operator_error_of_exact_circuit_exclusion
    {n s : ℕ} {U : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    (hU : ∀ C : TwoQubitCircuit n, C.gateCount ≤ s → C.eval ≠ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
      ε ≤ ‖(U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  have hnot : (U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∉
      circuitMatrixImageAtMost n s := by
    rintro ⟨V, hV, hVU⟩
    have hmem : U ∈ circuitImageAtMost n s := by
      have hVU' : V = U := Subtype.ext hVU
      simpa [hVU'] using hV
    obtain ⟨C, hC, hCU⟩ := mem_circuitImageAtMost_iff.mp hmem
    exact hU C hC hCU
  obtain ⟨ε, hε, hsep⟩ :=
    exists_pos_norm_sub_of_not_mem_circuitMatrixImageAtMost hnot
  refine ⟨ε, hε, ?_⟩
  intro C hC
  apply hsep
  refine ⟨C.eval, ?_, rfl⟩
  exact mem_circuitImageAtMost_iff.mpr ⟨C, hC, rfl⟩

end TwoQubitArchitecture

end

end GaloisForLFunctions.HTGeometry
