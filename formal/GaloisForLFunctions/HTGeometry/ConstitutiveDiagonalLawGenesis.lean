import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Diagonal law genesis

A Boolean self-evaluator cannot represent its complemented diagonal.  Adjoining one fresh row
realizes that challenge conservatively and minimally.  Iteration gives strict order on finite
ordinals.  Every finite part of the limiting all-true challenge is represented, but the whole
challenge is not; adjoining it at the limit produces an evaluator not isomorphic to that limit.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- A Boolean doctrine whose reporters and challenges use the same carrier. -/
abbrev BooleanSelfEvaluator (X : Type u) := X → X → Bool

/-- The challenge obtained by complementing self-evaluation. -/
def evaluatorAntiDiagonal {X : Type u} (E : BooleanSelfEvaluator X) : X → Bool :=
  fun x ↦ !(E x x)

/-- No existing reporter row represents the complemented diagonal challenge. -/
theorem evaluatorAntiDiagonal_ne_row {X : Type u} (E : BooleanSelfEvaluator X) (a : X) :
    (fun y ↦ E a y) ≠ evaluatorAntiDiagonal E := by
  intro h
  have ha := congrFun h a
  cases haa : E a a <;> simp [evaluatorAntiDiagonal, haa] at ha

/-- Carrier obtained by adjoining one fresh reporter. -/
abbrev EvaluatorSuccessorCarrier (X : Type u) := X ⊕ Fin 1

/-- Conservative one-point successor realizing the old anti-diagonal on old columns. -/
def evaluatorSuccessor {X : Type u} (E : BooleanSelfEvaluator X) :
    BooleanSelfEvaluator (EvaluatorSuccessorCarrier X)
  | Sum.inl x, Sum.inl y => E x y
  | Sum.inr _, Sum.inl y => evaluatorAntiDiagonal E y
  | _, Sum.inr _ => false

@[simp] theorem evaluatorSuccessor_old {X : Type u} (E : BooleanSelfEvaluator X)
    (x y : X) :
    evaluatorSuccessor E (Sum.inl x) (Sum.inl y) = E x y := rfl

@[simp] theorem evaluatorSuccessor_fresh_row {X : Type u} (E : BooleanSelfEvaluator X)
    (y : X) :
    evaluatorSuccessor E (Sum.inr 0) (Sum.inl y) = evaluatorAntiDiagonal E y := rfl

@[simp] theorem evaluatorSuccessor_fresh_column {X : Type u} (E : BooleanSelfEvaluator X)
    (x : EvaluatorSuccessorCarrier X) (k : Fin 1) :
    evaluatorSuccessor E x (Sum.inr k) = false := by
  cases x <;> rfl

/-- The fresh row is genuinely distinct from every transported old row. -/
theorem evaluatorSuccessor_fresh_ne_old {X : Type u} (E : BooleanSelfEvaluator X) (x : X) :
    (fun y ↦ evaluatorSuccessor E (Sum.inr 0) (Sum.inl y)) ≠
      fun y ↦ evaluatorSuccessor E (Sum.inl x) (Sum.inl y) := by
  simpa only [evaluatorSuccessor_fresh_row, evaluatorSuccessor_old] using
    (evaluatorAntiDiagonal_ne_row E x).symm

/-- A conservative extension equipped with a reporter realizing the old anti-diagonal. -/
structure BooleanEvaluatorExtension {X : Type u} (E : BooleanSelfEvaluator X) where
  Carrier : Type v
  embed : X → Carrier
  embed_injective : Function.Injective embed
  eval : BooleanSelfEvaluator Carrier
  realized : Carrier
  preserves : ∀ x y, eval (embed x) (embed y) = E x y
  realizes : ∀ y, eval realized (embed y) = evaluatorAntiDiagonal E y

/-- Every conservative realization of the anti-diagonal needs a genuinely new carrier point. -/
theorem BooleanEvaluatorExtension.realized_not_mem_range {X : Type u}
    {E : BooleanSelfEvaluator X} (ext : BooleanEvaluatorExtension E) :
    ext.realized ∉ Set.range ext.embed := by
  rintro ⟨x, hx⟩
  apply evaluatorAntiDiagonal_ne_row E x
  funext y
  calc
    E x y = ext.eval (ext.embed x) (ext.embed y) := (ext.preserves x y).symm
    _ = ext.eval ext.realized (ext.embed y) := by rw [hx]
    _ = evaluatorAntiDiagonal E y := ext.realizes y

/-- The canonical successor is a conservative realization using exactly one fresh point. -/
def canonicalBooleanEvaluatorExtension {X : Type u} (E : BooleanSelfEvaluator X) :
    BooleanEvaluatorExtension E where
  Carrier := EvaluatorSuccessorCarrier X
  embed := Sum.inl
  embed_injective := Sum.inl_injective
  eval := evaluatorSuccessor E
  realized := Sum.inr 0
  preserves := fun _ _ ↦ rfl
  realizes := fun _ ↦ rfl

/-- Relabelling equivalence of Boolean self-evaluators. -/
structure BooleanEvaluatorEquiv {X : Type u} {Y : Type v}
    (E : BooleanSelfEvaluator X) (F : BooleanSelfEvaluator Y) where
  relabel : X ≃ Y
  map_eval : ∀ x y, F (relabel x) (relabel y) = E x y

namespace BooleanEvaluatorEquiv

/-- Inverse relabelling equivalence. -/
def symm {X : Type u} {Y : Type v} {E : BooleanSelfEvaluator X}
    {F : BooleanSelfEvaluator Y} (h : BooleanEvaluatorEquiv E F) :
    BooleanEvaluatorEquiv F E where
  relabel := h.relabel.symm
  map_eval := by
    intro x y
    simpa using (h.map_eval (h.relabel.symm x) (h.relabel.symm y)).symm

/-- Diagonal succession is natural under relabelling. -/
def successor {X : Type u} {Y : Type v} {E : BooleanSelfEvaluator X}
    {F : BooleanSelfEvaluator Y} (h : BooleanEvaluatorEquiv E F) :
    BooleanEvaluatorEquiv (evaluatorSuccessor E) (evaluatorSuccessor F) where
  relabel := Equiv.sumCongr h.relabel (Equiv.refl (Fin 1))
  map_eval := by
    intro x y
    rcases x with x | k <;> rcases y with y | l
    · exact h.map_eval x y
    · rfl
    · simp [evaluatorSuccessor, evaluatorAntiDiagonal, h.map_eval]
    · rfl

end BooleanEvaluatorEquiv

/-- Finite stage of diagonal genesis: strict order as a Boolean evaluator. -/
def finiteDiagonalEvaluator (n : ℕ) : BooleanSelfEvaluator (Fin n) :=
  fun i j ↦ decide (j < i)

@[simp] theorem finiteDiagonalEvaluator_diagonal (n : ℕ) (i : Fin n) :
    finiteDiagonalEvaluator n i i = false := by
  simp [finiteDiagonalEvaluator]

@[simp] theorem finiteDiagonalEvaluator_antiDiagonal (n : ℕ) (i : Fin n) :
    evaluatorAntiDiagonal (finiteDiagonalEvaluator n) i = true := by
  simp [evaluatorAntiDiagonal]

/-- One diagonal successor is exactly the next finite strict-order evaluator up to canonical
relabelling. -/
def finiteDiagonalSuccessorEquiv (n : ℕ) :
    BooleanEvaluatorEquiv (evaluatorSuccessor (finiteDiagonalEvaluator n))
      (finiteDiagonalEvaluator (n + 1)) where
  relabel := finSumFinEquiv
  map_eval := by
    intro x y
    rcases x with i | k <;> rcases y with j | l
    · simp [finiteDiagonalEvaluator, evaluatorSuccessor, finSumFinEquiv_apply_left]
      simp only [Fin.lt_def, Fin.val_castAdd]
    · fin_cases l
      simp [finiteDiagonalEvaluator, evaluatorSuccessor, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right]
      apply Fin.le_iff_val_le_val.mpr
      rw [Fin.val_castAdd, Fin.val_natAdd]
      exact Nat.le_of_lt i.isLt
    · fin_cases k
      simp [finiteDiagonalEvaluator, evaluatorSuccessor, evaluatorAntiDiagonal,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
      apply Fin.lt_def.mpr
      rw [Fin.val_castAdd, Fin.val_natAdd]
      exact j.isLt
    · fin_cases k
      fin_cases l
      simp [finiteDiagonalEvaluator, evaluatorSuccessor, finSumFinEquiv_apply_right]

/-- Cofinal evaluator produced by the coherent union of all finite stages. -/
def diagonalLimitEvaluator : BooleanSelfEvaluator ℕ :=
  fun i j ↦ decide (j < i)

theorem diagonalLimit_restrict (n : ℕ) (i j : Fin n) :
    diagonalLimitEvaluator i j = finiteDiagonalEvaluator n i j := rfl

theorem diagonalLimit_row_support (i : ℕ) :
    {j : ℕ | diagonalLimitEvaluator i j = true} = Set.Iio i := by
  ext j
  simp [diagonalLimitEvaluator]

/-- Every row present at the filtered limit has finite true support. -/
theorem diagonalLimit_row_finite (i : ℕ) :
    Set.Finite {j : ℕ | diagonalLimitEvaluator i j = true} := by
  rw [diagonalLimit_row_support]
  exact Set.finite_Iio i

@[simp] theorem diagonalLimit_antiDiagonal (i : ℕ) :
    evaluatorAntiDiagonal diagonalLimitEvaluator i = true := by
  simp [evaluatorAntiDiagonal, diagonalLimitEvaluator]

/-- The cofinal constant-true challenge is not globally represented. -/
theorem diagonalLimit_constantTrue_not_row (i : ℕ) :
    (fun j ↦ diagonalLimitEvaluator i j) ≠ fun _ ↦ true := by
  intro h
  have hi := congrFun h i
  simp [diagonalLimitEvaluator] at hi

/-- Every finite observation of the cofinal challenge is represented by a sufficiently late row. -/
theorem diagonalLimit_realizes_finite_columns (s : Finset ℕ) :
    ∃ i : ℕ, ∀ j ∈ s, diagonalLimitEvaluator i j = true := by
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range s
  refine ⟨n, ?_⟩
  intro j hj
  have hjn : j < n := Finset.mem_range.mp (hn hj)
  simp [diagonalLimitEvaluator, hjn]

/-- A row dominates every other index except itself.  This is an evaluator-isomorphism invariant. -/
def EvaluatorHasTopRow {X : Type u} (E : BooleanSelfEvaluator X) : Prop :=
  ∃ x, ∀ y, y ≠ x → E x y = true

/-- Relabelling transports the existence of a top row. -/
theorem BooleanEvaluatorEquiv.hasTopRow {X : Type u} {Y : Type v}
    {E : BooleanSelfEvaluator X} {F : BooleanSelfEvaluator Y}
    (h : BooleanEvaluatorEquiv E F) : EvaluatorHasTopRow E → EvaluatorHasTopRow F := by
  rintro ⟨x, hx⟩
  refine ⟨h.relabel x, ?_⟩
  intro y hy
  let z := h.relabel.symm y
  have hyz : h.relabel z = y := h.relabel.apply_symm_apply y
  have hzx : z ≠ x := by
    intro hzx
    apply hy
    rw [← hyz, hzx]
  rw [← hyz, h.map_eval]
  exact hx z hzx

/-- The filtered limit has no top row. -/
theorem diagonalLimit_not_hasTopRow : ¬ EvaluatorHasTopRow diagonalLimitEvaluator := by
  rintro ⟨i, hi⟩
  have hbad := hi (i + 1) (by omega)
  simp [diagonalLimitEvaluator] at hbad

/-- The diagonal successor of the filtered limit has a fresh top row. -/
theorem diagonalLimit_successor_hasTopRow :
    EvaluatorHasTopRow (evaluatorSuccessor diagonalLimitEvaluator) := by
  refine ⟨Sum.inr 0, ?_⟩
  intro y hy
  rcases y with j | k
  · simp [evaluatorSuccessor, evaluatorAntiDiagonal, diagonalLimitEvaluator]
  · have hk : k = 0 := Subsingleton.elim _ _
    subst k
    exact (hy rfl).elim

/-- Therefore the filtered limit and its diagonal successor are not evaluator-isomorphic. -/
theorem diagonalLimit_equiv_successor_isEmpty :
    IsEmpty (BooleanEvaluatorEquiv diagonalLimitEvaluator
      (evaluatorSuccessor diagonalLimitEvaluator)) := by
  constructor
  intro h
  exact diagonalLimit_not_hasTopRow
    (h.symm.hasTopRow diagonalLimit_successor_hasTopRow)

theorem diagonalLimit_successor_fresh_old_support :
    {j : ℕ | evaluatorSuccessor diagonalLimitEvaluator (Sum.inr 0) (Sum.inl j) = true} =
      Set.univ := by
  ext j
  simp [evaluatorSuccessor, evaluatorAntiDiagonal, diagonalLimitEvaluator]

/-- The new limit row has infinite support on the old carrier. -/
theorem diagonalLimit_successor_fresh_old_support_infinite :
    Set.Infinite
      {j : ℕ | evaluatorSuccessor diagonalLimitEvaluator (Sum.inr 0) (Sum.inl j) = true} := by
  rw [diagonalLimit_successor_fresh_old_support]
  exact Set.infinite_univ

/-- Unconditional capstone: source-normal diagonal birth at every finite stage and exact failure
of finite/cofinal exchange at the filtered limit. -/
theorem diagonalLawGenesis_unconditional :
    (∀ (X : Type u) (E : BooleanSelfEvaluator X) (a : X),
      (fun y ↦ E a y) ≠ evaluatorAntiDiagonal E) ∧
    (∀ (X : Type u) (E : BooleanSelfEvaluator X),
      (canonicalBooleanEvaluatorExtension E).realized ∉
        Set.range (canonicalBooleanEvaluatorExtension E).embed) ∧
    (∀ n : ℕ,
      Nonempty (BooleanEvaluatorEquiv (evaluatorSuccessor (finiteDiagonalEvaluator n))
        (finiteDiagonalEvaluator (n + 1)))) ∧
    (∀ i : ℕ, Set.Finite {j : ℕ | diagonalLimitEvaluator i j = true}) ∧
    (∀ s : Finset ℕ, ∃ i : ℕ, ∀ j ∈ s, diagonalLimitEvaluator i j = true) ∧
    IsEmpty (BooleanEvaluatorEquiv diagonalLimitEvaluator
      (evaluatorSuccessor diagonalLimitEvaluator)) := by
  exact ⟨(fun _ E a ↦ evaluatorAntiDiagonal_ne_row E a),
    (fun _ E ↦ (canonicalBooleanEvaluatorExtension E).realized_not_mem_range),
    (fun n ↦ ⟨finiteDiagonalSuccessorEquiv n⟩),
    diagonalLimit_row_finite,
    diagonalLimit_realizes_finite_columns,
    diagonalLimit_equiv_successor_isEmpty⟩

end GaloisForLFunctions.HTGeometry
