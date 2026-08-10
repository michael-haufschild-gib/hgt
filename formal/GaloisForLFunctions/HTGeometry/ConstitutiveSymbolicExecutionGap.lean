import GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal
import Mathlib

/-!
# Symbolic admission versus executable repair

This module formalizes the first mechanism theorem of Symbolic--Execution Law Mechanics.
Local failure inequalities are necessary for a repair to decompose into legal grade-one pieces,
but a triangle failure family has locally admitted weights of arbitrarily high grade that admit no
such execution.  Their normalized profile and parity observer are nevertheless constant.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

universe u

/-- A weight is symbolically admitted at grade `m` when every failure kernel sees mass at least
`m`. -/
def WeightedLocalRepair {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ) : Prop :=
  ∀ K ∈ H, m ≤ ∑ i ∈ K, a i

/-- A weight is executable at grade `m` when it dominates a sum of `m` locally admitted
grade-one pieces. -/
def WeightedExecutableRepair {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ) : Prop :=
  ∃ pieces : Fin m → α → ℕ,
    (∀ j, WeightedLocalRepair H 1 (pieces j)) ∧
      ∀ i, ∑ j : Fin m, pieces j i ≤ a i

/-- Finite legal execution always implies symbolic local admission. -/
theorem weightedExecutableRepair_implies_local {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ)
    (h : WeightedExecutableRepair H m a) :
    WeightedLocalRepair H m a := by
  rintro K hKH
  obtain ⟨pieces, hlocal, hdom⟩ := h
  calc
    m = ∑ _j : Fin m, 1 := by simp
    _ ≤ ∑ j : Fin m, ∑ i ∈ K, pieces j i :=
      Finset.sum_le_sum fun j _hj => hlocal j K hKH
    _ = ∑ i ∈ K, ∑ j : Fin m, pieces j i := by rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ K, a i := Finset.sum_le_sum fun i _hi => hdom i

/-- The one-point failure system. -/
def unitFailureFamily : Finset (Finset PUnit) := {{PUnit.unit}}

/-- In the one-point system every locally admitted weight is executable. -/
theorem unitLocalRepair_executable (m : ℕ) (a : PUnit → ℕ)
    (h : WeightedLocalRepair unitFailureFamily m a) :
    WeightedExecutableRepair unitFailureFamily m a := by
  have hm : m ≤ a PUnit.unit := by
    have h' := h {PUnit.unit} (by simp [unitFailureFamily])
    simpa using h'
  refine ⟨fun _j _i => 1, ?_, ?_⟩
  · intro j K hK
    have hKeq : K = {PUnit.unit} := by
      simpa [unitFailureFamily] using hK
    subst K
    simp
  · intro i
    cases i
    simpa using hm

/-- Symbolic admission and execution coincide in the one-point system. -/
theorem unitLocalRepair_iff_executable (m : ℕ) (a : PUnit → ℕ) :
    WeightedLocalRepair unitFailureFamily m a ↔
      WeightedExecutableRepair unitFailureFamily m a := by
  exact ⟨unitLocalRepair_executable m a,
    weightedExecutableRepair_implies_local unitFailureFamily m a⟩

/-- The three pairwise failure kernels of a triangle. -/
def triangleFailureFamily : Finset (Finset (Fin 3)) :=
  {{0, 1}, {1, 2}, {0, 2}}

/-- Uniform weight `n` on the triangle vertices. -/
def triangleSymbolicWeight (n : ℕ) (_ : Fin 3) : ℕ := n

/-- Uniform triangle weight `n` is symbolically admitted at grade `2n`. -/
theorem triangleSymbolicWeight_local (n : ℕ) :
    WeightedLocalRepair triangleFailureFamily (2 * n)
      (triangleSymbolicWeight n) := by
  intro K hK
  simp only [triangleFailureFamily, Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with hK | hK | hK <;> subst K <;>
    simp [triangleSymbolicWeight]

/-- Every grade-one triangle repair spends at least two units of total weight. -/
theorem triangle_gradeOne_total_ge_two (b : Fin 3 → ℕ)
    (h : WeightedLocalRepair triangleFailureFamily 1 b) :
    2 ≤ ∑ i : Fin 3, b i := by
  have h01 := h {0, 1} (by simp [triangleFailureFamily])
  have h12 := h {1, 2} (by simp [triangleFailureFamily])
  have h02 := h {0, 2} (by simp [triangleFailureFamily])
  simp at h01 h12 h02
  rw [Fin.sum_univ_three]
  omega

/-- Positive uniform triangle weight `n` cannot execute its symbolically admitted grade `2n`:
legal pieces require total weight at least `4n`, while the target contains only `3n`. -/
theorem triangleSymbolicWeight_not_executable (n : ℕ) (hn : 0 < n) :
    ¬ WeightedExecutableRepair triangleFailureFamily (2 * n)
      (triangleSymbolicWeight n) := by
  rintro ⟨pieces, hlocal, hdom⟩
  have hlower : 4 * n ≤ ∑ j : Fin (2 * n), ∑ i : Fin 3, pieces j i := by
    calc
      4 * n = ∑ _j : Fin (2 * n), 2 := by simp; omega
      _ ≤ ∑ j : Fin (2 * n), ∑ i : Fin 3, pieces j i :=
        Finset.sum_le_sum fun j _hj => triangle_gradeOne_total_ge_two (pieces j) (hlocal j)
  have hupper : (∑ j : Fin (2 * n), ∑ i : Fin 3, pieces j i) ≤ 3 * n := by
    calc
      (∑ j : Fin (2 * n), ∑ i : Fin 3, pieces j i) =
          ∑ i : Fin 3, ∑ j : Fin (2 * n), pieces j i := by rw [Finset.sum_comm]
      _ ≤ ∑ i : Fin 3, triangleSymbolicWeight n i :=
        Finset.sum_le_sum fun i _hi => hdom i
      _ = 3 * n := by simp [triangleSymbolicWeight]
  omega

/-- Grade-normalized triangle profile. -/
def triangleNormalizedProfile (n : ℕ) (_ : Fin 3) : ℚ :=
  (n : ℚ) / (2 * n : ℕ)

/-- Grade parity recorded by the relaxed observer. -/
def triangleGradeParity (n : ℕ) : ZMod 2 := ((2 * n : ℕ) : ZMod 2)

/-- Relaxed observer retaining normalized profile and grade parity. -/
def triangleRelaxedObserver (n : ℕ) : (Fin 3 → ℚ) × ZMod 2 :=
  (triangleNormalizedProfile n, triangleGradeParity n)

/-- Every positive uniform symbolic grade has normalized profile `(1/2,1/2,1/2)`. -/
theorem triangleNormalizedProfile_eq_half (n : ℕ) (hn : 0 < n) :
    triangleNormalizedProfile n = fun _ : Fin 3 => (1 : ℚ) / 2 := by
  funext i
  change (n : ℚ) / (2 * n : ℕ) = (1 : ℚ) / 2
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [show ((2 * n : ℕ) : ℚ) = 2 * (n : ℚ) by norm_num]
  field_simp [hnq]

/-- Every even symbolic grade has zero parity. -/
theorem triangleGradeParity_eq_zero (n : ℕ) : triangleGradeParity n = 0 := by
  rw [triangleGradeParity, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- The relaxed observer is constant along all positive uniform symbolic grades. -/
theorem triangleRelaxedObserver_constant (n : ℕ) (hn : 0 < n) :
    triangleRelaxedObserver n = ((fun _ : Fin 3 => (1 : ℚ) / 2), 0) := by
  apply Prod.ext
  · exact triangleNormalizedProfile_eq_half n hn
  · exact triangleGradeParity_eq_zero n

/-- Positive symbolic grades escape every finite bound. -/
theorem triangleExecutionGrade_unbounded (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ N < 2 * n := by
  exact ⟨N + 1, by omega, by omega⟩

/-- Closed capstone: necessity, the exact one-kernel boundary, the triangle symbolic--execution
gap with observer erasure, and unbounded exact grade. -/
theorem symbolicExecutionGapMechanism_closed :
    (∀ (α : Type) (_ : DecidableEq α) (H : Finset (Finset α))
      (m : ℕ) (a : α → ℕ),
      WeightedExecutableRepair H m a → WeightedLocalRepair H m a) ∧
    (∀ m : ℕ, ∀ a : PUnit → ℕ,
      WeightedLocalRepair unitFailureFamily m a ↔
        WeightedExecutableRepair unitFailureFamily m a) ∧
    (∀ n : ℕ, 0 < n →
      WeightedLocalRepair triangleFailureFamily (2 * n) (triangleSymbolicWeight n) ∧
      ¬ WeightedExecutableRepair triangleFailureFamily (2 * n) (triangleSymbolicWeight n) ∧
      triangleRelaxedObserver n = ((fun _ : Fin 3 => (1 : ℚ) / 2), 0)) ∧
    (∀ N : ℕ, ∃ n : ℕ, 0 < n ∧ N < 2 * n) := by
  refine ⟨?_, unitLocalRepair_iff_executable, ?_, triangleExecutionGrade_unbounded⟩
  · intro α inst H m a h
    letI : DecidableEq α := inst
    exact weightedExecutableRepair_implies_local H m a h
  · intro n hn
    exact ⟨triangleSymbolicWeight_local n,
      triangleSymbolicWeight_not_executable n hn,
      triangleRelaxedObserver_constant n hn⟩

end GaloisForLFunctions.HTGeometry
