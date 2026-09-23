import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Exchangeable formation selection

The source-natural functional-equation history can alternate two reflected laws while remaining
two-periodic under the clock shift.  Two-slot orbit symmetrization cannot see the difference.  This
module proves the first nontrivial formation-descent law: the orbit-symmetrized three-slot
transposition defect is exactly one half of the reflected reporter square.

Summing over a finite separating reporter family gives a nonnegative complete defect.  Independent
formation depth multiplies it by the depth, so a uniform global work bound is equivalent to equality
of the two reflected reporter laws.  Reflection swaps the laws but preserves both defect and work.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section TensorFactorization

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Coordinate-free formation-interchange law.** The difference between the equal-phase and
alternating-phase orbit packets is the rank-one tensor square of the reflected-law difference. -/
theorem formationThinningTensorFactorization (p q : M) :
    (p ⊗ₜ[R] p + q ⊗ₜ[R] q) - (p ⊗ₜ[R] q + q ⊗ₜ[R] p) =
      (p - q) ⊗ₜ[R] (p - q) := by
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

end TensorFactorization

section PositiveReporter

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Positive/Gram shadow obtained by applying one real linear reporter to both tensor legs. -/
def formationThinningReporterDefect (φ : V →ₗ[ℝ] ℝ) (p q : V) : ℝ :=
  (φ p * φ p + φ q * φ q) - (φ p * φ q + φ q * φ p)

/-- The predicted positive-organ response is exactly the squared reflected reporter difference. -/
theorem formationThinningReporterDefect_eq_sq
    (φ : V →ₗ[ℝ] ℝ) (p q : V) :
    formationThinningReporterDefect φ p q = (φ p - φ q) ^ (2 : ℕ) := by
  unfold formationThinningReporterDefect
  ring

theorem formationThinningReporterDefect_nonneg
    (φ : V →ₗ[ℝ] ℝ) (p q : V) :
    0 ≤ formationThinningReporterDefect φ p q := by
  rw [formationThinningReporterDefect_eq_sq]
  positivity

/-- One reporter's positive shadow vanishes exactly when that reporter identifies the two laws. -/
theorem formationThinningReporterDefect_eq_zero_iff
    (φ : V →ₗ[ℝ] ℝ) (p q : V) :
    formationThinningReporterDefect φ p q = 0 ↔ φ p = φ q := by
  rw [formationThinningReporterDefect_eq_sq]
  constructor
  · intro h
    nlinarith [sq_nonneg (φ p - φ q)]
  · intro h
    rw [h, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

end PositiveReporter

/-- Orbit-symmetrized alternating probability of the cylinder `E,E,Eᶜ`. -/
def symAlternatingCylinder112 (p q : ℝ) : ℝ :=
  (p * q * (1 - p) + q * p * (1 - q)) / 2

/-- Orbit-symmetrized alternating probability of the transposed cylinder `E,Eᶜ,E`. -/
def symAlternatingCylinder121 (p q : ℝ) : ℝ :=
  (p * (1 - q) * p + q * (1 - p) * q) / 2

/-- The three-slot transposition defect is exactly one half of the reflected mass square. -/
theorem symAlternatingCylinder_gap (p q : ℝ) :
    symAlternatingCylinder121 p q - symAlternatingCylinder112 p q =
      (p - q) ^ (2 : ℕ) / 2 := by
  unfold symAlternatingCylinder121 symAlternatingCylinder112
  ring

/-- Three-slot exchangeability at one reporter occurs exactly when reflected masses agree. -/
theorem symAlternatingCylinder_eq_iff (p q : ℝ) :
    symAlternatingCylinder121 p q = symAlternatingCylinder112 p q ↔ p = q := by
  constructor
  · intro h
    have hzero : (p - q) ^ (2 : ℕ) / 2 = 0 := by
      rw [← symAlternatingCylinder_gap, h, sub_self]
    nlinarith [sq_nonneg (p - q)]
  · rintro rfl
    unfold symAlternatingCylinder121 symAlternatingCylinder112
    ring

/-- Two-slot orbit symmetrization is automatically blind to phase order. -/
theorem twoSlotOrbitSymmetrization_swap (p q : ℝ) :
    (p * q + q * p) / 2 = (q * p + p * q) / 2 := by
  ring

/-- Coincidence probability of one reporter on adjacent slots after phase averaging. -/
def phaseAveragedAdjacentCoincidence (p q : ℝ) : ℝ := p * q

/-- Coincidence probability after deleting one slot and retaining equal-parity slots. -/
def phaseAveragedSkippedCoincidence (p q : ℝ) : ℝ := (p ^ (2 : ℕ) + q ^ (2 : ℕ)) / 2

/-- A single deletion exposes exactly the reflected square hidden by shift stationarity. -/
theorem phaseAveragedSkipped_sub_adjacent (p q : ℝ) :
    phaseAveragedSkippedCoincidence p q - phaseAveragedAdjacentCoincidence p q =
      (p - q) ^ (2 : ℕ) / 2 := by
  unfold phaseAveragedSkippedCoincidence phaseAveragedAdjacentCoincidence
  ring

/-- Adjacent and one-deletion laws agree exactly at neutral reflected mass. -/
theorem phaseAveragedThinningConsistent_iff (p q : ℝ) :
    phaseAveragedSkippedCoincidence p q = phaseAveragedAdjacentCoincidence p q ↔ p = q := by
  constructor
  · intro h
    have hzero : (p - q) ^ (2 : ℕ) / 2 = 0 := by
      rw [← phaseAveragedSkipped_sub_adjacent, h, sub_self]
    nlinarith [sq_nonneg (p - q)]
  · rintro rfl
    unfold phaseAveragedSkippedCoincidence phaseAveragedAdjacentCoincidence
    ring

/-- Reporterwise commutation of phase averaging with deletion of one formation slot. -/
def PhaseAveragedThinningConsistent {ι : Type*} (p q : ι → ℝ) : Prop :=
  ∀ i, phaseAveragedSkippedCoincidence (p i) (q i) =
    phaseAveragedAdjacentCoincidence (p i) (q i)

/-- Formation-thinning consistency jointly reconstructs equality of the reflected reporter laws. -/
theorem phaseAveragedThinningConsistent_iff_laws_eq {ι : Type*} (p q : ι → ℝ) :
    PhaseAveragedThinningConsistent p q ↔ p = q := by
  constructor
  · intro h
    funext i
    exact (phaseAveragedThinningConsistent_iff (p i) (q i)).mp (h i)
  · rintro rfl
    intro i
    exact (phaseAveragedThinningConsistent_iff (p i) (p i)).mpr rfl

/-- Scalar exchangeability defect generated by the three-slot transposition. -/
def threeSlotExchangeDefect (p q : ℝ) : ℝ :=
  symAlternatingCylinder121 p q - symAlternatingCylinder112 p q

theorem threeSlotExchangeDefect_eq (p q : ℝ) :
    threeSlotExchangeDefect p q = (p - q) ^ (2 : ℕ) / 2 :=
  symAlternatingCylinder_gap p q

theorem threeSlotExchangeDefect_nonneg (p q : ℝ) :
    0 ≤ threeSlotExchangeDefect p q := by
  rw [threeSlotExchangeDefect_eq]
  positivity

/-- Functional-equation reflection swaps the laws but preserves the defect. -/
theorem threeSlotExchangeDefect_swap (p q : ℝ) :
    threeSlotExchangeDefect q p = threeSlotExchangeDefect p q := by
  simp only [threeSlotExchangeDefect_eq]
  ring

theorem threeSlotExchangeDefect_eq_zero_iff (p q : ℝ) :
    threeSlotExchangeDefect p q = 0 ↔ p = q := by
  rw [threeSlotExchangeDefect_eq]
  constructor
  · intro h
    nlinarith [sq_nonneg (p - q)]
  · rintro rfl
    simp

/-- A reporter family has full three-slot exchangeability when every transposition defect vanishes. -/
def ThreeSlotExchangeable {ι : Type*} (p q : ι → ℝ) : Prop :=
  ∀ i, symAlternatingCylinder121 (p i) (q i) =
    symAlternatingCylinder112 (p i) (q i)

/-- Complete three-slot descent reconstructs equality of the two reporter laws. -/
theorem threeSlotExchangeable_iff {ι : Type*} (p q : ι → ℝ) :
    ThreeSlotExchangeable p q ↔ p = q := by
  constructor
  · intro h
    funext i
    exact (symAlternatingCylinder_eq_iff (p i) (q i)).mp (h i)
  · rintro rfl
    intro i
    exact (symAlternatingCylinder_eq_iff (p i) (p i)).mpr rfl

/-- Complete finite-reporter exchangeability defect. -/
def finiteExchangeDefect {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, threeSlotExchangeDefect (p i) (q i)

theorem finiteExchangeDefect_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    0 ≤ finiteExchangeDefect p q := by
  exact Finset.sum_nonneg fun i _ => threeSlotExchangeDefect_nonneg (p i) (q i)

/-- Finite separating reporters jointly reconstruct equality from zero complete defect. -/
theorem finiteExchangeDefect_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    finiteExchangeDefect p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hz : ∀ i, threeSlotExchangeDefect (p i) (q i) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => threeSlotExchangeDefect_nonneg (p j) (q j))).mp h i
          (Finset.mem_univ i)
    funext i
    exact (threeSlotExchangeDefect_eq_zero_iff (p i) (q i)).mp (hz i)
  · rintro rfl
    simp [finiteExchangeDefect, threeSlotExchangeDefect_eq]

theorem finiteExchangeDefect_swap {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    finiteExchangeDefect q p = finiteExchangeDefect p q := by
  simp only [finiteExchangeDefect, threeSlotExchangeDefect_swap]

/-- Work of `n` independent three-slot reporter blocks. -/
def finiteExchangeWork {ι : Type*} [Fintype ι]
    (n : ℕ) (p q : ι → ℝ) : ℝ :=
  (n : ℝ) * finiteExchangeDefect p q

/-- Independent formation composition conserves work additively. -/
theorem finiteExchangeWork_add {ι : Type*} [Fintype ι]
    (m n : ℕ) (p q : ι → ℝ) :
    finiteExchangeWork (m + n) p q =
      finiteExchangeWork m p q + finiteExchangeWork n p q := by
  simp [finiteExchangeWork, Nat.cast_add]
  ring

/-- Functional-equation reflection preserves complete work. -/
theorem finiteExchangeWork_swap {ι : Type*} [Fintype ι]
    (n : ℕ) (p q : ι → ℝ) :
    finiteExchangeWork n q p = finiteExchangeWork n p q := by
  simp [finiteExchangeWork, finiteExchangeDefect_swap]

/-- **Global formation properness.** Uniformly bounded complete work along every independent
formation depth occurs exactly on the exchangeable locus. -/
theorem finiteExchangeWork_bounded_iff {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    (∃ C : ℝ, ∀ n : ℕ, finiteExchangeWork n p q ≤ C) ↔ p = q := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hpq
    have hdne : finiteExchangeDefect p q ≠ 0 :=
      mt (finiteExchangeDefect_eq_zero_iff p q).mp hpq
    have hdpos : 0 < finiteExchangeDefect p q :=
      lt_of_le_of_ne (finiteExchangeDefect_nonneg p q) (Ne.symm hdne)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / finiteExchangeDefect p q)
    have hstrict : C < finiteExchangeWork n p q := by
      rw [finiteExchangeWork]
      exact (div_lt_iff₀ hdpos).mp (by simpa [mul_comm] using hn)
    exact (not_lt_of_ge (hC n)) hstrict
  · rintro rfl
    refine ⟨0, ?_⟩
    intro n
    simp [finiteExchangeWork, finiteExchangeDefect, threeSlotExchangeDefect_eq]

/-- Formation-law capstone: three-slot descent, zero complete defect, and bounded global work are
equivalent descriptions of reflected-law equality. -/
theorem exchangeableFormationSelection_capstone {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) :
    ThreeSlotExchangeable p q ↔
      PhaseAveragedThinningConsistent p q ∧
        finiteExchangeDefect p q = 0 ∧
          ∃ C : ℝ, ∀ n : ℕ, finiteExchangeWork n p q ≤ C := by
  rw [threeSlotExchangeable_iff, phaseAveragedThinningConsistent_iff_laws_eq,
    finiteExchangeDefect_eq_zero_iff,
    finiteExchangeWork_bounded_iff]
  constructor
  · intro h
    exact ⟨h, h, h⟩
  · exact And.left

end

end GaloisForLFunctions.HTGeometry
