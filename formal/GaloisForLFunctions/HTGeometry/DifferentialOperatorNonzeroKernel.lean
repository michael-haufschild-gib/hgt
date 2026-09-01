import GaloisForLFunctions.HTGeometry.DifferentialOperatorFieldModule
import GaloisForLFunctions.HTGeometry.LinearSystemFundamentalMatrix
import GaloisForLFunctions.HTGeometry.DifferentialSolutionSpace

/-!
# Nonunit differential operators have nonzero solutions

Over a differentially closed field, every nonunit Ore differential operator has a nonzero vector
in its natural field-action kernel.  A positive-order operator is normalized to a monic scalar
equation and solved by one column of an invertible fundamental matrix.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

variable {K : Type*} [Field K] [Differential K]

/-- A solution of a companion system is the jet vector of its first coordinate. -/
theorem scalarCompanion_solution_eq_jetVec {n : ℕ} (hn : 0 < n) (a : Fin n → K)
    {v : Fin n → K} (hv : IsDifferentialSystemSolution (scalarCompanion a) v) :
    ∀ i : Fin n, v i = differentialJet (i : ℕ) (v ⟨0, hn⟩) := by
  have h : ∀ k : ℕ, ∀ hk : k < n,
      v ⟨k, hk⟩ = differentialJet k (v ⟨0, hn⟩) := by
    intro k
    induction k with
    | zero => intro; simp
    | succ k ih =>
        intro hklt
        have hkprev : k < n := by omega
        have hk0 : k + 1 ≠ n := by omega
        have hsys := hv ⟨k, hkprev⟩
        have hmul : (scalarCompanion a).mulVec v ⟨k, hkprev⟩ = v ⟨k + 1, hklt⟩ := by
          simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single ⟨k + 1, hklt⟩]
          · simp [scalarCompanion, hk0]
          · intro j _ hj
            have hjne : (j : ℕ) ≠ k + 1 := by
              intro heq
              exact hj (Fin.ext heq)
            simp [scalarCompanion, hk0, hjne]
          · simp
        rw [← hmul, ← hsys, ih hkprev, differentialJet_succ]
  intro i
  exact h i i.2

/-- The first coordinate of a companion-system solution satisfies the scalar equation. -/
theorem scalarCompanion_solution_first {n : ℕ} (hn : 0 < n) (a : Fin n → K)
    {v : Fin n → K} (hv : IsDifferentialSystemSolution (scalarCompanion a) v) :
    differentialJet n (v ⟨0, hn⟩) =
      ∑ i : Fin n, a i * differentialJet (i : ℕ) (v ⟨0, hn⟩) := by
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : (last : ℕ) + 1 = n := by simp [last]; omega
  have hsys := hv last
  have hmul : (scalarCompanion a).mulVec v last = ∑ i : Fin n, a i * v i := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [scalarCompanion, hlast]
  rw [hmul] at hsys
  have hjetlast := scalarCompanion_solution_eq_jetVec hn a hv last
  have hlhs : (v last)′ = differentialJet n (v ⟨0, hn⟩) := by
    rw [hjetlast, ← differentialJet_succ, hlast]
  rw [hlhs] at hsys
  rw [hsys]
  exact Finset.sum_congr rfl fun i _ => by
    rw [scalarCompanion_solution_eq_jetVec hn a hv i]

namespace DiffOp

/-- A nonzero order-zero operator is a unit. -/
theorem isUnit_of_degree_eq_zero {p : DiffOp K} (hp : p ≠ 0) (hdeg : degree p = 0) : IsUnit p := by
  have hpC : p = C (coeff p 0) := by
    apply ext
    intro n
    cases n with
    | zero => simp [C]
    | succ n =>
        rw [coeff_eq_zero_of_degree_lt (p := p) (by omega)]
        simp [C, coeff_mono]
  have hc : coeff p 0 ≠ 0 := by
    intro hc
    apply hp
    rw [hpC, hc]
    simp [C]
  rw [hpC]
  refine ⟨⟨C (coeff p 0), C (coeff p 0)⁻¹, ?_, ?_⟩, rfl⟩
  · rw [C_mul]
    simp [C, smul_mono, hc, one_def]
  · rw [C_mul]
    simp [C, smul_mono, hc, one_def]

/-- A nonunit operator has positive order. -/
theorem degree_pos_of_not_isUnit {p : DiffOp K} (hp : p ≠ 0) (hunit : ¬ IsUnit p) :
    0 < degree p := by
  by_contra h
  exact hunit (isUnit_of_degree_eq_zero hp (Nat.eq_zero_of_not_pos h))

/-- **Every nonunit differential operator has a nonzero solution over a differentially closed
field.** -/
theorem exists_ne_zero_fieldApply_eq_zero [Algebra ℚ K] [IsDifferentiallyClosed K]
    {p : DiffOp K} (hunit : ¬ IsUnit p) :
    ∃ x : K, x ≠ 0 ∧ fieldApply p x = 0 := by
  by_cases hp : p = 0
  · exact ⟨1, one_ne_zero, by simp [hp]⟩
  let n := degree p
  have hn : 0 < n := degree_pos_of_not_isUnit hp hunit
  have hlc : leadCoeff p ≠ 0 := leadCoeff_ne_zero hp
  let a : Fin n → K := fun i => -(coeff p (i : ℕ)) / leadCoeff p
  obtain ⟨P, hPunit, hPsys⟩ := exists_fundamentalMatrix (scalarCompanion a)
  have hrow : P (⟨0, hn⟩ : Fin n) ≠ 0 := by
    intro hzero
    have hdet : P.det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hn⟩ fun j =>
      congrFun hzero j
    exact (isUnit_iff_ne_zero.mp hPunit) hdet
  obtain ⟨j, hj⟩ : ∃ j : Fin n, P ⟨0, hn⟩ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hrow (funext h)
  let v : Fin n → K := fun i => P i j
  have hv : IsDifferentialSystemSolution (scalarCompanion a) v := by
    intro i
    have hentry := congrFun (congrFun hPsys i) j
    simpa [v, matrixDeriv_apply, Matrix.mul_apply, IsDifferentialSystemSolution,
      Matrix.mulVec, dotProduct] using hentry
  let x := v ⟨0, hn⟩
  refine ⟨x, hj, ?_⟩
  have hx := scalarCompanion_solution_first hn a hv
  have hsum := fieldApply_eq_sum p x (Finset.range (n + 1)) (fun m hm => by
    exact coeff_eq_zero_of_degree_lt (p := p) (by
      rw [Finset.mem_range] at hm
      omega))
  rw [Finset.sum_range_succ] at hsum
  rw [Finset.sum_range] at hsum
  have hlead : coeff p n = leadCoeff p := by rfl
  rw [hlead] at hsum
  change differentialJet n x =
    ∑ i : Fin n, (-coeff p (i : ℕ) / leadCoeff p) * differentialJet (i : ℕ) x at hx
  rw [hsum, hx]
  rw [Finset.mul_sum]
  have hterm : ∀ i : Fin n,
      leadCoeff p * ((-coeff p (i : ℕ) / leadCoeff p) * differentialJet (i : ℕ) x) =
        -(coeff p (i : ℕ) * differentialJet (i : ℕ) x) := by
    intro i
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_neg_distrib]
  abel

end DiffOp

end

end GaloisForLFunctions.HTGeometry
