import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetLoopAlgebra
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetLoopDescent

/-!
# One-sided velocity erasure collapses the common horizon field

Two chart directions supply their elementary transvections at depth one, and one of them also at
depth two.  Bracketing the two depth-one packets against the extra depth-two mode produces the
traceless diagonal of the pair at depth one, and bracketing that diagonal repeatedly against a
current raises its depth by one each time while only rescaling the matrix.

So a single extra velocity mode on one side propagates to every depth, on every row: each row keeps
a current family of all depths, and the highest-jet descent then forces the observable to be
constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The traceless diagonal of the chart pair -/

/-- The traceless diagonal of the two chart directions. -/
def chartDiag (i j : n) (K : Type*) [Field K] : Matrix n n K :=
  Matrix.single i i (1 : K) - Matrix.single j j (1 : K)

theorem chartDiag_commutator_of_ne {i j a : n} (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j) :
    chartDiag i j K * Matrix.single a i (1 : K) -
        Matrix.single a i (1 : K) * chartDiag i j K =
      (-1 : K) • Matrix.single a i (1 : K) := by
  have p1 : Matrix.single i i (1 : K) * Matrix.single a i (1 : K) = 0 := by simp [Ne.symm hai]
  have p2 : Matrix.single j j (1 : K) * Matrix.single a i (1 : K) = 0 := by simp [Ne.symm haj]
  have p3 : Matrix.single a i (1 : K) * Matrix.single i i (1 : K) =
      Matrix.single a i (1 : K) := by simp
  have p4 : Matrix.single a i (1 : K) * Matrix.single j j (1 : K) = 0 := by simp [hij]
  rw [chartDiag, sub_mul, mul_sub, p1, p2, p3, p4]
  module

theorem chartDiag_commutator_self {i j : n} (hij : i ≠ j) :
    chartDiag i j K * Matrix.single j i (1 : K) -
        Matrix.single j i (1 : K) * chartDiag i j K =
      (-2 : K) • Matrix.single j i (1 : K) := by
  have p1 : Matrix.single i i (1 : K) * Matrix.single j i (1 : K) = 0 := by simp [hij]
  have p2 : Matrix.single j j (1 : K) * Matrix.single j i (1 : K) =
      Matrix.single j i (1 : K) := by simp
  have p3 : Matrix.single j i (1 : K) * Matrix.single i i (1 : K) =
      Matrix.single j i (1 : K) := by simp
  have p4 : Matrix.single j i (1 : K) * Matrix.single j j (1 : K) = 0 := by simp [hij]
  rw [chartDiag, sub_mul, mul_sub, p1, p2, p3, p4]
  module

theorem chartDiag_commutator_row {i j : n} (hij : i ≠ j) :
    chartDiag i j K * Matrix.single i j (1 : K) -
        Matrix.single i j (1 : K) * chartDiag i j K =
      (2 : K) • Matrix.single i j (1 : K) := by
  have p1 : Matrix.single i i (1 : K) * Matrix.single i j (1 : K) =
      Matrix.single i j (1 : K) := by simp
  have p2 : Matrix.single j j (1 : K) * Matrix.single i j (1 : K) = 0 := by simp [Ne.symm hij]
  have p3 : Matrix.single i j (1 : K) * Matrix.single i i (1 : K) = 0 := by simp [Ne.symm hij]
  have p4 : Matrix.single i j (1 : K) * Matrix.single j j (1 : K) =
      Matrix.single i j (1 : K) := by simp
  rw [chartDiag, sub_mul, mul_sub, p1, p2, p3, p4]
  module

/-! ## The generation chain -/

/-- **One-sided collapse.**  If the depth-one transvections of two distinct chart directions and the
depth-two transvections of one of them all annihilate a jet observable, the observable is
constant. -/
theorem exists_algebraMap_of_oneSided_annihilation [CharZero K] {i j : n} (hij : i ≠ j)
    {f : HomogeneousJetField n K}
    (hH0 : ∀ x : n, x ≠ i → jetLoopDerivation 0 (Matrix.single x i (1 : K)) f = 0)
    (hH1 : ∀ x : n, x ≠ i → jetLoopDerivation 1 (Matrix.single x i (1 : K)) f = 0)
    (hK0 : ∀ x : n, x ≠ j → jetLoopDerivation 0 (Matrix.single x j (1 : K)) f = 0) :
    ∃ c : K, f = algebraMap K (HomogeneousJetField n K) c := by
  classical
  -- the traceless diagonal appears at depth one
  have hD : jetLoopDerivation 1 (chartDiag i j K) f = 0 := by
    have h := jetLoopDerivation_lie_eq_zero (hH1 j (Ne.symm hij)) (hK0 i hij)
    rwa [show Matrix.single i j (1 : K) * Matrix.single j i (1 : K) -
        Matrix.single j i (1 : K) * Matrix.single i j (1 : K) = chartDiag i j K from by
      rw [chartDiag]; simp] at h
  -- every row other than the depth-two chart direction keeps all depths
  have hE : ∀ a : n, a ≠ i → ∀ k : ℕ,
      jetLoopDerivation k (Matrix.single a i (1 : K)) f = 0 := by
    intro a hai k
    induction k with
    | zero => exact hH0 a hai
    | succ k ih =>
        have h := jetLoopDerivation_lie_eq_zero ih hD
        by_cases haj : a = j
        · subst haj
          rw [chartDiag_commutator_self (Ne.symm hai), jetLoopDerivation_smul,
            Derivation.smul_apply] at h
          exact (smul_eq_zero.1 h).resolve_left (by norm_num)
        · rw [chartDiag_commutator_of_ne hij hai haj, jetLoopDerivation_smul,
            Derivation.smul_apply] at h
          exact (smul_eq_zero.1 h).resolve_left (by norm_num)
  -- the depth-two chart direction keeps all depths through the other chart
  have hF : ∀ k : ℕ, jetLoopDerivation k (Matrix.single i j (1 : K)) f = 0 := by
    intro k
    induction k with
    | zero => exact hK0 i hij
    | succ k ih =>
        have h := jetLoopDerivation_lie_eq_zero ih hD
        rw [chartDiag_commutator_row hij, jetLoopDerivation_smul, Derivation.smul_apply] at h
        exact (smul_eq_zero.1 h).resolve_left (by norm_num)
  refine exists_algebraMap_of_forall_jetLoopDerivation (fun a => if a = i then j else i) ?_
  intro a k
  by_cases hai : a = i
  · subst hai
    rw [if_pos rfl]
    exact hF k
  · rw [if_neg hai]
    exact hE a hai k

end

end GaloisForLFunctions.HTGeometry
