import GaloisForLFunctions.HTGeometry.ExponentialTowerJets
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import GaloisForLFunctions.HTGeometry.CascadeExactOrderUnconditional
import Mathlib.RingTheory.Derivation.Lie

/-!
# Observability of the exponential tower

The jets of the tower's top state carry no coordinate variable, so the Jacobian of the coordinate
together with those jets, taken against the partial derivatives, is block diagonal with a unit block.
A nonvanishing jet Jacobian therefore makes the coordinate and the jets algebraically independent, and
the tower satisfies no algebraic differential equation of order below its height.

At height two the determinant is a single variable, and the unit-cost law is unconditional there.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The jets avoid the coordinate -/

theorem pderiv_zero_towerMonomial (k : ℕ) :
    (MvPolynomial.pderiv (0 : ℕ)) (towerMonomial k) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [towerMonomial_succ, Derivation.leibniz, ih]
      have h : (MvPolynomial.pderiv (0 : ℕ)) (MvPolynomial.X (k + 1) : MvPolynomial ℕ ℂ) = 0 := by
        rw [MvPolynomial.pderiv_X_of_ne]
        omega
      rw [h]
      simp

/-- The coordinate derivation commutes with the tower derivation. -/
theorem pderiv_zero_towerDerivation (P : MvPolynomial ℕ ℂ) :
    (MvPolynomial.pderiv (0 : ℕ)) (towerDerivation P)
      = towerDerivation ((MvPolynomial.pderiv (0 : ℕ)) P) := by
  have hcomm :
      ⁅(MvPolynomial.pderiv (0 : ℕ) : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)),
        towerDerivation⁆ = 0 := by
    refine MvPolynomial.derivation_ext ?_
    intro k
    rw [Derivation.commutator_apply, towerDerivation_X, pderiv_zero_towerMonomial]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [MvPolynomial.pderiv_X_self]
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (by omega)]
      simp
  have := Derivation.commutator_apply
    (D1 := (MvPolynomial.pderiv (0 : ℕ) : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)))
    (D2 := towerDerivation) (a := P)
  rw [hcomm] at this
  have hzero : (0 : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)) P = 0 := rfl
  rw [hzero] at this
  linear_combination -this

theorem pderiv_zero_towerJet {N : ℕ} (hN : N ≠ 0) (i : ℕ) :
    (MvPolynomial.pderiv (0 : ℕ)) (towerJet N i) = 0 := by
  induction i with
  | zero =>
      rw [towerJet_zero, MvPolynomial.pderiv_X_of_ne (by omega)]
  | succ i ih =>
      rw [towerJet_succ, pderiv_zero_towerDerivation, ih]
      simp

/-! ## The Jacobian criterion for the tower -/

/-- **No low-order equation from a nonvanishing jet Jacobian.**  The coordinate contributes a unit
block, so only the jets' own Jacobian matters. -/
theorem not_differentiallyAlgebraicOfOrder_expTower_of_det {m : ℕ}
    (hdet : (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (m + 1) (j : ℕ))).det ≠ 0) :
    ¬ DifferentiallyAlgebraicOfOrder (expTower (m + 1)) m := by
  classical
  set v : Fin (m + 2) → MvPolynomial ℕ ℂ :=
    Fin.cons (MvPolynomial.X (0 : ℕ)) (fun j : Fin (m + 1) => towerJet (m + 1) (j : ℕ)) with hv
  set M : Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => (MvPolynomial.pderiv ((i : ℕ))) (v j) with hM
  have hrow0 : ∀ j : Fin (m + 2), M 0 j = if j = 0 then 1 else 0 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simp [hM, hv]
    · intro l
      have hne : (Fin.succ l : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero l
      simp only [hM, hv, Matrix.of_apply, Fin.cons_succ, Fin.val_zero]
      rw [pderiv_zero_towerJet (by omega)]
      simp [hne]
  have hdetM : M.det ≠ 0 := by
    rw [Matrix.det_succ_row_zero]
    have hsum : ∑ j : Fin (m + 2), (-1) ^ (j : ℕ) * M 0 j *
        (M.submatrix Fin.succ j.succAbove).det
        = (M.submatrix Fin.succ (Fin.succAbove 0)).det := by
      rw [Finset.sum_eq_single (0 : Fin (m + 2))]
      · simp [hrow0]
      · intro j _ hj
        rw [hrow0 j]
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin (m + 2))) h
    rw [hsum]
    have hsub : M.submatrix Fin.succ (Fin.succAbove 0)
        = Matrix.of fun i j : Fin (m + 1) =>
            (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (m + 1) (j : ℕ)) := by
      funext i j
      simp [hM, hv, Fin.succAbove_zero]
    rw [hsub]
    exact hdet
  refine not_differentiallyAlgebraicOfOrder_expTower ?_
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) (R := MvPolynomial ℕ ℂ)
    v (fun i => fun P => (MvPolynomial.pderiv ((i : ℕ))) P) ?_ ?_ ?_ M hdetM ?_
  · intro i a b; simp
  · intro i a b
    rw [Derivation.leibniz]
    simp
  · intro i c
    have : (algebraMap ℂ (MvPolynomial ℕ ℂ)) c = MvPolynomial.C c := rfl
    rw [this]
    simp
  · intro i j; rfl

/-! ## Height two -/

theorem towerJet_two_zero : towerJet 2 0 = MvPolynomial.X 2 := rfl

theorem towerJet_two_one :
    towerJet 2 1 = MvPolynomial.X 1 * MvPolynomial.X 2 := by
  rw [towerJet_succ, towerJet_zero, towerDerivation_X, towerMonomial]
  rw [show Finset.Icc 1 2 = {1, 2} from rfl]
  rw [Finset.prod_insert (by decide)]
  simp

/-- **The double exponential has differential order exactly two.**  Unconditional. -/
theorem exactDifferentialOrder_expTower_two : ExactDifferentialOrder (expTower 2) 2 := by
  have hall : ∀ i : ℕ, TranscendentalEntire ((fun _ => Complex.exp) i) :=
    fun _ => transcendentalEntire_exp
  have h1 : ∀ k, k < 2 → DifferentiallyAlgebraicOfOrder ((fun _ => Complex.exp) k) 1 :=
    fun _ _ => differentiallyAlgebraicOfOrder_one_exp
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall h1, ?_⟩
  intro m hm
  interval_cases m
  · exact not_differentiallyAlgebraicOfOrder_zero_entireCascade hall (by omega)
  · refine not_differentiallyAlgebraicOfOrder_expTower_of_det (m := 1) ?_
    have hentry : (Matrix.of fun i j : Fin 2 =>
        (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet 2 (j : ℕ)))
        = !![0, MvPolynomial.X 2; 1, MvPolynomial.X 1] := by
      funext i j
      fin_cases i <;> fin_cases j <;>
        simp [towerJet_two_one, Derivation.leibniz]
    rw [hentry, Matrix.det_fin_two_of]
    intro h0
    simp at h0


/-- **The unit-cost law for a tower, from its jet determinant.**  Order monotonicity turns the single
top-order statement into the exact order. -/
theorem exactDifferentialOrder_expTower_of_det {m : ℕ}
    (hdet : (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (m + 1) (j : ℕ))).det ≠ 0) :
    ExactDifferentialOrder (expTower (m + 1)) (m + 1) := by
  have hall : ∀ i : ℕ, TranscendentalEntire ((fun _ => Complex.exp) i) :=
    fun _ => transcendentalEntire_exp
  have h1 : ∀ k, k < m + 1 → DifferentiallyAlgebraicOfOrder ((fun _ => Complex.exp) k) 1 :=
    fun _ _ => differentiallyAlgebraicOfOrder_one_exp
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall h1, ?_⟩
  intro k hk hDA
  exact not_differentiallyAlgebraicOfOrder_expTower_of_det hdet
    (hDA.mono (by omega : k ≤ m))

/-! ## Height three -/

theorem towerMonomial_one : towerMonomial 1 = MvPolynomial.X 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, towerMonomial_succ, towerMonomial_zero, one_mul]

theorem towerMonomial_two :
    towerMonomial 2 = MvPolynomial.X 1 * MvPolynomial.X 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, towerMonomial_succ, towerMonomial_one]

theorem towerMonomial_three :
    towerMonomial 3 = MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, towerMonomial_succ, towerMonomial_two]

theorem towerJet_three_one :
    towerJet 3 1 = MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  rw [towerJet_succ, towerJet_zero, towerDerivation_X, towerMonomial_three]

theorem towerJet_three_two :
    towerJet 3 2 =
      MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3
        + MvPolynomial.X 1 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3
        + MvPolynomial.X 1 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 2
            * MvPolynomial.X 3 := by
  rw [towerJet_succ, towerJet_three_one]
  simp only [Derivation.leibniz, towerDerivation_X, towerMonomial_one, towerMonomial_two,
    towerMonomial_three, smul_eq_mul]
  ring

/-- **The triple exponential has differential order exactly three.**  Unconditional. -/
theorem exactDifferentialOrder_expTower_three : ExactDifferentialOrder (expTower 3) 3 := by
  refine exactDifferentialOrder_expTower_of_det (m := 2) ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun _ : ℕ => (1 : ℂ))) h0
  rw [map_zero, RingHom.map_det] at h1
  have hmat : ((MvPolynomial.eval (fun _ : ℕ => (1 : ℂ))).mapMatrix
      (Matrix.of fun i j : Fin 3 =>
        (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (2 + 1) (j : ℕ))))
      = !![0, 1, 5; 0, 1, 4; 1, 1, 3] := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [towerJet_three_one, towerJet_three_two, Derivation.leibniz] <;> ring
  rw [hmat, Matrix.det_fin_three] at h1
  simp at h1
  norm_num at h1

end GaloisForLFunctions.HTGeometry
