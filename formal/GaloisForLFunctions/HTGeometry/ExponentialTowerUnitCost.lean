import GaloisForLFunctions.HTGeometry.ExponentialTowerSumJacobian
import GaloisForLFunctions.HTGeometry.ExponentialTowerObservability

/-!
# The exponential tower has differential order equal to its height

Two terminal-linear Bell reductions carry the output-jet determinant of the tower's top state down to
the partial-sum Jacobian: the top state's logarithmic derivative is the top monomial's cofactor, and
that monomial's logarithmic derivative is the partial sum below it.  Both cofactors avoid the variable
being eliminated, so each step drops one coordinate and contributes a nonzero factor.

Since the partial-sum Jacobian is nonzero at every height, so is the output-jet determinant, and the
`n`-fold exponential satisfies no algebraic differential equation of order below `n`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The Jacobian of the jets of the top monomial against the coordinates. -/
noncomputable def monomialJetJacobian (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial ℕ ℂ) :=
  Matrix.of fun i j => (MvPolynomial.pderiv ((j : ℕ) + 1))
    (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(i : ℕ)]) (towerMonomial r))

theorem pderiv_towerMonomial_succ (m : ℕ) :
    (MvPolynomial.pderiv (m + 1)) (towerMonomial (m + 1)) = towerMonomial m := by
  rw [towerMonomial_succ, Derivation.leibniz, MvPolynomial.pderiv_X_self,
    pderiv_eq_zero_of_mem_lowAlg (by omega : m < m + 1) (towerMonomial_mem_lowAlg (le_refl m))]
  simp

/-- **The monomial jet Jacobian is nonzero.**  One Bell reduction takes it to the partial-sum
Jacobian. -/
theorem monomialJetJacobian_det_ne_zero : ∀ r : ℕ, (monomialJetJacobian (r + 1)).det ≠ 0 := by
  intro r
  match r with
  | 0 =>
      rw [Matrix.det_fin_one]
      have hval : monomialJetJacobian 1 0 0 = 1 := by
        simp only [monomialJetJacobian, Matrix.of_apply]
        rw [show (0 : Fin 1).val = 0 from rfl, Function.iterate_zero_apply,
          show (1 : ℕ) = 0 + 1 from rfl, towerMonomial_succ, towerMonomial_zero, one_mul,
          MvPolynomial.pderiv_X_self]
      rw [hval]
      exact one_ne_zero
  | (s + 1) =>
      have hmat : monomialJetJacobian (s + 2)
          = derivationIterateOutputJacobian towerDerivation s
              (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1))
              (towerMonomial (s + 2)) := by
        funext i j
        rfl
      have hδH : towerDerivation (towerMonomial (s + 2))
          = towerSum (s + 1) * towerMonomial (s + 2) := by
        rw [towerDerivation_towerMonomial]; ring
      have hterm : ∀ i : Fin (s + 1),
          (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (Fin.last (s + 1))
            (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(i : ℕ)])
              (towerSum (s + 1))) = 0 := by
        intro i
        exact pderiv_eq_zero_of_mem_lowAlg (k := s + 2) (by omega)
          (iterate_towerDerivation_mem_lowAlg (towerSum_mem_lowAlg (le_refl (s + 1))) _)
      have hred := derivationIterateOutputJacobian_det_terminalScaled towerDerivation s
        (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1))
        (towerMonomial (s + 2)) (towerSum (s + 1)) hδH hterm
      have hlow : derivationLowerJetJacobian towerDerivation s
          (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (towerSum (s + 1))
          = sumJacobian (s + 1) := by
        funext i j
        rfl
      have hterminal :
          (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (Fin.last (s + 1))
            (towerMonomial (s + 2)) = towerMonomial (s + 1) := by
        show (MvPolynomial.pderiv (((Fin.last (s + 1) : Fin (s + 2)) : ℕ) + 1))
          (towerMonomial (s + 2)) = towerMonomial (s + 1)
        exact pderiv_towerMonomial_succ (s + 1)
      rw [hmat, hred, hlow, hterminal]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (sumJacobian_det_ne_zero s)
      · exact pow_ne_zero _ (by norm_num : (-1 : MvPolynomial ℕ ℂ) ≠ 0)
      · exact towerMonomial_ne_zero (s + 1)
      · exact pow_ne_zero _ (towerMonomial_ne_zero (s + 2))

/-- **The output-jet determinant of the tower is nonzero.** -/
theorem towerJet_det_ne_zero (m : ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (m + 1) (j : ℕ))).det ≠ 0 := by
  match m with
  | 0 =>
      rw [Matrix.det_fin_one]
      have hval : (Matrix.of fun i j : Fin 1 =>
          (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet 1 (j : ℕ))) 0 0 = 1 := by
        simp only [Matrix.of_apply]
        show (MvPolynomial.pderiv (0 + 1)) (towerJet 1 0) = 1
        rw [towerJet_zero, MvPolynomial.pderiv_X_self]
      rw [hval]
      exact one_ne_zero
  | (s + 1) =>
      have htrans : (Matrix.of fun i j : Fin (s + 2) =>
          (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (s + 2) (j : ℕ)))
          = (derivationIterateOutputJacobian towerDerivation s
              (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1))
              (MvPolynomial.X (s + 2))).transpose := by
        funext i j
        rfl
      rw [htrans, Matrix.det_transpose]
      have hδH : towerDerivation (MvPolynomial.X (s + 2))
          = towerMonomial (s + 1) * MvPolynomial.X (s + 2) := by
        rw [towerDerivation_X, towerMonomial_succ]
      have hterm : ∀ i : Fin (s + 1),
          (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (Fin.last (s + 1))
            (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(i : ℕ)])
              (towerMonomial (s + 1))) = 0 := by
        intro i
        exact pderiv_eq_zero_of_mem_lowAlg (k := s + 2) (by omega)
          (iterate_towerDerivation_mem_lowAlg (towerMonomial_mem_lowAlg (le_refl (s + 1))) _)
      have hred := derivationIterateOutputJacobian_det_terminalScaled towerDerivation s
        (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1))
        (MvPolynomial.X (s + 2)) (towerMonomial (s + 1)) hδH hterm
      have hlow : derivationLowerJetJacobian towerDerivation s
          (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (towerMonomial (s + 1))
          = monomialJetJacobian (s + 1) := by
        funext i j
        rfl
      have hterminal :
          (fun l : Fin (s + 2) => MvPolynomial.pderiv ((l : ℕ) + 1)) (Fin.last (s + 1))
            (MvPolynomial.X (s + 2) : MvPolynomial ℕ ℂ) = 1 := by
        show (MvPolynomial.pderiv (((Fin.last (s + 1) : Fin (s + 2)) : ℕ) + 1))
          (MvPolynomial.X (s + 2) : MvPolynomial ℕ ℂ) = 1
        exact MvPolynomial.pderiv_X_self (s + 2)
      rw [hred, hlow, hterminal]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ one_ne_zero) ?_)
        (monomialJetJacobian_det_ne_zero s)
      · exact pow_ne_zero _ (by norm_num : (-1 : MvPolynomial ℕ ℂ) ≠ 0)
      · exact pow_ne_zero _ (MvPolynomial.X_ne_zero (s + 2))

/-- **The unit-cost law for the exponential tower.**  The `n`-fold exponential has differential order
exactly `n`, for every `n ≥ 1`.  Unconditional. -/
theorem exactDifferentialOrder_expTower (m : ℕ) :
    ExactDifferentialOrder (expTower (m + 1)) (m + 1) :=
  exactDifferentialOrder_expTower_of_det (towerJet_det_ne_zero m)

end GaloisForLFunctions.HTGeometry
