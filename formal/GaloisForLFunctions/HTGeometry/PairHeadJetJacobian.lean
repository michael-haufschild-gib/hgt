import GaloisForLFunctions.HTGeometry.PairHeadProduct
import GaloisForLFunctions.HTGeometry.GenBellBorderedRows

/-!
# The head product's Jacobian is the peel's orbit determinant

The head product is logarithmically linear, so its jets are the product times the affine Bell values
of its multiplier, and its Jacobian has the uniformly scaled shape.  Row reduction against the first
row turns the determinant into a power of the product times a bordered determinant; the border row
is the gradient of the product, which is the product times the border row of the peel; and the Bell
rows may be replaced by the jet rows of the multiplier, which are the orbit of that same border row.

So the head product's jet Jacobian is a nonzero power of the product times exactly the determinant
the peel proves nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-- The Jacobian of the jets of the head product. -/
noncomputable def pairHeadJetJacobian (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ)
    (m : ℕ) : Matrix (Fin m) (Fin m) CascadeField :=
  Matrix.of fun i j => fpderiv ((j : ℕ) + 1)
    (((pairDerivation p : CascadeField → CascadeField)^[(i : ℕ)]) (pairHead p g m))

/-- The gradient of the head product. -/
noncomputable def pairHeadGradient (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ) (n : ℕ) :
    Fin (n + 1) → CascadeField :=
  fun j => fpderiv ((j : ℕ) + 1) (pairHead p g (n + 1))

/-- The gradients of the positive Bell values of the head product's multiplier. -/
noncomputable def pairHeadBellGradient (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ)
    (n : ℕ) : Fin n → Fin (n + 1) → CascadeField :=
  fun r j => fpderiv ((j : ℕ) + 1)
    (genJetA (pairDerivation p) (headSum p g (n + 1)) ((r : ℕ) + 1))

/-- **The head product's Jacobian has the uniformly scaled shape.** -/
theorem pairHeadJetJacobian_eq_uniform (hne : ∀ j, pairFactor (p j) j ≠ 0) {g : Polynomial ℂ}
    (hg : g ≠ 0) (n : ℕ) :
    pairHeadJetJacobian p g (n + 1)
      = uniformScaledMatrix (pairHead p g (n + 1)) (pairHeadGradient p g n)
          (fun r : Fin n => genJetA (pairDerivation p) (headSum p g (n + 1)) ((r : ℕ) + 1))
          (pairHeadBellGradient p g n) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [pairHeadJetJacobian, uniformScaledMatrix, pairHeadGradient]
  · have hjet : ((pairDerivation p : CascadeField → CascadeField)^[((r.succ : Fin (n + 1)) : ℕ)])
        (pairHead p g (n + 1))
        = pairHead p g (n + 1)
          * genJetA (pairDerivation p) (headSum p g (n + 1)) ((r : ℕ) + 1) := by
      rw [Fin.val_succ]
      exact iterate_pairDerivation_pairHead hne hg (n + 1) ((r : ℕ) + 1)
    simp only [pairHeadJetJacobian, Matrix.of_apply, uniformScaledMatrix, Fin.cases_succ, hjet,
      Derivation.leibniz, smul_eq_mul, pairHeadGradient, pairHeadBellGradient]

theorem pairHeadJetJacobian_det_eq (hne : ∀ j, pairFactor (p j) j ≠ 0) {g : Polynomial ℂ}
    (hg : g ≠ 0) (n : ℕ) :
    (pairHeadJetJacobian p g (n + 1)).det
      = pairHead p g (n + 1) ^ n
        * (uniformBordered (pairHeadGradient p g n) (pairHeadBellGradient p g n)).det := by
  rw [pairHeadJetJacobian_eq_uniform hne hg n, uniformScaledMatrix_det]

/-- **The head product scales out of the bordered determinant.** -/
theorem uniformBordered_pairHeadGradient_det (hne : ∀ j, pairFactor (p j) j ≠ 0)
    {g : Polynomial ℂ} (hg : g ≠ 0) (n : ℕ) (L : Fin n → Fin (n + 1) → CascadeField) :
    (uniformBordered (pairHeadGradient p g n) L).det
      = pairHead p g (n + 1)
        * (uniformBordered (fun j : Fin (n + 1) => headBorder p g (n + 1) ((j : ℕ) + 1)) L).det := by
  classical
  have hrow : uniformBordered (pairHeadGradient p g n) L
      = Matrix.of fun i j =>
        (Fin.cases (pairHead p g (n + 1)) (fun _ => (1 : CascadeField)) i)
          * (uniformBordered (fun j' : Fin (n + 1) => headBorder p g (n + 1) ((j' : ℕ) + 1)) L)
              i j := by
    funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [uniformBordered, Matrix.of_apply, Fin.cases_zero, pairHeadGradient]
      exact fpderiv_pairHead_eq hne hg (n + 1) ((j : ℕ) + 1)
    · simp [uniformBordered]
  rw [hrow, Matrix.det_mul_column]
  congr 1
  rw [Fin.prod_univ_succ]
  simp

/-- **The Bell rows are the jet rows of the multiplier.** -/
theorem uniformBordered_pairBell_det_eq (g : Polynomial ℂ) (n : ℕ)
    (a : Fin (n + 1) → CascadeField) :
    (uniformBordered a (pairHeadBellGradient p g n)).det
      = (uniformBordered a (fun k : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(k : ℕ)])
              (headSum p g (n + 1))))).det :=
  uniformBordered_genBell_det_eq (pairDerivation p) (headSum p g (n + 1)) n a

/-- **The bordered jet matrix is the peel's orbit matrix.** -/
theorem uniformBordered_eq_pairOrbitMatrix (g : Polynomial ℂ) (n : ℕ) :
    uniformBordered (fun j : Fin (n + 1) => headBorder p g (n + 1) ((j : ℕ) + 1))
        (fun k : Fin n => fun j : Fin (n + 1) =>
          fpderiv ((j : ℕ) + 1)
            (((pairDerivation p : CascadeField → CascadeField)^[(k : ℕ)])
              (headSum p g (n + 1))))
      = pairOrbitMatrix p (n + 1) (n + 1) (headBorder p g (n + 1)) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp only [uniformBordered, Matrix.of_apply, Fin.cases_zero, pairOrbitMatrix, Fin.val_zero,
      Function.iterate_zero, id_eq]
  · have hgrad := gradient_iterate_headSum (p := p) g (n + 1) (r : ℕ)
    have hval := congrArg (fun F : ℕ → CascadeField => F ((j : ℕ) + 1)) hgrad
    simp only [uniformBordered, Matrix.of_apply, Fin.cases_succ, pairOrbitMatrix, Fin.val_succ]
    exact hval

/-- **The head product's jet Jacobian is nonsingular.** -/
theorem pairHeadJetJacobian_det_ne_zero (a b : ℕ → Polynomial ℂ)
    (hp : ∀ j, p j = affinePair (a j) (b j)) (ha : ∀ j, a j ≠ 0)
    {g : Polynomial ℂ} (hg : g ≠ 0) (m : ℕ) :
    (pairHeadJetJacobian p g m).det ≠ 0 := by
  have hne : ∀ j, pairFactor (p j) j ≠ 0 := by
    intro j
    rw [hp j]
    exact pairFactor_affinePair_ne_zero (ha j) (b j) j
  match m with
  | 0 =>
      rw [Matrix.det_fin_zero]
      exact one_ne_zero
  | (n + 1) =>
      rw [pairHeadJetJacobian_det_eq hne hg n,
        uniformBordered_pairBell_det_eq g n (pairHeadGradient p g n)]
      rw [uniformBordered_pairHeadGradient_det hne hg n, uniformBordered_eq_pairOrbitMatrix]
      refine mul_ne_zero (pow_ne_zero _ (pairHead_ne_zero hne hg (n + 1)))
        (mul_ne_zero (pairHead_ne_zero hne hg (n + 1)) ?_)
      exact det_pairOrbitMatrix_ne_zero_of_peelHyp a b hp ha n g hg _
        (pairPeelHyp_headBorder a b hp ha n g)

end GaloisForLFunctions.HTGeometry
