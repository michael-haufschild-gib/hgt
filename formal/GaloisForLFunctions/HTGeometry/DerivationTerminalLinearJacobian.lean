import GaloisForLFunctions.HTGeometry.DerivationBellChain
import GaloisForLFunctions.HTGeometry.BellCoordinateJacobian
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import GaloisForLFunctions.HTGeometry.TerminalLinearJacobian
import GaloisForLFunctions.HTGeometry.TerminalScaledJacobian

/-!
# Terminal-linear Jacobians for actual derivation iterates

This file realizes the universal Bell and bordered-matrix identities on an arbitrary commutative
complex algebra carrying a time derivation and coordinate derivations.  The required independence
condition is stated honestly: the terminal coordinate derivation must kill every lower `A`-jet
used in the finite determinant, not merely `A` itself.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- The common-frame Bell value built from the iterates of `A`. -/
def derivationBellValue
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (A : R) (n : ℕ) (i : Fin (n + 1)) : R :=
  aeval (fun j : Fin (n + 1) => ((δ : R → R)^[(j : ℕ)]) A)
    (bellAt n ((i : ℕ) + 1) i.isLt)

/-- Actual positive iterates of a terminal-linear element are the common-frame Bell values. -/
theorem derivation_iterate_terminalLinear_eq_derivationBellValue
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (x A : R) (hδx : δ x = A * x)
    (n : ℕ) (i : Fin (n + 1)) :
    ((δ : R → R)^[(i : ℕ) + 1]) x = x * derivationBellValue δ A n i := by
  have h := derivation_iterate_terminalLinear_eq_bellCore δ x A hδx ((i : ℕ) + 1)
  simpa [derivationBellValue, bellAt, MvPolynomial.aeval_rename, Function.comp_def] using h

/-- Jacobian of the lower `A`-jet with respect to the lower coordinate derivations. -/
def derivationLowerJetJacobian
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (A : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => partial j.castSucc (((δ : R → R)^[(i : ℕ)]) A)

/-- Jacobian of the Bell values with respect to the lower coordinate derivations. -/
def derivationBellValueJacobian
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (A : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => partial j.castSucc (derivationBellValue δ A n i)

/-- The coordinate chain rule factors the Bell-value Jacobian through the unit Bell matrix. -/
theorem derivationBellValueJacobian_eq_mul
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (A : R) :
    derivationBellValueJacobian δ n partial A =
      ((bellCoordinateJacobian n).map
        (aeval fun j : Fin (n + 1) => ((δ : R → R)^[(j : ℕ)]) A)).transpose *
          derivationLowerJetJacobian δ n partial A := by
  funext i j
  rw [Matrix.mul_apply]
  simp only [derivationBellValueJacobian, derivationBellValue, Matrix.transpose_apply,
    Matrix.map_apply, bellCoordinateJacobian, derivationLowerJetJacobian]
  exact derivation_aeval_eq_sum_pderiv (partial j.castSucc)
    (fun k : Fin (n + 1) => ((δ : R → R)^[(k : ℕ)]) A)
    (bellAt n ((i : ℕ) + 1) i.isLt)

/-- Bell transformation preserves the determinant of the actual lower-jet coordinate Jacobian. -/
theorem derivationBellValueJacobian_det
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (A : R) :
    (derivationBellValueJacobian δ n partial A).det =
      (derivationLowerJetJacobian δ n partial A).det := by
  rw [derivationBellValueJacobian_eq_mul, Matrix.det_mul, Matrix.det_transpose]
  let ev : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] R :=
    aeval fun j : Fin (n + 1) => ((δ : R → R)^[(j : ℕ)]) A
  have hmap := ev.map_det (bellCoordinateJacobian n)
  rw [bellCoordinateJacobian_det, map_one] at hmap
  have hdet : ((bellCoordinateJacobian n).map ev).det = 1 := by
    simpa [ev] using hmap.symm
  rw [hdet, one_mul]

/-- Jacobian of the first `n+2` actual time-derivation iterates of `x`. -/
def derivationIterateOutputJacobian
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (x : R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  fun i j => partial j (((δ : R → R)^[(i : ℕ)]) x)

/-- If the terminal coordinate kills the complete finite lower jet, it kills every corresponding
Bell value. -/
theorem derivationBellValue_terminal_partial_eq_zero
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (A : R)
    (hterminalA : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) A) = 0)
    (i : Fin (n + 1)) :
    partial (Fin.last (n + 1)) (derivationBellValue δ A n i) = 0 := by
  rw [derivationBellValue, derivation_aeval_eq_sum_pderiv]
  simp [hterminalA]

/-- The actual iterate Jacobian is exactly the terminal-linear bordered matrix. -/
theorem derivationIterateOutputJacobian_eq_terminalLinear
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (x A : R)
    (hδx : δ x = A * x)
    (hlowerx : ∀ j : Fin (n + 1), partial j.castSucc x = 0)
    (hterminalx : partial (Fin.last (n + 1)) x = 1)
    (hterminalA : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) A) = 0) :
    derivationIterateOutputJacobian δ n partial x =
      terminalLinearJacobianMatrix x
        (derivationBellValue δ A n)
        (derivationBellValueJacobian δ n partial A) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · refine Fin.lastCases ?_ (fun c => ?_) j
    · simpa [derivationIterateOutputJacobian] using hterminalx
    · simpa [derivationIterateOutputJacobian] using hlowerx c
  · rw [derivationIterateOutputJacobian,
      derivation_iterate_terminalLinear_eq_derivationBellValue δ x A hδx n r,
      Derivation.leibniz]
    simp only [smul_eq_mul]
    refine Fin.lastCases ?_ (fun c => ?_) j
    · rw [hterminalx,
        derivationBellValue_terminal_partial_eq_zero δ n partial A hterminalA r]
      simp [terminalLinearJacobianMatrix]
    · rw [hlowerx,
        show partial c.castSucc (derivationBellValue δ A n r) =
          derivationBellValueJacobian δ n partial A r c from rfl]
      simp [terminalLinearJacobianMatrix]

/-- The actual iterate Jacobian of an arbitrary terminal-scaled output has the row-shear form.
Unlike the terminal-coordinate case, the lower coordinate derivatives of `H` may be nonzero; they
cancel from the determinant rather than being assumed away. -/
theorem derivationIterateOutputJacobian_eq_terminalScaled
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (H U : R)
    (hδH : δ H = U * H)
    (hterminalU : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) U) = 0) :
    derivationIterateOutputJacobian δ n partial H =
      terminalScaledJacobianMatrix H
        (partial (Fin.last (n + 1)) H)
        (fun c => partial c.castSucc H)
        (derivationBellValue δ U n)
        (derivationBellValueJacobian δ n partial U) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · refine Fin.lastCases ?_ (fun c => ?_) j <;>
      simp [derivationIterateOutputJacobian, terminalScaledJacobianMatrix]
  · rw [derivationIterateOutputJacobian,
      derivation_iterate_terminalLinear_eq_derivationBellValue δ H U hδH n r,
      Derivation.leibniz]
    simp only [smul_eq_mul]
    refine Fin.lastCases ?_ (fun c => ?_) j
    · rw [derivationBellValue_terminal_partial_eq_zero δ n partial U hterminalU r]
      simp [terminalScaledJacobianMatrix]
    · simp [terminalScaledJacobianMatrix, derivationBellValueJacobian]

/-- **Actual terminal-linear output-Jacobian reduction.**  The first `n+2` time iterates of `x`
have the exact determinant predicted by the lower `A`-jet, including the cofactor sign. -/
theorem derivationIterateOutputJacobian_det
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (x A : R)
    (hδx : δ x = A * x)
    (hlowerx : ∀ j : Fin (n + 1), partial j.castSucc x = 0)
    (hterminalx : partial (Fin.last (n + 1)) x = 1)
    (hterminalA : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) A) = 0) :
    (derivationIterateOutputJacobian δ n partial x).det =
      (-1 : R) ^ (n + 1) * x ^ (n + 1) *
        (derivationLowerJetJacobian δ n partial A).det := by
  rw [derivationIterateOutputJacobian_eq_terminalLinear δ n partial x A hδx hlowerx
      hterminalx hterminalA,
    terminalLinearJacobianMatrix_det, derivationBellValueJacobian_det]

/-- **Actual positive-power Bell reduction, differential form.**  For `δH = U H`, the determinant
is the terminal derivative of `H`, times `H^(n+1)`, times the lower `U`-jet determinant, with the
exact cofactor sign. -/
theorem derivationIterateOutputJacobian_det_terminalScaled
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (H U : R)
    (hδH : δ H = U * H)
    (hterminalU : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) U) = 0) :
    (derivationIterateOutputJacobian δ n partial H).det =
      (-1 : R) ^ (n + 1) * partial (Fin.last (n + 1)) H * H ^ (n + 1) *
        (derivationLowerJetJacobian δ n partial U).det := by
  rw [derivationIterateOutputJacobian_eq_terminalScaled δ n partial H U hδH hterminalU,
    terminalScaledJacobianMatrix_det, derivationBellValueJacobian_det]

/-- Concrete power-coordinate form of the positive-power Bell reduction.  If the terminal
coordinate derivation kills `C` and sends `X` to one, then the surviving terminal derivative of
`C * X^q` is exactly `q * C * X^(q-1)`. -/
theorem derivationIterateOutputJacobian_det_terminalPower
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (C X U : R) (q : ℕ)
    (hδH : δ (C * X ^ q) = U * (C * X ^ q))
    (hterminalC : partial (Fin.last (n + 1)) C = 0)
    (hterminalX : partial (Fin.last (n + 1)) X = 1)
    (hterminalU : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) U) = 0) :
    (derivationIterateOutputJacobian δ n partial (C * X ^ q)).det =
      (-1 : R) ^ (n + 1) * ((q : R) * C * X ^ (q - 1)) *
        (C * X ^ q) ^ (n + 1) *
          (derivationLowerJetJacobian δ n partial U).det := by
  have ht : partial (Fin.last (n + 1)) (C * X ^ q) =
      (q : R) * C * X ^ (q - 1) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, hterminalC, hterminalX]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero]
    ring
  rw [derivationIterateOutputJacobian_det_terminalScaled δ n partial
      (C * X ^ q) U hδH hterminalU,
    ht]

/-- Over a field, a nonzero terminal state and nonzero lower-jet determinant give a nonzero full
output-jet determinant. -/
theorem derivationIterateOutputJacobian_det_ne_zero
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (x A : R)
    (hδx : δ x = A * x)
    (hlowerx : ∀ j : Fin (n + 1), partial j.castSucc x = 0)
    (hterminalx : partial (Fin.last (n + 1)) x = 1)
    (hterminalA : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) A) = 0)
    (hx : x ≠ 0)
    (hlower : (derivationLowerJetJacobian δ n partial A).det ≠ 0) :
    (derivationIterateOutputJacobian δ n partial x).det ≠ 0 := by
  rw [derivationIterateOutputJacobian_det δ n partial x A hδx hlowerx hterminalx hterminalA]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hx)) hlower

/-- Nonvanishing form of the concrete positive-power Bell determinant. -/
theorem derivationIterateOutputJacobian_det_terminalPower_ne_zero
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (C X U : R) (q : ℕ)
    (hδH : δ (C * X ^ q) = U * (C * X ^ q))
    (hterminalC : partial (Fin.last (n + 1)) C = 0)
    (hterminalX : partial (Fin.last (n + 1)) X = 1)
    (hterminalU : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) U) = 0)
    (hq : 0 < q) (hC : C ≠ 0) (hX : X ≠ 0)
    (hlower : (derivationLowerJetJacobian δ n partial U).det ≠ 0) :
    (derivationIterateOutputJacobian δ n partial (C * X ^ q)).det ≠ 0 := by
  rw [derivationIterateOutputJacobian_det_terminalPower δ n partial C X U q hδH
    hterminalC hterminalX hterminalU]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hq.ne') hC)
          (pow_ne_zero _ hX)))
      (pow_ne_zero _ (mul_ne_zero hC (pow_ne_zero _ hX))))
    hlower

/-- A nonzero actual output-jet determinant makes the corresponding derivation iterates
algebraically independent.  The transpose only reconciles the output-by-coordinate convention of
`derivationIterateOutputJacobian` with the coordinate-by-output convention of the general
domain-valued Jacobian criterion. -/
theorem algebraicIndependent_derivationIterates_of_det_ne_zero
    {R : Type*} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (x : R)
    (hdet : (derivationIterateOutputJacobian δ n partial x).det ≠ 0) :
    AlgebraicIndependent ℂ
      (fun i : Fin (n + 2) ⇒ ((δ : R → R)^[(i : ℕ)]) x) := by
  let M := (derivationIterateOutputJacobian δ n partial x).transpose
  have hM : M.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hdet
  refine HTGeometry.algebraicIndependent_of_domain_jacobian
    (K := ℂ) (R := R)
    (fun i : Fin (n + 2) ⇒ ((δ : R → R)^[(i : ℕ)]) x)
    (fun j ⇒ partial j)
    (fun j a b ⇒ map_add (partial j) a b)
    (fun j a b ⇒ by
      simpa only [Algebra.smul_def] using (partial j).leibniz a b)
    (fun j c ⇒ (partial j).map_algebraMap c)
    M hM ?_
  intro j i
  rfl

/-- **Actual terminal-linear algebraic-independence reduction.**  A nonzero terminal state and a
nonzero lower `A`-jet determinant force the first `n+2` actual time iterates of `x` to be
algebraically independent over `ℂ`. -/
theorem algebraicIndependent_derivationIterates_terminalLinear
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (x A : R)
    (hδx : δ x = A * x)
    (hlowerx : ∀ j : Fin (n + 1), partial j.castSucc x = 0)
    (hterminalx : partial (Fin.last (n + 1)) x = 1)
    (hterminalA : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) A) = 0)
    (hx : x ≠ 0)
    (hlower : (derivationLowerJetJacobian δ n partial A).det ≠ 0) :
    AlgebraicIndependent ℂ
      (fun i : Fin (n + 2) ⇒ ((δ : R → R)^[(i : ℕ)]) x) := by
  apply algebraicIndependent_derivationIterates_of_det_ne_zero δ n partial x
  exact derivationIterateOutputJacobian_det_ne_zero δ n partial x A hδx hlowerx
    hterminalx hterminalA hx hlower

/-- **Positive-power terminal observability capstone.**  Under the exact power-coordinate and
lower-jet nondegeneracy hypotheses, the first `n+2` actual time iterates of `C * X^q` are
algebraically independent over `ℂ`. -/
theorem algebraicIndependent_derivationIterates_terminalPower
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partial : Fin (n + 2) → Derivation ℂ R R) (C X U : R) (q : ℕ)
    (hδH : δ (C * X ^ q) = U * (C * X ^ q))
    (hterminalC : partial (Fin.last (n + 1)) C = 0)
    (hterminalX : partial (Fin.last (n + 1)) X = 1)
    (hterminalU : ∀ i : Fin (n + 1),
      partial (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) U) = 0)
    (hq : 0 < q) (hC : C ≠ 0) (hX : X ≠ 0)
    (hlower : (derivationLowerJetJacobian δ n partial U).det ≠ 0) :
    AlgebraicIndependent ℂ
      (fun i : Fin (n + 2) ⇒ ((δ : R → R)^[(i : ℕ)]) (C * X ^ q)) := by
  apply algebraicIndependent_derivationIterates_of_det_ne_zero δ n partial (C * X ^ q)
  exact derivationIterateOutputJacobian_det_terminalPower_ne_zero δ n partial C X U q hδH
    hterminalC hterminalX hterminalU hq hC hX hlower

end GaloisForLFunctions

end
