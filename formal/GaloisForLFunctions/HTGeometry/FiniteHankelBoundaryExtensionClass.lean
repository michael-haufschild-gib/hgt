import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature
import GaloisForLFunctions.HTGeometry.HankelBoundaryFlux

/-!
# Projective extension class of a flat finite Hankel face

The first omitted coupling depends linearly on the chosen kernel vector and therefore changes sign
under reversal of that vector.  A singular Hankel face itself only determines the kernel line.
The canonical scalar is obtained by making the null polynomial monic.  This file proves that the
usual terminal product is the square of the terminal coefficient times that monic remainder.
Consequently its sign is intrinsic to the projective null line.
-/

open Matrix Polynomial

namespace HTGeometry

noncomputable section

/-- Canonically oriented first extension coordinate of a finite Hankel boundary. -/
def finiteHankelBoundaryMonicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  momentFunctional s
    (X ^ (n + 1) * finiteHankelNullMonicPolynomial c)

/-- The leading coefficient of the finite-coordinate null polynomial is its terminal coordinate. -/
theorem finiteHankelNullPolynomial_leadingCoeff_eq_terminal
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullPolynomial c).leadingCoeff = c (Fin.last n) := by
  rw [Polynomial.leadingCoeff, finiteHankelNullPolynomial_natDegree c hlast,
    finiteHankelNullPolynomial,
    Polynomial.ofFn_coeff_eq_val_of_lt c (Nat.lt_succ_self n)]
  apply congrArg c
  exact Fin.ext rfl

/-- Monic normalization divides the raw first remainder by the terminal coefficient. -/
theorem finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryMonicRemainder s c =
      (c (Fin.last n))⁻¹ *
        momentFunctional s (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
  rw [finiteHankelBoundaryMonicRemainder, finiteHankelNullMonicPolynomial]
  have hpoly :
      X ^ (n + 1) *
          (finiteHankelNullPolynomial c *
            C (finiteHankelNullPolynomial c).leadingCoeff⁻¹) =
        (finiteHankelNullPolynomial c).leadingCoeff⁻¹ •
          (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly, momentFunctional_smul,
    finiteHankelNullPolynomial_leadingCoeff_eq_terminal c hlast]

/-- **Projective terminal law.** The scaling-dependent terminal product is a positive square times
the canonical monic extension class. -/
theorem terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) *
        GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c =
      c (Fin.last n) ^ 2 * finiteHankelBoundaryMonicRemainder s c := by
  rw [GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
    ← momentFunctional_X_pow_mul_finiteHankelNullPolynomial]
  rw [finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw s c hlast]
  field_simp [hlast]

/-- The canonical monic remainder is also the quadrature error of the monic first-unseen
polynomial. -/
theorem finiteHankelBoundaryQuadratureError_monic_eq_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    finiteHankelBoundaryQuadratureError s c
        (X ^ (n + 1) * finiteHankelNullMonicPolynomial c) =
      finiteHankelBoundaryMonicRemainder s c := by
  have hsum : ∑ x ∈ finiteHankelBoundaryNodes c,
      finiteHankelBoundaryWeight s c x *
        (X ^ (n + 1) * finiteHankelNullMonicPolynomial c).eval x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [eval_mul, finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx,
      mul_zero, mul_zero]
  rw [finiteHankelBoundaryQuadratureError, hsum, sub_zero,
    finiteHankelBoundaryMonicRemainder]

/-! ### The extension coordinate is invisible to the current face -/

/-- Perturb one coordinate of a moment sequence additively. -/
def momentCoordinatePerturbation
    (s : ℕ → ℝ) (N : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  s k + if k = N then δ else 0

/-- A one-coordinate moment perturbation is evaluated by the corresponding polynomial
coefficient. -/
theorem momentFunctional_momentCoordinatePerturbation
    (s : ℕ → ℝ) (N : ℕ) (δ : ℝ) (p : Polynomial ℝ) :
    momentFunctional (momentCoordinatePerturbation s N δ) p =
      momentFunctional s p + δ * p.coeff N := by
  rw [momentFunctional_eq_support_sum, momentFunctional_eq_support_sum]
  simp only [momentCoordinatePerturbation, mul_add, Finset.sum_add_distrib]
  have hpert :
      (∑ k ∈ p.support, p.coeff k * if k = N then δ else 0) =
        δ * p.coeff N := by
    by_cases hN : N ∈ p.support
    · rw [Finset.sum_eq_single N]
      · simp [mul_comm]
      · intro k hk hkN
        simp [hkN]
      · exact fun h => (h hN).elim
    · have hcoeff : p.coeff N = 0 := by
        by_contra hcoeff
        exact hN (Polynomial.mem_support_iff.mpr hcoeff)
      rw [hcoeff]
      simp [hN]
  rw [hpert]

/-- Changing only moment `2n+1` leaves the entire size-`n+1` Hankel face unchanged. -/
theorem momentHankelMatrix_momentCoordinatePerturbation_firstUnseen
    (s : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    momentHankelMatrix (momentCoordinatePerturbation s (2 * n + 1) δ) (n + 1) =
      momentHankelMatrix s (n + 1) := by
  ext i j
  have hij : (i : ℕ) + (j : ℕ) ≠ 2 * n + 1 := by
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    have hj : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    omega
  simp [momentHankelMatrix, momentCoordinatePerturbation, hij]

/-- The monic first extension class translates by exactly the unseen coordinate perturbation. -/
theorem finiteHankelBoundaryMonicRemainder_momentCoordinatePerturbation
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (δ : ℝ) :
    finiteHankelBoundaryMonicRemainder
        (momentCoordinatePerturbation s (2 * n + 1) δ) c =
      finiteHankelBoundaryMonicRemainder s c + δ := by
  let P : Polynomial ℝ :=
    X ^ (n + 1) * finiteHankelNullMonicPolynomial c
  have hmonic : P.Monic :=
    (Polynomial.monic_X_pow (n + 1)).mul
      (finiteHankelNullMonicPolynomial_monic c hlast)
  have hdegree : P.natDegree = 2 * n + 1 := by
    rw [show P = X ^ (n + 1) * finiteHankelNullMonicPolynomial c by rfl,
      (Polynomial.monic_X_pow (R := ℝ) (n + 1)).natDegree_mul
        (finiteHankelNullMonicPolynomial_monic c hlast),
      Polynomial.natDegree_X_pow,
      finiteHankelNullMonicPolynomial_natDegree c hlast]
    omega
  have hcoeff : P.coeff (2 * n + 1) = 1 := by
    rw [← hdegree]
    exact hmonic.coeff_natDegree
  rw [finiteHankelBoundaryMonicRemainder,
    finiteHankelBoundaryMonicRemainder,
    momentFunctional_momentCoordinatePerturbation]
  change momentFunctional s P + δ * P.coeff (2 * n + 1) =
    momentFunctional s P + δ
  rw [hcoeff]
  ring

/-- **Face-indeterminacy theorem.** Keeping every current Hankel entry, null polynomial, root,
node, and quadrature weight fixed, the first extension class can be assigned any prescribed real
value by changing only moment `2n+1`. -/
theorem exists_momentSequence_same_face_monicRemainder_eq
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (r : ℝ) :
    ∃ t : ℕ → ℝ,
      momentHankelMatrix t (n + 1) = momentHankelMatrix s (n + 1) ∧
        finiteHankelBoundaryMonicRemainder t c = r := by
  let δ := r - finiteHankelBoundaryMonicRemainder s c
  refine ⟨momentCoordinatePerturbation s (2 * n + 1) δ,
    momentHankelMatrix_momentCoordinatePerturbation_firstUnseen s n δ, ?_⟩
  rw [finiteHankelBoundaryMonicRemainder_momentCoordinatePerturbation s c hlast]
  dsimp [δ]
  ring

/-- The monic extension class depends only on the projective null line, not on a nonzero choice of
kernel-vector scale. -/
theorem finiteHankelBoundaryMonicRemainder_smul
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    finiteHankelBoundaryMonicRemainder s (fun i => a * c i) =
      finiteHankelBoundaryMonicRemainder s c := by
  let ac : Fin (n + 1) → ℝ := fun i => a * c i
  have hlastac : ac (Fin.last n) ≠ 0 := mul_ne_zero ha hlast
  have hcoupling :
      GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) ac =
        a * GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c := by
    rw [GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
      GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [ac]
    ring
  have hnew :=
    terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
      s ac hlastac
  have hold :=
    terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
      s c hlast
  rw [hcoupling] at hnew
  dsimp [ac] at hnew
  have heq :
      (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s (fun i => a * c i) =
        (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s c := by
    calc
      (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s (fun i => a * c i) =
          (a * c (Fin.last n)) *
            (a * GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
              s (n + 1) c) := hnew.symm
      _ = a ^ 2 *
          (c (Fin.last n) *
            GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
              s (n + 1) c) := by ring
      _ = a ^ 2 *
          (c (Fin.last n) ^ 2 * finiteHankelBoundaryMonicRemainder s c) := by
            rw [hold]
      _ = (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s c := by ring
  exact mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero ha hlast)) heq

end

end HTGeometry
