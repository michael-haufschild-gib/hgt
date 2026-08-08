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

/-! ### The extension class is a shifted-square energy -/

/-- On a Hankel null vector, the shifted square of its raw null polynomial is exactly the
terminal coefficient times the first unseen moment pairing.  All other coefficients disappear by
the current kernel equations. -/
theorem momentFunctional_X_mul_finiteHankelNullPolynomial_sq
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentFunctional s
        (X * finiteHankelNullPolynomial c * finiteHankelNullPolynomial c) =
      c (Fin.last n) *
        momentFunctional s (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
  let P := finiteHankelNullPolynomial c
  let a := c (Fin.last n)
  let q := X * P - C a * X ^ (n + 1)
  have hPne : P ≠ 0 := finiteHankelNullPolynomial_ne_zero c hlast
  have hPdeg : P.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hPne,
      finiteHankelNullPolynomial_natDegree c hlast]
  have hXPne : X * P ≠ 0 := mul_ne_zero X_ne_zero hPne
  have hXPdeg : (X * P).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_X, hPdeg]
    rw [add_comm]
    norm_cast
  have hmonomialNe : C a * X ^ (n + 1) ≠ 0 := by
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hlast) (pow_ne_zero _ X_ne_zero)
  have hmonomialDeg : (C a * X ^ (n + 1)).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    exact Polynomial.degree_C_mul_X_pow _ hlast
  have hlead : (X * P).leadingCoeff = (C a * X ^ (n + 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X,
      one_mul, Polynomial.leadingCoeff_C_mul_X_pow]
    exact finiteHankelNullPolynomial_leadingCoeff_eq_terminal c hlast
  have hqdeg : q.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    dsimp [q]
    have h := Polynomial.degree_sub_lt
      (by rw [hXPdeg, hmonomialDeg]) hXPne hlead
    rwa [hXPdeg] at h
  have hqnat : q.natDegree < n + 1 := by
    by_cases hqzero : q = 0
    · simp [hqzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  have horth : momentInner s P q = 0 := by
    exact momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel hc hqnat
  have hsplit : X * P = q + C a * X ^ (n + 1) := by
    dsimp [q]
    ring
  change momentFunctional s (X * P * P) =
    a * momentFunctional s (X ^ (n + 1) * P)
  calc
    momentFunctional s (X * P * P) = momentInner s P (X * P) := by
      rw [momentInner_def]
      congr 1
      ring
    _ = momentInner s P (q + C a * X ^ (n + 1)) := by rw [← hsplit]
    _ = momentInner s P q + momentInner s P (C a * X ^ (n + 1)) := by
      rw [momentInner_add_right]
    _ = momentInner s P (C a * X ^ (n + 1)) := by rw [horth, zero_add]
    _ = a * momentFunctional s (X ^ (n + 1) * P) := by
      rw [momentInner_def, show P * (C a * X ^ (n + 1)) =
          a • (X ^ (n + 1) * P) by
        simp only [Polynomial.smul_eq_C_mul]
        ring,
        momentFunctional_smul]

/-- **Stieltjes boundary-energy law.** The projective extension coordinate is exactly the moment
of `X` times the square of the monic null polynomial.  The mass-shifted spectral-face problem is
therefore one shifted-Hankel square on the current Hankel kernel. -/
theorem finiteHankelBoundaryMonicRemainder_eq_shiftedSquare
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryMonicRemainder s c =
      momentFunctional s
        (X * finiteHankelNullMonicPolynomial c * finiteHankelNullMonicPolynomial c) := by
  have hraw := momentFunctional_X_mul_finiteHankelNullPolynomial_sq s c hc hlast
  rw [finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw s c hlast]
  rw [finiteHankelNullMonicPolynomial,
    finiteHankelNullPolynomial_leadingCoeff_eq_terminal c hlast]
  rw [show X *
      (finiteHankelNullPolynomial c * C (c (Fin.last n))⁻¹) *
      (finiteHankelNullPolynomial c * C (c (Fin.last n))⁻¹) =
        (c (Fin.last n))⁻¹ ^ 2 •
          (X * finiteHankelNullPolynomial c * finiteHankelNullPolynomial c) by
    simp only [Polynomial.smul_eq_C_mul]
    rw [map_pow]
    ring,
    momentFunctional_smul, hraw]
  field_simp [hlast]

/-! ### The shifted square is an oriented Christoffel-port imbalance -/

/-- **Universal Christoffel-port polarization.**  For every moment functional, the difference
between the forward and backward affine-multiplier square energies is exactly four times the
adjacent Hankel energy.  No positivity or moment-representability assumption is used. -/
theorem momentFunctional_christoffelPortDifference
    (s : ℕ → ℝ) (p : Polynomial ℝ) (a : ℝ) :
    momentFunctional s (((X + C a) * p) ^ 2) -
        momentFunctional s (((X - C a) * p) ^ 2) =
      4 * a * momentFunctional s (X * p * p) := by
  have hC4 : C (4 : ℝ) = (4 : Polynomial ℝ) := by
    exact map_natCast (Polynomial.C : ℝ →+* Polynomial ℝ) 4
  have hpoly :
      ((X + C a) * p) ^ 2 - ((X - C a) * p) ^ 2 =
        (4 * a) • (X * p * p) := by
    simp only [Polynomial.smul_eq_C_mul]
    rw [map_mul, hC4]
    ring
  have hlinear :
      momentFunctional s (((X + C a) * p) ^ 2) -
          momentFunctional s (((X - C a) * p) ^ 2) =
        momentFunctional s
          (((X + C a) * p) ^ 2 - ((X - C a) * p) ^ 2) := by
    symm
    calc
      momentFunctional s
          (((X + C a) * p) ^ 2 - ((X - C a) * p) ^ 2) =
          momentFunctional s
            (((X + C a) * p) ^ 2 + -((X - C a) * p) ^ 2) := by
              rw [sub_eq_add_neg]
      _ = momentFunctional s (((X + C a) * p) ^ 2) +
          momentFunctional s (-((X - C a) * p) ^ 2) := by
            rw [momentFunctional_add]
      _ = momentFunctional s (((X + C a) * p) ^ 2) -
          momentFunctional s (((X - C a) * p) ^ 2) := by
            rw [show -((X - C a) * p) ^ 2 =
                (-1 : ℝ) • (((X - C a) * p) ^ 2) by rw [neg_one_smul],
              momentFunctional_smul]
            ring
  rw [hlinear, hpoly, momentFunctional_smul]

/-- On a flat Hankel face, the canonical extension coordinate is exactly the normalized
forward-minus-backward Christoffel-port imbalance of its monic null polynomial. -/
theorem finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (a : ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentFunctional s
          (((X + C a) * finiteHankelNullMonicPolynomial c) ^ 2) -
        momentFunctional s
          (((X - C a) * finiteHankelNullMonicPolynomial c) ^ 2) =
      4 * a * finiteHankelBoundaryMonicRemainder s c := by
  rw [momentFunctional_christoffelPortDifference,
    ← finiteHankelBoundaryMonicRemainder_eq_shiftedSquare s c hc hlast]

/-- **Port-orientation criterion.**  Positivity of the first extension coordinate is equivalent
to strict dominance of the forward unit Christoffel port over the backward unit port. -/
theorem finiteHankelBoundaryMonicRemainder_pos_iff_christoffelPortOrder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < finiteHankelBoundaryMonicRemainder s c ↔
      momentFunctional s
          (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2) <
        momentFunctional s
          (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) := by
  have hdiff :=
    finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
      s c 1 hc hlast
  norm_num at hdiff
  constructor
  · intro h
    have h' :
        momentFunctional s
            (((X - 1) * finiteHankelNullMonicPolynomial c) ^ 2) <
          momentFunctional s
            (((X + 1) * finiteHankelNullMonicPolynomial c) ^ 2) := by
      linarith
    simpa using h'
  · intro h
    have h' :
        momentFunctional s
            (((X - 1) * finiteHankelNullMonicPolynomial c) ^ 2) <
          momentFunctional s
            (((X + 1) * finiteHankelNullMonicPolynomial c) ^ 2) := by
      simpa using h
    linarith

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

/-- **Port-orientation face no-go.**  Keeping the complete current Hankel face fixed, the
forward-minus-backward unit Christoffel-port imbalance can be assigned any prescribed real value.
Thus no theorem depending only on current-face incidence can select its orientation. -/
theorem exists_momentSequence_same_face_christoffelPortDifference_eq
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (d : ℝ) :
    ∃ t : ℕ → ℝ,
      momentHankelMatrix t (n + 1) = momentHankelMatrix s (n + 1) ∧
        momentFunctional t
              (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) -
            momentFunctional t
              (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2) = d := by
  obtain ⟨t, hface, hremainder⟩ :=
    exists_momentSequence_same_face_monicRemainder_eq s c hlast (d / 4)
  have hct : momentHankelMatrix t (n + 1) *ᵥ c = 0 := by
    rw [hface]
    exact hc
  refine ⟨t, hface, ?_⟩
  have hdiff :=
    finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
      t c 1 hct hlast
  norm_num at hdiff
  rw [hremainder] at hdiff
  calc
    momentFunctional t
          (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) -
        momentFunctional t
          (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2) =
        4 * (d / 4) := by simpa using hdiff
    _ = d := by ring

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
