import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheEulerProductOfLorentzianLocalFactorsIsLorentzian

/-!
# The closure produces exactly the Lorentzian forms

Which quadratic forms are Hessians of objects built by the closure calculus? Exactly the
Lorentzian ones: symmetric, entrywise nonnegative, one positive square.

* **Every Hessian of the closure is Lorentzian** (`IsMixedLorentzian.isLorentzian_hessAt`): the
  Hessian of a mixed-Lorentzian polynomial at a nonnegative point is symmetric, nonnegative and
  hyperbolic. In particular so is the Hessian of every Euler product of Lorentzian local factors
  composed with a nonnegative substitution (`isLorentzian_hessAt_prod_subst`).
* **Every Lorentzian form is a Hessian of the closure** (`isMixedLorentzian_quadForm`,
  `hessAt_quadForm`): `Q` is the Hessian of the mixed-Lorentzian quadratic `½ xᵀQx`.
* **Characterization** (`isLorentzian_iff_exists_hessAt`): `Q` is Lorentzian iff it is the Hessian
  at a nonnegative point of a mixed-Lorentzian polynomial.

So Hessians extract nothing beyond the Lorentzian signature: a form with a negative entry — such
as the atomic intersection form of `ζ`, whose atom diagonal is negative — is reached by the
closure only after a change of coordinates (the nef shift), that is, by identification.
-/

noncomputable section

open Matrix Finset MvPolynomial

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Hessians of the closure are Lorentzian -/

omit [Fintype ι] [DecidableEq ι] in
theorem hessAt_isSymm (p : MvPolynomial ι ℝ) (x : ι → ℝ) : (hessAt p x).IsSymm :=
  Matrix.IsSymm.ext fun j k => by
    simp only [hessAt, Matrix.of_apply, GaloisForLFunctions.pderiv_comm j k]

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_pderiv_nonneg {p : MvPolynomial ι ℝ} (hp : ∀ β, 0 ≤ coeff β p) (i : ι) (β : ι →₀ ℕ) :
    0 ≤ coeff β (pderiv i p) := by
  rw [coeff_pderiv]; exact mul_nonneg (hp _) (by positivity)

omit [DecidableEq ι] in
/-- **The Hessian of a mixed-Lorentzian polynomial at a nonnegative point is Lorentzian.** -/
theorem IsMixedLorentzian.isLorentzian_hessAt {n : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsMixedLorentzian (n + 2) p) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    IsLorentzian (hessAt p x) :=
  ⟨hessAt_isSymm p x, fun j k => eval_nonneg_of_coeff_nonneg
    (coeff_pderiv_nonneg (coeff_pderiv_nonneg hp.1 k) j) hx, hp.isHyperbolic_hessAt hx⟩

/-- **The Hessian of an Euler product of Lorentzian local factors, composed with a nonnegative
substitution, is Lorentzian at every nonnegative point.** -/
theorem isLorentzian_hessAt_prod_subst {κ τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype τ]
    [DecidableEq τ] {d : κ → ℕ} {f : κ → MvPolynomial ι ℝ} (s : Finset κ)
    (hf : ∀ p ∈ s, IsLorentzianPolynomial (d p) (f p)) {A : Matrix ι τ ℝ}
    (hA : ∀ i k, 0 ≤ A i k) {n : ℕ} (hn : ∑ p ∈ s, d p = n + 2) {y : τ → ℝ}
    (hy : ∀ k, 0 ≤ y k) : IsLorentzian (hessAt (aeval (linSub A) (∏ p ∈ s, f p)) y) := by
  have h := isMixedLorentzian_prod_subst s hf hA
  rw [hn] at h
  exact h.isLorentzian_hessAt hy

/-! ### Every Lorentzian form is a Hessian of the closure -/

/-- The quadratic `½ xᵀQx = Σ_j x_j (Σ_l (Q_{jl}/2) x_l)`. -/
def quadForm (Q : Matrix ι ι ℝ) : MvPolynomial ι ℝ :=
  ∑ j, X j * ∑ l, C (Q j l / 2) * X l

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_X_nonneg (j : ι) (β : ι →₀ ℕ) : 0 ≤ coeff β (X j : MvPolynomial ι ℝ) := by
  classical
  rw [coeff_X]; split_ifs <;> norm_num

omit [DecidableEq ι] in
theorem pderiv_quadForm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (k : ι) :
    pderiv k (quadForm Q) = ∑ b, C (Q k b) * X b := by
  classical
  have hL : ∀ j, pderiv k (∑ l, C (Q j l / 2) * X l : MvPolynomial ι ℝ) = C (Q j k / 2) := by
    intro j
    simp only [map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, if_true]
  simp only [quadForm, map_sum, pderiv_mul, hL, pderiv_X, Pi.single_apply, ite_mul, one_mul,
    zero_mul, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_comm (X b), ← add_mul, ← map_add, hQ.apply k b]
  congr 2
  ring

omit [DecidableEq ι] in
theorem pderiv_pderiv_quadForm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (j k : ι) :
    pderiv j (pderiv k (quadForm Q)) = C (Q j k) := by
  classical
  simp only [pderiv_quadForm hQ, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply, mul_ite,
    mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [hQ.apply j k]

omit [DecidableEq ι] in
theorem hessAt_quadForm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (x : ι → ℝ) :
    hessAt (quadForm Q) x = Q := by
  ext j k
  rw [hessAt, Matrix.of_apply, pderiv_pderiv_quadForm hQ, eval_C]

omit [DecidableEq ι] in
theorem hess0_quadForm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) : hess0 (quadForm Q) = Q := by
  ext j k
  rw [hess0, Matrix.of_apply, pderiv_pderiv_quadForm hQ, constantCoeff_C]

omit [DecidableEq ι] in
/-- **A Lorentzian form is the Hessian of a mixed-Lorentzian quadratic.** -/
theorem isMixedLorentzian_quadForm {Q : Matrix ι ι ℝ} (hQ : IsLorentzian Q) :
    IsMixedLorentzian 2 (quadForm Q) := by
  refine ⟨fun β => ?_, ?_, fun vs hvs _ => ?_⟩
  · classical
    simp only [quadForm, coeff_sum]
    refine sum_nonneg fun j _ => ?_
    rw [coeff_mul]
    refine sum_nonneg fun x _ => mul_nonneg (coeff_X_nonneg j _) ?_
    simp only [coeff_sum, coeff_C_mul]
    exact sum_nonneg fun l _ =>
      mul_nonneg (div_nonneg (hQ.2.1 j l) zero_le_two) (coeff_X_nonneg l _)
  · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℝ j).mul
      (IsHomogeneous.sum _ _ _ fun l _ => (isHomogeneous_X ℝ l).C_mul _)
  · have : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [show dirDerivs [] (quadForm Q) = quadForm Q from rfl, hess0_quadForm hQ.1]
    exact hQ.2.2

omit [DecidableEq ι] in
/-- **The closure produces exactly the Lorentzian forms**: a matrix is Lorentzian iff it is the
Hessian at a nonnegative point of a mixed-Lorentzian polynomial. -/
theorem isLorentzian_iff_exists_hessAt {Q : Matrix ι ι ℝ} :
    IsLorentzian Q ↔ ∃ (n : ℕ) (p : MvPolynomial ι ℝ) (x : ι → ℝ),
      IsMixedLorentzian (n + 2) p ∧ (∀ i, 0 ≤ x i) ∧ hessAt p x = Q := by
  constructor
  · intro hQ
    exact ⟨0, quadForm Q, 0, isMixedLorentzian_quadForm hQ, fun _ => le_rfl,
      hessAt_quadForm hQ.1 0⟩
  · rintro ⟨n, p, x, hp, hx, rfl⟩
    exact hp.isLorentzian_hessAt hx

omit [DecidableEq ι] in
/-- A form with a negative entry is not a Hessian of the closure at a nonnegative point. -/
theorem not_exists_hessAt_of_neg {Q : Matrix ι ι ℝ} {j k : ι} (h : Q j k < 0) :
    ¬ ∃ (n : ℕ) (p : MvPolynomial ι ℝ) (x : ι → ℝ),
      IsMixedLorentzian (n + 2) p ∧ (∀ i, 0 ≤ x i) ∧ hessAt p x = Q := fun hex =>
  absurd ((isLorentzian_iff_exists_hessAt.mpr hex).2.1 j k) (not_le.mpr h)

end GaloisForLFunctions.ArithmeticLorentzianGeometry
