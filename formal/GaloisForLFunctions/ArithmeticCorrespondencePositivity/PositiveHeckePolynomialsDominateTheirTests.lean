import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHeckeAnnihilatorsOfFiniteResonances

/-!
# Positive Hecke polynomials as literal operators

Evaluate a bivariate polynomial by ordered compositions of the normalized Hecke
operators at two and three. Nonnegative coefficients give pointwise positivity;
constant coefficient one gives domination of the original test. The established
Hecke eigen-equation identifies the action on completed Eisenstein modes exactly.
No commutation assertion on arbitrary, nonperiodic functions is needed.
-/

set_option autoImplicit false

open Complex Finset
open scoped NNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke

open ArithmeticPositiveDuality.PositiveAnnihilator

/-- An ordered Hecke monomial on the upper half-plane. -/
def monomialAction (d : Fin 2 →₀ ℕ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  (RHTower.heckeOp 2)^[d 0] ((RHTower.heckeOp 3)^[d 1] f)

/-- Literal finite-sum action of a positive Hecke polynomial. -/
def action (P : MvPolynomial (Fin 2) ℝ≥0) (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  ∑ d ∈ P.support, (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * monomialAction d f x y

private theorem hecke_nonneg {p : ℕ} (hp : 0 < p) {f : ℝ → ℝ → ℂ}
    (hf : ∀ x y, 0 < y → 0 ≤ (f x y).re) (x y : ℝ) (hy : 0 < y) :
    0 ≤ (RHTower.heckeOp p f x y).re := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold RHTower.heckeOp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re]
  rw [show (∑ b ∈ Finset.range p, f ((x + b) / p) (y / p)).re =
    ∑ b ∈ Finset.range p, (f ((x + b) / p) (y / p)).re from
      map_sum Complex.reAddGroupHom _ _]
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (add_nonneg (hf _ _ (mul_pos hpR hy))
      (Finset.sum_nonneg fun b _ => hf _ _ (div_pos hy hpR)))

private theorem iterate_nonneg {p : ℕ} (hp : 0 < p) (k : ℕ)
    {f : ℝ → ℝ → ℂ} (hf : ∀ x y, 0 < y → 0 ≤ (f x y).re) :
    ∀ x y, 0 < y → 0 ≤ ((RHTower.heckeOp p)^[k] f x y).re := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      intro x y hy
      rw [Function.iterate_succ_apply']
      exact hecke_nonneg hp ih x y hy

/-- Every ordered monomial preserves nonnegative real parts. -/
theorem monomialAction_nonneg (d : Fin 2 →₀ ℕ) {f : ℝ → ℝ → ℂ}
    (hf : ∀ x y, 0 < y → 0 ≤ (f x y).re) (x y : ℝ) (hy : 0 < y) :
    0 ≤ (monomialAction d f x y).re :=
  iterate_nonneg (by norm_num) (d 0)
    (iterate_nonneg (by norm_num) (d 1) hf) x y hy

private theorem action_re (P : MvPolynomial (Fin 2) ℝ≥0)
    (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    (action P f x y).re =
      ∑ d ∈ P.support, ((P.coeff d : ℝ≥0) : ℝ) * (monomialAction d f x y).re := by
  unfold action
  rw [show (∑ d ∈ P.support,
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * monomialAction d f x y).re =
      ∑ d ∈ P.support,
        ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) * monomialAction d f x y).re from
      map_sum Complex.reAddGroupHom _ _]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- Constant coefficient one gives pointwise domination on nonnegative tests. -/
theorem action_dominates (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) {f : ℝ → ℝ → ℂ}
    (hf : ∀ x y, 0 < y → 0 ≤ (f x y).re) (x y : ℝ) (hy : 0 < y) :
    (f x y).re ≤ (action P f x y).re := by
  classical
  have hc : P.coeff 0 = 1 := hP
  have hmem : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, hc]
    exact one_ne_zero
  rw [action_re]
  have h := Finset.single_le_sum
    (fun d (_ : d ∈ P.support) => mul_nonneg (P.coeff d).coe_nonneg
      (monomialAction_nonneg d hf x y hy)) hmem
  simpa only [hc, NNReal.coe_one, one_mul, monomialAction, Finsupp.zero_apply,
    Function.iterate_zero, id_eq] using h

private theorem hecke_congr {p : ℕ} (hp : 0 < p) {f g : ℝ → ℝ → ℂ}
    (h : ∀ x y, 0 < y → f x y = g x y) (x y : ℝ) (hy : 0 < y) :
    RHTower.heckeOp p f x y = RHTower.heckeOp p g x y := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold RHTower.heckeOp
  rw [h _ _ (mul_pos hpR hy)]
  congr 2
  exact Finset.sum_congr rfl fun b _ => h _ _ (div_pos hy hpR)

private theorem iterate_congr {p : ℕ} (hp : 0 < p) (k : ℕ)
    {f g : ℝ → ℝ → ℂ} (h : ∀ x y, 0 < y → f x y = g x y) :
    ∀ x y, 0 < y → (RHTower.heckeOp p)^[k] f x y =
      (RHTower.heckeOp p)^[k] g x y := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro x y hy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hecke_congr hp ih x y hy

private theorem iterate_const_mul (p k : ℕ) (c : ℂ) (f : ℝ → ℝ → ℂ) :
    (RHTower.heckeOp p)^[k] (fun x y => c * f x y) =
      fun x y => c * ((RHTower.heckeOp p)^[k] f x y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext x y
      exact RHTower.heckeOp_const_mul p c _ x y

private theorem iterate_eigen {p : ℕ} (hp : 0 < p) (k : ℕ) {lam : ℂ}
    {f : ℝ → ℝ → ℂ}
    (hf : ∀ x y, 0 < y → RHTower.heckeOp p f x y = lam * f x y) :
    ∀ x y, 0 < y → (RHTower.heckeOp p)^[k] f x y = lam ^ k * f x y := by
  induction k with
  | zero => intro x y _; simp
  | succ k ih =>
      intro x y hy
      rw [Function.iterate_succ_apply', hecke_congr hp ih x y hy,
        RHTower.heckeOp_const_mul, hf x y hy, pow_succ]
      ring

/-- The ordered monomial has the expected eigenvalue on every joint eigenfunction. -/
theorem monomialAction_eigen (d : Fin 2 →₀ ℕ) {lam : Fin 2 → ℂ}
    {f : ℝ → ℝ → ℂ}
    (h2 : ∀ x y, 0 < y → RHTower.heckeOp 2 f x y = lam 0 * f x y)
    (h3 : ∀ x y, 0 < y → RHTower.heckeOp 3 f x y = lam 1 * f x y)
    (x y : ℝ) (hy : 0 < y) :
    monomialAction d f x y = (lam 0 ^ d 0 * lam 1 ^ d 1) * f x y := by
  unfold monomialAction
  rw [iterate_congr (by norm_num : 0 < (2 : ℕ)) (d 0)
      (iterate_eigen (by norm_num) (d 1) h3) x y hy,
    iterate_const_mul]
  dsimp only
  rw [iterate_eigen (by norm_num) (d 0) h2 x y hy]
  ring

/-- The finite support expansion of the spectral polynomial. -/
theorem spectralEval_eq_sum (P : MvPolynomial (Fin 2) ℝ≥0) (u : ℂ) :
    spectralEval u P = ∑ d ∈ P.support,
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * (eigenvalue 0 u ^ d 0 * eigenvalue 1 u ^ d 1) := by
  change MvPolynomial.eval₂ _ _ P = _
  rw [MvPolynomial.eval₂_eq']
  simp only [Fin.prod_univ_two]
  rfl

/-- The exponential parametrization agrees with the eigenvalue at two. -/
theorem eigenvalue_two (u : ℂ) :
    eigenvalue 0 u = (2 : ℂ) ^ u + (2 : ℂ) ^ (-u) := by
  simp only [eigenvalue, primeBase, ↓reduceIte]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  simp only [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_ofNat, mul_neg]

/-- The exponential parametrization agrees with the eigenvalue at three. -/
theorem eigenvalue_three (u : ℂ) :
    eigenvalue 1 u = (3 : ℂ) ^ u + (3 : ℂ) ^ (-u) := by
  simp only [eigenvalue, primeBase, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0)]
  simp only [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3), Complex.ofReal_ofNat, mul_neg]

/-- A positive polynomial acts by its spectral evaluation on joint eigenfunctions. -/
theorem action_eigen (P : MvPolynomial (Fin 2) ℝ≥0) (u : ℂ)
    {f : ℝ → ℝ → ℂ}
    (h2 : ∀ x y, 0 < y → RHTower.heckeOp 2 f x y = eigenvalue 0 u * f x y)
    (h3 : ∀ x y, 0 < y → RHTower.heckeOp 3 f x y = eigenvalue 1 u * f x y)
    (x y : ℝ) (hy : 0 < y) :
    action P f x y = spectralEval u P * f x y := by
  unfold action
  simp_rw [monomialAction_eigen (lam := fun i => eigenvalue i u) _ h2 h3 x y hy,
    ← mul_assoc]
  rw [← Finset.sum_mul, spectralEval_eq_sum]
  simp only [mul_assoc]

/-- Literal operator action on the completed Eisenstein function at every parameter. -/
theorem action_cuspLeg (P : MvPolynomial (Fin 2) ℝ≥0) (u : ℂ)
    (x y : ℝ) (hy : 0 < y) :
    action P (fun x y => RHTower.d4BMCompletedEisensteinCuspLeg .scalar u x y) x y =
      spectralEval u P * RHTower.d4BMCompletedEisensteinCuspLeg .scalar u x y := by
  have h2 : ∀ x y, 0 < y → RHTower.heckeOp 2
      (fun x y => RHTower.d4BMCompletedEisensteinCuspLeg .scalar u x y) x y =
        eigenvalue 0 u * RHTower.d4BMCompletedEisensteinCuspLeg .scalar u x y := by
    intro x y hy
    rw [eigenvalue_two]
    exact RHTower.heckeOp_cuspLeg (by norm_num) u x hy
  have h3 : ∀ x y, 0 < y → RHTower.heckeOp 3
      (fun x y => RHTower.d4BMCompletedEisensteinCuspLeg .scalar u x y) x y =
        eigenvalue 1 u * RHTower.d4BMCompletedEisensteinCuspLeg .scalar u x y := by
    intro x y hy
    rw [eigenvalue_three]
    exact RHTower.heckeOp_cuspLeg (by norm_num) u x hy
  exact action_eigen P u h2 h3 x y hy

/-- Actual zeta resonances admit a positive dominating Hecke annihilator, with arbitrary
prescribed multiplicities of its spectral zeros. -/
theorem exists_positive_dominating_xi_annihilator
    (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    (m : {ρ : ℂ // RHTower.xi ρ = 0} → ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ ρ ∈ F, (m ρ : ℕ∞) ≤
        analyticOrderAt (fun u => spectralEval u P) (zeroParameter ρ) ∧
        ∀ x y, 0 < y → action P
          (fun x y => RHTower.d4BMCompletedEisensteinCuspLeg .scalar (zeroParameter ρ) x y)
          x y = 0) ∧
      ∀ f : ℝ → ℝ → ℝ, (∀ x y, 0 < y → 0 ≤ f x y) →
        ∀ x y, 0 < y → f x y ≤ (action P (fun x y => (f x y : ℂ)) x y).re := by
  obtain ⟨P, hPc, hP⟩ := exists_xi_zero_annihilator_with_multiplicities F m
  refine ⟨P, hPc, ?_, ?_⟩
  · intro ρ hρ
    refine ⟨(hP ρ hρ).2, ?_⟩
    intro x y hy
    rw [action_cuspLeg P _ x y hy, (hP ρ hρ).1, zero_mul]
  · intro f hf x y hy
    exact action_dominates P hPc (f := fun x y => (f x y : ℂ)) hf x y hy

end GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke.exists_positive_dominating_xi_annihilator
