import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHeckePolynomialsDominateTheirTests
import GaloisForLFunctions.ArithmeticCriticalityTheory.LightConeAntisymmetricVariationLaw

/-!
# The constant-mode cost of positive Hecke cancellation

Every Hecke eigenvalue attached to a nontrivial zeta zero has norm strictly below
the corresponding constant-mode eigenvalue. A positive polynomial with constant
coefficient one that vanishes on such a pair must therefore take a value strictly
larger than two on the constant mode: its nonconstant terms must cancel one, and
their constant-mode values strictly dominate their norms.
-/

set_option autoImplicit false

open Complex Finset
open scoped NNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke

open ArithmeticPositiveDuality.PositiveAnnihilator

/-- The positive eigenvalue of the constant function at either prime. -/
def constantEigenvalue (i : Fin 2) : ℝ :=
  2 * Real.cosh (Real.log (primeBase i) / 2)

theorem constantEigenvalue_pos (i : Fin 2) : 0 < constantEigenvalue i :=
  mul_pos (by norm_num) (Real.cosh_pos _)

theorem eigenvalue_half (i : Fin 2) :
    eigenvalue i (1 / 2) = (constantEigenvalue i : ℂ) := by
  apply Complex.ext <;>
    simp [eigenvalue, constantEigenvalue, Real.cosh_eq,
      Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, div_eq_mul_inv]
  ring

/-- Every parameter strictly between the constant and unitary axes has a strict
constant-mode norm gap, independently of its imaginary part. -/
theorem norm_eigenvalue_lt_constant {u : ℂ} (hlo : -(1 / 2 : ℝ) < u.re)
    (hhi : u.re < 0) (i : Fin 2) :
    ‖eigenvalue i u‖ < constantEigenvalue i := by
  let L := Real.log (primeBase i)
  have hL : 0 < L := by
    apply Real.log_pos
    dsimp [primeBase]
    split_ifs <;> norm_num
  have h0 : 0 ≤ -(L * u.re) := (neg_pos.mpr (mul_neg_of_pos_of_neg hL hhi)).le
  have hlt : -(L * u.re) < L / 2 := by nlinarith only [hL, hlo]
  have hc := ArithmeticCriticalityTheory.strictMonoOn_cosh_Ici
    h0 (by positivity : 0 ≤ L / 2) hlt
  calc
    ‖eigenvalue i u‖ ≤ ‖Complex.exp ((L : ℂ) * u)‖ +
        ‖Complex.exp (-((L : ℂ) * u))‖ := norm_add_le _ _
    _ = 2 * Real.cosh (-(L * u.re)) := by
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re,
        Real.cosh_eq, neg_neg]
      ring
    _ < 2 * Real.cosh (L / 2) := mul_lt_mul_of_pos_left hc (by norm_num)
    _ = constantEigenvalue i := rfl

private theorem monomial_norm_lt {z : Fin 2 → ℂ} {b : Fin 2 → ℝ}
    (hb : ∀ i, ‖z i‖ < b i) (d : Fin 2 →₀ ℕ) (hd : d ≠ 0) :
    ‖z 0 ^ d 0 * z 1 ^ d 1‖ < b 0 ^ d 0 * b 1 ^ d 1 := by
  have hb0 : 0 < b 0 := (norm_nonneg _).trans_lt (hb 0)
  have hb1 : 0 < b 1 := (norm_nonneg _).trans_lt (hb 1)
  rw [norm_mul, norm_pow, norm_pow]
  by_cases h0 : d 0 = 0
  · have h1 : d 1 ≠ 0 := by
      intro h1
      apply hd
      ext i
      fin_cases i <;> simp [h0, h1]
    simp only [h0, pow_zero, one_mul]
    exact pow_lt_pow_left₀ (hb 1) (norm_nonneg _) h1
  · calc
      ‖z 0‖ ^ d 0 * ‖z 1‖ ^ d 1 ≤ ‖z 0‖ ^ d 0 * b 1 ^ d 1 := by
        gcongr
        exact (hb 1).le
      _ < b 0 ^ d 0 * b 1 ^ d 1 :=
        mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (hb 0) (norm_nonneg _) h0)
          (pow_pos hb1 _)

private theorem positive_eval_gt_two (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (z : Fin 2 → ℂ) (b : Fin 2 → ℝ)
    (hb : ∀ i, ‖z i‖ < b i)
    (hz : MvPolynomial.eval₂Hom (Complex.ofRealHom.comp NNReal.toRealHom) z P = 0) :
    2 < MvPolynomial.eval₂ NNReal.toRealHom b P := by
  classical
  have hc : P.coeff 0 = 1 := hP
  have hmem : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, hc]
    exact one_ne_zero
  let S := P.support.erase 0
  let v : (Fin 2 →₀ ℕ) → ℂ := fun d =>
    (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * (z 0 ^ d 0 * z 1 ^ d 1)
  let w : (Fin 2 →₀ ℕ) → ℝ := fun d =>
    ((P.coeff d : ℝ≥0) : ℝ) * (b 0 ^ d 0 * b 1 ^ d 1)
  have hv0 : v 0 = 1 := by simp [v, hc]
  have hw0 : w 0 = 1 := by simp [w, hc]
  have hevalC : MvPolynomial.eval₂Hom
      (Complex.ofRealHom.comp NNReal.toRealHom) z P = ∑ d ∈ P.support, v d := by
    change MvPolynomial.eval₂ _ _ P = _
    rw [MvPolynomial.eval₂_eq']
    simp only [Fin.prod_univ_two]
    rfl
  have hevalR : MvPolynomial.eval₂ NNReal.toRealHom b P =
      ∑ d ∈ P.support, w d := by
    rw [MvPolynomial.eval₂_eq']
    simp only [Fin.prod_univ_two]
    rfl
  have hsumC : ∑ d ∈ S, v d = -1 := by
    have h := Finset.sum_erase_add P.support v hmem
    rw [hv0, ← hevalC, hz] at h
    dsimp [S]
    linear_combination h
  have hSne : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty] at hsumC
    norm_num at hsumC
  have hstrict : ∀ d ∈ S, ‖v d‖ < w d := by
    intro d hd
    have hdc : P.coeff d ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)
    have hcp : (0 : ℝ) < ((P.coeff d : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hdc : 0 < P.coeff d)
    have hd0 : d ≠ 0 := (Finset.mem_erase.mp hd).1
    dsimp [v, w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcp]
    exact mul_lt_mul_of_pos_left (monomial_norm_lt hb d hd0) hcp
  have hsum : (1 : ℝ) < ∑ d ∈ S, w d := by
    calc
      1 = ‖∑ d ∈ S, v d‖ := by rw [hsumC]; simp
      _ ≤ ∑ d ∈ S, ‖v d‖ := norm_sum_le _ _
      _ < ∑ d ∈ S, w d := Finset.sum_lt_sum_of_nonempty hSne hstrict
  rw [hevalR, ← Finset.sum_erase_add P.support w hmem, hw0]
  change 2 < (∑ d ∈ S, w d) + 1
  linarith only [hsum]

/-- The constant-mode value is a positive real polynomial evaluation. -/
theorem spectralEval_half (P : MvPolynomial (Fin 2) ℝ≥0) :
    spectralEval (1 / 2) P =
      ((MvPolynomial.eval₂ NNReal.toRealHom constantEigenvalue P : ℝ) : ℂ) := by
  rw [spectralEval_eq_sum, MvPolynomial.eval₂_eq']
  simp only [eigenvalue_half, Fin.prod_univ_two, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  rfl

/-- Any positive polynomial annihilating an actual zeta resonance amplifies the
constant mode by strictly more than two. -/
theorem constant_response_gt_two (ρ : {ρ : ℂ // RHTower.xi ρ = 0})
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    (hz : spectralEval (zeroParameter ρ) P = 0) :
    2 < (spectralEval (1 / 2) P).re := by
  have hr := RHTower.xi_zero_re_mem_open_unit ρ.property
  have hlo : -(1 / 2 : ℝ) < (zeroParameter ρ).re := by
    simpa [zeroParameter] using
      (show -(1 / 2 : ℝ) < ((ρ : ℂ).re - 1) / 2 by linarith only [hr.1])
  have hhi : (zeroParameter ρ).re < 0 := by
    simpa [zeroParameter] using
      (show ((ρ : ℂ).re - 1) / 2 < 0 by linarith only [hr.2])
  rw [spectralEval_half, Complex.ofReal_re]
  exact positive_eval_gt_two P hP (fun i => eigenvalue i (zeroParameter ρ))
    constantEigenvalue (norm_eigenvalue_lt_constant hlo hhi) hz

/-- Positive coefficients and constant coefficient one exclude all real parameters. -/
theorem spectralEval_real_re_ge_one (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (r : ℝ) :
    1 ≤ (spectralEval (r : ℂ) P).re := by
  classical
  let b : Fin 2 → ℝ := fun i =>
    Real.exp (Real.log (primeBase i) * r) + Real.exp (-(Real.log (primeBase i) * r))
  have he (i : Fin 2) : eigenvalue i (r : ℂ) = (b i : ℂ) := by
    apply Complex.ext <;>
      simp [eigenvalue, b, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have hb (i : Fin 2) : 0 ≤ b i := (add_pos (Real.exp_pos _) (Real.exp_pos _)).le
  have hc : P.coeff 0 = 1 := hP
  have hmem : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, hc]
    exact one_ne_zero
  rw [spectralEval_eq_sum]
  rw [show (∑ d ∈ P.support, (((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
      (eigenvalue 0 (r : ℂ) ^ d 0 * eigenvalue 1 (r : ℂ) ^ d 1)).re =
      ∑ d ∈ P.support, ((((P.coeff d : ℝ≥0) : ℝ) : ℂ) *
        (eigenvalue 0 (r : ℂ) ^ d 0 * eigenvalue 1 (r : ℂ) ^ d 1)).re from
      map_sum Complex.reAddGroupHom _ _]
  simp only [he, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := Finset.single_le_sum
    (fun d (_ : d ∈ P.support) => mul_nonneg (P.coeff d).coe_nonneg
      (mul_nonneg (pow_nonneg (hb 0) (d 0)) (pow_nonneg (hb 1) (d 1)))) hmem
  simpa only [hc, NNReal.coe_one, Finsupp.zero_apply, pow_zero, mul_one] using h

/-- On the left half-plane, nonreal parameters are exactly those admitting a positive
Hecke annihilator with constant coefficient one. -/
theorem exists_annihilator_iff_nonreal {u : ℂ} (hu : u.re < 0) :
    (∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧ spectralEval u P = 0) ↔ u.im ≠ 0 := by
  constructor
  · rintro ⟨P, hPc, hP⟩ hi
    have he : u = (u.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have h := spectralEval_real_re_ge_one P hPc u.re
    rw [← he, hP, Complex.zero_re] at h
    norm_num at h
  · intro hi
    obtain ⟨P, hPc, hP⟩ := exists_finite_annihilator {u} (by simpa using And.intro hu hi)
    exact ⟨P, hPc, hP u (Finset.mem_singleton_self u)⟩

private theorem hecke_one {p : ℕ} (hp : 0 < p) (x y : ℝ) :
    RHTower.heckeOp p (fun _ _ => 1) x y =
      (p : ℂ) ^ (1 / 2 : ℂ) + (p : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hr : Real.sqrt (p : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hp)).ne'
  have hrC : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hsq : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  rw [Complex.cpow_neg]
  simp only [← RHTower.sqrt_eq_cpow_half]
  unfold RHTower.heckeOp
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  linear_combination -hsq

/-- The polynomial's value at `u=1/2` is its literal action on constants. -/
theorem action_one (P : MvPolynomial (Fin 2) ℝ≥0) (x y : ℝ) (hy : 0 < y) :
    action P (fun _ _ => 1) x y = spectralEval (1 / 2) P := by
  have h2 : ∀ x y, 0 < y → RHTower.heckeOp 2 (fun _ _ => 1) x y =
      eigenvalue 0 (1 / 2) * 1 := by
    intro x y _
    rw [mul_one, eigenvalue_two]
    exact hecke_one (by norm_num) x y
  have h3 : ∀ x y, 0 < y → RHTower.heckeOp 3 (fun _ _ => 1) x y =
      eigenvalue 1 (1 / 2) * 1 := by
    intro x y _
    rw [mul_one, eigenvalue_three]
    exact hecke_one (by norm_num) x y
  simpa only [mul_one] using action_eigen P (1 / 2) h2 h3 x y hy

/-- Positive cancellation of any nonempty finite collection of actual zeta resonances
has a strict constant-mode cost, while retaining all prescribed zero multiplicities. -/
theorem exists_xi_annihilator_with_constant_cost
    (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    (m : {ρ : ℂ // RHTower.xi ρ = 0} → ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ ρ ∈ F, spectralEval (zeroParameter ρ) P = 0 ∧
        (m ρ : ℕ∞) ≤ analyticOrderAt (fun u => spectralEval u P) (zeroParameter ρ)) ∧
      (∀ ρ ∈ F, ∀ x y, 0 < y → action P
        (fun x y => RHTower.d4BMCompletedEisensteinCuspLeg .scalar (zeroParameter ρ) x y)
        x y = 0) ∧
      (∀ f : ℝ → ℝ → ℝ, (∀ x y, 0 < y → 0 ≤ f x y) →
        ∀ x y, 0 < y → f x y ≤ (action P (fun x y => (f x y : ℂ)) x y).re) ∧
      (F.Nonempty → ∀ x y, 0 < y → 2 < (action P (fun _ _ => 1) x y).re) := by
  obtain ⟨P, hPc, hP⟩ := exists_xi_zero_annihilator_with_multiplicities F m
  refine ⟨P, hPc, hP, ?_, ?_, ?_⟩
  · intro ρ hρ x y hy
    rw [action_cuspLeg P _ x y hy, (hP ρ hρ).1, zero_mul]
  · intro f hf x y hy
    exact action_dominates P hPc (f := fun x y => (f x y : ℂ)) hf x y hy
  · rintro ⟨ρ, hρ⟩ x y hy
    rw [action_one P x y hy]
    exact constant_response_gt_two ρ P hPc (hP ρ hρ).1

end GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke.constant_response_gt_two
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke.exists_annihilator_iff_nonreal
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke.exists_xi_annihilator_with_constant_cost
