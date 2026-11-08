import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# The Chebyshev cost of annihilator multiplicity

A zero of order `r+1` annihilates every logarithmic moment through degree `r`.
Testing these moments against a Chebyshev polynomial bounds the positive mass
from below in terms of the multiplicity and the logarithmic frequency span.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem iteratedDeriv_frequency_sum (P : MvPolynomial (Fin 2) ℝ≥0)
    (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => dirichletEval z P) s =
      ∑ d ∈ P.support, (-(monomialLog d : ℂ)) ^ k *
        (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s) := by
  induction k generalizing s with
  | zero =>
    simpa only [iteratedDeriv_zero, pow_zero, one_mul] using
      dirichletEval_eq_frequency_sum P s
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hf : iteratedDeriv k (fun z => dirichletEval z P) = fun z =>
        ∑ d ∈ P.support, (-(monomialLog d : ℂ)) ^ k *
          (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * z) :=
      funext ih
    rw [hf]
    have hd := HasDerivAt.fun_sum (u := P.support) fun d _ =>
      (((Complex.hasDerivAt_exp (-(monomialLog d : ℂ) * s)).comp s
        ((hasDerivAt_id s).const_mul (-(monomialLog d : ℂ)))).const_mul
          ((-(monomialLog d : ℂ)) ^ k * (((P.coeff d : ℝ≥0) : ℝ) : ℂ)))
    simp only [Function.comp_def] at hd
    rw [hd.deriv]
    apply Finset.sum_congr rfl
    intro d _
    simp only [pow_succ, mul_one]
    ring

/-- A zero of sufficiently high order kills every polynomial in the logarithmic frequency. -/
theorem polynomial_frequency_moment_eq_zero {P : MvPolynomial (Fin 2) ℝ≥0}
    {ρ : ℂ} (q : Polynomial ℝ)
    (horder : (↑(q.natDegree + 1) : ℕ∞) ≤ analyticOrderAt (fun z => dirichletEval z P) ρ) :
    (∑ d ∈ P.support, ((q.eval (-monomialLog d) : ℝ) : ℂ) *
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)) = 0 := by
  have hder := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((differentiable_dirichletEval P).analyticAt ρ)).mp horder
  have hm (k : ℕ) (hk : k < q.natDegree + 1) :
      (∑ d ∈ P.support, (-(monomialLog d : ℂ)) ^ k *
        (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)) = 0 := by
    rw [← iteratedDeriv_frequency_sum]
    exact hder k hk
  simp_rw [Polynomial.eval_eq_sum_range, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have he := hm k (Finset.mem_range.mp hk)
  simp only [mul_assoc] at he
  rw [he, mul_zero]

/-- A polynomial bounded by one on the supported frequencies gives a mass lower bound. -/
theorem polynomial_frequency_cost {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (q : Polynomial ℝ)
    (horder : (↑(q.natDegree + 1) : ℕ∞) ≤ analyticOrderAt (fun z => dirichletEval z P) ρ)
    (hq : ∀ d ∈ P.support.erase 0, |q.eval (-monomialLog d)| ≤ 1) :
    |q.eval 0| ≤ dirichletTailMass P ρ.re := by
  classical
  have hc : P.coeff 0 = 1 := hP
  have hmem : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, hc]
    exact one_ne_zero
  have ht := Finset.sum_erase_add P.support (fun d => ((q.eval (-monomialLog d) : ℝ) : ℂ) *
    (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)) hmem
  rw [polynomial_frequency_moment_eq_zero q horder] at ht
  have hzero : ((q.eval (-monomialLog 0) : ℝ) : ℂ) *
      (((P.coeff 0 : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog 0 : ℂ) * ρ) =
        ((q.eval 0 : ℝ) : ℂ) := by simp [monomialLog, hc]
  rw [hzero] at ht
  have htail : (∑ d ∈ P.support.erase 0, ((q.eval (-monomialLog d) : ℝ) : ℂ) *
      (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)) =
        -((q.eval 0 : ℝ) : ℂ) := eq_neg_of_add_eq_zero_left ht
  calc
    |q.eval 0| = ‖∑ d ∈ P.support.erase 0, ((q.eval (-monomialLog d) : ℝ) : ℂ) *
        (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)‖ := by
      rw [htail, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ d ∈ P.support.erase 0, ‖((q.eval (-monomialLog d) : ℝ) : ℂ) *
        (((P.coeff d : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)‖ :=
      norm_sum_le _ _
    _ ≤ dirichletTailMass P ρ.re := by
      apply Finset.sum_le_sum
      intro d hd
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (P.coeff d).coe_nonneg, Complex.norm_exp, Complex.mul_re,
        Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        neg_zero, zero_mul, sub_zero]
      have hw := mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos (-monomialLog d * ρ.re)).le
      simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right (hq d hd) hw

private theorem chebyshev_abs_le_one (r : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Polynomial.Chebyshev.T ℝ r).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- At fixed frequency span, an order-`r+1` zero costs at least the corresponding
Chebyshev value outside the frequency interval. -/
theorem multiplicity_forces_chebyshev_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (r : ℕ)
    (horder : (↑(r + 1) : ℕ∞) ≤ analyticOrderAt (fun z => dirichletEval z P) ρ)
    {B : ℝ} (hB : Real.log 2 < B)
    (hfreq : ∀ d ∈ P.support.erase 0, monomialLog d ≤ B) :
    |(Polynomial.Chebyshev.T ℝ r).eval ((B + Real.log 2) / (B - Real.log 2))| ≤
      dirichletTailMass P ρ.re := by
  let a := Real.log 2
  let l : Polynomial ℝ := Polynomial.C ((B + a) / (B - a)) +
    Polynomial.C (2 / (B - a)) * Polynomial.X
  let q := (Polynomial.Chebyshev.T ℝ r).comp l
  have hl : l.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp only [Polynomial.natDegree_C]; omega
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have hdeg : q.natDegree ≤ r := by
    calc
      q.natDegree ≤ (Polynomial.Chebyshev.T ℝ r).natDegree * l.natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ r * 1 := by simpa only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast] using
        Nat.mul_le_mul_left r hl
      _ = r := Nat.mul_one _
  have hqorder : (↑(q.natDegree + 1) : ℕ∞) ≤
      analyticOrderAt (fun z => dirichletEval z P) ρ := by
    apply le_trans _ horder
    exact_mod_cast Nat.add_le_add_right hdeg 1
  have heval (x : ℝ) : q.eval (-x) =
      (Polynomial.Chebyshev.T ℝ r).eval ((B + a - 2 * x) / (B - a)) := by
    simp only [q, l, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    congr 1
    ring
  have hcost := polynomial_frequency_cost hP q hqorder (fun d hd => by
    rw [heval]
    apply chebyshev_abs_le_one
    have hlo := log_two_le_monomialLog d (Finset.mem_erase.mp hd).1
    have hup := hfreq d hd
    constructor
    · apply (le_div_iff₀ (sub_pos.mpr hB)).mpr
      dsimp only [a]
      linarith only [hup]
    · apply (div_le_iff₀ (sub_pos.mpr hB)).mpr
      dsimp only [a]
      linarith only [hlo])
  simpa only [q, l, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, mul_zero, add_zero] using hcost

private theorem chebyshev_quadratic_lower (r : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    1 + (r : ℝ) ^ 2 * (x - 1) ≤ (Polynomial.Chebyshev.T ℝ r).eval x := by
  have h (n : ℕ) :
      1 + (n : ℝ) ^ 2 * (x - 1) ≤ (Polynomial.Chebyshev.T ℝ n).eval x ∧
      (2 * (n : ℝ) + 1) * (x - 1) ≤
        (Polynomial.Chebyshev.T ℝ (n + 1)).eval x -
          (Polynomial.Chebyshev.T ℝ n).eval x := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 1 + ((n : ℝ) + 1) ^ 2 * (x - 1) ≤
          (Polynomial.Chebyshev.T ℝ (n + 1)).eval x := by
        nlinarith only [ih.1, ih.2]
      have hnonneg : 0 ≤ ((n : ℝ) + 1) ^ 2 * (x - 1) :=
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hx)
      have hone : 1 ≤ (Polynomial.Chebyshev.T ℝ (n + 1)).eval x := by
        linarith only [hn, hnonneg]
      have hm := mul_le_mul_of_nonneg_left hone (sub_nonneg.mpr hx)
      have he : (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 2)).eval x =
          2 * x * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval x -
            (Polynomial.Chebyshev.T ℝ n).eval x := by
        rw [Polynomial.Chebyshev.T_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X]
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using hn
      · push_cast at ih hm ⊢
        rw [show (n : ℤ) + 1 + 1 = n + 2 by ring, he]
        nlinarith only [ih.2, hm]
  exact (h r).1

/-- Near unit mass, logarithmic bandwidth must grow at least quadratically in the
number of vanishing derivatives. -/
theorem multiplicity_forces_quadratic_frequency_cost {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} (r : ℕ)
    (horder : (↑(r + 1) : ℕ∞) ≤ analyticOrderAt (fun z => dirichletEval z P) ρ)
    {B : ℝ} (hB : Real.log 2 < B)
    (hfreq : ∀ d ∈ P.support.erase 0, monomialLog d ≤ B) :
    2 * Real.log 2 * (r : ℝ) ^ 2 ≤
      (B - Real.log 2) * (dirichletTailMass P ρ.re - 1) := by
  have hc := multiplicity_forces_chebyshev_mass hP r horder hB hfreq
  have hx : 1 ≤ (B + Real.log 2) / (B - Real.log 2) := by
    apply (le_div_iff₀ (sub_pos.mpr hB)).mpr
    linarith only [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hl := (chebyshev_quadratic_lower r hx).trans
    ((le_abs_self _).trans hc)
  have he : (B + Real.log 2) / (B - Real.log 2) - 1 =
      2 * Real.log 2 / (B - Real.log 2) := by
    field_simp [(sub_pos.mpr hB).ne']
    ring
  rw [he] at hl
  have hfrac : 2 * Real.log 2 * (r : ℝ) ^ 2 / (B - Real.log 2) ≤
      dirichletTailMass P ρ.re - 1 := by
    calc
      _ = (r : ℝ) ^ 2 * (2 * Real.log 2 / (B - Real.log 2)) := by ring
      _ ≤ _ := by linarith only [hl]
  simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hB)).mp hfrac

/-- Every multiple zero forces a supported monomial beyond the quadratic
multiplicity threshold; the frequency bound is a conclusion, not an input. -/
theorem multiplicity_forces_large_frequency {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {r : ℕ} (hr : 1 ≤ r)
    (horder : (↑(r + 1) : ℕ∞) ≤ analyticOrderAt (fun z => dirichletEval z P) ρ) :
    1 < dirichletTailMass P ρ.re ∧ ∃ d ∈ P.support.erase 0,
      Real.log 2 + 2 * Real.log 2 * (r : ℝ) ^ 2 / (dirichletTailMass P ρ.re - 1) ≤
        monomialLog d := by
  have hder := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((differentiable_dirichletEval P).analyticAt ρ)).mp horder
  have hz : dirichletEval ρ P = 0 := by
    simpa only [iteratedDeriv_zero] using hder 0 (by omega)
  have hd : deriv (fun z => dirichletEval z P) ρ = 0 := by
    have h := hder 1 (by omega)
    rw [show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at h
    exact h
  have hm := one_lt_tail_mass_of_zero_deriv hP hz hd
  have hS : (P.support.erase 0).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp only [dirichletTailMass, hn, Finset.sum_empty] at hm
    exact (by norm_num : ¬ (1 : ℝ) < 0) hm
  obtain ⟨d, hdmem, hmax⟩ := Finset.exists_max_image (P.support.erase 0) monomialLog hS
  have hgap := (double_zero_forces_frequency_span_cost hP hz hd (monomialLog d) hmax).1
  have hcost := multiplicity_forces_quadratic_frequency_cost hP r horder hgap hmax
  refine ⟨hm, d, hdmem, ?_⟩
  have hquot : 2 * Real.log 2 * (r : ℝ) ^ 2 / (dirichletTailMass P ρ.re - 1) ≤
      monomialLog d - Real.log 2 := (div_le_iff₀ (sub_pos.mpr hm)).mpr hcost
  linarith only [hquot]

#print axioms polynomial_frequency_moment_eq_zero
#print axioms multiplicity_forces_chebyshev_mass
#print axioms multiplicity_forces_quadratic_frequency_cost
#print axioms multiplicity_forces_large_frequency

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
