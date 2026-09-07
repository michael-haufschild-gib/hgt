import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Finite Dirichlet weights cannot cancel the simple critical divisor

A finite Dirichlet polynomial is entire of finite exponential type and determines its
coefficients. The unconditional superlinear census of simple critical Xi zeros therefore
forces nonvanishing beyond every height, even after any fixed finite set of exceptions.
This supplies the spectral separation step for finite retained-source fields. Transport
from the literal source to its Mellin transform and uniform control of changing fields
are separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower

/-- A Dirichlet polynomial with finitely supported coefficients. -/
def finiteDirichletPolynomial (a : ℕ →₀ ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ a.support, a n * (n : ℂ) ^ (-s)

lemma finiteDirichletPolynomial_eq_LSeries (a : ℕ →₀ ℂ) (ha : a 0 = 0) (s : ℂ) :
    finiteDirichletPolynomial a s = LSeries (fun n => a n) s := by
  rw [LSeries, tsum_eq_sum (s := a.support)]
  · simp only [finiteDirichletPolynomial, LSeries.term_def₀ ha]
  · intro n hn
    rw [LSeries.term_def₀ ha, Finsupp.notMem_support_iff.mp hn, zero_mul]

lemma finiteDirichletPolynomial_ne_zero (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0) :
    finiteDirichletPolynomial a ≠ 0 := by
  intro h
  have hL : LSeries (fun n => a n) = 0 := by
    ext s
    rw [← finiteDirichletPolynomial_eq_LSeries a ha]
    exact congrFun h s
  rcases (LSeries_eq_zero_iff ha).mp hL with hz | htop
  · apply hne
    ext n
    exact congrFun hz n
  · have hsum : LSeriesSummable (fun n => a n) 0 := by
      apply summable_of_ne_finset_zero (s := a.support)
      intro n hn
      rw [LSeries.term_def₀ ha, Finsupp.notMem_support_iff.mp hn, zero_mul]
    have hb := hsum.abscissaOfAbsConv_le
    simp [htop] at hb

lemma differentiable_finiteDirichletPolynomial (a : ℕ →₀ ℂ) (ha : a 0 = 0) :
    Differentiable ℂ (finiteDirichletPolynomial a) := by
  intro s
  apply DifferentiableAt.fun_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    exact (Finsupp.mem_support_iff.mp hn) ha
  exact (differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast hn0))).const_mul _

lemma finiteDirichletPolynomial_exponentialType (a : ℕ →₀ ℂ) (ha : a 0 = 0) :
    ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧
      ∀ s : ℂ, ‖finiteDirichletPolynomial a s‖ ≤ C * Real.exp (A * ‖s‖) := by
  let A : ℝ := ∑ n ∈ a.support, |Real.log n|
  let C : ℝ := 1 + ∑ n ∈ a.support, ‖a n‖
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  refine ⟨A, C, hA, hC, fun s => ?_⟩
  have hp (n : ℕ) (hn : n ∈ a.support) :
      ‖(n : ℂ) ^ (-s)‖ ≤ Real.exp (A * ‖s‖) := by
    have hn0 : 0 < n := by
      by_contra h
      have hnz : n = 0 := by omega
      subst n
      exact (Finsupp.mem_support_iff.mp hn) ha
    rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re,
      Real.rpow_def_of_pos (by exact_mod_cast hn0)]
    apply Real.exp_le_exp.mpr
    have hlog : |Real.log n| ≤ A := Finset.single_le_sum (f := fun n : ℕ => |Real.log n|) (fun _ _ => abs_nonneg _) hn
    have hnorm : -s.re ≤ ‖s‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm s)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn0)
    have hlogA : Real.log n ≤ A := (le_abs_self _).trans hlog
    nlinarith [norm_nonneg s]
  calc
    ‖finiteDirichletPolynomial a s‖ ≤ ∑ n ∈ a.support, ‖a n * (n : ℂ) ^ (-s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ a.support, ‖a n‖ * Real.exp (A * ‖s‖) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hp n hn) (norm_nonneg _)
    _ = (∑ n ∈ a.support, ‖a n‖) * Real.exp (A * ‖s‖) := (Finset.sum_mul _ _ _).symm
    _ ≤ C * Real.exp (A * ‖s‖) := by
      exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_pos _).le


private lemma finiteDirichletPolynomial_line_exponentialType (a : ℕ →₀ ℂ) (ha : a 0 = 0) :
    ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧ ∀ z : ℂ,
      ‖finiteDirichletPolynomial a ((1 / 2 : ℂ) + z * Complex.I)‖ ≤
        C * Real.exp (A * ‖z‖) := by
  obtain ⟨A, C, hA, hC, hg⟩ := finiteDirichletPolynomial_exponentialType a ha
  have he : 1 ≤ Real.exp A := by simpa using Real.exp_le_exp.mpr hA
  refine ⟨A, C * Real.exp A, hA, (by nlinarith), fun z => ?_⟩
  have hnorm : ‖(1 / 2 : ℂ) + z * Complex.I‖ ≤ 1 + ‖z‖ := by
    calc
      _ ≤ ‖(1 / 2 : ℂ)‖ + ‖z * Complex.I‖ := norm_add_le _ _
      _ ≤ 1 + ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]; norm_num
  calc
    _ ≤ C * Real.exp (A * ‖(1 / 2 : ℂ) + z * Complex.I‖) := hg _
    _ ≤ C * Real.exp (A * (1 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hnorm hA)) (by linarith)
    _ = C * Real.exp A * Real.exp (A * ‖z‖) := by rw [mul_add, mul_one, Real.exp_add, mul_assoc]

private lemma finiteDirichletPolynomial_line_ne_zero (a : ℕ →₀ ℂ)
    (ha : a 0 = 0) (hne : a ≠ 0) :
    (fun z : ℂ => finiteDirichletPolynomial a ((1 / 2 : ℂ) + z * Complex.I)) ≠ 0 := by
  intro h
  apply finiteDirichletPolynomial_ne_zero a ha hne
  ext s
  have hs : (1 / 2 : ℂ) + (-(s - 1 / 2) * Complex.I) * Complex.I = s := by
    rw [mul_assoc, Complex.I_mul_I]
    ring
  simpa only [hs, Pi.zero_apply] using congrFun h (-(s - 1 / 2) * Complex.I)


/-- Simple critical ordinates outside any finite set detect a nonzero entire function
of finite exponential type. -/
theorem exists_simpleCritical_nonzero_of_exponentialType
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hFne : F ≠ 0)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖)) (E : Finset ℝ) :
    ∃ t : ℝ, t ∉ E ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧ F (t : ℂ) ≠ 0 := by
  classical
  by_contra h
  have hv : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 → F (t : ℂ) = 0 := by
    intro t ht ht0 hz ho
    by_contra hne
    exact h ⟨t, ht, ht0, hz, ho, hne⟩
  obtain ⟨K, _, hlin⟩ :=
    exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros
      hF hFne hA hC hgrow E hv
  exact not_linear_bound_of_superlinear (by positivity : (0 : ℝ) < 1 / (72 * Real.pi))
    eventually_superlinear_xiSimpleCriticalZeroCount hlin

/-- Every nonzero finite Dirichlet polynomial is nonzero at a simple critical Xi zero
outside any prescribed finite set of ordinates. -/
theorem exists_simpleCritical_finiteDirichletPolynomial_ne_zero
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0) (E : Finset ℝ) :
    ∃ t : ℝ, t ∉ E ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧
      finiteDirichletPolynomial a (linePt t) ≠ 0 := by
  let F : ℂ → ℂ := fun z => finiteDirichletPolynomial a ((1 / 2 : ℂ) + z * Complex.I)
  have hF : Differentiable ℂ F :=
    (differentiable_finiteDirichletPolynomial a ha).comp
      ((differentiable_const (1 / 2)).add (differentiable_id.mul_const Complex.I))
  have hFne : F ≠ 0 := finiteDirichletPolynomial_line_ne_zero a ha hne
  obtain ⟨A, C, hA, hC, hg⟩ := finiteDirichletPolynomial_line_exponentialType a ha
  obtain ⟨t, ht, ht0, hz, ho, hn⟩ :=
    exists_simpleCritical_nonzero_of_exponentialType hF hFne hA hC hg E
  refine ⟨t, ht, ht0, hz, ho, ?_⟩
  simpa only [F, linePt, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hn

/-- Finite Dirichlet polynomials cannot annihilate the simple critical Xi divisor,
even after deletion of finitely many ordinates. -/
theorem finiteDirichletPolynomial_coeff_zero_of_cofinite_simpleCritical_zeros
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (E : Finset ℝ)
    (hv : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
      finiteDirichletPolynomial a (linePt t) = 0) : a = 0 := by
  by_contra hne
  obtain ⟨t, ht, ht0, hz, ho, hn⟩ :=
    exists_simpleCritical_finiteDirichletPolynomial_ne_zero a ha hne E
  exact hn (hv t ht ht0 hz ho)

/-- Uncancelled simple critical zeros occur beyond every height. -/
theorem exists_high_simpleCritical_finiteDirichletPolynomial_ne_zero
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧
      finiteDirichletPolynomial a (linePt t) ≠ 0 := by
  obtain ⟨t, ht, ht0, hz, ho, hn⟩ :=
    exists_simpleCritical_finiteDirichletPolynomial_ne_zero a ha hne
      (xiSimpleCriticalOrdinateFinset T)
  refine ⟨t, ?_, ht0, hz, ho, hn⟩
  by_contra hle
  exact ht (mem_xiSimpleCriticalOrdinateFinset.mpr ⟨ht0, by linarith, hz, ho⟩)

end RHTower
