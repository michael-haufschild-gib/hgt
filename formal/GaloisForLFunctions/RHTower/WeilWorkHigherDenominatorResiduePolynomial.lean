import GaloisForLFunctions.HTGeometry.MeromorphicPrincipalPart
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Every Mellin residue is an exact logarithmic polynomial

The polynomial retains all negative Laurent coefficients. Its vanishing is
exactly removability of the punctured germ, without constraining the function's
assigned value at the pole. No restriction on pole order is imposed.
-/

noncomputable section

open Complex Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

private lemma taylorCoeffZero_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeffZero (fun t => f t * g t) n =
      ∑ j ∈ Finset.range (n + 1), taylorCoeffZero f j * taylorCoeffZero g (n - j) := by
  have hd := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ)) hf.contDiffAt hg.contDiffAt
  simp only [taylorCoeffZero, hd, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : (n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hfac : ∀ m : ℕ, (m.factorial : ℂ) ≠ 0 := fun m => Nat.cast_ne_zero.mpr m.factorial_ne_zero
  field_simp [hfac n, hfac j, hfac (n - j)]
  linear_combination (iteratedDeriv j f 0 * iteratedDeriv (n - j) g 0) * hc

/-- The full polar part, expressed as a polynomial in the inverse-Mellin logarithm. -/
def residueLogPolynomial (F : ℂ → ℂ) (ρ : ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range k,
    monomial j ((-1 : ℂ) ^ j * laurentCoeff F ρ (-1 - (j : ℤ)) / (j.factorial : ℂ))

/-- Every coefficient is retained, with an explicitly nonzero scalar factor. -/
theorem coeff_residueLogPolynomial (F : ℂ → ℂ) (ρ : ℂ) (k j : ℕ) :
    (residueLogPolynomial F ρ k).coeff j =
      if j < k then (-1 : ℂ) ^ j * laurentCoeff F ρ (-1 - (j : ℤ)) / (j.factorial : ℂ) else 0 := by
  classical
  simp [residueLogPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

/-- Zero polynomial means every coefficient in the principal part vanishes. -/
theorem residueLogPolynomial_eq_zero_iff (F : ℂ → ℂ) (ρ : ℂ) (k : ℕ) :
    residueLogPolynomial F ρ k = 0 ↔ ∀ j : ℕ, j < k → laurentCoeff F ρ (-1 - (j : ℤ)) = 0 := by
  constructor
  · intro h j hj
    have hc := congrArg (fun P : Polynomial ℂ => P.coeff j) h
    rw [coeff_residueLogPolynomial, if_pos hj, Polynomial.coeff_zero] at hc
    have hfac : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hneg : (-1 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hc).resolve_right hfac)).resolve_left hneg
  · intro h
    ext j
    rw [coeff_residueLogPolynomial, Polynomial.coeff_zero]
    split_ifs with hj
    · rw [h j hj, mul_zero, zero_div]
    · rfl

private lemma taylorCoeffZero_mellin_weight {x : ℝ} (hx : 0 < x) (ρ : ℂ) (j : ℕ) :
    taylorCoeffZero (fun t : ℂ => (x : ℂ) ^ (-(ρ + t))) j =
      (x : ℂ) ^ (-ρ) * (-(Real.log x : ℂ)) ^ j / (j.factorial : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hfun : (fun t : ℂ => (x : ℂ) ^ (-(ρ + t))) =
      fun t => (x : ℂ) ^ (-ρ) * Complex.exp (-(Real.log x : ℂ) * t) := by
    funext t
    simp only [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [taylorCoeffZero, hfun, iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
  simp

/-- Exact residue formula at every positive real x, for an arbitrary admissible pole order. -/
theorem laurentCoeff_mellin_weight_eq_polynomial {F : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hk : AnalyticAt ℂ (laurentShift F ρ k) 0) (hk1 : 1 ≤ k) {x : ℝ} (hx : 0 < x) :
    laurentCoeff (fun s => (x : ℂ) ^ (-s) * F s) ρ (-1) =
      (x : ℂ) ^ (-ρ) * (residueLogPolynomial F ρ k).eval (Real.log x : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hwd : Differentiable ℂ (fun t : ℂ => (x : ℂ) ^ (-(ρ + t))) :=
    (by fun_prop : Differentiable ℂ (fun t : ℂ => -(ρ + t))).const_cpow (Or.inl hx0)
  have hw : AnalyticAt ℂ (fun t : ℂ => (x : ℂ) ^ (-(ρ + t))) 0 :=
    hwd.differentiableOn.analyticAt Filter.univ_mem
  have hshift : laurentShift (fun s => (x : ℂ) ^ (-s) * F s) ρ k =
      fun t => (x : ℂ) ^ (-(ρ + t)) * laurentShift F ρ k t := by
    funext t
    simp only [laurentShift]
    ring
  have hka : AnalyticAt ℂ (laurentShift (fun s => (x : ℂ) ^ (-s) * F s) ρ k) 0 := by
    rw [hshift]
    exact hw.mul hk
  rw [laurentCoeff_eq_taylorCoeffZero hka (by omega), hshift,
    show ((-1 : ℤ) + (k : ℤ)).toNat = k - 1 by omega,
    taylorCoeffZero_mul hw hk, show k - 1 + 1 = k by omega,
    residueLogPolynomial, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  have hidx : ((-1 - (j : ℤ)) + (k : ℤ)).toNat = k - 1 - j := by omega
  have hcoeff : taylorCoeffZero (laurentShift F ρ k) (k - 1 - j) =
      laurentCoeff F ρ (-1 - (j : ℤ)) := by
    rw [laurentCoeff_eq_taylorCoeffZero hk (by omega), hidx]
  rw [taylorCoeffZero_mellin_weight hx, hcoeff, Polynomial.eval_monomial]
  rw [show -(Real.log x : ℂ) = (-1 : ℂ) * (Real.log x : ℂ) by ring, mul_pow]
  ring

/-- Vanishing of the logarithmic polynomial is exactly removability of the punctured germ. -/
theorem residueLogPolynomial_eq_zero_iff_order_nonneg {F : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hk : AnalyticAt ℂ (laurentShift F ρ k) 0) :
    residueLogPolynomial F ρ k = 0 ↔ 0 ≤ meromorphicOrderAt F ρ := by
  have hf : MeromorphicAt F ρ :=
    (meromorphicAt_iff_exists_analyticAt_laurentShift F ρ).mpr ⟨k, hk⟩
  rw [residueLogPolynomial_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨g, hg, hfg⟩ := eq_add_principalPart hk
    have hpp : ∀ s, principalPart F ρ k s = 0 := by
      intro s
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hzj := hz (k - 1 - j) (by omega)
      have hidx : (-1 : ℤ) - ((k - 1 - j : ℕ) : ℤ) = (j : ℤ) - k := by omega
      rw [hidx] at hzj
      rw [hzj, zero_mul]
    apply hf.meromorphicOrderAt_nonneg_iff.mpr
    refine ⟨g, hg, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsne : s ≠ ρ := by simpa using hs
    simpa only [hpp s, add_zero] using hfg s hsne
  · intro ho j _
    exact laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg hf ho (by omega)

/-- Every meromorphic Mellin residue has one polynomial, zero exactly when the pole is removable. -/
theorem exists_mellin_residue_polynomial {F : ℂ → ℂ} {ρ : ℂ} (hf : MeromorphicAt F ρ) :
    ∃ Q : Polynomial ℂ,
      (∀ x : ℝ, 0 < x → laurentCoeff (fun s => (x : ℂ) ^ (-s) * F s) ρ (-1) =
        (x : ℂ) ^ (-ρ) * Q.eval (Real.log x : ℂ)) ∧
      (Q = 0 ↔ 0 ≤ meromorphicOrderAt F ρ) := by
  obtain ⟨k, hk1, hk⟩ := exists_analyticAt_laurentShift_ge hf 1
  exact ⟨residueLogPolynomial F ρ k,
    fun _ hx => laurentCoeff_mellin_weight_eq_polynomial hk hk1 hx,
    residueLogPolynomial_eq_zero_iff_order_nonneg hk⟩

end RHTower.WeilHigherDenominator
