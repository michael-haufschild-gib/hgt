import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# The finite-divisor Hadamard product at every finite order

`RHTower.exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet` gives the finite-zero Hadamard
normal form for entire functions of order strictly below two, where the zero-free cofactor is
`c·exp(Bz)`.  With the general zero-free factorization
`GaloisForLFunctions.HTGeometry.exists_polynomial_exp_of_ne_zero_of_growth` now available, the same
growth-transfer argument works at every finite order and produces a full polynomial exponent.

## Main results

* `exists_finiteDivisorFactor_mul_expPolynomial_of_finite_zeroSet` — the divisor form;
* `exists_polynomial_mul_expPolynomial_of_finite_zeroSet` — the same statement with the divisor
  packaged as a nonzero polynomial;
* `finiteDivisorPoly` — the divisor polynomial itself.
-/

noncomputable section

open Complex Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The finite divisor factor as a polynomial. -/
def finiteDivisorPoly (t : Finset ℂ) (m : ℂ → ℕ) : Polynomial ℂ :=
  ∏ w ∈ t, (Polynomial.X - Polynomial.C w) ^ m w

theorem finiteDivisorPoly_ne_zero (t : Finset ℂ) (m : ℂ → ℕ) :
    finiteDivisorPoly t m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)

theorem eval_finiteDivisorPoly (t : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    (finiteDivisorPoly t m).eval z = finiteDivisorFactor t m z := by
  rw [finiteDivisorPoly, finiteDivisorFactor, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun w _ => by simp

/-- **Finite-zero Hadamard rigidity at every finite order.**  An entire function with a
finite-order growth envelope and a finite zero set is exactly its finite divisor factor times the
exponential of a polynomial. -/
theorem exists_finiteDivisorFactor_mul_expPolynomial_of_finite_zeroSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} {d : ℕ} (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d))
    (hfinite : {z : ℂ | f z = 0}.Finite) :
    ∃ (t : Finset ℂ) (m : ℂ → ℕ) (q : Polynomial ℂ),
      (∀ z, f z = finiteDivisorFactor t m z * Complex.exp (q.eval z)) ∧
      (∀ z, f z = 0 ↔ z ∈ t) := by
  classical
  let t : Finset ℂ := hfinite.toFinset
  let S : ℝ := ∑ w ∈ t, ‖w‖
  let R : ℝ := 1 + S
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hR0 : 0 ≤ R := by dsimp [R]; linarith
  have htZeros (z : ℂ) : z ∈ t ↔ f z = 0 := by
    simp only [t, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hzAnchorNotMem : ((R : ℝ) : ℂ) ∉ t := by
    intro hz
    have hzSum : ‖((R : ℝ) : ℂ)‖ ≤ S := by
      have := Finset.single_le_sum (fun w _ => norm_nonneg w) hz
      simpa only [S] using this
    have hnormR : ‖((R : ℝ) : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
    rw [hnormR] at hzSum
    dsimp [R] at hzSum
    linarith
  have hfAnchor : f ((R : ℝ) : ℂ) ≠ 0 := fun hz => hzAnchorNotMem ((htZeros _).mpr hz)
  have hfA : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hord : ∀ w ∈ t, analyticOrderAt f w ≠ ⊤ := by
    intro w hw htop
    have hev : f =ᶠ[nhds w] 0 := analyticOrderAt_eq_top.mp htop
    have hall := hfA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ w) hev (Set.mem_univ ((R : ℝ) : ℂ))
    exact hfAnchor hall
  obtain ⟨m, h, hhA, hh0, hfactor⟩ :=
    exists_multi_peel isOpen_univ hfA t (fun _ _ => Set.mem_univ _)
      (fun z _ hz => (htZeros z).mpr hz) hord
  have hhDiff : Differentiable ℂ h := fun z => (hhA z (Set.mem_univ z)).differentiableAt
  have hbdd : BddAbove ((fun z : ℂ => ‖h z‖) '' Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : ℂ) R).bddAbove_image hhDiff.continuous.norm.continuousOn
  let K : ℝ := max 1 (sSup ((fun z : ℂ => ‖h z‖) '' Metric.closedBall 0 R))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hinside {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) : ‖h z‖ ≤ K :=
    (le_csSup hbdd (mem_image_of_mem (fun w : ℂ => ‖h w‖) hz)).trans (le_max_right _ _)
  have houtside {z : ℂ} (hz : z ∉ Metric.closedBall (0 : ℂ) R) :
      ‖h z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d) := by
    have hzFar : R ≤ ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using le_of_lt
        (show R < ‖z‖ by
          simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)
    have hP : 1 ≤ ‖finiteDivisorFactor t m z‖ := by
      apply one_le_norm_finiteDivisorFactor_of_far
      simpa only [R, S] using hzFar
    have hfactNorm : ‖f z‖ = ‖finiteDivisorFactor t m z‖ * ‖h z‖ := by
      rw [hfactor z (Set.mem_univ z), norm_mul]
      rfl
    have hhf : ‖h z‖ ≤ ‖f z‖ := by
      rw [hfactNorm]
      nlinarith [norm_nonneg (h z)]
    exact hhf.trans (hgrow z)
  let C' : ℝ := C + Real.log K
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hC'0 : 0 ≤ C' := by dsimp [C']; linarith
  have hhGrow : ∀ z, ‖h z‖ ≤ Real.exp (C' * (1 + ‖z‖) ^ d) := by
    intro z
    have hpow1 : 1 ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z])
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · calc
        ‖h z‖ ≤ K := hinside hz
        _ = Real.exp (Real.log K) := (Real.exp_log hKpos).symm
        _ ≤ Real.exp (C' * (1 + ‖z‖) ^ d) := by
          rw [Real.exp_le_exp]
          dsimp [C']
          nlinarith [hC, hlogK0]
    · refine (houtside hz).trans ?_
      rw [Real.exp_le_exp]
      dsimp [C']
      refine mul_le_mul_of_nonneg_right (by linarith) ?_
      positivity
  obtain ⟨q, hq⟩ := exists_polynomial_exp_of_ne_zero_of_growth
    hhDiff (fun z => hh0 z (Set.mem_univ z)) hC'0 hhGrow
  refine ⟨t, m, q, fun z => ?_, fun z => (htZeros z).symm⟩
  rw [hfactor z (Set.mem_univ z), hq z]
  rfl

/-- **The polynomial form.**  An entire function of finite order with finitely many zeros is a
nonzero polynomial times the exponential of a polynomial. -/
theorem exists_polynomial_mul_expPolynomial_of_finite_zeroSet
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C : ℝ} {d : ℕ} (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d))
    (hfinite : {z : ℂ | f z = 0}.Finite) :
    ∃ p q : Polynomial ℂ, p ≠ 0 ∧ ∀ z, f z = p.eval z * Complex.exp (q.eval z) := by
  obtain ⟨t, m, q, hform, -⟩ :=
    exists_finiteDivisorFactor_mul_expPolynomial_of_finite_zeroSet hf hC hgrow hfinite
  refine ⟨finiteDivisorPoly t m, q, finiteDivisorPoly_ne_zero t m, fun z => ?_⟩
  rw [eval_finiteDivisorPoly, hform z]

/-- **The polynomial form**, phrased through the envelope predicate. -/
theorem exists_polynomial_mul_expPolynomial_of_envelope
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (henv : FiniteOrderEnvelope f) (hfinite : {z : ℂ | f z = 0}.Finite) :
    ∃ p q : Polynomial ℂ, p ≠ 0 ∧ ∀ z, f z = p.eval z * Complex.exp (q.eval z) := by
  obtain ⟨C, d, hC, hgrow⟩ := henv
  exact exists_polynomial_mul_expPolynomial_of_finite_zeroSet hf hC hgrow hfinite

end RHTower
