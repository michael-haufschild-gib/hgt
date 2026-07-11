import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.SeamVerticalDecay

/-!
# The completed zeta has infinitely many distinct zeros

This proves the zero supply internally from two already formalized analytic facts.  The exact
Hadamard factorization identifies the centered completed zeta with its genus-one canonical product.
If the divisor support were finite, functional-equation pairing would cancel the exponential parts
of that product and leave a nonzero polynomial.  On the horizontal line corresponding to
`Re s = 3`, however, `xi_vertical_decay` forces this polynomial to tend to zero.  A nonzero
polynomial is either a nonzero constant or tends to infinity in norm, giving the contradiction.
-/

open Complex Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Under a finite zero-copy hypothesis, the genus-one product reduces to this polynomial. -/
def xiFinitePolynomial [Fintype XiZeroCopy] : ℂ[X] :=
  ∏ q : XiZeroCopy, (1 - C (xiSpectralPoint q)⁻¹ * X)

/-- Functional-equation pairing cancels the sum of reciprocal centered zero locations. -/
lemma xiSpectralPoint_inv_sum_eq_zero [Fintype XiZeroCopy] :
    ∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹ = 0 := by
  classical
  have hreindex := xiZeroCopyReflectEquiv.sum_comp (fun q => (xiSpectralPoint q)⁻¹)
  have hneg : (∑ q : XiZeroCopy, (xiSpectralPoint (xiZeroCopyReflectEquiv q))⁻¹) =
      -∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹ := by
    simp_rw [xiSpectralPoint_reflect, inv_neg]
    rw [Finset.sum_neg_distrib]
  rw [hneg] at hreindex
  have hadd := congrArg
    (fun x : ℂ => x + ∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹) hreindex
  change -(∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹) +
      (∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹) =
    (∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹) +
      (∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹) at hadd
  rw [neg_add_cancel] at hadd
  have htwo : (2 : ℂ) * (∑ q : XiZeroCopy, (xiSpectralPoint q)⁻¹) = 0 := by
    rw [two_mul]
    exact hadd.symm
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- With finitely many zero copies, the canonical product is the evaluation of
`xiFinitePolynomial`; the genus-one exponential corrections cancel in reflection pairs. -/
lemma xiCanonicalProduct_eq_eval_finite [Fintype XiZeroCopy] (z : ℂ) :
    xiCanonicalProduct z = xiFinitePolynomial.eval z := by
  classical
  rw [xiCanonicalProduct, canonicalProductE1Indexed, tprod_fintype]
  simp_rw [weierstrassE1]
  rw [Finset.prod_mul_distrib]
  have hsum : ∑ q : XiZeroCopy, z / xiSpectralPoint q = 0 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.mul_sum, xiSpectralPoint_inv_sum_eq_zero, mul_zero]
  rw [← Complex.exp_sum, hsum, Complex.exp_zero, mul_one]
  rw [xiFinitePolynomial, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro q _
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [div_eq_mul_inv]
  ring

/-- The finite canonical-product polynomial is nonzero. -/
lemma xiFinitePolynomial_ne_zero [Fintype XiZeroCopy] :
    xiFinitePolynomial ≠ 0 := by
  classical
  rw [xiFinitePolynomial, Finset.prod_ne_zero_iff]
  intro q _
  have ha : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hfac : (1 - C (xiSpectralPoint q)⁻¹ * X : ℂ[X]) =
      -C (xiSpectralPoint q)⁻¹ * (X - C (xiSpectralPoint q)) := by
    calc
      _ = -C (xiSpectralPoint q)⁻¹ * X + 1 := by ring
      _ = -C (xiSpectralPoint q)⁻¹ * X +
          C (xiSpectralPoint q)⁻¹ * C (xiSpectralPoint q) := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]
      _ = _ := by ring
  rw [hfac]
  exact mul_ne_zero (neg_ne_zero.mpr (Polynomial.C_ne_zero.mpr (inv_ne_zero ha)))
    (Polynomial.monic_X_sub_C (xiSpectralPoint q)).ne_zero

/-- **The completed zeta has infinitely many distinct zeros.**  More precisely, the support of its
global analytic divisor is infinite. -/
theorem xiDivisorSupport_infinite :
    (MeromorphicOn.divisor xi Set.univ).support.Infinite := by
  rw [← Set.infinite_coe_iff]
  by_contra hfinite
  letI : Finite XiDivisorSupport := not_infinite_iff_finite.mp hfinite
  letI : Finite XiZeroCopy := inferInstance
  letI : Fintype XiZeroCopy := Fintype.ofFinite XiZeroCopy
  let P : ℂ[X] := xiFinitePolynomial
  let d : ℂ := -(5 / 2 : ℂ) * Complex.I
  let Q : ℂ[X] := P.comp (X + C d)
  have hP : P ≠ 0 := xiFinitePolynomial_ne_zero
  have hQ : Q ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    change (P.comp (X + C d)).leadingCoeff ≠ 0
    rw [Polynomial.leadingCoeff_comp (by simp)]
    simp only [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  have hXiP : ∀ z : ℂ, XiC z = XiC 0 * P.eval z := by
    intro z
    have h := congrFun XiC_eq_constant_mul_canonicalProduct z
    simpa only [Pi.mul_apply, P, xiCanonicalProduct_eq_eval_finite] using h
  have hdec0 := xi_vertical_decay.comp tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun n : ℕ => ‖XiC ((n : ℂ) + d)‖) atTop (𝓝 0) := by
    refine hdec0.congr' (Filter.Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply]
    change ‖xi ((3 : ℂ) + (n : ℝ) * Complex.I)‖ =
      ‖xi (1 / 2 + ((n : ℂ) + d) * Complex.I)‖
    congr 2
    dsimp only [d]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hseq : ∀ n : ℕ,
      ‖XiC ((n : ℂ) + d)‖ = ‖XiC 0‖ * ‖Q.eval (n : ℂ)‖ := by
    intro n
    rw [hXiP, norm_mul]
    congr 1
    congr 1
    change P.eval ((n : ℂ) + d) = (P.comp (X + C d)).eval (n : ℂ)
    rw [Polynomial.eval_comp]
    simp
  have hC : 0 < ‖XiC 0‖ := norm_pos_iff.mpr XiC_zero_ne
  have hQnorm : Tendsto (fun n : ℕ => ‖Q.eval (n : ℂ)‖) atTop (𝓝 0) := by
    have hdiv := hdec.div_const ‖XiC 0‖
    simpa only [hseq, mul_div_cancel_left₀ _ hC.ne', zero_div] using hdiv
  rcases Nat.eq_zero_or_pos Q.natDegree with hdeg | hdeg
  · have hQC : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : Q.coeff 0 ≠ 0 := by
      intro hc
      apply hQ
      rw [hQC, hc, Polynomial.C_0]
    have hconst : Tendsto (fun _ : ℕ => ‖Q.coeff 0‖) atTop (𝓝 ‖Q.coeff 0‖) :=
      tendsto_const_nhds
    have hQnorm' : Tendsto (fun _ : ℕ => ‖Q.coeff 0‖) atTop (𝓝 0) := by
      have heq : (fun n : ℕ => ‖Q.eval (n : ℂ)‖) = fun _ : ℕ => ‖Q.coeff 0‖ := by
        funext n
        calc
          ‖Q.eval (n : ℂ)‖ = ‖(C (Q.coeff 0)).eval (n : ℂ)‖ := by
            exact congrArg norm (congrArg (fun p : ℂ[X] => p.eval (n : ℂ)) hQC)
          _ = ‖Q.coeff 0‖ := by rw [Polynomial.eval_C]
      rw [← heq]
      exact hQnorm
    exact (norm_ne_zero_iff.mpr hc) (tendsto_nhds_unique hconst hQnorm')
  · have hz : Tendsto (fun n : ℕ => ‖(n : ℂ)‖) atTop atTop := by
      simpa using (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hinf : Tendsto (fun n : ℕ => ‖Q.eval (n : ℂ)‖) atTop atTop :=
      Polynomial.tendsto_abv_atTop norm Q
        (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg) hz
    exact not_tendsto_nhds_of_tendsto_atTop hinf 0 hQnorm

end

end RHTower
