import GaloisForLFunctions.ExceptionalLayerTheory.TheCommonDivisorOfTheCyclicCoverCoefficients
import GaloisForLFunctions.ExceptionalLayerTheory.FirstMeansOfDyadicBinomialGcdsAndTheZetaZeros

/-!
# First means of cyclic-cover coefficient heights

The height and the logarithmic binomial gcd have complementary linear terms.
Their pointwise discrepancy costs a square root, uniformly in the width.
Summation transfers every first-mean exponent from one sequence to the other.
-/

noncomputable section

open Finset Filter

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Cumulative deviation of the coefficient heights from a linear function of degree. -/
def cyclicCoefficientHeightTotal (q : ℕ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (cyclicCoefficientHeight q n-B*n)

/-- The error is bounded uniformly even when the width varies with the degree. -/
theorem cyclicCoefficientHeight_complementary_sqrt :
    ∃ K : ℝ, 0≤K ∧ ∀ j n : ℕ,
      let q := 2^(j+1)
      |cyclicCoefficientHeight q n+Real.log (dyadicBinomialGcd j n)-(n:ℝ)*Real.log (2*q:ℕ)| ≤
        K*Real.sqrt (q*n:ℕ) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C|+1,by positivity,fun j n => ?_⟩
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : dyadicBinomialGcd j 0=1 := by
      induction j with
      | zero => simp [dyadicBinomialGcd,Nat.centralBinom]
      | succ j ih => simp [dyadicBinomialGcd,ih,Nat.centralBinom]
    change |cyclicCoefficientHeight q 0+Real.log (dyadicBinomialGcd j 0)-_| ≤ _
    simp [cyclicCoefficientHeight_zero hq,hzero]
  · have hx : n+1 ≤ q*n := by
      have he := Nat.mul_le_mul_right n hq
      omega
    have hlog : Real.log ((n:ℝ)+1) ≤ Real.sqrt (q*n:ℕ) :=
      (_root_.RHTower.log_le_sqrt (by positivity)).trans (Real.sqrt_le_sqrt (by exact_mod_cast hx))
    apply (cyclicCoefficientHeight_add_log_gcd j n hn).trans
    have hc := (hC (q*n:ℕ)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
    exact (add_le_add hc hlog).trans_eq (by ring)

private theorem complementary_first_totals {b : ℝ} (hb : 1/2≤b) (j : ℕ) {A B : ℝ}
    (hAB : A*(2^(j+1):ℕ)+B=Real.log (2*2^(j+1):ℕ)) :
    ∃ K : ℝ, 0≤K ∧ ∀ N : ℕ,
      |cyclicCoefficientHeightTotal (2^(j+1)) B N+binomialGcdFirstTotal j A N| ≤ K*(N:ℝ)^(b+1) := by
  let q := 2^(j+1)
  obtain ⟨C,hC,h⟩ := cyclicCoefficientHeight_complementary_sqrt
  refine ⟨C*Real.sqrt q,by positivity,fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cyclicCoefficientHeightTotal,binomialGcdFirstTotal,Real.zero_rpow (show b+1≠0 by linarith only [hb])]
  have h1 : 1≤(N:ℝ) := by exact_mod_cast hN
  have hpow : Real.sqrt N≤(N:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1 hb
  rw [cyclicCoefficientHeightTotal,binomialGcdFirstTotal,← sum_add_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ range N, (C*Real.sqrt q)*(N:ℝ)^b := by
      refine sum_le_sum fun n hn => ?_
      have he : cyclicCoefficientHeight q n-B*n+(Real.log (dyadicBinomialGcd j n)-A*(q*n:ℕ)) =
          cyclicCoefficientHeight q n+Real.log (dyadicBinomialGcd j n)-(n:ℝ)*Real.log (2*q:ℕ) := by
        rw [← hAB,Nat.cast_mul]; ring
      rw [he]
      apply (h j n).trans
      rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg q),← mul_assoc]
      exact mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt (by exact_mod_cast (mem_range.mp hn).le :
        (n:ℝ)≤N)).trans hpow) (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = _ := by
      rw [sum_const,card_range,nsmul_eq_mul,Real.rpow_add_one (by positivity : (N:ℝ)≠0)]
      ring

private theorem height_bound_of_complement {f g w : ℕ → ℝ} {K C : ℝ}
    (hk : ∀ n, |f n+g n|≤K*w n) (hc : ∀ n, |g n|≤C*w n) :
    ∀ n, |f n|≤(K+C)*w n := by
  intro n
  have he := abs_sub (f n+g n) (g n)
  rw [add_sub_cancel_right] at he
  exact (he.trans (add_le_add (hk n) (hc n))).trans_eq (add_mul ..).symm

/-- RH is equivalent to a cumulative power bound for the logarithmic projective
heights in degree n, at arbitrarily large fixed dyadic widths. -/
theorem riemannHypothesis_iff_cyclicCoefficientHeight_first_means :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → b<1 → ∃ᶠ j : ℕ in atTop,
      ∃ B C : ℝ, 0≤C ∧ ∀ N : ℕ, |cyclicCoefficientHeightTotal (2^(j+1)) B N|≤C*(N:ℝ)^(b+1) := by
  rw [riemannHypothesis_iff_binomialGcd_first_means]
  constructor
  · intro h b hb hb1
    apply (h b hb hb1).mono
    rintro j ⟨A,C,hC,hg⟩
    let q := 2^(j+1)
    let B := Real.log (2*q:ℕ)-A*q
    obtain ⟨K,hK,h⟩ := complementary_first_totals hb.le j (A := A) (B := B) (by dsimp only [B,q]; ring)
    exact ⟨B,K+C,add_nonneg hK hC,height_bound_of_complement h hg⟩
  · intro h b hb hb1
    apply (h b hb hb1).mono
    rintro j ⟨B,C,hC,hh⟩
    let q := 2^(j+1)
    let A := (Real.log (2*q:ℕ)-B)/(q:ℝ)
    have hq : (q:ℝ)≠0 := by dsimp only [q]; positivity
    have hAB : A*(q:ℝ)+B=Real.log (2*q:ℕ) := by rw [A,div_mul_cancel₀ _ hq,sub_add_cancel]
    obtain ⟨K,hK,h⟩ := complementary_first_totals hb.le j hAB
    exact ⟨A,K+C,add_nonneg hK hC,height_bound_of_complement
      (fun N => by rw [add_comm]; exact h N) hh⟩

#print axioms cyclicCoefficientHeight_complementary_sqrt
#print axioms riemannHypothesis_iff_cyclicCoefficientHeight_first_means

end GaloisForLFunctions.ExceptionalLayerTheory
