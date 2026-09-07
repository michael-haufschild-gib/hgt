import GaloisForLFunctions.RHTower.MobiusDivisorAbelGcdCross
import GaloisForLFunctions.RHTower.MobiusDivisorElevenChannelBounds
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Unbounded positive gcd components with a negative complete witness

Analytic logarithm, Euler-constant and square-root bounds certify opposite signs
for the primitive and complete cross terms at eleven. Exact prime homothety
then makes the positive individual components unbounded. The aggregate
diagonal-dominance conjecture is not refuted by this obstruction.
-/

noncomputable section
open Finset
namespace RHTower

private def gcdElevenCoprimePolynomial (x a b c y e z : ℝ) : ℝ :=
  2*(a*b+a*c+a*e+b*c+b*e+c*e - x*(a+b+c+e-y-z)-b*z-c*y-e*y-e*z)
private def gcdElevenTotalPolynomial (x a b c y e z : ℝ) : ℝ :=
  (x-a-b-c+y-e+z)^2-(x^2+a^2+b^2+c^2+y^2+e^2+z^2)

private theorem gcd_coprime_polynomial_box {x a b c y e z : ℝ}
    (hx : 0.15 ≤ x ∧ x ≤ 0.18) (ha : 0.20 ≤ a ∧ a ≤ 0.21)
    (hb : 0.19 ≤ b ∧ b ≤ 0.20) (hc : 0.14 ≤ c ∧ c ≤ 0.15)
    (hy : 0.13 ≤ y ∧ y ≤ 0.14) (he : 0.10 ≤ e ∧ e ≤ 0.11)
    (hz : 0.023 ≤ z ∧ z ≤ 0.025) :
    1/100 < gcdElevenCoprimePolynomial x a b c y e z := by
  have hab := mul_le_mul ha.1 hb.1 (by norm_num : (0:ℝ) ≤ 0.19) (by linarith : 0 ≤ a)
  have hac := mul_le_mul ha.1 hc.1 (by norm_num : (0:ℝ) ≤ 0.14) (by linarith : 0 ≤ a)
  have hae := mul_le_mul ha.1 he.1 (by norm_num : (0:ℝ) ≤ 0.10) (by linarith : 0 ≤ a)
  have hbc := mul_le_mul hb.1 hc.1 (by norm_num : (0:ℝ) ≤ 0.14) (by linarith : 0 ≤ b)
  have hbe := mul_le_mul hb.1 he.1 (by norm_num : (0:ℝ) ≤ 0.10) (by linarith : 0 ≤ b)
  have hce := mul_le_mul hc.1 he.1 (by norm_num : (0:ℝ) ≤ 0.10) (by linarith : 0 ≤ c)
  have ht0 : 0 ≤ a+b+c+e-y-z := by linarith
  have hthi : a+b+c+e-y-z ≤ 517/1000 := by linarith
  have hxt := mul_le_mul hx.2 hthi ht0 (by norm_num : (0:ℝ) ≤ 0.18)
  have hbz := mul_le_mul hb.2 hz.2 (by linarith : 0 ≤ z) (by norm_num : (0:ℝ) ≤ 0.20)
  have hcy := mul_le_mul hc.2 hy.2 (by linarith : 0 ≤ y) (by norm_num : (0:ℝ) ≤ 0.15)
  have hey := mul_le_mul he.2 hy.2 (by linarith : 0 ≤ y) (by norm_num : (0:ℝ) ≤ 0.11)
  have hez := mul_le_mul he.2 hz.2 (by linarith : 0 ≤ z) (by norm_num : (0:ℝ) ≤ 0.11)
  unfold gcdElevenCoprimePolynomial
  nlinarith only [hab,hac,hae,hbc,hbe,hce,hxt,hbz,hcy,hey,hez]

private theorem gcd_total_polynomial_box {x a b c y e z : ℝ}
    (hx : 0.15 ≤ x ∧ x ≤ 0.18) (ha : 0.20 ≤ a ∧ a ≤ 0.21)
    (hb : 0.19 ≤ b ∧ b ≤ 0.20) (hc : 0.14 ≤ c ∧ c ≤ 0.15)
    (hy : 0.13 ≤ y ∧ y ≤ 0.14) (he : 0.10 ≤ e ∧ e ≤ 0.11)
    (hz : 0.023 ≤ z ∧ z ≤ 0.025) :
    gcdElevenTotalPolynomial x a b c y e z < -1/100 := by
  have hsq (l u : ℝ) (hl : 0 ≤ l) (hu : l ≤ u) : l^2 ≤ u^2 := by
    simpa only [pow_two] using mul_le_mul hu hu hl (hl.trans hu)
  have hQ : (145629/1000000:ℝ) ≤ x^2+a^2+b^2+c^2+y^2+e^2+z^2 := by
    linarith [hsq 0.15 x (by norm_num) hx.1,hsq 0.20 a (by norm_num) ha.1,
      hsq 0.19 b (by norm_num) hb.1,hsq 0.14 c (by norm_num) hc.1,
      hsq 0.13 y (by norm_num) hy.1,hsq 0.10 e (by norm_num) he.1,
      hsq 0.023 z (by norm_num) hz.1]
  have hSlo : -(367/1000:ℝ) ≤ x-a-b-c+y-e+z := by linarith
  have hShi : x-a-b-c+y-e+z ≤ -(285/1000:ℝ) := by linarith
  have hp := mul_nonneg (show 0 ≤ (x-a-b-c+y-e+z)+367/1000 by linarith)
    (show 0 ≤ 367/1000-(x-a-b-c+y-e+z) by linarith)
  have hSsq : (x-a-b-c+y-e+z)^2 ≤ (367/1000:ℝ)^2 := by nlinarith only [hp]
  unfold gcdElevenTotalPolynomial
  nlinarith only [hQ,hSsq]

private theorem gcd_eleven_one_formula :
    mobiusDivisorGcdCross 11 1 = gcdElevenCoprimePolynomial
      (mobiusDivisorDilationChannel 11 1) (-mobiusDivisorDilationChannel 11 2)
      (-mobiusDivisorDilationChannel 11 3) (-mobiusDivisorDilationChannel 11 5)
      (mobiusDivisorDilationChannel 11 6) (-mobiusDivisorDilationChannel 11 7)
      (mobiusDivisorDilationChannel 11 10) := by
  obtain ⟨h4,h8,h9,h11⟩ := mobiusDivisorDilationChannel_eleven_zero
  norm_num [mobiusDivisorGcdCross,sum_Icc_succ_top,h4,h8,h9,h11,gcdElevenCoprimePolynomial]
  ring

private theorem gcd_eleven_total_formula :
    (∑ r ∈ Icc 1 11, mobiusDivisorGcdCross 11 r) = gcdElevenTotalPolynomial
      (mobiusDivisorDilationChannel 11 1) (-mobiusDivisorDilationChannel 11 2)
      (-mobiusDivisorDilationChannel 11 3) (-mobiusDivisorDilationChannel 11 5)
      (mobiusDivisorDilationChannel 11 6) (-mobiusDivisorDilationChannel 11 7)
      (mobiusDivisorDilationChannel 11 10) := by
  rw [sum_mobiusDivisorGcdCross]
  obtain ⟨h4,h8,h9,h11⟩ := mobiusDivisorDilationChannel_eleven_zero
  norm_num [sum_Icc_succ_top,h4,h8,h9,h11,gcdElevenTotalPolynomial]

/-- The actual coprime component has the wrong sign for componentwise diagonal dominance. -/
theorem oneHundredth_lt_mobiusDivisorGcdCross_one_eleven :
    (1/100:ℝ) < mobiusDivisorGcdCross 11 1 := by
  rw [gcd_eleven_one_formula]
  obtain ⟨hx,ha,hb,hc,hy,he,hz⟩ := mobiusDivisorDilationChannel_eleven_box
  exact gcd_coprime_polynomial_box hx ha hb hc hy he hz

/-- At the same actual cutoff the complete cross sum is strictly negative. Positive coprime
interference is compensated by the other common-divisor components. -/
theorem sum_mobiusDivisorGcdCross_eleven_lt_neg_oneHundredth :
    (∑ r ∈ Icc 1 11, mobiusDivisorGcdCross 11 r) < -(1/100:ℝ) := by
  rw [gcd_eleven_total_formula]
  obtain ⟨hx,ha,hb,hc,hy,he,hz⟩ := mobiusDivisorDilationChannel_eleven_box
  convert gcd_total_polynomial_box hx ha hb hc hy he hz using 1
  ring

/-- Every prime dilation beyond eleven carries a positive common-divisor component. -/
theorem prime_div_hundred_lt_mobiusDivisorGcdCross {p : ℕ}
    (hp : Nat.Prime p) (hp11 : 11 < p) :
    (p : ℝ)/100 < mobiusDivisorGcdCross (p*11) p := by
  rw [mobiusDivisorGcdCross_mul_prime hp hp11]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h := mul_lt_mul_of_pos_left oneHundredth_lt_mobiusDivisorGcdCross_one_eleven hp0
  nlinarith only [h]

/-- The literal positive common-divisor components are unbounded, at unbounded cutoffs.
This refutes separate component sign control; it does not determine the complete cross sum. -/
theorem mobiusDivisorGcdCross_positive_unbounded :
    ∀ N : ℕ, ∃ M r : ℕ, N ≤ M ∧ 1 ≤ r ∧ (N : ℝ) < mobiusDivisorGcdCross M r := by
  intro N
  obtain ⟨p,hpN,hp⟩ := Nat.exists_infinite_primes (100*N+12)
  have hp11 : 11 < p := by omega
  refine ⟨p*11,p,by omega,hp.pos,?_⟩
  have hlow : (100 : ℝ)*(N : ℝ)+12 ≤ p := by exact_mod_cast hpN
  exact lt_trans (by linarith : (N : ℝ) < (p : ℝ)/100)
    (prime_div_hundred_lt_mobiusDivisorGcdCross hp hp11)

end RHTower
