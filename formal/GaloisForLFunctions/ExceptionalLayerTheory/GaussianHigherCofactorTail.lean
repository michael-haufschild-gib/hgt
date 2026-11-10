import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherCentredVaughan
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanCofactorTail

/-!
# Gaussian tails for higher arithmetic moments

The actual complementary Vaughan convolution vanishes below its product
cutoff. Extracting Gaussian decay there gives an estimate uniform in the
moment order, with only a factorial cost.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve ArithmeticFunction
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The complete higher moment with cofactors exceeding the cutoff. -/
def gaussianHigherVaughanCofactorTail (r : ℕ) (σ t : ℝ) (U V W : ℕ) (ε : ℂ) : ℂ :=
  ∑' n : ℕ, (gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
    gaussianHigherPrimeMomentWeight r σ t ε n

private theorem higher_tail_term_le (r : ℕ) {σ t : ℝ} (hσ : 0 ≤ σ)
    (ht : 0 < t) {ε : ℂ} (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (U V W n : ℕ) :
    ‖(gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
        gaussianHigherPrimeMomentWeight r σ t ε n‖ ≤
      2 * (4 * ε.re) ^ r * (n : ℝ) ^ (2 * (r + 1)) * Real.exp (-ε.re * (n : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hQ : ‖(ε / (t : ℂ)) ^ r‖ ≤ (4 * ε.re) ^ r := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    apply pow_le_pow_left₀ (by positivity)
    exact (div_le_iff₀ ht).mpr hsector
  rw [norm_mul]
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) *
        (‖(ε / (t : ℂ)) ^ r‖ * (n : ℝ) ^ (2 * r) * Real.exp (-ε.re * (n : ℝ) ^ 2)) :=
      mul_le_mul (norm_gaussianVaughanCofactorTailCoeff_le U V W n)
        (norm_gaussianHigherPrimeMomentWeight_le r hσ t ε hn) (norm_nonneg _) (by positivity)
    _ ≤ (2 * (n : ℝ) ^ 2) *
        ((4 * ε.re) ^ r * (n : ℝ) ^ (2 * r) * Real.exp (-ε.re * (n : ℝ) ^ 2)) := by gcongr
    _ = _ := by rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]; ring

/-- A direct Gaussian bound for the actual complementary arithmetic convolution. -/
theorem norm_gaussianHigherVaughanCofactorTail_le_gaussian (r : ℕ)
    {σ t X : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) {ε : ℂ}
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hX : 1 ≤ X) (hscale : ε.re * X ^ 2 = 2) (U V W : ℕ) :
    ‖gaussianHigherVaughanCofactorTail r σ t U V W ε‖ ≤
      784 * 32 ^ r * ((r + 1).factorial : ℝ) * X ^ 3 *
        Real.exp (-(((U * W : ℕ) : ℝ) / X) ^ 2) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  let B : ℝ := ((U * W : ℕ) : ℝ)
  let f := fun n : ℕ => (gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
    gaussianHigherPrimeMomentWeight r σ t ε n
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hs : Summable (fun n : ℕ => ‖f n‖) :=
    ((RHTower.summable_pow_mul_exp_neg_nat_sq (2 * (r + 1)) hε).mul_left
      (2 * (4 * ε.re) ^ r)).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
        simpa only [f, mul_assoc] using higher_tail_term_le r hσ ht hsector U V W n)
  have hpt (n : ℕ) : ‖f n‖ ≤
      (2 * (4 * ε.re) ^ r * Real.exp (-(ε.re / 2) * B ^ 2)) *
        ((n : ℝ) ^ (2 * (r + 1)) * Real.exp (-(ε.re / 4) * (n : ℝ) ^ 2)) := by
    by_cases hn : n ≤ U * W
    · dsimp only [f]
      rw [gaussianVaughanCofactorTailCoeff_eq_zero hn, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    have hBn : B ≤ (n : ℝ) := by
      dsimp only [B]
      exact_mod_cast (show U * W ≤ n by omega)
    have hsq := pow_le_pow_left₀ hB hBn 2
    have he : Real.exp (-ε.re * (n : ℝ) ^ 2) ≤
        Real.exp (-(ε.re / 2) * B ^ 2) * Real.exp (-(ε.re / 4) * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hsq hε.le,
        mul_nonneg hε.le (sq_nonneg (n : ℝ))]
    apply (higher_tail_term_le r hσ ht hsector U V W n).trans
    calc
      _ ≤ 2 * (4 * ε.re) ^ r * (n : ℝ) ^ (2 * (r + 1)) *
          (Real.exp (-(ε.re / 2) * B ^ 2) * Real.exp (-(ε.re / 4) * (n : ℝ) ^ 2)) := by gcongr
      _ = _ := by ring
  have hY : 1 ≤ 2 * X := by linarith only [hX]
  have hscaleY : (ε.re / 4) * (2 * X) ^ 2 = 2 := by nlinarith only [hscale]
  have hm := tsum_pow_mul_exp_gaussian_le (by positivity : 0 < ε.re / 4)
    hY hscaleY (r + 1)
  have hsum : ‖∑' n : ℕ, f n‖ ≤
      (2 * (4 * ε.re) ^ r * Real.exp (-(ε.re / 2) * B ^ 2)) *
        (49 * ((r + 1).factorial : ℝ) * (2 * X) ^ (2 * (r + 1) + 1)) := by
    calc
      _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, (2 * (4 * ε.re) ^ r * Real.exp (-(ε.re / 2) * B ^ 2)) *
          ((n : ℝ) ^ (2 * (r + 1)) * Real.exp (-(ε.re / 4) * (n : ℝ) ^ 2)) :=
        hs.tsum_le_tsum hpt ((RHTower.summable_pow_mul_exp_neg_nat_sq
          (2 * (r + 1)) (by positivity : 0 < ε.re / 4)).mul_left _)
      _ = (2 * (4 * ε.re) ^ r * Real.exp (-(ε.re / 2) * B ^ 2)) *
          ∑' n : ℕ, (n : ℝ) ^ (2 * (r + 1)) * Real.exp (-(ε.re / 4) * (n : ℝ) ^ 2) := by
        rw [tsum_mul_left]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  change ‖∑' n : ℕ, f n‖ ≤ _
  apply hsum.trans_eq
  have he : -(ε.re / 2) * B ^ 2 = -(B / X) ^ 2 := by
    have hα : ε.re = 2 / X ^ 2 := (eq_div_iff (pow_ne_zero 2 hX0.ne')).mpr hscale
    rw [hα]
    field_simp
  have hp : (4 * ε.re) ^ r * (2 * X) ^ (2 * r) = (32 : ℝ) ^ r := by
    rw [pow_mul, ← mul_pow]
    congr 1
    nlinarith only [hscale]
  rw [he, show 2 * (r + 1) + 1 = 2 * r + 3 by omega, pow_add]
  calc
    _ = 98 * ((r + 1).factorial : ℝ) *
        ((4 * ε.re) ^ r * (2 * X) ^ (2 * r)) * (2 * X) ^ 3 * Real.exp (-(B / X) ^ 2) := by ring
    _ = _ := by rw [hp]; dsimp only [B]; ring

/-- Factorial order cost is paid by a height power throughout `r≤t`. -/
private theorem higher_tail_factorial_le (r : ℕ) {t : ℝ}
    (ht : 32 ≤ t) (hrt : (r : ℝ) ≤ t) :
    (32 : ℝ) ^ r * ((r + 1).factorial : ℝ) ≤ t ^ (3 * r + 2) := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hbase : ((r + 1 : ℕ) : ℝ) ≤ t ^ 2 := by
    push_cast
    nlinarith only [hrt, ht, sq_nonneg (t - 1)]
  have hf : ((r + 1).factorial : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ (r + 1) := by
    exact_mod_cast Nat.factorial_le_pow (r + 1)
  have hfp : ((r + 1).factorial : ℝ) ≤ t ^ (2 * (r + 1)) := by
    apply hf.trans
    simpa only [pow_mul] using pow_le_pow_left₀ (by positivity) hbase (r + 1)
  calc
    _ ≤ t ^ r * t ^ (2 * (r + 1)) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) ht r) hfp
        (by positivity) (pow_nonneg ht0 _)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Gaussian decay beyond a polynomial-height product horizon dominates
every moment order below the height. -/
theorem norm_gaussianHigherVaughanCofactorTail_le_exp_neg_sq (r : ℕ)
    {σ a t : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) (ht : 32 ≤ t)
    (hat : 3 * a ≤ t) (hrt : (r : ℝ) ≤ t) {ε : ℂ}
    (hε : 0 < ε.re) (hsector : ‖ε‖ ≤ 4 * ε.re * t)
    (hscale : ε.re * (Real.exp (a * t)) ^ 2 = 2) (U V W : ℕ)
    (hUW : Real.exp (a * t) * t ^ 2 ≤ ((U * W : ℕ) : ℝ)) :
    ‖gaussianHigherVaughanCofactorTail r σ t U V W ε‖ ≤ 784 * Real.exp (-t ^ 2) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hX0 := Real.exp_pos (a * t)
  have hX1 : 1 ≤ Real.exp (a * t) := Real.one_le_exp_iff.mpr (by positivity)
  have hratio : t ^ 2 ≤ ((U * W : ℕ) : ℝ) / Real.exp (a * t) := by
    apply (le_div_iff₀ hX0).mpr
    simpa only [mul_comm] using hUW
  have hratio2 := pow_le_pow_left₀ (sq_nonneg t) hratio 2
  have hlog : Real.log t ≤ t := by
    have hh := Real.log_le_sub_one_of_pos ht0
    linarith only [hh]
  have hcost : ((3 * r + 2 : ℕ) : ℝ) * Real.log t ≤ (3 * t + 2) * t := by
    push_cast
    calc
      _ ≤ (3 * (r : ℝ) + 2) * t := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hrt]) ht0.le
  have hquad : 6 ≤ t ^ 2 := by nlinarith only [ht, sq_nonneg (t - 3)]
  have hfour := mul_le_mul_of_nonneg_right hquad (sq_nonneg t)
  have hlinear : 2 * t ≤ t ^ 2 := by nlinarith only [ht, sq_nonneg (t - 1)]
  have haquad := mul_le_mul_of_nonneg_right hat ht0.le
  have hexponent : ((3 * r + 2 : ℕ) : ℝ) * Real.log t + 3 * (a * t) -
      (((U * W : ℕ) : ℝ) / Real.exp (a * t)) ^ 2 ≤ -t ^ 2 := by
    nlinarith only [hcost, hratio2, hfour, hlinear, haquad]
  have hbound : t ^ (3 * r + 2) * Real.exp (a * t) ^ 3 *
      Real.exp (-(((U * W : ℕ) : ℝ) / Real.exp (a * t)) ^ 2) ≤ Real.exp (-t ^ 2) := by
    have hp : t ^ (3 * r + 2) = Real.exp (((3 * r + 2 : ℕ) : ℝ) * Real.log t) := by
      rw [Real.exp_nat_mul, Real.exp_log ht0]
    rw [hp, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent
  apply (norm_gaussianHigherVaughanCofactorTail_le_gaussian r hσ ht0 hε hsector
    hX1 hscale U V W).trans
  calc
    _ ≤ 784 * t ^ (3 * r + 2) * Real.exp (a * t) ^ 3 *
        Real.exp (-(((U * W : ℕ) : ℝ) / Real.exp (a * t)) ^ 2) := by
      have hh := higher_tail_factorial_le r ht hrt
      nlinarith only [mul_le_mul_of_nonneg_right hh
        (show 0 ≤ 784 * Real.exp (a * t) ^ 3 *
          Real.exp (-(((U * W : ℕ) : ℝ) / Real.exp (a * t)) ^ 2) by positivity)]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 784)]

/-- Absolute convergence of the higher-moment complementary convolution. -/
theorem summable_gaussianHigherVaughanCofactorTail (r : ℕ) {σ t : ℝ}
    (hσ : 0 ≤ σ) (ht : 0 < t) {ε : ℂ} (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (U V W : ℕ) :
    Summable (fun n : ℕ => (gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n) := by
  apply ((RHTower.summable_pow_mul_exp_neg_nat_sq (2 * (r + 1)) hε).mul_left
    (2 * (4 * ε.re) ^ r)).of_norm_bounded
  intro n
  simpa only [mul_assoc] using higher_tail_term_le r hσ ht hsector U V W n

private theorem cofactorTail_zero_eq_typeII (U V : ℕ) :
    gaussianVaughanCofactorTailCoeff U V 0 = typeIILong U * typeIIShort V := by
  have hz : truncAF (typeIIShort V) 0 = 0 := by
    ext n
    change (if n ≤ 0 then typeIIShort V n else 0) = 0
    split_ifs with hn
    · simp [Nat.le_zero.mp hn]
    · rfl
  unfold gaussianVaughanCofactorTailCoeff
  rw [hz, sub_zero]

/-- The centred higher-moment current with an actual finite cofactor cutoff. -/
def gaussianHigherCentredVaughanCofactorCurrent
    (r : ℕ) (σ t : ℝ) (ε : ℂ) (U V W : ℕ) : ℂ :=
  (∑' n : ℕ, (((typeIILong U * truncAF (typeIIShort V) W) n : ℝ) : ℂ) *
    gaussianHigherPrimeMomentWeight r σ t ε n) +
  (∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t -
  (1 + (∑ b ∈ Icc 1 (U * V),
      (((truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b : ℝ) : ℂ) / (b : ℂ)) +
    ∑ b ∈ Icc 1 V, ((truncAF (moebius : ArithmeticFunction ℝ) V b : ℝ) : ℂ) *
      (Real.log (b : ℝ) : ℂ) / (b : ℂ)) *
    gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t

/-- Cofactor truncation leaves the two signed continuum corrections unchanged;
its exact error is the complementary arithmetic convolution. -/
theorem gaussianHigherCentredVaughan_sub_cofactorCurrent_eq (r : ℕ) {σ t : ℝ}
    (hσ : 0 ≤ σ) (ht : 0 < t) {ε : ℂ} (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (U V W : ℕ) :
    gaussianHigherCentredVaughanCurrent r σ t ε U V -
      gaussianHigherCentredVaughanCofactorCurrent r σ t ε U V W =
        gaussianHigherVaughanCofactorTail r σ t U V W ε := by
  let f := fun n : ℕ => (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
    gaussianHigherPrimeMomentWeight r σ t ε n
  let g := fun n : ℕ => (gaussianVaughanCofactorTailCoeff U V W n : ℂ) *
    gaussianHigherPrimeMomentWeight r σ t ε n
  have hf : Summable f := by
    have hh := summable_gaussianHigherVaughanCofactorTail r hσ ht hε hsector U V 0
    rw [cofactorTail_zero_eq_typeII] at hh
    exact hh
  have hg : Summable g := summable_gaussianHigherVaughanCofactorTail r hσ ht hε hsector U V W
  have hsplit : typeIILong U * typeIIShort V - gaussianVaughanCofactorTailCoeff U V W =
      typeIILong U * truncAF (typeIIShort V) W := by
    unfold gaussianVaughanCofactorTailCoeff
    rw [mul_sub]
    abel
  have hs : (∑' n : ℕ, (((typeIILong U * truncAF (typeIIShort V) W) n : ℝ) : ℂ) *
      gaussianHigherPrimeMomentWeight r σ t ε n) = (∑' n : ℕ, f n) - ∑' n : ℕ, g n := by
    rw [← hf.tsum_sub hg]
    apply tsum_congr
    intro n
    rw [← hsplit]
    change (((typeIILong U * typeIIShort V) n - gaussianVaughanCofactorTailCoeff U V W n : ℝ) : ℂ) *
        gaussianHigherPrimeMomentWeight r σ t ε n = f n - g n
    push_cast
    dsimp only [f, g]
    ring
  unfold gaussianHigherCentredVaughanCurrent gaussianHigherCentredVaughanCofactorCurrent
    gaussianHigherVaughanCofactorTail
  rw [hs]
  dsimp only [f, g]
  ring

#print axioms gaussianHigherCentredVaughan_sub_cofactorCurrent_eq
#print axioms norm_gaussianHigherVaughanCofactorTail_le_exp_neg_sq
#print axioms norm_gaussianHigherVaughanCofactorTail_le_gaussian
end GaloisForLFunctions.ExceptionalLayerTheory
