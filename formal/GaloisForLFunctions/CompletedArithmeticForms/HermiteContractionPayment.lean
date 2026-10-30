import GaloisForLFunctions.CompletedArithmeticForms.HermiteRadiusPayment

/-!
# Factorial payment at a common Gaussian contraction degree

The falling factorial between two Hermite degrees is bounded by the top degree
power. A single radius four times the top Gaussian derivative scale then pays
every contraction coefficient by a geometric weight in its two degree gaps.
-/

noncomputable section

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- A lower Hermite degree pays its factorial gap at the top derivative scale. -/
theorem hermiteContractionFactor_le {r i N : ℕ} (hr : r ≤ i) (hi : i ≤ N) :
    (i.choose r : ℝ) * ((i - r).factorial : ℝ) * Real.sqrt (hermiteGaussianNormSq r) ≤
      hermiteContourRadius N ^ (i - r) * Real.sqrt (hermiteGaussianNormSq i) := by
  let F : ℝ := (i.choose r : ℝ) * ((i - r).factorial : ℝ)
  have hrp : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hfac : F * (r.factorial : ℝ) = (i.factorial : ℝ) := by
    have h : (i.choose r : ℝ) * (r.factorial : ℝ) * ((i - r).factorial : ℝ) =
        (i.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hr
    dsimp only [F]
    nlinarith only [h]
  have hdesc : (r.factorial : ℝ) * (i.descFactorial (i - r) : ℝ) =
      (i.factorial : ℝ) := by
    have h := Nat.factorial_mul_descFactorial (Nat.sub_le i r)
    rw [show i - (i - r) = r by omega] at h
    exact_mod_cast h
  have hFeq : F = (i.descFactorial (i - r) : ℝ) := by
    apply mul_right_cancel₀ hrp.ne'
    calc
      _ = (i.factorial : ℝ) := hfac
      _ = _ := by nlinarith only [hdesc]
  have hF : F ≤ ((N : ℝ) + 1) ^ (i - r) := by
    rw [hFeq]
    calc
      _ ≤ (i : ℝ) ^ (i - r) := by exact_mod_cast Nat.descFactorial_le_pow i (i - r)
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg i)
        (by
          have hir : (i : ℝ) ≤ N := by exact_mod_cast hi
          linarith only [hir]) _
  have hp8 : (8 : ℝ) ^ i = (8 : ℝ) ^ r * (8 : ℝ) ^ (i - r) := by
    rw [← pow_add, show r + (i - r) = i by omega]
  have ht : (hermiteContourRadius N ^ (i - r)) ^ 2 =
      (((N : ℝ) + 1) / 8) ^ (i - r) := by
    rw [← pow_mul, Nat.mul_comm (i - r) 2, pow_mul, hermiteContourRadius_sq]
  have hl : (F * Real.sqrt (hermiteGaussianNormSq r)) ^ 2 =
      F * (8 : ℝ) ^ r * (i.factorial : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (hermiteGaussianNormSq_pos r).le, hermiteGaussianNormSq]
    calc
      _ = F * (8 : ℝ) ^ r * (F * (r.factorial : ℝ)) := by ring
      _ = _ := by rw [hfac]
  have hu : (hermiteContourRadius N ^ (i - r) * Real.sqrt (hermiteGaussianNormSq i)) ^ 2 =
      ((N : ℝ) + 1) ^ (i - r) * (8 : ℝ) ^ r * (i.factorial : ℝ) := by
    rw [mul_pow, ht, Real.sq_sqrt (hermiteGaussianNormSq_pos i).le,
      hermiteGaussianNormSq, div_pow, hp8]
    field_simp
  have hb := mul_le_mul_of_nonneg_right hF
    (show 0 ≤ (8 : ℝ) ^ r * (i.factorial : ℝ) by positivity)
  have hs : (F * Real.sqrt (hermiteGaussianNormSq r)) ^ 2 ≤
      (hermiteContourRadius N ^ (i - r) * Real.sqrt (hermiteGaussianNormSq i)) ^ 2 := by
    rw [hl, hu]
    simpa only [mul_assoc] using hb
  have htpos := hermiteContourRadius_pos N
  have hrhs : 0 ≤ hermiteContourRadius N ^ (i - r) * Real.sqrt (hermiteGaussianNormSq i) :=
    mul_nonneg (pow_nonneg htpos.le _) (Real.sqrt_nonneg _)
  change F * Real.sqrt (hermiteGaussianNormSq r) ≤ _
  nlinarith only [hs, hrhs]

/-- One radius pays both factorial gaps and the entire binomial convolution coefficient. -/
theorem hermiteContractionCoefficient_le {r i j N : ℕ}
    (hri : r ≤ i) (hrj : r ≤ j) (hi : i ≤ N) (hj : j ≤ N) :
    (i.choose r : ℝ) * (j.choose r : ℝ) * hermiteGaussianNormSq r *
        (((i - r) + (j - r)).factorial : ℝ) /
        (4 * hermiteContourRadius N) ^ ((i - r) + (j - r)) ≤
      (1 / 2 : ℝ) ^ ((i - r) + (j - r)) *
        Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j) := by
  let a := i - r
  let b := j - r
  let t := hermiteContourRadius N
  have ht : 0 < t := hermiteContourRadius_pos N
  have hi' := hermiteContractionFactor_le hri hi
  have hj' := hermiteContractionFactor_le hrj hj
  have hm := mul_le_mul hi' hj' (by positivity) (by positivity)
  have hchoose : ((a + b).choose a : ℝ) ≤ (2 : ℝ) ^ (a + b) := by
    exact_mod_cast Nat.choose_le_two_pow (a + b) a
  have hfac : ((a + b).factorial : ℝ) =
      ((a + b).choose a : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h.symm
  have hprod :
      ((i.choose r : ℝ) * (a.factorial : ℝ) * Real.sqrt (hermiteGaussianNormSq r)) *
        ((j.choose r : ℝ) * (b.factorial : ℝ) * Real.sqrt (hermiteGaussianNormSq r)) ≤
      t ^ (a + b) * Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j) := by
    calc
      _ ≤ (t ^ a * Real.sqrt (hermiteGaussianNormSq i)) *
          (t ^ b * Real.sqrt (hermiteGaussianNormSq j)) := hm
      _ = _ := by rw [pow_add]; ring
  have hboth := mul_le_mul hchoose hprod (by positivity) (by positivity)
  have hden : 0 < (4 * t) ^ (a + b) := by positivity
  have hratio : (2 : ℝ) ^ (a + b) * t ^ (a + b) / (4 * t) ^ (a + b) =
      (1 / 2 : ℝ) ^ (a + b) := by
    rw [← mul_pow, ← div_pow]
    congr 1
    field_simp
    norm_num
  change (i.choose r : ℝ) * (j.choose r : ℝ) * hermiteGaussianNormSq r *
      ((a + b).factorial : ℝ) / (4 * t) ^ (a + b) ≤ _
  calc
    _ = ((a + b).choose a : ℝ) *
        (((i.choose r : ℝ) * (a.factorial : ℝ) * Real.sqrt (hermiteGaussianNormSq r)) *
          ((j.choose r : ℝ) * (b.factorial : ℝ) * Real.sqrt (hermiteGaussianNormSq r))) /
        (4 * t) ^ (a + b) := by
      rw [hfac]
      ring_nf
      rw [Real.sq_sqrt (hermiteGaussianNormSq_pos r).le]
      ring
    _ ≤ (2 : ℝ) ^ (a + b) *
        (t ^ (a + b) * Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j)) /
        (4 * t) ^ (a + b) := div_le_div_of_nonneg_right hboth hden.le
    _ = ((2 : ℝ) ^ (a + b) * t ^ (a + b) / (4 * t) ^ (a + b)) *
        Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j) := by ring
    _ = _ := by rw [hratio]

#print axioms hermiteContractionFactor_le
#print axioms hermiteContractionCoefficient_le

end GaloisForLFunctions.CompletedArithmeticForms
