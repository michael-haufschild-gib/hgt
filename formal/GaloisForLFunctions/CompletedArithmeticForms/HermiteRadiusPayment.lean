import GaloisForLFunctions.RHTower.WholeAnchorHarmonicE3

/-!+# Polynomial payment of the Hermite contour factors

The radius of the degree `n` contour is `sqrt ((n+1)/8)`. Stirling's bound
then cancels the mixed Gaussian exponential, including either zero degree.
The resulting normalized contour cost is at most linear in the largest degree.
-/

noncomputable section

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Positive contour radius matched to a Gaussian polynomial degree. -/
def hermiteContourRadius (n : ℕ) : ℝ := Real.sqrt (((n : ℝ) + 1) / 8)

/-- Factorial remainder after the Gaussian norm and contour power are removed. -/
def hermiteContourWeight (n : ℕ) : ℝ :=
  Real.sqrt ((n.factorial : ℝ) / ((n : ℝ) + 1) ^ n)

/-- Exact diagonal norm of the monic Hermite polynomial for variance eight. -/
def hermiteGaussianNormSq (n : ℕ) : ℝ := (8 : ℝ) ^ n * (n.factorial : ℝ)

theorem hermiteGaussianNormSq_pos (n : ℕ) : 0 < hermiteGaussianNormSq n := by
  unfold hermiteGaussianNormSq
  positivity

theorem hermiteContourRadius_pos (n : ℕ) : 0 < hermiteContourRadius n := by
  unfold hermiteContourRadius
  positivity

theorem hermiteContourRadius_sq (n : ℕ) :
    hermiteContourRadius n ^ 2 = ((n : ℝ) + 1) / 8 := by
  exact Real.sq_sqrt (by positivity)

theorem hermiteContourWeight_pos (n : ℕ) : 0 < hermiteContourWeight n := by
  unfold hermiteContourWeight
  positivity

theorem hermiteContourWeight_sq (n : ℕ) :
    hermiteContourWeight n ^ 2 = (n.factorial : ℝ) / ((n : ℝ) + 1) ^ n := by
  exact Real.sq_sqrt (by positivity)

/-- Exact payment of one Cauchy factorial by its Hermite norm and adaptive weight. -/
theorem hermiteContour_factorial_identity (n : ℕ) :
    (n.factorial : ℝ) / hermiteContourRadius n ^ n =
      hermiteContourWeight n * Real.sqrt (hermiteGaussianNormSq n) := by
  have hr := hermiteContourRadius_pos n
  have hw := hermiteContourWeight_pos n
  have hD := hermiteGaussianNormSq_pos n
  have hp : (hermiteContourRadius n ^ n) ^ 2 = (((n : ℝ) + 1) / 8) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, hermiteContourRadius_sq]
  have he : ((n.factorial : ℝ) / hermiteContourRadius n ^ n) ^ 2 =
      (hermiteContourWeight n * Real.sqrt (hermiteGaussianNormSq n)) ^ 2 := by
    rw [div_pow, hp, div_pow, mul_pow, hermiteContourWeight_sq, Real.sq_sqrt hD.le]
    unfold hermiteGaussianNormSq
    field_simp
  have hl : 0 ≤ (n.factorial : ℝ) / hermiteContourRadius n ^ n := by positivity
  have hr' : 0 ≤ hermiteContourWeight n * Real.sqrt (hermiteGaussianNormSq n) := by positivity
  nlinarith only [he, hl, hr']

/-- A uniform Stirling envelope with the zero degree included. -/
theorem factorial_le_successor_exponential (n : ℕ) :
    (n.factorial : ℝ) ≤ Real.exp 1 * ((n : ℝ) + 1) *
      ((n : ℝ) + 1) ^ n * Real.exp (-(n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, zero_add, pow_zero,
      mul_one, neg_zero, Real.exp_zero]
    exact Real.one_le_exp zero_le_one
  have hn1 : 1 ≤ n := by omega
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
    have h := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [h, Real.sqrt_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n,
      sq_nonneg (n : ℝ)]
  have hp : ((n : ℝ) / Real.exp 1) ^ n ≤
      (((n : ℝ) + 1) / Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (by linarith) (Real.exp_pos _).le) n
  calc
    _ ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n :=
      _root_.RHTower.factorial_le_stirling hn1
    _ ≤ Real.exp 1 * ((n : ℝ) + 1) * (((n : ℝ) + 1) / Real.exp 1) ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) hp
        (by positivity) (by positivity)
    _ = _ := by
      rw [div_pow, ← Real.exp_nat_mul, mul_one, div_eq_mul_inv, ← Real.exp_neg]
      ring

/-- The factorial-normalized radius cost has Gaussian exponential decay in degree. -/
theorem hermiteContourWeight_sq_le (n : ℕ) :
    hermiteContourWeight n ^ 2 ≤
      Real.exp 1 * ((n : ℝ) + 1) * Real.exp (-(n : ℝ)) := by
  rw [hermiteContourWeight_sq]
  apply (div_le_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ n)).mpr
  calc
    _ ≤ Real.exp 1 * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ n *
        Real.exp (-(n : ℝ)) := factorial_le_successor_exponential n
    _ = _ := by ring

/-- The two radii retain only the geometric-mean Gaussian exponential. -/
theorem hermiteContourRadius_cross_le (i j : ℕ) :
    16 * hermiteContourRadius i * hermiteContourRadius j ≤
      (i : ℝ) + (j : ℝ) + 2 := by
  have h := sq_nonneg (hermiteContourRadius i - hermiteContourRadius j)
  have hi := hermiteContourRadius_sq i
  have hj := hermiteContourRadius_sq j
  nlinarith only [h, hi, hj]

/-- Combined normalized two-contour payment, before choosing a rank bound. -/
def hermiteContourPairWeight (i j : ℕ) : ℝ :=
  hermiteContourWeight i * hermiteContourWeight j *
    Real.exp (8 * hermiteContourRadius i * hermiteContourRadius j)

theorem hermiteContourPairWeight_sq_le (i j : ℕ) :
    hermiteContourPairWeight i j ^ 2 ≤
      Real.exp 4 * ((i : ℝ) + 1) * ((j : ℝ) + 1) := by
  have he : Real.exp (8 * hermiteContourRadius i * hermiteContourRadius j) ^ 2 =
      Real.exp (16 * hermiteContourRadius i * hermiteContourRadius j) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hp := mul_le_mul (hermiteContourWeight_sq_le i) (hermiteContourWeight_sq_le j)
    (sq_nonneg _) (by positivity)
  unfold hermiteContourPairWeight
  rw [mul_pow, mul_pow, he]
  calc
    _ ≤ (Real.exp 1 * ((i : ℝ) + 1) * Real.exp (-(i : ℝ))) *
        (Real.exp 1 * ((j : ℝ) + 1) * Real.exp (-(j : ℝ))) *
        Real.exp ((i : ℝ) + (j : ℝ) + 2) :=
      mul_le_mul hp (Real.exp_le_exp.mpr (hermiteContourRadius_cross_le i j))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      have he' : Real.exp 1 * Real.exp (-(i : ℝ)) * Real.exp 1 *
          Real.exp (-(j : ℝ)) * Real.exp ((i : ℝ) + (j : ℝ) + 2) = Real.exp 4 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp 1 * Real.exp (-(i : ℝ)) * Real.exp 1 *
            Real.exp (-(j : ℝ)) * Real.exp ((i : ℝ) + (j : ℝ) + 2)) *
            ((i : ℝ) + 1) * ((j : ℝ) + 1) := by ring
        _ = _ := by rw [he']

/-- Both factorial costs and the mixed exponential have only a linear rank payment. -/
theorem hermiteContourPairWeight_le {i j N : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    hermiteContourPairWeight i j ≤ Real.exp 2 * ((N : ℝ) + 1) := by
  have hir : (i : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hi 1
  have hjr : (j : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hj 1
  have hp := mul_le_mul hir hjr (by positivity : 0 ≤ (j : ℝ) + 1) (by positivity)
  have hb := (hermiteContourPairWeight_sq_le i j).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (Real.exp_pos 4).le)
  have he : Real.exp (2 : ℝ) ^ 2 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpos : 0 ≤ Real.exp 2 * ((N : ℝ) + 1) := by positivity
  have hb' : hermiteContourPairWeight i j ^ 2 ≤ (Real.exp 2 * ((N : ℝ) + 1)) ^ 2 := by
    calc
      _ ≤ Real.exp 4 * ((N : ℝ) + 1) * ((N : ℝ) + 1) := by
        simpa only [mul_assoc] using hb
      _ = _ := by rw [← he]; ring
  nlinarith only [hb', hpos]

/-- A common disk of radius `sqrt (N+2)` contains every pair of adaptive contours. -/
theorem hermiteContourRadius_add_le {i j N : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    hermiteContourRadius i + hermiteContourRadius j ≤ Real.sqrt ((N : ℝ) + 2) := by
  have hir : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hjr : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hr := sq_nonneg (hermiteContourRadius i - hermiteContourRadius j)
  have hri := hermiteContourRadius_sq i
  have hrj := hermiteContourRadius_sq j
  have hR := Real.sq_sqrt (show 0 ≤ (N : ℝ) + 2 by positivity)
  have hR0 := Real.sqrt_nonneg ((N : ℝ) + 2)
  have hi0 := (hermiteContourRadius_pos i).le
  have hj0 := (hermiteContourRadius_pos j).le
  nlinarith only [hir, hjr, hr, hri, hrj, hR, hR0, hi0, hj0,
    Nat.cast_nonneg (α := ℝ) N]

#print axioms hermiteContourPairWeight_le
#print axioms hermiteContourRadius_add_le
#print axioms hermiteContour_factorial_identity

end GaloisForLFunctions.CompletedArithmeticForms
