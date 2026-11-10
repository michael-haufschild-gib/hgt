import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherLogLattice

/-!
# Uniform constants for growing Gaussian moment orders

On the critical abscissa, the derivative recursion visits only quarter-line
Gamma values. Bounding those values before summing the recursion makes the
moment-order dependence explicit.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem gamma_nat_add_le {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (j p : ℕ) (hjp : j ≤ p) :
    Real.Gamma ((j : ℝ) + q) ≤ Real.Gamma q * (p : ℝ) ^ j := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
    have hjp' : j ≤ p := by omega
    have harg : 0 < (j : ℝ) + q := by positivity
    have hfac : (j : ℝ) + q ≤ p := by
      have hp : (j : ℝ) + 1 ≤ p := by exact_mod_cast hjp
      linarith only [hp, hq1]
    calc
      _ = ((j : ℝ) + q) * Real.Gamma ((j : ℝ) + q) := by
        rw [Nat.cast_add, Nat.cast_one, show (j : ℝ) + 1 + q = ((j : ℝ) + q) + 1 by ring,
          Real.Gamma_add_one harg.ne']
      _ ≤ (p : ℝ) * (Real.Gamma q * (p : ℝ) ^ j) :=
        mul_le_mul hfac (ih p hjp') (Real.Gamma_pos_of_pos harg).le (Nat.cast_nonneg p)
      _ = _ := by rw [pow_succ]; ring

private theorem gamma_nat_add_le_cap {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (j p : ℕ) (hp : 1 ≤ p) (hjp : j ≤ p) :
    Real.Gamma ((j : ℝ) + q) ≤ Real.Gamma q * (p : ℝ) ^ p := by
  apply (gamma_nat_add_le hq hq1 j p hjp).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by exact_mod_cast hp : (1 : ℝ) ≤ p) hjp)
    (Real.Gamma_pos_of_pos hq).le

/-- A single explicit envelope bounds every branch of the critical-abscissa
Gaussian derivative recursion. -/
theorem gaussianMellinJetConstant_quarter_le (p k j : ℕ) (hp : 1 ≤ p)
    (hkj : k + j ≤ p) :
    gaussianMellinJetConstant k ((k : ℝ) + 2 * j - 1 / 2) ≤
      Real.Gamma (1 / 4) / 2 * (p : ℝ) ^ p * (2 * p + 9) ^ k := by
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  induction k generalizing j with
  | zero =>
    simp only [gaussianMellinJetConstant, Nat.cast_zero, zero_add, pow_zero, mul_one]
    rw [show (2 * (j : ℝ) - 1 / 2 + 1) / 2 = (j : ℝ) + 1 / 4 by ring]
    have hh := gamma_nat_add_le_cap (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) j p hp (by omega)
    linarith only [hh]
  | succ k ih =>
    have hm := ih j (by omega : k + j ≤ p)
    have hu := ih (j + 1) (by omega : k + (j + 1) ≤ p)
    let a : ℝ := ((k + 1 : ℕ) : ℝ) + 2 * j - 1 / 2
    have ha : 0 < a := by
      dsimp [a]
      push_cast
      nlinarith only [Nat.cast_nonneg k, Nat.cast_nonneg j]
    have hmarg : a - 1 = (k : ℝ) + 2 * j - 1 / 2 := by dsimp [a]; push_cast; ring
    have huarg : a + 1 = (k : ℝ) + 2 * (j + 1 : ℕ) - 1 / 2 := by
      dsimp [a]; push_cast; ring
    have hcoef : |a| + 1 ≤ 2 * (p : ℝ) + 1 := by
      rw [abs_of_pos ha]
      have hh : (k : ℝ) + 1 + j ≤ p := by exact_mod_cast hkj
      dsimp [a]
      push_cast
      linarith only [hh, Nat.cast_nonneg k]
    have hE : 0 ≤ Real.Gamma (1 / 4) / 2 * (p : ℝ) ^ p * (2 * p + 9) ^ k := by positivity
    change (|a| + 1) * gaussianMellinJetConstant k (a - 1) +
      8 * gaussianMellinJetConstant k (a + 1) ≤ _
    rw [hmarg, huarg]
    calc
      _ ≤ (|a| + 1) * (Real.Gamma (1 / 4) / 2 * (p : ℝ) ^ p * (2 * p + 9) ^ k) +
          8 * (Real.Gamma (1 / 4) / 2 * (p : ℝ) ^ p * (2 * p + 9) ^ k) :=
        _root_.add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
          (mul_le_mul_of_nonneg_left hu (by norm_num))
      _ ≤ (2 * (p : ℝ) + 1) *
          (Real.Gamma (1 / 4) / 2 * (p : ℝ) ^ p * (2 * p + 9) ^ k) +
          8 * (Real.Gamma (1 / 4) / 2 * (p : ℝ) ^ p * (2 * p + 9) ^ k) :=
        _root_.add_le_add (mul_le_mul_of_nonneg_right hcoef hE) (le_refl _)
      _ = _ := by rw [pow_succ]; ring

private theorem bernoulli_quotient_le {r : ℕ} (hr : r ≠ 0) :
    |((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ) ≤ 1 := by
  have hF : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpow : (4 : ℝ) ≤ 2 ^ (2 * r) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ 2 * r by omega)
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hden : (4 : ℝ) ≤ (2 * Real.pi) ^ (2 * r) :=
    hpow.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hpi _)
  have hd0 : (0 : ℝ) < (2 * Real.pi) ^ (2 * r) := by positivity
  have hf : (2 : ℝ) / 2 ^ (2 * r) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (2 * r))).mpr (by linarith only [hpow])
  have he : (0 : ℝ) < 1 - 2 / 2 ^ (2 * r) := by linarith only [hf]
  have hi : ((1 : ℝ) - 2 / 2 ^ (2 * r))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ he).mpr (by linarith only [hf])
  have hn : 2 * ((2 * r).factorial : ℝ) / (2 * Real.pi) ^ (2 * r) ≤
      ((2 * r).factorial : ℝ) / 2 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden hF.le]
  apply (div_le_iff₀ hF).mpr
  calc
    _ ≤ 2 * ((2 * r).factorial : ℝ) / (2 * Real.pi) ^ (2 * r) *
        ((1 : ℝ) - 2 / 2 ^ (2 * r))⁻¹ := (RHTower.DQPT.dqpt_abs_bernoulli_bounds hr).2
    _ ≤ (((2 * r).factorial : ℝ) / 2) * 2 :=
      mul_le_mul hn hi (by positivity) (by positivity)
    _ = _ := by ring

/-- The physical critical-abscissa lattice constant grows at most like
`(8192 r⁴)^r`, with a fixed Gamma multiplier. -/
theorem gaussianHigherMomentLatticeConstant_half_physical_le (r : ℕ) (hr : r ≠ 0) :
    gaussianHigherMomentLatticeConstant r (1 / 2) *
      (2 : ℝ) ^ (((2 * r : ℕ) + (1 / 2 : ℝ) - 1) / 2) ≤
      Real.Gamma (1 / 4) * (8192 * (r : ℝ) ^ 4) ^ r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hG : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hC := gaussianMellinJetConstant_quarter_le (2 * r) (2 * r) 0
    (by omega) (by omega)
  simp only [Nat.cast_zero, mul_zero, add_zero] at hC
  have hC0 := gaussianMellinJetConstant_nonneg (2 * r)
    (show ((2 * r : ℕ) : ℝ) - 1 < (2 * r : ℕ) - (1 / 2 : ℝ) by linarith)
  have hB := bernoulli_quotient_le hr
  have htwo : (2 : ℝ) ^ (((2 * r : ℕ) + (1 / 2 : ℝ) - 1) / 2) ≤ (2 : ℝ) ^ r := by
    rw [← Real.rpow_natCast 2 r]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hbase : 8 * (2 * (r : ℝ)) ^ 2 * (4 * (r : ℝ) + 9) ^ 2 ≤
      8192 * (r : ℝ) ^ 4 := by
    calc
      _ ≤ 8 * (2 * (r : ℝ)) ^ 2 * (13 * (r : ℝ)) ^ 2 := by gcongr; linarith only [hr1]
      _ = 5408 * (r : ℝ) ^ 4 := by ring
      _ ≤ _ := by nlinarith only [pow_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) 4]
  calc
    _ = (4 ^ r * (|((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ)) *
        gaussianMellinJetConstant (2 * r) ((2 * r : ℕ) - (1 / 2 : ℝ))) *
        (2 : ℝ) ^ (((2 * r : ℕ) + (1 / 2 : ℝ) - 1) / 2) := by
      unfold gaussianHigherMomentLatticeConstant
      ring
    _ ≤ (4 ^ r * 1 *
        (Real.Gamma (1 / 4) / 2 * ((2 * r : ℕ) : ℝ) ^ (2 * r) *
          (2 * (2 * r : ℕ) + 9) ^ (2 * r))) * (2 : ℝ) ^ r := by gcongr
    _ = Real.Gamma (1 / 4) / 2 *
        (8 * (2 * (r : ℝ)) ^ 2 * (4 * (r : ℝ) + 9) ^ 2) ^ r := by
      push_cast
      rw [pow_mul, pow_mul]
      calc
        _ = Real.Gamma (1 / 4) / 2 *
            (((4 : ℝ) ^ r * 2 ^ r) * ((2 * (r : ℝ)) ^ 2) ^ r *
              ((4 * (r : ℝ) + 9) ^ 2) ^ r) := by ring
        _ = _ := by rw [← mul_pow, ← mul_pow, ← mul_pow]; norm_num
    _ ≤ _ := mul_le_mul (by linarith only [hG])
      (pow_le_pow_left₀ (by positivity) hbase r) (by positivity) hG.le

/-- Below the height, all lattice constants are paid by five height powers
per moment order. -/
theorem gaussianHigherMomentLatticeConstant_half_le_height (r : ℕ) (hr : r ≠ 0)
    {t : ℝ} (ht : 8192 ≤ t) (hrt : (r : ℝ) ≤ t) :
    gaussianHigherMomentLatticeConstant r (1 / 2) *
      (2 : ℝ) ^ (((2 * r : ℕ) + (1 / 2 : ℝ) - 1) / 2) ≤
      Real.Gamma (1 / 4) * t ^ (5 * r) := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hbase : 8192 * (r : ℝ) ^ 4 ≤ t ^ 5 := by
    calc
      _ ≤ t * t ^ 4 := mul_le_mul ht (pow_le_pow_left₀ (Nat.cast_nonneg r) hrt 4)
        (by positivity) ht0
      _ = _ := by ring
  apply (gaussianHigherMomentLatticeConstant_half_physical_le r hr).trans
  rw [pow_mul]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase r)
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).le

#print axioms gaussianMellinJetConstant_quarter_le
#print axioms gaussianHigherMomentLatticeConstant_half_physical_le
#print axioms gaussianHigherMomentLatticeConstant_half_le_height

end GaloisForLFunctions.ExceptionalLayerTheory
