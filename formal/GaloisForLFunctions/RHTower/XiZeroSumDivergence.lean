import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.XiRealAxisGrowth

/-!
# The reciprocal zero sum of the completed zeta function diverges

The unconditional Hadamard factorization of `XiC` carries no exponential factor, so `XiC` is
literally `XiC 0` times its genus-one canonical product.  If the reciprocal zero norms were
summable in the first power, the termwise bound `|E₁(w)| ≤ exp (2‖w‖)` would give

```
‖XiC z‖ ≤ ‖XiC 0‖ · exp (2 ‖z‖ · ∑ 1/‖ρ‖),
```

that is, exponential type.  Along the even integers `xi` grows like a factorial, so this is
impossible: `∑_ρ 1/‖ρ‖ = ∞`.

This is the classical statement that the Xi divisor has genus one and not genus zero, obtained here
without any counting law.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Exponential type from first-power summability.**  A genus-one canonical product whose
reciprocal zero norms are summable has at most exponential growth. -/
theorem norm_canonicalProductE1Indexed_le_exp_of_summable_inv {ι : Type*}
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsq : Summable (fun i => 1 / ‖a i‖ ^ 2))
    (hsum : Summable (fun i => 1 / ‖a i‖)) (z : ℂ) :
    ‖canonicalProductE1Indexed a z‖ ≤ Real.exp (2 * ‖z‖ * ∑' i, 1 / ‖a i‖) := by
  refine le_trans (canonicalProductE1Indexed_norm_le_exp_min a ha hsq z) ?_
  refine Real.exp_le_exp.mpr ?_
  have hdom : Summable (fun i => 2 * ‖z‖ * (1 / ‖a i‖)) := hsum.mul_left _
  have hminle : ∀ i, min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ 2 / ‖a i‖ ^ 2)
      ≤ 2 * ‖z‖ * (1 / ‖a i‖) := by
    intro i
    refine le_trans (min_le_left _ _) (le_of_eq ?_)
    ring
  have hminnn : ∀ i, 0 ≤ min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ 2 / ‖a i‖ ^ 2) := by
    intro i
    exact le_min (by positivity) (by positivity)
  have hminsum : Summable (fun i => min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ 2 / ‖a i‖ ^ 2)) :=
    Summable.of_nonneg_of_le hminnn hminle hdom
  calc (∑' i, min (2 * ‖z‖ / ‖a i‖) (2 * ‖z‖ ^ 2 / ‖a i‖ ^ 2))
      ≤ ∑' i, 2 * ‖z‖ * (1 / ‖a i‖) := Summable.tsum_le_tsum hminle hminsum hdom
    _ = 2 * ‖z‖ * ∑' i, 1 / ‖a i‖ := hsum.tsum_mul_left _

/-- The Xi canonical product would have exponential type. -/
theorem norm_xiCanonicalProduct_le_exp_of_summable
    (hsum : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖)) (z : ℂ) :
    ‖xiCanonicalProduct z‖
      ≤ Real.exp (2 * ‖z‖ * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖) :=
  norm_canonicalProductE1Indexed_le_exp_of_summable_inv xiSpectralPoint
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable hsum z

/-- Hence so would `XiC`, the Hadamard factorization contributing only the constant `XiC 0`. -/
theorem norm_XiC_le_exp_of_summable
    (hsum : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖)) (z : ℂ) :
    ‖XiC z‖
      ≤ ‖XiC 0‖ * Real.exp (2 * ‖z‖ * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖) := by
  have hfac : XiC z = XiC 0 * xiCanonicalProduct z :=
    congrFun XiC_eq_constant_mul_canonicalProduct z
  rw [hfac, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_xiCanonicalProduct_le_exp_of_summable hsum z)
    (norm_nonneg _)

/-- The rotation carrying the centered variable onto the even integer `2(m+1)`. -/
def xiEvenRotation (m : ℕ) : ℂ := -Complex.I * (2 * ((m : ℂ) + 1) - 1 / 2)

theorem XiC_xiEvenRotation (m : ℕ) :
    XiC (xiEvenRotation m) = xi (2 * ((m : ℂ) + 1)) := by
  rw [XiC, xiEvenRotation]
  congr 1
  have hI : (-Complex.I) * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  calc (1 : ℂ) / 2 + -Complex.I * (2 * ((m : ℂ) + 1) - 1 / 2) * Complex.I
      = 1 / 2 + ((-Complex.I) * Complex.I) * (2 * ((m : ℂ) + 1) - 1 / 2) := by ring
    _ = 2 * ((m : ℂ) + 1) := by rw [hI]; ring

theorem norm_xiEvenRotation_le (m : ℕ) : ‖xiEvenRotation m‖ ≤ 2 * ((m : ℝ) + 1) := by
  have hval : xiEvenRotation m
      = -Complex.I * ((2 * ((m : ℝ) + 1) - 1 / 2 : ℝ) : ℂ) := by
    rw [xiEvenRotation]
    push_cast
    ring
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [hval, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- **The reciprocal Xi zero sum diverges.**  Summability in the first power would make `XiC` of
exponential type, contradicting the factorial growth of `xi` along the even integers. -/
theorem not_summable_inv_norm_xiSpectralPoint :
    ¬ Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖) := by
  intro hsum
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun q => by positivity
  have hXi0 : ‖XiC 0‖ ≠ 0 := norm_ne_zero_iff.mpr XiC_zero_ne
  have hXi0pos : 0 < ‖XiC 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hXi0)
  set C : ℝ := |Real.log ‖XiC 0‖| + 2 * S with hC
  have hbdd : ∀ m : ℕ,
      Real.log ‖xi (2 * ((m : ℂ) + 1))‖ / (2 * ((m : ℝ) + 1)) ≤ C := by
    intro m
    have hden : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
    have hpos : 0 < ‖xi (2 * ((m : ℂ) + 1))‖ := by
      have hlow := factorial_mul_rpow_le_norm_xi m
      have : (0 : ℝ) < (m.factorial : ℝ) * Real.pi ^ (-((m : ℝ) + 1)) := by
        have := Real.rpow_pos_of_pos Real.pi_pos (-((m : ℝ) + 1))
        positivity
      linarith
    have hupper : ‖xi (2 * ((m : ℂ) + 1))‖
        ≤ ‖XiC 0‖ * Real.exp (2 * ‖xiEvenRotation m‖ * S) := by
      rw [← XiC_xiEvenRotation m]
      exact norm_XiC_le_exp_of_summable hsum _
    have hlog := Real.log_le_log hpos hupper
    have hval : Real.log (‖XiC 0‖ * Real.exp (2 * ‖xiEvenRotation m‖ * S))
        = Real.log ‖XiC 0‖ + 2 * ‖xiEvenRotation m‖ * S := by
      rw [Real.log_mul hXi0 (Real.exp_ne_zero _), Real.log_exp]
    rw [hval] at hlog
    have hrot : 2 * ‖xiEvenRotation m‖ * S ≤ 2 * (2 * ((m : ℝ) + 1)) * S := by
      have := norm_xiEvenRotation_le m
      nlinarith [hSnn, norm_nonneg (xiEvenRotation m)]
    rw [div_le_iff₀ hden, hC]
    have habs : Real.log ‖XiC 0‖ ≤ |Real.log ‖XiC 0‖| := le_abs_self _
    have habsnn : 0 ≤ |Real.log ‖XiC 0‖| := abs_nonneg _
    nlinarith [hlog, hrot, habs, habsnn, hSnn]
  have hgt := tendsto_log_norm_xi_div_atTop.eventually_gt_atTop C
  obtain ⟨m, hm⟩ := hgt.exists
  exact absurd (hbdd m) (not_le.mpr hm)

/-- Equivalent statement over the Xi zeros: the divisor is of genus one, not genus zero. -/
theorem not_summable_inv_norm_sub_half :
    ¬ Summable (fun q : XiZeroCopy => 1 / ‖(q.1 : ℂ) - 1 / 2‖) := by
  intro hsum
  refine not_summable_inv_norm_xiSpectralPoint ?_
  exact hsum.congr fun q => by rw [norm_xiSpectralPoint]

end

end RHTower
