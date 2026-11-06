import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheForcedJumpsOfAProducer

/-!
# The Hecke action on producers

The dilation `T_j` sends a stencil `c` to `c(·/j)`. It acts on multiplicities by `g ↦ g(⌊r/j⌋)` and on
slopes by division by `j`. So producers form a module over the positive Hecke semiring: adding a positive
dilation keeps a producer a producer, with the same multiplicity floor.

**Positive amplification does not exist.** Adding `a T_j c` multiplies the slope by `1 + a/j` and
keeps the window, so the normalized slope strictly increases. Stencils cannot be improved by the Hecke
algebra alone. Negative combinations can leave the cone: the product of two balanced Dirichlet
polynomials has a double zero at `s = 1`, so its slope is `0`, and its multiplicity must change sign.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The dilation of a stencil by `j`. -/
def dilate (j : ℕ) (c : ℕ →₀ ℤ) : ℕ →₀ ℤ := c.mapDomain (j * ·)

private lemma stepWeight_eq_sum (c : ℕ →₀ ℤ) (m : ℕ) :
    stepWeight c m = c.sum fun k a => a * ((m / k : ℕ) : ℤ) := rfl

/-- Additivity of the multiplicity. -/
theorem stepWeight_add (c d : ℕ →₀ ℤ) (m : ℕ) :
    stepWeight (c + d) m = stepWeight c m + stepWeight d m := by
  simp only [stepWeight_eq_sum]
  exact Finsupp.sum_add_index' (by simp) (by intro _ a b; ring)

/-- Scaling of the multiplicity. -/
theorem stepWeight_smul (a : ℤ) (c : ℕ →₀ ℤ) (m : ℕ) :
    stepWeight (a • c) m = a * stepWeight c m := by
  simp only [stepWeight_eq_sum]
  rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun k _ => by ring

/-- **The Hecke action on multiplicities.** `g_{T_j c}(r) = g_c(⌊r/j⌋)`. -/
theorem stepWeight_dilate {j : ℕ} (c : ℕ →₀ ℤ) (m : ℕ) :
    stepWeight (dilate j c) m = stepWeight c (m / j) := by
  simp only [stepWeight_eq_sum, dilate]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intro _ a b; ring)]
  exact Finsupp.sum_congr fun k _ => by rw [Nat.div_div_eq_div_mul]

private lemma balance_eq_sum (c : ℕ →₀ ℤ) :
    ∑ k ∈ c.support, (c k : ℝ) / k = c.sum fun k a => (a : ℝ) / k := rfl

private lemma slope_eq_sum (c : ℕ →₀ ℤ) :
    stencilSlope c = c.sum fun k a => -(a : ℝ) * Real.log k / k := rfl

/-- Dilation keeps balance. -/
theorem isBalanced_dilate {j : ℕ} (hj : 0 < j) {c : ℕ →₀ ℤ} (hbal : IsBalanced c) :
    IsBalanced (dilate j c) := by
  rw [IsBalanced, balance_eq_sum, dilate, Finsupp.sum_mapDomain_index (by simp) (by
    intro _ a b; push_cast; ring)]
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have h : (c.sum fun k a => ((a : ℤ) : ℝ) / ((j * k : ℕ) : ℝ)) =
      (1 / (j : ℝ)) * ∑ k ∈ c.support, (c k : ℝ) / k := by
    rw [balance_eq_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun k _ => ?_
    push_cast
    rw [div_mul_div_comm, one_mul]
  rw [h, show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hbal, mul_zero]

/-- **The Hecke action on slopes.** A balanced stencil has `slope (T_j c) = slope c / j`. -/
theorem stencilSlope_dilate {j : ℕ} (hj : 0 < j) {c : ℕ →₀ ℤ} (hc0 : c 0 = 0)
    (hbal : IsBalanced c) : stencilSlope (dilate j c) = stencilSlope c / j := by
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [slope_eq_sum, dilate, Finsupp.sum_mapDomain_index (by simp) (by
    intro _ a b; push_cast; ring)]
  have hterm : ∀ k ∈ c.support, -((c k : ℤ) : ℝ) * Real.log ((j * k : ℕ) : ℝ) / ((j * k : ℕ) : ℝ) =
      (-(Real.log j) / j) * ((c k : ℝ) / k) + (-(c k : ℝ) * Real.log k / k) / j := by
    intro k hk
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    push_cast
    rw [Real.log_mul hjR hkR]
    field_simp
    ring
  have hsum : (c.sum fun k a => -((a : ℤ) : ℝ) * Real.log ((j * k : ℕ) : ℝ) / ((j * k : ℕ) : ℝ)) =
      ∑ k ∈ c.support, ((-(Real.log j) / j) * ((c k : ℝ) / k) +
        (-(c k : ℝ) * Real.log k / k) / j) := Finset.sum_congr rfl hterm
  rw [hsum, sum_add_distrib, ← mul_sum, ← sum_div,
    show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hbal, mul_zero, zero_add]
  rfl

private lemma isBalanced_add {c d : ℕ →₀ ℤ} (hc : IsBalanced c) (hd : IsBalanced d) :
    IsBalanced (c + d) := by
  rw [IsBalanced, balance_eq_sum, Finsupp.sum_add_index' (by simp) (by intro _ a b; push_cast; ring),
    ← balance_eq_sum, ← balance_eq_sum, show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hc,
    show ∑ k ∈ d.support, (d k : ℝ) / k = 0 from hd, add_zero]

private lemma stencilSlope_add (c d : ℕ →₀ ℤ) :
    stencilSlope (c + d) = stencilSlope c + stencilSlope d := by
  simp only [slope_eq_sum]
  exact Finsupp.sum_add_index' (by simp) (by intro _ a b; push_cast; ring)

/-- **Positive Hecke combinations stay in the cone.** -/
theorem IsProducer.add_dilate {c : ℕ →₀ ℤ} {m B j : ℕ} (hP : IsProducer c m B) (hj : 0 < j) (a : ℕ) :
    IsProducer (c + a • dilate j c) m B := by
  have hdil0 : dilate j c 0 = 0 := by
    rw [dilate, Finsupp.mapDomain_notin_range]
    rintro ⟨k, hk, hk'⟩
    have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hP.zero
    simp only at hk'
    rcases Nat.mul_eq_zero.mp hk' with h | h <;> omega
  have hweight : ∀ r, stepWeight (c + a • dilate j c) r =
      stepWeight c r + (a : ℤ) * stepWeight c (r / j) := by
    intro r
    rw [stepWeight_add, ← natCast_zsmul, stepWeight_smul, stepWeight_dilate]
  refine ⟨?_, ?_, fun r => ?_, hP.one_le_m, hP.two_le_B, fun r hr => ?_⟩
  · simp [hP.zero, hdil0]
  · rw [← natCast_zsmul]
    have hbal : IsBalanced ((a : ℤ) • dilate j c) := by
      have hdbal := isBalanced_dilate hj hP.balanced
      rw [IsBalanced, balance_eq_sum, Finsupp.sum_smul_index (by simp)]
      have h : (((dilate j c).sum fun k b => (((a : ℤ) * b : ℤ) : ℝ) / k)) =
          (a : ℝ) * ∑ k ∈ (dilate j c).support, ((dilate j c) k : ℝ) / k := by
        rw [balance_eq_sum, Finsupp.mul_sum]
        refine Finsupp.sum_congr fun k _ => ?_
        push_cast
        ring
      rw [h, show ∑ k ∈ (dilate j c).support, ((dilate j c) k : ℝ) / k = 0 from hdbal, mul_zero]
    exact isBalanced_add hP.balanced hbal
  · rw [hweight]
    have h1 := hP.nonneg r
    have h2 := hP.nonneg (r / j)
    positivity
  · rw [hweight]
    have h1 := hP.window r hr
    have h2 := hP.nonneg (r / j)
    have h3 : (0 : ℤ) ≤ (a : ℤ) * stepWeight c (r / j) := by positivity
    linarith

/-- **No positive amplification.** Adding a positive dilation multiplies the normalized slope by
`1 + a/j`. -/
theorem IsProducer.normSlope_add_dilate {c : ℕ →₀ ℤ} {m B j : ℕ} (hP : IsProducer c m B) (hj : 0 < j)
    (a : ℕ) : normSlope (c + a • dilate j c) m B = normSlope c m B * (1 + (a : ℝ) / j) := by
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hsmul : stencilSlope (a • dilate j c) = (a : ℝ) * stencilSlope (dilate j c) := by
    induction a with
    | zero => simp [stencilSlope]
    | succ a ih =>
      rw [succ_nsmul, stencilSlope_add, ih]
      push_cast
      ring
  rw [normSlope, normSlope, stencilSlope_add, hsmul, stencilSlope_dilate hj hP.zero hP.balanced]
  field_simp

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
