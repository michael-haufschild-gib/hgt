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

/-- Balance is additive. -/
theorem isBalanced_add {c d : ℕ →₀ ℤ} (hc : IsBalanced c) (hd : IsBalanced d) :
    IsBalanced (c + d) := by
  rw [IsBalanced, balance_eq_sum, Finsupp.sum_add_index' (by simp) (by intro _ a b; push_cast; ring),
    ← balance_eq_sum, ← balance_eq_sum, show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hc,
    show ∑ k ∈ d.support, (d k : ℝ) / k = 0 from hd, add_zero]

/-- The slope is additive. -/
theorem stencilSlope_add (c d : ℕ →₀ ℤ) :
    stencilSlope (c + d) = stencilSlope c + stencilSlope d := by
  simp only [slope_eq_sum]
  exact Finsupp.sum_add_index' (by simp) (by intro _ a b; push_cast; ring)

/-- Scaling keeps balance. -/
theorem isBalanced_nsmul {c : ℕ →₀ ℤ} (hc : IsBalanced c) (a : ℕ) : IsBalanced (a • c) := by
  induction a with
  | zero =>
    rw [zero_nsmul]
    simp [IsBalanced]
  | succ a ih =>
    rw [succ_nsmul]
    exact isBalanced_add ih hc

/-- The slope scales. -/
theorem stencilSlope_nsmul (c : ℕ →₀ ℤ) (a : ℕ) : stencilSlope (a • c) = (a : ℝ) * stencilSlope c := by
  induction a with
  | zero =>
    rw [zero_nsmul]
    simp [stencilSlope]
  | succ a ih =>
    rw [succ_nsmul, stencilSlope_add, ih]
    push_cast
    ring

/-- The multiplicity scales. -/
theorem stepWeight_nsmul (c : ℕ →₀ ℤ) (a r : ℕ) :
    stepWeight (a • c) r = (a : ℤ) * stepWeight c r := by
  rw [← natCast_zsmul, stepWeight_smul]

/-- A nonnegative balanced stencil may be added to a producer: the window is unchanged. -/
theorem IsProducer.add_of_nonneg {c d : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (hd0 : d 0 = 0)
    (hdbal : IsBalanced d) (hdnn : ∀ r, 0 ≤ stepWeight d r) : IsProducer (c + d) m B := by
  refine ⟨by simp [hP.zero, hd0], isBalanced_add hP.balanced hdbal, fun r => ?_, hP.one_le_m,
    hP.two_le_B, fun r hr => ?_⟩
  · rw [stepWeight_add]
    have h1 := hP.nonneg r
    have h2 := hdnn r
    linarith
  · rw [stepWeight_add]
    have h1 := hP.window r hr
    have h2 := hdnn r
    linarith

/-- A positive multiple of a producer is a producer, with the multiplicity scaled. -/
theorem IsProducer.nsmul {c : ℕ →₀ ℤ} {m B N : ℕ} (hP : IsProducer c m B) (hN : 0 < N) :
    IsProducer (N • c) (N * m) B := by
  have hN' : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  refine ⟨by simp [hP.zero], isBalanced_nsmul hP.balanced N, fun r => ?_,
    Nat.mul_pos hN hP.one_le_m, hP.two_le_B, fun r hr => ?_⟩
  · rw [stepWeight_nsmul]
    exact mul_nonneg hN' (hP.nonneg r)
  · rw [stepWeight_nsmul]
    push_cast
    exact mul_le_mul_of_nonneg_left (hP.window r hr) hN'

/-- Dilation sends a stencil vanishing at `0` to one vanishing at `0`. -/
theorem dilate_zero {j : ℕ} (hj : 0 < j) {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) : dilate j c 0 = 0 := by
  have hinj : Function.Injective (j * ·) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hj h
  have h := Finsupp.mapDomain_apply hinj c 0
  simpa [dilate, hc0] using h

/-- A nonnegative stencil stays nonnegative under dilation and scaling. -/
theorem stepWeight_nsmul_dilate_nonneg {c : ℕ →₀ ℤ} (hc : ∀ r, 0 ≤ stepWeight c r) (j a r : ℕ) :
    0 ≤ stepWeight (a • dilate j c) r := by
  rw [stepWeight_nsmul, stepWeight_dilate]
  exact mul_nonneg (Int.natCast_nonneg a) (hc _)

/-- **Positive Hecke combinations stay in the cone.** -/
theorem IsProducer.add_dilate {c : ℕ →₀ ℤ} {m B j : ℕ} (hP : IsProducer c m B) (hj : 0 < j) (a : ℕ) :
    IsProducer (c + a • dilate j c) m B :=
  hP.add_of_nonneg (by simp [dilate_zero hj hP.zero])
    (isBalanced_nsmul (isBalanced_dilate hj hP.balanced) a)
    (stepWeight_nsmul_dilate_nonneg hP.nonneg j a)

/-- **No positive amplification.** Adding a positive dilation multiplies the normalized slope by
`1 + a/j`. -/
theorem IsProducer.normSlope_add_dilate {c : ℕ →₀ ℤ} {m B j : ℕ} (hP : IsProducer c m B) (hj : 0 < j)
    (a : ℕ) : normSlope (c + a • dilate j c) m B = normSlope c m B * (1 + (a : ℝ) / j) := by
  have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  rw [normSlope, normSlope, stencilSlope_add, stencilSlope_nsmul,
    stencilSlope_dilate hj hP.zero hP.balanced]
  field_simp

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
