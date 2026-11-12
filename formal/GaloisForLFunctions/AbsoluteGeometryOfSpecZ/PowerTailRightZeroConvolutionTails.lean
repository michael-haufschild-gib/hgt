import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRightZeroCutoffs
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroConvolutionModes
import GaloisForLFunctions.RHTower.ShortWindowNoGo

/-!
# Harmonic convolution pays the complete exterior zero mass

At the power boundary, normalization cancels the retained zero exponent
and leaves the harmonic divisor weight. The full omitted convolution is
therefore bounded by the reciprocal exterior mass times `2(1+log N)`.
-/

noncomputable section

open Complex Finset
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- The normalized harmonic convolution of the complete shifted trace. -/
def powerTailRightZeroConvolution (a σ : ℝ) (N : ℕ) : ℂ :=
  (((N : ℝ) ^ (2 * a - 1) : ℝ) : ℂ) *
    ∑ m ∈ Icc 1 N, (powerTailWeight (2 * a) m : ℂ) *
      rightShiftedZeroTrace σ a a ((N : ℝ) / m)

/-- The same convolution after retaining a finite core of zero copies. -/
def powerTailFiniteRightZeroConvolution (a σ : ℝ) (N : ℕ) (F : Finset XiZeroCopy) : ℂ :=
  (((N : ℝ) ^ (2 * a - 1) : ℝ) : ℂ) *
    ∑ m ∈ Icc 1 N, (powerTailWeight (2 * a) m : ℂ) *
      ∑ q ∈ F, rightShiftedZeroTerm σ a a ((N : ℝ) / m) q

/-- The power boundary leaves exactly the harmonic divisor weight. -/
theorem normalized_powerTailWeight_mul_boundaryPower_eq (a : ℝ)
    {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    (N : ℝ) ^ (2 * a - 1) * powerTailWeight (2 * a) m *
      ((N : ℝ) / m) ^ (1 - 2 * a) = 1 / (m : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  rw [powerTailWeight, Real.div_rpow hNp.le hmp.le]
  calc
    _ = ((N : ℝ) ^ (2 * a - 1) * (N : ℝ) ^ (1 - 2 * a)) *
        ((m : ℝ) ^ (-(2 * a)) / (m : ℝ) ^ (1 - 2 * a)) := by ring
    _ = (m : ℝ) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hNp, ← Real.rpow_sub hmp,
        show 2 * a - 1 + (1 - 2 * a) = 0 by ring,
        show -(2 * a) - (1 - 2 * a) = -(1 : ℝ) by ring,
        Real.rpow_zero, one_mul]
    _ = _ := by rw [Real.rpow_neg hmp.le, Real.rpow_one, one_div]

/-- The entire exterior convolution is paid by a logarithmic multiple
of its reciprocal mass; no individual zero separation is required. -/
theorem norm_powerTailRightZeroConvolution_sub_finite_le {a σ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a)
    {N : ℕ} (hN : 1 ≤ N) (F : Finset XiZeroCopy) :
    ‖powerTailRightZeroConvolution a σ N - powerTailFiniteRightZeroConvolution a σ N F‖ ≤
      2 * (1 + Real.log N) * ∑' q, rightSubstripTailWeight σ F q := by
  let T := ∑' q, rightSubstripTailWeight σ F q
  have hT : 0 ≤ T := tsum_nonneg (rightSubstripTailWeight_nonneg σ F)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 ≤ (N : ℝ) ^ (2 * a - 1) := Real.rpow_nonneg hNp.le _
  have he : powerTailRightZeroConvolution a σ N - powerTailFiniteRightZeroConvolution a σ N F =
      (((N : ℝ) ^ (2 * a - 1) : ℝ) : ℂ) *
        ∑ m ∈ Icc 1 N, (powerTailWeight (2 * a) m : ℂ) *
          (rightShiftedZeroTrace σ a a ((N : ℝ) / m) -
            ∑ q ∈ F, rightShiftedZeroTerm σ a a ((N : ℝ) / m) q) := by
    rw [powerTailRightZeroConvolution, powerTailFiniteRightZeroConvolution,
      ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    exact (mul_sub _ _ _).symm
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale]
  calc
    _ ≤ (N : ℝ) ^ (2 * a - 1) * ∑ m ∈ Icc 1 N,
        ‖(powerTailWeight (2 * a) m : ℂ) *
          (rightShiftedZeroTrace σ a a ((N : ℝ) / m) -
            ∑ q ∈ F, rightShiftedZeroTerm σ a a ((N : ℝ) / m) q)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hscale
    _ ≤ ∑ m ∈ Icc 1 N, 2 * T * (1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hm1 := (Finset.mem_Icc.mp hm).1
      have hmp : (0 : ℝ) < m := by exact_mod_cast hm1
      have hmN : (m : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      have hx : 1 ≤ (N : ℝ) / m := (le_div_iff₀ hmp).mpr (by simpa only [one_mul] using hmN)
      have hw : 0 ≤ powerTailWeight (2 * a) m := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hb := norm_rightShiftedZeroTrace_sub_sum_le hσ ha ha1 hx hβ F
      rw [show (1 - a) - a = 1 - 2 * a by ring] at hb
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        _ ≤ (N : ℝ) ^ (2 * a - 1) *
            (powerTailWeight (2 * a) m * (2 * ((N : ℝ) / m) ^ (1 - 2 * a) * T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hw) hscale
        _ = 2 * T * ((N : ℝ) ^ (2 * a - 1) * powerTailWeight (2 * a) m *
            ((N : ℝ) / m) ^ (1 - 2 * a)) := by ring
        _ = _ := by rw [normalized_powerTailWeight_mul_boundaryPower_eq a hN hm1]
    _ = 2 * T * ∑ m ∈ Icc 1 N, 1 / (m : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * T * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left (harmonic_Icc_le_one_add_log N hN) (by positivity)
    _ = _ := by ring

/-- A retained right-substrip core is exactly the sum of its individual
finite convolution modes. -/
theorem powerTailFiniteRightZeroConvolution_eq_sum_modes (a σ : ℝ) (N : ℕ)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, σ ≤ (q.1 : ℂ).re) :
    powerTailFiniteRightZeroConvolution a σ N F = ∑ q ∈ F, powerTailZeroConvolutionMode a N q := by
  classical
  simp only [powerTailFiniteRightZeroConvolution, powerTailZeroConvolutionMode]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [rightShiftedZeroTerm, if_pos (hF q hq)]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
