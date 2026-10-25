import GaloisForLFunctions.BiarithmeticGeometry.PrimeFivePaymentCriterion
import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk

/-!
# Isometric real coefficient lifts at the critical radius

Multiplication of the coefficient at `5^r` by `sqrt(5)^r` cancels its Wiener
weight exactly. The existing real-kernel embedding therefore preserves the
coefficient `ell1` norm and distances, while actual payment reads partial sums.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The critical coefficient growth cancels the exact Wiener weight at every five-power. -/
theorem fiveCritical_weight_cancel (r : ℕ) :
    Real.sqrt 5 ^ r * ((5 ^ r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h := abs_localFactorInverse_mul_rpow (by norm_num : Nat.Prime 5) (Real.sqrt 5) r
  rw [localFactorInverse_pow (by omega : 1 < 5), abs_of_pos (pow_pos hs r),
    abs_of_pos hs, Nat.cast_ofNat, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5),
    ← Real.sqrt_eq_rpow, mul_inv_cancel₀ hs.ne', one_pow] at h
  exact h

/-- The normalized tower preserves total absolute coefficient mass, including nonsummable rows. -/
theorem tsum_abs_fiveCriticalKernelLift (g : ℕ → ℝ) :
    (∑' n : ℕ, |fiveCriticalKernelLift g n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) =
      ∑' r : ℕ, |g r| := by
  have hsupp : Function.support
      (fun n : ℕ => |fiveCriticalKernelLift g n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) ⊆
      Set.range (fun r : ℕ => 5 ^ r) := by
    intro n hn
    by_contra hnot
    apply hn
    change |fiveCriticalKernelLift g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 0
    rw [fiveCriticalKernelLift, fiveTowerKernelLift_off_support _ _ hnot, abs_zero, zero_mul]
  rw [← (Nat.pow_right_injective (by omega : 2 ≤ 5)).tsum_eq hsupp]
  apply tsum_congr
  intro r
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [fiveCriticalKernelLift, fiveTowerKernelLift_pow, abs_mul, abs_of_pos (pow_pos hs r)]
  calc
    _ = (Real.sqrt 5 ^ r * ((5 ^ r : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) * |g r| := by ring
    _ = _ := by rw [fiveCritical_weight_cancel, one_mul]

/-- Real `ell1` coefficients as an actual critical Wiener kernel. -/
def fiveCriticalWienerLift (g : ℕ → ℝ) (hg : Summable fun r => |g r|) :
    WienerAlgebraAt (1 / 2) :=
  toWiener (fiveCriticalKernelLift g) ((criticalWiener_fiveCriticalKernelLift_iff g).mpr hg)

theorem fiveCriticalWienerLift_toFn (g : ℕ → ℝ) (hg : Summable fun r => |g r|) (n : ℕ) :
    (fiveCriticalWienerLift g hg).toFn n = (fiveCriticalKernelLift g n : ℂ) := by
  change (if n = 0 then 0 else (fiveCriticalKernelLift g n : ℂ)) = _
  by_cases hn : n = 0
  · subst n
    simp only [fiveCriticalKernelLift, fiveTowerKernelLift_zero, Complex.ofReal_zero, ite_self]
  · exact if_neg hn

/-- The actual Wiener norm is exactly the normalized coefficient `ell1` norm. -/
theorem norm_fiveCriticalWienerLift (g : ℕ → ℝ) (hg : Summable fun r => |g r|) :
    ‖fiveCriticalWienerLift g hg‖ = ∑' r, |g r| := by
  change (∑' n, ‖LSeries.term (⇑(realFn (fiveCriticalKernelLift g)))
    ((1 / 2 : ℝ) : ℂ) n‖) = _
  simp_rw [norm_term_realFn]
  exact tsum_abs_fiveCriticalKernelLift g

private theorem fiveCriticalKernelLift_sub (g h : ℕ → ℝ) :
    fiveCriticalKernelLift (fun r => g r - h r) =
      fun n => fiveCriticalKernelLift g n - fiveCriticalKernelLift h n := by
  funext n
  simp only [fiveCriticalKernelLift, fiveTowerKernelLift]
  split_ifs <;> ring

/-- Normalized lifting preserves every coefficient distance exactly. -/
theorem norm_fiveCriticalWienerLift_sub (g h : ℕ → ℝ)
    (hg : Summable fun r => |g r|) (hh : Summable fun r => |h r|) :
    ‖fiveCriticalWienerLift g hg - fiveCriticalWienerLift h hh‖ =
      ∑' r, |g r - h r| := by
  have he : (fiveCriticalWienerLift g hg - fiveCriticalWienerLift h hh).toFn =
      realFn (fiveCriticalKernelLift (fun r => g r - h r)) := by
    ext n
    change (fiveCriticalWienerLift g hg).toFn n - (fiveCriticalWienerLift h hh).toFn n = _
    rw [fiveCriticalWienerLift_toFn, fiveCriticalWienerLift_toFn]
    by_cases hn : n = 0
    · subst n
      simp only [fiveCriticalKernelLift, fiveTowerKernelLift_zero,
        Complex.ofReal_zero, sub_self]
      rfl
    · rw [realFn_apply hn, fiveCriticalKernelLift_sub, Complex.ofReal_sub]
  rw [WienerAlgebraAt.norm_def, wienerNorm, he]
  simp_rw [norm_term_realFn]
  exact tsum_abs_fiveCriticalKernelLift (fun r => g r - h r)

private theorem rePart_fiveCriticalWienerLift (g : ℕ → ℝ)
    (hg : Summable fun r => |g r|) :
    rePart (fiveCriticalWienerLift g hg) = fiveCriticalKernelLift g := by
  funext n
  simp only [rePart, fiveCriticalWienerLift_toFn, Complex.ofReal_re]

private theorem imPart_fiveCriticalWienerLift (g : ℕ → ℝ)
    (hg : Summable fun r => |g r|) :
    imPart (fiveCriticalWienerLift g hg) = fun _ => 0 := by
  funext n
  simp only [imPart, fiveCriticalWienerLift_toFn, Complex.ofReal_im]

/-- In the actual complex Wiener algebra, a real lifted kernel pays exactly its partial-sum energy. -/
theorem mem_paidIdeal_critical_fiveCriticalWienerLift_iff (g : ℕ → ℝ)
    (hg : Summable fun r => |g r|) :
    fiveCriticalWienerLift g hg ∈ paidIdeal (localFactorInverse 5 (Real.sqrt 5))
      (summable_abs_fiveTower_div (Real.sqrt 5) (by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
        nlinarith only [h, Real.sqrt_nonneg (5 : ℝ)])) ↔
      Summable (fun M : ℕ => (∑ r ∈ range (M + 1), g r) ^ 2) := by
  rw [mem_paidIdeal, rePart_fiveCriticalWienerLift, imPart_fiveCriticalWienerLift,
    dirichletConv_zero_left]
  simp only [receiverBounded_zero, and_true]
  exact receiverBounded_critical_fiveTower_iff_partialSums g hg

end GaloisForLFunctions.BiarithmeticGeometry
