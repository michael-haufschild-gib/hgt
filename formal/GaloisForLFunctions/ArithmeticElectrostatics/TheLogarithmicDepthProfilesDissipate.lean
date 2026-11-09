import GaloisForLFunctions.ArithmeticElectrostatics.ConjugatePairsDissipateLogarithmicDepth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic profiles of elapsed depth

The profiles `log(A+u^r)−log A`, with `A>0` and `r>0`, vanish at zero.
Their logarithmic height derivative factors into two nonnegative increasing
ratios. They therefore dissipate complete conjugate-pair interactions.
The time derivative along a zero branch exposes the self-conjugate heat credit.
-/

open Filter Topology Set

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

/-- A smooth approximation, after scaling, to a threshold in logarithmic depth. -/
def elapsedLogDepthProfile (r A u : ℝ) : ℝ := Real.log (A + u ^ r) - Real.log A

/-- Vertical derivative of the logarithmic profile at elapsed depth `y²+c`. -/
def elapsedLogDepthWeight (r A c y : ℝ) : ℝ :=
  elapsedDepthWeight r c y / (A + (y ^ 2 + c) ^ r)

theorem elapsedLogDepthProfile_zero {r : ℝ} (hr : 0 < r) (A : ℝ) :
    elapsedLogDepthProfile r A 0 = 0 := by
  simp only [elapsedLogDepthProfile, Real.zero_rpow hr.ne', add_zero, sub_self]

theorem elapsedLogDepthProfile_nonneg {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) (r : ℝ) :
    0 ≤ elapsedLogDepthProfile r A u := by
  apply sub_nonneg.mpr
  exact Real.log_le_log hA (le_add_of_nonneg_right (Real.rpow_nonneg hu r))

theorem continuous_elapsedLogDepthProfile_clamped {r A : ℝ} (hr : 0 ≤ r) (hA : 0 < A) :
    Continuous (fun u : ℝ => elapsedLogDepthProfile r A (max u 0)) := by
  have hp : Continuous (fun u : ℝ => (max u 0) ^ r) :=
    (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr hr)
  exact ((continuous_const.add hp).log (fun u =>
    (add_pos_of_pos_of_nonneg hA (Real.rpow_nonneg (le_max_right u 0) r)).ne')).sub
      continuous_const

private theorem logarithmic_elapsedLogDepthWeight {r A c y : ℝ}
    (hc : 0 ≤ c) (hy : 0 < y) :
    y * elapsedLogDepthWeight r A c y =
      2 * r * (y ^ 2 / (y ^ 2 + c)) *
        ((y ^ 2 + c) ^ r / (A + (y ^ 2 + c) ^ r)) := by
  have hbase : 0 < y ^ 2 + c := add_pos_of_pos_of_nonneg (sq_pos_of_pos hy) hc
  rw [elapsedLogDepthWeight, elapsedDepthWeight, Real.rpow_sub hbase, Real.rpow_one]
  ring

/-- The two increasing ratios give exactly the conjugate-pair admissibility criterion. -/
theorem elapsedLogDepthWeight_admissible {r A c : ℝ}
    (hr : 0 ≤ r) (hA : 0 < A) (hc : 0 ≤ c) :
    (∀ y, 0 < y → 0 ≤ y * elapsedLogDepthWeight r A c y) ∧
      MonotoneOn (fun y => y * elapsedLogDepthWeight r A c y) (Ioi 0) := by
  have hbase (y : ℝ) (hy : 0 < y) : 0 < y ^ 2 + c :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hy) hc
  constructor
  · intro y hy
    rw [logarithmic_elapsedLogDepthWeight hc hy]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg zero_le_two hr) (div_nonneg (sq_nonneg _) (hbase y hy).le))
      (div_nonneg (Real.rpow_nonneg (hbase y hy).le r)
        (add_nonneg hA.le (Real.rpow_nonneg (hbase y hy).le r)))
  · intro a ha b hb hab
    change a * elapsedLogDepthWeight r A c a ≤ b * elapsedLogDepthWeight r A c b
    rw [logarithmic_elapsedLogDepthWeight hc ha, logarithmic_elapsedLogDepthWeight hc hb]
    have hs : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha.le hb.le).mpr hab
    have hu := hbase a ha
    have hv := hbase b hb
    have hratio : a ^ 2 / (a ^ 2 + c) ≤ b ^ 2 / (b ^ 2 + c) := by
      rw [div_le_div_iff₀ hu hv]
      nlinarith only [mul_nonneg hc (sub_nonneg.mpr hs)]
    have hp := Real.rpow_le_rpow hu.le (add_le_add hs le_rfl) hr
    have hdena : 0 < A + (a ^ 2 + c) ^ r :=
      add_pos_of_pos_of_nonneg hA (Real.rpow_nonneg hu.le r)
    have hdenb : 0 < A + (b ^ 2 + c) ^ r :=
      add_pos_of_pos_of_nonneg hA (Real.rpow_nonneg hv.le r)
    have hratio' : (a ^ 2 + c) ^ r / (A + (a ^ 2 + c) ^ r) ≤
        (b ^ 2 + c) ^ r / (A + (b ^ 2 + c) ^ r) := by
      rw [div_le_div_iff₀ hdena hdenb]
      nlinarith only [mul_nonneg hA.le (sub_nonneg.mpr hp)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hratio (mul_nonneg zero_le_two hr)) hratio'
      (div_nonneg (Real.rpow_nonneg hu.le r) hdena.le)
      (mul_nonneg (mul_nonneg zero_le_two hr) (div_nonneg (sq_nonneg _) hv.le))

/-- Every logarithmic profile dissipates the interaction of distinct conjugate pairs. -/
theorem elapsedLogDepth_conjugatePairWork_nonneg {r A c a b d : ℝ}
    (hr : 0 ≤ r) (hA : 0 < A) (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d ^ 2 + (a - b) ^ 2) :
    0 ≤ conjugatePairWork (elapsedLogDepthWeight r A c a)
      (elapsedLogDepthWeight r A c b) a b d :=
  conjugatePairWork_nonneg (elapsedLogDepthWeight_admissible hr hA hc).1
    (elapsedLogDepthWeight_admissible hr hA hc).2 ha hb hd

/-- The chain rule separates elapsed time from the zero's vertical velocity. -/
theorem elapsedLogDepth_hasDerivWithinAt {y : ℝ → ℝ} {v t r A : ℝ} {s : Set ℝ}
    (hy : HasDerivWithinAt y v s t) (ht : 0 < t) (hA : 0 < A) :
    HasDerivWithinAt (fun u => elapsedLogDepthProfile r A (y u ^ 2 + 2 * u))
      (2 * r * (y t ^ 2 + 2 * t) ^ (r - 1) / (A + (y t ^ 2 + 2 * t) ^ r) +
        elapsedLogDepthWeight r A (2 * t) (y t) * v) s t := by
  have hbase : 0 < y t ^ 2 + 2 * t :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (by norm_num) ht)
  have hd := ((hy.pow 2).add ((hasDerivAt_id t).const_mul 2).hasDerivWithinAt).rpow_const
    (Or.inl hbase.ne') (p := r)
  have hden : A + (y t ^ 2 + 2 * t) ^ r ≠ 0 :=
    (add_pos_of_pos_of_nonneg hA (Real.rpow_nonneg hbase.le r)).ne'
  have hl := ((hd.const_add A).log hden).sub_const (Real.log A)
  apply hl.congr_deriv
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one]
  unfold elapsedLogDepthWeight elapsedDepthWeight
  ring

#print axioms elapsedLogDepthWeight_admissible
#print axioms elapsedLogDepth_conjugatePairWork_nonneg
#print axioms elapsedLogDepth_hasDerivWithinAt

end
end GaloisForLFunctions.ArithmeticElectrostatics
