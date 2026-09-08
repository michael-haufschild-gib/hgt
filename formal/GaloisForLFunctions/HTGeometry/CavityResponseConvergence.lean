import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
/-!
# Cavity response geometry and convergent Chebyshev expansion

The sum-of-squares normalization in arXiv:2608.14343, S2, forces the Chebyshev
argument into `[-1,1]`. Its coefficients grow at most linearly. The parameter
`s/(1+|s|)` lies inside the convergence disk for every real `s`, allowing a closed
HasSum theorem with no analytical premises. The proof passes the exact finite
remainder to the limit using absolute summability.
-/

open scoped BigOperators
open Filter Topology
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- Normalized detuning coordinate of the Chebyshev cavity hierarchy. -/
def cavityChebyshevCoordinate (D E : ℝ) : ℝ := -D / Real.sqrt (D ^ 2 + E ^ 2)
/-- The detuning coordinate lies in the Chebyshev oscillatory interval, including the totalized origin. -/
theorem abs_cavityChebyshevCoordinate_le_one (D E : ℝ) :
    |cavityChebyshevCoordinate D E| ≤ 1 := by
  have hle : |D| ≤ Real.sqrt (D ^ 2 + E ^ 2) := by
    calc |D| = Real.sqrt (D ^ 2) := (Real.sqrt_sq_eq_abs D).symm
         _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg E))
  by_cases hz : Real.sqrt (D ^ 2 + E ^ 2) = 0
  · simp [cavityChebyshevCoordinate, hz]
  · rw [cavityChebyshevCoordinate, abs_div, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz))).mpr hle
/-- Real damping coordinate with range the open unit interval `(-1,1)`. -/
def cavityDiskCoordinate (s : ℝ) : ℝ := s / (1 + |s|)
/-- The chosen damping coordinate is strictly inside the convergence disk for every real input. -/
theorem abs_cavityDiskCoordinate_lt_one (s : ℝ) : |cavityDiskCoordinate s| < 1 := by
  rw [cavityDiskCoordinate, abs_div, abs_of_pos (by positivity : 0 < 1 + |s|)]
  exact (div_lt_one (by positivity : 0 < 1 + |s|)).mpr (by linarith)
/-- The physical Lorentzian denominator is the same sum of squares used by the Chebyshev coordinate. -/
theorem cavityLorentzian_denominator_identity (a c p : ℝ) :
    ((1 + p / (a ^ 2 + 1)) ^ 2 + (c - p * a / (a ^ 2 + 1)) ^ 2) * (a ^ 2 + 1) =
      (1 - a * c + p) ^ 2 + (a + c) ^ 2 := by
  have hn : a ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring
/-- Nonnegative population-coupling product gives a nonvanishing physical response denominator. -/
theorem cavityLorentzian_denominator_pos (a c r : ℝ) :
    0 < (1 - a * c + r ^ 2) ^ 2 + (a + c) ^ 2 := by
  have hidentity := cavityLorentzian_denominator_identity a c (r ^ 2)
  have hp : 0 ≤ r ^ 2 / (a ^ 2 + 1) := by positivity
  have hfirst : 0 < (1 + r ^ 2 / (a ^ 2 + 1)) ^ 2 := by positivity
  rw [← hidentity]
  positivity
/-- Uniform linear coefficient bound underlying the paper's all-order coupling estimate. -/
theorem quadraticResponseCoeff_cavity_bound (D E : ℝ) (n : ℕ) :
    |quadraticResponseCoeff (-(2 * cavityChebyshevCoordinate D E)) 1 n| ≤ (n : ℝ) + 1 := by
  let x := cavityChebyshevCoordinate D E
  have hx : |x| ≤ 1 := abs_cavityChebyshevCoordinate_le_one D E
  change |quadraticResponseCoeff (-(2 * x)) 1 n| ≤ (n : ℝ) + 1
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      simp only [quadraticResponseCoeff_one, neg_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2), Nat.cast_one]
      linarith
  | more n h0 _ =>
      have heq : quadraticResponseCoeff (-(2 * x)) 1 (n + 2) =
          2 * (Polynomial.Chebyshev.T ℝ (n + 2)).eval x + quadraticResponseCoeff (-(2 * x)) 1 n := by
        simp only [quadraticResponseCoeff_eq_chebyshev]
        have h := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ (n : ℤ))
        simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Nat.cast_add,
          Nat.cast_ofNat] using h
      rw [heq]
      have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (n + 2 : ℕ) hx
      simp only [Nat.cast_add, Nat.cast_ofNat] at hT
      have hb := abs_add_le (2 * (Polynomial.Chebyshev.T ℝ (n + 2)).eval x)
        (quadraticResponseCoeff (-(2 * x)) 1 n)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)] at hb
      push_cast
      linarith
/-- The damped cavity hierarchy is absolutely summable at every parameterized interior point. -/
theorem summable_quadraticCavityResponse (D E s : ℝ) :
    Summable (fun n => quadraticResponseCoeff (-(2 * cavityChebyshevCoordinate D E)) 1 n *
      cavityDiskCoordinate s ^ n) := by
  let r := cavityDiskCoordinate s
  have hr : ‖(|r| : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs, r] using abs_cavityDiskCoordinate_lt_one s
  have hmajor : Summable (fun n : ℕ => ((n : ℝ) + 1) * |r| ^ n) := by
    simpa only [pow_one, add_mul, one_mul, Pi.add_apply] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
        (summable_geometric_of_norm_lt_one hr)
  apply hmajor.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_right (quadraticResponseCoeff_cavity_bound D E n) (by positivity)
/-- The Chebyshev generating function, proved from the exact finite residual and absolute convergence. -/
theorem hasSum_quadraticCavityResponse (D E s : ℝ) :
    HasSum (fun n => quadraticResponseCoeff (-(2 * cavityChebyshevCoordinate D E)) 1 n *
      cavityDiskCoordinate s ^ n)
      (1 - 2 * cavityChebyshevCoordinate D E * cavityDiskCoordinate s +
        cavityDiskCoordinate s ^ 2)⁻¹ := by
  let x := cavityChebyshevCoordinate D E
  let r := cavityDiskCoordinate s
  let f := fun n => quadraticResponseCoeff (-(2 * x)) 1 n * r ^ n
  have hs : Summable f := summable_quadraticCavityResponse D E s
  have hz := hs.tendsto_atTop_zero
  have hz1 := hz.comp (Filter.tendsto_add_atTop_nat 1)
  have hp := hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hlimit : Tendsto (fun n => (1 - 2 * x * r + r ^ 2) *
      (∑ k ∈ Finset.range (n + 1), f k)) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hc.sub hz1).add (hz.mul_const (r ^ 2))
    simp only [sub_zero, zero_mul, add_zero] at h
    convert h using 1
    funext n
    have hid := quadraticResponseCoeff_finite_remainder (-(2 * x)) 1 r n
    dsimp [f]
    convert hid using 1 <;> ring
  have hid : (1 - 2 * x * r + r ^ 2) * (∑' n, f n) = 1 :=
    tendsto_nhds_unique (hp.const_mul _) hlimit
  have hd : 1 - 2 * x * r + r ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hid
    exact zero_ne_one hid
  have heq : (∑' n, f n) = (1 - 2 * x * r + r ^ 2)⁻¹ := by
    apply (mul_left_cancel₀ hd)
    rw [hid, mul_inv_cancel₀ hd]
  exact heq ▸ hs.hasSum

end
end GaloisForLFunctions.HTGeometry
