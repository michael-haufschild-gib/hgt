import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovIterates

/-!
Quantitative mixing of the critical Gibbs Markov chain derived from arXiv:2609.00025.
The exact harmonic formula yields a uniform entrywise bound and convergence of
all fixed complex profiles to their mean, without assumptions on the input profile.
-/
namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped Matrix

noncomputable section

/-- An explicit real formula for each transition entry, viewed in the complex field. -/
theorem egbFixedChargeACriticalMarkovMatrix_pow_entry
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    (egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j =
      (((1 + 2 * (2 / 3 : ℝ) ^ (m + 1) *
        Real.cos (2 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j)) +
        2 * (1 / 6 : ℝ) ^ (m + 1) *
        Real.cos (4 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j))) /
          (2 : ℝ) ^ (n + 3) : ℝ) : ℂ) := by
  apply Complex.ext_iff.mpr
  constructor
  · simp only [Complex.ofReal_re]
    have h := egbFixedChargeACriticalMarkovMatrix_pow_real n m i j
    exact (div_eq_of_eq_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
      (h.symm.trans (mul_comm _ _))).symm
  · simp only [egbFixedChargeACriticalMarkovMatrix_pow_im_zero, Complex.ofReal_im]

/-- A two-rate bound holds uniformly over every pair of states and every grid size. -/
theorem egbFixedChargeACriticalMarkovMatrix_mixing_bound
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    |(2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re - 1| ≤
      2 * (2 / 3 : ℝ) ^ (m + 1) + 2 * (1 / 6 : ℝ) ^ (m + 1) := by
  rw [egbFixedChargeACriticalMarkovMatrix_pow_real]
  let a := 2 * (2 / 3 : ℝ) ^ (m + 1)
  let b := 2 * (1 / 6 : ℝ) ^ (m + 1)
  let x := 2 * (egbFixedChargeAFourierGrid (n + 3) i - egbFixedChargeAFourierGrid (n + 3) j)
  let y := 4 * (egbFixedChargeAFourierGrid (n + 3) i - egbFixedChargeAFourierGrid (n + 3) j)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  change |1 + a * Real.cos x + b * Real.cos y - 1| ≤ a + b
  rw [show 1 + a * Real.cos x + b * Real.cos y - 1 = a * Real.cos x + b * Real.cos y by ring]
  have h₁ : |a * Real.cos x| ≤ a := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [Real.abs_cos_le_one x]
  have h₂ : |b * Real.cos y| ≤ b := by
    rw [abs_mul, abs_of_nonneg hb]
    nlinarith [Real.abs_cos_le_one y]
  exact (abs_add_le _ _).trans (add_le_add h₁ h₂)

/-- The slow nonconstant Fourier rate controls the complete transition matrix. -/
theorem egbFixedChargeACriticalMarkovMatrix_geometric_bound
    (n m : ℕ) (i j : Fin (2 ^ (n + 3))) :
    |(2 : ℝ) ^ (n + 3) * ((egbFixedChargeACriticalMarkovMatrix n ^ (m + 1)) i j).re - 1| ≤
      4 * (2 / 3 : ℝ) ^ (m + 1) := by
  have h := egbFixedChargeACriticalMarkovMatrix_mixing_bound n m i j
  have hp : (1 / 6 : ℝ) ^ (m + 1) ≤ (2 / 3 : ℝ) ^ (m + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  linarith

/-- All matrix powers converge to the uniform averaging operator. -/
theorem egbFixedChargeACriticalMarkovMatrix_mixing_limit (n : ℕ) :
    Tendsto (fun m : ℕ => egbFixedChargeACriticalMarkovMatrix n ^ m) atTop
      (𝓝 (Matrix.of fun _ _ : Fin (2 ^ (n + 3)) => (((2 : ℝ) ^ (n + 3))⁻¹ : ℂ))) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have ha : Tendsto (fun m : ℕ => (2 / 3 : ℝ) ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hb : Tendsto (fun m : ℕ => (1 / 6 : ℝ) ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hs := (((ha.const_mul 2).mul_const
    (Real.cos (2 * (egbFixedChargeAFourierGrid (n + 3) i -
      egbFixedChargeAFourierGrid (n + 3) j)))).add
      ((hb.const_mul 2).mul_const
        (Real.cos (4 * (egbFixedChargeAFourierGrid (n + 3) i -
          egbFixedChargeAFourierGrid (n + 3) j))))).const_add 1
  have hq := hs.div_const ((2 : ℝ) ^ (n + 3))
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  simpa only [Function.comp_def, egbFixedChargeACriticalMarkovMatrix_pow_entry,
    Matrix.of_apply, mul_zero, zero_mul, zero_add, add_zero, one_div, add_assoc,
    Complex.ofReal_inv, Complex.ofReal_pow] using hc

/-- Every fixed complex source profile converges to its conserved mean. -/
theorem egbFixedChargeACriticalMarkovMatrix_profile_limit
    (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℂ) :
    Tendsto (fun m : ℕ => (egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ f) atTop
      (𝓝 (fun _ : Fin (2 ^ (n + 3)) =>
        (((2 : ℝ) ^ (n + 3))⁻¹ : ℂ) * ∑ j : Fin (2 ^ (n + 3)), f j)) := by
  have hc : Continuous (fun M : Matrix (Fin (2 ^ (n + 3))) (Fin (2 ^ (n + 3))) ℂ => M *ᵥ f) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have h := hc.continuousAt.tendsto.comp (egbFixedChargeACriticalMarkovMatrix_mixing_limit n)
  have hm : (Matrix.of fun _ _ : Fin (2 ^ (n + 3)) =>
      (((2 : ℝ) ^ (n + 3))⁻¹ : ℂ)) *ᵥ f =
      fun _ : Fin (2 ^ (n + 3)) =>
        (((2 : ℝ) ^ (n + 3))⁻¹ : ℂ) * ∑ j : Fin (2 ^ (n + 3)), f j := by
    funext i
    change (∑ j, (((2 : ℝ) ^ (n + 3))⁻¹ : ℂ) * f j) = _
    rw [Finset.mul_sum]
  rw [hm] at h
  simpa only [Function.comp_def] using h

end

end GaloisForLFunctions.HTGeometry
