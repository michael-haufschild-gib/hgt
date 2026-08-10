import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Inverting an asymptotically unimodular comparison

If a family of nonzero complex numbers is asymptotically equal to a family of unimodular ones,
then so are their reciprocals.  The point is that the comparison forces the norms to approach one,
so the denominator in

`a⁻¹ - b⁻¹ = (b - a)/(a b)`

is eventually bounded below, and the numerator carries the convergence.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- Reciprocals inherit an asymptotic comparison with a unimodular family. -/
theorem tendsto_inv_sub_inv_of_tendsto_sub_zero {ι : Type*} {l : Filter ι} {a b : ι → ℂ}
    (ha : ∀ i, a i ≠ 0) (hbnorm : ∀ i, ‖b i‖ = 1)
    (h : Tendsto (fun i => a i - b i) l (nhds 0)) :
    Tendsto (fun i => (a i)⁻¹ - (b i)⁻¹) l (nhds 0) := by
  have hnorm : Tendsto (fun i => ‖a i - b i‖) l (nhds 0) := by
    simpa using h.norm
  have hev : ∀ᶠ i in l, (1 : ℝ) / 2 ≤ ‖a i‖ := by
    have hlt : ∀ᶠ i in l, ‖a i - b i‖ < 1 / 2 := by
      have := hnorm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
      simpa using this
    filter_upwards [hlt] with i hi
    have hstep : ‖b i‖ - ‖a i‖ ≤ ‖b i - a i‖ := norm_sub_norm_le _ _
    rw [hbnorm i, norm_sub_rev] at hstep
    linarith
  have hdom : Tendsto (fun i => 2 * ‖a i - b i‖) l (nhds 0) := by
    simpa using hnorm.const_mul (2 : ℝ)
  refine squeeze_zero_norm' ?_ hdom
  filter_upwards [hev] with i hi
  have hbne : b i ≠ 0 := by
    intro hb
    have hnb := hbnorm i
    rw [hb] at hnb
    simp at hnb
  have hanorm : (0 : ℝ) < ‖a i‖ := by linarith
  have hsplit : (a i)⁻¹ - (b i)⁻¹ = (b i - a i) / (a i * b i) := by
    field_simp [ha i, hbne]
  rw [hsplit, norm_div, norm_mul, hbnorm i, mul_one, norm_sub_rev,
    div_le_iff₀ hanorm]
  nlinarith [norm_nonneg (a i - b i)]

/-- Exponentials of asymptotically equal purely imaginary exponents are asymptotically equal.
The unimodularity of the reference exponential is what keeps the error from being amplified. -/
theorem tendsto_exp_sub_exp_zero_of_tendsto_sub_zero {ι : Type*} {l : Filter ι} {u v : ι → ℂ}
    (hv : ∀ i, (v i).re = 0) (h : Tendsto (fun i => u i - v i) l (nhds 0)) :
    Tendsto (fun i => Complex.exp (u i) - Complex.exp (v i)) l (nhds 0) := by
  have hone : Tendsto (fun i => Complex.exp (u i - v i) - 1) l (nhds 0) := by
    have hcomp := (Complex.continuous_exp.tendsto 0).comp h
    simp only [Function.comp_def, Complex.exp_zero] at hcomp
    have hconst : Tendsto (fun _ : ι => (1 : ℂ)) l (nhds 1) := tendsto_const_nhds
    simpa using hcomp.sub hconst
  have hbounded : IsBoundedUnder (· ≤ ·) l (fun i => ‖Complex.exp (v i)‖) := by
    refine ⟨1, ?_⟩
    change ∀ᶠ i in l, ‖Complex.exp (v i)‖ ≤ 1
    filter_upwards with i
    rw [Complex.norm_exp, hv i]
    simp
  have hzero := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hone hbounded
  refine hzero.congr ?_
  intro i
  simp only [Pi.mul_apply, smul_eq_mul]
  rw [sub_mul, one_mul, ← Complex.exp_add, sub_add_cancel]

end GaloisForLFunctions
