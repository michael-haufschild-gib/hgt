import GaloisForLFunctions.RHTower.SuzukiCarlemanCommutatorKernel
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The low-frequency port and the weighted Carleman target

The low-pass part of a cutoff graph relation is a regular port: its frequency content sits in a
compact band, so every derivative of the profile is bounded by the band radius to the power of the
order times the `L¹` mass of the band content.  Nothing singular is discarded when it is retained,
and the high-pass and low-pass parts reconstruct the mode exactly.

What remains after the cutoff is the weighted Carleman target: the derivative of the cutoff defect,
weighted by `e^{σL}`, is square integrable on the ray for some `σ > 1/2`.  This is a genuine strip
condition — it descends to every smaller weight.
-/

open Set MeasureTheory Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ## The bandlimited port -/

/-- Frequency content confined to a band of radius `R`. -/
def BandLimited (g : ℝ → ℂ) (R : ℝ) : Prop := ∀ x : ℝ, R < |x| → g x = 0

theorem integrable_pow_smul_of_bandLimited {g : ℝ → ℂ} {R : ℝ}
    (hg : Integrable g) (hband : BandLimited g R) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • g x) := by
  refine Integrable.mono' (g := fun x : ℝ => R ^ n * ‖g x‖) (hg.norm.const_mul (R ^ n))
    ((measurable_id.pow_const n).aestronglyMeasurable.smul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : R < |x|
  · rw [hband x hx]
    simp
  · have hle : |x| ≤ R := le_of_not_gt hx
    rw [norm_smul, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg x) hle n) (norm_nonneg _)

/-- **`(24)`: every derivative of a bandlimited port is bounded.**  The bound is the band radius
to the power of the order, times the `L¹` mass of the frequency content. -/
theorem norm_iteratedDeriv_fourier_le_of_bandLimited {g : ℝ → ℂ} {R : ℝ}
    (hg : Integrable g) (hband : BandLimited g R) (n : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv n (𝓕 g) ξ‖ ≤ (2 * Real.pi * R) ^ n * ∫ x : ℝ, ‖g x‖ := by
  have hint : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (fun x : ℝ => x ^ k • g x) :=
    fun k _ => integrable_pow_smul_of_bandLimited hg hband k
  have hderiv := Real.iteratedDeriv_fourier (f := g) (N := (⊤ : ℕ∞)) (n := n) hint le_top
  rw [hderiv]
  have hbound : ‖𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * x) ^ n • g x) ξ‖
      ≤ ∫ x : ℝ, ‖(-2 * Real.pi * Complex.I * (x:ℂ)) ^ n • g x‖ := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show ‖Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)
        • ((-2 * (Real.pi : ℂ) * Complex.I * (v:ℂ)) ^ n • g v)‖
      = ‖(-2 * (Real.pi : ℂ) * Complex.I * (v:ℂ)) ^ n • g v‖
    rw [norm_smul, Complex.norm_exp]
    have hre : ((((-2 * Real.pi * v * ξ : ℝ)) : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
  refine le_trans hbound ?_
  have hpoint : ∀ x : ℝ, ‖(-2 * Real.pi * Complex.I * (x:ℂ)) ^ n • g x‖
      ≤ (2 * Real.pi * R) ^ n * ‖g x‖ := by
    intro x
    rw [norm_smul, norm_pow]
    have hnorm : ‖(-2 * (Real.pi : ℂ) * Complex.I * (x:ℂ))‖ = 2 * Real.pi * |x| := by
      rw [show (-2 * (Real.pi : ℂ) * Complex.I * (x:ℂ))
          = -(2 * (Real.pi : ℂ) * Complex.I * (x:ℂ)) by ring, norm_neg]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    by_cases hx : R < |x|
    · rw [hband x hx]
      simp
    · have hle : |x| ≤ R := le_of_not_gt hx
      rw [hnorm]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ n) (norm_nonneg _)
      have := Real.pi_pos
      nlinarith
  have hmono : (∫ x : ℝ, ‖(-2 * Real.pi * Complex.I * (x:ℂ)) ^ n • g x‖)
      ≤ ∫ x : ℝ, (2 * Real.pi * R) ^ n * ‖g x‖ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (hg.norm.const_mul _) (Filter.Eventually.of_forall hpoint)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-! ## Exact reconstruction from the two ports -/

/-- **`(21)`: the high-pass carrier and the low-pass port reconstruct the mode.** -/
theorem highPass_add_lowPass (χ û e : ℝ → ℂ) (ξ : ℝ) (hcarrier : e ξ = χ ξ * û ξ) :
    e ξ + (1 - χ ξ) * û ξ = û ξ := by
  rw [hcarrier]
  ring

/-! ## The weighted Carleman target -/

/-- **`(12)`: the weighted trace-zero target.**  The derivative of the cutoff defect profile,
weighted by `e^{σL}`, is square integrable on the physical ray. -/
def WeightedCarlemanTarget (D : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun L => (Real.exp (σ * L) * D L) ^ (2 : ℕ)) (Ioi (0:ℝ)) volume

/-- The target is a strip condition: it descends to every smaller weight on the ray. -/
theorem weightedCarlemanTarget_mono {D : ℝ → ℝ} {σ τ : ℝ} (hτ : τ ≤ σ)
    (hmeas : Measurable D) (h : WeightedCarlemanTarget D σ) : WeightedCarlemanTarget D τ := by
  have hmeas2 : Measurable fun L : ℝ => (Real.exp (τ * L) * D L) ^ (2 : ℕ) := by
    have hbase : Measurable fun L : ℝ => Real.exp (τ * L) * D L :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hmeas
    exact hbase.pow_const 2
  refine Integrable.mono' h hmeas2.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hL0 : (0:ℝ) < L := hL
  have hexp : Real.exp (τ * L) ≤ Real.exp (σ * L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hτ hL0.le
  have hsq : (Real.exp (τ * L) * D L) ^ (2 : ℕ) ≤ (Real.exp (σ * L) * D L) ^ (2 : ℕ) := by
    have h1 : |Real.exp (τ * L) * D L| ≤ |Real.exp (σ * L) * D L| := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    have h2 := sq_le_sq' (neg_abs_le _) (le_abs_self (Real.exp (τ * L) * D L))
    nlinarith [abs_nonneg (Real.exp (τ * L) * D L), abs_nonneg (Real.exp (σ * L) * D L),
      sq_abs (Real.exp (τ * L) * D L), sq_abs (Real.exp (σ * L) * D L)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq

end

end RHTower
