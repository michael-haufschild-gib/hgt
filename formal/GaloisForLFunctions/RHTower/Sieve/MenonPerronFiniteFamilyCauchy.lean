import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWindowRelevantCellSelection
import GaloisForLFunctions.HTGeometry.WeightedCauchySchwarz
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# Finite-family weighted Cauchy for Menon's Perron integral

The square is taken after the exact Perron integral and before any vertical shift is selected.
This keeps every cofactor polynomial at its original ordinate.  The resulting right-hand side is
an integral of fixed-shift product mean squares, to which Montgomery estimates apply directly.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory
open GaloisForLFunctions.HTGeometry

/-- Weighted Cauchy--Schwarz summed over a finite family.  Every family member retains the same
kernel mass, while its own weighted energy remains inside the finite sum. -/
theorem sum_norm_integral_mul_sq_le
    {α : Type*} (S : Finset α) (F : α → ℝ → ℂ) (K : ℝ → ℂ)
    (hF : ∀ r ∈ S, AEStronglyMeasurable (F r) volume)
    (hK : AEStronglyMeasurable K volume)
    (hKint : Integrable fun y : ℝ => ‖K y‖)
    (hE : ∀ r ∈ S, Integrable fun y : ℝ => ‖F r y‖ ^ 2 * ‖K y‖) :
    ∑ r ∈ S, ‖∫ y : ℝ, F r y * K y‖ ^ 2 ≤
      (∫ y : ℝ, ‖K y‖) *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ := by
  have hKnonneg : 0 ≤ ∫ y : ℝ, ‖K y‖ := integral_nonneg fun _ => norm_nonneg _
  have hpoint : ∀ r ∈ S,
      ‖∫ y : ℝ, F r y * K y‖ ^ 2 ≤
        (∫ y : ℝ, ‖K y‖) *
          (∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖) := by
    intro r hr
    have hcs := norm_integral_mul_mul_le_sqrt_mul_sqrt
      (g₁ := F r) (g₂ := fun _ : ℝ => (1 : ℂ)) (W := K)
      (hF r hr) aestronglyMeasurable_const hK (hE r hr) (by simpa using hKint)
    simp only [mul_one, norm_one, one_pow, one_mul] at hcs
    have hsquare := pow_le_pow_left₀ (norm_nonneg (∫ y : ℝ, F r y * K y)) hcs 2
    have hEnonneg : 0 ≤ ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ :=
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt hEnonneg, Real.sq_sqrt hKnonneg] at hsquare
    nlinarith
  calc
    ∑ r ∈ S, ‖∫ y : ℝ, F r y * K y‖ ^ 2
        ≤ ∑ r ∈ S, (∫ y : ℝ, ‖K y‖) *
            (∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖) :=
      Finset.sum_le_sum fun r hr => hpoint r hr
    _ = (∫ y : ℝ, ‖K y‖) *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ := by
      rw [Finset.mul_sum]

/-- A sharp half-width Mellin difference has integrable modulus. -/
theorem integrable_norm_menonSharpIntervalMellinKernel
    {a b sigma C : ℝ} (hsigma : 0 < sigma) (hC : 0 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel a b sigma y‖ ≤ C * (1 + y ^ 2)⁻¹) :
    Integrable fun y : ℝ => ‖menonSharpIntervalMellinKernel a b sigma y‖ := by
  have hmajor : Integrable fun y : ℝ => C * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hmajor
    (continuous_menonSharpIntervalMellinKernel hsigma).norm.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hkernel y

/-- Finite-family Perron Cauchy bound with the sharp kernel replaced by its Lorentzian
majorant.  Fixed shifts remain under the final integral. -/
theorem sum_norm_integral_menonSharpIntervalMellinKernel_sq_le
    {α : Type*} (S : Finset α) (F : α → ℝ → ℂ)
    {a b sigma C : ℝ} (hsigma : 0 < sigma) (hC : 0 ≤ C)
    (hF : ∀ r ∈ S, AEStronglyMeasurable (F r) volume)
    (hkernel : ∀ y : ℝ,
      ‖menonSharpIntervalMellinKernel a b sigma y‖ ≤ C * (1 + y ^ 2)⁻¹)
    (hE : ∀ r ∈ S,
      Integrable fun y : ℝ => ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) :
    ∑ r ∈ S,
        ‖∫ y : ℝ, F r y * menonSharpIntervalMellinKernel a b sigma y‖ ^ 2 ≤
      C ^ 2 * Real.pi *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
  let K : ℝ → ℂ := menonSharpIntervalMellinKernel a b sigma
  have hKm : AEStronglyMeasurable K volume :=
    (continuous_menonSharpIntervalMellinKernel hsigma).aestronglyMeasurable
  have hKint : Integrable fun y : ℝ => ‖K y‖ :=
    integrable_norm_menonSharpIntervalMellinKernel hsigma hC hkernel
  have hEr : ∀ r ∈ S, Integrable fun y : ℝ => ‖F r y‖ ^ 2 * ‖K y‖ := by
    intro r hr
    have hmajor : Integrable fun y : ℝ => C *
        (‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) := (hE r hr).const_mul C
    refine Integrable.mono' hmajor ((hF r hr).norm.pow 2 |>.mul hKm.norm) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ‖F r y‖ ^ 2 * ‖K y‖)]
    have hm := mul_le_mul_of_nonneg_left (hkernel y) (sq_nonneg ‖F r y‖)
    calc
      ‖F r y‖ ^ 2 * ‖K y‖ ≤ ‖F r y‖ ^ 2 * (C * (1 + y ^ 2)⁻¹) := hm
      _ = C * (‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by ring
  have hbase := sum_norm_integral_mul_sq_le S F K hF hKm hKint hEr
  have hKmass : (∫ y : ℝ, ‖K y‖) ≤ C * Real.pi := by
    have hmajor : Integrable fun y : ℝ => C * (1 + y ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul C
    have hmono := integral_mono hKint hmajor hkernel
    rw [integral_const_mul, show (∫ y : ℝ, (1 + y ^ 2)⁻¹) = Real.pi by
      simpa using (integral_inv_sq_add_sq (a := (1 : ℝ)) (by norm_num))] at hmono
    exact hmono
  have henergy :
      ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ ≤
        C * ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
    calc
      ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ ≤
          ∑ r ∈ S, C * ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hmono := integral_mono (hEr r hr) ((hE r hr).const_mul C) (fun y => by
          have hm := mul_le_mul_of_nonneg_left (hkernel y) (sq_nonneg ‖F r y‖)
          calc
            ‖F r y‖ ^ 2 * ‖K y‖ ≤
                ‖F r y‖ ^ 2 * (C * (1 + y ^ 2)⁻¹) := hm
            _ = C * (‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by ring)
        simpa only [integral_const_mul] using hmono
      _ = C * ∑ r ∈ S, ∫ y : ℝ,
          ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by rw [Finset.mul_sum]
  have hmass0 : 0 ≤ ∫ y : ℝ, ‖K y‖ := integral_nonneg fun _ => norm_nonneg _
  have henergy0 : 0 ≤ ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ := by
    positivity
  calc
    _ ≤ (∫ y : ℝ, ‖K y‖) *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ := hbase
    _ ≤ (C * Real.pi) *
        (C * ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) :=
      mul_le_mul hKmass henergy henergy0 (mul_nonneg hC Real.pi_pos.le)
    _ = C ^ 2 * Real.pi *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by ring

end RHTower.Sieve

