import GaloisForLFunctions.RHTower.CCMFiniteExponentialRemainderOrbit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Quantitative Fourier tails of the actual odd remainder orbit

The certified finite-exponential envelope integrates to an inverse-square
Fourier tail. Reflection handles the negative half-line; the exact
Plancherel cutoff identity transfers both tails back to physical L2 norm.
The final theorem applies to every literal normalized remainder iterate,
with no assumed tail regularity of the unknown Riesz response.
-/

open MeasureTheory Set Filter
open scoped FourierTransform
noncomputable section
namespace RHTower

private theorem half_tail_le {g : ℝ → ℂ} {V R : ℝ} (hR : 0 < R)
    (hb : ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ V / (Real.pi * |ξ|)) :
    (∫ ξ in Ioi R, ‖g ξ‖ ^ 2) ≤ V ^ 2 / (Real.pi ^ 2 * R) := by
  have hi : IntegrableOn (fun ξ : ℝ => (V / Real.pi) ^ 2 * ξ ^ (-2 : ℝ)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).const_mul _
  have hcmp : (∫ ξ in Ioi R, ‖g ξ‖ ^ 2) ≤
      ∫ ξ in Ioi R, (V / Real.pi) ^ 2 * ξ ^ (-2 : ℝ) := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun ξ => sq_nonneg _) hi
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioi] with ξ hξ hx
    have hξpos : 0 < ξ := hR.trans hx
    have h := hξ hξpos.ne'
    rw [abs_of_pos hξpos] at h
    have hs : ‖g ξ‖ ^ 2 ≤ (V / (Real.pi * ξ)) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) h
    refine hs.trans_eq ?_
    rw [Real.rpow_neg hξpos.le, Real.rpow_two]
    ring
  refine hcmp.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
  norm_num only
  rw [Real.rpow_neg_one]
  ring

/-- Exact inverse-square integration upgrades the certified Fourier envelope
to a physical L2 truncation bound. -/
theorem CCMFiniteExponentialBudget.fourier_tail_sq_le
    {f : SoninL2} {V R : ℝ} (hf : CCMFiniteExponentialBudget f V) (hR : 0 < R) :
    ‖f - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f‖ ^ 2 ≤
      2 * V ^ 2 / (Real.pi ^ 2 * R) := by
  let g : ℝ → ℂ := (fourierUnitary f : ℝ → ℂ)
  have hb : ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖g ξ‖ ≤ V / (Real.pi * |ξ|) :=
    hf.ae_norm_fourier_le
  have hn : ∀ᵐ ξ : ℝ, ξ ≠ 0 → ‖g (-ξ)‖ ≤ V / (Real.pi * |ξ|) := by
    have ht := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hb
    filter_upwards [ht] with ξ hξ
    intro hξ0
    simpa only [abs_neg] using hξ (neg_ne_zero.mpr hξ0)
  have hp := half_tail_le hR hb
  have hm := half_tail_le hR hn
  rw [integral_comp_neg_Ioi R (fun ξ : ℝ => ‖g ξ‖ ^ 2), integral_Iic_eq_integral_Iio] at hm
  have hi : Integrable (fun ξ : ℝ => ‖g ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hset : (centralInterval R)ᶜ = Iio (-R) ∪ Ioi R := by
    ext ξ
    simp only [centralInterval, mem_compl_iff, mem_Icc, not_and_or,
      not_le, mem_union, mem_Iio, mem_Ioi]
  have hd : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro ξ hξ hξ'
    have h1 : ξ < -R := hξ
    have h2 : R < ξ := hξ'
    linarith
  rw [norm_sq_sub_fourierCutoff_central_eq_tailIntegral,
    integral_indicator (measurableSet_centralInterval R).compl, hset,
    setIntegral_union hd measurableSet_Ioi hi.integrableOn hi.integrableOn]
  calc
    _ ≤ V ^ 2 / (Real.pi ^ 2 * R) + V ^ 2 / (Real.pi ^ 2 * R) := add_le_add hm hp
    _ = _ := by ring

/-- The actual odd source orbit has a quantitative tail at every iteration
and every positive frequency cutoff. -/
theorem ccmNormalizedWeilRemainder_odd_iterate_tail
    (a : SuzukiPositiveAperture) (n : ℕ) {R : ℝ} (hR : 0 < R) :
    let f : SoninL2 := (((ccmNormalizedWeilRemainder a)^[n])
      ((1 / 2 : ℂ) • (ccmPolarApertureVector a (1 / 2) -
        ccmPolarApertureVector a (-1 / 2))) : SoninL2)
    ‖f - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f‖ ^ 2 ≤
      2 * ((2 * (‖ccmArchimedeanRemainderScalar‖ + 46)) ^ n * Real.exp (a.1 / 2)) ^ 2 /
        (Real.pi ^ 2 * R) :=
  (ccmNormalizedWeilRemainder_odd_iterate_budget a n).fourier_tail_sq_le hR

end RHTower
end
