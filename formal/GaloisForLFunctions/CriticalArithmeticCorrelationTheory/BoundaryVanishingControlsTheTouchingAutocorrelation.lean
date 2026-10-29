import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# Endpoint decay of the autocorrelation

A Lipschitz bump supported on an interval vanishes at both endpoints. Near
the last possible overlap, its two endpoint distances multiply. This gives
quadratic decay of the autocorrelation, which pays an inverse-square kernel
without a cost depending on the remaining gap between the supports.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis

private theorem endpoint_values_eq_zero {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0) : g 0 = 0 ∧ g w = 0 := by
  have hz : IsClosed {u : ℝ | g u = 0} := isClosed_eq hg continuous_const
  have hl : Iio (0 : ℝ) ⊆ {u : ℝ | g u = 0} := by
    intro u hu
    exact hsupp u (fun h => (not_le_of_gt hu) h.1)
  have hr : Ioi w ⊆ {u : ℝ | g u = 0} := by
    intro u hu
    exact hsupp u (fun h => (not_le_of_gt hu) h.2)
  have hcl := closure_minimal hl hz
  have hcr := closure_minimal hr hz
  rw [closure_Iio] at hcl
  rw [closure_Ioi] at hcr
  exact ⟨hcl (by simp), hcr (by simp)⟩

/-- Two endpoint distances force quadratic decay at the last possible overlap. -/
theorem abs_bumpAutocorr_le_endpoint_square {g : ℝ → ℝ} {w L z : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, u ∉ Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hLip : ∀ x y, |g y - g x| ≤ L * |y - x|) :
    |bumpAutocorr g z| ≤ (L ^ 2 * w / 4) * (w - |z|) ^ 2 := by
  obtain ⟨hg0, hgw⟩ := endpoint_values_eq_zero hg hsupp
  have hleft (u : ℝ) (hu : 0 ≤ u) : |g u| ≤ L * u := by
    simpa only [hg0, sub_zero, abs_of_nonneg hu] using hLip 0 u
  have hright (u : ℝ) (hu : u ≤ w) : |g u| ≤ L * (w - u) := by
    simpa only [hgw, sub_zero, abs_of_nonpos (sub_nonpos.mpr hu), neg_sub] using hLip w u
  have hproduct (u : ℝ) : |g u * g (u + z)| ≤ L ^ 2 * (w - |z|) ^ 2 / 4 := by
    by_cases hu : u ∈ Icc 0 w
    · by_cases huz : u + z ∈ Icc 0 w
      · by_cases hz0 : 0 ≤ z
        · have hq : u * (w - u - z) ≤ (w - z) ^ 2 / 4 := by
            nlinarith only [sq_nonneg (2 * u - w + z)]
          calc
            |g u * g (u + z)| = |g u| * |g (u + z)| := abs_mul _ _
            _ ≤ (L * u) * (L * (w - (u + z))) :=
              mul_le_mul (hleft u hu.1) (hright (u + z) huz.2)
                (abs_nonneg _) (mul_nonneg hL hu.1)
            _ = L ^ 2 * (u * (w - u - z)) := by ring
            _ ≤ L ^ 2 * ((w - z) ^ 2 / 4) := mul_le_mul_of_nonneg_left hq (sq_nonneg L)
            _ = _ := by rw [abs_of_nonneg hz0]; ring
        · have hz0' : z ≤ 0 := le_of_not_ge hz0
          have hq : (w - u) * (u + z) ≤ (w + z) ^ 2 / 4 := by
            nlinarith only [sq_nonneg (2 * u - w + z)]
          calc
            |g u * g (u + z)| = |g u| * |g (u + z)| := abs_mul _ _
            _ ≤ (L * (w - u)) * (L * (u + z)) :=
              mul_le_mul (hright u hu.2) (hleft (u + z) huz.1)
                (abs_nonneg _) (mul_nonneg hL (sub_nonneg.mpr hu.2))
            _ = L ^ 2 * ((w - u) * (u + z)) := by ring
            _ ≤ L ^ 2 * ((w + z) ^ 2 / 4) := mul_le_mul_of_nonneg_left hq (sq_nonneg L)
            _ = _ := by rw [abs_of_nonpos hz0']; ring
      · rw [hsupp (u + z) huz, mul_zero, abs_zero]
        positivity
    · rw [hsupp u hu, zero_mul, abs_zero]
      positivity
  have heq : bumpAutocorr g z = ∫ u in Icc 0 w, g u * g (u + z) := by
    unfold bumpAutocorr
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro u hu
    rw [hsupp u hu, zero_mul]
  have hi : IntegrableOn (fun u => |g u * g (u + z)|) (Icc 0 w) := by
    have hc : Continuous fun u => |g u * g (u + z)| := by fun_prop
    exact hc.integrableOn_Icc
  rw [heq]
  calc
    |∫ u in Icc 0 w, g u * g (u + z)| ≤ ∫ u in Icc 0 w, |g u * g (u + z)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ in Icc (0 : ℝ) w, L ^ 2 * (w - |z|) ^ 2 / 4 :=
      setIntegral_mono_on hi continuous_const.integrableOn_Icc measurableSet_Icc
        (fun u _ => hproduct u)
    _ = _ := by simp [hw]; ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_bumpAutocorr_le_endpoint_square
