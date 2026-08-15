import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# A finite window costs only its own length

On a bounded window the whole integral of a density is controlled by its energy through
Cauchy–Schwarz, `(∫_S G)² ≤ |S| ∫_S G²`, so a profile bounded pointwise by `M ∫_S G` has squared
mass at most `M²|S|² ∫_S G²`.  Applied to a variation-of-constants integral over a bounded frequency
window, the propagator contributes only its uniform bound and the window only its length: no decay
is needed, and the cost is a single power of the window length in the norm.

Stated in the extended norm, so no integrability or measurability hypothesis is placed on the
profile — only on the density that dominates it.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Cauchy–Schwarz on a finite window.** -/
theorem sq_lintegral_le_measure_mul {S : Set ℝ} {G : ℝ → ℝ≥0∞}
    (hG : AEMeasurable G (volume.restrict S)) :
    (∫⁻ t in S, G t) ^ 2 ≤ volume S * ∫⁻ t in S, G t ^ 2 := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hone : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) (volume.restrict S) := aemeasurable_const
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hconj hone hG
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow] at hCS
  have hsq : ((∫⁻ _ in S, (1 : ℝ≥0∞)) ^ ((1 : ℝ) / 2)
      * (∫⁻ t in S, G t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2
      = (∫⁻ _ in S, (1 : ℝ≥0∞)) * ∫⁻ t in S, G t ^ (2 : ℝ) := by
    rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ _ in S, (1 : ℝ≥0∞)) ^ ((1 : ℝ) / 2)) 2,
      ← ENNReal.rpow_natCast ((∫⁻ t in S, G t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) 2,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  have hpow : ∀ t : ℝ, G t ^ (2 : ℝ) = G t ^ 2 := by
    intro t
    rw [← ENNReal.rpow_natCast (G t) 2]
    norm_num
  calc (∫⁻ t in S, G t) ^ 2
      ≤ ((∫⁻ _ in S, (1 : ℝ≥0∞)) ^ ((1 : ℝ) / 2)
          * (∫⁻ t in S, G t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' hCS 2
    _ = (∫⁻ _ in S, (1 : ℝ≥0∞)) * ∫⁻ t in S, G t ^ (2 : ℝ) := hsq
    _ = volume S * ∫⁻ t in S, G t ^ 2 := by
        rw [setLIntegral_one]
        congr 1
        exact lintegral_congr fun t => hpow t

variable {Y : Type*} [NormedAddCommGroup Y]

/-- **The finite-window estimate.**  A profile dominated on a window by `M` times the total mass of
a density has squared mass at most `M²|S|²` times the density's energy. -/
theorem lintegral_sq_windowAverage_le {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    {F : ℝ → Y} {G : ℝ → ℝ≥0∞} (hG : AEMeasurable G (volume.restrict (Ioo a b)))
    (hF : ∀ x ∈ Ioo a b, ‖F x‖ₑ ≤ ENNReal.ofReal M * ∫⁻ t in Ioo a b, G t) :
    (∫⁻ x in Ioo a b, ‖F x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2 * (b - a) ^ 2) * ∫⁻ t in Ioo a b, G t ^ 2 := by
  have hvol : volume (Ioo a b) = ENNReal.ofReal (b - a) := Real.volume_Ioo
  have hCS := sq_lintegral_le_measure_mul (S := Ioo a b) hG
  rw [hvol] at hCS
  have hpt : ∀ x ∈ Ioo a b, ‖F x‖ₑ ^ 2
      ≤ ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal (b - a) * ∫⁻ t in Ioo a b, G t ^ 2) := by
    intro x hx
    calc ‖F x‖ₑ ^ 2 ≤ (ENNReal.ofReal M * ∫⁻ t in Ioo a b, G t) ^ 2 :=
          pow_le_pow_left' (hF x hx) 2
      _ = ENNReal.ofReal (M ^ 2) * (∫⁻ t in Ioo a b, G t) ^ 2 := by
          rw [mul_pow, ← ENNReal.ofReal_pow hM]
      _ ≤ ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal (b - a) * ∫⁻ t in Ioo a b, G t ^ 2) :=
          mul_le_mul' le_rfl hCS
  calc (∫⁻ x in Ioo a b, ‖F x‖ₑ ^ 2)
      ≤ ∫⁻ _ in Ioo a b,
          ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal (b - a) * ∫⁻ t in Ioo a b, G t ^ 2) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ = ENNReal.ofReal (b - a)
          * (ENNReal.ofReal (M ^ 2) * (ENNReal.ofReal (b - a) * ∫⁻ t in Ioo a b, G t ^ 2)) := by
        rw [setLIntegral_const, hvol]
        ring
    _ = ENNReal.ofReal (M ^ 2 * (b - a) ^ 2) * ∫⁻ t in Ioo a b, G t ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ M ^ 2),
          ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ b - a)]
        ring

end GaloisForLFunctions.HTGeometry
