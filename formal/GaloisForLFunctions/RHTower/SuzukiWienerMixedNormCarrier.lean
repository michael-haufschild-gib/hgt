import Mathlib
import GaloisForLFunctions.HTGeometry.DiscreteL1Convolution

/-!
# The mixed norm of the two-root Wiener carrier

A frequency coefficient family dominated by two translated `ℓ¹` kernels against two `L²` Hardy
amplitudes is `ℓ¹` in `L²`: each coordinate obeys
`‖ĉ_ν‖₂ ≤ K₋(ν) ‖B₋‖₂ + K₊(ν) ‖B₊‖₂` (weighted `L²` triangle bound in `ℝ≥0∞`), and summing the
kernels gives the total `∑_ν ‖ĉ_ν‖₂ ≤ ‖K₋‖₁ ‖B₋‖₂ + ‖K₊‖₁ ‖B₊‖₂`.

Plancherel — mathlib's `L²` Fourier isometry — transports the frequency family to position space
coordinatewise with the same norms, so the position family is absolutely summable in `L²` and its
sum satisfies the same bound: the two-root carrier lies in `ℓ¹_ν(L²_x)`, and evaluation is the
convergent sum in the physical Hilbert space.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

variable {G : Type*}

/-- **The weighted two-term `L²` bound**: an a.e. domination by two scaled amplitudes bounds the
`L²` norm by the scaled `L²` norms. -/
theorem eLpNorm_le_two_kernel {f a b : ℝ → ℂ} {ka kb : ℝ≥0∞}
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hka : ka ≠ ⊤) (hkb : kb ≠ ⊤)
    (hdom : ∀ᵐ ξ ∂volume, ‖f ξ‖ₑ ≤ ka * ‖a ξ‖ₑ + kb * ‖b ξ‖ₑ) :
    eLpNorm f 2 volume ≤ ka * eLpNorm a 2 volume + kb * eLpNorm b 2 volume := by
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  have hmono : (∫⁻ ξ, ‖f ξ‖ₑ ^ (2 : ℝ)) ≤ ∫⁻ ξ, (ka * ‖a ξ‖ₑ + kb * ‖b ξ‖ₑ) ^ (2 : ℝ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hdom] with ξ hξ
    exact ENNReal.rpow_le_rpow hξ (by norm_num)
  refine le_trans (ENNReal.rpow_le_rpow hmono (by norm_num)) ?_
  have hmink := ENNReal.lintegral_Lp_add_le
    (f := fun ξ => ka * ‖a ξ‖ₑ) (g := fun ξ => kb * ‖b ξ‖ₑ)
    (ha.enorm.const_mul ka) (hb.enorm.const_mul kb) (by norm_num : (1 : ℝ) ≤ 2)
  refine le_trans hmink ?_
  have hpull : ∀ (k : ℝ≥0∞) (g : ℝ → ℂ), AEMeasurable (fun ξ => ‖g ξ‖ₑ) volume → k ≠ ⊤ →
      (∫⁻ ξ, (k * ‖g ξ‖ₑ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        = k * (∫⁻ ξ, ‖g ξ‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
    intro k g hg hk
    have h1 : ∀ ξ, (k * ‖g ξ‖ₑ) ^ (2 : ℝ) = k ^ (2 : ℝ) * ‖g ξ‖ₑ ^ (2 : ℝ) := fun ξ =>
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    simp_rw [h1]
    have hktop : k ^ (2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk
    rw [lintegral_const_mul' _ _ hktop,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_mul]
    norm_num
  rw [hpull ka a ha.enorm hka, hpull kb b hb.enorm hkb]

/-- **The `ℓ¹(L²)` mixed-norm bound** — the card's `(21)`: summing the coordinatewise bound over
the lattice pays the kernel masses once. -/
theorem tsum_eLpNorm_le_twoKernel {chat : G → ℝ → ℂ} {Bm Bp : ℝ → ℂ} {Km Kp : G → ℝ≥0∞}
    (hBm : AEStronglyMeasurable Bm volume) (hBp : AEStronglyMeasurable Bp volume)
    (hKm : discreteMass Km ≠ ⊤) (hKp : discreteMass Kp ≠ ⊤)
    (hdom : ∀ ν, ∀ᵐ ξ ∂volume, ‖chat ν ξ‖ₑ ≤ Km ν * ‖Bm ξ‖ₑ + Kp ν * ‖Bp ξ‖ₑ) :
    (∑' ν, eLpNorm (chat ν) 2 volume)
      ≤ discreteMass Km * eLpNorm Bm 2 volume + discreteMass Kp * eLpNorm Bp 2 volume := by
  calc ∑' ν, eLpNorm (chat ν) 2 volume
      ≤ ∑' ν, (Km ν * eLpNorm Bm 2 volume + Kp ν * eLpNorm Bp 2 volume) := by
        refine ENNReal.tsum_le_tsum fun ν => ?_
        exact eLpNorm_le_two_kernel hBm hBp
          (ne_top_of_le_ne_top hKm (le_discreteMass Km ν))
          (ne_top_of_le_ne_top hKp (le_discreteMass Kp ν)) (hdom ν)
    _ = discreteMass Km * eLpNorm Bm 2 volume + discreteMass Kp * eLpNorm Bp 2 volume := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
        rfl

/-- A family of `L²` elements with finite total `eLpNorm` has summable norms. -/
theorem summable_norm_of_tsum_eLpNorm_ne_top {c : G → Lp ℂ 2 (volume : Measure ℝ)}
    (h : (∑' ν, eLpNorm (c ν : ℝ → ℂ) 2 volume) ≠ ⊤) :
    Summable fun ν => ‖c ν‖ := by
  have hnn : ∀ ν, (‖c ν‖₊ : ℝ≥0∞) = eLpNorm (c ν : ℝ → ℂ) 2 volume := fun ν => by
    rw [Lp.nnnorm_def, ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top (c ν))]
  have hs : Summable fun ν => ‖c ν‖₊ := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [hnn] using h
  have := NNReal.summable_coe.mpr hs
  simpa [coe_nnnorm] using this

/-- **The position carrier** — the card's `(22)`–`(24)`: Plancherel transports the frequency
family coordinatewise with the same norms, so the position family is absolutely summable in `L²`
and its sum — the physical evaluation — obeys the same two-kernel bound. -/
theorem suzukiWienerTwoRootCarrier
    {chat : G → Lp ℂ 2 (volume : Measure ℝ)} {Bm Bp : Lp ℂ 2 (volume : Measure ℝ)}
    {Km Kp : G → ℝ≥0∞}
    (hKm : discreteMass Km ≠ ⊤) (hKp : discreteMass Kp ≠ ⊤)
    (hdom : ∀ ν, ∀ᵐ ξ ∂volume, ‖(chat ν : ℝ → ℂ) ξ‖ₑ
      ≤ Km ν * ‖(Bm : ℝ → ℂ) ξ‖ₑ + Kp ν * ‖(Bp : ℝ → ℂ) ξ‖ₑ) :
    Summable (fun ν => (Lp.fourierTransformₗᵢ ℝ ℂ).symm (chat ν))
      ∧ ‖∑' ν, (Lp.fourierTransformₗᵢ ℝ ℂ).symm (chat ν)‖
          ≤ (discreteMass Km * eLpNorm (Bm : ℝ → ℂ) 2 volume
              + discreteMass Kp * eLpNorm (Bp : ℝ → ℂ) 2 volume).toReal := by
  have htot := tsum_eLpNorm_le_twoKernel (Lp.aestronglyMeasurable Bm)
    (Lp.aestronglyMeasurable Bp) hKm hKp hdom
  have hfin : (discreteMass Km * eLpNorm (Bm : ℝ → ℂ) 2 volume
      + discreteMass Kp * eLpNorm (Bp : ℝ → ℂ) 2 volume) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hKm (Lp.eLpNorm_ne_top Bm),
        ENNReal.mul_ne_top hKp (Lp.eLpNorm_ne_top Bp)⟩
  have hne : (∑' ν, eLpNorm ((chat ν : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) 2 volume) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin htot
  have hnorm : Summable fun ν => ‖chat ν‖ := summable_norm_of_tsum_eLpNorm_ne_top hne
  have hnormT : Summable fun ν => ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (chat ν)‖ := by
    simpa [LinearIsometryEquiv.norm_map] using hnorm
  refine ⟨Summable.of_norm hnormT, ?_⟩
  refine le_trans (norm_tsum_le_tsum_norm hnormT) ?_
  have heq : (∑' ν, ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (chat ν)‖) = ∑' ν, ‖chat ν‖ :=
    tsum_congr fun ν => LinearIsometryEquiv.norm_map _ _
  rw [heq]
  have h1 : (∑' ν, ‖chat ν‖)
      = (∑' ν, eLpNorm ((chat ν : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) 2 volume).toReal := by
    rw [ENNReal.tsum_toReal_eq fun ν => Lp.eLpNorm_ne_top (chat ν)]
    exact tsum_congr fun ν => Lp.norm_def (chat ν)
  rw [h1]
  exact ENNReal.toReal_mono hfin htot

end GaloisForLFunctions.RHTower
