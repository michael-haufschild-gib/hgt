/-
The transversal two-dimensional small-ball law.

Where a phase map `Φ : ℂ → ℂ` is injective with a non-degenerate real Jacobian — modulus of the
determinant bounded below by `λ > 0` — the level set at scale `t` has area at most `π t² / λ`: the
genuine quadratic (`t²`) anti-concentration.  This is the area formula read as a small-ball bound:
the image of the level set lands inside the disc of radius `t`, so its area is at most `π t²`, and the
`≥ λ` Jacobian expands area by at least `λ`, so the preimage has area at most `π t² / λ`.

Two independent phases whose combined map is transversal (their velocity vectors span `ℝ²`) realise
this `Φ`; the bound is strictly better than any single non-linear phase's `t^{1/n}` floor
(`RouteBSinglePhase`), which is why closing the smooth-packet small-ball needs the mass spread across
multiplicatively independent directions rather than concentrated on one phase.
-/
import Mathlib

open MeasureTheory Metric

namespace RHTower
namespace Sublevel

/-- **The transversal `t²` small-ball law.**  If `Φ : ℂ → ℂ` is injective on a measurable `region`,
differentiable there with derivative `Φ' z`, and its real Jacobian determinant has modulus at least
`λ > 0` throughout, then the level set `{z ∈ region : ‖Φ z‖ ≤ t}` has measure at most `π t² / λ`.
Proof: the image lands in the disc of radius `t` (area `π t²`), and the area formula equates that
image's area with `∫ |det Φ'| ≥ λ · (level-set area)`. -/
theorem transversal_smallball {Φ : ℂ → ℂ} {Φ' : ℂ → (ℂ →L[ℝ] ℂ)} {region : Set ℂ}
    {lam t : ℝ} (hreg : MeasurableSet region) (hΦm : Measurable Φ)
    (hd : ∀ z ∈ region, HasFDerivWithinAt Φ (Φ' z) region z)
    (hinj : Set.InjOn Φ region) (hlam : 0 < lam)
    (hdet : ∀ z ∈ region, lam ≤ |(Φ' z).det|) (ht : 0 ≤ t) :
    volume (region ∩ {z : ℂ | ‖Φ z‖ ≤ t}) ≤ ENNReal.ofReal (Real.pi * t ^ 2 / lam) := by
  classical
  set A : Set ℂ := region ∩ {z : ℂ | ‖Φ z‖ ≤ t} with hA
  have hAsub : A ⊆ region := Set.inter_subset_left
  have hAm : MeasurableSet A := hreg.inter (hΦm.norm measurableSet_Iic)
  have hderivA : ∀ z ∈ A, HasFDerivWithinAt Φ (Φ' z) A z :=
    fun z hz => (hd z (hAsub hz)).mono hAsub
  have hinjA : Set.InjOn Φ A := hinj.mono hAsub
  have harea := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm hderivA hinjA
    (fun _ => (1 : ENNReal))
  simp only [mul_one] at harea
  rw [setLIntegral_one] at harea
  -- the image lands in the closed disc of radius `t`
  have hsub : Φ '' A ⊆ closedBall (0 : ℂ) t := by
    rintro w ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hz.2
  have hballvol : volume (closedBall (0 : ℂ) t) = ENNReal.ofReal (Real.pi * t ^ 2) := by
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow ht,
      show ((NNReal.pi : ENNReal)) = ENNReal.ofReal Real.pi by
        rw [← ENNReal.ofReal_coe_nnreal]; rfl,
      ← ENNReal.ofReal_mul (by positivity), mul_comm]
  -- the Jacobian floor
  have hlb : ∫⁻ _z in A, ENNReal.ofReal lam ≤ ∫⁻ z in A, ENNReal.ofReal |(Φ' z).det| := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hAm] with z hz
    exact ENNReal.ofReal_le_ofReal (hdet z (hAsub hz))
  have hchain : ENNReal.ofReal lam * volume A ≤ ENNReal.ofReal (Real.pi * t ^ 2) :=
    calc ENNReal.ofReal lam * volume A
        = ∫⁻ _z in A, ENNReal.ofReal lam := (setLIntegral_const A _).symm
      _ ≤ ∫⁻ z in A, ENNReal.ofReal |(Φ' z).det| := hlb
      _ = volume (Φ '' A) := harea.symm
      _ ≤ volume (closedBall (0 : ℂ) t) := measure_mono hsub
      _ = ENNReal.ofReal (Real.pi * t ^ 2) := hballvol
  -- cancel the positive factor `ofReal lam`
  have hkey : ENNReal.ofReal lam * volume A
      ≤ ENNReal.ofReal lam * ENNReal.ofReal (Real.pi * t ^ 2 / lam) := by
    rw [← ENNReal.ofReal_mul hlam.le,
      show lam * (Real.pi * t ^ 2 / lam) = Real.pi * t ^ 2 by field_simp]
    exact hchain
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hlam).ne' ENNReal.ofReal_ne_top).mp hkey

end Sublevel
end RHTower
