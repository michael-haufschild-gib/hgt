import GaloisForLFunctions.RHTower.HedenmalmCompletedRadialWorkSoninLyapunovBridge

/-!
# Exact Sonin escape cannot be cancelled by a holomorphic scalar gauge

P-G129 identifies the off-critical Sonin aperture escape rate with the absolute centered spectral
width.  Cancelling that escape uniformly on both sides of the critical wall would require scalar
modulus `exp (-c * |x|)` in the transverse coordinate.  This file proves that no scalar gauge
complex-differentiable at the wall can have that modulus when `c > 0`.

Consequently, any source mechanism capable of sewing the two Sonin orientations cannot be a
regular holomorphic scalar normalization.  It must retain vector-valued direction data, carry a
singularity at the wall, or act only on a discrete divisor rather than on a transverse
neighborhood.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Exact scalar modulus required to cancel two-sided aperture escape of rate `c`. -/
def soninEscapeCancellingGaugeModulus (c x : ℝ) : ℝ :=
  Real.exp (-c * |x|)

@[simp]
theorem soninEscapeCancellingGaugeModulus_zero (c : ℝ) :
    soninEscapeCancellingGaugeModulus c 0 = 1 := by
  simp [soninEscapeCancellingGaugeModulus]

/-- Positive-rate escape-cancelling modulus has an unavoidable cusp at the critical wall. -/
theorem not_differentiableAt_soninEscapeCancellingGaugeModulus
    {c : ℝ} (hc : 0 < c) :
    ¬ DifferentiableAt ℝ (soninEscapeCancellingGaugeModulus c) 0 := by
  intro hescape
  have hlog := hescape.log (by simp : soninEscapeCancellingGaugeModulus c 0 ≠ 0)
  have hc0 : (-c : ℝ) ≠ 0 := neg_ne_zero.mpr hc.ne'
  have habs : DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
    have hscaled := hlog.const_mul (-c)⁻¹
    have heq :
        (fun x : ℝ => (-c)⁻¹ * Real.log (soninEscapeCancellingGaugeModulus c x)) =
          (abs : ℝ → ℝ) := by
      funext x
      rw [soninEscapeCancellingGaugeModulus, Real.log_exp]
      field_simp
    rw [heq] at hscaled
    exact hscaled
  exact not_differentiableAt_abs_zero habs

/-- **Analytic cusp no-go.**  A scalar gauge holomorphic at the critical wall cannot cancel exact
positive-rate two-sided Sonin escape.  The prescribed modulus is nonzero at the wall, so the norm
of a differentiable gauge would be differentiable there.  Taking its logarithm would make
`|x|` differentiable at zero, a contradiction. -/
theorem no_holomorphic_exact_sonin_escape_cancelling_gauge
    {c : ℝ} (hc : 0 < c) :
    ¬ ∃ g : ℂ → ℂ,
      DifferentiableAt ℂ g 0 ∧
        ∀ x : ℝ, ‖g (x : ℂ)‖ = soninEscapeCancellingGaugeModulus c x := by
  rintro ⟨g, hg, hmod⟩
  have hgR : DifferentiableAt ℝ (fun x : ℝ => g (x : ℂ)) 0 := by
    exact hg.hasDerivAt.comp_ofReal.differentiableAt
  have hg0 : g 0 ≠ 0 := by
    intro hzero
    have h : (0 : ℝ) = 1 := by
      simpa [hzero] using hmod 0
    norm_num at h
  have hnorm : DifferentiableAt ℝ (fun x : ℝ => ‖g (x : ℂ)‖) 0 :=
    hgR.norm ℂ hg0
  have hescape : DifferentiableAt ℝ (soninEscapeCancellingGaugeModulus c) 0 := by
    apply hnorm.congr_of_eventuallyEq
    filter_upwards with x
    exact (hmod x).symm
  exact not_differentiableAt_soninEscapeCancellingGaugeModulus hc hescape

/-- Geometric aperture towers have strictly positive transverse escape coefficient.  Hence their
exact two-sided scalar cancellation modulus cannot come from a gauge holomorphic at the wall. -/
theorem no_holomorphic_geometric_sonin_tower_escape_cancelling_gauge
    {r : ℝ} {N : ℕ} (hr : 1 < r) (hN : 0 < N) :
    ¬ ∃ g : ℂ → ℂ,
      DifferentiableAt ℂ g 0 ∧
        ∀ x : ℝ,
          ‖g (x : ℂ)‖ =
            soninEscapeCancellingGaugeModulus ((N : ℝ) * Real.log r) x := by
  exact no_holomorphic_exact_sonin_escape_cancelling_gauge
    (mul_pos (Nat.cast_pos.mpr hN) (Real.log_pos hr))

end RHTower
