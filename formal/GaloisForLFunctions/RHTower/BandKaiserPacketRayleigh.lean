import GaloisForLFunctions.RHTower.BandKaiserPacketEnergy

/-!
# Exponential Rayleigh bound for finite conditioned Kaiser packets

The exact shifted-tail envelope is combined with the uniform physical-energy lower bound.  The
result already displays the Fuchs clock `exp (-2c)`: after division by physical energy and
`exp (2c)`, only the explicit finite edge envelope remains.
-/

open MeasureTheory Set intervalIntegral FourierTransform
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Sum of the exact single-packet tail envelopes on the conditioned grid. -/
def kaiserGridTailEnvelope {m : ℕ} (c : ℝ) : ℝ :=
  ∑ j : Fin m, (8 + 2 * (kaiserBandRadius c + |kaiserPacketFrequency c j|) *
    kaiserEdgeTransformBoundAt
      (2 * c * |2 * Real.pi * kaiserPacketFrequency c j|) ^ 2)

theorem kaiserGridTailEnvelope_nonneg {m : ℕ} {c : ℝ} (hc : 0 < c) :
    0 ≤ kaiserGridTailEnvelope (m := m) c := by
  apply Finset.sum_nonneg
  intro j _
  have hradius : 0 ≤ kaiserBandRadius c := by
    rw [kaiserBandRadius]
    positivity
  positivity

theorem kaiserPacketAngularFrequency_le_c {m : ℕ} {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ 2 ≤ Real.sqrt c) (j : Fin m) :
    kaiserPacketAngularFrequency c j ≤ c := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hcpos : 0 < c := one_pos.trans_le hc
  have hstep0 : 0 ≤ kaiserPacketAngularStep c :=
    (kaiserPacketAngularStep_pos hcpos).le
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsqrtSq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hsq : ((m : ℝ) * kaiserPacketAngularStep c) ^ 2 ≤ c ^ 2 := by
    rw [mul_pow, kaiserPacketAngularStep_sq hc0]
    calc
      (m : ℝ) ^ 2 * (c * Real.sqrt c) =
          (8 * (m : ℝ) ^ 2) * (c * Real.sqrt c / 8) := by ring
      _ ≤ Real.sqrt c * (c * Real.sqrt c / 8) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = c ^ 2 / 8 := by nlinarith [hsqrtSq]
      _ ≤ c ^ 2 := by nlinarith [sq_nonneg c]
  have hmstep : (m : ℝ) * kaiserPacketAngularStep c ≤ c := by
    rw [← sq_le_sq₀ (mul_nonneg hm0 hstep0) hc0]
    exact hsq
  exact (kaiserPacketAngularFrequency_le_card_mul hc0 j).trans hmstep

theorem abs_two_pi_mul_kaiserPacketFrequency {m : ℕ} {c : ℝ}
    (hc : 0 < c) (j : Fin m) :
    |2 * Real.pi * kaiserPacketFrequency c j| =
      kaiserPacketAngularFrequency c j := by
  have hq0 : 0 ≤ kaiserPacketAngularFrequency c j :=
    (kaiserPacketAngularFrequency_pos hc j).le
  rw [kaiserPacketFrequency]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hpi]
  exact abs_of_nonneg hq0

/-- Exact finite-span tail estimate specialized to the conditioned packet grid. -/
theorem integral_compl_band_norm_sq_fourier_kaiserGridCombination_le {m : ℕ}
    {c : ℝ} (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ 2 ≤ Real.sqrt c)
    (b : Fin m → ℝ) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2) ≤
      (∑ j, b j ^ 2) * kaiserGridTailEnvelope (m := m) c := by
  have hcpos : 0 < c := one_pos.trans_le hc
  have hw : ∀ j : Fin m, |2 * Real.pi * kaiserPacketFrequency c j| ≤ c := by
    intro j
    rw [abs_two_pi_mul_kaiserPacketFrequency hcpos j]
    exact kaiserPacketAngularFrequency_le_c hc hscale j
  exact integral_compl_band_norm_sq_fourier_kaiserCosCombination_general_shift_le
    hcpos (kaiserPacketFrequency c) b hw

/-- The finite conditioned packet span has the correct `exp (-2c)` Rayleigh clock. -/
theorem exp_sq_mul_kaiserGridSpectralTail_le {m : ℕ} (hm : 0 < m) {c : ℝ}
    (hc : 1 ≤ c) (hscale : 8 * (m : ℝ) ^ 2 ≤ Real.sqrt c)
    (hsmall : 32 * (m : ℝ) * Real.exp (-(Real.sqrt c / 2)) ≤ 1)
    (b : Fin m → ℝ) :
    Real.exp c ^ 2 *
        (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          ‖𝓕 (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2) ≤
      128 * (m : ℝ) * c ^ 2 * kaiserGridTailEnvelope (m := m) c *
        (∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2) := by
  let C : ℝ := ∑ j, b j ^ 2
  let S : ℝ := kaiserGridTailEnvelope (m := m) c
  let Q : ℝ := ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
    ‖𝓕 (bandTrunc (kaiserGridCombination c b)) ξ‖ ^ 2
  let E : ℝ := ∫ x in (-1 : ℝ)..1, kaiserGridCombination c b x ^ 2
  have htail : Q ≤ C * S :=
    integral_compl_band_norm_sq_fourier_kaiserGridCombination_le hc hscale b
  have henergy : C * Real.exp c ^ 2 ≤ 128 * (m : ℝ) * c ^ 2 * E :=
    exp_sq_mul_coeffEnergy_le_kaiserGridEnergy hm hc hscale hsmall b
  have hS0 : 0 ≤ S := kaiserGridTailEnvelope_nonneg (one_pos.trans_le hc)
  change Real.exp c ^ 2 * Q ≤ 128 * (m : ℝ) * c ^ 2 * S * E
  calc
    Real.exp c ^ 2 * Q ≤ Real.exp c ^ 2 * (C * S) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg _)
    _ = (C * Real.exp c ^ 2) * S := by ring
    _ ≤ (128 * (m : ℝ) * c ^ 2 * E) * S :=
      mul_le_mul_of_nonneg_right henergy hS0
    _ = 128 * (m : ℝ) * c ^ 2 * S * E := by ring

end GaloisForLFunctions.RHTower

end
