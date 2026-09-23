import GaloisForLFunctions.RHTower.SoninPacketChannelHeightBound

/-!
# The outer term depends only on the half-width times the cut radius

Written out, the geometric term of the height-uniform bound carries the packet's half-width to a
negative power and the cut radius to the same negative power.  They therefore combine: the whole term
is a constant of the shell divided by the `(2N-2)`-nd power of the single product `δ` times the cut
radius.

That is the form the schedule reads.  Under the tied scale the half-width times any radius
proportional to the carrier is a fixed multiple of the schedule constant, so the outer term is fixed
while the cut and the scale both move.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- The half-width and the cut radius enter the outer term to the same negative order, so they
combine into one product. -/
theorem soninChannelOuterTerm_eq {a r δ : ℝ} (ha : 0 < a) (hr : 1 < r) (hδ : 0 < δ)
    {N : ℕ} (hN : 2 ≤ N) (Kc : ℕ) (K : ℝ) :
    4 * (2 * (K * δ ^ (2 : ℕ) / δ ^ (2 * N)) / ((2 * N : ℝ) - 1)) / a ^ (2 * N - 2) *
        ((r ^ (2 * N - 2))⁻¹ ^ Kc * (1 - (r ^ (2 * N - 2))⁻¹)⁻¹) =
      8 * K / (((2 * N : ℝ) - 1) * (1 - (r ^ (2 * N - 2))⁻¹)) *
        ((δ * logShellRadius a r Kc) ^ (2 * N - 2))⁻¹ := by
  have hp2 : 2 * N - 2 + 2 = 2 * N := by omega
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hδp : δ ^ (2 * N) = δ ^ (2 * N - 2) * δ ^ (2 : ℕ) := by rw [← pow_add, hp2]
  have hcomb : (δ * logShellRadius a r Kc) ^ (2 * N - 2) =
      δ ^ (2 * N - 2) * (a ^ (2 * N - 2) * (r ^ (2 * N - 2)) ^ Kc) := by
    rw [mul_pow, logShellRadius_pow]
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * N : ℝ) - 1 := by linarith
  have hrp1 : (1 : ℝ) < r ^ (2 * N - 2) := one_lt_pow₀ hr (by omega)
  have hgap : (0 : ℝ) < 1 - (r ^ (2 * N - 2))⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hrp1
    linarith
  have hapos : (0 : ℝ) < a ^ (2 * N - 2) := pow_pos ha (2 * N - 2)
  have hrpos : (0 : ℝ) < r ^ (2 * N - 2) := pow_pos (lt_trans zero_lt_one hr) (2 * N - 2)
  have hrkpos : (0 : ℝ) < (r ^ (2 * N - 2)) ^ Kc := pow_pos hrpos Kc
  have hdpos : (0 : ℝ) < δ ^ (2 * N - 2) := pow_pos hδ (2 * N - 2)
  rw [hδp, hcomb, inv_pow]
  field_simp
  ring

/-- **The frequency-side channel on a rescaled packet, in the schedule's own variables.**  The bound
is the largest layer logarithm below the cut against the packet's mass, plus a shell constant over
the `(2N-2)`-nd power of the half-width times the cut radius.  Neither term mentions the tower's
height. -/
theorem exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_combined
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a r : ℝ), 0 < a → 1 < r → ∀ (n Kc : ℕ) (m δ w M : ℝ) (hδ : 0 < δ),
      0 < w → |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 →
      1 ≤ logShellRadius a r Kc → 2 * w ≤ logShellRadius a r Kc →
      (∀ k, k < Kc → |Real.log (logShellRadius a r k)| ≤ M) →
        ‖evenFourierLogShellChannel a r n
            (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ≤
          Real.sqrt (M ^ (2 : ℕ) * ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ (2 : ℕ) +
            8 * K / (((2 * N : ℝ) - 1) * (1 - (r ^ (2 * N - 2))⁻¹)) *
              ((δ * logShellRadius a r Kc) ^ (2 * N - 2))⁻¹) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le N hN
  refine ⟨K, hK0, ?_⟩
  intro a r ha hr n Kc m δ w M hδ hw hmean hone h2w hM
  have h := hK a r ha hr n Kc m δ w M hδ hw hmean hone h2w hM
  rwa [soninChannelOuterTerm_eq ha hr hδ hN Kc K] at h

end RHTower

