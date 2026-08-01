import GaloisForLFunctions.HTGeometry.PowerTailIntegral
import GaloisForLFunctions.RHTower.SoninScaledPacketHighTail
import GaloisForLFunctions.RHTower.SoninRefTailPolynomialDecay

/-!
# The energy a rescaled packet loses above a band

Substituting the polynomial rate for the majorant into the pointwise bound turns the spectral
density above twice the carrier into a genuine power tail in the frequency, of order twice the rate.
That tail is integrable for every positive order, so the packet's energy outside a band above twice
its carrier is bounded explicitly, and decays in the band radius at every polynomial rate.

This is the last of the aperture reduction's error terms: unlike the others it lives on an unbounded
region, and unlike the others it is controlled by decay rather than by measure or compactness.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- **The density is a power tail above twice the carrier.** -/
theorem exists_soninScaledPacketSpectralDensity_le_powerTail (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m δ w ξ : ℝ, 0 < δ → 0 < w →
      |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 → 2 * w ≤ |ξ| →
        soninScaledPacketSpectralDensity m δ (2 * Real.pi * w) ξ ≤
          (K * δ ^ 2 / δ ^ (2 * N)) * |ξ| ^ (-(2 * N : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_soninRefTailSup_le_div N
  refine ⟨16 * C ^ 2 * 2 ^ (2 * N), by positivity, ?_⟩
  intro m δ w ξ hδ hw hmean hξ
  have hξpos : 0 < |ξ| := by linarith
  have hupos : 0 < δ * |ξ| / 2 := by positivity
  have hSnn : 0 ≤ soninRefTailSup (δ * |ξ| / 2) := soninRefTailSup_nonneg _
  have hS := hC (δ * |ξ| / 2) hupos
  have hdiv : (0 : ℝ) < (δ * |ξ| / 2) ^ N := by positivity
  -- square the majorant bound
  have hSsq : soninRefTailSup (δ * |ξ| / 2) ^ 2 ≤ C ^ 2 / ((δ * |ξ| / 2) ^ N) ^ 2 := by
    have hnn : (0 : ℝ) ≤ C / (δ * |ξ| / 2) ^ N := by positivity
    have := mul_self_le_mul_self hSnn hS
    calc soninRefTailSup (δ * |ξ| / 2) ^ 2
        = soninRefTailSup (δ * |ξ| / 2) * soninRefTailSup (δ * |ξ| / 2) := by ring
      _ ≤ (C / (δ * |ξ| / 2) ^ N) * (C / (δ * |ξ| / 2) ^ N) := this
      _ = C ^ 2 / ((δ * |ξ| / 2) ^ N) ^ 2 := by
          rw [div_mul_div_comm]
          ring
  have hpt := soninScaledPacketSpectralDensity_le_tailSup m δ w ξ hδ hw hmean hξ
  -- rewrite the denominator
  have hden : ((δ * |ξ| / 2) ^ N) ^ 2 = δ ^ (2 * N) * |ξ| ^ (2 * N) / 2 ^ (2 * N) := by
    rw [← pow_mul, div_pow, mul_pow]
    ring_nf
  have hrpow : |ξ| ^ (-(2 * N : ℝ)) = (|ξ| ^ (2 * N))⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg ξ)]
    congr 1
    rw [show (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hxpow : (0 : ℝ) < |ξ| ^ (2 * N) := by positivity
  have hδpow : (0 : ℝ) < δ ^ (2 * N) := by positivity
  rw [hrpow]
  refine le_trans hpt ?_
  rw [hden] at hSsq
  have hstep : 16 * δ ^ 2 * soninRefTailSup (δ * |ξ| / 2) ^ 2 ≤
      16 * δ ^ 2 * (C ^ 2 / (δ ^ (2 * N) * |ξ| ^ (2 * N) / 2 ^ (2 * N))) := by
    have h16 : (0 : ℝ) ≤ 16 * δ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hSsq h16
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **The energy above a band.**  Beyond twice the carrier the packet keeps only a power-tail
amount of energy, at every order. -/
theorem exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m δ w t : ℝ) (hδ : 0 < δ), 0 < w → 2 * w ≤ t →
      |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1 →
        ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ -
            evenFourierCutoff t (soninScaledPacketEven m δ (2 * Real.pi * w) hδ)‖ ^ 2 ≤
          2 * (K * δ ^ 2 / δ ^ (2 * N)) *
            (t ^ (1 - (2 * N : ℝ)) / ((2 * N : ℝ) - 1)) := by
  obtain ⟨K, hK0, hK⟩ := exists_soninScaledPacketSpectralDensity_le_powerTail N
  refine ⟨K, hK0, ?_⟩
  intro m δ w t hδ hw ht hmean
  have htpos : 0 < t := by linarith
  have hp : (1 : ℝ) < (2 * N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  -- the discarded energy as an integral over the closed tail
  have hnull : volume ({(-t), t} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
  have haenot : ∀ᵐ ξ : ℝ, ξ ∉ ({(-t), t} : Set ℝ) := compl_mem_ae_iff.mpr hnull
  have hae : ∀ᵐ ξ : ℝ, {η : ℝ | t < |η|}.indicator
      (soninScaledPacketSpectralDensity m δ (2 * Real.pi * w)) ξ =
      {η : ℝ | t ≤ |η|}.indicator
      (soninScaledPacketSpectralDensity m δ (2 * Real.pi * w)) ξ := by
    refine haenot.mono fun ξ hξ => ?_
    by_cases hlt : t < |ξ|
    · have hmem₁ : ξ ∈ {η : ℝ | t < |η|} := hlt
      have hmem₂ : ξ ∈ {η : ℝ | t ≤ |η|} := le_of_lt hlt
      rw [Set.indicator_of_mem hmem₁, Set.indicator_of_mem hmem₂]
    · have hne : |ξ| ≠ t := by
        intro h
        rcases (abs_eq htpos.le).mp h with h' | h'
        · exact hξ (by simp [h'])
        · exact hξ (by simp [h'])
      have hnotmem : ξ ∉ {η : ℝ | t ≤ |η|} := by
        simp only [Set.mem_setOf_eq]
        intro hle
        exact hne (le_antisymm (not_lt.mp hlt) hle)
      have hnotmem₁ : ξ ∉ {η : ℝ | t < |η|} := hlt
      rw [Set.indicator_of_notMem hnotmem₁, Set.indicator_of_notMem hnotmem]
  rw [norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_eq_density m δ (2 * Real.pi * w) hδ t,
    integral_congr_ae hae,
    integral_indicator (GaloisForLFunctions.HTGeometry.measurableSet_centralTail t)]
  refine GaloisForLFunctions.HTGeometry.setIntegral_le_of_le_powerTail
    (fun ξ => by
      rw [soninScaledPacketSpectralDensity]
      positivity)
    htpos hp fun ξ hξ => hK m δ w ξ hδ hw hmean (by linarith)

end RHTower
