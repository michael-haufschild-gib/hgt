import GaloisForLFunctions.RHTower.ZetaChiDualRetainedAllocation
import GaloisForLFunctions.RHTower.PrimeWindowHarmonicMultiplicity

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The physical free-block first mean pays only logarithmic cofactor cost,
with every selected integer retained and all thresholds uniform in `H`. -/
theorem eventually_zetaChi_dual_free_block_mean_harmonic_log_le
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ H : ℕ,
      1 ≤ H → H ^ 2 ≤ (5 * m) ^ 10 →
      ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
              zetaChiDualInteriorAtom s n t‖ * Real.log ((5 * (m : ℝ)) ^ 10) ≤
        (2 * Real.pi + 1) * (2 * Real.log 4) *
          (1 + Real.log H) * (5 * (m : ℝ)) ^ 10 := by
  filter_upwards [eventually_zetaChi_dual_block_subset_mean_bounds c hr hc0 hc1,
    eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro s hs H hH hHN
  have hsub : primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H ⊆
      zetaChiDualCoherentBlock m := Finset.filter_subset _ _
  have hb := (hm s hs _ hsub).2
  have hc := card_primeWindowSupported_mul_log_le_log hH hHN
    (fun n hn => zetaChiDualCoherentBlock_pos_le hm1 hn)
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hc
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlog : 0 ≤ Real.log ((5 * (m : ℝ)) ^ 10) :=
    Real.log_nonneg (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 5 * m))
  calc
    _ ≤ ((2 * Real.pi + 1) *
        (primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H).card) *
        Real.log ((5 * (m : ℝ)) ^ 10) := mul_le_mul_of_nonneg_right hb hlog
    _ = (2 * Real.pi + 1) *
        ((primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H).card *
          Real.log ((5 * (m : ℝ)) ^ 10)) := by ring
    _ ≤ (2 * Real.pi + 1) *
        (2 * (5 * (m : ℝ)) ^ 10 * Real.log 4 * (1 + Real.log H)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- A sufficiently small explicit logarithmic share leaves a positive
retained physical mean, uniformly in the cofactor budget. -/
theorem eventually_zetaChi_dual_retained_block_log_share_lower
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ H : ℕ,
      1 ≤ H → H ^ 2 ≤ (5 * m) ^ 10 →
      100 * Real.log 4 * (1 + Real.log H) ≤ Real.log ((5 * (m : ℝ)) ^ 10) →
      (Real.pi * (smoothAFECutoff 1).re / 50) * (5 * (m : ℝ)) ^ 10 ≤
        (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ zetaChiDualCoherentBlock m \
            primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
              zetaChiDualInteriorAtom s n t).re := by
  filter_upwards [eventually_zetaChi_dual_block_subset_mean_bounds c hr hc0 hc1,
    eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro s hs H hH hHN hshare
  let F := primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H
  have hc := card_primeWindowSupported_mul_log_le_log hH hHN
    (fun n hn => zetaChiDualCoherentBlock_pos_le hm1 hn)
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hc
  change (F.card : ℝ) * _ ≤ _ at hc
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlog : 0 < Real.log ((5 * (m : ℝ)) ^ 10) := by
    apply Real.log_pos
    have hp : (1 : ℝ) ≤ (m : ℝ) ^ 10 := one_le_pow₀ hmR
    nlinarith only [hp]
  have hfree : (F.card : ℝ) ≤ (5 * (m : ℝ)) ^ 10 / 50 := by
    have hmult := mul_le_mul_of_nonneg_right hshare (show 0 ≤ (5 * (m : ℝ)) ^ 10 by positivity)
    have hbound : (F.card : ℝ) * Real.log ((5 * (m : ℝ)) ^ 10) ≤
        ((5 * (m : ℝ)) ^ 10 / 50) * Real.log ((5 * (m : ℝ)) ^ 10) := by
      nlinarith only [hc, hmult]
    exact le_of_mul_le_mul_right hbound hlog
  have hsub : F ⊆ zetaChiDualCoherentBlock m := Finset.filter_subset _ _
  have hsplit : ((zetaChiDualCoherentBlock m \ F).card : ℝ) + F.card =
      (zetaChiDualCoherentBlock m).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  have hwhole : (5 * (m : ℝ)) ^ 10 / 25 ≤ ((zetaChiDualCoherentBlock m).card : ℝ) := by
    rw [card_zetaChiDualCoherentBlock]
    push_cast
    nlinarith only [show 0 ≤ (m : ℝ) ^ 10 by positivity]
  have hret : (5 * (m : ℝ)) ^ 10 / 50 ≤ ((zetaChiDualCoherentBlock m \ F).card : ℝ) := by
    linarith only [hfree, hsplit, hwhole]
  have hb := (hm s hs (zetaChiDualCoherentBlock m \ F) Finset.sdiff_subset).1
  have hv : 0 < (smoothAFECutoff 1).re := smoothAFECutoff_re_pos (by norm_num)
  calc
    _ = (Real.pi * (smoothAFECutoff 1).re) * ((5 * (m : ℝ)) ^ 10 / 50) := by ring
    _ ≤ (Real.pi * (smoothAFECutoff 1).re) * (zetaChiDualCoherentBlock m \ F).card :=
      mul_le_mul_of_nonneg_left hret (by positivity)
    _ ≤ _ := hb

/-- A length-order physical first mean in the free block forces a power-size
cofactor budget. This is a first-moment boundary, not a target-event obstruction. -/
theorem eventually_zetaChi_dual_free_mean_forces_cofactor_floor
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ H : ℕ,
      1 ≤ H → H ^ 2 ≤ (5 * m) ^ 10 → ∀ ρ : ℝ, 0 < ρ →
      ρ * (5 * (m : ℝ)) ^ 10 ≤
        ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
              zetaChiDualInteriorAtom s n t‖ →
      Real.exp (ρ / ((2 * Real.pi + 1) * (2 * Real.log 4)) *
        Real.log ((5 * (m : ℝ)) ^ 10) - 1) ≤ (H : ℝ) := by
  filter_upwards [eventually_zetaChi_dual_free_block_mean_harmonic_log_le c hr hc0 hc1,
    eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro s hs H hH hHN ρ _hρ hmean
  let C : ℝ := (2 * Real.pi + 1) * (2 * Real.log 4)
  have hC : 0 < C := by dsimp only [C]; have := Real.log_pos (by norm_num : (1 : ℝ) < 4); positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hN : 0 < (5 * (m : ℝ)) ^ 10 := by positivity
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlog : 0 ≤ Real.log ((5 * (m : ℝ)) ^ 10) := Real.log_nonneg
    (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 5 * m))
  have hbound := (mul_le_mul_of_nonneg_right hmean hlog).trans (hm s hs H hH hHN)
  have hcancel : ρ * Real.log ((5 * (m : ℝ)) ^ 10) ≤ C * (1 + Real.log H) := by
    apply le_of_mul_le_mul_right (a := (5 * (m : ℝ)) ^ 10) _ hN
    convert hbound using 1; ring
  have hquot : ρ * Real.log ((5 * (m : ℝ)) ^ 10) / C ≤ 1 + Real.log H :=
    (div_le_iff₀ hC).mpr (by nlinarith only [hcancel])
  have hexponent : ρ / C * Real.log ((5 * (m : ℝ)) ^ 10) - 1 ≤ Real.log H := by
    rw [div_mul_eq_mul_div]
    linarith only [hquot]
  have hHR : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  simpa only [Real.exp_log hHR] using Real.exp_le_exp.mpr hexponent

end RHTower
