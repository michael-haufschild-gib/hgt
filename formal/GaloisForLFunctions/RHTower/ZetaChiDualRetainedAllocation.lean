import GaloisForLFunctions.RHTower.ZetaChiDualBlockSubsetMean
import GaloisForLFunctions.RHTower.PrimeWindowMultiplicity

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The complementary support is exactly the literal retained-prime support.
This applies in particular to the full source's retained set at any `L ≥ N`. -/
theorem mem_sdiff_primeWindowSupported_iff {S : Finset ℕ} {N H L n : ℕ}
    (hnS : n ∈ S) (hn0 : 0 < n) (hnL : n ≤ L) :
    n ∈ S \ primeWindowSupported S N H ↔
      n.primeFactors ⊆ Nat.primesLE L \ largePrimes N (N / H) := by
  classical
  constructor
  · intro hn p hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hn0 hpn).trans hnL, hprime⟩, ?_⟩
    intro hpw
    exact (Finset.mem_sdiff.mp hn).2 (Finset.mem_filter.mpr ⟨hnS, p, hpw, hpn⟩)
  · intro hret
    apply Finset.mem_sdiff.mpr
    refine ⟨hnS, ?_⟩
    intro hn
    obtain ⟨_, p, hp, hpn⟩ := Finset.mem_filter.mp hn
    have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr
      ⟨(mem_largePrimes.mp hp).1.2, hpn, hn0.ne'⟩
    exact (Finset.mem_sdiff.mp (hret hpf)).2 hp

/-- Complete free-window first-mean cost, uniform also in the growing
cofactor budget up to the square-root seam. -/
theorem eventually_zetaChi_dual_free_block_mean_log_le
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ H : ℕ,
      1 ≤ H → H ^ 2 ≤ (5 * m) ^ 10 →
      ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
              zetaChiDualInteriorAtom s n t‖ * Real.log ((5 * (m : ℝ)) ^ 10) ≤
        (2 * Real.pi + 1) * (2 * (H : ℝ) * Real.log 4) * (5 * (m : ℝ)) ^ 10 := by
  filter_upwards [eventually_zetaChi_dual_block_subset_mean_bounds c hr hc0 hc1,
    eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro s hs H hH hHN
  have hsub : primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H ⊆
      zetaChiDualCoherentBlock m := Finset.filter_subset _ _
  have hb := (hm s hs _ hsub).2
  have hc := card_primeWindowSupported_mul_log_le hH hHN
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
    _ ≤ (2 * Real.pi + 1) * (2 * (H : ℝ) * (5 * (m : ℝ)) ^ 10 * Real.log 4) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- At each fixed cofactor budget the physical free-block first mean is
arbitrarily small compared with the height-window length. -/
theorem eventually_zetaChi_dual_free_block_mean_small
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1)
    (H : ℕ) (hH : 1 ≤ H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
              zetaChiDualInteriorAtom s n t‖ ≤ ε * (5 * (m : ℝ)) ^ 10 := by
  have hpi : 0 < 2 * Real.pi + 1 := by positivity
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_card_primeWindowSupported_le H hH (div_pos hε hpi))
  filter_upwards [eventually_zetaChi_dual_block_subset_mean_bounds c hr hc0 hc1,
    eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)] with m hm hmM hm1
  intro s hs
  have hmN : m ≤ (5 * m) ^ 10 := (by omega : m ≤ 5 * m).trans (Nat.le_self_pow (by norm_num) _)
  have hc := hM ((5 * m) ^ 10) (hmM.trans hmN) (zetaChiDualCoherentBlock m)
    (fun n hn => zetaChiDualCoherentBlock_pos_le hm1 hn)
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hc
  have hb := (hm s hs _ (show primeWindowSupported (zetaChiDualCoherentBlock m)
    ((5 * m) ^ 10) H ⊆ zetaChiDualCoherentBlock m from Finset.filter_subset _ _)).2
  calc
    _ ≤ (2 * Real.pi + 1) *
        (primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H).card := hb
    _ ≤ (2 * Real.pi + 1) * ((ε / (2 * Real.pi + 1)) * (5 * (m : ℝ)) ^ 10) :=
      mul_le_mul_of_nonneg_left hc hpi.le
    _ = _ := by field_simp

/-- An order-one positive physical mean remains entirely in the retained
part of the literal coherent block, for every fixed cofactor budget. -/
theorem exists_zetaChi_dual_retained_block_mean_lower
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1)
    (H : ℕ) (hH : 1 ≤ H) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      κ * (5 * (m : ℝ)) ^ 10 ≤
        (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ zetaChiDualCoherentBlock m \
            primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
              zetaChiDualInteriorAtom s n t).re := by
  have hv : 0 < (smoothAFECutoff 1).re := smoothAFECutoff_re_pos (by norm_num)
  refine ⟨Real.pi * (smoothAFECutoff 1).re / 50, by positivity, ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_card_primeWindowSupported_le H hH (by norm_num : (0 : ℝ) < 1 / 50))
  filter_upwards [eventually_zetaChi_dual_block_subset_mean_bounds c hr hc0 hc1,
    eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)] with m hm hmM hm1
  intro s hs
  have hmN : m ≤ (5 * m) ^ 10 := (by omega : m ≤ 5 * m).trans (Nat.le_self_pow (by norm_num) _)
  have hc := hM ((5 * m) ^ 10) (hmM.trans hmN) (zetaChiDualCoherentBlock m)
    (fun n hn => zetaChiDualCoherentBlock_pos_le hm1 hn)
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hc
  let F := primeWindowSupported (zetaChiDualCoherentBlock m) ((5 * m) ^ 10) H
  have hsub : F ⊆ zetaChiDualCoherentBlock m := Finset.filter_subset _ _
  have hsplitN := Finset.card_sdiff_add_card_eq_card hsub
  have hsplit : ((zetaChiDualCoherentBlock m \ F).card : ℝ) + F.card =
      (zetaChiDualCoherentBlock m).card := by exact_mod_cast hsplitN
  have hwhole : (5 * (m : ℝ)) ^ 10 / 25 ≤ ((zetaChiDualCoherentBlock m).card : ℝ) := by
    rw [card_zetaChiDualCoherentBlock]
    push_cast
    nlinarith only [show 0 ≤ (m : ℝ) ^ 10 by positivity]
  have hret : (5 * (m : ℝ)) ^ 10 / 50 ≤ ((zetaChiDualCoherentBlock m \ F).card : ℝ) := by
    change (F.card : ℝ) ≤ _ at hc
    linarith only [hc, hsplit, hwhole]
  have hb := (hm s hs (zetaChiDualCoherentBlock m \ F) Finset.sdiff_subset).1
  calc
    _ = (Real.pi * (smoothAFECutoff 1).re) * ((5 * (m : ℝ)) ^ 10 / 50) := by ring
    _ ≤ (Real.pi * (smoothAFECutoff 1).re) * (zetaChiDualCoherentBlock m \ F).card :=
      mul_le_mul_of_nonneg_left hret (by positivity)
    _ ≤ _ := hb

end RHTower
