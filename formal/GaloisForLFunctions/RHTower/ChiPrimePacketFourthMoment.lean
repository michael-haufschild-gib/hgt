import GaloisForLFunctions.RHTower.ChiPhysicalQuarticPackets
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import Mathlib.Combinatorics.Pigeonhole

/-!
# Actual prime packets with large physical fourth moments

The dyadic source PNT and finite pigeonhole produce prime packets in coherent
square-root-scale cells. The complete physical chi-four kernel retains negative
real mass on these packets. After normalizing coefficient energy to one, this
signed correlation and the ordinary physical fourth moment grow without bound
per unit height, even though the largest coefficient tends to zero.

This rules out a uniform energy-and-flatness-only fourth-moment estimate. It
makes no assertion against the particular full-window BAG coefficient family.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower PrimeCells


private theorem eventually_log_packet_scale_le :
    ∀ᶠ m : ℕ in atTop, Real.log (128 * (m : ℝ) ^ 8) ≤ (m : ℝ) / 2 := by
  have hlo : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x / 32 := by
    have hh := Real.isLittleO_log_id_atTop.def (c := 1 / 32) (by norm_num)
    filter_upwards [hh, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      id, abs_of_nonneg (by linarith : 0 ≤ x), one_div, div_eq_mul_inv, mul_comm, one_mul] using hx
  have hc : ∀ᶠ m : ℕ in atTop, 4 * Real.log 128 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlo, hc,
    eventually_ge_atTop (1 : ℕ)] with m hm hc hm1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hm0.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The source PNT supplies enough actual primes for a dense coherent packet. -/
theorem eventually_prime_packet_dyadic_count :
    ∀ᶠ m : ℕ in atTop,
      64 * m ^ 7 ≤ ((Finset.Ioc (64 * m ^ 8) (128 * m ^ 8)).filter Nat.Prime).card := by
  obtain ⟨R₀, hR₀, hcount⟩ := exists_card_windowPrimes_div_ge 0
    (ε := 1 / 2) (by norm_num)
  have ht : Tendsto (fun m : ℕ => 128 * (m : ℝ) ^ 8) atTop atTop :=
    (tendsto_const_mul_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) < 128)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop R₀, eventually_log_packet_scale_le,
    eventually_ge_atTop (1 : ℕ)] with m hm hlog hm1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hR : 0 < 128 * (m : ℝ) ^ 8 := by positivity
  have hR1 : 1 < 128 * (m : ℝ) ^ 8 := by
    have hh : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hp : (1 : ℝ) ≤ (m : ℝ) ^ 8 := one_le_pow₀ hh
    linarith
  have hh := hcount (128 * (m : ℝ) ^ 8) hm 2 (by norm_num) (by norm_num)
    (128 * (m : ℝ) ^ 8) (256 * (m : ℝ) ^ 8) le_rfl (by nlinarith)
    (by ring_nf; rfl) (by simp only [Real.rpow_zero, div_one]; nlinarith)
  have hwin : windowPrimes (128 * (m : ℝ) ^ 8 / 2) (256 * (m : ℝ) ^ 8 / 2) =
      ((Finset.Ioc (64 * m ^ 8) (128 * m ^ 8)).filter Nat.Prime) := by
    have h1 : 128 * (m : ℝ) ^ 8 / 2 = ((64 * m ^ 8 : ℕ) : ℝ) := by push_cast; ring
    have h2 : 256 * (m : ℝ) ^ 8 / 2 = ((128 * m ^ 8 : ℕ) : ℝ) := by push_cast; ring
    rw [h1, h2]
    simp only [windowPrimes, Nat.floor_natCast]
  rw [hwin] at hh
  have hmain : (64 : ℝ) * (m : ℝ) ^ 7 ≤
      (1 - 1 / 2) * (256 * (m : ℝ) ^ 8 - 128 * (m : ℝ) ^ 8) /
        (2 * Real.log (128 * (m : ℝ) ^ 8)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) (Real.log_pos hR1))).mpr
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (128 : ℝ) * (m : ℝ) ^ 7 by positivity)
    nlinarith only [hmul]
  have hout := hmain.trans hh
  exact_mod_cast hout

/-- Dense prime packets are constructed by finite pigeonhole, not assumed. -/
theorem eventually_exists_dense_prime_packet :
    ∀ᶠ m : ℕ in atTop, ∃ (N : ℕ) (S : Finset ℕ),
      64 * m ^ 8 ≤ N ∧ N ≤ 128 * m ^ 8 ∧ m ^ 3 ≤ S.card ∧
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N + m ^ 4) := by
  filter_upwards [eventually_prime_packet_dyadic_count, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  let L : ℕ := 64 * m ^ 8
  let H : ℕ := m ^ 4
  let K : ℕ := 64 * m ^ 4
  let U : ℕ := 128 * m ^ 8
  let P : Finset ℕ := (Finset.Ioc L U).filter Nat.Prime
  let f : ℕ → ℕ := fun p => (p - (L + 1)) / H
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hU : U = L + K * H := by dsimp [U, L, K, H]; ring
  have hmap : ∀ p ∈ P, f p ∈ Finset.range K := by
    intro p hp
    have hp' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1)
    rw [Finset.mem_range]
    apply (Nat.div_lt_iff_lt_mul hH).mpr
    omega
  have hcard : (Finset.range K).card * m ^ 3 ≤ P.card := by
    rw [Finset.card_range]
    have he : K * m ^ 3 = 64 * m ^ 7 := by dsimp [K]; ring
    rw [he]
    exact hm
  obtain ⟨j, hj, hjcard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    hmap (⟨0, Finset.mem_range.mpr hK⟩) hcard
  let N : ℕ := L + j * H + 1
  let S : Finset ℕ := P.filter (fun p => f p = j)
  have hjK : j < K := Finset.mem_range.mp hj
  refine ⟨N, S, ?_, ?_, hjcard, ?_⟩
  · dsimp [N, L]; omega
  · change N ≤ U
    dsimp only [N]
    have hmul : (j + 1) * H ≤ K * H := Nat.mul_le_mul_right H hjK
    nlinarith
  · intro p hp
    obtain ⟨hpP, hpj⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpLU, hprime⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hpL, hpU⟩ := Finset.mem_Ioc.mp hpLU
    have hflo : j * H ≤ p - (L + 1) := by
      rw [← hpj]
      exact Nat.div_mul_le_self _ _
    have hfhi : p - (L + 1) < (j + 1) * H := by
      rw [← hpj]
      simpa only [f, mul_comm] using Nat.lt_mul_div_succ (p - (L + 1)) hH
    dsimp only [N]
    refine ⟨hprime, by omega, ?_⟩
    change p ≤ L + j * H + 1 + H
    nlinarith [Nat.sub_add_cancel (show L + 1 ≤ p by omega)]

/-- The actual logarithmic polynomial of a finite prime packet. -/
def coherentPrimePacketPoly (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ S, bourgainOscillation (t * Real.log p)

private theorem physicalDegreeFourPacket_one_eq (S : Finset ℕ) (t : ℝ) :
    physicalDegreeFourPacket S (fun _ _ _ _ => 1) t = coherentPrimePacketPoly S t ^ 4 := by
  have he (p q r s : ℕ) :
      Complex.exp (((((Real.log p + Real.log q + Real.log r + Real.log s) * t : ℝ) : ℂ) * I)) =
        bourgainOscillation (t * Real.log p) * bourgainOscillation (t * Real.log q) *
          bourgainOscillation (t * Real.log r) * bourgainOscillation (t * Real.log s) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [physicalDegreeFourPacket, Complex.ofReal_one, one_mul, he]
  change _ = (∑ p ∈ S, bourgainOscillation (t * Real.log p)) ^ 4
  rw [show (∑ p ∈ S, bourgainOscillation (t * Real.log p)) ^ 4 =
    (∑ p ∈ S, bourgainOscillation (t * Real.log p)) *
    (∑ p ∈ S, bourgainOscillation (t * Real.log p)) *
    (∑ p ∈ S, bourgainOscillation (t * Real.log p)) *
    (∑ p ∈ S, bourgainOscillation (t * Real.log p)) by ring]
  simp only [Finset.mul_sum, mul_comm, mul_assoc]

private theorem packet_fourth_mass_lower :
    ∃ N₀ : ℝ, 0 < N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H → H ≤ N / 6 →
      2 * Real.pi * H ^ 2 / N ≤ 1 / 4 →
      ∀ S : Finset ℕ, (∀ p ∈ S, (p : ℝ) ∈ Icc N (N + H)) →
      (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
          zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4).re ≤
        -((Real.pi * Real.sqrt N / 8) * (S.card : ℝ) ^ 4) ∧
      (Real.pi * Real.sqrt N / 8) * (S.card : ℝ) ^ 4 ≤
        ∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
          bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
            ‖coherentPrimePacketPoly S t‖ ^ 4 := by
  obtain ⟨N₀, hN₀, hb⟩ := exists_physicalDegreeFourPacket_negative_real
  refine ⟨N₀, hN₀, ?_⟩
  intro N H hN hH hHN heps S hS
  have hNpos : 0 < N := hN₀.trans_le hN
  have hT : 0 < physicalDegreeFourScale N := by unfold physicalDegreeFourScale; positivity
  have hh := hb N H hN hH hHN heps S hS (fun _ _ _ _ => 1)
    (by intros; norm_num)
  have hmass : (∑ p ∈ S, ∑ q ∈ S, ∑ r ∈ S, ∑ s ∈ S, (1 : ℝ)) = (S.card : ℝ) ^ 4 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hmass] at hh
  simp_rw [physicalDegreeFourPacket_one_eq] at hh
  let J : ℂ := ∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
    (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
      zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4
  have hJ : (Real.pi * Real.sqrt N / 8) * (S.card : ℝ) ^ 4 ≤ ‖J‖ := by
    have hre := (abs_le.mp (Complex.abs_re_le_norm J)).1
    change J.re ≤ _ at hh
    nlinarith only [hh, hre]
  have hnorm (t : ℝ) : ‖(bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
      zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4‖ =
      bagPhysicalHeightWindow (t / physicalDegreeFourScale N) * ‖coherentPrimePacketPoly S t‖ ^ 4 := by
    rw [norm_mul, norm_mul, norm_zpow, norm_zetaChi_line, one_zpow, mul_one, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bagPhysicalHeightWindow.nonneg]
  have hbound := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t => (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
      zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4)
    (show physicalDegreeFourScale N ≤ 2 * physicalDegreeFourScale N by linarith)
  simp_rw [hnorm] at hbound
  exact ⟨by simpa only [neg_mul] using hh, hJ.trans hbound⟩

/-- Actual prime packets have unbounded fourth physical moment relative to quadratic
coefficient energy. All heights and primes are supplied by the source PNT and chi kernel. -/
theorem eventually_exists_prime_packet_fourth_moment_large :
    ∀ᶠ m : ℕ in atTop, ∃ (N : ℕ) (S : Finset ℕ),
      64 * m ^ 8 ≤ N ∧ N ≤ 128 * m ^ 8 ∧ m ^ 3 ≤ S.card ∧
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N + m ^ 4) ∧
      (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
          zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4).re ≤
        -(physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128) * (S.card : ℝ) ^ 2) ∧
      physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128) * (S.card : ℝ) ^ 2 ≤
        ∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
          bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
            ‖coherentPrimePacketPoly S t‖ ^ 4 := by
  obtain ⟨N₀, hN₀, hb⟩ := packet_fourth_mass_lower
  have ht : Tendsto (fun m : ℕ => 64 * (m : ℝ) ^ 8) atTop atTop :=
    (tendsto_const_mul_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) < 64)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_dense_prime_packet, ht.eventually_ge_atTop N₀,
    eventually_ge_atTop (1 : ℕ)] with m hm hmlarge hm1
  obtain ⟨N, S, hNlo, hNhi, hcard, hS⟩ := hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hNloR : (64 : ℝ) * (m : ℝ) ^ 8 ≤ N := by exact_mod_cast hNlo
  have hNhiR : (N : ℝ) ≤ 128 * (m : ℝ) ^ 8 := by exact_mod_cast hNhi
  have hcardR : (m : ℝ) ^ 3 ≤ S.card := by exact_mod_cast hcard
  have hNpos : (0 : ℝ) < N := hN₀.trans_le (hmlarge.trans hNloR)
  have hH1 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hmR
  have hHsq : ((m : ℝ) ^ 4) ^ 2 = (m : ℝ) ^ 8 := by ring
  have hplateau : (m : ℝ) ^ 4 ≤ (N : ℝ) / 6 := by nlinarith only [hNloR, hHsq, hH1]
  have hcohere : 2 * Real.pi * ((m : ℝ) ^ 4) ^ 2 / (N : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hNpos).mpr
    have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg ((m : ℝ) ^ 4))
    nlinarith only [hNloR, hHsq, hpi]
  have hSreal : ∀ p ∈ S, (p : ℝ) ∈ Icc (N : ℝ) (N + (m : ℝ) ^ 4) := by
    intro p hp
    exact ⟨by exact_mod_cast (hS p hp).2.1, by exact_mod_cast (hS p hp).2.2⟩
  have hlower := hb N ((m : ℝ) ^ 4) (hmlarge.trans hNloR) (by positivity)
    hplateau hcohere S hSreal
  have hsqrt : Real.sqrt N ≤ 12 * (m : ℝ) ^ 4 := by
    have hs := Real.sq_sqrt hNpos.le
    have hs0 := Real.sqrt_nonneg (N : ℝ)
    nlinarith only [hNhiR, hHsq, hs, hs0, hH1]
  have hcore : Real.sqrt N * (m : ℝ) ^ 2 ≤ 12 * (S.card : ℝ) ^ 2 := by
    calc
      _ ≤ (12 * (m : ℝ) ^ 4) * (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsqrt (sq_nonneg _)
      _ = 12 * ((m : ℝ) ^ 3) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hcardR 2) (by norm_num)
  have hscale : physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128) * (S.card : ℝ) ^ 2 ≤
      (Real.pi * Real.sqrt N / 8) * (S.card : ℝ) ^ 4 := by
    calc
      _ = (Real.pi * Real.sqrt N / 96) * (S.card : ℝ) ^ 2 *
          (Real.sqrt N * (m : ℝ) ^ 2) := by
        unfold physicalDegreeFourScale
        ring_nf
        rw [Real.sq_sqrt hNpos.le]
        ring
      _ ≤ (Real.pi * Real.sqrt N / 96) * (S.card : ℝ) ^ 2 *
          (12 * (S.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = (Real.pi * Real.sqrt N / 8) * (S.card : ℝ) ^ 4 := by ring
  exact ⟨N, S, hNlo, hNhi, hcard, hS, hlower.1.trans (neg_le_neg hscale),
    hscale.trans hlower.2⟩

/-- Unit coefficient-energy normalization of the actual prime packet. -/
def normalizedCoherentPrimePacketPoly (S : Finset ℕ) (t : ℝ) : ℂ :=
  ((Real.sqrt (S.card : ℝ) : ℂ)⁻¹) * coherentPrimePacketPoly S t

/-- Arbitrarily flat, unit-energy prime packets still have unbounded physical fourth moments. -/
theorem eventually_exists_flat_prime_packet_fourth_moment_large :
    ∀ᶠ m : ℕ in atTop, ∃ (N : ℕ) (S : Finset ℕ),
      64 * m ^ 8 ≤ N ∧ N ≤ 128 * m ^ 8 ∧ m ^ 3 ≤ S.card ∧
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N + m ^ 4) ∧
      (∑ _p ∈ S, ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ^ 2) = 1 ∧
      ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ≤ 1 / (m : ℝ) ∧
      (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
          zetaChi (linePt t) ^ (4 : ℤ) * normalizedCoherentPrimePacketPoly S t ^ 4).re ≤
        -(physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128)) ∧
      physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128) ≤
        ∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
          bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
            ‖normalizedCoherentPrimePacketPoly S t‖ ^ 4 := by
  filter_upwards [eventually_exists_prime_packet_fourth_moment_large,
    eventually_ge_atTop (1 : ℕ)] with m hm hm1
  obtain ⟨N, S, hNlo, hNhi, hcard, hS, hnegative, hlarge⟩ := hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hcardR : (m : ℝ) ^ 3 ≤ S.card := by exact_mod_cast hcard
  have hM : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hcardR
  have hs : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.2 hM
  have hs2 := Real.sq_sqrt hM.le
  have hs4 : Real.sqrt (S.card : ℝ) ^ 4 = (S.card : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt (S.card : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs2]
  have hn : ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ = (Real.sqrt (S.card : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have henergy : (∑ _p ∈ S, ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ^ 2) = 1 := by
    simp only [hn, Finset.sum_const, nsmul_eq_mul, inv_pow, hs2]
    exact mul_inv_cancel₀ hM.ne'
  have hflat : ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ≤ 1 / (m : ℝ) := by
    have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      nlinarith only [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hmR)]
    have hms : (m : ℝ) ≤ Real.sqrt (S.card : ℝ) := by
      nlinarith only [hpow.trans hcardR, hs2, hs.le, hm0.le]
    rw [hn, ← one_div]
    exact one_div_le_one_div_of_le hm0 hms
  have hpoint (t : ℝ) : bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
      ‖normalizedCoherentPrimePacketPoly S t‖ ^ 4 = (S.card : ℝ)⁻¹ ^ 2 *
        (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
          ‖coherentPrimePacketPoly S t‖ ^ 4) := by
    simp only [normalizedCoherentPrimePacketPoly, norm_mul, hn, mul_pow, inv_pow, hs4]
    ring
  have hint : (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
      bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
        ‖normalizedCoherentPrimePacketPoly S t‖ ^ 4) = (S.card : ℝ)⁻¹ ^ 2 *
      (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
          ‖coherentPrimePacketPoly S t‖ ^ 4) := by
    simp_rw [hpoint]
    exact intervalIntegral.integral_const_mul _ _
  have hcomplex (t : ℝ) :
      (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
        zetaChi (linePt t) ^ (4 : ℤ) * normalizedCoherentPrimePacketPoly S t ^ 4 =
      (((S.card : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) *
        ((bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
          zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4) := by
    have hc : ((Real.sqrt (S.card : ℝ) : ℂ)⁻¹) ^ 4 =
        (((S.card : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) := by
      rw [inv_pow, ← Complex.ofReal_pow, hs4]
      push_cast
      rw [inv_pow]
    simp only [normalizedCoherentPrimePacketPoly, mul_pow, hc]
    ring
  have hsigned : (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
      (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
        zetaChi (linePt t) ^ (4 : ℤ) * normalizedCoherentPrimePacketPoly S t ^ 4).re =
      (S.card : ℝ)⁻¹ ^ 2 * (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        (bagPhysicalHeightWindow (t / physicalDegreeFourScale N) : ℂ) *
          zetaChi (linePt t) ^ (4 : ℤ) * coherentPrimePacketPoly S t ^ 4).re := by
    simp_rw [hcomplex]
    rw [intervalIntegral.integral_const_mul, Complex.re_ofReal_mul]
  have hcancel : (S.card : ℝ)⁻¹ ^ 2 *
      (physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128) * (S.card : ℝ) ^ 2) =
        physicalDegreeFourScale N * ((m : ℝ) ^ 2 / 128) := by field_simp
  refine ⟨N, S, hNlo, hNhi, hcard, hS, henergy, hflat, ?_, ?_⟩
  · rw [hsigned]
    have hh := mul_le_mul_of_nonneg_left hnegative (sq_nonneg (S.card : ℝ)⁻¹)
    rw [mul_neg, hcancel] at hh
    exact hh
  · rw [hint]
    have hh := mul_le_mul_of_nonneg_left hlarge (sq_nonneg (S.card : ℝ)⁻¹)
    rw [hcancel] at hh
    exact hh

/-- No constant controls these literal physical fourth moments, even along packets
whose coefficient energy is one and whose maximum coefficient tends to zero. -/
theorem no_uniform_flat_prime_packet_fourth_moment_bound :
    ¬ ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∀ (N : ℕ) (S : Finset ℕ),
      64 * m ^ 8 ≤ N → N ≤ 128 * m ^ 8 → m ^ 3 ≤ S.card →
      (∀ p ∈ S, p.Prime ∧ N ≤ p ∧ p ≤ N + m ^ 4) →
      (∑ _p ∈ S, ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ^ 2) = 1 →
      ‖(Real.sqrt (S.card : ℝ) : ℂ)⁻¹‖ ≤ 1 / (m : ℝ) →
      (∫ t in physicalDegreeFourScale N..2 * physicalDegreeFourScale N,
        bagPhysicalHeightWindow (t / physicalDegreeFourScale N) *
          ‖normalizedCoherentPrimePacketPoly S t‖ ^ 4) ≤ C * physicalDegreeFourScale N := by
  rintro ⟨C, hC⟩
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 / 128) atTop atTop := by
    have hh := (tendsto_const_mul_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) < 1 / 128)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul, mul_comm] using hh
  obtain ⟨m, hm, hmC, hm1, hmlarge⟩ := (eventually_exists_flat_prime_packet_fourth_moment_large.and
    (hC.and ((eventually_ge_atTop (1 : ℕ)).and (ht.eventually_gt_atTop C)))).exists
  obtain ⟨N, S, hNlo, hNhi, hcard, hS, henergy, hflat, _hnegative, hlower⟩ := hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hNloR : (64 : ℝ) * (m : ℝ) ^ 8 ≤ N := by exact_mod_cast hNlo
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNloR
  have hT : 0 < physicalDegreeFourScale N := by unfold physicalDegreeFourScale; positivity
  have hupper := hmC N S hNlo hNhi hcard hS henergy hflat
  nlinarith only [hlower, hupper, mul_pos hT (sub_pos.mpr hmlarge)]

end RHTower
