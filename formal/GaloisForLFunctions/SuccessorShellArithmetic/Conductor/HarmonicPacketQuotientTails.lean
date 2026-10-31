import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramLogarithmicPlateau
import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin

/-!
# Harmonic mass on short quotient horizons

Subtracting two packet Gram expansions cancels their common torsion
term. The logarithmic plateau therefore controls every terminal packet
interval, uniformly in the conductor cutoff. A bounded multiplier that
is small at large quotients inherits a uniform squared-norm bound.
-/

open Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
noncomputable section

private def packetValue (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n

private def packetGram (Q : ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, packetValue Q a n ^ 2 / (n : ℝ)

private theorem sum_Ioc_eq_sub {K N : ℕ} (hKN : K ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc K N, f n) = (∑ n ∈ Icc 1 N, f n) - ∑ n ∈ Icc 1 K, f n := by
  have hset : (Finset.Ioc K N : Finset ℕ) = Finset.Icc 1 N \ Finset.Icc 1 K := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [hset]
  exact eq_sub_iff_add_eq.mpr (sum_sdiff (Icc_subset_Icc le_rfl hKN))

private theorem plateau_le_eight (Q : ℕ) :
    6 * Real.log Q + Real.log 4 + 5 ≤ 8 * (1 + Real.log Q) := by
  have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
  linarith only [hfour, Real.log_natCast_nonneg Q]

/-- Every conductor packet has harmonic norm bounded by one horizon logarithm and seventeen conductor logarithms. -/
theorem harmonicConductorPacket_le_log {Q : ℕ} (hQ : 2 ≤ Q) (N : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
      (Real.log N + 17 * (1 + Real.log Q)) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let T := torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  let L : ℝ := 6 * Real.log Q + Real.log 4 + 5
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have htop := (abs_le.mp (abs_harmonicGram_torsion_remainder_le_log hQ N a)).2
  have hzero := abs_harmonicGram_torsion_remainder_le_log hQ 0 a
  simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, harmonic_zero,
    Rat.cast_zero, zero_mul, sub_zero, zero_add] at hzero
  have hlow := (abs_le.mp hzero).1
  have hH := mul_le_mul_of_nonneg_right (harmonic_le_one_add_log N) hM
  have hL := mul_le_mul_of_nonneg_right (plateau_le_eight Q) hM
  have hHM := mul_nonneg (Real.log_natCast_nonneg Q) hM
  change packetGram Q a N ≤ (Real.log N + 17 * (1 + Real.log Q)) * M
  change packetGram Q a N - (harmonic N : ℝ) * M + T ≤ L * M at htop
  change -(L * M) ≤ T at hlow
  change L * M ≤ 8 * (1 + Real.log Q) * M at hL
  linarith only [htop, hlow, hH, hL, hHM]

/-- Torsion cancels between packet horizons; the two endpoint remainders cost only logarithms. -/
theorem harmonicConductorPacket_interval_le {Q K N : ℕ}
    (hQ : 2 ≤ Q) (hKN : K ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Ioc K N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
      ((harmonic N : ℝ) - harmonic K + 2 * (6 * Real.log Q + Real.log 4 + 5)) *
        ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hN := (abs_le.mp (abs_harmonicGram_torsion_remainder_le_log hQ N a)).2
  have hK := (abs_le.mp (abs_harmonicGram_torsion_remainder_le_log hQ K a)).1
  rw [sum_Ioc_eq_sub hKN]
  linarith only [hN, hK]

/-- A short complementary horizon carries only logarithmic packet mass, uniformly in every coefficient. -/
theorem harmonicConductorPacket_quotient_tail_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    {T : ℝ} (hT : 1 ≤ T) (a : ℕ → ℝ) :
    (∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
      (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
        (1 + Real.log (2 * T) + 2 * (6 * Real.log Q + Real.log 4 + 5)) *
          ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let K : ℕ := ⌊(N : ℝ) / T⌋₊
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hKle : K ≤ N := by
    have h : (K : ℝ) ≤ N :=
      (Nat.floor_le (div_nonneg hNR.le hT0.le)).trans (div_le_self hNR.le hT)
    exact_mod_cast h
  have hset : (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T) = Ioc K N := by
    ext n
    constructor
    · intro hn
      rcases mem_filter.mp hn with ⟨hn, hquot⟩
      have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hx : (N : ℝ) / T < n := by
        apply (div_lt_iff₀ hT0).mpr
        have h := (div_lt_iff₀ hnR).mp hquot
        nlinarith only [h]
      have hKn : (K : ℝ) < n := (Nat.floor_le (div_nonneg hNR.le hT0.le)).trans_lt hx
      exact mem_Ioc.mpr ⟨by exact_mod_cast hKn, (mem_Icc.mp hn).2⟩
    · intro hn
      rcases mem_Ioc.mp hn with ⟨hKn, hnN⟩
      have hn1 : 1 ≤ n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hKnR : (K : ℝ) + 1 ≤ n := by exact_mod_cast (show K + 1 ≤ n by omega)
      have hx : (N : ℝ) / T < n := (Nat.lt_floor_add_one _).trans_le hKnR
      have hquot : (N : ℝ) / n < T := by
        apply (div_lt_iff₀ hnR).mpr
        have h := (div_lt_iff₀ hT0).mp hx
        nlinarith only [h]
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1, hnN⟩, hquot⟩
  have hscalar : (harmonic N : ℝ) - harmonic K ≤ 1 + Real.log (2 * T) := by
    have h := HTGeometry.harmonic_quotient_tail_le hN hT
    rw [hset, sum_Ioc_eq_sub hKle, HTGeometry.sum_Icc_one_div_eq_harmonic,
      HTGeometry.sum_Icc_one_div_eq_harmonic] at h
    exact h
  have hM : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun m _ => sq_nonneg (a m)
  rw [hset]
  exact (harmonicConductorPacket_interval_le hQ hKle a).trans
    (mul_le_mul_of_nonneg_right (add_le_add hscalar le_rfl) hM)

/-- Uniformly bounded multipliers can be estimated separately at large and small quotient horizons. -/
theorem sum_sq_packet_le_quotient_tail {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    {T : ℝ} (hT : 1 ≤ T) {A B : ℝ} (a r : ℕ → ℝ)
    (hglobal : ∀ n ∈ Icc 1 N, |r n| ≤ B)
    (hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n → |r n| ≤ A) :
    (∑ n ∈ Icc 1 N, r n ^ 2 * (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) ≤
      (A ^ 2 * (Real.log N + 17 * (1 + Real.log Q)) +
        B ^ 2 * (1 + Real.log (2 * T) + 16 * (1 + Real.log Q))) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hsq (n : ℕ) (C : ℝ) (h : |r n| ≤ C) : r n ^ 2 ≤ C ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg (r n)) h
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      r n ^ 2 * packetValue Q a n ^ 2 / (n : ℝ) ≤
        A ^ 2 * (packetValue Q a n ^ 2 / (n : ℝ)) +
          if (N : ℝ) / n < T then B ^ 2 * (packetValue Q a n ^ 2 / (n : ℝ)) else 0 := by
    have hw : 0 ≤ packetValue Q a n ^ 2 / (n : ℝ) := by positivity
    rw [mul_div_assoc]
    by_cases hq : (N : ℝ) / n < T
    · rw [if_pos hq]
      exact (mul_le_mul_of_nonneg_right (hsq n B (hglobal n hn)) hw).trans
        (le_add_of_nonneg_left (mul_nonneg (sq_nonneg A) hw))
    · rw [if_neg hq, add_zero]
      exact mul_le_mul_of_nonneg_right (hsq n A (hgood n hn (le_of_not_gt hq))) hw
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, ← sum_filter, ← mul_sum] at hsum
  have hM : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun m _ => sq_nonneg (a m)
  have htail := (harmonicConductorPacket_quotient_tail_le hQ hN hT a).trans
    (mul_le_mul_of_nonneg_right
      (show 1 + Real.log (2 * T) + 2 * (6 * Real.log Q + Real.log 4 + 5) ≤
        1 + Real.log (2 * T) + 16 * (1 + Real.log Q) by
          have hL := plateau_le_eight Q
          linarith only [hL]) hM)
  have hbound := add_le_add
    (mul_le_mul_of_nonneg_left (harmonicConductorPacket_le_log hQ N a) (sq_nonneg A))
    (mul_le_mul_of_nonneg_left htail (sq_nonneg B))
  change (∑ n ∈ Icc 1 N, r n ^ 2 * packetValue Q a n ^ 2 / (n : ℝ)) ≤ _
  exact hsum.trans (by simpa only [packetValue, add_mul, mul_assoc] using hbound)

private def primeRowScalarError (N n : ℕ) : ℝ :=
  mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)

private theorem abs_primeRowScalarError_le {N n : ℕ} (hn : n ∈ Icc 1 N) :
    |primeRowScalarError N n| ≤ 9 := by
  refine (abs_row_sub_le hn).trans ?_
  have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
  have htwo := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
  linarith only [hfour, htwo, Real.eulerMascheroniConstant_lt_two_thirds]

private theorem exists_primeRowScalarError_small {A : ℝ} (hA : 0 < A) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ N n : ℕ, n ∈ Icc 1 N → T ≤ (N : ℝ) / n →
      |primeRowScalarError N n| ≤ A := by
  obtain ⟨Y₀, hY₀⟩ := Metric.tendsto_atTop.mp tendsto_mertensSum_sub_log (A / 2) (by positivity)
  let Y : ℕ := max Y₀ (⌈2 / A⌉₊ + 1)
  refine ⟨(Y : ℝ) + 1, le_add_of_nonneg_left (Nat.cast_nonneg Y), ?_⟩
  intro N n hn hlarge
  rcases mem_Icc.mp hn with ⟨hn1, hnN⟩
  have hq : 1 ≤ N / n := Nat.div_pos hnN hn1
  have hqR : (0 : ℝ) < (N / n : ℕ) := by exact_mod_cast hq
  have hcast := _root_.RHTower.Mertens.cast_div_lt N n hn1
  have hYq : Y ≤ N / n := by
    have h : (Y : ℝ) < (N / n : ℕ) := by linarith only [hlarge, hcast]
    exact_mod_cast h.le
  have he : |mertensSum (N / n) - Real.log (N / n : ℕ) + Real.eulerMascheroniConstant| ≤ A / 2 := by
    have h := (hY₀ (N / n) ((le_max_left _ _).trans hYq)).le
    simpa only [Real.dist_eq, sub_neg_eq_add] using h
  have hceil : (⌈2 / A⌉₊ : ℝ) ≤ (N / n : ℕ) := by
    exact_mod_cast (Nat.le_succ ⌈2 / A⌉₊).trans ((le_max_right _ _).trans hYq)
  have hinv : (1 : ℝ) / (N / n : ℕ) ≤ A / 2 := by
    have hprod := (div_le_iff₀ hA).mp ((Nat.le_ceil (2 / A)).trans hceil)
    apply (div_le_iff₀ hqR).mpr
    nlinarith only [hprod]
  have hr := roundoff_le hn1 hnN
  have hrhi := hr.2.trans hinv
  rcases abs_le.mp he with ⟨helo, hehi⟩
  rw [primeRowScalarError, abs_le]
  constructor <;> linarith only [helo, hehi, hr.1, hrhi]

/-- The actual scalar prime-row residual has a common packet norm bound with only a logarithmic conductor loss. -/
theorem eventually_primeRowScalarError_packet_sq_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, 2 ≤ Q → ∀ a : ℕ → ℝ,
      (∑ n ∈ Icc 1 N,
        (mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) ^ 2 *
          (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) / Real.log N ≤
        (ε + 2048 * (1 + Real.log Q) / Real.log N) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let A : ℝ := min 1 (ε / 4)
  have hA : 0 < A := lt_min (by norm_num) (by positivity)
  have hAone : A ≤ 1 := min_le_left _ _
  have hAeps : A ≤ ε / 4 := min_le_right _ _
  have hAsq : A ^ 2 ≤ A := by nlinarith only [hA.le, hAone]
  have hAsqone := hAsq.trans hAone
  have hAsqeps := hAsq.trans hAeps
  obtain ⟨T, hT, hgood⟩ := exists_primeRowScalarError_small hA
  let θ : ℝ := 81 * (1 + Real.log (2 * T))
  have hlim : Tendsto (fun N : ℕ => θ / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop (max 2 N₀)] with N hN
  intro Q hQ a
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hθ : θ / Real.log N ≤ ε / 2 := by
    have h := (hN₀ N ((le_max_right _ _).trans hN)).le
    rw [Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans h
  let H : ℝ := 1 + Real.log Q
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hH : 0 ≤ H := add_nonneg zero_le_one (Real.log_natCast_nonneg Q)
  have hratio : 0 ≤ H / Real.log N := div_nonneg hH hlog.le
  have hcoef : (A ^ 2 * (Real.log N + 17 * H) +
      81 * (1 + Real.log (2 * T) + 16 * H)) / Real.log N ≤
      ε + 2048 * H / Real.log N := by
    calc
      _ = A ^ 2 + (17 * A ^ 2 + 1296) * (H / Real.log N) + θ / Real.log N := by
        dsimp only [θ]
        field_simp [hlog.ne']
        ring
      _ ≤ ε / 4 + 1313 * (H / Real.log N) + ε / 2 :=
        add_le_add (add_le_add hAsqeps
          (mul_le_mul_of_nonneg_right (by linarith only [hAsqone]) hratio)) hθ
      _ ≤ ε + 2048 * (H / Real.log N) := by nlinarith only [hε.le, hratio]
      _ = _ := by ring
  have hbase := sum_sq_packet_le_quotient_tail hQ (by omega : 1 ≤ N) hT a
    (primeRowScalarError N) (fun n hn => abs_primeRowScalarError_le hn)
    (fun n hn hTn => hgood N n hn hTn)
  norm_num only [show (9 : ℝ) ^ 2 = 81 by norm_num] at hbase
  change (∑ n ∈ Icc 1 N, primeRowScalarError N n ^ 2 * packetValue Q a n ^ 2 / (n : ℝ)) /
    Real.log N ≤ (ε + 2048 * H / Real.log N) * M
  calc
    _ ≤ ((A ^ 2 * (Real.log N + 17 * H) +
        81 * (1 + Real.log (2 * T) + 16 * H)) * M) / Real.log N :=
      div_le_div_of_nonneg_right hbase hlog.le
    _ = ((A ^ 2 * (Real.log N + 17 * H) +
        81 * (1 + Real.log (2 * T) + 16 * H)) / Real.log N) * M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hM

#print axioms harmonicConductorPacket_le_log
#print axioms harmonicConductorPacket_interval_le
#print axioms harmonicConductorPacket_quotient_tail_le
#print axioms sum_sq_packet_le_quotient_tail
#print axioms eventually_primeRowScalarError_packet_sq_le

end
end GaloisForLFunctions.SuccessorShellArithmetic
