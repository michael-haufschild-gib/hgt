import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ZeroExceptionBandAndHotEdgeReduction
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightOneHundredEightyFour

/-!
# Signed partial-sum classification, `lcm`-free Abel tails, reflected Möbius sieves, and zero-exception coverage through height 184

This module resolves what general signed partial sums beating their Abel tail can and cannot certify,
while advancing zero-exception coverage from height `150` through height `184`:

1. **Non-selective `±1` tail-beating dichotomy and zero-blindness
   (`etaSign_and_etaFlipSign_properties`, `exists_unitSign_partialSum_beats_tail_everywhere`,
   `etaFlipSign_beats_tail_at_zeta_zero`)**:
   The two pure `±1` sequences `etaSign k = (-1)^k` and `etaFlipSign k` (flipping `(k = 0, 1)` from
   `(+1, -1)` to `(-1, +1)`) both have `|c k| = 1`, zero-balanced pair prefixes `∑_{k < 2K} c k = 0`,
   `|∑_{k < N} c k| ≤ 1`, and the identical `ζ`-free Abel tail bound
   `(‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re` for every `K ≥ 1`. At **every** point `s` with
   `0 < s.re` and `s ≠ 1` (zero exceptions across all heights), at least one of
   `{etaSign, etaFlipSign}` strictly beats its Abel tail; yet at any zero `ρ` of `riemannZeta` in the
   strip, `etaFlipSign` strictly beats its tail while `etaSign` fails. Unrestricted `±1`
   zero-balanced partial sums therefore cannot exclude a zero of `ζ`.

2. **Exact pole-cancellation classification and universal `lcm`-free Abel tail for `ζ`-divisible
   signed partial sums (`divisorSignedCoeff`, `bdd_divisorSignedPrefix_iff_harmonic_sum_eq_zero`,
   `divisorSignedPrefix_diff_abs_le`, `norm_divisorSignedSeries_sub_partialSum_le`,
   `zeta_ne_zero_of_divisorSignedPartialSum_beats_tail`,
   `norm_divisorSignedPartialSum_le_tail_of_zeta_eq_zero`)**:
   For any finite real divisor packet `b` on `{1, ..., M}` (`c_{M,b}(n) = ∑_{m ∣ n, 1 ≤ m ≤ M} b(m)`),
   prefix sums `C_{M,b}(N) = ∑_{n=1}^N c_{M,b}(n)` are bounded if and only if
   `∑_{m=1}^M b(m) / m = 0`. Under `∑_{m=1}^M b(m) / m = 0`, `|C_{M,b}(n) - C_{M,b}(N)| ≤ ∑_{m=1}^M |b(m)|`
   for all `n, N ∈ ℕ` (with no `lcm` factor), `∑_{n=1}^N c_{M,b}(n) n^{-z} → (∑_{m=1}^M b(m) m^{-z}) ζ(z)`
   across `Re z > 0`, `z ≠ 1`, and the tail is bounded at **every** integer cutoff `N ∈ ℕ` by
   `(∑_{m=1}^M |b(m)|) * (‖z‖ / z.re) * occupationWeight N ^ z.re`. At any `ζ`-zero `ρ`, **every**
   pole-cancelled signed partial sum (`M, b, N` arbitrary) is dominated by its Abel tail.

3. **Reflected right-strip Möbius-sieved packet and zero-exception advance through height `184`
   (`moebiusSievedEtaPacket_properties`, `riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour`,
   `zero_exception_band_oneHundredFifty_to_oneHundredEightyFour`,
   `rh_iff_exists_divisorSigned_partialSum_above_oneHundredEightyFour`)**:
   Convolving `δ_1 - 2 δ_2` with `μ_{≤ R}` (`R ≥ 2`) produces a pole-cancelled divisor packet on
   `{1, ..., 2R}` of `ℓ¹` norm `≤ 3 R` whose signed Dirichlet coefficients satisfy `c(1) = 1`,
   `c(2) = -2`, and `c(n) = 0` for every `3 ≤ n ≤ R`, annihilating the head `[3, R]` while
   evaluating at `w = 1 - conj s` accelerates tail decay from `N^{-Re s}` to `N^{-(1 - Re s)}`.
   Combining with `rhVerifiedThrough_oneHundredEightyFour` covers **every** point of
   `{3001/24000 ≤ Re s < 1/2 ∧ 150 < |Im s| ≤ 184}` with zero exceptions and proves that covering
   `{3001/24000 ≤ Re s < 1/2 ∧ 184 < |Im s|}` with any pole-cancelled signed partial sum is
   unconditionally equivalent (`↔`) to `RiemannHypothesis`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Complex Filter MeasureTheory Set Topology Finset
open scoped ComplexConjugate
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open InverseSpectrum.ShellMixing

/-! ### Part 1: Non-selective `±1` signed partial sums beat their tail everywhere, including at `ζ`-zeros -/

/-- Standard alternating `±1` sign `(-1)^k` (`0`-indexed, pairing `(k + 1)^{-s}`). -/
def etaSign (k : ℕ) : ℝ := (-1 : ℝ) ^ k

/-- First-pair-flipped `±1` sign: `(-1, +1)` on `k = 0, 1` and `(-1)^k` for `k ≥ 2`. -/
def etaFlipSign (k : ℕ) : ℝ :=
  if k = 0 then -1 else if k = 1 then 1 else (-1 : ℝ) ^ k

/-- `N`-term `0`-indexed signed Dirichlet partial sum `∑_{k < N} c(k) (k + 1)^{-s}` written via
`occupationWeight k = (k + 1)⁻¹`. -/
def unitSignPartialSum (c : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, (c k : ℂ) * (occupationWeight k : ℂ) ^ s

/-- Exact unit-sign, zero-balanced-pair, and unit-prefix-oscillation properties shared by `etaSign`
and `etaFlipSign`. -/
theorem etaSign_and_etaFlipSign_properties :
    (∀ k : ℕ, |etaSign k| = 1 ∧ |etaFlipSign k| = 1) ∧
    (∀ K : ℕ, (∑ k ∈ Finset.range (2 * K), etaSign k) = 0 ∧
      (∑ k ∈ Finset.range (2 * K), etaFlipSign k) = 0) ∧
    (∀ N : ℕ, |∑ k ∈ Finset.range N, etaSign k| ≤ 1 ∧
      |∑ k ∈ Finset.range N, etaFlipSign k| ≤ 1) := by
  have h1 : ∀ k : ℕ, |etaSign k| = 1 ∧ |etaFlipSign k| = 1 := fun k => by
    unfold etaSign etaFlipSign
    refine ⟨by rw [abs_pow, abs_neg, abs_one, one_pow], ?_⟩
    split_ifs <;> simp [abs_pow]
  have heven : ∀ K : ℕ, (∑ k ∈ Finset.range (2 * K), etaSign k) = 0 ∧
      (∑ k ∈ Finset.range (2 * K), etaFlipSign k) = 0 := by
    intro K
    induction K with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      rcases m with _ | m'
      · simp [Finset.sum_range_succ, etaSign, etaFlipSign]
      · have hk0 : 2 * (m' + 1) ≠ 0 := by omega
        have hk1 : 2 * (m' + 1) ≠ 1 := by omega
        have hk2 : 2 * (m' + 1) + 1 ≠ 0 := by omega
        have hk3 : 2 * (m' + 1) + 1 ≠ 1 := by omega
        have hp1 : (-1 : ℝ) ^ (2 * (m' + 1)) = 1 := Even.neg_one_pow ⟨m' + 1, by ring⟩
        have hp2 : (-1 : ℝ) ^ (2 * (m' + 1) + 1) = -1 := by rw [pow_succ, hp1]; ring
        refine ⟨?_, ?_⟩
        · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih.1]
          unfold etaSign; rw [hp1, hp2]; ring
        · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih.2]
          unfold etaFlipSign
          rw [if_neg hk0, if_neg hk1, if_neg hk2, if_neg hk3, hp1, hp2]; ring
  refine ⟨h1, heven, fun N => ?_⟩
  rcases Nat.even_or_odd' N with ⟨K, rfl | rfl⟩
  · rw [(heven K).1, (heven K).2, abs_zero]
    exact ⟨zero_le_one, zero_le_one⟩
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, (heven K).1, (heven K).2, zero_add, zero_add]
    exact ⟨(h1 (2 * K)).1.le, (h1 (2 * K)).2.le⟩

private theorem occ_cpow_eq_neg_cpow (k : ℕ) (s : ℂ) :
    (occupationWeight k : ℂ) ^ s = (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have harg : (((k : ℝ) + 1 : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_pos.ne
  rw [occupationWeight_eq, Complex.ofReal_inv, Complex.inv_cpow _ s harg, Complex.cpow_neg]

private theorem unitSignPartialSum_etaSign_two_mul (K : ℕ) (s : ℂ) :
    unitSignPartialSum etaSign (2 * K) s =
      ∑ j ∈ Finset.range K, ((occupationWeight (2 * j) : ℂ) ^ s -
        (occupationWeight (2 * j + 1) : ℂ) ^ s) := by
  induction K with
  | zero => simp [unitSignPartialSum]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, unitSignPartialSum,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ← unitSignPartialSum, ih]
    have hp0 : etaSign (2 * m) = 1 := Even.neg_one_pow ⟨m, by ring⟩
    have hp1 : etaSign (2 * m + 1) = -1 := by
      unfold etaSign; rw [pow_succ, Even.neg_one_pow ⟨m, by ring⟩]; ring
    rw [hp0, hp1]; push_cast; ring

private theorem unitSignPartialSum_etaFlipSign_two_mul {K : ℕ} (hK : 1 ≤ K) (s : ℂ) :
    unitSignPartialSum etaFlipSign (2 * K) s =
      unitSignPartialSum etaSign (2 * K) s - 2 * (1 - (2 : ℂ) ^ (-s)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK
  induction m with
  | zero =>
    have hocc0 : (occupationWeight 0 : ℂ) ^ s = 1 := by simp [occupationWeight_eq]
    have hocc1 : (occupationWeight 1 : ℂ) ^ s = (2 : ℂ) ^ (-s) := by
      have h := occ_cpow_eq_neg_cpow 1 s
      norm_num at h
      exact h
    simp only [Nat.add_zero, Nat.mul_one, unitSignPartialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, etaFlipSign, etaSign, ↓reduceIte, Nat.one_ne_zero]
    rw [hocc0, hocc1]
    push_cast; ring
  | succ r ih =>
    have hstep : ∀ (c : ℕ → ℝ) (n : ℕ), unitSignPartialSum c (n + 2) s =
        unitSignPartialSum c n s + (c n : ℂ) * (occupationWeight n : ℂ) ^ s +
          (c (n + 1) : ℂ) * (occupationWeight (n + 1) : ℂ) ^ s := fun c n => by
      unfold unitSignPartialSum
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : 1 ≤ 1 + r := by omega
    have hk0 : 2 * (1 + r) ≠ 0 := by omega
    have hk1 : 2 * (1 + r) ≠ 1 := by omega
    have hk2 : 2 * (1 + r) + 1 ≠ 0 := by omega
    have hk3 : 2 * (1 + r) + 1 ≠ 1 := by omega
    rw [show 1 + (r + 1) = (1 + r) + 1 by omega, show 2 * ((1 + r) + 1) = 2 * (1 + r) + 2 by omega,
      hstep etaFlipSign, hstep etaSign, ih h1]
    unfold etaFlipSign etaSign
    rw [if_neg hk0, if_neg hk1, if_neg hk2, if_neg hk3]
    ring

private theorem norm_etaSign_limit_sub_partialSum_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (K : ℕ) :
    ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - unitSignPartialSum etaSign (2 * K) s‖ ≤
      (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re := by
  let f : ℕ → ℂ := fun j => (occupationWeight (2 * j) : ℂ) ^ s - (occupationWeight (2 * j + 1) : ℂ) ^ s
  have hf_eq : ∀ j : ℕ, f j = _root_.RHTower.etaTerm s j := fun j => by
    dsimp only [f]
    unfold _root_.RHTower.etaTerm
    rw [occ_cpow_eq_neg_cpow (2 * j) s, occ_cpow_eq_neg_cpow (2 * j + 1) s]
    push_cast; ring_nf
  have hf_bound : ∀ j : ℕ, ‖f j‖ ≤
      (‖s‖ / s.re) * (occupationWeight (2 * j) ^ s.re - occupationWeight (2 * (j + 1)) ^ s.re) := by
    intro j
    have hch := norm_thermal_chord (occupationWeight_pos (2 * j + 1))
      (occupationWeight_antitone (Nat.le_succ (2 * j))) (occupation_in_unit (2 * j)).2 hs0 le_rfl
    have hmono : occupationWeight (2 * (j + 1)) ^ s.re ≤ occupationWeight (2 * j + 1) ^ s.re :=
      Real.rpow_le_rpow (occupationWeight_pos _).le
        (occupationWeight_antitone (by omega : 2 * j + 1 ≤ 2 * (j + 1))) hs0.le
    exact hch.trans (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (norm_nonneg s) hs0.le))
  have hsum_f : Summable (fun j : ℕ => ‖f j‖) := by
    have hsum_tel : Summable (fun j : ℕ =>
        (‖s‖ / s.re) * (occupationWeight (2 * j) ^ s.re - occupationWeight (2 * (j + 1)) ^ s.re)) := by
      refine Summable.mul_left _ (summable_of_sum_range_le (c := occupationWeight 0 ^ s.re)
        (fun j => sub_nonneg.mpr
          (Real.rpow_le_rpow (occupationWeight_pos _).le
            (occupationWeight_antitone (by omega)) hs0.le)) fun N => ?_)
      rw [Finset.sum_range_sub' (fun j => occupationWeight (2 * j) ^ s.re) N]
      linarith [Real.rpow_nonneg (occupationWeight_pos (2 * N)).le s.re]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf_bound hsum_tel
  have hlim : (∑' j : ℕ, f j) = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
    have h1 : (∑' j : ℕ, f j) = _root_.RHTower.etaPair s := by
      unfold _root_.RHTower.etaPair; simp_rw [hf_eq]
    rw [h1, _root_.RHTower.etaPair_eq s hs0 hs1]
  rw [← hlim, unitSignPartialSum_etaSign_two_mul]
  change ‖(∑' j : ℕ, f j) - ∑ j ∈ Finset.range K, f j‖ ≤ _
  rw [← hsum_f.of_norm.sum_add_tsum_nat_add K, add_sub_cancel_left]
  have hshift_sum : Summable (fun m : ℕ => ‖f (m + K)‖) := hsum_f.comp_injective (add_left_injective K)
  calc ‖∑' m : ℕ, f (m + K)‖
      ≤ ∑' m : ℕ, ‖f (m + K)‖ := norm_tsum_le_tsum_norm hshift_sum
    _ ≤ (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re := by
        refine le_of_tendsto hshift_sum.hasSum.tendsto_sum_nat (Eventually.of_forall fun M => ?_)
        calc (∑ m ∈ Finset.range M, ‖f (m + K)‖)
            ≤ (‖s‖ / s.re) * ∑ m ∈ Finset.range M,
                (occupationWeight (2 * (K + m)) ^ s.re -
                  occupationWeight (2 * (K + (m + 1))) ^ s.re) := by
              rw [Finset.mul_sum]
              refine Finset.sum_le_sum fun m _ => ?_
              simpa only [Nat.add_comm m K, Nat.add_assoc] using hf_bound (m + K)
          _ ≤ (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re := by
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (norm_nonneg s) hs0.le)
              have ht := Finset.sum_range_sub' (fun m : ℕ => occupationWeight (2 * (K + m)) ^ s.re) M
              simp only [Nat.add_zero] at ht
              rw [ht]
              linarith [Real.rpow_nonneg (occupationWeight_pos (2 * (K + M))).le s.re]

/-- **Universal `±1` tail-beating dichotomy across `0 < Re s` (`s ≠ 1`):**
both `etaSign` and `etaFlipSign` obey the exact `ζ`-free Abel tail bound
`(‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re` for all `K ≥ 1`, and at **every** point `s` with
`0 < s.re` and `s ≠ 1` (zero exceptions across all heights), at least one of `{etaSign, etaFlipSign}`
strictly beats that tail bound. -/
theorem exists_unitSign_partialSum_beats_tail_everywhere
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    (∀ K : ℕ, 1 ≤ K →
      ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - unitSignPartialSum etaSign (2 * K) s‖ ≤
        (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re ∧
      ‖((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - 2 * (1 - (2 : ℂ) ^ (-s))) -
          unitSignPartialSum etaFlipSign (2 * K) s‖ ≤
        (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re) ∧
    ∃ c ∈ ({etaSign, etaFlipSign} : Set (ℕ → ℝ)), ∃ K : ℕ, 1 ≤ K ∧
      (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re < ‖unitSignPartialSum c (2 * K) s‖ := by
  have htails : ∀ K : ℕ, 1 ≤ K →
      ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - unitSignPartialSum etaSign (2 * K) s‖ ≤
        (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re ∧
      ‖((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - 2 * (1 - (2 : ℂ) ^ (-s))) -
          unitSignPartialSum etaFlipSign (2 * K) s‖ ≤
        (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re := fun K hK => by
    refine ⟨norm_etaSign_limit_sub_partialSum_le hs0 hs1 K, ?_⟩
    rw [unitSignPartialSum_etaFlipSign_two_mul hK s, sub_sub_sub_cancel_right]
    exact norm_etaSign_limit_sub_partialSum_le hs0 hs1 K
  refine ⟨htails, ?_⟩
  set L₁ : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
  set L₂ : ℂ := L₁ - 2 * (1 - (2 : ℂ) ^ (-s))
  have hgap : 0 < ‖1 - (2 : ℂ) ^ (-s)‖ := by
    have h2 : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hs0)
    have hn : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
        Complex.neg_re]
    have h := norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (-s))
    rw [norm_one, hn] at h
    linarith
  have hor : 0 < ‖L₁‖ ∨ 0 < ‖L₂‖ := by
    by_contra! hall
    have h1 : ‖L₁‖ = 0 := le_antisymm hall.1 (norm_nonneg _)
    have h2 : ‖L₂‖ = 0 := le_antisymm hall.2 (norm_nonneg _)
    have hdiff : L₁ - L₂ = 2 * (1 - (2 : ℂ) ^ (-s)) := by dsimp only [L₂]; ring
    have htri := norm_sub_le L₁ L₂
    rw [hdiff, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, h1, h2] at htri
    linarith
  have htend : Tendsto (fun K : ℕ => (‖s‖ / s.re) * occupationWeight (2 * K) ^ s.re) atTop (𝓝 0) := by
    have hocc : Tendsto (fun K : ℕ => occupationWeight (2 * K) ^ s.re) atTop (𝓝 0) := by
      have h0 : Tendsto (fun K : ℕ => ((2 * (K : ℝ) + 1) : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hs0).comp
          (tendsto_atTop_add_const_right atTop 1
            ((tendsto_natCast_atTop_atTop).const_mul_atTop two_pos))
      refine h0.congr fun K => ?_
      have hpos : (0 : ℝ) < 2 * (K : ℝ) + 1 := by positivity
      rw [occupationWeight_eq, Real.inv_rpow (by positivity), Real.rpow_neg hpos.le]
      push_cast; ring_nf
    simpa only [mul_zero] using hocc.const_mul (‖s‖ / s.re)
  rcases hor with hL1 | hL2
  · obtain ⟨K, hK1, hK_lt⟩ := ((eventually_ge_atTop 1).and
      (htend.eventually (gt_mem_nhds (half_pos hL1)))).exists
    have htb := (htails K hK1).1
    have htri : ‖L₁‖ ≤ ‖unitSignPartialSum etaSign (2 * K) s‖ +
        ‖L₁ - unitSignPartialSum etaSign (2 * K) s‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (unitSignPartialSum etaSign (2 * K) s) (L₁ - unitSignPartialSum etaSign (2 * K) s)
    exact ⟨etaSign, by simp, K, hK1, by linarith⟩
  · obtain ⟨K, hK1, hK_lt⟩ := ((eventually_ge_atTop 1).and
      (htend.eventually (gt_mem_nhds (half_pos hL2)))).exists
    have htb := (htails K hK1).2
    have htri : ‖L₂‖ ≤ ‖unitSignPartialSum etaFlipSign (2 * K) s‖ +
        ‖L₂ - unitSignPartialSum etaFlipSign (2 * K) s‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (unitSignPartialSum etaFlipSign (2 * K) s)
          (L₂ - unitSignPartialSum etaFlipSign (2 * K) s)
    exact ⟨etaFlipSign, by simp, K, hK1, by linarith⟩

/-- **Zero-blindness of non-`ζ`-divisible `±1` partial sums:** at any point `ρ` (`0 < ρ.re`, `ρ ≠ 1`)
where `riemannZeta ρ = 0`, `etaSign` never beats its Abel tail at any `K`, whereas `etaFlipSign`
strictly beats the identical Abel tail `(‖ρ‖ / ρ.re) * occupationWeight (2 * K) ^ ρ.re` for all
sufficiently large `K`. -/
theorem etaFlipSign_beats_tail_at_zeta_zero
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    (∀ K : ℕ, ‖unitSignPartialSum etaSign (2 * K) ρ‖ ≤
      (‖ρ‖ / ρ.re) * occupationWeight (2 * K) ^ ρ.re) ∧
    (∀ᶠ K : ℕ in atTop,
      (‖ρ‖ / ρ.re) * occupationWeight (2 * K) ^ ρ.re <
        ‖unitSignPartialSum etaFlipSign (2 * K) ρ‖) := by
  refine ⟨fun K => ?_, ?_⟩
  · have h := norm_etaSign_limit_sub_partialSum_le hρ0 hρ1 K
    rwa [hz, mul_zero, zero_sub, norm_neg] at h
  · have hgap : 0 < 2 * ‖1 - (2 : ℂ) ^ (-ρ)‖ := by
      have h2 : (2 : ℝ) ^ (-ρ.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hρ0)
      have hn : ‖(2 : ℂ) ^ (-ρ)‖ = (2 : ℝ) ^ (-ρ.re) := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
          Complex.neg_re]
      have h := norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (-ρ))
      rw [norm_one, hn] at h
      linarith
    have htend : Tendsto (fun K : ℕ => (‖ρ‖ / ρ.re) * occupationWeight (2 * K) ^ ρ.re) atTop (𝓝 0) := by
      have hocc : Tendsto (fun K : ℕ => occupationWeight (2 * K) ^ ρ.re) atTop (𝓝 0) := by
        have h0 : Tendsto (fun K : ℕ => ((2 * (K : ℝ) + 1) : ℝ) ^ (-ρ.re)) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop hρ0).comp
            (tendsto_atTop_add_const_right atTop 1
              ((tendsto_natCast_atTop_atTop).const_mul_atTop two_pos))
        refine h0.congr fun K => ?_
        have hpos : (0 : ℝ) < 2 * (K : ℝ) + 1 := by positivity
        rw [occupationWeight_eq, Real.inv_rpow (by positivity), Real.rpow_neg hpos.le]
        push_cast; ring_nf
      simpa only [mul_zero] using hocc.const_mul (‖ρ‖ / ρ.re)
    filter_upwards [eventually_ge_atTop 1, htend.eventually (gt_mem_nhds (half_pos hgap))]
      with K hK1 hK_lt
    have htb := norm_etaSign_limit_sub_partialSum_le hρ0 hρ1 K
    rw [hz, mul_zero, zero_sub, norm_neg] at htb
    rw [unitSignPartialSum_etaFlipSign_two_mul hK1 ρ]
    have htri := norm_sub_norm_le (2 * (1 - (2 : ℂ) ^ (-ρ))) (unitSignPartialSum etaSign (2 * K) ρ)
    rw [norm_sub_rev, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at htri
    linarith

/-! ### Part 2: Exact pole-cancellation classification and `lcm`-free Abel tail for `ζ`-divisible signed partial sums -/

/-- `ζ`-divisible signed Dirichlet coefficient generated by a finite real divisor packet `b` on
`{1, ..., M}`: `c_{M,b}(n) = ∑_{m ∈ Icc 1 M, m ∣ n} b(m)` for `n ≥ 1` (`0` at `n = 0`). -/
def divisorSignedCoeff (M : ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ∑ m ∈ (Finset.Icc 1 M).filter (· ∣ n), b m

/-- Prefix sum `C_{M,b}(N) = ∑_{n=1}^N c_{M,b}(n)`. -/
def divisorSignedPrefix (M : ℕ) (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, divisorSignedCoeff M b n

/-- Finite Dirichlet multiplier `B_{M,b}(z) = ∑_{m=1}^M b(m) m^{-z}`. -/
def divisorPacketPoly (M : ℕ) (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z)

/-- `N`-term signed Dirichlet partial sum `∑_{n=1}^N c_{M,b}(n) n^{-z}`. -/
def divisorSignedPartialSum (M : ℕ) (b : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (divisorSignedCoeff M b n : ℂ) * ((n : ℝ) : ℂ) ^ (-z)

/-- `ℓ¹` norm `∑_{m=1}^M |b(m)|` governing the `lcm`-free prefix oscillation and Abel tail. -/
def divisorPacketL1 (M : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, |b m|

/-- Exact integer-quotient formula `C_{M,b}(N) = ∑_{m=1}^M b(m) ⌊N / m⌋`. -/
theorem divisorSignedPrefix_eq_sum_div (M : ℕ) (b : ℕ → ℝ) (N : ℕ) :
    divisorSignedPrefix M b N = ∑ m ∈ Finset.Icc 1 M, b m * ((N / m : ℕ) : ℝ) := by
  unfold divisorSignedPrefix divisorSignedCoeff
  have h1 : (∑ n ∈ Finset.Icc 1 N, if n = 0 then (0 : ℝ) else ∑ m ∈ (Finset.Icc 1 M).filter (· ∣ n), b m) =
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 M, if m ∣ n then b m else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [if_neg hn0, Finset.sum_filter]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
  rw [← Finset.sum_filter]
  have hcard : ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = (Finset.Icc 1 (N / m)).card := by
    refine Finset.card_bij (fun n _ => n / m) ?_ ?_ ?_
    · intro n hn
      obtain ⟨hn_lu, hmn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn_lu
      obtain ⟨k, rfl⟩ := hmn
      have hk1 : 1 ≤ k := by rcases k with _ | k <;> omega
      rw [Nat.mul_div_cancel_left k hm_pos]
      exact Finset.mem_Icc.mpr ⟨hk1, (Nat.le_div_iff_mul_le hm_pos).mpr (by rw [mul_comm]; exact hnN)⟩
    · intro n₁ hn₁ n₂ hn₂ heq
      obtain ⟨_, k₁, rfl⟩ := Finset.mem_filter.mp hn₁
      obtain ⟨_, k₂, rfl⟩ := Finset.mem_filter.mp hn₂
      rw [Nat.mul_div_cancel_left _ hm_pos, Nat.mul_div_cancel_left _ hm_pos] at heq
      rw [heq]
    · intro k hk
      obtain ⟨hk1, hkQ⟩ := Finset.mem_Icc.mp hk
      refine ⟨m * k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right m k⟩,
        Nat.mul_div_cancel_left k hm_pos⟩
      · exact Nat.mul_pos hm_pos hk1
      · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm_pos).mp hkQ
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm, hcard]

/-- **Exact pole-cancellation classification of bounded prefix sums:**
`divisorSignedPrefix M b` is bounded on `ℕ` if and only if the harmonic pole-cancellation identity
`∑_{m=1}^M b(m) / m = 0` holds. -/
theorem bdd_divisorSignedPrefix_iff_harmonic_sum_eq_zero (M : ℕ) (b : ℕ → ℝ) :
    (∃ B : ℝ, ∀ N : ℕ, |divisorSignedPrefix M b N| ≤ B) ↔
      (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 := by
  have hdecomp : ∀ N : ℕ,
      divisorSignedPrefix M b N =
        (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) * (N : ℝ) -
          ∑ m ∈ Finset.Icc 1 M, b m * (((N % m : ℕ) : ℝ) / (m : ℝ)) := fun N => by
    rw [divisorSignedPrefix_eq_sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    have hdiv_mod : (m : ℝ) * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N m
    have hq : ((N / m : ℕ) : ℝ) * (m : ℝ) = (N : ℝ) - ((N % m : ℕ) : ℝ) := by linarith [hdiv_mod]
    field_simp [hm_ne]
    rw [mul_assoc, hq]
  have hrem_le : ∀ N : ℕ,
      |∑ m ∈ Finset.Icc 1 M, b m * (((N % m : ℕ) : ℝ) / (m : ℝ))| ≤ divisorPacketL1 M b := fun N => by
    unfold divisorPacketL1
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm_r : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
    have hlt : ((N % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast Nat.mod_lt N hm_pos
    have hfrac : |((N % m : ℕ) : ℝ) / (m : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hm_r.le)]
      exact (div_lt_one hm_r).mpr hlt |>.le
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hfrac
  constructor
  · rintro ⟨B, hB⟩
    set S := ∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)
    by_contra hS
    have hS_pos : 0 < |S| := abs_pos.mpr hS
    obtain ⟨N, hN⟩ := exists_nat_gt ((B + divisorPacketL1 M b + 1) / |S|)
    have hmul : B + divisorPacketL1 M b + 1 < |S| * (N : ℝ) := by
      rw [mul_comm]; exact (div_lt_iff₀ hS_pos).mp hN
    have h1 := hB N
    rw [hdecomp N] at h1
    have h2 := hrem_le N
    have h3 : |S * (N : ℝ)| - |∑ m ∈ Finset.Icc 1 M, b m * (((N % m : ℕ) : ℝ) / (m : ℝ))| ≤
        |S * (N : ℝ) - ∑ m ∈ Finset.Icc 1 M, b m * (((N % m : ℕ) : ℝ) / (m : ℝ))| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul, abs_of_nonneg (a := (N : ℝ)) (Nat.cast_nonneg N)] at h3
    linarith
  · intro h0
    refine ⟨divisorPacketL1 M b, fun N => ?_⟩
    rw [hdecomp N, h0, zero_mul, zero_sub, abs_neg]
    exact hrem_le N

/-- **`lcm`-free fractional-part oscillation bound:** whenever `∑_{m=1}^M b(m) / m = 0`,
`|C_{M,b}(n) - C_{M,b}(N)| ≤ divisorPacketL1 M b` for **all** `n, N ∈ ℕ` without any `lcm` factor. -/
theorem divisorSignedPrefix_diff_abs_le {M : ℕ} {b : ℕ → ℝ}
    (hpole : (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0) (n N : ℕ) :
    |divisorSignedPrefix M b n - divisorSignedPrefix M b N| ≤ divisorPacketL1 M b := by
  have hval : ∀ K : ℕ, divisorSignedPrefix M b K =
      -∑ m ∈ Finset.Icc 1 M, b m * (((K % m : ℕ) : ℝ) / (m : ℝ)) := fun K => by
    rw [divisorSignedPrefix_eq_sum_div]
    have h0 : (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) * (K : ℝ) = 0 := by rw [hpole, zero_mul]
    rw [Finset.sum_mul] at h0
    linarith [show (∑ m ∈ Finset.Icc 1 M, b m * ((K / m : ℕ) : ℝ)) +
        (∑ m ∈ Finset.Icc 1 M, b m * (((K % m : ℕ) : ℝ) / (m : ℝ))) =
        ∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ) * (K : ℝ) by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
      have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
      have hdm : (m : ℝ) * ((K / m : ℕ) : ℝ) + ((K % m : ℕ) : ℝ) = (K : ℝ) := by
        exact_mod_cast Nat.div_add_mod K m
      have hq : ((K / m : ℕ) : ℝ) * (m : ℝ) + ((K % m : ℕ) : ℝ) = (K : ℝ) := by linarith [hdm]
      field_simp [hm_ne]; rw [hq]]
  have hbounds : ∀ K : ℕ,
      -(∑ m ∈ Finset.Icc 1 M, max (b m) 0) ≤ divisorSignedPrefix M b K ∧
        divisorSignedPrefix M b K ≤ ∑ m ∈ Finset.Icc 1 M, max (-b m) 0 := fun K => by
    rw [hval K]
    refine ⟨?_, ?_⟩
    · rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun m hm => ?_
      have hm_r : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
      have hlt : ((K % m : ℕ) : ℝ) / (m : ℝ) ≤ 1 :=
        ((div_lt_one hm_r).mpr (by exact_mod_cast Nat.mod_lt K (Finset.mem_Icc.mp hm).1)).le
      have hnn : 0 ≤ ((K % m : ℕ) : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hm_r.le
      rcases le_total 0 (b m) with hb | hb
      · rw [max_eq_left hb]; nlinarith
      · rw [max_eq_right hb]; nlinarith
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun m hm => ?_
      have hm_r : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
      have hlt : ((K % m : ℕ) : ℝ) / (m : ℝ) ≤ 1 :=
        ((div_lt_one hm_r).mpr (by exact_mod_cast Nat.mod_lt K (Finset.mem_Icc.mp hm).1)).le
      have hnn : 0 ≤ ((K % m : ℕ) : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hm_r.le
      rcases le_total 0 (b m) with hb | hb
      · rw [max_eq_right (by linarith)]; nlinarith
      · rw [max_eq_left (by linarith)]; nlinarith
  have hsum_abs : (∑ m ∈ Finset.Icc 1 M, max (b m) 0) + (∑ m ∈ Finset.Icc 1 M, max (-b m) 0) =
      divisorPacketL1 M b := by
    unfold divisorPacketL1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rcases le_total 0 (b m) with hb | hb
    · rw [max_eq_left hb, max_eq_right (by linarith), abs_of_nonneg hb, add_zero]
    · rw [max_eq_right hb, max_eq_left (by linarith), abs_of_nonpos hb, zero_add]
  obtain ⟨hn_lo, hn_hi⟩ := hbounds n
  obtain ⟨hN_lo, hN_hi⟩ := hbounds N
  exact abs_le.mpr ⟨by linarith [hsum_abs], by linarith [hsum_abs]⟩

private theorem abel_tail_finite_identity (M : ℕ) (b : ℕ → ℝ) (N d : ℕ) (z : ℂ) :
    divisorSignedPartialSum M b (N + d) z - divisorSignedPartialSum M b N z =
      ((divisorSignedPrefix M b (N + d) - divisorSignedPrefix M b N : ℝ) : ℂ) *
          (((N + d + 1 : ℕ) : ℝ) : ℂ) ^ (-z) +
        ∑ j ∈ Finset.range d,
          ((divisorSignedPrefix M b (N + j + 1) - divisorSignedPrefix M b N : ℝ) : ℂ) *
            ((((N + j + 1 : ℕ) : ℝ) : ℂ) ^ (-z) - (((N + j + 2 : ℕ) : ℝ) : ℂ) ^ (-z)) := by
  induction d with
  | zero => simp
  | succ k ih =>
    have hstep_S : divisorSignedPartialSum M b (N + (k + 1)) z =
        divisorSignedPartialSum M b (N + k) z +
          (divisorSignedCoeff M b (N + k + 1) : ℂ) * (((N + k + 1 : ℕ) : ℝ) : ℂ) ^ (-z) := by
      unfold divisorSignedPartialSum
      rw [show N + (k + 1) = (N + k) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ (N + k) + 1)]
    have hstep_C : divisorSignedPrefix M b (N + k + 1) =
        divisorSignedPrefix M b (N + k) + divisorSignedCoeff M b (N + k + 1) := by
      unfold divisorSignedPrefix
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (N + k) + 1)]
    rw [hstep_S, add_sub_right_comm, ih, Finset.sum_range_succ,
      show N + (k + 1) = N + k + 1 by omega, show N + k + 1 + 1 = N + k + 2 by omega, hstep_C]
    push_cast; ring

private theorem divisorSignedPartialSum_eq_sum_divisors (M : ℕ) (b : ℕ → ℝ) (K : ℕ) (z : ℂ) :
    divisorSignedPartialSum M b K z =
      ∑ m ∈ Finset.Icc 1 M, (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z) *
        ∑ k ∈ Finset.Icc 1 (K / m), ((k : ℝ) : ℂ) ^ (-z) := by
  have h1 : ∀ n ∈ Finset.Icc 1 K,
      (divisorSignedCoeff M b n : ℂ) * ((n : ℝ) : ℂ) ^ (-z) =
        ∑ m ∈ Finset.Icc 1 M, if m ∣ n then (b m : ℂ) * ((n : ℝ) : ℂ) ^ (-z) else 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    unfold divisorSignedCoeff
    rw [if_neg hn0, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_filter]
  unfold divisorSignedPartialSum
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm_pos : 0 < m := (Finset.mem_Icc.mp hm).1
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij (fun n _ => n / m) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn_lu, k, rfl⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.mp hn_lu
    have hk1 : 1 ≤ k := by rcases k with _ | k <;> omega
    rw [Nat.mul_div_cancel_left k hm_pos]
    exact Finset.mem_Icc.mpr ⟨hk1, (Nat.le_div_iff_mul_le hm_pos).mpr (by rw [mul_comm]; exact hnK)⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    obtain ⟨_, k₁, rfl⟩ := Finset.mem_filter.mp hn₁
    obtain ⟨_, k₂, rfl⟩ := Finset.mem_filter.mp hn₂
    rw [Nat.mul_div_cancel_left _ hm_pos, Nat.mul_div_cancel_left _ hm_pos] at heq
    rw [heq]
  · intro k hk
    obtain ⟨hk1, hkQ⟩ := Finset.mem_Icc.mp hk
    refine ⟨m * k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right m k⟩,
      Nat.mul_div_cancel_left k hm_pos⟩
    · exact Nat.mul_pos hm_pos hk1
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm_pos).mp hkQ
  · intro n hn
    obtain ⟨_, k, rfl⟩ := Finset.mem_filter.mp hn
    rw [Nat.mul_div_cancel_left k hm_pos, Nat.cast_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg k) (-z), mul_assoc]

/-- **Universal `lcm`-free convergence and `ζ`-free Abel tail theorem for pole-cancelled signed
partial sums:** whenever `∑_{m=1}^M b(m) / m = 0` and `0 < z.re`, `z ≠ 1`:
1. `divisorSignedPartialSum M b K z → divisorPacketPoly M b z * riemannZeta z` as `K → ∞`;
2. At **every** integer cutoff `N ∈ ℕ` (with no `lcm` divisibility restriction),
   `‖divisorPacketPoly M b z * riemannZeta z - divisorSignedPartialSum M b N z‖ ≤ divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re`. -/
theorem norm_divisorSignedSeries_sub_partialSum_le {M : ℕ} {b : ℕ → ℝ}
    (hpole : (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) (N : ℕ) :
    Tendsto (fun K : ℕ => divisorSignedPartialSum M b K z) atTop
        (𝓝 (divisorPacketPoly M b z * riemannZeta z)) ∧
      ‖divisorPacketPoly M b z * riemannZeta z - divisorSignedPartialSum M b N z‖ ≤
        divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re := by
  let g : ℕ → ℂ := fun j =>
    ((divisorSignedPrefix M b (N + j + 1) - divisorSignedPrefix M b N : ℝ) : ℂ) *
      ((((N + j + 1 : ℕ) : ℝ) : ℂ) ^ (-z) - (((N + j + 2 : ℕ) : ℝ) : ℂ) ^ (-z))
  have hg_bound : ∀ j : ℕ, ‖g j‖ ≤
      divisorPacketL1 M b * (‖z‖ / z.re) *
        (occupationWeight (N + j) ^ z.re - occupationWeight (N + j + 1) ^ z.re) := by
    intro j
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hosc := divisorSignedPrefix_diff_abs_le hpole (N + j + 1) N
    have hdiff_eq : (((N + j + 1 : ℕ) : ℝ) : ℂ) ^ (-z) - (((N + j + 2 : ℕ) : ℝ) : ℂ) ^ (-z) =
        (occupationWeight (N + j) : ℂ) ^ z - (occupationWeight (N + j + 1) : ℂ) ^ z := by
      rw [occ_cpow_eq_neg_cpow (N + j) z, occ_cpow_eq_neg_cpow (N + j + 1) z]
      push_cast; ring_nf
    rw [hdiff_eq]
    have hch := norm_thermal_chord (occupationWeight_pos (N + j + 1))
      (occupationWeight_antitone (Nat.le_succ (N + j))) (occupation_in_unit (N + j)).2 hz0 le_rfl
    calc |divisorSignedPrefix M b (N + j + 1) - divisorSignedPrefix M b N| *
            ‖(occupationWeight (N + j) : ℂ) ^ z - (occupationWeight (N + j + 1) : ℂ) ^ z‖
        ≤ divisorPacketL1 M b *
            ((‖z‖ / z.re) * (occupationWeight (N + j) ^ z.re - occupationWeight (N + j + 1) ^ z.re)) :=
          mul_le_mul hosc hch (norm_nonneg _) ((abs_nonneg _).trans hosc)
      _ = divisorPacketL1 M b * (‖z‖ / z.re) *
            (occupationWeight (N + j) ^ z.re - occupationWeight (N + j + 1) ^ z.re) := by ring
  have hL1_nn : 0 ≤ divisorPacketL1 M b := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum_g : Summable (fun j : ℕ => ‖g j‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hg_bound
      (Summable.mul_left _ (summable_of_sum_range_le (c := occupationWeight N ^ z.re)
        (fun j => sub_nonneg.mpr
          (Real.rpow_le_rpow (occupationWeight_pos _).le
            (occupationWeight_antitone (Nat.le_succ _)) hz0.le)) fun D => ?_))
    have ht := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (N + j) ^ z.re) D
    simp only [Nat.add_zero, ← Nat.add_assoc] at ht
    rw [ht]
    linarith [Real.rpow_nonneg (occupationWeight_pos (N + D)).le z.re]
  have htsum_le : ‖∑' j : ℕ, g j‖ ≤
      divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re := by
    refine (norm_tsum_le_tsum_norm hsum_g).trans
      (le_of_tendsto hsum_g.hasSum.tendsto_sum_nat (Eventually.of_forall fun D => ?_))
    calc (∑ j ∈ Finset.range D, ‖g j‖)
        ≤ (divisorPacketL1 M b * (‖z‖ / z.re)) *
            ∑ j ∈ Finset.range D,
              (occupationWeight (N + j) ^ z.re - occupationWeight (N + j + 1) ^ z.re) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ => hg_bound j
      _ ≤ divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have ht := Finset.sum_range_sub' (fun j : ℕ => occupationWeight (N + j) ^ z.re) D
          simp only [Nat.add_zero, ← Nat.add_assoc] at ht
          rw [ht]
          linarith [Real.rpow_nonneg (occupationWeight_pos (N + D)).le z.re]
  have hbnd_zero : Tendsto
      (fun d : ℕ => ((divisorSignedPrefix M b (N + d) - divisorSignedPrefix M b N : ℝ) : ℂ) *
        (((N + d + 1 : ℕ) : ℝ) : ℂ) ^ (-z)) atTop (𝓝 0) := by
    have hnorm_zero : Tendsto (fun d : ℕ => divisorPacketL1 M b * ((N + d + 1 : ℕ) : ℝ) ^ (-z.re))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun d : ℕ => ((d : ℝ) + ((N + 1 : ℕ) : ℝ)) ^ (-z.re)) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop hz0).comp
          (tendsto_atTop_add_const_right atTop ((N + 1 : ℕ) : ℝ) tendsto_natCast_atTop_atTop)
      simpa only [mul_zero] using (h0.congr fun d => by push_cast; ring_nf).const_mul (divisorPacketL1 M b)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) hnorm_zero)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (N + d + 1 : ℕ)),
      Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (divisorSignedPrefix_diff_abs_le hpole (N + d) N)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have htend_shift : Tendsto (fun d : ℕ => divisorSignedPartialSum M b (N + d) z) atTop
      (𝓝 (divisorSignedPartialSum M b N z + ∑' j : ℕ, g j)) := by
    have hdiff := hbnd_zero.add hsum_g.of_norm.hasSum.tendsto_sum_nat
    rw [zero_add] at hdiff
    have hcongr : (fun d : ℕ => divisorSignedPartialSum M b (N + d) z -
          divisorSignedPartialSum M b N z) =
        fun d : ℕ => ((divisorSignedPrefix M b (N + d) - divisorSignedPrefix M b N : ℝ) : ℂ) *
          (((N + d + 1 : ℕ) : ℝ) : ℂ) ^ (-z) + ∑ j ∈ Finset.range d, g j :=
      funext fun d => abel_tail_finite_identity M b N d z
    rw [← hcongr] at hdiff
    simpa only [add_sub_cancel] using hdiff.const_add (divisorSignedPartialSum M b N z)
  have htend_full : Tendsto (fun K : ℕ => divisorSignedPartialSum M b K z) atTop
      (𝓝 (divisorSignedPartialSum M b N z + ∑' j : ℕ, g j)) := by
    rw [← tendsto_add_atTop_iff_nat N]
    simpa only [Nat.add_comm _ N] using htend_shift
  set F_fac : ℕ := M.factorial
  have hF_pos : 0 < F_fac := Nat.factorial_pos M
  have hsubseq_lim : Tendsto (fun L : ℕ => divisorSignedPartialSum M b (F_fac * (L + 1)) z) atTop
      (𝓝 (divisorPacketPoly M b z * riemannZeta z)) := by
    have h1m_ne : (1 : ℂ) - z ≠ 0 := fun h => hz1 (by linear_combination -h)
    have hrew : ∀ L : ℕ, divisorSignedPartialSum M b (F_fac * (L + 1)) z =
        ∑ m ∈ Finset.Icc 1 M, (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z) *
          ((∑ k ∈ Finset.Icc 1 ((F_fac / m) * (L + 1)), ((k : ℝ) : ℂ) ^ (-z)) -
            ((((F_fac / m) * (L + 1) : ℕ) : ℝ) : ℂ) ^ (1 - z) / (1 - z)) := by
      intro L
      rw [divisorSignedPartialSum_eq_sum_divisors]
      have hdiv_eq : ∀ m ∈ Finset.Icc 1 M, (F_fac * (L + 1)) / m = (F_fac / m) * (L + 1) := by
        intro m hm
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
        obtain ⟨q, hq⟩ := Nat.dvd_factorial hm1 hmM
        dsimp only [F_fac]
        rw [hq, Nat.mul_assoc, Nat.mul_div_cancel_left _ hm1, Nat.mul_div_cancel_left _ hm1]
      have hsum1 : (∑ m ∈ Finset.Icc 1 M, (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z) *
            ∑ k ∈ Finset.Icc 1 (F_fac * (L + 1) / m), ((k : ℝ) : ℂ) ^ (-z)) =
          ∑ m ∈ Finset.Icc 1 M, (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z) *
            ∑ k ∈ Finset.Icc 1 ((F_fac / m) * (L + 1)), ((k : ℝ) : ℂ) ^ (-z) :=
        Finset.sum_congr rfl fun m hm => by rw [hdiv_eq m hm]
      have hpole_term : (∑ m ∈ Finset.Icc 1 M,
          (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z) *
            (((((F_fac / m) * (L + 1) : ℕ) : ℝ) : ℂ) ^ (1 - z) / (1 - z))) = 0 := by
        have hcongr : ∀ m ∈ Finset.Icc 1 M,
            (b m : ℂ) * ((m : ℝ) : ℂ) ^ (-z) *
              (((((F_fac / m) * (L + 1) : ℕ) : ℝ) : ℂ) ^ (1 - z) / (1 - z)) =
            (((b m / (m : ℝ) : ℝ) : ℂ)) *
              ((((F_fac * (L + 1) : ℕ) : ℝ) : ℂ) ^ (1 - z) / (1 - z)) := by
          intro m hm
          obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
          obtain ⟨q, hq⟩ := Nat.dvd_factorial hm1 hmM
          have hquot_eq : (((F_fac / m) * (L + 1) : ℕ) : ℝ) * (m : ℝ) =
              ((F_fac * (L + 1) : ℕ) : ℝ) := by
            have : ((F_fac / m) * (L + 1)) * m = F_fac * (L + 1) := by
              dsimp only [F_fac]
              rw [hq, Nat.mul_div_cancel_left _ hm1]; ring
            exact_mod_cast this
          have hm_r_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm1
          have hm_c_ne : ((m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm_r_pos.ne'
          have hm_split : ((m : ℝ) : ℂ) ^ (1 - z) = ((m : ℝ) : ℂ) * ((m : ℝ) : ℂ) ^ (-z) := by
            rw [show (1 - z : ℂ) = 1 + (-z) by ring, Complex.cpow_add _ _ hm_c_ne, Complex.cpow_one]
          have hmul_cpow : ((((F_fac * (L + 1) : ℕ) : ℝ) : ℂ)) ^ (1 - z) =
              ((((F_fac / m) * (L + 1) : ℕ) : ℝ) : ℂ) ^ (1 - z) *
                (((m : ℝ) : ℂ) * ((m : ℝ) : ℂ) ^ (-z)) := by
            rw [← hquot_eq, Complex.ofReal_mul,
              Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (1 - z),
              hm_split]
          rw [Complex.ofReal_div, hmul_cpow]
          field_simp [hm_c_ne, h1m_ne]
        rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, ← Complex.ofReal_sum, hpole,
          Complex.ofReal_zero, zero_mul]
      rw [hsum1, ← sub_zero (∑ m ∈ Finset.Icc 1 M, _), ← hpole_term, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simp_rw [hrew]
    unfold divisorPacketPoly
    rw [Finset.sum_mul]
    refine tendsto_finsetSum _ fun m hm => ?_
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have hq_pos : 0 < F_fac / m := Nat.div_pos (Nat.le_of_dvd hF_pos (Nat.dvd_factorial hm1 hmM)) hm1
    have hidx_top : Tendsto (fun L : ℕ => (F_fac / m) * (L + 1)) atTop atTop :=
      tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left (L + 1) hq_pos) (tendsto_add_atTop_nat 1)
    exact ((_root_.RHTower.tendsto_sum_cpow_sub_pow hz0 hz1).comp hidx_top).const_mul _
  have hsubseq_full : Tendsto (fun L : ℕ => divisorSignedPartialSum M b (F_fac * (L + 1)) z) atTop
      (𝓝 (divisorSignedPartialSum M b N z + ∑' j : ℕ, g j)) :=
    htend_full.comp (tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left (L + 1) hF_pos)
      (tendsto_add_atTop_nat 1))
  have hid := tendsto_nhds_unique hsubseq_lim hsubseq_full
  rw [← hid] at htend_full
  refine ⟨htend_full, ?_⟩
  rw [hid, add_sub_cancel_left]
  exact htsum_le

/-- **Sufficiency of any pole-cancelled signed partial sum beating its `lcm`-free Abel tail:**
if `∑_{m=1}^M b(m) / m = 0` and at a single cutoff `N : ℕ` the partial sum strictly beats
`divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re`, then `riemannZeta z ≠ 0` and
`divisorPacketPoly M b z ≠ 0`. -/
theorem zeta_ne_zero_of_divisorSignedPartialSum_beats_tail {M : ℕ} {b : ℕ → ℝ}
    (hpole : (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) {N : ℕ}
    (hbeat : divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re <
      ‖divisorSignedPartialSum M b N z‖) :
    riemannZeta z ≠ 0 ∧ divisorPacketPoly M b z ≠ 0 := by
  have htb := (norm_divisorSignedSeries_sub_partialSum_le hpole hz0 hz1 N).2
  have hprod_ne : divisorPacketPoly M b z * riemannZeta z ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg] at htb
    linarith
  exact ⟨right_ne_zero_of_mul hprod_ne, left_ne_zero_of_mul hprod_ne⟩

/-- **Universal zero-point ceiling across ALL pole-cancelled signed partial sums:**
if `riemannZeta ρ = 0` (`0 < ρ.re`, `ρ ≠ 1`), then for **every** `M : ℕ`, **every** `b : ℕ → ℝ`
satisfying `∑_{m=1}^M b(m) / m = 0`, and **every** `N : ℕ`,
`‖divisorSignedPartialSum M b N ρ‖ ≤ divisorPacketL1 M b * (‖ρ‖ / ρ.re) * occupationWeight N ^ ρ.re`. -/
theorem norm_divisorSignedPartialSum_le_tail_of_zeta_eq_zero
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0)
    (M : ℕ) {b : ℕ → ℝ} (hpole : (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0) (N : ℕ) :
    ‖divisorSignedPartialSum M b N ρ‖ ≤
      divisorPacketL1 M b * (‖ρ‖ / ρ.re) * occupationWeight N ^ ρ.re := by
  have htb := (norm_divisorSignedSeries_sub_partialSum_le hpole hρ0 hρ1 N).2
  rwa [hz, mul_zero, zero_sub, norm_neg] at htb

/-! ### Part 3: Reflected Möbius-sieved divisor packets and zero-exception coverage through height `184` -/

/-- Truncated real Möbius weight supported on `{1, ..., R}`. -/
def moebiusTrunc (R d : ℕ) : ℝ :=
  if 1 ≤ d ∧ d ≤ R then (ArithmeticFunction.moebius d : ℝ) else 0

/-- Pole-cancelled Möbius-sieved Dirichlet-eta divisor packet `(δ_1 - 2 δ_2) * μ_{≤ R}` supported
on `{1, ..., 2 R}`. -/
def moebiusSievedEtaPacket (R m : ℕ) : ℝ :=
  moebiusTrunc R m - if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0

private theorem sum_moebius_divisors_eq_ite {k R : ℕ} (hk1 : 1 ≤ k) (hkR : k ≤ R) :
    (∑ d ∈ (Finset.Icc 1 (2 * R)).filter (· ∣ k), moebiusTrunc R d) =
      if k = 1 then 1 else 0 := by
  have hsub : k.divisors = (Finset.Icc 1 (2 * R)).filter (fun d => d ∣ k ∧ 1 ≤ d ∧ d ≤ R) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdk, hk0⟩
      have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdk (by omega)
      have hd_le : d ≤ k := Nat.le_of_dvd (by omega) hdk
      exact ⟨⟨hd_pos, by omega⟩, hdk, hd_pos, hd_le.trans hkR⟩
    · rintro ⟨_, hdk, _, _⟩
      exact ⟨hdk, by omega⟩
  have hrew : (∑ d ∈ (Finset.Icc 1 (2 * R)).filter (· ∣ k), moebiusTrunc R d) =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    rw [hsub]
    unfold moebiusTrunc
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h1 : d ∣ k
    · by_cases h2 : 1 ≤ d ∧ d ≤ R <;> simp [h1, h2]
    · simp [h1]
  rw [hrew]
  simp_rw [← ArithmeticFunction.intCoe_apply (R := ℝ) (f := ArithmeticFunction.moebius)]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

/-- **Exact pole cancellation, `3 R` `ℓ¹` bound, and `[3, R]` head annihilation of
`moebiusSievedEtaPacket R` (`R ≥ 2`):**
1. `∑_{m=1}^{2R} moebiusSievedEtaPacket R m / m = 0`;
2. `divisorPacketL1 (2 * R) (moebiusSievedEtaPacket R) ≤ 3 * R`;
3. `divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) 1 = 1`,
   `divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) 2 = -2`, and
   `divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) n = 0` for all `3 ≤ n ≤ R`. -/
theorem moebiusSievedEtaPacket_properties {R : ℕ} (hR : 2 ≤ R) :
    (∑ m ∈ Finset.Icc 1 (2 * R), moebiusSievedEtaPacket R m / (m : ℝ)) = 0 ∧
    divisorPacketL1 (2 * R) (moebiusSievedEtaPacket R) ≤ 3 * (R : ℝ) ∧
    divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) 1 = 1 ∧
    divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) 2 = -2 ∧
    (∀ n : ℕ, 3 ≤ n → n ≤ R → divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) n = 0) := by
  have hs1 : (∑ m ∈ Finset.Icc 1 (2 * R), moebiusTrunc R m / (m : ℝ)) =
      ∑ d ∈ Finset.Icc 1 R, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : R ≤ 2 * R))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [moebiusTrunc, if_pos (Finset.mem_Icc.mp hd)]
    · intro m hm hnot
      rw [Finset.mem_Icc] at hm hnot
      rw [moebiusTrunc, if_neg (by omega), zero_div]
  have hs2 : (∑ m ∈ Finset.Icc 1 (2 * R),
        (if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0) / (m : ℝ)) =
      ∑ d ∈ Finset.Icc 1 R, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
    have hsplit : ∀ m : ℕ, (if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0) / (m : ℝ) =
        if 2 ∣ m then (2 * moebiusTrunc R (m / 2)) / (m : ℝ) else 0 := fun m => by
      split_ifs <;> simp
    simp_rw [hsplit]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun m _ => m / 2) ?_ ?_ ?_ ?_
    · intro m hm
      obtain ⟨hlu, k, rfl⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hm2R⟩ := Finset.mem_Icc.mp hlu
      rw [Nat.mul_div_cancel_left k two_pos]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      obtain ⟨_, k₁, rfl⟩ := Finset.mem_filter.mp hm₁
      obtain ⟨_, k₂, rfl⟩ := Finset.mem_filter.mp hm₂
      rw [Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos] at heq
      rw [heq]
    · intro d hd
      obtain ⟨hd1, hdR⟩ := Finset.mem_Icc.mp hd
      exact ⟨2 * d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, dvd_mul_right 2 d⟩,
        Nat.mul_div_cancel_left d two_pos⟩
    · intro m hm
      obtain ⟨hlu, k, rfl⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hm2R⟩ := Finset.mem_Icc.mp hlu
      have hk1 : 1 ≤ k := by omega
      have hkR : k ≤ R := by omega
      have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Nat.mul_div_cancel_left k two_pos, moebiusTrunc, if_pos ⟨hk1, hkR⟩, Nat.cast_mul,
        Nat.cast_ofNat]
      field_simp [hk_ne]
  have hpole : (∑ m ∈ Finset.Icc 1 (2 * R), moebiusSievedEtaPacket R m / (m : ℝ)) = 0 := by
    unfold moebiusSievedEtaPacket
    simp_rw [sub_div]
    rw [Finset.sum_sub_distrib, hs1, hs2, sub_self]
  have habs_mu : ∀ d : ℕ, |moebiusTrunc R d| ≤ if 1 ≤ d ∧ d ≤ R then 1 else 0 := fun d => by
    unfold moebiusTrunc
    split_ifs with h
    · by_cases hsq : Squarefree d
      · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, Int.cast_pow, Int.cast_neg,
          Int.cast_one, abs_pow, abs_neg, abs_one, one_pow]
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero, abs_zero]
        exact zero_le_one
    · rw [abs_zero]
  have hl1 : divisorPacketL1 (2 * R) (moebiusSievedEtaPacket R) ≤ 3 * (R : ℝ) := by
    unfold divisorPacketL1 moebiusSievedEtaPacket
    have htri : (∑ m ∈ Finset.Icc 1 (2 * R),
          |moebiusTrunc R m - if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0|) ≤
        (∑ m ∈ Finset.Icc 1 (2 * R), |moebiusTrunc R m|) +
          ∑ m ∈ Finset.Icc 1 (2 * R), |if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun m _ => abs_sub _ _
    have hb1 : (∑ m ∈ Finset.Icc 1 (2 * R), |moebiusTrunc R m|) ≤ (R : ℝ) := by
      calc (∑ m ∈ Finset.Icc 1 (2 * R), |moebiusTrunc R m|)
          ≤ ∑ m ∈ Finset.Icc 1 (2 * R), (if 1 ≤ m ∧ m ≤ R then (1 : ℝ) else 0) :=
            Finset.sum_le_sum fun m _ => habs_mu m
        _ = ∑ m ∈ Finset.Icc 1 R, (1 : ℝ) := by
            rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : R ≤ 2 * R))]
            · exact Finset.sum_congr rfl fun m hm => if_pos (Finset.mem_Icc.mp hm)
            · intro m hm hnot; rw [Finset.mem_Icc] at hm hnot; exact if_neg (by omega)
        _ = (R : ℝ) := by simp
    have hb2 : (∑ m ∈ Finset.Icc 1 (2 * R), |if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0|) ≤
        2 * (R : ℝ) := by
      have hrew2 : (∑ m ∈ Finset.Icc 1 (2 * R), |if 2 ∣ m then 2 * moebiusTrunc R (m / 2) else 0|) =
          ∑ m ∈ (Finset.Icc 1 (2 * R)).filter (fun m => 2 ∣ m), 2 * |moebiusTrunc R (m / 2)| := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs
        · rw [abs_mul, abs_of_nonneg zero_le_two]
        · rw [abs_zero]
      rw [hrew2]
      have hbij : (∑ m ∈ (Finset.Icc 1 (2 * R)).filter (fun m => 2 ∣ m), 2 * |moebiusTrunc R (m / 2)|) =
          ∑ d ∈ Finset.Icc 1 R, 2 * |moebiusTrunc R d| := by
        refine Finset.sum_bij (fun m _ => m / 2) ?_ ?_ ?_ ?_
        · intro m hm
          obtain ⟨hlu, k, rfl⟩ := Finset.mem_filter.mp hm
          obtain ⟨_, hm2R⟩ := Finset.mem_Icc.mp hlu
          rw [Nat.mul_div_cancel_left k two_pos]
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro m₁ hm₁ m₂ hm₂ heq
          obtain ⟨_, k₁, rfl⟩ := Finset.mem_filter.mp hm₁
          obtain ⟨_, k₂, rfl⟩ := Finset.mem_filter.mp hm₂
          rw [Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos] at heq
          rw [heq]
        · intro d hd
          obtain ⟨hd1, hdR⟩ := Finset.mem_Icc.mp hd
          exact ⟨2 * d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, dvd_mul_right 2 d⟩,
            Nat.mul_div_cancel_left d two_pos⟩
        · intro _ _; rfl
      rw [hbij]
      calc (∑ d ∈ Finset.Icc 1 R, 2 * |moebiusTrunc R d|)
          ≤ ∑ d ∈ Finset.Icc 1 R, (2 : ℝ) := by
            refine Finset.sum_le_sum fun d hd => ?_
            have h := habs_mu d
            rw [if_pos (Finset.mem_Icc.mp hd)] at h
            linarith
        _ = 2 * (R : ℝ) := by simp [mul_comm]
    linarith
  have hcoeff_formula : ∀ n : ℕ, 1 ≤ n → n ≤ R →
      divisorSignedCoeff (2 * R) (moebiusSievedEtaPacket R) n =
        (if n = 1 then 1 else 0) - if 2 ∣ n then 2 * (if n / 2 = 1 then 1 else 0) else 0 := by
    intro n hn1 hnR
    unfold divisorSignedCoeff moebiusSievedEtaPacket
    rw [if_neg (by omega : n ≠ 0), Finset.sum_sub_distrib, sum_moebius_divisors_eq_ite hn1 hnR]
    congr 1
    by_cases h2n : 2 ∣ n
    · obtain ⟨q, rfl⟩ := h2n
      have hq1 : 1 ≤ q := by omega
      have hqR : q ≤ R := by omega
      rw [if_pos (dvd_mul_right 2 q), Nat.mul_div_cancel_left q two_pos, ← Finset.sum_filter]
      have hbij : (∑ m ∈ ((Finset.Icc 1 (2 * R)).filter (· ∣ 2 * q)).filter (fun m => 2 ∣ m),
            2 * moebiusTrunc R (m / 2)) =
          2 * ∑ d ∈ (Finset.Icc 1 (2 * R)).filter (· ∣ q), moebiusTrunc R d := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun m _ => m / 2) ?_ ?_ ?_ ?_
        · intro m hm
          obtain ⟨hm_div, k, rfl⟩ := Finset.mem_filter.mp hm
          obtain ⟨hlu, h2k_2q⟩ := Finset.mem_filter.mp hm_div
          rw [Nat.mul_div_cancel_left k two_pos]
          have hk_dvd : k ∣ q := (Nat.mul_dvd_mul_iff_left two_pos).mp h2k_2q
          have hk1 : 1 ≤ k := Nat.pos_of_dvd_of_pos hk_dvd hq1
          have hk_le : k ≤ q := Nat.le_of_dvd hq1 hk_dvd
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, by omega⟩, hk_dvd⟩
        · intro m₁ hm₁ m₂ hm₂ heq
          obtain ⟨_, k₁, rfl⟩ := Finset.mem_filter.mp hm₁
          obtain ⟨_, k₂, rfl⟩ := Finset.mem_filter.mp hm₂
          rw [Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos] at heq
          rw [heq]
        · intro d hd
          obtain ⟨_, hd_q⟩ := Finset.mem_filter.mp hd
          have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_q hq1
          have hd_le : d ≤ q := Nat.le_of_dvd hq1 hd_q
          exact ⟨2 * d, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Nat.mul_dvd_mul_left 2 hd_q⟩,
            dvd_mul_right 2 d⟩, Nat.mul_div_cancel_left d two_pos⟩
        · intro _ _; rfl
      rw [hbij, sum_moebius_divisors_eq_ite hq1 hqR]
    · rw [if_neg h2n]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hmn : m ∣ n := (Finset.mem_filter.mp hm).2
      have hnot2m : ¬ 2 ∣ m := fun h2m => h2n (dvd_trans h2m hmn)
      rw [if_neg hnot2m]
  refine ⟨hpole, hl1, ?_, ?_, fun n hn3 hnR => ?_⟩
  · rw [hcoeff_formula 1 le_rfl (by omega)]; norm_num
  · rw [hcoeff_formula 2 (by norm_num) hR]; norm_num
  · rw [hcoeff_formula n (by omega) hnR, if_neg (by omega : n ≠ 1)]
    by_cases h2n : 2 ∣ n
    · obtain ⟨q, rfl⟩ := h2n
      rw [if_pos (dvd_mul_right 2 q), Nat.mul_div_cancel_left q two_pos, if_neg (by omega : q ≠ 1)]
      norm_num
    · rw [if_neg h2n, sub_zero]

/-- **Off-line nonvanishing of `riemannZeta` and `continued` across `|Im s| ≤ 184`:** -/
theorem riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hne_half : s.re ≠ 1 / 2) (him : |s.im| ≤ 184) :
    riemannZeta s ≠ 0 ∧ continued s ≠ 0 := by
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  have hζ : riemannZeta s ≠ 0 := by
    intro h0
    have hxi : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff hs0 hs_ne1).mpr h0
    have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
      VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_oneHundredEightyFour hxi hs0 hs1 hne_half
    linarith
  have h2_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := (factor_zero_iff s).mp h0
    exact hs0.ne' ((congrArg Complex.re hk).trans (frequency_re k))
  exact ⟨hζ, mul_ne_zero h2_ne hζ⟩

/-- Exact equivalence at every strip point `0 < Re z < 1` between `riemannZeta z ≠ 0` and existence
of a pole-cancelled `ζ`-divisible signed partial sum beating its `lcm`-free Abel tail. -/
theorem exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    (∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
      (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
      divisorPacketL1 M b * (‖z‖ / z.re) * occupationWeight N ^ z.re <
        ‖divisorSignedPartialSum M b N z‖) ↔
      riemannZeta z ≠ 0 := by
  have hzne1 : z ≠ 1 := fun h => hz1.ne (by rw [h, Complex.one_re])
  constructor
  · rintro ⟨M, b, N, hpole, hbeat⟩
    exact (zeta_ne_zero_of_divisorSignedPartialSum_beats_tail hpole hz0 hzne1 hbeat).1
  · intro hζ
    let b₂ : ℕ → ℝ := fun m => if m = 1 then 1 else if m = 2 then -2 else 0
    have hpole₂ : (∑ m ∈ Finset.Icc 1 2, b₂ m / (m : ℝ)) = 0 := by
      have : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
      rw [this]; norm_num [b₂]
    have hpoly₂ : divisorPacketPoly 2 b₂ z = 1 - (2 : ℂ) ^ (1 - z) := by
      have : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
      unfold divisorPacketPoly
      rw [this, Finset.sum_pair (by norm_num)]
      dsimp only [b₂]
      norm_num
      have h2_pow : (2 : ℂ) * (2 : ℂ) ^ (-z) = (2 : ℂ) ^ (1 - z) := by
        rw [show (1 - z : ℂ) = 1 + (-z) by ring, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
      rw [← h2_pow]; ring
    have h1m2_ne : 1 - (2 : ℂ) ^ (1 - z) ≠ 0 := by
      intro h0
      have h2_gt1 : (1 : ℝ) < (2 : ℝ) ^ (1 - z.re) := Real.one_lt_rpow one_lt_two (sub_pos.mpr hz1)
      have hn : ‖(2 : ℂ) ^ (1 - z)‖ = (2 : ℝ) ^ (1 - z.re) := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
          Complex.sub_re, Complex.one_re]
      have h := norm_sub_norm_le ((2 : ℂ) ^ (1 - z)) 1
      rw [norm_sub_rev, h0, norm_zero, hn, norm_one] at h
      linarith
    have hlim_pos : 0 < ‖divisorPacketPoly 2 b₂ z * riemannZeta z‖ := by
      rw [hpoly₂]
      exact norm_pos_iff.mpr (mul_ne_zero h1m2_ne hζ)
    have htend : Tendsto (fun N : ℕ => divisorPacketL1 2 b₂ * (‖z‖ / z.re) * occupationWeight N ^ z.re)
        atTop (𝓝 0) := by
      have hocc : Tendsto (fun N : ℕ => occupationWeight N ^ z.re) atTop (𝓝 0) := by
        have h0 : Tendsto (fun N : ℕ => (((N : ℝ) + 1) : ℝ) ^ (-z.re)) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop hz0).comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
        refine h0.congr fun N => ?_
        have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        rw [occupationWeight_eq, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
      simpa only [mul_zero] using hocc.const_mul _
    obtain ⟨N, hN_lt⟩ := (htend.eventually (gt_mem_nhds (half_pos hlim_pos))).exists
    have htb := (norm_divisorSignedSeries_sub_partialSum_le hpole₂ hz0 hzne1 N).2
    have htri : ‖divisorPacketPoly 2 b₂ z * riemannZeta z‖ ≤
        ‖divisorSignedPartialSum 2 b₂ N z‖ +
          ‖divisorPacketPoly 2 b₂ z * riemannZeta z - divisorSignedPartialSum 2 b₂ N z‖ := by
      simpa only [add_sub_cancel] using norm_add_le (divisorSignedPartialSum 2 b₂ N z)
        (divisorPacketPoly 2 b₂ z * riemannZeta z - divisorSignedPartialSum 2 b₂ N z)
    exact ⟨2, b₂, N, hpole₂, by linarith⟩

/-- **Complete zero-exception elimination across `{3001/24000 ≤ Re s < 1/2 ∧ 150 < |Im s| ≤ 184}`:**
every single point in this band (zero isolated zeros permitted) carries a simultaneous UV-capped and
uncapped finite-eigenvalue witness `(v, K)`, a `hotEdge 1` Dirichlet-eta margin, a pole-cancelled
signed partial sum beating its `lcm`-free tail at `s`, and an accelerated reflected pole-cancelled
signed partial sum beating its `lcm`-free tail at `1 - conj s`. -/
theorem zero_exception_band_oneHundredFifty_to_oneHundredEightyFour
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2)
    (_him_lo : 150 < |s.im|) (him_hi : |s.im| ≤ 184) {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ)
      (M₁ : ℕ) (b₁ : ℕ → ℝ) (N₁ : ℕ) (M₂ : ℕ) (b₂ : ℕ → ℝ) (N₂ : ℕ),
      uvRegularRankOne s hs0 Λ v ∧
      (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ ∧
      (chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s <
        ‖finiteTriadReading (missingWaveSpectrum v) K s‖ ∧
      (∑ m ∈ Finset.Icc 1 M₁, b₁ m / (m : ℝ)) = 0 ∧
      divisorPacketL1 M₁ b₁ * (‖s‖ / s.re) * occupationWeight N₁ ^ s.re <
        ‖divisorSignedPartialSum M₁ b₁ N₁ s‖ ∧
      (∑ m ∈ Finset.Icc 1 M₂, b₂ m / (m : ℝ)) = 0 ∧
      divisorPacketL1 M₂ b₂ * (‖1 - conj s‖ / (1 - s.re)) * occupationWeight N₂ ^ (1 - s.re) <
        ‖divisorSignedPartialSum M₂ b₂ N₂ (1 - conj s)‖ := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  obtain ⟨hζ_s, hcs_s⟩ := riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
    hs0 hs1 hhi.ne him_hi
  obtain ⟨v, K, huv, hcap, huncap⟩ :=
    exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ
      (div_pos (norm_pos_iff.mpr hcs_s) two_pos)
  obtain ⟨M₁, b₁, N₁, hp₁, hb₁⟩ :=
    (exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).mpr hζ_s
  set w : ℂ := 1 - conj s
  have hw_re : w.re = 1 - s.re := by simp [w]
  have hw0 : 0 < w.re := by linarith
  have hw1 : w.re < 1 := by linarith
  have hw_gt_half : 1 / 2 < w.re := by linarith
  have hw_im : |w.im| ≤ 184 := by
    have : w.im = s.im := by simp [w]
    rwa [this]
  have hζ_w := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
    hw0 hw1 hw_gt_half.ne' hw_im).1
  obtain ⟨M₂, b₂, N₂, hp₂, hb₂⟩ :=
    (exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hw0 hw1).mpr hζ_w
  rw [hw_re] at hb₂
  have hcs_pos : 0 < ‖continued s‖ := norm_pos_iff.mpr hcs_s
  exact ⟨hs0, v, K, M₁, b₁, N₁, M₂, b₂, N₂, huv, by linarith, by linarith, hp₁, hb₁, hp₂, hb₂⟩

/-- **Unconditional advance of the `RiemannHypothesis` frontier to `|Im s| > 184` and equivalence
with pole-cancelled signed partial sums (direct at `s` and reflected at `1 - conj s`):** -/
theorem rh_iff_exists_divisorSigned_partialSum_above_oneHundredEightyFour
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne s hs0 Λ v ∧
            (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
              ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖s‖ / s.re) * occupationWeight N ^ s.re <
            ‖divisorSignedPartialSum M b N s‖) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖1 - conj s‖ / (1 - s.re)) * occupationWeight N ^ (1 - s.re) <
            ‖divisorSignedPartialSum M b N (1 - conj s)‖) := by
  obtain ⟨hcap150, _, _⟩ := rh_iff_exists_finite_eigenvalue_witness_above_oneHundredFifty hΛ
  have hcap184 : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne s hs0 Λ v ∧
            (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
              ‖finiteTriadReading (missingWaveSpectrum v) K s‖ := by
    rw [hcap150]
    constructor
    · intro hall s hlo hhi him184
      exact hall s hlo hhi (by linarith)
    · intro hall s hlo hhi him150
      rcases le_or_gt |s.im| 184 with hle184 | hgt184
      · obtain ⟨hs0, v, K, _, _, _, _, _, _, huv, hcap, _, _, _, _, _⟩ :=
          zero_exception_band_oneHundredFifty_to_oneHundredEightyFour hlo hhi him150 hle184 hΛ
        exact ⟨hs0, v, K, huv, hcap⟩
      · exact hall s hlo hhi hgt184
  have hzeta_iff_refl : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      (riemannZeta s ≠ 0 ↔ riemannZeta (1 - conj s) ≠ 0) := by
    intro s hs0 hs1
    set w : ℂ := 1 - conj s
    have hw0 : 0 < w.re := by simp [w]; linarith
    have hw1 : w.re < 1 := by simp [w]; linarith
    have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
    have hw_ne1 : w ≠ 1 := fun h => hw1.ne (by rw [h, Complex.one_re])
    have hxi_symm : _root_.RHTower.xi w = conj (_root_.RHTower.xi s) :=
      (_root_.RHTower.xi_one_sub (conj s)).trans (_root_.RHTower.xi_conj s)
    simp only [ne_eq, ← _root_.RHTower.xi_eq_zero_iff hs0 hs_ne1,
      ← _root_.RHTower.xi_eq_zero_iff hw0 hw_ne1, hxi_symm, map_eq_zero]
  have hdir184 : (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (hs0 : 0 < s.re) (v : MissingWave) (K : ℕ),
          uvRegularRankOne s hs0 Λ v ∧
            (uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s <
              ‖finiteTriadReading (missingWaveSpectrum v) K s‖) ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖s‖ / s.re) * occupationWeight N ^ s.re <
            ‖divisorSignedPartialSum M b N s‖ := by
    refine forall₄_congr fun s hlo hhi _ => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have h2_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := (factor_zero_iff s).mp h0
      exact hs0.ne' ((congrArg Complex.re hk).trans (frequency_re k))
    have hcs_iff_ζ : continued s ≠ 0 ↔ riemannZeta s ≠ 0 :=
      ⟨right_ne_zero_of_mul, mul_ne_zero h2_ne⟩
    constructor
    · rintro ⟨_, v, K, huv, hcap⟩
      have hhot := (exists_finite_witness_iff_hotEdge_beats_tail hs0 hs1 hΛ).1.mp ⟨v, K, huv, hcap⟩
      obtain ⟨K', hK'⟩ := hhot
      have htb := norm_jointSurviving_sub_finiteTriadReading_le (hotEdge 1) K' hs0 hs1.ne
      rw [jointSurvivingPartition_hot] at htb
      have hcs : continued s ≠ 0 := by
        intro h0; rw [h0, zero_sub, norm_neg] at htb; linarith
      exact (exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).mpr
        (hcs_iff_ζ.mp hcs)
    · intro hdiv
      have hcs : continued s ≠ 0 :=
        hcs_iff_ζ.mpr ((exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).mp hdiv)
      obtain ⟨v, K, huv, h1, _⟩ :=
        exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ
          (div_pos (norm_pos_iff.mpr hcs) two_pos)
      have hcs_pos : 0 < ‖continued s‖ := norm_pos_iff.mpr hcs
      exact ⟨hs0, v, K, huv, by linarith⟩
  have hrefl184 : (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖s‖ / s.re) * occupationWeight N ^ s.re <
            ‖divisorSignedPartialSum M b N s‖) ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖1 - conj s‖ / (1 - s.re)) * occupationWeight N ^ (1 - s.re) <
            ‖divisorSignedPartialSum M b N (1 - conj s)‖ := by
    refine forall₄_congr fun s hlo hhi _ => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hw_re : (1 - conj s).re = 1 - s.re := by simp
    have hw0 : 0 < (1 - conj s).re := by linarith
    have hw1 : (1 - conj s).re < 1 := by linarith
    have h2 := exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hw0 hw1
    rw [hw_re] at h2
    rw [exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1,
      hzeta_iff_refl s hs0 hs1, ← h2]
  exact ⟨hcap184, hcap184.trans hdir184, (hcap184.trans hdir184).trans hrefl184⟩

#print axioms etaSign_and_etaFlipSign_properties
#print axioms exists_unitSign_partialSum_beats_tail_everywhere
#print axioms etaFlipSign_beats_tail_at_zeta_zero
#print axioms divisorSignedPrefix_eq_sum_div
#print axioms bdd_divisorSignedPrefix_iff_harmonic_sum_eq_zero
#print axioms divisorSignedPrefix_diff_abs_le
#print axioms norm_divisorSignedSeries_sub_partialSum_le
#print axioms zeta_ne_zero_of_divisorSignedPartialSum_beats_tail
#print axioms norm_divisorSignedPartialSum_le_tail_of_zeta_eq_zero
#print axioms moebiusSievedEtaPacket_properties
#print axioms riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
#print axioms exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero
#print axioms zero_exception_band_oneHundredFifty_to_oneHundredEightyFour
#print axioms rh_iff_exists_divisorSigned_partialSum_above_oneHundredEightyFour

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
