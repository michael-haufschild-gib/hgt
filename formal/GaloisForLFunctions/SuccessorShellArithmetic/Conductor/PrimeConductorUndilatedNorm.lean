import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramLogarithmicPlateau
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory
import GaloisForLFunctions.HTGeometry.LogHarmonicFinitePart

/-!
# A uniform torsion finite part for undilated prime heads

Divisor summation identifies the scalar term without an asymptotic
replacement. The elementary Mertens bound controls the prime mass on
the short quotient horizons by the logarithm of the conductor cutoff.
Combining the quadratic tail with the logarithmic Gram plateau gives
one error bound for every packet and every horizon.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
noncomputable section

/-- Harmonic averaging of the prime divisor identity retains the exact logarithmic scalar. -/
theorem primeHead_harmonic_convolution (N : ℕ) :
    (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * (harmonic (N / k) : ℝ)) =
      ∑ n ∈ Icc 1 N, Real.log n / (n : ℝ) := by
  symm
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, vonMangoldt d / (n : ℝ) := by
      apply sum_congr rfl
      intro n _
      rw [← sum_div, vonMangoldt_sum]
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (d ∣ ·), vonMangoldt d / (n : ℝ) := by
      rw [sum_comm']
      intro n d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hn1, hnN⟩, hdn, _⟩
        exact ⟨⟨⟨hn1, hnN⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn hn1,
          (Nat.le_of_dvd hn1 hdn).trans hnN⟩
      · rintro ⟨⟨⟨hn1, hnN⟩, hdn⟩, _⟩
        exact ⟨⟨hn1, hnN⟩, hdn, by omega⟩
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      rw [← HTGeometry.sum_Icc_one_div_eq_harmonic, mul_sum]
      apply sum_nbij' (fun n => n / d) (fun k => d * k)
      · intro n hn
        rcases mem_filter.mp hn with ⟨hn, hdn⟩
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hn).1 hdn) hd0,
          Nat.div_le_div_right (mem_Icc.mp hn).2⟩
      · intro k hk
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd0 (mem_Icc.mp hk).1,
          (Nat.mul_le_mul_left d (mem_Icc.mp hk).2).trans (Nat.mul_div_le N d)⟩,
          dvd_mul_right d k⟩
      · intro n hn
        exact Nat.mul_div_cancel' (mem_filter.mp hn).2
      · intro k _
        exact Nat.mul_div_cancel_left k hd0
      · intro n hn
        have hprod : (d : ℝ) * (n / d : ℕ) = n := by
          exact_mod_cast Nat.mul_div_cancel' (mem_filter.mp hn).2
        rw [← hprod]
        ring

private theorem abs_primeMertens_error_le_seven {N : ℕ} (hN : 1 ≤ N) :
    |mertensSum N - Real.log N| ≤ 7 := by
  have h := _root_.RHTower.Mertens.mertens_first N hN
  have hfour : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith only [h]
  exact h.trans (by linarith only [hfour])

private theorem prime_quotient_tail_mass {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 2 ≤ N) :
    mertensSum N - mertensSum (N / (Q * Q)) ≤ 2 * Real.log Q + 15 := by
  have hQ0 : 0 < Q := by omega
  have hD : 0 < Q * Q := Nat.mul_pos hQ0 hQ0
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogD : Real.log (Q * Q : ℕ) = 2 * Real.log Q := by
    rw [Nat.cast_mul, Real.log_mul hQR hQR]
    ring
  have hNupper := (abs_le.mp (abs_primeMertens_error_le_seven (by omega : 1 ≤ N))).2
  by_cases hK : N / (Q * Q) = 0
  · have hND : N < Q * Q := by
      by_contra h
      have hpos := Nat.div_pos (Nat.le_of_not_gt h) hD
      omega
    have hlog := Real.log_le_log hNR (show (N : ℝ) ≤ (Q * Q : ℕ) by exact_mod_cast hND.le)
    rw [hlogD] at hlog
    rw [hK]
    simp only [mertensSum, Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, sub_zero]
    change (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ)) - Real.log N ≤ 7 at hNupper
    linarith only [hlog, hNupper]
  · have hKpos : 1 ≤ N / (Q * Q) := Nat.pos_of_ne_zero hK
    have hDN : Q * Q ≤ N := by
      by_contra h
      exact hK (Nat.div_eq_of_lt (Nat.lt_of_not_ge h))
    have hKlower := (abs_le.mp (abs_primeMertens_error_le_seven hKpos)).1
    have hround := (roundoff_le hD hDN).2
    rw [hlogD] at hround
    have hinv : (1 : ℝ) / (N / (Q * Q) : ℕ) ≤ 1 :=
      (div_le_one (by exact_mod_cast hKpos : (0 : ℝ) < (N / (Q * Q) : ℕ))).mpr
        (by exact_mod_cast hKpos)
    linarith only [hNupper, hKlower, hround, hinv]

private def packetGram (Q : ℕ) (a : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 Y, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)

private def packetRemainder (Q : ℕ) (a : ℕ → ℝ) (Y : ℕ) : ℝ :=
  packetGram Q a Y - (harmonic Y : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
    torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))

private theorem inverse_quotient_succ_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    (1 : ℝ) / (((N / k : ℕ) : ℝ) + 1) ≤ (k : ℝ) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := _root_.RHTower.Mertens.cast_div_lt N k hk
  rw [div_lt_iff₀ hkR] at h
  rw [div_le_div_iff₀ (by positivity) hNR]
  nlinarith only [h]

private theorem weighted_gram_remainder_small {Q N k : ℕ}
    (hQ : 2 ≤ Q) (hN : 0 < N) (hk : 0 < k) (a : ℕ → ℝ) :
    vonMangoldt k / (k : ℝ) * |packetRemainder Q a (N / k)| ≤
      (Q : ℝ) ^ 2 / N * vonMangoldt k * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hM : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun m _ => sq_nonneg (a m)
  have hw : 0 ≤ vonMangoldt k / (k : ℝ) :=
    div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hq : (Q : ℝ) * ((Q : ℝ) - 1) ≤ (Q : ℝ) ^ 2 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) Q]
  have hscale : (Q : ℝ) * ((Q : ℝ) - 1) / (((N / k : ℕ) : ℝ) + 1) ≤
      (Q : ℝ) ^ 2 * k / N := by
    calc
      _ ≤ (Q : ℝ) ^ 2 / (((N / k : ℕ) : ℝ) + 1) :=
        div_le_div_of_nonneg_right hq (by positivity)
      _ = (Q : ℝ) ^ 2 * (1 / (((N / k : ℕ) : ℝ) + 1)) := by ring
      _ ≤ (Q : ℝ) ^ 2 * ((k : ℝ) / N) :=
        mul_le_mul_of_nonneg_left (inverse_quotient_succ_le hN hk) (sq_nonneg _)
      _ = _ := by ring
  have hr := (abs_harmonicGram_quadratic_torsion_remainder hQ (N / k) a).trans
    (mul_le_mul_of_nonneg_right hscale hM)
  calc
    _ ≤ vonMangoldt k / (k : ℝ) *
        ((Q : ℝ) ^ 2 * k / N * ∑ m ∈ Icc 1 Q, a m ^ 2) :=
      mul_le_mul_of_nonneg_left hr hw
    _ = _ := by
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hkR, hNR]

private theorem weighted_gram_remainder_bound {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 2 ≤ N) (a : ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * |packetRemainder Q a (N / k)|) ≤
      127 * (1 + Real.log Q) ^ 2 * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let K := N / (Q * Q)
  let tail := (Icc 1 N).filter (fun k => ¬ k ≤ K)
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let L : ℝ := 6 * Real.log Q + Real.log 4 + 5
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hK : K ≤ N := Nat.div_le_self N (Q * Q)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hhead : (Icc 1 N).filter (fun k => k ≤ K) = Icc 1 K := by
    ext k
    simp only [mem_filter, mem_Icc]
    omega
  have hsplit (f : ℕ → ℝ) :
      (∑ k ∈ Icc 1 K, f k) + (∑ k ∈ tail, f k) = ∑ k ∈ Icc 1 N, f k := by
    simpa only [hhead] using sum_filter_add_sum_filter_not (Icc 1 N) (fun k => k ≤ K) f
  have htailMass : (∑ k ∈ tail, vonMangoldt k / (k : ℝ)) ≤ 2 * Real.log Q + 15 := by
    have h := hsplit (fun k => vonMangoldt k / (k : ℝ))
    have hb := prime_quotient_tail_mass hQ hN
    change mertensSum K + (∑ k ∈ tail, vonMangoldt k / (k : ℝ)) = mertensSum N at h
    change mertensSum N - mertensSum K ≤ 2 * Real.log Q + 15 at hb
    linarith only [h, hb]
  have hsmall : (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * |packetRemainder Q a (N / k)|) ≤
      7 * M := by
    calc
      _ ≤ ∑ k ∈ Icc 1 K, (Q : ℝ) ^ 2 / N * vonMangoldt k * M :=
        sum_le_sum fun k hk => weighted_gram_remainder_small hQ (by omega) (mem_Icc.mp hk).1 a
      _ = (Q : ℝ) ^ 2 / N * _root_.RHTower.chebyshevPsi K * M := by
        change _ = (Q : ℝ) ^ 2 / N * (∑ k ∈ Icc 1 K, vonMangoldt k) * M
        rw [← sum_mul, ← mul_sum]
      _ ≤ (Q : ℝ) ^ 2 / N * (7 * K) * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (_root_.RHTower.chebyshevPsi_le_seven K) (by positivity)) hM
      _ ≤ 7 * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        have hDK : (Q : ℝ) ^ 2 * K ≤ N := by
          have h := Nat.mul_div_le N (Q * Q)
          simpa only [Nat.cast_mul, sq] using (show (((Q * Q) * K : ℕ) : ℝ) ≤ N by exact_mod_cast h)
        rw [div_mul_eq_mul_div, div_le_iff₀ hNR]
        nlinarith only [hDK]
  have hlarge : (∑ k ∈ tail, vonMangoldt k / (k : ℝ) * |packetRemainder Q a (N / k)|) ≤
      L * M * (2 * Real.log Q + 15) := by
    calc
      _ ≤ ∑ k ∈ tail, vonMangoldt k / (k : ℝ) * (L * M) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (abs_harmonicGram_torsion_remainder_le_log hQ (N / k) a)
          (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      _ = L * M * (∑ k ∈ tail, vonMangoldt k / (k : ℝ)) := by rw [← sum_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htailMass (mul_nonneg hL hM)
  have hLbound : L ≤ 8 * (1 + Real.log Q) := by
    have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    dsimp only [L]
    linarith only [hfour, hlogQ]
  have htailBound : 2 * Real.log Q + 15 ≤ 15 * (1 + Real.log Q) := by
    linarith only [hlogQ]
  have hpoly : 7 + L * (2 * Real.log Q + 15) ≤ 127 * (1 + Real.log Q) ^ 2 := by
    have hp := mul_le_mul hLbound htailBound (by linarith only [hlogQ]) (by positivity)
    have hs : 1 ≤ (1 + Real.log Q) ^ 2 :=
      one_le_pow₀ (by linarith only [hlogQ] : (1 : ℝ) ≤ 1 + Real.log Q)
    nlinarith only [hp, hs]
  rw [← hsplit (fun k => vonMangoldt k / (k : ℝ) * |packetRemainder Q a (N / k)|)]
  calc
    _ ≤ 7 * M + L * M * (2 * Real.log Q + 15) := add_le_add hsmall hlarge
    _ = (7 + L * (2 * Real.log Q + 15)) * M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpoly hM

/-- Every undilated prime packet retains its exact scalar and torsion terms with one logarithmic error bound. -/
theorem abs_primeConductorUndilatedPacket_remainder {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 2 ≤ N) (a : ℕ → ℝ) :
    |(2 * ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) *
          (∑ n ∈ Icc 1 (N / k), (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ))) /
        Real.log N -
      (2 * ∑ n ∈ Icc 1 N, Real.log n / (n : ℝ)) / Real.log N * (∑ m ∈ Icc 1 Q, a m ^ 2) +
      (2 * mertensSum N / Real.log N) * torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))| ≤
        (256 * (1 + Real.log Q) ^ 2 / Real.log N) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let T := torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsum : (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetRemainder Q a (N / k)) =
      (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetGram Q a (N / k)) -
        (∑ n ∈ Icc 1 N, Real.log n / (n : ℝ)) * M + mertensSum N * T := by
    simp only [packetRemainder, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← mul_assoc,
      ← sum_mul, primeHead_harmonic_convolution]
    rfl
  have heq :
      (2 * ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetGram Q a (N / k)) / Real.log N -
        (2 * ∑ n ∈ Icc 1 N, Real.log n / (n : ℝ)) / Real.log N * M +
        (2 * mertensSum N / Real.log N) * T =
      2 * (∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetRemainder Q a (N / k)) / Real.log N := by
    rw [hsum]
    ring
  change |(2 * ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetGram Q a (N / k)) / Real.log N -
    (2 * ∑ n ∈ Icc 1 N, Real.log n / (n : ℝ)) / Real.log N * M +
      (2 * mertensSum N / Real.log N) * T| ≤ _
  rw [heq, abs_div, abs_mul, abs_of_pos hlog, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hweighted : |∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetRemainder Q a (N / k)| ≤
      127 * (1 + Real.log Q) ^ 2 * M := by
    calc
      _ ≤ ∑ k ∈ Icc 1 N, |vonMangoldt k / (k : ℝ) * packetRemainder Q a (N / k)| := abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * |packetRemainder Q a (N / k)| := by
        apply sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))]
      _ ≤ _ := weighted_gram_remainder_bound hQ hN a
  calc
    _ ≤ 2 * (127 * (1 + Real.log Q) ^ 2 * M) / Real.log N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweighted (by norm_num)) hlog.le
    _ ≤ (256 * (1 + Real.log Q) ^ 2 / Real.log N) * M := by
      have hp : 0 ≤ (1 + Real.log Q) ^ 2 * M / Real.log N := by positivity
      calc
        _ = 254 * ((1 + Real.log Q) ^ 2 * M / Real.log N) := by ring
        _ ≤ 256 * ((1 + Real.log Q) ^ 2 * M / Real.log N) :=
          mul_le_mul_of_nonneg_right (by norm_num : (254 : ℝ) ≤ 256) hp
        _ = _ := by ring

#print axioms primeHead_harmonic_convolution
#print axioms abs_primeConductorUndilatedPacket_remainder

private theorem normalized_selfMass (Q : ℕ) (a : ℕ → ℝ) :
    selfMass Q (fun m => a m / Real.sqrt (m.totient : ℝ)) = ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  unfold selfMass
  apply sum_congr rfl
  intro m hm
  have hphi : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp [hphi]

/-- One absolute constant controls the full undilated torsion finite part on every conductor packet. -/
theorem exists_abs_primeConductorUndilatedPacket_finitePart_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      |(2 * ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) *
          (∑ n ∈ Icc 1 (N / k), (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ))) /
        Real.log N - Real.log N * (∑ m ∈ Icc 1 Q, a m ^ 2) +
          2 * torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))| ≤
        (C * (1 + Real.log Q) ^ 2 / Real.log N) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let B : ℝ := ∑' n : ℕ, |HTGeometry.logarithmicHarmonicError n|
  have hB : 0 ≤ B := tsum_nonneg fun n => abs_nonneg _
  have hBsum : Summable (fun n : ℕ => |HTGeometry.logarithmicHarmonicError n|) := by
    simpa only [Real.norm_eq_abs] using HTGeometry.summable_logarithmicHarmonicError.norm
  have hscalar (N : ℕ) : |HTGeometry.logarithmicHarmonic N - Real.log N ^ 2 / 2| ≤ B := by
    rw [HTGeometry.logarithmicHarmonic_sub_eq_sum]
    exact (abs_sum_le_sum_abs _ _).trans
      (Summable.sum_le_tsum (range N) (fun n _ => abs_nonneg _) hBsum)
  refine ⟨354 + 2 * B, by positivity, ?_⟩
  intro Q N hQ hN a
  let M : ℝ := ∑ m ∈ Icc 1 Q, a m ^ 2
  let T := torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  let U : ℝ := 2 * ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) * packetGram Q a (N / k)
  let Z : ℝ := HTGeometry.logarithmicHarmonic N
  let H : ℝ := 1 + Real.log Q
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hH : 1 ≤ H := by dsimp only [H]; linarith only [Real.log_natCast_nonneg Q]
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbase : |U - 2 * Z * M + 2 * mertensSum N * T| ≤ 256 * H ^ 2 * M := by
    have h := abs_primeConductorUndilatedPacket_remainder hQ hN a
    change |U / Real.log N - 2 * Z / Real.log N * M + 2 * mertensSum N / Real.log N * T| ≤
      (256 * H ^ 2 / Real.log N) * M at h
    have heq : U / Real.log N - 2 * Z / Real.log N * M + 2 * mertensSum N / Real.log N * T =
        (U - 2 * Z * M + 2 * mertensSum N * T) / Real.log N := by ring
    rw [heq, abs_div, abs_of_pos hlog, div_mul_eq_mul_div] at h
    exact (div_le_div_iff_of_pos_right hlog).mp h
  have htor : |T| ≤ 7 * H * M := by
    have h := abs_torsionPairing_le_log Q (fun m => a m / Real.sqrt (m.totient : ℝ))
    rw [normalized_selfMass] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hM)
    have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    dsimp only [H]
    linarith only [hfour, Real.log_natCast_nonneg Q]
  have hscalarM : |2 * (Z - Real.log N ^ 2 / 2) * M| ≤ 2 * B * M := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hscalar N) (by norm_num)) hM
  have hMertensT : |2 * (mertensSum N - Real.log N) * T| ≤ 14 * |T| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (abs_primeMertens_error_le_seven (by omega : 1 ≤ N)) (by norm_num : (0 : ℝ) ≤ 2))
      (abs_nonneg T)
    norm_num only [show (2 : ℝ) * 7 = 14 by norm_num] at h
    exact h
  have hcoef : 256 * H ^ 2 + 2 * B + 98 * H ≤ (354 + 2 * B) * H ^ 2 := by
    have hs : 1 ≤ H ^ 2 := one_le_pow₀ hH
    have hHsq : H ≤ H ^ 2 := by nlinarith only [hH]
    have hBs := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
    nlinarith only [hHsq, hBs]
  have htotal : |U - Real.log N ^ 2 * M + 2 * Real.log N * T| ≤
      (354 + 2 * B) * H ^ 2 * M := by
    calc
      _ = |(U - 2 * Z * M + 2 * mertensSum N * T) +
          2 * (Z - Real.log N ^ 2 / 2) * M - 2 * (mertensSum N - Real.log N) * T| := by
        congr 1
        ring
      _ ≤ (|U - 2 * Z * M + 2 * mertensSum N * T| + |2 * (Z - Real.log N ^ 2 / 2) * M|) +
          |2 * (mertensSum N - Real.log N) * T| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (256 * H ^ 2 * M + 2 * B * M) + 14 * (7 * H * M) :=
        add_le_add (add_le_add hbase hscalarM)
          (hMertensT.trans (mul_le_mul_of_nonneg_left htor (by norm_num)))
      _ = (256 * H ^ 2 + 2 * B + 98 * H) * M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hM
  have heq : U / Real.log N - Real.log N * M + 2 * T =
      (U - Real.log N ^ 2 * M + 2 * Real.log N * T) / Real.log N := by
    field_simp [hlog.ne']
  change |U / Real.log N - Real.log N * M + 2 * T| ≤ ((354 + 2 * B) * H ^ 2 / Real.log N) * M
  rw [heq, abs_div, abs_of_pos hlog, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right htotal hlog.le

#print axioms exists_abs_primeConductorUndilatedPacket_finitePart_le

end
end GaloisForLFunctions.SuccessorShellArithmetic
