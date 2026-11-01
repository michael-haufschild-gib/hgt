import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeResidual
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramUniformRemainder

/-!
# Prime residual mass on a terminal interval

The two endpoint Gram expansions have the same torsion term. Their difference
costs the harmonic length of the interval and a quadratic horizon remainder.
Applying this before summing prime dilations preserves that short-interval gain.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology ArithmeticFunction
open scoped Classical
namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity
open SuccessorShellArithmetic RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
  SignedArithmeticHodgeTheory

/-- Harmonic interval length plus the two endpoint large-sieve remainders. -/
def terminalPacketCost (Q M N : ℕ) : ℝ :=
  (harmonic N : ℝ) - harmonic M + 2 * (Q : ℝ) ^ 2 / ((M : ℝ) + 1)

private theorem sum_terminal_eq_sub {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc M N, f n) = (∑ n ∈ Icc 1 N, f n) - ∑ n ∈ Icc 1 M, f n := by
  have hs : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [hs]
  exact eq_sub_iff_add_eq.mpr (sum_sdiff (Icc_subset_Icc le_rfl hMN))

theorem terminalPacketCost_nonneg (Q : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    0 ≤ terminalPacketCost Q M N := by
  have hh : 0 ≤ (harmonic N : ℝ) - harmonic M := by
    rw [← HTGeometry.sum_Icc_one_div_eq_harmonic,
      ← HTGeometry.sum_Icc_one_div_eq_harmonic, ← sum_terminal_eq_sub hMN]
    exact sum_nonneg fun n _ => by positivity
  exact add_nonneg hh (by positivity)

/-- Torsion cancels exactly between the two horizons. -/
theorem harmonicConductorPacket_terminal_le {Q M N : ℕ} (hQ : 2 ≤ Q)
    (hMN : M ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Ioc M N, normalizedConductorPacket Q a n ^ 2 / (n : ℝ)) ≤
      terminalPacketCost Q M N * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  have hN := (abs_le.mp (abs_harmonicGram_quadratic_torsion_remainder hQ N a)).2
  have hM := (abs_le.mp (abs_harmonicGram_quadratic_torsion_remainder hQ M a)).1
  have hmass : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hQR0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hq : 0 ≤ (Q : ℝ) * ((Q : ℝ) - 1) := by
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    exact mul_nonneg (Nat.cast_nonneg Q) (sub_nonneg.mpr hQ1)
  have hden : (M : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hMN 1
  have hremN : (Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1) ≤
      (Q : ℝ) ^ 2 / ((M : ℝ) + 1) := by
    calc
      _ ≤ (Q : ℝ) * ((Q : ℝ) - 1) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hq (by positivity) hden
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hQR0]) (by positivity)
  have hremM : (Q : ℝ) * ((Q : ℝ) - 1) / ((M : ℝ) + 1) ≤
      (Q : ℝ) ^ 2 / ((M : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by nlinarith only [hQR0]) (by positivity)
  have hn := mul_le_mul_of_nonneg_right hremN hmass
  have hm := mul_le_mul_of_nonneg_right hremM hmass
  rw [sum_terminal_eq_sub hMN]
  dsimp only [normalizedConductorPacket, terminalPacketCost]
  have hd := sub_le_sub (hN.trans hn) ((neg_le_neg hm).trans hM)
  have hh := add_le_add_right hd
    (((harmonic N : ℝ) - harmonic M) * (∑ m ∈ Icc 1 Q, a m ^ 2))
  convert hh using 2 <;> first | rfl | ring

private theorem dilation_energy_head_le (Q : ℕ) (a : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) ≤ primeAdjunctionMass Q a := by
  have hs := hasSum_primeConductorDilationJump_sq Q a
  have h := hs.summable.sum_le_tsum (Icc 1 K) (fun k _ =>
    mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      (sum_nonneg fun _ _ => sq_nonneg _))
  simpa only [hs.tsum_eq, primeAdjunctionMass] using h

/-- Any row-dependent complementary head has the same terminal interval cost. -/
theorem finitePrimeDilationTail_terminal_sq_le {Q M N : ℕ} (hQ : 2 ≤ Q)
    (hMN : M ≤ N) (a : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ Ioc M N, finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ)) ≤
      primeActivityMass Q * terminalPacketCost Q M N * primeAdjunctionMass Q a := by
  let F := normalizedConductorPacket Q a
  have hrow (n : ℕ) : finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ) ≤
      primeActivityMass Q * ∑ k ∈ Icc 1 K,
        vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ) := by
    have h := div_le_div_of_nonneg_right
      (primeHead_value_sq_le Q a ((Icc 1 K).filter (fun k => N / n < k)) n)
      (Nat.cast_nonneg n)
    have hsub : (∑ k ∈ (Icc 1 K).filter (fun k => N / n < k),
        vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ)) ≤
        ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ => by
        exact div_nonneg (mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
          (sq_nonneg _)) (Nat.cast_nonneg n)
    have hh : finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ) ≤
        primeActivityMass Q * ∑ k ∈ (Icc 1 K).filter (fun k => N / n < k),
          vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ) := by
      simpa only [finitePrimeDilationTail, F, sum_div, mul_div_assoc] using h
    exact hh.trans (mul_le_mul_of_nonneg_left hsub (primeActivityMass_nonneg Q))
  have hsum := sum_le_sum (fun n (_ : n ∈ Ioc M N) => hrow n)
  rw [← mul_sum, sum_comm] at hsum
  have hjump (k : ℕ) :
      (∑ n ∈ Ioc M N, (F (k * n) - F n) ^ 2 / (n : ℝ)) ≤
        terminalPacketCost Q M N * ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
    have h := harmonicConductorPacket_terminal_le hQ hMN (primeConductorDilationJump Q a k)
    simpa only [normalizedConductorPacket, primeConductorDilationJump_packet, F] using h
  have htail : (∑ k ∈ Icc 1 K, ∑ n ∈ Ioc M N,
      vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ)) ≤
      terminalPacketCost Q M N * primeAdjunctionMass Q a := by
    calc
      _ = ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
          ∑ n ∈ Ioc M N, (F (k * n) - F n) ^ 2 / (n : ℝ) := by
        simp only [mul_sum, mul_div_assoc]
      _ ≤ ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
          (terminalPacketCost Q M N * ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hjump k)
          (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
      _ = terminalPacketCost Q M N * (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (dilation_energy_head_le Q a K)
        (terminalPacketCost_nonneg Q hMN)
  exact (hsum.trans (mul_le_mul_of_nonneg_left htail (primeActivityMass_nonneg Q))).trans_eq
    (by ring)

/-- The completed prime-dilation tail retains the terminal interval gain. -/
theorem completedPrimeDilationTail_terminal_sq_le {Q M N : ℕ} (hQ : 2 ≤ Q)
    (hMN : M ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Ioc M N, completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ)) ≤
      primeActivityMass Q * terminalPacketCost Q M N * primeAdjunctionMass Q a := by
  have hlim : Tendsto
      (fun K => ∑ n ∈ Ioc M N, finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ)) atTop
      (𝓝 (∑ n ∈ Ioc M N, completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ))) :=
    tendsto_finsetSum _ fun n _ => ((tendsto_finitePrimeDilationTail Q a (N / n) n).pow 2).div_const n
  exact le_of_tendsto hlim (Eventually.of_forall (finitePrimeDilationTail_terminal_sq_le hQ hMN a))

/-- The scalar row pays its global bound; only the short-interval cost multiplies adjunction energy. -/
theorem exists_primeResidual_packet_terminal_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q M N : ℕ, 2 ≤ Q → 2 ≤ N → M ≤ N → ∀ a : ℕ → ℝ,
      (∑ n ∈ Ioc M N, (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2) / Real.log N ≤
        (C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
          2 * primeActivityMass Q * terminalPacketCost Q M N * primeAdjunctionMass Q a) /
            Real.log N := by
  obtain ⟨C, hC, hscalar⟩ := exists_scalarPrimeResidual_packet_sq_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q M N hQ hN hMN a
  let r : ℕ → ℝ := fun n => mertensSum (N / n) + Real.log n -
    (Real.log N - Real.eulerMascheroniConstant)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsub : Ioc M N ⊆ Icc 1 N := by
    intro n hn
    exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  have hrow (n : ℕ) (hn : n ∈ Ioc M N) :
      (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2 ≤
        2 * (r n ^ 2 * normalizedConductorPacket Q a n ^ 2 / (n : ℝ)) +
          2 * (completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ)) := by
    rw [primeResidual_packet_eq_scalar_sub_tail a (hsub hn), mul_pow, poleVector, div_pow,
      one_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_one_div]
    have hs : (r n * normalizedConductorPacket Q a n - completedPrimeDilationTail Q a (N / n) n) ^ 2 ≤
        2 * (r n ^ 2 * normalizedConductorPacket Q a n ^ 2) +
          2 * completedPrimeDilationTail Q a (N / n) n ^ 2 := by
      nlinarith only [sq_nonneg (r n * normalizedConductorPacket Q a n +
        completedPrimeDilationTail Q a (N / n) n)]
    exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)).trans_eq (by ring)
  have hs0 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun n => r n ^ 2 * normalizedConductorPacket Q a n ^ 2 / (n : ℝ))
    (fun n _ _ => by positivity)
  have hs : (∑ n ∈ Ioc M N, r n ^ 2 * normalizedConductorPacket Q a n ^ 2 / (n : ℝ)) /
      Real.log N ≤ C * (1 + Real.log Q) / Real.log N * (∑ m ∈ Icc 1 Q, a m ^ 2) := by
    apply (div_le_div_of_nonneg_right hs0 hL.le).trans
    simpa only [r, normalizedConductorPacket, mul_div_assoc] using hscalar Q N hQ hN a
  simp only [mul_div_assoc] at hs
  have ht := div_le_div_of_nonneg_right (completedPrimeDilationTail_terminal_sq_le hQ hMN a) hL.le
  have hsplit := div_le_div_of_nonneg_right (sum_le_sum hrow) hL.le
  simp only [sum_add_distrib, ← mul_sum, add_div, mul_div_assoc] at hsplit
  calc
    _ ≤ 2 * (C * ((1 + Real.log Q) / Real.log N) * (∑ m ∈ Icc 1 Q, a m ^ 2)) +
        2 * (primeActivityMass Q * terminalPacketCost Q M N * primeAdjunctionMass Q a /
          Real.log N) := hsplit.trans
      (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num))
        (mul_le_mul_of_nonneg_left ht (by norm_num)))
    _ = _ := by ring

/-- Below the square-root prefix horizon, terminal Gram cost depends only on the horizon ratio. -/
theorem terminalPacketCost_le_log_ratio {Q M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (hQM : Q * Q ≤ M) :
    terminalPacketCost Q M N ≤ Real.log N - Real.log M + 4 := by
  have hN : 1 ≤ N := hM.trans hMN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm := (abs_le.mp (_root_.HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hM)).1
  have hn := (abs_le.mp (_root_.HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hN)).2
  have him : 1 / (M : ℝ) ≤ 1 := (div_le_one hMR).mpr hM1
  have hin : 1 / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hN1
  have hQsq : (Q : ℝ) ^ 2 ≤ (M : ℝ) + 1 := by
    have hh : (Q : ℝ) * Q ≤ M := by exact_mod_cast hQM
    nlinarith only [hh]
  have hquot : (Q : ℝ) ^ 2 / ((M : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hQsq
  have hH : (harmonic N : ℝ) - harmonic M ≤ Real.log N - Real.log M + 2 := by
    linarith only [hm, hn, him, hin]
  have hh := add_le_add hH (mul_le_mul_of_nonneg_left hquot zero_le_two)
  calc
    _ = ((harmonic N : ℝ) - harmonic M) + 2 * ((Q : ℝ) ^ 2 / ((M : ℝ) + 1)) := by
      unfold terminalPacketCost
      ring
    _ ≤ (Real.log N - Real.log M + 2) + 2 * 1 := hh
    _ = _ := by ring

/-- An integer quotient cutoff has logarithmic terminal cost, independent of conductor size. -/
theorem terminalPacketCost_nat_div_le {Q T N : ℕ} (hT : 1 ≤ T) (hTN : T ≤ N)
    (hQ : Q * Q ≤ N / T) :
    terminalPacketCost Q (N / T) N ≤ 4 + Real.log (2 * (T : ℝ)) := by
  let M := N / T
  have hM : 1 ≤ M := Nat.div_pos hTN hT
  have hMN : M ≤ N := Nat.div_le_self N T
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hT.trans hTN
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hfloor : (N : ℝ) < ((M : ℝ) + 1) * T := by
    have hh : N < (M + 1) * T := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
    exact_mod_cast hh
  have hratio : (N : ℝ) ≤ (2 * (T : ℝ)) * M := by
    nlinarith only [hfloor, mul_nonneg (sub_nonneg.mpr hM1) hTR.le]
  have hlog : Real.log N - Real.log M ≤ Real.log (2 * (T : ℝ)) := by
    rw [← Real.log_div hNR.ne' hMR.ne']
    exact Real.log_le_log (div_pos hNR hMR) ((div_le_iff₀ hMR).mpr hratio)
  have hh := terminalPacketCost_le_log_ratio hM hMN hQ
  linarith only [hh, hlog]

#print axioms terminalPacketCost_le_log_ratio
#print axioms terminalPacketCost_nat_div_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity

#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.harmonicConductorPacket_terminal_le
#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.completedPrimeDilationTail_terminal_sq_le
#print axioms GaloisForLFunctions.CriticalScaleArithmeticRigidity.exists_primeResidual_packet_terminal_sq_le
