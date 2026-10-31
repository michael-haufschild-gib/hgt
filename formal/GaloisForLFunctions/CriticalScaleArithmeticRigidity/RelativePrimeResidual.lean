import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeHeads
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicPacketQuotientTails
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.ScalarPrimePacketNorm

/-!
# The literal prime residual retains adjunction energy

The common Mertens row and the complementary prime-dilation tail have
different costs. Active-prime Cauchy–Schwarz and the logarithmic dilation
moment bound control the tail by the packet's exact adjunction energy.
Combining it with the scalar row retains this distinction in the full
prime residual, uniformly over growing packets and every horizon.
-/

noncomputable section

open Finset Filter Topology ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SuccessorShellArithmetic RenormalizedArithmeticPotentialTheory
  SignedArithmeticHodgeTheory BezoutValuationIncidence ArithmeticIntersectionTheory
  CriticalArithmeticCorrelationTheory ArithmeticElectrostatics ArithmeticEffectivityTheory

/-- A finite complementary head of the actual prime-dilation generator. -/
def finitePrimeDilationTail (Q : ℕ) (a : ℕ → ℝ) (y K n : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 K).filter (fun k => y < k), vonMangoldt k / (k : ℝ) *
    (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n)

/-- The exact complementary prime tail, expressed through the arithmetic divisor jet. -/
def completedPrimeDilationTail (Q : ℕ) (a : ℕ → ℝ) (y n : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 Q, a m *
    (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
      (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) -
    ∑ k ∈ Icc 1 y, vonMangoldt k / (k : ℝ) *
      (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n)

private theorem nat_quotient_lt_iff_real {N n k : ℕ} (hn : 0 < n) :
    N / n < k ↔ (N : ℝ) / n < k := by
  rw [Nat.div_lt_iff_lt_mul hn, div_lt_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  exact_mod_cast (Iff.rfl : N < k * n ↔ N < k * n)

private theorem dilationJump_quotient_tail_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ n ∈ (Icc 1 N).filter (fun n => N / n < k),
      (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n) ^ 2 / (n : ℝ)) ≤
      (18 * (1 + Real.log Q) + Real.log k) *
        ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
  have hset : (Icc 1 N).filter (fun n => N / n < k) =
      (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < k) := by
    apply filter_congr
    intro n hn
    exact nat_quotient_lt_iff_real (mem_Icc.mp hn).1
  have htail := harmonicConductorPacket_quotient_tail_le hQ hN
    (by exact_mod_cast hk : (1 : ℝ) ≤ k) (primeConductorDilationJump Q a k)
  have hcoef : 1 + Real.log (2 * (k : ℝ)) + 2 * (6 * Real.log Q + Real.log 4 + 5) ≤
      18 * (1 + Real.log Q) + Real.log k := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast (Nat.ne_of_gt hk) : (k : ℝ) ≠ 0)]
    have htwo := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    have hfour := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith only [htwo, hfour, Real.log_natCast_nonneg Q]
  rw [hset]
  simp only [primeConductorDilationJump_packet] at htail
  exact htail.trans (mul_le_mul_of_nonneg_right hcoef (sum_nonneg fun _ _ => sq_nonneg _))

/-- Complementary rows cost one logarithmic moment of the exact dilation energy. -/
theorem finitePrimeDilationTail_harmonic_sq_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ Icc 1 N, finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ)) ≤
      19 * primeActivityMass Q * (1 + Real.log Q) * primeAdjunctionMass Q a := by
  let F := normalizedConductorPacket Q a
  have hrow : (∑ n ∈ Icc 1 N, finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ)) ≤
      primeActivityMass Q *
        ∑ n ∈ Icc 1 N, ∑ k ∈ (Icc 1 K).filter (fun k => N / n < k),
          vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    have h := div_le_div_of_nonneg_right
      (primeHead_value_sq_le Q a ((Icc 1 K).filter (fun k => N / n < k)) n)
      (Nat.cast_nonneg n)
    simpa only [finitePrimeDilationTail, F, sum_div, mul_div_assoc] using h
  have hswap : (∑ n ∈ Icc 1 N, ∑ k ∈ (Icc 1 K).filter (fun k => N / n < k),
      vonMangoldt k / (k : ℝ) * (F (k * n) - F n) ^ 2 / (n : ℝ)) =
      ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
        ∑ n ∈ (Icc 1 N).filter (fun n => N / n < k), (F (k * n) - F n) ^ 2 / (n : ℝ) := by
    simp only [sum_filter, mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  have htail : (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
      ∑ n ∈ (Icc 1 N).filter (fun n => N / n < k), (F (k * n) - F n) ^ 2 / (n : ℝ)) ≤
      ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
        ((18 * (1 + Real.log Q) + Real.log k) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2) :=
    sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
      (dilationJump_quotient_tail_le hQ hN a (mem_Icc.mp hk).1)
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
  rw [hswap] at hrow
  exact (hrow.trans (mul_le_mul_of_nonneg_left
    (htail.trans (primeDilation_logWeightedEnergy_le (by omega : 1 ≤ Q) a K))
      (primeActivityMass_nonneg Q))).trans_eq (by ring)

/-- The proved prime generator sum supplies the complete complementary tail. -/
theorem tendsto_finitePrimeDilationTail (Q : ℕ) (a : ℕ → ℝ) (y n : ℕ) :
    Tendsto (fun K => finitePrimeDilationTail Q a y K n) atTop
      (𝓝 (completedPrimeDilationTail Q a y n)) := by
  let g : ℕ → ℝ := fun k => vonMangoldt k / (k : ℝ) *
    (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n)
  have h := ((hasSum_normalizedRamanujanPacket_up Q a n).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)).sub_const (∑ k ∈ Icc 1 y, g k)
  change Tendsto (fun K => (∑ k ∈ range (K + 1), g k) - ∑ k ∈ Icc 1 y, g k)
    atTop (𝓝 (completedPrimeDilationTail Q a y n)) at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop y] with K hK
  have hrange : range (K + 1) =
      insert 0 (Icc 1 y ∪ (Icc 1 K).filter (fun k => y < k)) := by
    ext k
    simp only [mem_range, mem_insert, mem_union, mem_filter, mem_Icc]
    omega
  have hdisj : Disjoint (Icc 1 y) ((Icc 1 K).filter (fun k => y < k)) := by
    rw [disjoint_left]
    intro k hk hyk
    have := (mem_Icc.mp hk).2
    have := (mem_filter.mp hyk).2
    omega
  have hzero : (0 : ℕ) ∉ Icc 1 y ∪ (Icc 1 K).filter (fun k => y < k) := by
    simp only [mem_union, mem_Icc, mem_filter]
    omega
  rw [hrange, sum_insert hzero, sum_union hdisj]
  have hg0 : g 0 = 0 := by simp only [g, Nat.cast_zero, div_zero, zero_mul]
  rw [hg0, zero_add]
  change (∑ k ∈ Icc 1 y, g k) +
    (∑ k ∈ (Icc 1 K).filter (fun k => y < k), g k) - (∑ k ∈ Icc 1 y, g k) =
      ∑ k ∈ (Icc 1 K).filter (fun k => y < k), g k
  ring

/-- Removing the prime cutoff preserves the source-relative harmonic tail bound. -/
theorem completedPrimeDilationTail_harmonic_sq_le {Q N : ℕ} (hQ : 2 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ)) ≤
      19 * primeActivityMass Q * (1 + Real.log Q) * primeAdjunctionMass Q a := by
  have hlim : Tendsto
      (fun K => ∑ n ∈ Icc 1 N, finitePrimeDilationTail Q a (N / n) K n ^ 2 / (n : ℝ)) atTop
      (𝓝 (∑ n ∈ Icc 1 N, completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ))) :=
    tendsto_finsetSum _ fun n _ => ((tendsto_finitePrimeDilationTail Q a (N / n) n).pow 2).div_const n
  exact le_of_tendsto hlim (Eventually.of_forall (finitePrimeDilationTail_harmonic_sq_le hQ hN a))

private theorem normalized_correction_eq_up_sub_jet {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (y : ℕ) :
    poleProfileCorrection (normalizedRamanujanMode m) y n =
      (∑ k ∈ Icc 1 y, vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) -
      ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) := by
  have hg : normalizedRamanujanMode m =
      fun j => ramanujanLagCoefficient m j / Real.sqrt (m.totient : ℝ) :=
    funext (normalizedRamanujanMode_eq_coefficient hm)
  rw [hg, poleProfileCorrection_div, poleProfileCorrection_eq_divisor_jumps]
  change ((∑ k ∈ Icc 1 y,
    (ramanujanLagCoefficient m (n * k) - ramanujanLagCoefficient m n) * vonMangoldt k / (k : ℝ)) +
      ramanujanDownCorrection m n) / Real.sqrt (m.totient : ℝ) = _
  rw [ramanujanDownCorrection_eq_neg_logDivisorJet m hn, add_div, neg_div, ← sub_eq_add_neg]
  congr 1
  rw [sum_div]
  apply sum_congr rfl
  intro k _
  rw [Nat.mul_comm n k]
  ring

private theorem primeResidual_mode_eq {m N n : ℕ} (hm : 0 < m) (hn : n ∈ Icc 1 N) :
    ramanujanPrimeResidual m N n =
      ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
          normalizedRamanujanMode m n +
        (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
          (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) -
        (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
          (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) * poleVector n := by
  rw [ramanujanPrimeResidual]
  simp only [ramanujanPoleProfile_eq_mul_poleVector]
  rw [sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m)
    (mem_Icc.mp hn).1 (mem_Icc.mp hn).2,
    normalized_correction_eq_up_sub_jet hm (mem_Icc.mp hn).1]
  dsimp only [ramanujanAdjunctionEnergy]
  ring

/-- Exact source decomposition of the full packet residual, before its two square estimates. -/
theorem primeResidual_packet_eq_scalar_sub_tail {Q N n : ℕ}
    (a : ℕ → ℝ) (hn : n ∈ Icc 1 N) :
    (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) =
      ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
        normalizedConductorPacket Q a n - completedPrimeDilationTail Q a (N / n) n) * poleVector n := by
  have hsum : (∑ m ∈ Icc 1 Q, a m *
      (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
        (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n))) =
      ∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
        (normalizedConductorPacket Q a (k * n) - normalizedConductorPacket Q a n) := by
    simp only [normalizedConductorPacket, mul_sum, ← sum_sub_distrib]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro m _
    ring
  calc
    _ = (∑ m ∈ Icc 1 Q, a m *
        ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
            normalizedRamanujanMode m n +
          (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
            (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n)) -
          (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n))) * poleVector n := by
      rw [sum_mul]
      apply sum_congr rfl
      intro m hm
      rw [primeResidual_mode_eq (mem_Icc.mp hm).1 hn]
      ring
    _ = ((mertensSum (N / n) + Real.log n - (Real.log N - Real.eulerMascheroniConstant)) *
        normalizedConductorPacket Q a n +
        (∑ m ∈ Icc 1 Q, a m *
          (∑ k ∈ Icc 1 (N / n), vonMangoldt k / (k : ℝ) *
            (normalizedRamanujanMode m (k * n) - normalizedRamanujanMode m n))) -
        (∑ m ∈ Icc 1 Q, a m *
          (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ) -
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n))) * poleVector n := by
      congr 1
      rw [normalizedConductorPacket, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intro m _
      ring
    _ = _ := by rw [hsum, completedPrimeDilationTail]; ring

/-- The literal residual has separate scalar-mass and arithmetic-energy costs. -/
theorem exists_primeResidual_packet_relative_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2) / Real.log N ≤
        (C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
          38 * primeActivityMass Q * (1 + Real.log Q) * primeAdjunctionMass Q a) / Real.log N := by
  obtain ⟨C, hC, hscalar⟩ := exists_scalarPrimeResidual_packet_sq_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q N hQ hN a
  let M := ∑ m ∈ Icc 1 Q, a m ^ 2
  let H := 1 + Real.log (Q : ℝ)
  let r : ℕ → ℝ := fun n => mertensSum (N / n) + Real.log n -
    (Real.log N - Real.eulerMascheroniConstant)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2 ≤
        2 * (r n ^ 2 * normalizedConductorPacket Q a n ^ 2 / (n : ℝ)) +
          2 * (completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ)) := by
    rw [primeResidual_packet_eq_scalar_sub_tail a hn, mul_pow, poleVector, div_pow, one_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), mul_one_div]
    have hsq : (r n * normalizedConductorPacket Q a n - completedPrimeDilationTail Q a (N / n) n) ^ 2 ≤
        2 * (r n ^ 2 * normalizedConductorPacket Q a n ^ 2) +
          2 * completedPrimeDilationTail Q a (N / n) n ^ 2 := by
      nlinarith only [sq_nonneg (r n * normalizedConductorPacket Q a n +
        completedPrimeDilationTail Q a (N / n) n)]
    exact (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n)).trans_eq (by ring)
  have hsplit := div_le_div_of_nonneg_right (sum_le_sum hrow) hlog.le
  simp only [sum_add_distrib, ← mul_sum, add_div, mul_div_assoc] at hsplit
  have hs : (∑ n ∈ Icc 1 N, r n ^ 2 * (normalizedConductorPacket Q a n ^ 2 / (n : ℝ))) /
      Real.log N ≤ C * H / Real.log N * M := by
    simpa only [r, normalizedConductorPacket, H, M, mul_div_assoc] using hscalar Q N hQ hN a
  have ht := div_le_div_of_nonneg_right
    (completedPrimeDilationTail_harmonic_sq_le hQ (by omega : 1 ≤ N) a) hlog.le
  calc
    _ ≤ 2 * (C * H / Real.log N * M) +
        2 * (19 * primeActivityMass Q * H * primeAdjunctionMass Q a / Real.log N) :=
      hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num))
        (mul_le_mul_of_nonneg_left ht (by norm_num)))
    _ = _ := by dsimp only [H, M]; ring

/-- A quadratic logarithmic cost multiplies adjunction energy; only the scalar row pays
coefficient mass. -/
theorem exists_primeResidual_packet_relative_log_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2) / Real.log N ≤
        (C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
          532 * (1 + Real.log Q) ^ 2 * primeAdjunctionMass Q a) / Real.log N := by
  obtain ⟨C, hC, hrel⟩ := exists_primeResidual_packet_relative_sq_le
  refine ⟨C, hC, fun Q N hQ hN a => (hrel Q N hQ hN a).trans ?_⟩
  have hA := primeActivityMass_le_log (by omega : 1 ≤ Q)
  have hL := primeAdjunctionMass_nonneg Q a
  have hH : 0 ≤ 1 + Real.log (Q : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hA
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 38) hH) hL)
  have hterm : 38 * primeActivityMass Q * (1 + Real.log Q) * primeAdjunctionMass Q a ≤
      532 * (1 + Real.log Q) ^ 2 * primeAdjunctionMass Q a := by nlinarith only [hm]
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg N)
  exact add_le_add le_rfl hterm

#print axioms completedPrimeDilationTail_harmonic_sq_le
#print axioms exists_primeResidual_packet_relative_sq_le
#print axioms exists_primeResidual_packet_relative_log_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
