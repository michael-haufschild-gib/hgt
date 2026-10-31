import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorDilationMoments
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingRamanujanFamiliesHaveASquareRootHorizon
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRenormalizedPrimeEnergyControlsTheDefect

set_option autoImplicit false

/-!
# Direct defect coercivity for conductor packets

Apply the harmonic lower frame to each prime-dilation square before summing
prime powers. The exact dilation energy and its first logarithmic moment
leave only a linear logarithmic conductor loss.
-/

noncomputable section
open Finset Filter Topology ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open SuccessorShellArithmetic CriticalArithmeticCorrelationTheory ArithmeticElectrostatics

private theorem sum_Icc_div_comm (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / n), f n k) =
      ∑ k ∈ Icc 1 N, ∑ n ∈ Icc 1 (N / k), f n k := by
  refine sum_comm' fun n k => ?_
  simp only [mem_Icc]
  constructor
  · rintro ⟨⟨hn1, -⟩, hk1, hkN⟩
    rw [Nat.le_div_iff_mul_le hn1] at hkN
    refine ⟨⟨hn1, ?_⟩, hk1, ?_⟩
    · rw [Nat.le_div_iff_mul_le hk1]
      nlinarith only [hkN]
    · nlinarith only [hkN, hn1]
  · rintro ⟨⟨hn1, hnN⟩, hk1, -⟩
    rw [Nat.le_div_iff_mul_le hk1] at hnN
    refine ⟨⟨hn1, ?_⟩, hk1, ?_⟩
    · nlinarith only [hnN, hk1]
    · rw [Nat.le_div_iff_mul_le hn1]
      nlinarith only [hnN]

/-- The packet defect is a harmonic sum of its literal prime-dilation squares. -/
theorem poleDefect_ramanujanPacket_eq (Q N : ℕ) (a : ℕ → ℝ) :
    poleDefect N (fun n => ∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) =
      ∑ k ∈ Icc 1 N, vonMangoldt k / (k : ℝ) *
        ∑ n ∈ Icc 1 (N / k),
          ((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (k * n)) -
            ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ) := by
  let F : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n
  have hpacket (n : ℕ) : (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) =
      F n / Real.sqrt n := by
    simp only [F, ramanujanPoleProfile, ← mul_div_assoc, ← sum_div]
  unfold poleDefect
  rw [sum_Icc_div_comm]
  apply sum_congr rfl
  intro k hk
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  have hedge : (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m (n * k)) -
      (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) / Real.sqrt k =
      (F (k * n) - F n) / (Real.sqrt k * Real.sqrt n) := by
    rw [hpacket, hpacket, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n),
      Nat.mul_comm n k]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hedge, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k),
    Real.sq_sqrt (Nat.cast_nonneg n)]
  dsimp only [F]
  ring

/-- The exact arithmetic energy loses only `3 log Q + 1` under finite-horizon truncation. -/
theorem poleDefect_ramanujanPacket_ge_logarithmic {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 1 ≤ N) (a : ℕ → ℝ) :
    (Real.log N - 3 * Real.log Q - 1) *
        (∑ m ∈ Icc 1 Q,
          (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2) ≤
      poleDefect N (fun n => ∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) := by
  let F : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n
  let E := ∑ m ∈ Icc 1 Q,
    (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2
  let J : ℕ → ℝ := fun k => ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2
  let e : ℕ → ℝ := fun k => vonMangoldt k / (k : ℝ) * J k
  let g : ℕ → ℝ := fun k => vonMangoldt k / (k : ℝ) *
    ∑ n ∈ Icc 1 (N / k), (F (k * n) - F n) ^ 2 / (n : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hJ (k : ℕ) : 0 ≤ J k := sum_nonneg fun _ _ => sq_nonneg _
  have hpoint (k : ℕ) (hk : 1 ≤ k) :
      (Real.log N - 2 * Real.log Q) * e k - Real.log k * e k ≤ g k := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hquot : (N : ℝ) / k ≤ ((N / k : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hkR]
      have hmod := Nat.mod_lt N hk
      have hid := Nat.mod_add_div N k
      have hn : N ≤ (N / k + 1) * k := by nlinarith only [hmod, hid]
      exact_mod_cast hn
    have hlog := Real.log_le_log (div_pos hNR hkR) hquot
    rw [Real.log_div hNR.ne' hkR.ne'] at hlog
    have hframe := ramanujanPoleProfile_family_squareRoot_lower hQ
      (primeConductorDilationJump Q a k) (N / k)
    have hframe' : (Real.log (((N / k : ℕ) : ℝ) + 1) - 2 * Real.log Q) * J k ≤
        ∑ n ∈ Icc 1 (N / k), (F (k * n) - F n) ^ 2 / (n : ℝ) := by
      convert hframe using 1
      apply sum_congr rfl
      intro n hn
      simp only [ramanujanPoleProfile, ← mul_div_assoc, ← sum_div, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg n), primeConductorDilationJump_packet, F]
    have hlow : (Real.log N - Real.log k - 2 * Real.log Q) * J k ≤
        ∑ n ∈ Icc 1 (N / k), (F (k * n) - F n) ^ 2 / (n : ℝ) :=
      (mul_le_mul_of_nonneg_right (by linarith only [hlog]) (hJ k)).trans hframe'
    have hm := mul_le_mul_of_nonneg_left hlow
      (div_nonneg (vonMangoldt_nonneg (n := k)) (Nat.cast_nonneg k))
    dsimp only [e, g]
    nlinarith only [hm]
  have hgzero (k : ℕ) (hk : N < k) : g k = 0 := by
    dsimp only [g]
    rw [Nat.div_eq_of_lt hk]
    simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty, mul_zero]
  have hfinite (K : ℕ) (hNK : N ≤ K) :
      (Real.log N - 2 * Real.log Q) * (∑ k ∈ Icc 1 K, e k) ≤
        poleDefect N (fun n => ∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) +
          (1 + Real.log Q) * E := by
    have hsum := sum_le_sum fun k (hk : k ∈ Icc 1 K) => hpoint k (mem_Icc.mp hk).1
    have hsumg : (∑ k ∈ Icc 1 K, g k) = ∑ k ∈ Icc 1 N, g k := by
      apply (sum_subset (Icc_subset_Icc le_rfl hNK) ?_).symm
      intro k hk hnot
      apply hgzero
      have hk1 := (mem_Icc.mp hk).1
      by_contra h
      exact hnot (mem_Icc.mpr ⟨hk1, Nat.le_of_not_gt h⟩)
    rw [sum_sub_distrib, ← mul_sum, hsumg] at hsum
    have hmoment := sum_primeConductorDilationJump_logMoment_le (by omega : 1 ≤ Q) a K
    have hmoment_eq : (∑ k ∈ Icc 1 K, Real.log k * e k) =
        ∑ k ∈ Icc 1 K, vonMangoldt k * Real.log k / (k : ℝ) *
          ∑ m ∈ Icc 1 Q, primeConductorDilationJump Q a k m ^ 2 := by
      apply sum_congr rfl
      intro k _
      dsimp only [e, J]
      ring
    rw [hmoment_eq] at hsum
    have hdef : (∑ k ∈ Icc 1 N, g k) =
        poleDefect N (fun n => ∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) :=
      (poleDefect_ramanujanPacket_eq Q N a).symm
    rw [hdef] at hsum
    change _ ≤ (1 + Real.log Q) * E at hmoment
    linarith only [hsum, hmoment]
  have hlimit : Tendsto (fun K : ℕ => ∑ k ∈ Icc 1 K, e k) atTop (𝓝 E) := by
    have hh := (hasSum_primeConductorDilationJump_sq Q a).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
    change Tendsto (fun K : ℕ => ∑ k ∈ range (K + 1), e k) atTop (𝓝 E) at hh
    apply hh.congr'
    apply Eventually.of_forall
    intro K
    change (∑ k ∈ range (K + 1), e k) = ∑ k ∈ Icc 1 K, e k
    have hrange : range (K + 1) = insert 0 (Icc 1 K) := by
      ext k
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hrange, sum_insert (by simp)]
    simp only [e, Nat.cast_zero, div_zero, zero_mul, zero_add]
  have hlast := le_of_tendsto (hlimit.const_mul (Real.log N - 2 * Real.log Q))
    ((eventually_ge_atTop N).mono fun K hK => hfinite K hK)
  change (Real.log N - 3 * Real.log Q - 1) * E ≤ _
  nlinarith only [hlast]

/-- Logarithmically normalized packets retain the same relative arithmetic energy. -/
theorem poleDefect_normalizedRamanujanPacket_ge_logarithmic {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 2 ≤ N) (a : ℕ → ℝ) :
    ((Real.log N - 3 * Real.log Q - 1) / Real.log N) *
        (∑ m ∈ Icc 1 Q,
          (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2) ≤
      poleDefect N (primeHorizonExtension
        (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)) := by
  let b : ℕ → ℝ := fun m => a m / Real.sqrt (Real.log N)
  let y := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hx (n : ℕ) (hn : n ∈ Icc 1 N) :
      primeHorizonExtension y n = ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n := by
    rw [primeHorizonExtension_coe y ⟨n, hn⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
      (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = _
    rw [map_sum]
    apply sum_congr rfl
    intro m _
    change a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
    dsimp only [b]
    ring
  have hdef : poleDefect N (primeHorizonExtension y) =
      poleDefect N (fun n => ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n) := by
    unfold poleDefect
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro k hk
    have hnk : n * k ∈ Icc 1 N := by
      refine mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hn).1 (mem_Icc.mp hk).1, ?_⟩
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (mem_Icc.mp hn).1).mp (mem_Icc.mp hk).2
    rw [hx n hn, hx (n * k) hnk]
  have hscale : (∑ m ∈ Icc 1 Q,
      (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * b m ^ 2) =
        (∑ m ∈ Icc 1 Q,
          (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2) / Real.log N := by
    rw [sum_div]
    apply sum_congr rfl
    intro m _
    dsimp only [b]
    rw [div_pow, Real.sq_sqrt hL.le]
    ring
  have hraw := poleDefect_ramanujanPacket_ge_logarithmic hQ (by omega : 1 ≤ N) b
  rw [hscale, ← hdef] at hraw
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hraw

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.poleDefect_ramanujanPacket_ge_logarithmic

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.poleDefect_normalizedRamanujanPacket_ge_logarithmic
