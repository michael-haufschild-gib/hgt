import GaloisForLFunctions.ArithmeticCouplingTheory.TheMertensPolarization
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilEnergyControlsThePrimeDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.HorizonKernelEuclideanIdentities
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The complete Weil form on packets: Euler's constant cancels Mertens' constant

A packet `F : ℕ → ℝ` sits on the atoms `log n`, `n ≤ N`, with amplitudes `x_n = F(n)/√n`
(`atomAmplitude`). On these amplitudes Weil's prime matrix is the prime dilation form
(`atomicWeilForm_atomAmplitude`):

  `⟨P x, x⟩ = P_N(F) = Σ_{kn ≤ N} (Λ(k)/k) · 2F(n)F(kn)/n`.

The complete Weil matrix of strictly separated atoms carries the archimedean counterterm
`log N − γ` on its diagonal (RAPT `completeWeilEnergy_eq_decomposition`). With the Mertens
polarization `P_N = Σ F²/n (ψ₁(⌊N/n⌋) + log n) − J_N` the `log N` and the `−γ` meet the prime
diagonal `ψ₁(M) = Σ_{k ≤ M} Λ(k)/k = log M − γ + o(1)` and cancel exactly
(`completeWeilEnergy_atomAmplitude`):

  `E(x) = J_N(F) + Σ_{n ≤ N} F(n)²/n · (s_c + e_N − R(⌊N/n⌋) + δ_N(n)) + (pole terms)`,

with `J_N(F) ≥ 0` the dilation jump energy, `s_c` the self finite part of the atom profile, `e_N`
its vanishing error, `R(M) = ψ₁(M) − log M + γ → 0` the Mertens remainder
(`tendsto_mertensRemainder`, `abs_mertensRemainder_le`) and `δ_N(n) = log(N/(n⌊N/n⌋)) ∈ [0, log 2]`
the floor defect (`floorDefect_nonneg`, `floorDefect_le_log_two`).

So on every packet the complete form is a sum of squares of dilation jumps plus a bounded diagonal
plus the pole and boundary terms: the pole enters only through Mertens' constant and the running
counterterm, and both are cancelled. On the coherent prime sector the jumps are incidence events
(`completeWeilEnergy_incidencePacket`).
-/

open Finset ArithmeticFunction Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The amplitudes `x_n = F(n)/√n` of a packet on the atoms `log n`. -/
def atomAmplitude (F : ℕ → ℝ) (n : ℕ) : ℝ := F n / Real.sqrt n

/-- The divisor half of Weil's prime kernel: `Λ(n/m)/√(n/m)` when `m ∣ n`. -/
def divisorKernel (m n : ℕ) : ℝ := if m ∣ n then Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ) else 0

theorem weilPrimeKernel_eq_divisorKernel_add (m n : ℕ) :
    weilPrimeKernel m n = divisorKernel m n + divisorKernel n m := by
  unfold weilPrimeKernel divisorKernel
  by_cases hmn : m = n
  · subst hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [Nat.div_self hm]
  by_cases h1 : m ∣ n
  · have h2 : ¬n ∣ m := fun h => hmn (Nat.dvd_antisymm h1 h)
    simp [h1, h2, hmn]
  · by_cases h2 : n ∣ m
    · simp [h1, h2, Ne.symm hmn]
    · simp [h1, h2]

/-- Summing the divisor half over the horizon box is summing over dilation pairs. -/
theorem sum_divisorKernel_eq (N : ℕ) (x : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * divisorKernel m n =
      ∑ p ∈ dilationPairs N, Λ p.1 / Real.sqrt p.1 * (x p.2 * x (p.1 * p.2)) := by
  rw [sum_dilationPairs_eq N (fun k m => Λ k / Real.sqrt k * (x m * x (k * m)))]
  refine sum_congr rfl fun m hm => ?_
  have hm0 : 0 < m := by simp only [mem_Icc] at hm; omega
  have hfilter : ∑ n ∈ Icc 1 N, x m * x n * divisorKernel m n =
      ∑ n ∈ (Icc 1 N).filter (fun n => m ∣ n), x m * x n * (Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)) := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    unfold divisorKernel
    split_ifs <;> simp
  have himage : (Icc 1 N).filter (fun n => m ∣ n) = (Icc 1 (N / m)).image (fun k => k * m) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, k, rfl⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hm0).mpr (by rw [mul_comm]; exact hnN)⟩, mul_comm _ _⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hn1
      · exact hk
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hk1 hm0, (Nat.le_div_iff_mul_le hm0).mp hkN⟩, Dvd.intro_left k rfl⟩
  rw [hfilter, himage, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hm0 h]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.mul_div_cancel _ hm0]
  ring

/-- Weil's prime form on atoms is twice the divisor sum over dilation pairs. -/
theorem atomicWeilForm_eq_dilationPairs (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x =
      2 * ∑ p ∈ dilationPairs N, Λ p.1 / Real.sqrt p.1 * (x p.2 * x (p.1 * p.2)) := by
  have hsplit : atomicWeilForm N x = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * divisorKernel m n +
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x n * x m * divisorKernel n m := by
    rw [atomicWeilForm, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [weilPrimeKernel_eq_divisorKernel_add]; ring
  rw [hsplit, sum_comm (f := fun m n => x n * x m * divisorKernel n m), sum_divisorKernel_eq]
  ring

/-- **The prime matrix on packet amplitudes is the prime dilation form.** -/
theorem atomicWeilForm_atomAmplitude (N : ℕ) (F : ℕ → ℝ) :
    atomicWeilForm N (atomAmplitude F) = primeDilationForm N F := by
  rw [atomicWeilForm_eq_dilationPairs, primeDilationForm, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨hk, hn, -⟩ := mem_dilationPairs.mp hp
  have hk0 : (0 : ℝ) < p.1 := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < p.2 := by exact_mod_cast hn
  have hsk := Real.sqrt_pos.mpr hk0
  have hsn := Real.sqrt_pos.mpr hn0
  have hk' : (p.1 : ℝ) = Real.sqrt p.1 ^ 2 := (Real.sq_sqrt hk0.le).symm
  have hn' : (p.2 : ℝ) = Real.sqrt p.2 ^ 2 := (Real.sq_sqrt hn0.le).symm
  simp only [atomAmplitude]
  rw [Nat.cast_mul, Real.sqrt_mul hk0.le]
  conv_rhs => rw [hk', hn']
  field_simp

theorem atomAmplitude_sq {n : ℕ} (hn : 1 ≤ n) (F : ℕ → ℝ) :
    atomAmplitude F n ^ 2 = F n ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [atomAmplitude, div_pow, Real.sq_sqrt hn0.le]

/-- **The jump energy is the pole defect in packet coordinates.** With `x = F/√n`, the dilation jump
energy `J_N(F)` is the Dirichlet energy `D_N(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²` of the pole
relations, so the Mertens polarization is RAPT's ground-state identity
`atomicWeilForm_add_poleDefect` written for packets. -/
theorem jumpEnergy_eq_poleDefect (N : ℕ) (F : ℕ → ℝ) :
    jumpEnergy N F = poleDefect N (atomAmplitude F) := by
  rw [jumpEnergy, sum_dilationPairs_eq N (fun k n => Λ k / k * ((F (k * n) - F n) ^ 2 / n)),
    poleDefect]
  refine sum_congr rfl fun m hm => sum_congr rfl fun t ht => ?_
  have hm0 : (0 : ℝ) < m := by
    have := (mem_Icc.mp hm).1; exact_mod_cast this
  have ht0 : (0 : ℝ) < t := by
    have := (mem_Icc.mp ht).1; exact_mod_cast this
  have hsm := Real.sqrt_pos.mpr hm0
  have hst := Real.sqrt_pos.mpr ht0
  have hm' : (m : ℝ) = Real.sqrt m ^ 2 := (Real.sq_sqrt hm0.le).symm
  have ht' : (t : ℝ) = Real.sqrt t ^ 2 := (Real.sq_sqrt ht0.le).symm
  simp only [atomAmplitude]
  rw [Nat.cast_mul, Real.sqrt_mul hm0.le, mul_comm t m]
  conv_lhs => rw [hm', ht']
  field_simp

/-! ### The Mertens remainder and the floor defect -/

/-- The Mertens remainder `R(M) = ψ₁(M) − log M + γ`. -/
def mertensRemainder (M : ℕ) : ℝ := mertensSum M - Real.log M + Real.eulerMascheroniConstant

/-- **Mertens' second theorem**: `R(M) → 0`. -/
theorem tendsto_mertensRemainder : Tendsto mertensRemainder atTop (𝓝 0) := by
  have h := RHTower.tendsto_sum_vonMangoldt_div_sub_log
  have h2 := h.add_const Real.eulerMascheroniConstant
  rw [neg_add_cancel] at h2
  refine h2.congr fun M => ?_
  simp [mertensRemainder, mertensSum]

/-- **Mertens' first theorem** bounds the remainder explicitly. -/
theorem abs_mertensRemainder_le {M : ℕ} (hM : 1 ≤ M) :
    |mertensRemainder M| ≤ Real.log 4 + 4 + Real.eulerMascheroniConstant := by
  have h := RHTower.Mertens.mertens_first M hM
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  unfold mertensRemainder mertensSum
  calc |(∑ k ∈ Icc 1 M, Λ k / k) - Real.log M + Real.eulerMascheroniConstant|
      ≤ |(∑ k ∈ Icc 1 M, Λ k / k) - Real.log M| + |Real.eulerMascheroniConstant| :=
        abs_add_le _ _
    _ ≤ Real.log 4 + 4 + Real.eulerMascheroniConstant := by
        rw [abs_of_nonneg hγ]; linarith

/-- The floor defect `δ_N(n) = log N − log n − log ⌊N/n⌋`. -/
def floorDefect (N n : ℕ) : ℝ := Real.log N - Real.log n - Real.log (N / n : ℕ)

theorem floorDefect_nonneg {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) : 0 ≤ floorDefect N n := by
  have hq : 1 ≤ N / n := (Nat.one_le_div_iff hn).mpr hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < (N / n : ℕ) := by exact_mod_cast hq
  have hle : ((n * (N / n) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N n
  rw [floorDefect, sub_sub, ← Real.log_mul hn0.ne' hq0.ne', sub_nonneg]
  push_cast at hle
  exact Real.log_le_log (mul_pos hn0 hq0) hle

theorem floorDefect_le_log_two {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    floorDefect N n ≤ Real.log 2 := by
  have hq : 1 ≤ N / n := (Nat.one_le_div_iff hn).mpr hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < (N / n : ℕ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : N ≤ 2 * (n * (N / n)) := by
    have hdm := Nat.div_add_mod N n
    have hmod := Nat.mod_lt N (show n > 0 by omega)
    have hnq : n ≤ n * (N / n) := Nat.le_mul_of_pos_right n hq
    linarith
  have h2 : (N : ℝ) ≤ 2 * ((n : ℝ) * (N / n : ℕ)) := by exact_mod_cast h1
  have hlog := Real.log_le_log hN0 h2
  rw [Real.log_mul two_ne_zero (mul_pos hn0 hq0).ne', Real.log_mul hn0.ne' hq0.ne'] at hlog
  unfold floorDefect
  linarith

/-- The diagonal coefficient of a packet: `log N − γ − ψ₁(⌊N/n⌋) − log n = δ_N(n) − R(⌊N/n⌋)`. -/
theorem log_sub_euler_sub_mertens (N n : ℕ) :
    Real.log N - Real.eulerMascheroniConstant - mertensSum (N / n) - Real.log n =
      floorDefect N n - mertensRemainder (N / n) := by
  simp only [floorDefect, mertensRemainder]; ring

/-! ### The complete energy of a packet -/

/-- **The complete Weil energy of a packet.** For strictly separated atoms, the complete energy of
the amplitudes `F(n)/√n` is the dilation jump energy plus a diagonal in which the archimedean
counterterm `log N − γ` and the Mertens sum cancel to `δ_N(n) − R(⌊N/n⌋)`, plus the pole and
boundary terms of the atom profile. -/
theorem completeWeilEnergy_atomAmplitude {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hsep : c / N < atomSpacing N) (F : ℕ → ℝ) :
    completeWeilEnergy φ c N (horizonProfileVector (atomAmplitude F) N) =
      jumpEnergy N F + ∑ n ∈ Icc 1 N, F n ^ 2 / n * (completeWeilSelfFinitePart φ c +
        completeWeilSelfError φ c N + floorDefect N n - mertensRemainder (N / n)) +
      (⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (horizonProfileVector (atomAmplitude F) N), horizonProfileVector (atomAmplitude F) N⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
          (horizonProfileVector (atomAmplitude F) N), horizonProfileVector (atomAmplitude F) N⟫ +
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (horizonProfileVector (atomAmplitude F) N), horizonProfileVector (atomAmplitude F) N⟫) := by
  set x := horizonProfileVector (atomAmplitude F) N
  have hext : ∀ n ∈ Icc 1 N, primeHorizonExtension x n = atomAmplitude F n := fun n hn => by
    simp [primeHorizonExtension, hn, x, horizonProfileVector]
  have hnorm : ‖x‖ ^ 2 = ∑ n ∈ Icc 1 N, F n ^ 2 / n := by
    rw [horizonProfileVector_norm_sq]
    exact sum_congr rfl fun n hn => atomAmplitude_sq (mem_Icc.mp hn).1 F
  have hprime : ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, x⟫ = primeDilationForm N F := by
    rw [← atomicWeilForm_primeHorizonExtension, atomicWeilForm_congr hext,
      atomicWeilForm_atomAmplitude]
  rw [completeWeilEnergy_eq_decomposition hφ hsupp hM hc hN hsep, renormalizedPrimeEnergy, hprime,
    primeDilationForm_eq, mertensDiagonal, hnorm]
  have hdiag : ∀ n ∈ Icc 1 N, F n ^ 2 / n * (completeWeilSelfFinitePart φ c +
      completeWeilSelfError φ c N + floorDefect N n - mertensRemainder (N / n)) =
      Real.log N * (F n ^ 2 / n) - F n ^ 2 / n * (mertensSum (N / n) + Real.log n) +
        (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
          completeWeilSelfError φ c N) * (F n ^ 2 / n) := fun n _ => by
    rw [show completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N + floorDefect N n -
        mertensRemainder (N / n) = completeWeilSelfFinitePart φ c + completeWeilSelfError φ c N +
          (Real.log N - Real.eulerMascheroniConstant - mertensSum (N / n) - Real.log n) by
      rw [log_sub_euler_sub_mertens]; ring]
    ring
  rw [sum_congr rfl hdiag, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  ring

/-- **On the coherent prime sector the complete energy is incidence squares plus a bounded
diagonal plus the pole and boundary terms.** -/
theorem completeWeilEnergy_incidencePacket {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hsep : c / N < atomSpacing N)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℕ → ℝ) :
    completeWeilEnergy φ c N (horizonProfileVector (atomAmplitude (incidencePacket P b)) N) =
      (∑ p ∈ dilationPairs N, Λ p.1 / p.1 *
        ((if p.1.minFac ∈ P ∧ ¬p.1.minFac ∣ p.2 then b p.1.minFac ^ 2 else 0) / p.2)) +
      ∑ n ∈ Icc 1 N, incidencePacket P b n ^ 2 / n * (completeWeilSelfFinitePart φ c +
        completeWeilSelfError φ c N + floorDefect N n - mertensRemainder (N / n)) +
      (⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (horizonProfileVector (atomAmplitude (incidencePacket P b)) N),
          horizonProfileVector (atomAmplitude (incidencePacket P b)) N⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
          (horizonProfileVector (atomAmplitude (incidencePacket P b)) N),
          horizonProfileVector (atomAmplitude (incidencePacket P b)) N⟫ +
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (horizonProfileVector (atomAmplitude (incidencePacket P b)) N),
          horizonProfileVector (atomAmplitude (incidencePacket P b)) N⟫) := by
  rw [completeWeilEnergy_atomAmplitude hφ hsupp hM hc hN hsep, jumpEnergy_incidencePacket hP]

end GaloisForLFunctions.ArithmeticCouplingTheory
