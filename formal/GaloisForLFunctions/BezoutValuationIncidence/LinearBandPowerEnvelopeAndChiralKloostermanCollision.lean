import GaloisForLFunctions.BezoutValuationIncidence.LinearBandVaughanTypeIIBilinearEstimate
import GaloisForLFunctions.BezoutValuationIncidence.KloostermanTerminalBlockAndGlobalFrequencyCollision
import GaloisForLFunctions.RHTower.Sieve.KubalalikaPowerEnvelope
import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionChirality
import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionGram

/-!
# Quadratic-Log Kubalalika Power Envelopes and Chiral / Fourth-Moment Kloosterman Collision Bounds on Linear Type-II Bands

This module connects `LinearBandVaughanTypeIIBilinearEstimate` and
`KloostermanTerminalBlockAndGlobalFrequencyCollision` (`BezoutValuationIncidence`) to
`KubalalikaPowerEnvelope`, `KloostermanGlobalCollisionChirality`,
`KloostermanGlobalCollisionExactReal`, and `KloostermanGlobalCollisionGram` (`RHTower/Sieve/`):

1. **Halving the Logarithmic Exponent in the Kubalalika Power Envelope from `(1 + log B)^4` to
   `(1 + log B)^2` (`kubalalikaRootPower_le_sqrt_log`,
   `linearBandTypeIIHybridPieceEnvelope_le_power`,
   `linearBandKubalalikaBlockPower`,
   `exists_norm_sum_vonMangoldt_ndPhaseExp_le_linearBand_kubalalika_power`):**
   In `KubalalikaPowerEnvelope.lean`, the Type-I piece `secondThirdMixedVaughanTypeIEnvelope_le_power`
   carries only `(1 + log B)^2`, and had to be inflated to `(1 + log B)^4` solely because
   `typeIIHybridPieceEnvelope_le_power` carried `(1 + log B)^4` from `typeIIPolylogEnvelope B = 1 + (1 + log B)^3`.
   Here we prove that `kubalalikaRootPower T r B U V` is bounded with `√(1 + log B)` rather than
   `1 + log B`, which combines with `√(4 C K^2 log B) ≤ 2 √C K √(1 + log B)` and
   `Nat.log 2 B + 1 ≤ 2 (1 + log B)` to bound `linearBandTypeIIHybridPieceEnvelope`—and hence the
   entire mixed second/third-derivative von Mangoldt block sum whenever
   `effHigh B (U / 2 + 1) ≤ (K + 1) * V`—with `(1 + log B)^2` instead of `(1 + log B)^4`.
2. **Exact Real / Chiral and Fourth-Moment Global Kloosterman Collision Bounds on Linear Type-II Bands
   (`kloostermanPrimeGlobalCollisionEnergy_typeIIShort_eq`,
   `kloostermanPrimeGlobalCollisionEnergy_typeIIShort_le_band_width_sq`,
   `kloostermanAverageResponseMassDefect_typeIIShort_le_band_width_sq`):**
   Connects `kloostermanPrimeGlobalCollisionEnergy_eq_localFourierProducts`,
   `kloostermanPrimeGlobalCollisionEnergy_add_heightOdd_eq_two_crossTuple`, and
   `kloostermanGlobalFrequencyCollisionEnergy_eq_average_responseMassDefect` to the log-free
   linear-band short-side energy bound `kloostermanSourceResidueEnergy_Icc_typeIIShort_le_band_width_sq`.
-/

open scoped BigOperators ComplexConjugate
open Finset ArithmeticFunction Complex RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Halving the Logarithmic Exponent in the Kubalalika Power Envelope -/

/-- `kubalalikaRootPower T r B U V` carries only a square-root logarithmic factor `√(1 + log B)`
rather than `1 + log B`: only the `P2` summand contains `√(1 + log B)` and `1 ≤ √(1 + log B)`. -/
theorem kubalalikaRootPower_le_sqrt_log {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {B U V : ℕ}
    (hB : 1 ≤ B) :
    kubalalikaRootPower T r B U V
      ≤ 64 * Real.sqrt (1 + Real.log B) *
          ((B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
            + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  set s : ℝ := 1 + Real.log B with hsdef
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hsqrts : (1 : ℝ) ≤ Real.sqrt s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hs
  set P2 : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) with hP2
  set P3 : ℝ := (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) with hP3
  set P4 : ℝ := (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP4
  set P5 : ℝ := (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP5
  have h2 : (0 : ℝ) ≤ P2 := by rw [hP2]; positivity
  have h3 : (0 : ℝ) ≤ P3 := by rw [hP3]; positivity
  have h4 : (0 : ℝ) ≤ P4 := by rw [hP4]; positivity
  have h5 : (0 : ℝ) ≤ P5 := by rw [hP5]; positivity
  have hrew : kubalalikaRootPower T r B U V = P3 + 64 * P4 + 9 * P2 * Real.sqrt s + 2 * P5 := by
    rw [kubalalikaRootPower, hP2, hP3, hP4, hP5, hsdef]
    ring
  rw [hrew]
  have h3s : P3 ≤ P3 * Real.sqrt s := le_mul_of_one_le_right h3 hsqrts
  have h4s : P4 ≤ P4 * Real.sqrt s := le_mul_of_one_le_right h4 hsqrts
  have h5s : P5 ≤ P5 * Real.sqrt s := le_mul_of_one_le_right h5 hsqrts
  nlinarith only [h2, h3, h4, h5, hsqrts, h3s, h4s, h5s]

/-- **Quadratic-Log Power Bound on `linearBandTypeIIHybridPieceEnvelope`
(`linearBandTypeIIHybridPieceEnvelope_le_power`):**
Replaces `512 * √C * (1 + log B)^4` in `KubalalikaPowerEnvelope.typeIIHybridPieceEnvelope_le_power`
with `256 * √C * K * (1 + log B)^2`, saving two full powers of `1 + log B`. -/
theorem linearBandTypeIIHybridPieceEnvelope_le_power {C T r : ℝ}
    (hC : 0 < C) (hT : 0 < T) (hr : 0 < r)
    {A B U V K : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hBA : B ≤ 2 * A) :
    linearBandTypeIIHybridPieceEnvelope C T r A B B U V K
      ≤ 256 * Real.sqrt C * (K : ℝ) * (1 + Real.log B) ^ 2 *
          ((B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
            + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
            + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hlogB : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
  set s : ℝ := 1 + Real.log B with hsdef
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  set S : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
      + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; positivity
  have h1 : ((Nat.log 2 B : ℝ) + 1) ≤ 2 * s := natLogTwo_succ_le_two_mul_one_add_log hB
  have hCKs : 0 ≤ 2 * Real.sqrt C * (K : ℝ) * Real.sqrt s := by positivity
  have hsqC : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
  have hsqs : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0
  have hrad : 4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log B
      ≤ (2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) ^ 2 := by
    have hval : (2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) ^ 2
        = 4 * C * (K : ℝ) ^ (2 : ℕ) * s := by
      calc (2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) ^ 2
          = 4 * (Real.sqrt C) ^ 2 * (K : ℝ) ^ (2 : ℕ) * (Real.sqrt s) ^ 2 := by ring
        _ = 4 * C * (K : ℝ) ^ (2 : ℕ) * s := by rw [hsqC, hsqs]
    rw [hval]
    have hlogs : Real.log B ≤ s := by rw [hsdef]; linarith
    exact mul_le_mul_of_nonneg_left hlogs (by positivity)
  have h2 : Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log B)
      ≤ 2 * Real.sqrt C * (K : ℝ) * Real.sqrt s := by
    calc Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log B)
        ≤ Real.sqrt ((2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) ^ 2) := Real.sqrt_le_sqrt hrad
      _ = 2 * Real.sqrt C * (K : ℝ) * Real.sqrt s := Real.sqrt_sq hCKs
  have h20 : 0 ≤ Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log B) := Real.sqrt_nonneg _
  have h3 : typeIIHybridVaughanRootEnvelope T r A B U V ≤ 64 * Real.sqrt s * S := by
    refine le_trans (typeIIHybridVaughanRootEnvelope_le_power hT hr hA hB hU hV hBA) ?_
    rw [hSdef, hsdef]
    exact kubalalikaRootPower_le_sqrt_log hT hr hB
  have h30 : 0 ≤ typeIIHybridVaughanRootEnvelope T r A B U V :=
    typeIIHybridVaughanRootEnvelope_nonneg T r A B U V
  rw [linearBandTypeIIHybridPieceEnvelope]
  have hprod : Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log B)
      * typeIIHybridVaughanRootEnvelope T r A B U V
      ≤ (2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) * (64 * Real.sqrt s * S) :=
    mul_le_mul h2 h3 h30 hCKs
  have hall : ((Nat.log 2 B : ℝ) + 1) *
      (Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log B)
        * typeIIHybridVaughanRootEnvelope T r A B U V)
      ≤ (2 * s) * ((2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) * (64 * Real.sqrt s * S)) :=
    mul_le_mul h1 hprod (mul_nonneg h20 h30) (by positivity)
  refine hall.trans (le_of_eq ?_)
  calc (2 * s) * ((2 * Real.sqrt C * (K : ℝ) * Real.sqrt s) * (64 * Real.sqrt s * S))
      = 256 * Real.sqrt C * (K : ℝ) * (s * (Real.sqrt s) ^ 2) * S := by ring
    _ = 256 * Real.sqrt C * (K : ℝ) * s ^ 2 * S := by rw [hsqs]; ring

/-- Quadratic-log Kubalalika block power envelope: replaces `(1 + log B)^4` in
`kubalalikaBlockPower` with `(1 + log B)^2` when all active Type-II blocks lie in a linear band. -/
def linearBandKubalalikaBlockPower (D T r : ℝ) (A B U V : ℕ) : ℝ :=
  D * (1 + Real.log B) ^ 2 *
    ((A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt (U * V)
      + (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ)
      + (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ)
      + (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ))

/-- **Quadratic-Log Mixed Hybrid Vaughan Block Estimate
(`exists_norm_sum_vonMangoldt_ndPhaseExp_le_linearBand_kubalalika_power`):**
Whenever `effHigh B (U / 2 + 1) ≤ (K + 1) * V`, the entire mixed second/third-derivative Vaughan +
Babu–Sankaranarayanan von Mangoldt block sum is bounded by `linearBandKubalalikaBlockPower`,
cutting the logarithmic exponent in `exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power`
from `(1 + log B)^4` to `(1 + log B)^2`. -/
theorem exists_norm_sum_vonMangoldt_ndPhaseExp_le_linearBand_kubalalika_power :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B U V K : ℕ},
      0 < T → 0 < r → 1 ≤ A → A ≤ B → B ≤ 2 * A → 1 ≤ U → 1 ≤ V → 1 ≤ K →
      U < A → U * V ≤ A → 8 * r ≤ (A : ℝ) →
      effHigh B (U / 2 + 1) ≤ (K + 1) * V →
      T * r * ((U * V : ℕ) : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 →
      (∀ b ∈ Finset.Icc 1 (U * V),
        fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) →
      ‖∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ linearBandKubalalikaBlockPower (1200000 + 256 * Real.sqrt C * (K : ℝ)) T r A B U V := by
  obtain ⟨C, hC0, hII⟩ := exists_norm_typeII_piece_le_linearBand_hybrid_vaughan
  refine ⟨C, hC0, ?_⟩
  intro T r A B U V K hT hr hA hAB hBA hU hV hK hUA hUVA h8 hUV_band hcurv hsecondUV
  have hB : 1 ≤ B := le_trans hA hAB
  have hUV1 : 1 ≤ U * V := by simpa using Nat.mul_le_mul hU hV
  have hVUV : V ≤ U * V := by simpa [mul_comm] using Nat.mul_le_mul_left V hU
  have hVA : V ≤ A := le_trans hVUV hUVA
  have hUVB : U * V ≤ B := le_trans hUVA hAB
  have hVB : V ≤ B := le_trans hVA hAB
  have hthirdUV := thirdDerivative_fibre_conditions hT hr hA hAB hBA hUVA h8 hcurv
  have hcondUV : ∀ b ∈ Finset.Icc 1 (U * V),
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1
        ∧ (fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) := by
    intro b hb
    obtain ⟨hspan, hrA, hlam3⟩ := hthirdUV b hb
    exact ⟨hspan, hrA, hlam3, hsecondUV b hb⟩
  have hVpow : (V : ℝ) ^ 3 ≤ ((U * V : ℕ) : ℝ) ^ 3 := by
    have : (V : ℝ) ≤ ((U * V : ℕ) : ℝ) := by exact_mod_cast hVUV
    gcongr
  have hcurvV : T * r * (V : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4 :=
    le_trans (mul_le_mul_of_nonneg_left hVpow (by positivity)) hcurv
  have hthirdV := thirdDerivative_fibre_conditions hT hr hA hAB hBA hVA h8 hcurvV
  have hcondV : ∀ b ∈ Finset.Icc 1 V,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1
        ∧ (fibreKernel T r A ≤
            secondThirdMixedFibreMainCoefficient T r A * (b : ℝ) ^ (-(1 / 2 : ℝ)) →
          nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) := by
    intro b hb
    obtain ⟨hspan, hrA, hlam3⟩ := hthirdV b hb
    have hbUV : b ∈ Finset.Icc 1 (U * V) := Finset.mem_Icc.2
      ⟨(Finset.mem_Icc.mp hb).1, le_trans (Finset.mem_Icc.mp hb).2 hVUV⟩
    exact ⟨hspan, hrA, hlam3, hsecondUV b hbUV⟩
  have hraw := norm_sum_vonMangoldt_ndPhaseExp_secondThird_mixed_le' hT hr hUA hA hB (by omega)
    hUVB hVB hcondUV hcondV
  have hI1 := sum_log_secondThirdMixedFibreBound_le hT hr hA hUV1 hUVA hAB hBA
  have hI2 := sum_two_secondThirdMixedFibreBound_log_le hT hr hA hVA hAB hBA
  have hIIbound := hII hT hr hA hB hB (by omega) hU hV hK h8 hUV_band
  have hTypeI :
      (∑ b ∈ Finset.Icc 1 (U * V), Real.log b * secondThirdMixedFibreBound T r A B b)
        + (∑ b ∈ Finset.Icc 1 V, 2 * secondThirdMixedFibreBound T r A B b *
            Real.log (((B - 1) / b + 1 - 1 : ℕ) : ℝ))
      ≤ secondThirdMixedVaughanTypeIEnvelope T r A B U V := by
    rw [secondThirdMixedVaughanTypeIEnvelope]
    push_cast at hI1
    linarith
  have hIpwr := secondThirdMixedVaughanTypeIEnvelope_le_power hT hr hA hAB hU hV hUVB
  have hIIpwr := linearBandTypeIIHybridPieceEnvelope_le_power (K := K) hC0 hT hr hA hB hU hV hBA
  rw [linearBandKubalalikaBlockPower]
  set s : ℝ := 1 + Real.log B with hsdef
  set P1 : ℝ := (A : ℝ) ^ (1 / 3 : ℝ) * (T * r) ^ (1 / 6 : ℝ) * Real.sqrt (U * V) with hP1
  set P2 : ℝ := (B : ℝ) ^ (3 / 2 : ℝ) * (T * r) ^ (-(1 / 2) : ℝ) with hP2
  set P3 : ℝ := (B : ℝ) * (V : ℝ) ^ (-(1 / 2) : ℝ) with hP3
  set P4 : ℝ := (T * r) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (3 / 4 : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP4
  set P5 : ℝ := (B : ℝ) * (U : ℝ) ^ (-(1 / 2) : ℝ) with hP5
  have h1 : (0 : ℝ) ≤ P1 := by rw [hP1]; positivity
  have h2 : (0 : ℝ) ≤ P2 := by rw [hP2]; positivity
  have h3 : (0 : ℝ) ≤ P3 := by rw [hP3]; positivity
  have h4 : (0 : ℝ) ≤ P4 := by rw [hP4]; positivity
  have h5 : (0 : ℝ) ≤ P5 := by rw [hP5]; positivity
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hCpos : 0 ≤ 256 * Real.sqrt C * (K : ℝ) * s ^ 2 := by positivity
  have hstep1 : 1200000 * s ^ 2 * (P1 + P2)
      ≤ 1200000 * s ^ 2 * (P1 + P2 + P3 + P4 + P5) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hstep2 : 256 * Real.sqrt C * (K : ℝ) * s ^ 2 * (P2 + P3 + P4 + P5)
      ≤ 256 * Real.sqrt C * (K : ℝ) * s ^ 2 * (P1 + P2 + P3 + P4 + P5) :=
    mul_le_mul_of_nonneg_left (by linarith) hCpos
  have hsplit : (1200000 + 256 * Real.sqrt C * (K : ℝ)) * s ^ 2 * (P1 + P2 + P3 + P4 + P5)
      = 1200000 * s ^ 2 * (P1 + P2 + P3 + P4 + P5)
        + 256 * Real.sqrt C * (K : ℝ) * s ^ 2 * (P1 + P2 + P3 + P4 + P5) := by ring
  linarith

/-! ## §2. Exact Real / Chiral and Fourth-Moment Kloosterman Collision Bounds on Linear Type-II Bands -/

/-- Because `typeIIShort V` is real-valued, on any prime-clock family
`Q = kloostermanPrimeIndexSet (P.image Subtype.val)` with real modulus weights `w : ℕ → ℝ`, the
global frequency collision energy `kloostermanGlobalFrequencyCollisionEnergy` is **equal** (no
inequality) to twice the sum of off-diagonal products of local unit-Fourier energies. -/
theorem kloostermanPrimeGlobalCollisionEnergy_typeIIShort_eq
    (P : Finset Nat.Primes) (w : ℕ → ℝ) (V N : ℕ) :
    let Q := kloostermanPrimeIndexSet (P.image Subtype.val)
    kloostermanGlobalFrequencyCollisionEnergy Q
        (fun q => (w q : ℂ)) (Finset.Icc 1 N) (fun n => ((typeIIShort V n : ℝ) : ℂ)) =
      2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
          (∑ x : (ZMod (q + 1))ˣ,
            Complex.normSq
              (kloostermanSourceFourier (q + 1) (Finset.Icc 1 N)
                (fun n => ((typeIIShort V n : ℝ) : ℂ)) x)) *
          ∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq
              (kloostermanSourceFourier (r + 1) (Finset.Icc 1 N)
                (fun n => ((typeIIShort V n : ℝ) : ℂ)) y) :=
  kloostermanPrimeGlobalCollisionEnergy_eq_localFourierProducts P w (typeIIShort V) (Finset.Icc 1 N)

/-- **Exact-Real Prime-Clock Collision Bound on Linear Type-II Short Bands
(`kloostermanPrimeGlobalCollisionEnergy_typeIIShort_le_band_width_sq`):**
Combines `kloostermanPrimeGlobalCollisionEnergy_typeIIShort_eq` with unit-to-complete Parseval
monotonicity (`sum_normSq_kloostermanSourceFourier_le_residueEnergy`) and the log-free linear-band
bound `kloostermanSourceResidueEnergy_Icc_typeIIShort_le_band_width_sq`, eliminating both the
`|Q|^2` Cauchy–Schwarz factor and the divisor-cube factor `(1 + log N)^3`. -/
theorem kloostermanPrimeGlobalCollisionEnergy_typeIIShort_le_band_width_sq
    (P : Finset Nat.Primes) (w : ℕ → ℝ) {V K N : ℕ}
    (hV : 1 ≤ V) (hK : 1 ≤ K) (hhi : N ≤ (K + 1) * V) :
    let Q := kloostermanPrimeIndexSet (P.image Subtype.val)
    kloostermanGlobalFrequencyCollisionEnergy Q
        (fun q => (w q : ℂ)) (Finset.Icc 1 N) (fun n => ((typeIIShort V n : ℝ) : ℂ)) ≤
      2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
          (((q + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) *
          (((r + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) := by
  dsimp only
  let Q := kloostermanPrimeIndexSet (P.image Subtype.val)
  let b : ℕ → ℂ := fun n => ((typeIIShort V n : ℝ) : ℂ)
  rw [kloostermanPrimeGlobalCollisionEnergy_typeIIShort_eq P w V N]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun r _ => ?_)
    (by norm_num)
  have hFq :
      (∑ x : (ZMod (q + 1))ˣ, Complex.normSq (kloostermanSourceFourier (q + 1) (Finset.Icc 1 N) b x))
        ≤ ((q + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ))) := by
    have h1 :
        (∑ x : (ZMod (q + 1))ˣ, Complex.normSq (kloostermanSourceFourier (q + 1) (Finset.Icc 1 N) b x))
          ≤ kloostermanSourceResidueEnergy q (Finset.Icc 1 N) b := by
      unfold kloostermanSourceResidueEnergy
      simpa only [Complex.sq_norm] using
        sum_normSq_kloostermanSourceFourier_le_residueEnergy (q + 1) (Finset.Icc 1 N) b
    exact h1.trans (kloostermanSourceResidueEnergy_Icc_typeIIShort_le_band_width_sq q hV hK hhi)
  have hFr :
      (∑ y : (ZMod (r + 1))ˣ, Complex.normSq (kloostermanSourceFourier (r + 1) (Finset.Icc 1 N) b y))
        ≤ ((r + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ))) := by
    have h1 :
        (∑ y : (ZMod (r + 1))ˣ, Complex.normSq (kloostermanSourceFourier (r + 1) (Finset.Icc 1 N) b y))
          ≤ kloostermanSourceResidueEnergy r (Finset.Icc 1 N) b := by
      unfold kloostermanSourceResidueEnergy
      simpa only [Complex.sq_norm] using
        sum_normSq_kloostermanSourceFourier_le_residueEnergy (r + 1) (Finset.Icc 1 N) b
    exact h1.trans (kloostermanSourceResidueEnergy_Icc_typeIIShort_le_band_width_sq r hV hK hhi)
  have hFq0 : 0 ≤ ∑ x : (ZMod (q + 1))ˣ,
      Complex.normSq (kloostermanSourceFourier (q + 1) (Finset.Icc 1 N) b x) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hFr0 : 0 ≤ ∑ y : (ZMod (r + 1))ˣ,
      Complex.normSq (kloostermanSourceFourier (r + 1) (Finset.Icc 1 N) b y) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hw0 : 0 ≤ Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ) :=
    mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hprod := mul_le_mul hFq hFr hFr0 (by positivity)
  calc
    (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
        (∑ x : (ZMod (q + 1))ˣ,
          Complex.normSq (kloostermanSourceFourier (q + 1) (Finset.Icc 1 N) b x)) *
        (∑ y : (ZMod (r + 1))ˣ,
          Complex.normSq (kloostermanSourceFourier (r + 1) (Finset.Icc 1 N) b y))
      = (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
          ((∑ x : (ZMod (q + 1))ˣ,
            Complex.normSq (kloostermanSourceFourier (q + 1) (Finset.Icc 1 N) b x)) *
          (∑ y : (ZMod (r + 1))ˣ,
            Complex.normSq (kloostermanSourceFourier (r + 1) (Finset.Icc 1 N) b y))) := by ring
    _ ≤ (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
          ((((q + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) *
          (((r + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ))))) :=
        mul_le_mul_of_nonneg_left hprod hw0
    _ = (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
          (((q + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) *
          (((r + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
            ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) := by ring

/-- **Common-Period Fourth-Moment Response Mass Defect Bound on Linear Type-II Short Bands
(`kloostermanAverageResponseMassDefect_typeIIShort_le_band_width_sq`):**
Combines `KloostermanGlobalCollisionGram.kloostermanGlobalFrequencyCollisionEnergy_eq_average_responseMassDefect`
with `kloostermanPrimeGlobalCollisionEnergy_typeIIShort_le_band_width_sq` to bound the common-period
average of the squared total-response mass defect with no logarithmic factor. -/
theorem kloostermanAverageResponseMassDefect_typeIIShort_le_band_width_sq
    (P : Finset Nat.Primes) (w : ℕ → ℝ) {V K N : ℕ}
    (hV : 1 ≤ V) (hK : 1 ≤ K) (hhi : N ≤ (K + 1) * V) :
    let Q := kloostermanPrimeIndexSet (P.image Subtype.val)
    let b : ℕ → ℂ := fun n => ((typeIIShort V n : ℝ) : ℂ)
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
      ∑ k : ZMod (kloostermanGlobalPeriod Q),
        (Complex.normSq
            (∑ q ∈ Q, (w q : ℂ) * kloostermanGlobalModulusTimeResponse q (Finset.Icc 1 N) b k.val) -
          ∑ q ∈ Q,
            Complex.normSq ((w q : ℂ) * kloostermanGlobalModulusTimeResponse q (Finset.Icc 1 N) b k.val)) ^ 2
      ≤ 2 * ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          (Complex.normSq (w q : ℂ) * Complex.normSq (w r : ℂ)) *
            (((q + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
              ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) *
            (((r + 1 : ℕ) : ℝ) * ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
              ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ)))) := by
  dsimp only
  rw [← kloostermanGlobalFrequencyCollisionEnergy_eq_average_responseMassDefect]
  exact kloostermanPrimeGlobalCollisionEnergy_typeIIShort_le_band_width_sq P w hV hK hhi

end

end GaloisForLFunctions.BezoutValuationIncidence
