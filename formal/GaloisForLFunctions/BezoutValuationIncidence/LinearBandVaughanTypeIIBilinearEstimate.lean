import GaloisForLFunctions.BezoutValuationIncidence.VaughanTypeIIShortAndAllHorizonMobiusL2Energy
import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIIEstimate
import GaloisForLFunctions.RHTower.Sieve.TypeIIHybridPiece

/-!
# Log-Free Linear-Band Vaughan Type-II Bilinear Estimates

In `RHTower/Sieve/`, the hybrid Type-II block and piece estimates (`TypeIIHybridBlockPower`,
`TypeIIHybridBlockRoot`, `TypeIIHybridVaughanScale`, `TypeIIHybridPiece`) bound the short-side
coefficient energy `∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ 2` via the global divisor-cube
bound `typeIIShortEnergyEnvelope (effHigh B P) ≤ 2 * (B / P) * (1 + (1 + log B)^3)`.

This module feeds the complementary-quotient compression bound `sum_typeIIShort_sq_le_band_width_sq`
from `BezoutValuationIncidence` directly into the `RHTower/Sieve/` Type-II bilinear assembly:

1. **Sub-Horizon Vanishing and Trans-Horizon Support Restriction
   (`sum_typeII_piece_eq_zero_of_le`, `sum_typeII_piece_eq_Ioc`):**
   Because `typeIIShort V m = 0` for `1 ≤ m ≤ V`, the entire Vaughan Type-II sum vanishes when
   `B - 1 ≤ L ≤ V`, and for `V ≤ L` the short-side sum in `sum_typeII_piece_eq` restricts strictly
   to the trans-horizon interval `m ∈ Finset.Ioc V L`.
2. **Log-Free Effective-Set Short Energy on Linear Bands
   (`sum_typeIIShort_sq_effSet_le_band_width_sq`, `sum_typeIIShort_sq_effSet_le_div`):**
   Whenever `effHigh B P ≤ (K + 1) * V` (`V, K ≥ 1`), the effective-set short energy is bounded by
   `K^2 * (effHigh B P - V) ≤ K^2 * (B / P)`, eliminating `typeIIPolylogEnvelope B = 1 + (1 + log B)^3`.
3. **Automatic Linear-Band Confinement When `U * V ≍ B` and Log-Free Hybrid Vaughan Estimate
   (`effHigh_le_of_maskedBlockSum_ne_zero`, `exists_norm_typeII_piece_le_linearBand_hybrid_vaughan`):**
   Every non-zero dyadic block `[P, Q)` (`Q ≤ 2 * P`) of `typeIILong U` satisfies `U + 1 < Q ≤ 2 * P`,
   forcing `U / 2 + 1 ≤ P` and `effHigh B P ≤ effHigh B (U / 2 + 1)`. Thus whenever the global
   Vaughan cutoffs satisfy `effHigh B (U / 2 + 1) ≤ (K + 1) * V`, **every active dyadic block** lies
   in the linear short-side band `(V, (K + 1) * V]`, eliminating `typeIIPolylogEnvelope B` from the
   entire hybrid Vaughan Type-II estimate.
-/

open Finset ArithmeticFunction RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Sub-Horizon Vanishing and Trans-Horizon Restriction of the Vaughan Type-II Piece -/

/-- When the short-side cutoff `V` covers `[1, L]` (`B - 1 ≤ L ≤ V`), the Vaughan Type-II sum on
`[A, B)` vanishes identically. -/
theorem sum_typeII_piece_eq_zero_of_le {A B L U V : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hLV : L ≤ V) (T r : ℝ) :
    (∑ n ∈ Finset.Ico A B,
      (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n) = 0 := by
  rw [sum_typeII_piece_eq hA hB hBL T r U V]
  refine Finset.sum_eq_zero fun d _ => ?_
  suffices hzero :
      (∑ m ∈ Finset.Icc 1 L, ((typeIIShort V m : ℝ) : ℂ) * maskedNdExp T r A B d m) = 0 by
    rw [hzero, mul_zero]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨hm1, hmL⟩ := Finset.mem_Icc.mp hm
  rw [typeIIShort_apply_eq_zero_of_le hm1 (hmL.trans hLV)]
  simp

/-- Because `typeIIShort V` vanishes on `[1, V]` and equals `-sieveSeq V moebiusReal` on `(V, L]`,
the inner short-side sum in `sum_typeII_piece_eq` restricts strictly to `Finset.Ioc V L`. -/
theorem sum_typeII_piece_eq_Ioc {A B L U V : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (hV : 1 ≤ V) (T r : ℝ) :
    (∑ n ∈ Finset.Ico A B,
      (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n) =
      ∑ d ∈ Finset.Icc 1 L, ((typeIILong U d : ℝ) : ℂ) *
        ∑ m ∈ Finset.Ioc V L, (-(sieveSeq V moebiusReal m : ℂ)) * maskedNdExp T r A B d m := by
  rw [sum_typeII_piece_eq hA hB hBL T r U V]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  by_cases hVL : V ≤ L
  · have hsplit : Finset.Icc 1 L = Finset.Icc 1 V ∪ Finset.Ioc V L := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 V) (Finset.Ioc V L) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hm1 hm2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hzero :
        (∑ m ∈ Finset.Icc 1 V, ((typeIIShort V m : ℝ) : ℂ) * maskedNdExp T r A B d m) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      obtain ⟨hm1, hmV⟩ := Finset.mem_Icc.mp hm
      rw [typeIIShort_apply_eq_zero_of_le hm1 hmV]
      simp
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hmV, _⟩ := Finset.mem_Ioc.mp hm
    rw [typeIIShort_eq_neg_sieveSeq_of_two_le V (by omega : 2 ≤ m)]
    push_cast
    ring
  · have hempty : Finset.Ioc V L = ∅ := by
      ext m
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨hm1, hmL⟩ := Finset.mem_Icc.mp hm
    rw [typeIIShort_apply_eq_zero_of_le hm1 (by omega : m ≤ V)]
    simp

/-! ## §2. Log-Free Effective-Set Short Energy on Linear Bands -/

/-- On any block `[P, Q)` whose effective short-side upper endpoint `effHigh B P` lies in the
linear horizon window `effHigh B P ≤ (K + 1) * V`, the effective-set short energy is bounded by
`K^2 * (effHigh B P - V)` with no logarithmic factor. -/
theorem sum_typeIIShort_sq_effSet_le_band_width_sq {A B L P Q V K : ℕ}
    (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hV : 1 ≤ V) (hK : 1 ≤ K)
    (hhi : effHigh B P ≤ (K + 1) * V) :
    (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ)) ≤
      (K : ℝ) ^ (2 : ℕ) * ((effHigh B P - V : ℕ) : ℝ) := by
  have hsub :
      (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ)) ≤
        ∑ m ∈ Finset.Icc 1 (effHigh B P), |typeIIShort V m| ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (effSet_subset_Icc_effHigh hP hQ)
      fun _ _ _ => sq_nonneg _
  have hnorm :
      (∑ m ∈ Finset.Icc 1 (effHigh B P), |typeIIShort V m| ^ (2 : ℕ)) =
        ∑ m ∈ Finset.Icc 1 (effHigh B P), ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [norm_typeIIShort_eq]
  exact hsub.trans (by rw [hnorm]; exact sum_typeIIShort_sq_le_band_width_sq hV hK hhi)

/-- Divisor-scale form of the log-free effective-set short energy bound: on any linear-band block
`effHigh B P ≤ (K + 1) * V`, the short-side energy is at most `K^2 * (B / P)`, replacing
`2 * (B / P) * typeIIPolylogEnvelope B` in `typeIIShortEnergyEnvelope_effHigh_le_div`. -/
theorem sum_typeIIShort_sq_effSet_le_div {A B L P Q V K : ℕ}
    (hP : 1 ≤ P) (hQ : 2 ≤ Q) (hV : 1 ≤ V) (hK : 1 ≤ K)
    (hhi : effHigh B P ≤ (K + 1) * V) :
    (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ)) ≤
      (K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)) := by
  refine (sum_typeIIShort_sq_effSet_le_band_width_sq hP hQ hV hK hhi).trans ?_
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hmulNat : P * (effHigh B P - V) ≤ B := by
    calc
      P * (effHigh B P - V) ≤ P * effHigh B P :=
        Nat.mul_le_mul_left P (Nat.sub_le _ _)
      _ ≤ B - 1 := Nat.mul_div_le (B - 1) P
      _ ≤ B := Nat.sub_le B 1
  have hdiv : ((effHigh B P - V : ℕ) : ℝ) ≤ (B : ℝ) / (P : ℝ) := by
    rw [le_div_iff₀ hP0]
    simpa [mul_comm] using (show (P : ℝ) * ((effHigh B P - V : ℕ) : ℝ) ≤ (B : ℝ) by
      exact_mod_cast hmulNat)
  exact mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)

/-! ## §3. Log-Free Hybrid Block Estimates on Linear Bands -/

/-- Log-free square envelope for one hybrid Type-II dyadic block in a linear short-side band of
width `K`: replaces `2 * typeIIPolylogEnvelope B` in `typeIIHybridBlockSqEnvelope` by `K^2`. -/
def linearBandTypeIIHybridBlockSqEnvelope (C T r : ℝ) (A B L P K : ℕ) : ℝ :=
  4 * C * (K : ℝ) ^ (2 : ℕ) * (B : ℝ) * Real.log L *
    ((P : ℝ) + typeIIHybridGapPowerEnvelope T r A B P)

/-- Log-free piece envelope for the full hybrid Vaughan Type-II sum when all active dyadic blocks
lie in a linear short-side band of width `K`. -/
def linearBandTypeIIHybridPieceEnvelope (C T r : ℝ) (A B L U V K : ℕ) : ℝ :=
  ((Nat.log 2 L : ℝ) + 1) *
    (Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
      typeIIHybridVaughanRootEnvelope T r A B U V)

/-- Closed log-free hybrid square bound for one Vaughan Type-II dyadic block `[P, Q)` satisfying
`effHigh B P ≤ (K + 1) * V`. -/
theorem exists_norm_maskedBlockSum_sq_le_linearBand_hybrid_power :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q K : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ V → 1 ≤ K →
      1 ≤ P → 2 ≤ Q → Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      effHigh B P ≤ (K + 1) * V →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖ ^ (2 : ℕ)
        ≤ linearBandTypeIIHybridBlockSqEnvelope C T r A B L P K := by
  obtain ⟨C, hC0, hClong⟩ := exists_sum_typeIILong_sq_block_le
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q K hT hr hA hB hL hV hK hP hQ hQ2P hQL h8 hhi
  have hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ) :=
    fun m hm => four_r_div_le_of_mem_effSet hA hP hQ hQ2P hr.le h8 hm
  have hmain := norm_maskedBlockSum_sq_le_hybrid_bound hT hr hA hB hP hQ hQ2P
    (fun d => typeIILong U d) (fun m => typeIIShort V m) hfour
  have hlong := sum_typeIILong_sq_block_abs_le hClong U P Q L hL hQL
  have hshort := sum_typeIIShort_sq_effSet_le_div (A := A) (L := L) hP hQ hV hK hhi
  have hgap :
      (∑ h ∈ Finset.Icc 1 (effGap A B P Q),
        hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h) ≤
        typeIIHybridGapPowerEnvelope T r A B P := by
    refine (sum_hybridGapCorrBound_le hT hr (one_le_effLow A Q) hP).trans ?_
    simpa only [typeIIHybridGapPowerEnvelope] using
      hybridGapSumBound_le_power (B := B) hT hr hA hP hQ hQ2P
  have hQcast : (Q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hQ2P
  have hDcast : ((Q - P : ℕ) : ℝ) ≤ 2 * (P : ℝ) := by
    exact_mod_cast le_trans (Nat.sub_le Q P) hQ2P
  have hlog0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hP)
  have hgap0 : 0 ≤ ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
      hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h :=
    Finset.sum_nonneg fun h _ =>
      hybridGapCorrBound_nonneg hT hr (effLow A Q) (effHigh B P) P Q h
  have hshort0 : 0 ≤ ∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEenv0 : 0 ≤ (K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)) := by positivity
  have hprefix : C * (Q : ℝ) * Real.log L ≤ C * (2 * (P : ℝ)) * Real.log L := by
    have hCQ := mul_le_mul_of_nonneg_left hQcast hC0.le
    exact mul_le_mul_of_nonneg_right hCQ hlog0
  have hbracket :
      (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
          + (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
            * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
              hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h))
        ≤ (2 * (P : ℝ)) * ((K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)))
          + ((K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)))
            * (2 * typeIIHybridGapPowerEnvelope T r A B P) := by
    have h1 := mul_le_mul hDcast hshort hshort0 (by positivity)
    have h2 := mul_le_mul hshort
      (mul_le_mul_of_nonneg_left hgap (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity) hEenv0
    linarith
  have hraw0 : 0 ≤
      (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
        + (∑ m ∈ effSet A B P Q L, |typeIIShort V m| ^ (2 : ℕ))
          * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
            hybridGapCorrBound T r (effLow A Q) (effHigh B P) P Q h)) := by positivity
  have hlongEnv0 : 0 ≤ C * (Q : ℝ) * Real.log L := by positivity
  have hprefixEnv0 : 0 ≤ C * (2 * (P : ℝ)) * Real.log L := by positivity
  refine hmain.trans ?_
  refine (mul_le_mul hlong hbracket hraw0 hlongEnv0).trans ?_
  calc
    (C * (Q : ℝ) * Real.log L) *
        ((2 * (P : ℝ)) * ((K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)))
          + ((K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)))
            * (2 * typeIIHybridGapPowerEnvelope T r A B P))
      ≤ (C * (2 * (P : ℝ)) * Real.log L) *
          ((2 * (P : ℝ)) * ((K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)))
            + ((K : ℝ) ^ (2 : ℕ) * ((B : ℝ) / (P : ℝ)))
              * (2 * typeIIHybridGapPowerEnvelope T r A B P)) := by
        refine mul_le_mul_of_nonneg_right hprefix ?_
        have := typeIIHybridGapPowerEnvelope_nonneg hT hr A B P
        positivity
    _ = linearBandTypeIIHybridBlockSqEnvelope C T r A B L P K := by
        rw [linearBandTypeIIHybridBlockSqEnvelope]
        field_simp
        ring

/-- Root-form log-free hybrid bound for one Vaughan Type-II dyadic block `[P, Q)` satisfying
`effHigh B P ≤ (K + 1) * V`. -/
theorem exists_norm_maskedBlockSum_le_linearBand_hybrid_root :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q K : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ V → 1 ≤ K →
      1 ≤ P → 2 ≤ Q → Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      effHigh B P ≤ (K + 1) * V →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖
        ≤ Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          typeIIHybridBlockRootEnvelope T r A B P := by
  obtain ⟨C, hC0, hmain⟩ := exists_norm_maskedBlockSum_sq_le_linearBand_hybrid_power
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q K hT hr hA hB hL hV hK hP hQ hQ2P hQL h8 hhi
  have hsq := hmain (U := U) hT hr hA hB hL hV hK hP hQ hQ2P hQL h8 hhi
  have hfact := mul_add_typeIIHybridGapPowerEnvelope_eq_components (B := B) hT hr hA hP
  have hK0 : 0 ≤ 4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L := by
    have hlog : (0 : ℝ) ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
    positivity
  have hcomp0 := typeIIHybridBlockComponents_nonneg hT hr A B P
  have hrew :
      linearBandTypeIIHybridBlockSqEnvelope C T r A B L P K =
        (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          typeIIHybridBlockComponents T r A B P := by
    rw [linearBandTypeIIHybridBlockSqEnvelope, ← hfact]
    ring
  rw [hrew] at hsq
  have hE0 : 0 ≤
      (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
        typeIIHybridBlockComponents T r A B P := mul_nonneg hK0 hcomp0
  have hsqrt :
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖ ≤
        Real.sqrt ((4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          typeIIHybridBlockComponents T r A B P) := by
    have h1 := Real.sq_sqrt hE0
    nlinarith [norm_nonneg (maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m)),
      Real.sqrt_nonneg ((4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
        typeIIHybridBlockComponents T r A B P)]
  calc
    ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
        (fun m => typeIIShort V m)‖
      ≤ Real.sqrt ((4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          typeIIHybridBlockComponents T r A B P) := hsqrt
    _ = Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          Real.sqrt (typeIIHybridBlockComponents T r A B P) := Real.sqrt_mul hK0 _
    _ ≤ Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          typeIIHybridBlockRootEnvelope T r A B P :=
        mul_le_mul_of_nonneg_left
          (sqrt_typeIIHybridBlockComponents_le_rootEnvelope (B := B) hT hr hA hP)
          (Real.sqrt_nonneg _)

/-! ## §4. Automatic Linear-Band Confinement Across All Active Dyadic Blocks When `U * V ≍ B` -/

/-- Because `typeIILong U` vanishes up to `U`, any non-zero dyadic block `[P, Q)` (`Q ≤ 2 * P`)
satisfies `U + 1 < Q ≤ 2 * P`, hence `U / 2 + 1 ≤ P` and `effHigh B P ≤ effHigh B (U / 2 + 1)`. -/
theorem effHigh_le_of_maskedBlockSum_ne_zero {T r : ℝ} {A B L U V P Q : ℕ}
    (hQ2P : Q ≤ 2 * P)
    (hne : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) ≠ 0) :
    effHigh B P ≤ effHigh B (U / 2 + 1) := by
  have hupper := upper_gt_truncation_of_maskedBlockSum_typeIILong_ne_zero hne
  have hUP : U / 2 + 1 ≤ P := by omega
  unfold effHigh
  exact Nat.div_le_div_left hUP (by omega : 0 < U / 2 + 1)

/-- Whenever the global Vaughan cutoffs `U, V` satisfy `effHigh B (U / 2 + 1) ≤ (K + 1) * V`,
every dyadic block `[P, Q)` (`Q ≤ 2 * P`)—whether support-empty or active—obeys the log-free
Vaughan-scale hybrid root estimate. -/
theorem exists_norm_maskedBlockSum_le_linearBand_hybrid_vaughan :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V P Q K : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → 1 ≤ U → 1 ≤ V → 1 ≤ K →
      1 ≤ P → 2 ≤ Q → Q ≤ 2 * P → Q ≤ L + 1 → 8 * r ≤ (A : ℝ) →
      effHigh B (U / 2 + 1) ≤ (K + 1) * V →
      ‖maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
          (fun m => typeIIShort V m)‖
        ≤ Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
          typeIIHybridVaughanRootEnvelope T r A B U V := by
  obtain ⟨C, hC0, hmain⟩ := exists_norm_maskedBlockSum_le_linearBand_hybrid_root
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V P Q K hT hr hA hB hL hU hV hK hP hQ hQ2P hQL h8 hUV
  by_cases hzero : maskedBlockSum T r A B L P Q (fun d => typeIILong U d)
      (fun m => typeIIShort V m) = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (typeIIHybridVaughanRootEnvelope_nonneg T r A B U V)
  · have hhi : effHigh B P ≤ (K + 1) * V :=
      (effHigh_le_of_maskedBlockSum_ne_zero hQ2P hzero).trans hUV
    have hblock := hmain (U := U) (V := V) hT hr hA hB hL hV hK hP hQ hQ2P hQL h8 hhi
    have hscale := typeIIHybridBlockRootEnvelope_le_vaughan_of_ne_zero
      hT hr hA hU hV hP hQ hQ2P hzero
    exact hblock.trans (mul_le_mul_of_nonneg_left hscale (Real.sqrt_nonneg _))

/-- **Log-Free Hybrid Vaughan Type-II Estimate (`exists_norm_typeII_piece_le_linearBand_hybrid_vaughan`):**
Whenever the Vaughan cutoffs `U, V` satisfy `effHigh B (U / 2 + 1) ≤ (K + 1) * V`, complementary-quotient
compression (`sum_typeIIShort_sq_le_band_width_sq`) eliminates the cubic logarithmic factor
`typeIIPolylogEnvelope B = 1 + (1 + log B)^3` from `exists_norm_typeII_piece_le_hybrid_vaughan`. -/
theorem exists_norm_typeII_piece_le_linearBand_hybrid_vaughan :
    ∃ C : ℝ, 0 < C ∧ ∀ {T r : ℝ} {A B L U V K : ℕ},
      0 < T → 0 < r → 1 ≤ A → 1 ≤ B → 1 ≤ L → B - 1 ≤ L →
      1 ≤ U → 1 ≤ V → 1 ≤ K → 8 * r ≤ (A : ℝ) →
      effHigh B (U / 2 + 1) ≤ (K + 1) * V →
      ‖∑ n ∈ Finset.Ico A B,
          (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖
        ≤ linearBandTypeIIHybridPieceEnvelope C T r A B L U V K := by
  obtain ⟨C, hC0, hblock⟩ := exists_norm_maskedBlockSum_le_linearBand_hybrid_vaughan
  refine ⟨C, hC0, ?_⟩
  intro T r A B L U V K hT hr hA hB hL hBL hU hV hK h8 hUV
  have hstart := norm_typeII_piece_le_sum_blockSums hA hB hBL T r U V
  have hpoint : ∀ j ∈ Finset.range (Nat.log 2 L + 1),
      ‖maskedBlockSum T r A B L (2 ^ j) (min (2 ^ (j + 1)) (L + 1))
        (fun d => typeIILong U d) (fun m => typeIIShort V m)‖
      ≤ Real.sqrt (4 * C * (K : ℝ) ^ (2 : ℕ) * Real.log L) *
        typeIIHybridVaughanRootEnvelope T r A B U V := by
    intro j _
    have hP : 1 ≤ 2 ^ j := one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))
    have hpow2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have hQ : 2 ≤ min (2 ^ (j + 1)) (L + 1) := by
      rw [le_min_iff]
      constructor
      · rw [hpow2]; omega
      · omega
    have hQ2P : min (2 ^ (j + 1)) (L + 1) ≤ 2 * 2 ^ j :=
      le_trans (min_le_left _ _) (by rw [hpow2])
    have hQL : min (2 ^ (j + 1)) (L + 1) ≤ L + 1 := min_le_right _ _
    exact hblock hT hr hA hB hL hU hV hK hP hQ hQ2P hQL h8 hUV
  refine hstart.trans ?_
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [linearBandTypeIIHybridPieceEnvelope, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

end

end GaloisForLFunctions.BezoutValuationIncidence
