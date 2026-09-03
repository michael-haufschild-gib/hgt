import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownTwistedSmoothHandoff
import GaloisForLFunctions.RHTower.Sieve.MaynardBoxFactorization
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateCellExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPerron
import GaloisForLFunctions.RHTower.Sieve.HalaszPerronAssembly
import GaloisForLFunctions.RHTower.Sieve.TripleConvolutionPerronSum

/-!
# Twisted Heath--Brown cell and literal-core selection

This module localizes the exact smooth Heath--Brown integral forced by a sharp twisted Chebyshev
prefix.  It preserves the signed full aggregate until frequency-cell extraction, then selects a
literal full dyadic core with every analytic and combinatorial loss explicit.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Exact damped coefficient mass of the complete finite Heath--Brown packet. -/
def heathBrownPacketDampedL1 (L X k : ℕ) (sigma : ℝ) : ℝ :=
  let M := (L + 1) ^ k * (X + 1) ^ k
  ∑ n ∈ Finset.Icc 1 M,
    ‖complexCoeff (heathBrownFiniteCompressedPacket L X k) n‖ *
      (n : ℝ) ^ (-sigma)

theorem heathBrownPacketDampedL1_nonneg (L X k : ℕ) (sigma : ℝ) :
    0 ≤ heathBrownPacketDampedL1 L X k sigma := by
  unfold heathBrownPacketDampedL1
  positivity

/-- Uniform vertical-line bound for the complete signed packet, retaining its exact finite
coefficient mass. -/
theorem norm_heathBrownDyadicAggregate_le_packetDampedL1
    (L X k : ℕ) (sigma t : ℝ) :
    ‖heathBrownDyadicAggregate L X k
        ((sigma : ℂ) + (t : ℝ) * I)‖ ≤
      heathBrownPacketDampedL1 L X k sigma := by
  let F := heathBrownFiniteCompressedPacket L X k
  let M := (L + 1) ^ k * (X + 1) ^ k
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro h
      apply hn
      simp [complexCoeff_apply, h]
    exact upperSupported_heathBrownFiniteCompressedPacket L X k n hnF
  rw [heathBrownDyadicAggregate,
    ← LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts]
  simpa only [F, M, heathBrownPacketDampedL1] using
    norm_LSeries_line_le_l1 hzero hsupp sigma t

/-- Continuity of the full signed packet after translating its ordinate by a physical twist. -/
theorem continuous_heathBrownDyadicAggregate_line_shift
    (L X k : ℕ) (sigma tau : ℝ) :
    Continuous (fun y : ℝ =>
      heathBrownDyadicAggregate L X k
        ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I)) := by
  let F := heathBrownFiniteCompressedPacket L X k
  let M := (L + 1) ^ k * (X + 1) ^ k
  have hzero : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsupp : ∀ n : ℕ, complexCoeff F n ≠ 0 → n ∈ Finset.Icc 1 M := by
    intro n hn
    have hnF : F n ≠ 0 := by
      intro h
      apply hn
      simp [complexCoeff_apply, h]
    exact upperSupported_heathBrownFiniteCompressedPacket L X k n hnF
  have hshift : Continuous (fun y : ℝ => y + tau) :=
    continuous_id.add continuous_const
  have hcont := (continuous_LSeries_line_of_support hzero hsupp sigma).comp hshift
  refine hcont.congr fun y => ?_
  change LSeries (complexCoeff (heathBrownFiniteCompressedPacket L X k))
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) = _
  rw [LSeries_heathBrownFiniteCompressedPacket_eq_sum_dyadicProducts,
    heathBrownDyadicAggregate]

/-- The shifted full-packet Mellin integrand is integrable on the complete vertical line. -/
theorem integrable_heathBrownDyadicAggregate_shift_mul_mellin_smoothWeight
    (L X k : ℕ) (tau : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownDyadicAggregate L X k
          ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)) := by
  let A : ℝ → ℂ := fun y =>
    heathBrownDyadicAggregate L X k
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I)
  let K : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * I)
  let P := heathBrownPacketDampedL1 L X k sigma
  have hA : Continuous A :=
    continuous_heathBrownDyadicAggregate_line_shift L X k sigma tau
  have hAbdd : ∀ y, ‖A y‖ ≤ P := fun y =>
    norm_heathBrownDyadicAggregate_le_packetDampedL1 L X k sigma (y + tau)
  have hK : Integrable K := verticalIntegrable_mellin_smoothWeight hN hH hsigma
  have hAK : Integrable fun y => A y * K y := by
    refine Integrable.bdd_mul (c := P) hK hA.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hAbdd
  exact hAK

/-- A positive quadratic-decay constant for the smoothing Mellin kernel. -/
theorem exists_menonMellinLocalizationConstant
    {N H sigma : ℝ} (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : ℝ,
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤ C * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C0, hC0, hkernel⟩ :=
    exists_bound_mellin_smoothWeight_line hN hH hsigma
  refine ⟨C0 + 1, by linarith, fun y => (hkernel y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- Quadratic Mellin decay localizes the shifted complete packet to a symmetric frequency band,
for any stated positive decay constant. -/
theorem integral_norm_heathBrownDyadicAggregate_shift_mellin_tail_le_of_bound
    (L X k : ℕ) {N H sigma C : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤ C * (1 + y ^ 2)⁻¹)
    (tau : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    (∫ y in (Set.Icc (-V) V)ᶜ,
      ‖heathBrownDyadicAggregate L X k
          ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * I)‖) ≤
      heathBrownPacketDampedL1 L X k sigma * C *
        (Real.pi - 2 * Real.arctan V) := by
  let A : ℝ → ℂ := fun y =>
    heathBrownDyadicAggregate L X k
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I)
  let K : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * I)
  let P := heathBrownPacketDampedL1 L X k sigma
  let tail := (Set.Icc (-V) V)ᶜ
  have hP : 0 ≤ P := heathBrownPacketDampedL1_nonneg L X k sigma
  have hA : ∀ y, ‖A y‖ ≤ P := fun y =>
    norm_heathBrownDyadicAggregate_le_packetDampedL1 L X k sigma (y + tau)
  have hK : ∀ y, ‖K y‖ ≤ C * (1 + y ^ 2)⁻¹ := by
    intro y
    exact hkernel y
  have hAKint : Integrable fun y => A y * K y := by
    simpa only [A, K] using
      integrable_heathBrownDyadicAggregate_shift_mul_mellin_smoothWeight
        L X k tau hN hH hsigma
  have hmajInt : Integrable fun y : ℝ => (P * C) * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul (P * C)
  have hmono : (∫ y in tail, ‖A y * K y‖) ≤
      ∫ y in tail, (P * C) * (1 + y ^ 2)⁻¹ := by
    apply setIntegral_mono_on hAKint.norm.integrableOn hmajInt.integrableOn
      measurableSet_Icc.compl
    intro y _hy
    rw [norm_mul]
    calc
      ‖A y‖ * ‖K y‖ ≤ P * (C * (1 + y ^ 2)⁻¹) :=
        mul_le_mul (hA y) (hK y) (norm_nonneg _) hP
      _ = (P * C) * (1 + y ^ 2)⁻¹ := by ring
  have htail := integral_compl_Icc_inv_one_add_sq_le hV
  calc
    (∫ y in (Set.Icc (-V) V)ᶜ, ‖A y * K y‖) ≤
        ∫ y in tail, (P * C) * (1 + y ^ 2)⁻¹ := hmono
    _ = (P * C) * ∫ y in tail, (1 + y ^ 2)⁻¹ := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (P * C) * (Real.pi - 2 * Real.arctan V) :=
      mul_le_mul_of_nonneg_left (by simpa only [tail] using htail)
        (mul_nonneg hP (by linarith))
    _ = P * C * (Real.pi - 2 * Real.arctan V) := by ring

/-- Quadratic Mellin decay localizes the shifted complete packet to a symmetric frequency band.
The only packet cost is its exact damped coefficient mass. -/
theorem exists_integral_norm_heathBrownDyadicAggregate_shift_mellin_tail_le
    (L X k : ℕ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 0 < sigma) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (tau : ℝ) {V : ℝ}, 0 ≤ V →
      (∫ y in (Set.Icc (-V) V)ᶜ,
        ‖heathBrownDyadicAggregate L X k
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * I)‖) ≤
        heathBrownPacketDampedL1 L X k sigma * C *
          (Real.pi - 2 * Real.arctan V) := by
  obtain ⟨C, hC, hkernel⟩ :=
    exists_menonMellinLocalizationConstant hN hH hsigma
  exact ⟨C, hC, fun tau V hV =>
    integral_norm_heathBrownDyadicAggregate_shift_mellin_tail_le_of_bound
      L X k hN hH hsigma hC hkernel tau hV⟩

/-- Exact localization of a large sharp twisted Chebyshev prefix to one frequency cell of the
complete signed Heath--Brown aggregate.  The threshold retains the full quadratic Mellin tail,
the exact number and width of the cells, and the stated kernel constant. -/
theorem exists_heathBrownDyadicAggregate_cell_large_of_vonMangoldtTwist_prefix_gt
    (L X k K cells : ℕ) (hXL : X < (L + 1) ^ k) (tau : ℝ)
    {H B sigma C V Δ : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hKH : 1 ≤ (K : ℝ) + H)
    (hsupport : (K : ℝ) + H ≤ X) (hsigma : 1 < sigma)
    (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight (K : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤ C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hlarge : B / (2 * Real.pi) + Real.log ((K : ℝ) + H) * H <
      ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist tau n‖) :
    ∃ j ∈ Finset.range cells,
      ∃ y ∈ Set.Icc (-V + (j : ℝ) * Δ) (-V + ((j : ℝ) + 1) * Δ),
        (B - heathBrownPacketDampedL1 L X k sigma * C *
            (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C) ≤
          ‖heathBrownDyadicAggregate L X k
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I)‖ := by
  let A : ℝ → ℂ := fun y =>
    heathBrownDyadicAggregate L X k
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I)
  let W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight (K : ℝ) H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * I)
  let P := heathBrownPacketDampedL1 L X k sigma
  let E := P * C * (Real.pi - 2 * Real.arctan V)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hP : 0 ≤ P := heathBrownPacketDampedL1_nonneg L X k sigma
  have hC0 : 0 ≤ C := by linarith
  have hA : Continuous A :=
    continuous_heathBrownDyadicAggregate_line_shift L X k sigma tau
  have hW : Continuous W :=
    continuous_mellin_smoothWeight_line hH (by linarith)
  have hAbound : ∀ y, ‖A y‖ ≤ P := fun y =>
    norm_heathBrownDyadicAggregate_le_packetDampedL1 L X k sigma (y + tau)
  have hint : Integrable fun y => A y * W y := by
    simpa only [A, W] using
      integrable_heathBrownDyadicAggregate_shift_mul_mellin_smoothWeight
        L X k tau hKR hH (by linarith : 0 < sigma)
  have hfull : B < ‖∫ y : ℝ, A y * W y‖ := by
    simpa only [A, W] using
      norm_integral_heathBrownDyadicAggregate_gt_of_vonMangoldtTwist_prefix_gt
        L X k K hXL tau hK hH hKH hsupport hsigma hlarge
  have hsplit : ‖∫ y : ℝ, A y * W y‖ ≤
      ‖∫ y in Set.Icc (-V) V, A y * W y‖ + E := by
    simpa only [E, P, W] using
      norm_integral_le_truncated_add_tail
        (g := A) (W := W) hV hP hC0 hAbound hkernel hint
  have hcentral : B - E < ‖∫ y in Set.Icc (-V) V, A y * W y‖ := by
    linarith
  have hend : -V + (cells : ℝ) * Δ = V := by
    linarith
  have hsetInterval :
      (∫ y in Set.Icc (-V) V, A y * W y) =
        ∫ y in (-V)..V, A y * W y := by
    rw [intervalIntegral.integral_of_le (neg_le_self hV),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hWcentral : ∀ y ∈ Set.Icc (-V) (-V + (cells : ℝ) * Δ), ‖W y‖ ≤ C := by
    intro y _hy
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hinv : (1 + y ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hden]
      nlinarith [sq_nonneg y]
    calc
      ‖W y‖ ≤ C * (1 + y ^ 2)⁻¹ := hkernel y
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hinv hC0
      _ = C := by ring
  obtain ⟨c, hc, hcellsUpper⟩ :=
    exists_cell_max_norm_intervalIntegral_mul_le hA hW hΔ cells hWcentral
  have hsumLower : B - E ≤
      ∑ j ∈ Finset.range cells, Δ * (C * ‖A (c j)‖) := by
    apply (le_of_lt hcentral).trans
    rw [hsetInterval]
    rw [hend] at hcellsUpper
    exact hcellsUpper
  let f : ℕ → ℝ := fun j => Δ * (C * ‖A (c j)‖)
  have hf : ∀ j, 0 ≤ f j := fun j => by
    dsimp only [f]
    positivity
  have hsumNonneg : 0 ≤ ∑ j ∈ Finset.range cells, f j := by positivity
  have hsumNorm : ‖∑ j ∈ Finset.range cells, f j‖ =
      ∑ j ∈ Finset.range cells, f j := by
    rw [Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
  have hrange : (Finset.range cells).Nonempty :=
    ⟨0, Finset.mem_range.mpr hcells⟩
  have hlargeSum : B - E ≤ ‖∑ j ∈ Finset.range cells, f j‖ := by
    rw [hsumNorm]
    simpa only [f] using hsumLower
  obtain ⟨j, hj, hjlarge⟩ :=
    exists_mem_card_mul_norm_ge (Finset.range cells) hrange f hlargeSum
  have hfnorm : ‖f j‖ = Δ * (C * ‖A (c j)‖) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf j)]
  have hden : 0 < (cells : ℝ) * Δ * C := by positivity
  refine ⟨j, hj, c j, hc j (Finset.mem_range.mp hj), ?_⟩
  rw [div_le_iff₀ hden]
  calc
    B - heathBrownPacketDampedL1 L X k sigma * C *
          (Real.pi - 2 * Real.arctan V) = B - E := rfl
    _ ≤ (cells : ℝ) * ‖f j‖ := by simpa using hjlarge
    _ = ‖A (c j)‖ * ((cells : ℝ) * Δ * C) := by rw [hfnorm]; ring

/-- Exact sharp-prefix-to-literal-core handoff.  One physical twisted prefix selects one literal
Heath--Brown core product at an ordinate lying in a stated frequency cell, with no truncated-box
surrogate and with every localization and combinatorial loss visible. -/
theorem exists_heathBrownDyadicCoreProduct_cell_large_of_vonMangoldtTwist_prefix_gt
    (L X k K cells : ℕ) (hk : 0 < k) (hXL : X < (L + 1) ^ k) (tau : ℝ)
    {H B sigma C V Δ : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hKH : 1 ≤ (K : ℝ) + H)
    (hsupport : (K : ℝ) + H ≤ X) (hsigma : 1 < sigma)
    (hC : 1 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight (K : ℝ) H x : ℝ) : ℂ))
        ((sigma : ℂ) + (y : ℝ) * I)‖ ≤ C * (1 + y ^ 2)⁻¹)
    (hV : 0 ≤ V) (hΔ : 0 < Δ) (hcells : 0 < cells)
    (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hlarge : B / (2 * Real.pi) + Real.log ((K : ℝ) + H) * H <
      ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist tau n‖) :
    ∃ j ∈ Finset.range cells,
      ∃ y ∈ Set.Icc (-V + (j : ℝ) * Δ) (-V + ((j : ℝ) + 1) * Δ),
        ∃ m ∈ Finset.range k,
          ∃ q ∈ Finset.range (Nat.log 2 X + 1),
            ∃ b ∈ dyadicChoiceSet (k - m - 1) X,
              ∃ a ∈ dyadicChoiceSet (k - m) L,
                (B - heathBrownPacketDampedL1 L X k sigma * C *
                    (Real.pi - 2 * Real.arctan V)) /
                    ((cells : ℝ) * Δ * C) ≤
                  (k : ℝ) * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (k - m)) *
                    (((Nat.log 2 L + 1 : ℕ) : ℝ) ^ (k - m)) * (2 ^ k : ℝ) *
                      ‖heathBrownDyadicCoreProduct L X k m a b q
                        ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I)‖ := by
  obtain ⟨j, hj, y, hy, hylarge⟩ :=
    exists_heathBrownDyadicAggregate_cell_large_of_vonMangoldtTwist_prefix_gt
      L X k K cells hXL tau hK hH hKH hsupport hsigma hC hkernel
        hV hΔ hcells hgrid hlarge
  obtain ⟨m, hm, q, hq, b, hb, a, ha, hcore⟩ :=
    exists_large_heathBrownDyadicCoreProduct L X k hk
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * I) hylarge
  exact ⟨j, hj, y, hy, m, hm, q, hq, b, hb, a, ha, hcore⟩

end RHTower.Sieve
