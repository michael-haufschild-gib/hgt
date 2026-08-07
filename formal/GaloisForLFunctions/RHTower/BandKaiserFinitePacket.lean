import GaloisForLFunctions.RHTower.BandKaiserGeneralShiftTail

/-!
# Finite Kaiser packet spectral tails

The single-packet translated tail estimate is stable under arbitrary finite real linear
combinations.  Finite Cauchy--Schwarz gives the pointwise spectral-density bound, after which
Tonelli-free finite linearity of the Bochner integral reduces the tail to the sum of the individual
packet tails.

This is the analytic half of the fixed-depth trial-space construction: once a packet family has a
polynomially conditioned Gram matrix, every vector in its span inherits the ground-state
`exp (-2 * c)` leakage clock up to a polynomial factor.
-/

open MeasureTheory Set intervalIntegral FourierTransform
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- A finite real linear combination of cosine-modulated Kaiser packets. -/
def kaiserCosCombination {m : ℕ} (c : ℝ) (w b : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ j, b j * kaiserCosTrial c (w j) x

theorem continuous_kaiserCosCombination {m : ℕ} (c : ℝ) (w b : Fin m → ℝ) :
    Continuous (kaiserCosCombination c w b) := by
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_kaiserCosTrial c (w j))

theorem kaiserCosCombination_even {m : ℕ} (c : ℝ) (w b : Fin m → ℝ) :
    Function.Even (kaiserCosCombination c w b) := by
  intro x
  simp only [kaiserCosCombination]
  apply Finset.sum_congr rfl
  intro j _
  rw [kaiserCosTrial_even]

set_option maxHeartbeats 400000 in
/-- Cauchy--Schwarz for the cosine-transform readings of a finite packet combination. -/
theorem norm_sq_fourier_bandTrunc_kaiserCosCombination_le {m : ℕ}
    (c : ℝ) (w b : Fin m → ℝ) (ξ : ℝ) :
    ‖𝓕 (bandTrunc (kaiserCosCombination c w b)) ξ‖ ^ 2 ≤
      (∑ j, b j ^ 2) *
        ∑ j, ‖𝓕 (bandTrunc (kaiserCosTrial c (w j))) ξ‖ ^ 2 := by
  rw [norm_sq_fourier_bandTrunc_of_even
    (continuous_kaiserCosCombination c w b) (kaiserCosCombination_even c w b) ξ]
  have hinterval : ∀ j : Fin m, IntervalIntegrable
      (fun x => b j * kaiserCosTrial c (w j) x * Real.cos (2 * Real.pi * ξ * x))
      volume (-1) 1 := by
    intro j
    exact Continuous.intervalIntegrable (μ := volume)
      ((continuous_const.mul (continuous_kaiserCosTrial c (w j))).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))) (-1) 1
  change (∫ x in (-1 : ℝ)..1,
    (∑ j, b j * kaiserCosTrial c (w j) x) * Real.cos (2 * Real.pi * ξ * x)) ^ 2 ≤ _
  have hintegrand :
      (fun x : ℝ => (∑ j, b j * kaiserCosTrial c (w j) x) *
        Real.cos (2 * Real.pi * ξ * x)) =
      (fun x : ℝ => ∑ j, b j * kaiserCosTrial c (w j) x *
        Real.cos (2 * Real.pi * ξ * x)) := by
    funext x
    simpa using (Finset.sum_mul (Finset.univ : Finset (Fin m))
      (fun j => b j * kaiserCosTrial c (w j) x)
      (Real.cos (2 * Real.pi * ξ * x)))
  rw [hintegrand]
  rw [intervalIntegral.integral_finsetSum (fun j _ => hinterval j)]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b
    (fun j => ∫ x in (-1 : ℝ)..1,
      kaiserCosTrial c (w j) x * Real.cos (2 * Real.pi * ξ * x))
  have hpacketSq :
      (∑ j, (∫ x in (-1 : ℝ)..1,
        kaiserCosTrial c (w j) x * Real.cos (2 * Real.pi * ξ * x)) ^ 2) =
        ∑ j, ‖𝓕 (bandTrunc (kaiserCosTrial c (w j))) ξ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    exact (norm_sq_fourier_bandTrunc_of_even
      (continuous_kaiserCosTrial c (w j)) (kaiserCosTrial_even c (w j)) ξ).symm
  rw [hpacketSq] at hcs
  simpa only [mul_assoc] using hcs

/-- Common polynomial envelope for every allowed shifted packet. -/
def kaiserPacketTailBound (c : ℝ) : ℝ :=
  8 + 2 * (kaiserBandRadius c + kaiserAllowedShift c) *
    kaiserEdgeTransformBound ^ 2

theorem kaiserPacketTailBound_nonneg {c : ℝ} (hc : 1 ≤ c) :
    0 ≤ kaiserPacketTailBound c := by
  have hcpos : 0 < c := one_pos.trans_le hc
  have hsum : 0 ≤ kaiserBandRadius c + kaiserAllowedShift c := by
    simp only [kaiserBandRadius, kaiserAllowedShift]
    positivity
  unfold kaiserPacketTailBound
  positivity

/-- Integrated finite Cauchy--Schwarz before any individual packet envelope is inserted. -/
theorem integral_compl_band_norm_sq_fourier_kaiserCosCombination_le_sum {m : ℕ}
    (c : ℝ) (w b : Fin m → ℝ) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserCosCombination c w b)) ξ‖ ^ 2) ≤
      (∑ j, b j ^ 2) *
        ∑ j, ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          ‖𝓕 (bandTrunc (kaiserCosTrial c (w j))) ξ‖ ^ 2 := by
  let coeff : ℝ := ∑ j, b j ^ 2
  let packetDensity : Fin m → ℝ → ℝ := fun j ξ =>
    ‖𝓕 (bandTrunc (kaiserCosTrial c (w j))) ξ‖ ^ 2
  let combinationDensity : ℝ → ℝ := fun ξ =>
    ‖𝓕 (bandTrunc (kaiserCosCombination c w b)) ξ‖ ^ 2
  have hcombination : Integrable combinationDensity :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserCosCombination c w b)
  have hpacket : ∀ j, Integrable (packetDensity j) := fun j =>
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserCosTrial c (w j))
  have hsum : Integrable (fun ξ => ∑ j, packetDensity j ξ) :=
    integrable_finsetSum _ fun j _ => hpacket j
  have hpoint : ∀ᵐ ξ : ℝ ∂(volume.restrict
      (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ),
      combinationDensity ξ ≤ coeff * ∑ j, packetDensity j ξ :=
    Filter.Eventually.of_forall fun ξ =>
      norm_sq_fourier_bandTrunc_kaiserCosCombination_le c w b ξ
  have hmono :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          combinationDensity ξ) ≤
        ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          coeff * ∑ j, packetDensity j ξ :=
    integral_mono_ae hcombination.integrableOn
      (hsum.const_mul coeff).integrableOn hpoint
  have hrearrange :
      (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          coeff * ∑ j, packetDensity j ξ) =
        coeff * ∑ j, ∫ ξ in
          (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          packetDensity j ξ := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact MeasureTheory.integral_finsetSum Finset.univ
      (fun j _ => (hpacket j).integrableOn)
  rw [hrearrange] at hmono
  simpa only [coeff, packetDensity, combinationDensity] using hmono

/-- Every finite combination of allowed packets has tail bounded by coefficient energy times
packet count times the common single-packet envelope. -/
theorem integral_compl_band_norm_sq_fourier_kaiserCosCombination_le {m : ℕ}
    {c : ℝ} (hc : 1 ≤ c) (w b : Fin m → ℝ)
    (hw : ∀ j, |w j| ≤ kaiserAllowedShift c) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserCosCombination c w b)) ξ‖ ^ 2) ≤
      (∑ j, b j ^ 2) * (m : ℝ) * kaiserPacketTailBound c := by
  have hmono := integral_compl_band_norm_sq_fourier_kaiserCosCombination_le_sum c w b
  refine hmono.trans ?_
  have hcoeff : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (b j)
  have hsumBound :
      (∑ j, ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserCosTrial c (w j))) ξ‖ ^ 2) ≤
          (m : ℝ) * kaiserPacketTailBound c := by
    calc
      (∑ j, ∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
          ‖𝓕 (bandTrunc (kaiserCosTrial c (w j))) ξ‖ ^ 2)
          ≤ ∑ _j : Fin m, kaiserPacketTailBound c := by
            apply Finset.sum_le_sum
            intro j _
            exact integral_compl_band_norm_sq_fourier_kaiserCosTrial_le hc (hw j)
      _ = (m : ℝ) * kaiserPacketTailBound c := by
        simp [Fintype.card_fin]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsumBound hcoeff

/-- General-shift finite-span tail bound, retaining each packet's exact depth envelope. -/
theorem integral_compl_band_norm_sq_fourier_kaiserCosCombination_general_shift_le {m : ℕ}
    {c : ℝ} (hc : 0 < c) (w b : Fin m → ℝ)
    (hw : ∀ j, |2 * Real.pi * w j| ≤ c) :
    (∫ ξ in (Icc (-(kaiserBandRadius c)) (kaiserBandRadius c))ᶜ,
        ‖𝓕 (bandTrunc (kaiserCosCombination c w b)) ξ‖ ^ 2) ≤
      (∑ j, b j ^ 2) *
        ∑ j, (8 + 2 * (kaiserBandRadius c + |w j|) *
          kaiserEdgeTransformBoundAt (2 * c * |2 * Real.pi * w j|) ^ 2) := by
  have hmono := integral_compl_band_norm_sq_fourier_kaiserCosCombination_le_sum c w b
  refine hmono.trans ?_
  have hcoeff : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (b j)
  apply mul_le_mul_of_nonneg_left _ hcoeff
  apply Finset.sum_le_sum
  intro j _
  exact integral_compl_band_norm_sq_fourier_kaiserCosTrial_general_shift_le hc (hw j)

end GaloisForLFunctions.RHTower

end
