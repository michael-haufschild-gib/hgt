import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedSpatialMellinL2
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSpatialL2

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-!
# Weighted fixed-ambient bad-base measure

This module turns the actual-coefficient weighted spatial `L²` law into a restricted-volume
superlevel estimate.  In particular, pole cancellation on the first `K` cells pays `K³` rather
than the uniform-envelope bound.  This is the low-cell input required by the natural-cutoff
Route-T gap-shell assembly.
-/

/-- Convert any fixed-ambient packet `L²` estimate into the corresponding restricted-volume
superlevel estimate.  The positive extension removes the artificial singularity at dilation zero;
on the physical block it is exactly the original packet. -/
theorem volume_maynardFixedAmbientPhysicalDefectPacket_large_le_of_integral_sq_le
    {x N R H D C : ℝ} {S : Finset ℕ} (hx : 1 ≤ x)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hD : 0 < D)
    (a : ℝ → ℂ) (ha : Continuous a)
    (hmean :
      (∫ lambda : ℝ in x..(2 * x),
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖ ^ 2) ≤ C) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} ≤
      C / D ^ 2 := by
  let b : ℕ → ℝ → ℂ :=
    maynardFixedAmbientDefectCellCoefficient a N R H 1
  let Q : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b 0
  let E : ℝ → ℂ := fun lambda =>
    maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1
  have hb : ∀ m ∈ S, Continuous (b m) := by
    intro m hm
    exact continuous_maynardFixedAmbientDefectCellCoefficient
      ha hN hR hH (by norm_num) m
  have hQ : Continuous Q :=
    continuous_maynardUnitCellMellinPacketPosExtension S b 0 hb
  have hQE : ∀ lambda ∈ Set.Icc x (2 * x), Q lambda = E lambda := by
    intro lambda hlambda
    have hlambdaOne : 1 ≤ lambda := hx.trans hlambda.1
    have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambdaOne
    dsimp only [Q, E, b]
    rw [maynardUnitCellMellinPacketPosExtension_eq hlambdaOne]
    simpa using (maynardFixedAmbientPhysicalDefectPacket_eq_mellinPacket
      S a lambda N R H 1 hlambdaPos hR hH).symm
  have hmeanQ :
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) ≤ C := by
    calc
      (∫ lambda : ℝ in x..(2 * x), ‖Q lambda‖ ^ 2) =
          ∫ lambda : ℝ in x..(2 * x), ‖E lambda‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro lambda hlambda
        rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hlambda
        change ‖Q lambda‖ ^ 2 = ‖E lambda‖ ^ 2
        rw [hQE lambda hlambda]
      _ ≤ C := hmean
  have hcheb := maynard_restrictVolume_norm_ge_le_of_intervalIntegral_sq_le
    Q hQ (by linarith : x ≤ 2 * x) hD hmeanQ
  let μ : Measure ℝ := volume.restrict (Set.Icc x (2 * x))
  have hae : {lambda | D ≤ ‖E lambda‖} =ᵐ[μ]
      {lambda | D ≤ ‖Q lambda‖} := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lambda hlambda
    apply propext
    change (D ≤ ‖E lambda‖) ↔ (D ≤ ‖Q lambda‖)
    rw [← hQE lambda hlambda]
  have hmeasure : μ.real {lambda | D ≤ ‖E lambda‖} =
      μ.real {lambda | D ≤ ‖Q lambda‖} := by
    rw [measureReal_def, measureReal_def, measure_congr hae]
  calc
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖} =
        μ.real {lambda | D ≤ ‖E lambda‖} := by rfl
    _ = μ.real {lambda | D ≤ ‖Q lambda‖} := hmeasure
    _ ≤ C / D ^ 2 := by simpa only [μ] using hcheb

/-- Low-cell bad-base bound with the exact pole-cancelled cube.  Compared with the old uniform
cell estimate, the kernel factor `R/N` is retained before summing actual squared cell envelopes. -/
theorem volume_fixedSource_lowRange_large_le_cube
    (L X k K : ℕ) (hX : 1 ≤ X) (T0 t M x N H R D : ℝ)
    (hM : 0 < M) (hx : 1 ≤ x) (hN : 0 < N)
    (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R) (hD : 0 < D)
    (hsmall : (K : ℝ) * (2 * R / N) ≤ 1) :
    (volume.restrict (Set.Icc x (2 * x))).real
        {lambda | D ≤
          ‖maynardFixedAmbientPhysicalDefectPacket (Finset.range K)
            (fun y : ℝ =>
              heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I))
            lambda N R H 1‖} ≤
      (4 * (2 * x) * (1 + 2 * (1 + Real.log K)) *
        (8 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 * (R / N)) ^ 2 *
          (K : ℝ) ^ 3) / D ^ 2 := by
  let source : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have hsource : Continuous source :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line L X k T0 t M 1
  apply volume_maynardFixedAmbientPhysicalDefectPacket_large_le_of_integral_sq_le
    hx hN hR hH hD source hsource
  simpa only [source] using
    integral_norm_sq_fixedSource_lowRange_le_cube
      L X k K hX T0 t M x N H R hM hx hN hH hR hHR hsmall

end

end RHTower.Sieve
