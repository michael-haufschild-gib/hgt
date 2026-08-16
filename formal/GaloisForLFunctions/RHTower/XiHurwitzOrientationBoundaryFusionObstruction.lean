import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositiveBoundarySourceSaturation

/-!
# Mixed-incidence obstruction for fusing the two Route-Q boundaries

The two exact null-boundary witnesses sum to the signed Hurwitz orientation vector. Although each
boundary admits genuine source-nonnegative separated packet reconstructions, their mixed quadratic
interference converges to minus the complete orientation energy. Thus off-RH negativity is carried
entirely by cross-incidence between the two positive boundary channels, not by either diagonal.
-/

open Complex Metric Function Filter Topology
open scoped Topology BigOperators

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- The two antipodal exact boundary witnesses fuse back to the signed orientation vector. -/
theorem xiHurwitzOrientationBoundaryPlus_add_boundaryMinus :
    xiHurwitzOrientationBoundaryPlus + xiHurwitzOrientationBoundaryMinus =
      xiHurwitzOrientationVector := by
  unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
  module

/-- Mixed quadratic interference left after subtracting both diagonal energies. -/
def xiHurwitzOrientationBoundaryFusionDefect
    (u v : XiWeilCarrier) : ℝ :=
  xiWeilHilbertQuadratic (u + v) -
    xiWeilHilbertQuadratic u - xiWeilHilbertQuadratic v

theorem continuous_xiHurwitzOrientationBoundaryFusionDefect :
    Continuous (Function.uncurry xiHurwitzOrientationBoundaryFusionDefect) := by
  unfold xiHurwitzOrientationBoundaryFusionDefect Function.uncurry
  exact ((continuous_xiWeilHilbertQuadratic.comp
    (continuous_fst.add continuous_snd)).sub
      (continuous_xiWeilHilbertQuadratic.comp continuous_fst)).sub
    (continuous_xiWeilHilbertQuadratic.comp continuous_snd)

/-- The two null boundary diagonals hide the full negative orientation energy in their mixed
interaction. -/
theorem xiHurwitzOrientationBoundaryFusionDefect_exact :
    xiHurwitzOrientationBoundaryFusionDefect
        xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus =
      -xiHurwitzOrientationEnergy := by
  unfold xiHurwitzOrientationBoundaryFusionDefect
  rw [xiHurwitzOrientationBoundaryPlus_add_boundaryMinus,
    xiWeilHilbertQuadratic_xiHurwitzOrientationVector,
    xiHurwitzOrientationBoundaryPlus_exact.1,
    xiHurwitzOrientationBoundaryMinus_exact.1]
  ring

/-- Boundary convergence forces the mixed interference to converge to minus the complete
orientation energy. -/
theorem tendsto_xiHurwitzOrientationBoundaryFusionDefect
    {u v : ℕ → XiWeilCarrier}
    (hu : Tendsto u atTop (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hv : Tendsto v atTop (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    Tendsto (fun n => xiHurwitzOrientationBoundaryFusionDefect (u n) (v n))
      atTop (𝓝 (-xiHurwitzOrientationEnergy)) := by
  have hsum := hu.add hv
  rw [xiHurwitzOrientationBoundaryPlus_add_boundaryMinus] at hsum
  have hQsum := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hsum
  have hQu := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hu
  have hQv := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hv
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector] at hQsum
  rw [xiHurwitzOrientationBoundaryPlus_exact.1] at hQu
  rw [xiHurwitzOrientationBoundaryMinus_exact.1] at hQv
  simpa only [Function.comp_apply,
    xiHurwitzOrientationBoundaryFusionDefect, sub_zero] using
    (hQsum.sub hQu).sub hQv

/-- Hilbert energy of fusing the evaluations of two actual separated source packets. -/
def xiSeparatedBoundaryPacketFusionEnergy
    (P Q : XiSeparatedContinuedCauchyPacket) : ℝ :=
  xiWeilHilbertQuadratic (P.evaluation + Q.evaluation)

/-- Mixed part of the fused packet energy after removing the two exact source diagonals. -/
def xiSeparatedBoundaryPacketFusionDefect
    (P Q : XiSeparatedContinuedCauchyPacket) : ℝ :=
  xiSeparatedBoundaryPacketFusionEnergy P Q - P.sourceEnergy - Q.sourceEnergy

theorem xiSeparatedBoundaryPacketFusionDefect_eq_hilbert
    (P Q : XiSeparatedContinuedCauchyPacket) :
    xiSeparatedBoundaryPacketFusionDefect P Q =
      xiHurwitzOrientationBoundaryFusionDefect P.evaluation Q.evaluation := by
  rw [xiSeparatedBoundaryPacketFusionDefect,
    xiSeparatedBoundaryPacketFusionEnergy,
    P.sourceEnergy_eq_hilbertQuadratic,
    Q.sourceEnergy_eq_hilbertQuadratic]
  rfl

theorem tendsto_xiSeparatedBoundaryPacketFusionEnergy
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    Tendsto (fun n => xiSeparatedBoundaryPacketFusionEnergy (P n) (Q n))
      atTop (𝓝 (-xiHurwitzOrientationEnergy)) := by
  have hsum := hP.add hQ
  rw [xiHurwitzOrientationBoundaryPlus_add_boundaryMinus] at hsum
  have h := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hsum
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector] at h
  change Tendsto
    (xiWeilHilbertQuadratic ∘ fun n => (P n).evaluation + (Q n).evaluation)
    atTop (𝓝 (-xiHurwitzOrientationEnergy))
  exact h

theorem tendsto_xiSeparatedBoundaryPacketFusionDefect
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    Tendsto (fun n => xiSeparatedBoundaryPacketFusionDefect (P n) (Q n))
      atTop (𝓝 (-xiHurwitzOrientationEnergy)) := by
  apply (tendsto_xiHurwitzOrientationBoundaryFusionDefect hP hQ).congr'
  exact Eventually.of_forall fun n =>
    (xiSeparatedBoundaryPacketFusionDefect_eq_hilbert (P n) (Q n)).symm

/-- Off RH, every fusion of the two boundary reconstructions is eventually trapped in a strictly
negative mixed chamber. -/
theorem eventually_xiSeparatedBoundaryPacketFusionEnergy_lt_neg_half_of_not_rh
    (hnot : ¬RiemannHypothesis)
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    ∀ᶠ n in atTop,
      xiSeparatedBoundaryPacketFusionEnergy (P n) (Q n) <
        -xiHurwitzOrientationEnergy / 2 := by
  have hEne : xiHurwitzOrientationEnergy ≠ 0 := by
    intro hzero
    exact hnot (riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.2 hzero)
  have hEpos : 0 < xiHurwitzOrientationEnergy :=
    lt_of_le_of_ne xiHurwitzOrientationEnergy_nonneg (Ne.symm hEne)
  exact (tendsto_xiSeparatedBoundaryPacketFusionEnergy P Q hP hQ).eventually
    (Iio_mem_nhds (by linarith :
      -xiHurwitzOrientationEnergy < -xiHurwitzOrientationEnergy / 2))

/-- Any cofinal nonnegative fusion of the two exact source-boundary reconstructions forces RH. -/
theorem riemannHypothesis_of_cofinal_nonnegative_boundaryPacketFusion
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus))
    (hcofinal : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      0 ≤ xiSeparatedBoundaryPacketFusionEnergy (P n) (Q n)) :
    RiemannHypothesis := by
  by_contra hnot
  have hneg :=
    eventually_xiSeparatedBoundaryPacketFusionEnergy_lt_neg_half_of_not_rh
      hnot P Q hP hQ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hneg
  obtain ⟨n, hnN, hnnonneg⟩ := hcofinal N
  have hnneg := hN n hnN
  linarith [xiHurwitzOrientationEnergy_nonneg]

/-- **Unconditional Route-Q interference decomposition.** There are actual source-nonnegative
separated packets approaching both exact null boundaries, while their fused energy and their
mixed defect both converge to minus the complete orientation energy. Thus all off-RH negativity
is asymptotically carried by cross-incidence, not by either source diagonal. -/
theorem exists_nonnegativeSeparatedBoundaryPackets_with_exact_fusionDefect :
    ∃ Pplus Pminus : ℕ → XiSeparatedContinuedCauchyPacket,
      Tendsto (fun n => (Pplus n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryPlus) ∧
      Tendsto (fun n => (Pplus n).sourceEnergy) atTop (𝓝 0) ∧
      (∀ n, 0 ≤ (Pplus n).sourceEnergy) ∧
      Tendsto (fun n => (Pminus n).evaluation) atTop
        (𝓝 xiHurwitzOrientationBoundaryMinus) ∧
      Tendsto (fun n => (Pminus n).sourceEnergy) atTop (𝓝 0) ∧
      (∀ n, 0 ≤ (Pminus n).sourceEnergy) ∧
      Tendsto (fun n =>
        xiSeparatedBoundaryPacketFusionEnergy (Pplus n) (Pminus n))
        atTop (𝓝 (-xiHurwitzOrientationEnergy)) ∧
      Tendsto (fun n =>
        xiSeparatedBoundaryPacketFusionDefect (Pplus n) (Pminus n))
        atTop (𝓝 (-xiHurwitzOrientationEnergy)) := by
  obtain ⟨Pplus, Pminus, hPplus, hEplus, hplusNonneg,
      hPminus, hEminus, hminusNonneg, _hstrict⟩ :=
    exists_nonnegativeSeparatedPackets_tendsto_both_orientationBoundaries
  exact ⟨Pplus, Pminus, hPplus, hEplus, hplusNonneg,
    hPminus, hEminus, hminusNonneg,
    tendsto_xiSeparatedBoundaryPacketFusionEnergy Pplus Pminus hPplus hPminus,
    tendsto_xiSeparatedBoundaryPacketFusionDefect Pplus Pminus hPplus hPminus⟩

end

end RHTower
