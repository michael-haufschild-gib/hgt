import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositiveBoundarySourceSaturation
import GaloisForLFunctions.RHTower.XiHurwitzOrientationBoundaryTransverseCompensation

/-!
# Route Q mixed source incidence at the null boundary

The two positive-side separated source reconstructions have diagonal energies tending to zero.
Their missing polarized incidence does not tend to zero off RH: it converges to exactly one half
of the negative orientation energy.  Consequently no Cauchy--Schwarz estimate using the two
diagonal source energies can control the fusion.  The mixed term eventually dominates every
fixed multiple of their geometric mean.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Real polarized incidence of the Xi--Weil fundamental symmetry. -/
def xiWeilMixedIncidence (x y : XiWeilCarrier) : ℝ :=
  (inner ℂ (xiWeilLineConjLinearIsometry x) y).re

/-- Mixed incidence is symmetric even though its displayed Hilbert product is oriented. -/
theorem xiWeilMixedIncidence_comm (x y : XiWeilCarrier) :
    xiWeilMixedIncidence x y = xiWeilMixedIncidence y x := by
  unfold xiWeilMixedIncidence
  rw [CliffordWeil.inner_map_left_eq_inner_map_right
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive]
  exact inner_re_symm (𝕜 := ℂ) _ _

/-- Polarization of the exact finite source energies.  This identity isolates the datum discarded
when the two boundary packets are inspected only through their diagonal energies. -/
theorem xiWeilHilbertQuadratic_packetFusion_eq_sourceEnergy_add_mixed
    (P Q : XiSeparatedContinuedCauchyPacket) :
    xiWeilHilbertQuadratic (P.evaluation + Q.evaluation) =
      P.sourceEnergy + Q.sourceEnergy +
        2 * xiWeilMixedIncidence P.evaluation Q.evaluation := by
  rw [xiWeilHilbertQuadratic_add_cross,
    ← P.sourceEnergy_eq_hilbertQuadratic,
    ← Q.sourceEnergy_eq_hilbertQuadratic]
  rfl

/-- The two exact null-boundary axes have nonzero mixed incidence `-E/2`. -/
theorem xiWeilMixedIncidence_orientationBoundaries :
    xiWeilMixedIncidence xiHurwitzOrientationBoundaryPlus
        xiHurwitzOrientationBoundaryMinus =
      -xiHurwitzOrientationEnergy / 2 := by
  have h := xiWeilHilbertQuadratic_add_cross
    xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
  rw [xiHurwitzOrientationBoundaryPlus_exact.1,
    xiHurwitzOrientationBoundaryMinus_exact.1,
    xiHurwitzOrientationBoundaryPlus_add_boundaryMinus,
    xiWeilHilbertQuadratic_xiHurwitzOrientationVector] at h
  change -xiHurwitzOrientationEnergy =
    0 + 0 + 2 * xiWeilMixedIncidence
      xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus at h
  linarith

/-- Every pair of separated packet reconstructions of the two boundary axes has the same mixed
incidence limit, independent of packet choices and of their diagonal source signs. -/
theorem tendsto_xiWeilMixedIncidence_boundaryPackets
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    Tendsto (fun n => xiWeilMixedIncidence
        (P n).evaluation (Q n).evaluation) atTop
      (𝓝 (-xiHurwitzOrientationEnergy / 2)) := by
  have hJ : Tendsto
      (fun n => xiWeilLineConjLinearIsometry (P n).evaluation) atTop
      (𝓝 (xiWeilLineConjLinearIsometry
        xiHurwitzOrientationBoundaryPlus)) :=
    xiWeilLineConjLinearIsometry.continuous.continuousAt.tendsto.comp hP
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ) hJ hQ
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hinner
  rw [← xiWeilMixedIncidence_orientationBoundaries]
  exact hre

/-- Off RH, the fixed negative mixed incidence eventually dominates every prescribed multiple of
the geometric mean of the two positive diagonal source energies. -/
theorem eventually_mixedIncidence_neg_dominates_sourceGeometricMean_of_not_rh
    (hnot : ¬RiemannHypothesis)
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus))
    (hPE : Tendsto (fun n => (P n).sourceEnergy) atTop (𝓝 0))
    (hQE : Tendsto (fun n => (Q n).sourceEnergy) atTop (𝓝 0))
    (C : ℝ) (_hC : 0 < C) :
    ∀ᶠ n in atTop,
      C * Real.sqrt ((P n).sourceEnergy * (Q n).sourceEnergy) <
        -xiWeilMixedIncidence (P n).evaluation (Q n).evaluation := by
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  have hgeom : Tendsto (fun n =>
      Real.sqrt ((P n).sourceEnergy * (Q n).sourceEnergy)) atTop (𝓝 0) := by
    have hprod := hPE.mul hQE
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hprod
    change Tendsto (fun n =>
      Real.sqrt ((P n).sourceEnergy * (Q n).sourceEnergy)) atTop
        (𝓝 (Real.sqrt (0 * 0))) at hsqrt
    simpa using hsqrt
  have hleft : Tendsto (fun n =>
      C * Real.sqrt ((P n).sourceEnergy * (Q n).sourceEnergy)) atTop (𝓝 0) :=
    by
      have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
        tendsto_const_nhds
      simpa using hconst.mul hgeom
  have hmix := tendsto_xiWeilMixedIncidence_boundaryPackets P Q hP hQ
  have hright : Tendsto (fun n =>
      -xiWeilMixedIncidence (P n).evaluation (Q n).evaluation) atTop
      (𝓝 (xiHurwitzOrientationEnergy / 2)) := by
    have hneg := (continuous_id.neg).continuousAt.tendsto.comp hmix
    change Tendsto (fun n =>
      -xiWeilMixedIncidence (P n).evaluation (Q n).evaluation) atTop
        (𝓝 (-(-xiHurwitzOrientationEnergy / 2))) at hneg
    convert hneg using 1
    ring
  filter_upwards [
    hleft.eventually_lt_const (by nlinarith : (0 : ℝ) < xiHurwitzOrientationEnergy / 4),
    hright.eventually_const_lt (by nlinarith :
      xiHurwitzOrientationEnergy / 4 < xiHurwitzOrientationEnergy / 2)
  ] with n hnleft hnright
  exact hnleft.trans hnright

/-- Unconditional Route-Q alternative.  Either RH already holds, or actual finite separated
prime--Gamma packets exhibit a catastrophic failure of every diagonal-energy Cauchy--Schwarz
budget at the two canonical null boundaries. -/
theorem riemannHypothesis_or_exists_positiveBoundaryPackets_mixedIncidenceDominates :
    RiemannHypothesis ∨
      ∃ P Q : ℕ → XiSeparatedContinuedCauchyPacket,
        Tendsto (fun n => (P n).evaluation) atTop
            (𝓝 xiHurwitzOrientationBoundaryPlus) ∧
        Tendsto (fun n => (Q n).evaluation) atTop
            (𝓝 xiHurwitzOrientationBoundaryMinus) ∧
        Tendsto (fun n => (P n).sourceEnergy) atTop (𝓝 0) ∧
        Tendsto (fun n => (Q n).sourceEnergy) atTop (𝓝 0) ∧
        (∀ n, 0 < (P n).sourceEnergy) ∧
        (∀ n, 0 < (Q n).sourceEnergy) ∧
        Tendsto (fun n => xiWeilMixedIncidence
            (P n).evaluation (Q n).evaluation) atTop
          (𝓝 (-xiHurwitzOrientationEnergy / 2)) ∧
        ∀ C : ℝ, 0 < C → ∀ᶠ n in atTop,
          C * Real.sqrt ((P n).sourceEnergy * (Q n).sourceEnergy) <
            -xiWeilMixedIncidence (P n).evaluation (Q n).evaluation := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    have hE : 0 < xiHurwitzOrientationEnergy :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hRH
    obtain ⟨P, Q, hP, hPE, hPpos, hQ, hQE, hQpos⟩ :=
      exists_positiveSeparatedPackets_tendsto_both_orientationBoundaries_of_energy_pos hE
    refine ⟨P, Q, hP, hQ, hPE, hQE, hPpos, hQpos,
      tendsto_xiWeilMixedIncidence_boundaryPackets P Q hP hQ, ?_⟩
    intro C hC
    exact eventually_mixedIncidence_neg_dominates_sourceGeometricMean_of_not_rh
      hRH P Q hP hQ hPE hQE C hC

end

end RHTower
