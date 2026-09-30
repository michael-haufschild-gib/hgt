import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelForcedCriticalWallResidue
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelHilbert

/-!
# The natural Wold square-energy half endpoint fails

The unconditional critical-wall residue excludes square summability of the actual natural
Wold residual.  Generic Abel Hilbert estimates supply the zero-residue contradiction.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower
open WoldNaturalAbelHilbert

/-- The natural Wold residual fails square summability at the exact half-density exponent. -/
theorem not_woldNatResidualSquareEnergy_half : ¬ WoldNatResidualSquareEnergy (1/2) := by
  intro hEnergy
  have hr0 : Summable (fun N : ℕ => (xiHeatCassiniWoldNatResidualLogDiscrepancy N)^2) := by
    simpa [WoldNatResidualSquareEnergy, sq_abs] using hEnergy
  let r : ℕ → ℝ := fun n => xiHeatCassiniWoldNatResidualLogDiscrepancy (n+1)
  have hr : Summable (fun n => (r n)^2) := (summable_nat_add_iff 1).mpr hr0
  let C : ℂ := (xiHeatCassiniWoldLogHolonomyConstant : ℂ)
  let F : ℂ → ℂ := fun s => current r s + C
  have hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1) := by
    apply DifferentiableOn.analyticOnNhd _ (isOpen_xiHeatCassiniWoldResidualODESector 1)
    intro s hs
    exact ((current_differentiableAt hr (by simpa only [neg_div] using hs.1)).add_const C).differentiableWithinAt
  have hsafe : Set.EqOn F (fun s => abelDirichlet woldNatDifferenceCoeff s)
      {s | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re} := by
    intro s hs
    have hD := summable_naturalCpowKernel_sub_succ hs.2
    have hA := atom_summable hr (show -1/2 < s.re by linarith [hs.2])
    have hCD := hD.mul_left C
    have heq : (fun n : ℕ => coeffPartial woldNatDifferenceCoeff (n+1) *
        (((((n:ℝ)+1:ℝ):ℂ)^(-s))-((((n:ℝ)+2:ℝ):ℂ)^(-s)))) =
        fun n => atom r s n + C * naturalCpowIncrement s n := by
      funext n
      rw [coeffPartial_woldNatDifferenceCoeff]
      dsimp [r, C, atom, naturalCpowIncrement, naturalCpowKernel]
      push_cast
      simp only [show ((n : ℂ)+1)+1=(n:ℂ)+2 by ring]
      ring
    change current r s + C = ∑' n : ℕ, _
    rw [heq, hA.tsum_add hCD, tsum_mul_left, tsum_naturalCpowKernel_sub_succ hs.2]
    simp [current]
  obtain ⟨s0, m, hs0, him, hm, hpole⟩ := exists_woldNatAbelContinuation_forced_criticalWall_residue
  have hzero : Tendsto (fun x : ℝ => (x:ℂ)*F (s0+(x:ℂ))) (𝓝[>]0) (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ => (x:ℂ)*C) (𝓝[>]0) (𝓝 0) := by
      simpa using ((Complex.continuous_ofReal.tendsto 0).mul_const C).mono_left nhdsWithin_le_nhds
    simpa [F, mul_add] using (current_radial_zero hr (by simpa only [neg_div] using hs0)).add hc
  have hcontr := tendsto_nhds_unique hzero (hpole F hF hsafe)
  have hmzero : m = 0 := by simpa using hcontr.symm
  omega

end RHTower
