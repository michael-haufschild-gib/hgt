import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.DeficitProfile.GateDeficit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.FourthPower.PhysicalBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # Joint deficit and quartic bounds at the first below-sweep crossing -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
open private least_crossing increment_fit from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess
noncomputable section
private abbrev frozen (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- After any tenth-error visit, every budget between the incoming
budget and its complement in one sweep has a first robust crossing.
The deficit and quartic cost contribute together at that very date. -/
theorem gaussian_subsweep_first_passages :
    ∃ b>(0:ℝ), ∃ A>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      let H := frozen ω n
      ∀ (v : ℝ) (r k : ℕ), r≤k → r+k≤n+1 →
        HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H.val v) →
        ∀ ρ∈Icc (9/80:ℝ) (1/8), ∃ τ∈Ioc (0:ℝ) 1,
          IsLeast {t : ℝ | 0≤t ∧ ρ≤orbitCircuitDistance H k (v+t)} τ ∧
          orbitCircuitDistance H k (v+τ)=ρ ∧
          (N-((r+k:ℕ):ℝ)+b*N*τ^4)^10*τ^9≤A*N := by
  obtain ⟨b,hb,A,hA,hw⟩ := gaussian_quartic_gate_deficit
  obtain ⟨c,hc,hu⟩ := gaussian_polynomial_fourth_power_band
  refine ⟨b,hb,A,hA,?_⟩
  filter_upwards [hw,hu] with ω hw hu
  filter_upwards [hw,hu] with n hw hu
  intro N H v r k hr hk hv ρ hρ
  let f (t : ℝ) := orbitCircuitDistance H k (v+t)
  have pay (t : ℝ) (he : f t≤ρ) :
      HasProjectiveCircuitApproximation (n+2) (1/4) (r+k) (unitaryEvolution H.val t) := by
    have h := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val (v+t)) k ρ).mpr he
    obtain ⟨z,hz,C,hC,hfit⟩ := increment_fit H hv h
    exact ⟨z,hz,C,hC,hfit.trans (by linarith only [hρ.2])⟩
  have hN : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hnum : ((r+k:ℕ):ℝ)≤N := Nat.cast_le.mpr hk
  have hlate : ρ<f 1 := by
    apply lt_of_not_ge
    intro h
    have hcost := hu.2.2.2.2 1 ⟨hu.2.1,le_rfl⟩ (r+k) (pay 1 h)
    change (1+c*1^4)*N<((r+k:ℕ):ℝ) at hcost
    linarith only [hcost,hnum,mul_pos hc hN]
  obtain ⟨z,hz,C,hC,hfit⟩ := hv
  have hstart : f 0<ρ := by
    have he := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val v) k (1/10)).mp
      ⟨z,hz,C,hC.trans hr,hfit⟩
    change orbitCircuitDistance H k (v+0)<ρ
    rw [add_zero]
    change orbitCircuitDistance H k v≤1/10 at he
    exact he.trans_lt (lt_of_lt_of_le (by norm_num : (1/10:ℝ)<9/80) hρ.1)
  have hcont : Continuous f := (orbitCircuitDistance_lipschitz H k).continuous.comp (continuous_const.add continuous_id)
  obtain ⟨hm,he⟩ := least_crossing hcont hstart (v:=1) zero_le_one hlate.le
  let τ := sInf {t : ℝ | 0≤t ∧ ρ≤f t}
  change IsLeast {t : ℝ | 0≤t ∧ ρ≤f t} τ at hm
  change f τ=ρ at he
  have ht : 0<τ := lt_of_le_of_ne hm.1.1 (fun h => hstart.ne ((congrArg f h).trans he))
  have ht₁ := hm.2 ⟨zero_le_one,hlate.le⟩
  have hcost := hw τ ⟨ht.le,ht₁⟩ (r+k) (pay τ he.le)
  change (max 0 ((1+b*τ^4)*N-((r+k:ℕ):ℝ)))^10*τ^9≤A*N at hcost
  have hp : 0≤(1+b*τ^4)*N-((r+k:ℕ):ℝ) := by
    linarith only [hnum,mul_nonneg (mul_nonneg hb.le (pow_nonneg ht.le 4)) hN.le]
  rw [max_eq_right hp] at hcost
  refine ⟨τ,⟨ht,ht₁⟩,hm,he,?_⟩
  rwa [show N-((r+k:ℕ):ℝ)+b*N*τ^4=(1+b*τ^4)*N-((r+k:ℕ):ℝ) by ring]

/-- The signed deficit estimate holds throughout the final approach
to the original first low return and its rebound. Subtracting the
incoming r-gate circuit pays for the shift of origin. -/
theorem gaussian_first_dip_gate_deficit :
    ∃ b>(0:ℝ), ∃ A>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ r : ℕ, let v := firstLowAfterCrossing ω n r
        ∀ h : ℝ, |h|≤1 → ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (3/20) k
          (unitaryEvolution (frozen ω n).val (v+h)) →
          (max 0 ((1+b* |h|^4)*N-((r+k:ℕ):ℝ)))^10* |h|^9≤A*N := by
  obtain ⟨b,hb,A,hA,hw⟩ := gaussian_quartic_gate_deficit
  refine ⟨b,hb,A,hA,?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro N r v h hh k hk
  let H := frozen ω n
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ r (by norm_num : (0:ℝ)<1/10)).1.2
  have he := increment_fit H hv hk
  rw [show (1/10:ℝ)+3/20=1/4 by norm_num] at he
  apply hn |h| ⟨abs_nonneg h,hh⟩ (r+k)
  rcases le_total 0 h with hp|hp
  · rwa [abs_of_nonneg hp]
  · rw [abs_of_nonpos hp]
    exact he.neg_time H

#print axioms gaussian_first_dip_gate_deficit
#print axioms gaussian_subsweep_first_passages
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
