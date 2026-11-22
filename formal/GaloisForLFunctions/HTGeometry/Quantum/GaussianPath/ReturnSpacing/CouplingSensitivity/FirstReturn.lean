import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.CouplingSensitivity.PhysicalBalls
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Sharp disorder stability scale at the chain’s first deep scalar return -/
open MeasureTheory Filter Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.CouplingSensitivity
noncomputable section

/-- At the first physical s-gate return after the chain's own crossing,
a perturbation of order 1/(v√N) reaches a whole ball where s plus the
new gate cost is extensive. The constants are uniform in N and s. -/
theorem gaussian_physical_first_return_hard_ball :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Matrix (Fin N→Bool) (Fin N→Bool) ℂ) :=
        ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧ ∀ s : ℕ,
          let v := firstCircuitVisit H s σ
          ∃ z : PathShell (k+1), v*sqrt N*‖z-u‖ ≤ C ∧
            ∀ y : PathShell (k+1), v*sqrt N*‖y-z‖ ≤ 1/100 →
              ∀ r : ℕ, affordable y v (1/10) r → c*(N:ℝ) ≤ s+r := by
  obtain ⟨c,C,hc,hC,hballs⟩ := gaussian_hard_ball_at_visits
  obtain ⟨_,hf⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hballs,hf] with ω hb hσ
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hb,hσ] with k hball hfirst
  intro N u H P
  obtain ⟨σ,hpos,he,hprior,_,_⟩ := hfirst
  have hσ0 : 0 < σ := (by positivity : (0:ℝ)<2^(N-10*N.sqrt)).trans hpos
  refine ⟨σ,hσ0,he,hprior,?_⟩
  intro s v
  have hv := PrecisionReturns.firstVisit_isLeast H σ s (by norm_num : (0:ℝ)<1/10)
  exact hball v (hσ0.trans_le hv.1.1) s hv.1.2

/-- At the first 1/20 scalar return after the initial 9/80 crossing,
one ball of couplings admits the scalar at physical error 1/10 and a
nearby ball requires cN gates. Both have radius 1/(100v√N). -/
theorem gaussian_first_return_stability_scale :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Matrix (Fin N→Bool) (Fin N→Bool) ℂ) :=
        ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ v : ℝ, 0 < σ ∧ orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        IsLeast (PrecisionReturns.visitSet H σ 0 (1/20)) v ∧
        (∀ y : PathShell (k+1), v*sqrt N*‖y-u‖ ≤ 1/100 → affordable y v (1/10) 0) ∧
        ∃ z : PathShell (k+1), v*sqrt N*‖z-u‖ ≤ C ∧
          ∀ y : PathShell (k+1), v*sqrt N*‖y-z‖ ≤ 1/100 →
            ∀ r : ℕ, affordable y v (1/10) r → c*(N:ℝ) ≤ r := by
  obtain ⟨c,C,hc,hC,hballs⟩ := gaussian_hard_ball_at_visits
  obtain ⟨_,hf⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hballs,hf] with ω hb hσ
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hb,hσ] with k hball hfirst
  intro N u H P
  obtain ⟨σ,hpos,he,hprior,_,_⟩ := hfirst
  have hσ0 : 0 < σ := (by positivity : (0:ℝ)<2^(N-10*N.sqrt)).trans hpos
  let v := PrecisionReturns.firstVisit H σ 0 (1/20)
  have hv := PrecisionReturns.firstVisit_isLeast H σ 0 (by norm_num : (0:ℝ)<1/20)
  have hp : 0 < v := hσ0.trans_le hv.1.1
  have hh : affordable u v (1/20) 0 := hv.1.2
  have hphys : affordable u v (1/10) 0 := by
    obtain ⟨z,hz,Y,hY,herr⟩ := hh
    exact ⟨z,hz,Y,hY,herr.trans (by norm_num)⟩
  obtain ⟨z,hz,hy⟩ := hball v hp 0 hphys
  refine ⟨σ,v,hσ0,he,hprior,hv,fun y hd => ?_,z,hz,fun y hd r hr => ?_⟩
  · simpa only [show (1/20+1/20:ℝ)=1/10 by norm_num] using affordable_ball hp hh hd
  · simpa only [Nat.cast_zero,zero_add] using hy y hd r hr

#print axioms gaussian_first_return_stability_scale
#print axioms gaussian_physical_first_return_hard_ball
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.CouplingSensitivity
