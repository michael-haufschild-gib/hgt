import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.CriticalHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.ToleranceCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles

/-! # Exponential clearance of the actual maximum at regular tolerances -/
open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
open DiagonalSynthesis (Register)
noncomputable section

/-- The same frozen chain on successive open prefixes of length at least three. -/
def chainGenerator (ω : PathPauliDisorder) (k : ℕ) : selfAdjoint (Register (k+3)) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩

/-- Tolerances approximated at every exponential rate by critical values of the frozen prefixes. -/
def chainExceptional (ω : PathPauliDisorder) : Set ℝ :=
  exceptionalTolerances (fun k j => criticalHeight (chainGenerator ω k) j)

/-- Off the exceptional set, some exponential increase in tolerance leaves
the actual maximum exactly unchanged on every sufficiently long prefix. -/
theorem gaussian_frozen_maximum_clearance :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ e ∈ Ioc (0:ℝ) (11/25), e ∉ chainExceptional ω → ∃ c : ℕ, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          IsRecurrentOrbitCircuitMaximumAt H (e+1/(2:ℝ)^(c*N)) m := by
  filter_upwards [gaussian_pauli_prefix_maximum_and_occupation_quantiles] with ω hmax
  intro e he hreg
  obtain ⟨c,hc⟩ := not_forall.mp hreg
  refine ⟨c,?_⟩
  filter_upwards [not_frequently.mp hc,hmax] with k hfar hm
  intro N H
  let δ := 1/(2:ℝ)^(c*N)
  let u := pathPauliDisorderShell ω (k+1)
  obtain ⟨m,hmP,hm,_⟩ := hm e he
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hN : 2 ≤ N := by dsimp [N]; omega
  obtain ⟨j,hj⟩ := twoLocal_exists_recurrent_maximum_at hN H
    (hasPauliWeightAtMost_pathHamiltonian u (isSelfAdjoint_pathHamiltonian u)) (e+δ) (add_pos he.1 hδ)
  have hmj : m ≤ j := by
    by_contra! hlt
    obtain ⟨hcap,hu,hv⟩ := criticalHeight_of_maximum_drop hN H he.1.le hm hj hlt
    apply hfar ⟨j,hcap,?_⟩
    change |e-criticalHeight H j| ≤ 1/(2:ℝ)^(c*k)
    rw [abs_of_nonpos (sub_nonpos.mpr hu.le)]
    have hbit : (2:ℝ)^(c*k) ≤ (2:ℝ)^(c*N) := pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left c (by dsimp [N]; omega))
    exact (show -(e-criticalHeight H j) ≤ δ by linarith only [hv]).trans
      (one_div_le_one_div_of_le (by positivity) hbit)
  obtain ⟨t,ht⟩ := required_at_some_date hj
  obtain ⟨z,hz,C,hC,hh⟩ := hm.1 t
  have hjm := ht m ⟨z,hz,C,hC,hh.trans (le_add_of_nonneg_right hδ.le)⟩
  exact ⟨m,hmP,hm,(le_antisymm hjm hmj) ▸ hj⟩

#print axioms gaussian_frozen_maximum_clearance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
