import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.RecurrentCenters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.ExponentialCompiler

/-! # Time density of maximizers surrounded by long near-maximum intervals -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
open SharpOccupation
noncomputable section

/-- At almost every prescribed tolerance, the orbit has a measurable
family of true maximizers with an explicit positive time density.
Every center has a full exponential neighborhood with the same gate-deficit bound. -/
theorem gaussian_prescribed_maximum_center_density :
    ∀ᵐ e : ℝ ∂volume, e ∈ Ioc (0:ℝ) (11/25) → ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∃ b : ℕ, 0 < b ∧ ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H := chainGenerator ω k
        let η := 1/(2:ℝ)^(b*N)
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∃ S : Set ℝ, MeasurableSet S ∧
            (∀ a : ℝ, Tendsto (fun T : ℝ => volume.real (S ∩ Icc a T)/(T-a))
              atTop (𝓝 ((D:ℝ)*(physicalArc η)^(D-1)))) ∧
            ∀ z ∈ S, (∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val z) → m ≤ j) ∧
              ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j,
                HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z+t)) →
                  m ≤ j+⌊(2:ℝ)^(α*(N:ℝ))⌋₊ := by
  filter_upwards [gaussian_prescribed_regular_tolerances] with e hreg he
  filter_upwards [hreg,gaussian_frozen_maximum_clearance,LocalPatches.gaussian_exponential_precision_compiler,
    gaussian_path_all_prefixes_maximally_projective] with ω hw hmax hsim hspec
  obtain ⟨c,hc⟩ := hmax e he hw
  refine ⟨c+1,Nat.succ_pos _,?_⟩
  intro γ α hγ hγα hα
  filter_upwards [hc,hsim (c+1) γ α hγ hγα hα.le] with k hk hs
  intro N D H η
  obtain ⟨m,hP,hm,hcoarse⟩ := hk
  have hη : 0 < η := by dsimp [η]; positivity
  have hle : η ≤ 1 := (div_le_one (by positivity : 0 < (2:ℝ)^((c+1)*N))).mpr
    (one_le_pow₀ (by norm_num))
  have hsmall : η < sqrt 2 := hle.trans_lt ((lt_sqrt zero_le_one).mpr (by norm_num))
  have hbud : c*N+1 ≤ (c+1)*N := by dsimp [N]; rw [Nat.add_mul,one_mul]; omega
  have hpay : 2*η ≤ 1/(2:ℝ)^(c*N) := by
    change 2*(1/(2:ℝ)^((c+1)*N)) ≤ _
    rw [show 2*(1/(2:ℝ)^((c+1)*N))=2/(2:ℝ)^((c+1)*N) by ring,
      div_le_div_iff₀ (by positivity) (by positivity),one_mul,←pow_succ' (2:ℝ) (c*N)]
    exact pow_le_pow_right₀ (by norm_num) hbud
  exact ⟨m,hP,hm,centers_of_maximum_clearance H (hspec k) hη hsmall hpay hcoarse hs⟩

#print axioms gaussian_prescribed_maximum_center_density
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
