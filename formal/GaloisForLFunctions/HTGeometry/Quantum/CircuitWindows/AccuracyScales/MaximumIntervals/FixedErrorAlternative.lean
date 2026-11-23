import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FrozenClearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.QuadraticBits

/-! # Long hard intervals or a sharp loss of gates at prescribed accuracy -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
noncomputable section

/-- At every prescribed tolerance, failure of the long near-maximum
interval forces a loss of more than L gates in the actual maximum
when the error increases by 2^(-(N/b)^2). The coarser budget then
covers every physical date, including every fine-error maximizer. -/
theorem gaussian_fixed_error_maximum_alternative (γ α : ℝ) (hγ : 0 ≤ γ)
    (hγα : γ < α) (hα : α < 1) :
    ∃ b > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H := chainGenerator ω k
      let L := ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
      let δ := 1/(2:ℝ)^((N/b)^2)
      ∀ e ∈ Ioc (0:ℝ) (11/25), ∃ m > nearHilbertContinuousCircuitBudget N,
        IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ((∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ u ∈ Icc a (a+G), ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) →
            ∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (u+t)) → m ≤ j+2*L) ∨
          ∃ j, j+L < m ∧ IsRecurrentOrbitCircuitMaximumAt H (e+δ) j ∧ criticalHeight H j ∈ Ioc e (e+δ)) := by
  obtain ⟨b,hb,hcompile⟩ := LocalPatches.gaussian_quadratic_precision_compiler γ α hγ hγα hα.le
  refine ⟨b,hb,?_⟩
  filter_upwards [hcompile,gaussian_pauli_prefix_maximum_and_occupation_quantiles] with ω hs hm
  filter_upwards [hs,hm] with k hsim hmax
  intro N H L δ e he
  obtain ⟨m,hP,hfine,_⟩ := hmax e he
  refine ⟨m,hP,hfine,?_⟩
  have hN : 2 ≤ N := by dsimp only [N]; omega
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let x := pathPauliDisorderShell ω (k+1)
  obtain ⟨j,hcoarse⟩ := twoLocal_exists_recurrent_maximum_at hN H
    (hasPauliWeightAtMost_pathHamiltonian x (isSelfAdjoint_pathHamiltonian x)) (e+δ) (add_pos he.1 hδ)
  by_cases h : m ≤ j+L
  · left
    obtain ⟨G,hG,hr⟩ := recurrent_floor_of_compiler H hcoarse hsim
    refine ⟨G,hG,?_⟩
    intro a
    obtain ⟨u,hu,hv⟩ := hr a
    refine ⟨u,hu,?_⟩
    intro t ht s hfit
    have hj := hv t ht s hfit
    change j ≤ s+L at hj
    omega
  · right
    have hj : j+L<m := Nat.lt_of_not_ge h
    exact ⟨j,hj,hcoarse,(criticalHeight_of_maximum_drop hN H he.1.le hfine hcoarse (by omega)).2⟩

#print axioms gaussian_fixed_error_maximum_alternative
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
