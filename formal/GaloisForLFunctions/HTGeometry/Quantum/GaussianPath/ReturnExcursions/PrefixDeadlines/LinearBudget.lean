import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.PhysicalOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.GaussianLaw

/-! # First-return deadlines at twice the cost of one path-product step -/

open Set MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
open SharpOccupation PhaseBoundary
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- A linear gate allowance improves the explicit scalar occupation floor by
`√D/(128πJ)`, where `J` is the number of terms in the path Hamiltonian.
The deadline uses affordable time only up to the chosen observation origin. -/
theorem gaussian_linear_budget_deadline :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let J := Fintype.card (PathLabel (k+1))
      ∀ (s : ℕ) (e : ℝ), J + J ≤ s → e ∈ Ioc (0 : ℝ) (1/4) →
        let μ := zeroGateArcDensity D (physicalArc e/2)
        ∀ a≥(0:ℝ), Real.sqrt (D:ℝ)*μ*firstVisit H a s e ≤
          128*Real.pi*(J:ℝ)*volume.real (visitSet H s e∩Icc 0 a) := by
  filter_upwards [gaussian_observed_prefix_deadline,FluxOccupation.gaussian_fixed_error_occupation_gain,
    gaussian_uniform_affordable_fraction,gaussian_path_all_prefixes_maximally_projective] with ω hpre hgain hmass henergy
  intro k N D H J s e hJ he μ a ha
  have hsmall : e<Real.sqrt 2 := by
    nlinarith only [he.2,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  obtain ⟨hx,htol⟩ := physicalArc_spec he.1 hsmall
  let y : Icc (0:ℝ) (1/2) := ⟨physicalArc e/2,div_nonneg hx.1.le zero_le_two,
    by linarith only [hx.2]⟩
  let d := zeroGateArcTolerance y
  have hy : 0<(y:ℝ) := half_pos hx.1
  have hd : 0<d := calc
    0 = zeroGateArcTolerance 0 := by simp [zeroGateArcTolerance]
    _ < d := strictMonoOn_zeroGateArcTolerance
      (show (0:ℝ)∈Icc (0:ℝ) (1/2) by constructor <;> norm_num) y.2 hy
  have hde : d<e := (strictMonoOn_zeroGateArcTolerance y.2 (Ioo_subset_Icc_self hx)
    (show (y:ℝ)<physicalArc e from half_lt_self hx.1)).trans_eq htol
  have h₀ := zero_visitFraction_tendsto H (henergy k) y 0
  have hJlim := hmass k J d (fun _ => 0)
  simp only [zero_add] at hJlim
  have hg := le_of_tendsto_of_tendsto (h₀.const_mul (Real.sqrt (D:ℝ)))
    (hJlim.const_mul (128*Real.pi*(J:ℝ))) (hgain k d hd (hde.le.trans he.2))
  have hv := (firstVisit_isLeast H a s he.1).1.1
  have hw := hpre k J s e hJ ⟨he.1,by linarith only [he.2]⟩ a ha
  exact (mul_le_mul_of_nonneg_right hg (ha.trans hv)).trans
    ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left hw (by positivity)))

#print axioms gaussian_linear_budget_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
