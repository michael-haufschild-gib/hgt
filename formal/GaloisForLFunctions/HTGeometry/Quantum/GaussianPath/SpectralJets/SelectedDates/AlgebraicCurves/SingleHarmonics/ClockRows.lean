import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.GapClock

/-! # Independent readings of a fixed pair clock at incommensurate time ratios -/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
open PrescribedTimes.PhaseLaws
noncomputable section
variable {J : Type*} [Fintype J]

/-- All rows use the same off-pair energies of one draw. Only their
elapsed times, measured in units of the closing gap, differ. -/
def clockRows (k : ℕ) (i j : Level k) (v : J→ℝ) (x : Coupling k) (p : J×Outside i j) :=
  v p.1*gapFrequency k i j x p.2

theorem measurable_clockRows (k : ℕ) (i j : Level k) (v : J→ℝ) :
    Measurable (clockRows k i j v) :=
  measurable_pi_lambda _ fun p =>
    (((measurable_pi_apply p.2).comp (gapFrequency_measurable k i j)).const_mul (v p.1))

/-- At rationally independent multiples of the same late pair clock, all
free phase rows converge jointly to product Haar. The coefficient law
may be restricted to any fixed event of positive Gaussian probability. -/
theorem clockRows_haar (k : ℕ) (i j : Level k) (hij : i≠j) (v : J→ℝ)
    (hv : RationallyIndependentFrequency v) (μ : ProbabilityMeasure (Coupling k))
    (hμ : (μ : Measure (Coupling k))≪volume) :
    Tendsto (frequencySnapshot μ (clockRows k i j v) (measurable_clockRows k i j v)) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  refine frequencySnapshot_haar μ (clockRows k i j v) (measurable_clockRows k i j v) ?_
  intro m hm
  let a (l : Outside i j) := ∑ s : J, (m (s,l):ℝ)*v s
  have ha : a≠0 := by
    intro hz
    apply hm
    funext p
    obtain ⟨s,l⟩ := p
    exact congrFun (hv (fun q => m (q,l)) (congrFun hz l)) s
  have he (x : Coupling k) : finiteTorusCharacterDetuning m (clockRows k i j v x)=
      ∑ l, a l*gapFrequency k i j x l := by
    simp only [finiteTorusCharacterDetuning,Fintype.sum_prod_type,clockRows,a,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm
  simpa only [he] using gap_projection_ac k i j hij _ hμ a ha

#print axioms clockRows_haar
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
