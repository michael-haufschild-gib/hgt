import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Response
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.Domains

/-! # Regularity of the complex response up to each finite line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem majorant_sum (v : MissingWave) {a : ℝ} (h : finiteSplit v (a:ℂ)) :
    Summable (fun n => shellMass (a:ℂ) n*occupationProbability v n) :=
  Equiv.pnatEquivNat.symm.summable_iff.mp ((finiteSplit_iff_law _ _).mp h)

private theorem majorant_le (v : MissingWave) {a : ℝ} {z : ℂ} (h : a ≤ z.re) (n : ℕ+) :
    ‖(occupationProbability v n:ℂ)*heat (2*z-1) n‖ ≤ shellMass (a:ℂ) n*occupationProbability v n := by
  rw [compositionTerm_norm]
  exact mul_le_mul_of_nonneg_right (shellMass_antitone_re (t := (a:ℂ)) h n) ((exteriorLaw v).property.1 n)

private theorem term_entire (v : MissingWave) (n : ℕ+) :
    Differentiable ℂ (fun z : ℂ => (occupationProbability v n:ℂ)*heat (2*z-1) n) := by
  unfold heat
  fun_prop

/-- A single finite reading gives continuity up to its full vertical line. -/
theorem compositionResponse_continuous_from (v : MissingWave) {a : ℝ} (h : finiteSplit v (a:ℂ)) :
    ContinuousOn (compositionResponse v) {z : ℂ | a ≤ z.re} :=
  continuousOn_tsum (fun n => (term_entire v n).continuous.continuousOn) (majorant_sum v h)
    (fun n _ hz => majorant_le v hz n)

/-- All points strictly to the right of an individual split abscissa are ordinary holomorphic points. -/
theorem compositionResponse_analytic_at (v : MissingWave) {s : ℂ} (h : splitAbscissa v < s.re) :
    AnalyticAt ℂ (compositionResponse v) s := by
  obtain ⟨a,ha,hs⟩ := exists_between h
  have hf : finiteSplit v (a:ℂ) := (finiteSplit_iff_abscissa v _).mpr (Or.inl ha)
  have hopen : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (compositionResponse v) {z : ℂ | a < z.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (majorant_sum v hf) (fun n => (term_entire v n).differentiableOn)
      hopen (fun n _ (hz : a < _) => majorant_le v hz.le n)
  exact hd.analyticOnNhd hopen s hs

#print axioms compositionResponse_continuous_from
#print axioms compositionResponse_analytic_at

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
