import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum.Measure
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-! # The unique measure inferred from the unrestricted vacuum experiment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open Filter MeasureTheory InverseSpectrum.ShellMixing
open scoped Topology

def realizes (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (μ : Measure ℝ) :=
  ∀ k : ℕ, Tendsto (fun N => calibrated (z N) (t N).val N (k+1)) atTop (𝓝 (∫ x, (x:ℝ)^k ∂μ))

/-- The detector readings force both finiteness and compact determinacy
for arbitrary candidate Borel measures. -/
theorem realizes_iff (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (μ : Measure ℝ) :
    realizes t z μ ↔ μ=spectrum := by
  constructor
  · intro h
    let v (k : ℕ) := (riemannZeta ((k+2:ℕ):ℂ)).re
    have mμ (k : ℕ) : v k=∫ x,(x:ℝ)^k ∂μ := tendsto_nhds_unique (critical_limit k t z) (h k)
    have intμ (k : ℕ) : Integrable (fun x : ℝ => x^k) μ := by
      by_contra bad
      exact (positive_moment k).ne' ((mμ k).trans (integral_undef bad))
    have one : Integrable (fun _ : ℝ => (1:ℝ)) μ := by simpa only [pow_zero] using intμ 0
    letI : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure one_ne_zero).mp one
    have ms (k : ℕ) : v k=∫ x,(x:ℝ)^k ∂spectrum := (moment k).symm
    have ci : spectrum (Set.Icc ((0:ℝ)-1) (0+1))ᶜ=0 := by simpa only [zero_sub,zero_add] using carried
    exact (_root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried (c:=0) (r:=1) zero_lt_one
      ci ms integrable_moment mμ intμ).symm
  · rintro rfl k
    rw [moment]
    exact critical_limit k t z

theorem unique_readout (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) :
    ∃! μ : Measure ℝ, realizes t z μ :=
  ⟨spectrum,(realizes_iff t z _).mpr rfl,fun μ h => (realizes_iff t z μ).mp h⟩

/-- Reconstruction uses only the binary output data across cutoffs and depths. -/
def measured (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) : Measure ℝ :=
  Classical.choose (unique_readout t z).exists

theorem measured_eq (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) :
    measured t z=spectrum := (realizes_iff t z _).mp (Classical.choose_spec (unique_readout t z).exists)

theorem measured_atoms (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (x : ℝ) :
    0 < (measured t z).real {x} ↔ ∃ k, x=occupationWeight k := by
  rw [measured_eq,atoms]

#print axioms realizes_iff
#print axioms unique_readout
#print axioms measured_atoms

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
