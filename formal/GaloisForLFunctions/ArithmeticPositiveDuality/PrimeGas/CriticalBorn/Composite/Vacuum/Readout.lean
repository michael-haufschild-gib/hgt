import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Branch
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction.Partition

/-! # The prime spectrum and complex trace from one vacuum detector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum

open MeasureTheory Filter Real
open scoped Topology
open Collisions

/-- One elementary excitation is used at every depth. After each success
the surviving output is fed back into the next divisor split. -/
def reading (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (k N : ℕ) :=
  log (log N)*probability 1 (t N).val N (z N) (k+1)

/-- Every depth uses the same logarithmic normalization. The clock phases
may change with the cutoff, with the input, and at each successive split. -/
theorem reading_limit (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (k : ℕ) :
    Tendsto (reading t z k) atTop (𝓝 (_root_.RHTower.primeZeta ((k+2:ℕ):ℝ))) := by
  have num := (powerMass_limit (replicated_negative k)).comp tendsto_natCast_atTop_atTop
  have den := harmonic_mass_ratio.comp tendsto_natCast_atTop_atTop
  have lim := num.div den one_ne_zero
  rw [div_one,total_eq_primeZeta] at lim
  apply lim.congr'
  filter_upwards [Crossover.logEnergy_growth.eventually_gt_atTop 0] with N hl
  change powerMass (1-((k+2:ℕ):ℝ)) N/(powerMass 0 N/log (log N))=_
  rw [reading,probability_eq,(t N).property,show (1:ℝ)-2*(1/2)=0 by ring,zero_sub,pow_one,
    show -((k+1:ℕ):ℝ)=1-((k+2:ℕ):ℝ) by push_cast; ring]
  field_simp [(powerMass_pos 0 N).ne',(show 0<log (log (N:ℝ)) from hl).ne']

theorem composite_limit (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (k m : ℕ) :
    Tendsto (fun N : ℕ => (log (log N))^m*probability m (t N).val N (z N) (k+1)) atTop
      (𝓝 ((_root_.RHTower.primeZeta ((k+2:ℕ):ℝ))^m)) := by
  apply ((reading_limit t z k).pow m).congr
  intro N
  rw [reading,mul_pow,probability_eq,probability_eq,pow_one]

def realizes (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (μ : Measure ℝ) :=
  ∀ k : ℕ, Tendsto (reading t z k) atTop (𝓝 (∫ x, (x:ℝ)^k ∂μ))

/-- The single-detector data determine exactly the measure of the
independent replica experiments, including all its atoms. -/
theorem realizes_iff (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (μ : Measure ℝ) :
    realizes t z μ ↔ μ=Reconstruction.intensity := by
  constructor
  · intro h
    apply (Reconstruction.realizes_iff μ).mp
    intro k
    rw [←tendsto_nhds_unique (reading_limit t z k) (h k)]
    exact Reconstruction.reading_limit k
  · rintro rfl k
    rw [Reconstruction.moment]
    exact reading_limit t z k

theorem unique_readout (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) :
    ∃! μ : Measure ℝ, realizes t z μ := ⟨_,(realizes_iff t z _).mpr rfl,
      fun μ h => (realizes_iff t z μ).mp h⟩

/-- The measured measure is defined solely by consecutive vacuum outcomes. -/
def measured (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) : Measure ℝ :=
  Classical.choose (unique_readout t z).exists

theorem measured_eq (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) :
    measured t z=Reconstruction.reconstructed := by
  rw [Reconstruction.reconstructed_eq]
  exact (realizes_iff t z _).mp (Classical.choose_spec (unique_readout t z).exists)

theorem atoms (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (x : ℝ) :
    0<(measured t z).real {x} ↔ ∃ p : Nat.Primes, x=Reconstruction.node p.val := by
  rw [measured_eq,Reconstruction.atoms]

/-- One vacuum detector on the composition output determines the entire
Gibbs trace, through an integrable test of its measured spectrum. -/
theorem thermal_partition (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter)
    (s : {s : ℂ // 1<s.re}) :
    Complex.exp (∫ u,Reconstruction.eulerResponse s.val u ∂(measured t z))=(gibbsOperator s).opTrace := by
  rw [measured_eq,Reconstruction.thermal_partition]

#print axioms reading_limit
#print axioms composite_limit
#print axioms unique_readout
#print axioms atoms
#print axioms thermal_partition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum
