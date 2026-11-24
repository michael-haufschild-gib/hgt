import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.SplitDomain

/-! # The complex Born response of divisor composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Mellin transform of the occupation law with the multiplicity of the two-copy split. -/
def compositionResponse (v : MissingWave) (s : ℂ) : ℂ :=
  ∑' n : ℕ+, (occupationProbability v n:ℂ)*heat (2*s-1) n

theorem composition_heat_norm (s : ℂ) (n : ℕ+) : ‖heat (2*s-1) n‖ = shellMass s n := by
  rw [norm_heat,shellMass]
  congr 1
  simp only [two_mul,Complex.sub_re,Complex.add_re,Complex.one_re]
  ring

theorem compositionTerm_norm (v : MissingWave) (s : ℂ) (n : ℕ+) :
    ‖(occupationProbability v n:ℂ)*heat (2*s-1) n‖ = shellMass s n*occupationProbability v n := by
  have h : 0 ≤ occupationProbability v n := (exteriorLaw v).property.1 n
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg h,composition_heat_norm,mul_comm]

/-- Absolute convergence has precisely the domain of the pair wave. -/
theorem response_absolute_iff (v : MissingWave) (s : ℂ) :
    Summable (fun n : ℕ+ => ‖(occupationProbability v n:ℂ)*heat (2*s-1) n‖) ↔ finiteSplit v s := by
  rw [finiteSplit_iff_law,← Equiv.pnatEquivNat.symm.summable_iff
    (f := fun n : ℕ+ => ‖(occupationProbability v n:ℂ)*heat (2*s-1) n‖)]
  change Summable (fun k => ‖(occupationProbability v (number k):ℂ)*heat (2*s-1) (number k)‖) ↔ _
  exact (congrArg Summable (funext fun k => compositionTerm_norm v s (number k))).to_iff

private theorem real_weight (x : ℝ) (n : ℕ+) : heat (2*(x:ℂ)-1) n = (shellMass (x:ℂ) n:ℂ) := by
  have he : -(2*(x:ℂ)-1)*(energy n:ℂ) = (((1-2*x)*energy n:ℝ):ℂ) := by push_cast; ring
  rw [heat,he,shellMass,Complex.ofReal_re,Complex.ofReal_exp]

/-- A real split reading gives the value of the complex response at that same temperature. -/
theorem compositionResponse_of_reading {v : MissingWave} {x r : ℝ} (hr : splitMassReading v (x:ℂ) r) :
    compositionResponse v (x:ℂ) = (r:ℂ) := by
  have ht := (splitMassReading_iff v _ _).mp hr
  have hpos : HasSum (fun n : ℕ+ => shellMass (x:ℂ) n*occupationProbability v n) r :=
    Equiv.pnatEquivNat.symm.hasSum_iff.mp ht
  rw [compositionResponse,← hpos.tsum_eq,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [real_weight,Complex.ofReal_mul,mul_comm]

open Filter Topology in
theorem compositionResponse_of_germ {v w : MissingWave} {z : ℂ} (hz : 0 < z.re)
    (hg : omissionPartition v =ᶠ[𝓝 z] omissionPartition w) : compositionResponse v = compositionResponse w := by
  funext s
  simp only [compositionResponse,(omission_germ_iff_probability v w hz).mp hg]

#print axioms composition_heat_norm
#print axioms compositionTerm_norm
#print axioms response_absolute_iff
#print axioms compositionResponse_of_reading
#print axioms compositionResponse_of_germ

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
