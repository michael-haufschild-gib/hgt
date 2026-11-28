import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum.Readout

/-! # Complex thermal trace directly from the measured integer spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open MeasureTheory InverseSpectrum.ShellMixing

/-- The Mellin response divided by the quadratic mass of each detected atom. -/
def response (s : ℂ) (u : ℝ) := (u:ℂ)^s/(u:ℂ)^2

private theorem weighted (s : ℂ) (n : ℕ) :
    (weight n:ℂ) * response s (occupationWeight n) = (occupationWeight n:ℂ)^s := by
  have nz := Complex.ofReal_ne_zero.mpr (occupationWeight_pos n).ne'
  rw [response,weight,Complex.ofReal_pow,mul_div_cancel₀ _ (pow_ne_zero 2 nz)]

private theorem weighted_norm (s : ℂ) (n : ℕ) :
    weight n * ‖response s (occupationWeight n)‖ = ‖(occupationWeight n:ℂ)^s‖ := by
  simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_pos n).le] using congrArg norm (weighted s n)

private theorem integral_iff (s : ℂ) : Integrable (response s) spectrum ↔ 1<s.re := by
  have absSum : Summable (fun n => ‖(occupationWeight n:ℂ)^s‖) ↔ 1<s.re := by
    rw [summable_norm_iff]
    exact summable_band_cpow_iff (hotEdge 0) s
  constructor
  · intro h
    rw [spectrum,_root_.HTGeometry.countableWeightedDirac] at h
    have hs := (integrable_sum_measure_iff.mp h).2
    apply absSum.mp
    refine hs.congr fun n => ?_
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (weight_pos n).le,smul_eq_mul,weighted_norm]
  · intro hs
    apply _root_.HTGeometry.integrable_complex_countableWeightedDirac (fun n => (weight_pos n).le)
    exact (absSum.mpr hs).congr fun n => (weighted_norm s n).symm

/-- The measured spectrum itself determines the exact trace half-plane. -/
theorem trace_domain (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) (s : ℂ) :
    Integrable (response s) (measured t z) ↔ 1<s.re := by rw [measured_eq,integral_iff]

private theorem reciprocal_cpow (n : ℕ) (s : ℂ) :
    (occupationWeight n:ℂ)^s = 1/((n:ℂ)+1)^s := by
  have harg : (((n:ℝ)+1:ℝ):ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  simpa only [occupationWeight_eq,Complex.ofReal_inv,one_div,Complex.ofReal_add,
    Complex.ofReal_natCast,Complex.ofReal_one] using Complex.inv_cpow (((n:ℝ)+1:ℝ):ℂ) s harg

/-- The integral of the response equals the Gibbs operator trace on the
original occupation Hilbert space for every complex trace temperature. -/
theorem thermal_partition (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter)
    (s : {s : ℂ // 1<s.re}) :
    (∫ u,response s.val u ∂(measured t z))=(gibbsOperator s).opTrace := by
  have hi := (integral_iff s.val).mpr s.property
  rw [measured_eq,spectrum,_root_.HTGeometry.integral_complex_countableWeightedDirac
    (fun n => (weight_pos n).le) hi,tsum_congr (weighted s.val),partition_eq_zeta,
    zeta_eq_tsum_one_div_nat_add_one_cpow s.property]
  exact tsum_congr fun n => reciprocal_cpow n s.val

#print axioms trace_domain
#print axioms thermal_partition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
