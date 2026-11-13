import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.Tactic

/-!
# Complementary boundary energies of a strip

The two-boundary Hardy weight is a sum of opposite exponentials. Dividing
its two square-root weights by their common normalization gives bounded
multipliers whose squared energies add exactly to the input energy.
Plancherel transports this identity to the two boundary Fourier data.
-/

namespace GaloisForLFunctions.Goldbach

open MeasureTheory FourierTransform
noncomputable section

/-- One normalized edge of the two-boundary exponential weight. -/
def stripEdgeSymbol (a x : ℝ) : ℂ :=
  Real.sqrt (Real.exp (a * x) / (Real.exp (a * x) + Real.exp (-(a * x))))

/-- The normalized boundary density is the square of its multiplier magnitude. -/
theorem norm_sq_stripEdgeSymbol (a x : ℝ) :
    ‖stripEdgeSymbol a x‖ ^ 2 =
      Real.exp (a * x) / (Real.exp (a * x) + Real.exp (-(a * x))) := by
  simp only [stripEdgeSymbol, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (by positivity)

/-- The two edge densities form an exact partition of one. -/
theorem stripEdgeSymbol_partition (a x : ℝ) :
    ‖stripEdgeSymbol a x‖ ^ 2 + ‖stripEdgeSymbol (-a) x‖ ^ 2 = 1 := by
  rw [norm_sq_stripEdgeSymbol, norm_sq_stripEdgeSymbol]
  simp only [neg_mul, neg_neg]
  have hd : Real.exp (a * x) + Real.exp (-(a * x)) ≠ 0 := by positivity
  rw [add_comm (Real.exp (-(a * x))), ← add_div, div_self hd]

/-- Every normalized edge is contractive. -/
theorem norm_stripEdgeSymbol_le_one (a x : ℝ) : ‖stripEdgeSymbol a x‖ ≤ 1 := by
  have h := stripEdgeSymbol_partition a x
  nlinarith only [h, sq_nonneg ‖stripEdgeSymbol (-a) x‖,
    sq_nonneg (‖stripEdgeSymbol a x‖ - 1)]

theorem continuous_stripEdgeSymbol (a : ℝ) : Continuous (stripEdgeSymbol a) := by
  unfold stripEdgeSymbol
  apply Complex.continuous_ofReal.comp
  apply Continuous.sqrt
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- The boundary multiplier on the corpus's continuous spectral `L²` space. -/
def stripEdgeOperator (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (continuous_stripEdgeSymbol a).measurable (by norm_num)
    (norm_stripEdgeSymbol_le_one a)

/-- The two normalized boundary energies recover the full spectral norm. -/
theorem stripEdgeOperator_energy (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖stripEdgeOperator a f‖ ^ 2 + ‖stripEdgeOperator (-a) f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq,
    _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq,
    _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  rw [← integral_add
    ((Lp.memLp (stripEdgeOperator a f)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    ((Lp.memLp (stripEdgeOperator (-a) f)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
  apply integral_congr_ae
  filter_upwards [lpBoundedMulCLM_coeFn (continuous_stripEdgeSymbol a).measurable
    (by norm_num : (0 : ℝ) ≤ 1) (norm_stripEdgeSymbol_le_one a) f,
    lpBoundedMulCLM_coeFn (continuous_stripEdgeSymbol (-a)).measurable
    (by norm_num : (0 : ℝ) ≤ 1) (norm_stripEdgeSymbol_le_one (-a)) f] with x hp hm
  change ‖(stripEdgeOperator a f) x‖ ^ 2 + ‖(stripEdgeOperator (-a) f) x‖ ^ 2 = _
  rw [show (stripEdgeOperator a f) x = stripEdgeSymbol a x * f x from hp,
    show (stripEdgeOperator (-a) f) x = stripEdgeSymbol (-a) x * f x from hm,
    norm_mul, norm_mul, mul_pow, mul_pow, ← add_mul, stripEdgeSymbol_partition, one_mul]

/-- Plancherel gives the same exact metric for the pair of boundary Fourier data. -/
theorem stripEdgeOperator_fourier_energy (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖𝓕 (stripEdgeOperator a f)‖ ^ 2 + ‖𝓕 (stripEdgeOperator (-a) f)‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [Lp.norm_fourier_eq, Lp.norm_fourier_eq, stripEdgeOperator_energy]

end
end GaloisForLFunctions.Goldbach

-- Temporary dependency audit.
#print axioms GaloisForLFunctions.Goldbach.stripEdgeSymbol
#print axioms GaloisForLFunctions.Goldbach.norm_sq_stripEdgeSymbol
#print axioms GaloisForLFunctions.Goldbach.stripEdgeSymbol_partition
#print axioms GaloisForLFunctions.Goldbach.norm_stripEdgeSymbol_le_one
#print axioms GaloisForLFunctions.Goldbach.continuous_stripEdgeSymbol
#print axioms GaloisForLFunctions.Goldbach.stripEdgeOperator
#print axioms GaloisForLFunctions.Goldbach.stripEdgeOperator_energy
#print axioms GaloisForLFunctions.Goldbach.stripEdgeOperator_fourier_energy
