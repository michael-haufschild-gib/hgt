import GaloisForLFunctions.HTGeometry.FokasLenellsCausalPhase

/-!
# The rational rate map behind actual causal phase eigenvalues

The phase rate is an involution of the complex plane with its total inverse
convention at zero. It exchanges the open upper half-plane with the open left
half-plane. Thus the actual rational eigenvector parametrization reaches every
strictly negative-real-part rate, without an existence premise.
-/

open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual time rate of the singular analytic phase at a complex pole. -/
def causalPoleRate (w : ℂ) : ℂ := -(I/w)/2

/-- Exact real part of the rational phase rate, including the total inverse value at zero. -/
theorem causalPoleRate_re (w : ℂ) : (causalPoleRate w).re = -(w.im/Complex.normSq w)/2 := by
  change ((-(I/w))/((2:ℝ):ℂ)).re = _
  rw [Complex.div_ofReal_re]
  simp only [Complex.neg_re,Complex.div_re,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_div,zero_add]

/-- Exact imaginary part of the same rational phase rate. -/
theorem causalPoleRate_im (w : ℂ) : (causalPoleRate w).im = -(w.re/Complex.normSq w)/2 := by
  change ((-(I/w))/((2:ℝ):ℂ)).im = _
  rw [Complex.div_ofReal_im]
  simp only [Complex.neg_im,Complex.div_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_div,sub_zero]

/-- The actual rational rate map is its own inverse on the entire complex plane. -/
theorem causalPoleRate_involution (w : ℂ) : causalPoleRate (causalPoleRate w) = w := by
  by_cases hw : w = 0
  · simp only [hw,causalPoleRate,div_zero,neg_zero,zero_div]
  · unfold causalPoleRate
    field_simp [hw]

/-- Every upper pole has a strictly negative real time rate. -/
theorem causalPoleRate_re_neg (w : {z : ℂ // 0 < z.im}) : (causalPoleRate w.val).re < 0 := by
  have hw : w.val ≠ 0 := by
    intro h
    have hp := w.property
    simp only [h,Complex.zero_im,lt_self_iff_false] at hp
  rw [causalPoleRate_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos w.property (Complex.normSq_pos.mpr hw))) (by norm_num)

/-- The actual upper pole determined by an arbitrary open-left-half-plane rate. -/
def causalEigenPole (z : {z : ℂ // z.re < 0}) : {w : ℂ // 0 < w.im} :=
  ⟨causalPoleRate z.val,by
    have hz : z.val ≠ 0 := by
      intro h
      have hp := z.property
      simp only [h,Complex.zero_re,lt_self_iff_false] at hp
    rw [causalPoleRate_im]
    exact div_pos (neg_pos.mpr (div_neg_of_neg_of_pos z.property (Complex.normSq_pos.mpr hz))) (by norm_num)⟩

/-- Every open-left-half-plane rate is reached by its explicitly constructed upper pole. -/
theorem causalPoleRate_eigenPole (z : {z : ℂ // z.re < 0}) :
    causalPoleRate (causalEigenPole z).val = z.val := causalPoleRate_involution z.val

/-- The paper's actual analytic phase is the ordinary exponential of the rational rate. -/
theorem causalAnalyticPhase_rate (t : ℝ≥0) (w : ℂ) :
    causalAnalyticPhase t w = Complex.exp (((t:ℝ):ℂ)*causalPoleRate w) := by
  unfold causalAnalyticPhase causalPoleRate
  congr 1
  rw [Complex.ofReal_div]
  norm_num only [Complex.ofReal_ofNat]
  ring

end
end RHTower.FokasLenells
