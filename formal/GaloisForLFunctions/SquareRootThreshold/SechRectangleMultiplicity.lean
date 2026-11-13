import GaloisForLFunctions.SquareRootThreshold.SechStripKernel
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.RectIntegralEdges

/-!
# Positive strip weights retain zero multiplicities

The weighted argument principle, combined with positivity of the reciprocal
cosine, bounds each enclosed multiplicity by the rectangle boundary integral.
-/

open Complex Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.SquareRootThreshold

open GaloisForLFunctions.HTGeometry _root_.RHTower _root_.RHTower.Sieve

noncomputable section

private theorem abs_re_sub_half_le_of_mem_rectangle {b : ℝ} {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (hleft : |z₁.re - 1 / 2| ≤ b)
    (hright : |z₂.re - 1 / 2| ≤ b)
    (hz : z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im)) :
    |z.re - 1 / 2| ≤ b := by
  obtain ⟨hzre, _⟩ := Complex.mem_reProdIm.mp hz
  rw [uIcc_of_le hre] at hzre
  obtain ⟨hl, _⟩ := abs_le.mp hleft
  obtain ⟨_, hr⟩ := abs_le.mp hright
  exact abs_le.mpr ⟨by linarith only [hl, hzre.1], by linarith only [hr, hzre.2]⟩

/-- Positivity of the secant strip weight retains each enclosed zero with its exact
analytic multiplicity in the weighted argument principle. -/
theorem multiplicity_mul_sechStripWeight_le_rectangle
    {a b T : ℝ} (hb : 0 ≤ b) (hba : b < a) {z₁ z₂ ρ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hl : |z₁.re - 1 / 2| ≤ b) (hr : |z₂.re - 1 / 2| ≤ b)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0)
    (hρ : ρ ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂) :
    ((analyticOrderAt zetaResidueUnit ρ).toNat : ℝ) * (sechStripWeight a T ρ).re ≤
      (rectIntegral (fun z => sechStripWeight a T z * logDeriv zetaResidueUnit z)
        z₁ z₂).im / (2 * Real.pi) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      {s : ℂ | |s.re - 1 / 2| < a} := by
    intro z hz
    exact lt_of_le_of_lt (abs_re_sub_half_le_of_mem_rectangle hre.le hl hr hz) hba
  have hres := rectIntegral_mul_logDeriv_zetaResidueUnit_eq_closedRectangleZeroSum
    (isOpen_lt (by fun_prop) continuous_const)
    (analyticOnNhd_sechStripWeight ha T) hsub hre him hbot htop hright hleft
  have hsum : ((analyticOrderAt zetaResidueUnit ρ).toNat : ℝ) *
      (sechStripWeight a T ρ).re ≤
      ∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (sechStripWeight a T w).re := by
    apply Finset.single_le_sum _ hρ
    intro w hw
    exact mul_nonneg (Nat.cast_nonneg _) (sechStripWeight_re_pos ha
      (hsub (mem_zetaResidueUnitClosedRectangleZeros.mp hw).1)).le
  have himres := congrArg Complex.im hres
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im,
    map_sum, zero_mul, mul_zero, zero_add, add_zero,
    mul_one, sub_zero] at himres
  rw [himres, mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  exact hsum

end
end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.multiplicity_mul_sechStripWeight_le_rectangle
