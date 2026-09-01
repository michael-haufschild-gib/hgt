import GaloisForLFunctions.RHTower.DeningerQ8FroehlichFiniteSign
import GaloisForLFunctions.RHTower.DeningerQ8FroehlichLocalGaussianFactors

/-!
# Odd-prime Gaussian side of Fröhlich's Q8 formula

For the actual maximal abelian field `ℚ(√5, √41)`, this file multiplies the literal
same-additive split factor at `5` by the positively oriented quadratic factor at `41`.
The result is `-1`, exactly Fröhlich's independently defined finite residue sign `α_K β_K`.

This is the finite Gaussian-to-residue bridge. It does not identify that value with a global
Artin epsilon factor; the latter remains a separate theorem.
-/

namespace RHTower

noncomputable section

/-- Product of the two normalized odd-prime Gaussian factors selected by the actual Q8 source. -/
def deningerQ8FroehlichOddGaussianProduct : ℂ :=
  deningerQ8FroehlichSplitFiveSameAdditiveGaussianPair *
    deningerQ8FroehlichFortyOneGaussianPhase

theorem deningerQ8FroehlichOddGaussianProduct_eq_neg_one :
    deningerQ8FroehlichOddGaussianProduct = -1 := by
  rw [deningerQ8FroehlichOddGaussianProduct,
    deningerQ8FroehlichSplitFiveSameAdditiveGaussianPair_eq_neg_one,
    deningerQ8FroehlichFortyOneGaussianPhase_eq_one]
  norm_num

/-- Exact agreement of Fröhlich's local Gaussian calculation with its finite residue formula. -/
theorem deningerQ8FroehlichOddGaussianProduct_eq_finiteSign :
    deningerQ8FroehlichOddGaussianProduct =
      (deningerQ8FroehlichFiniteSign : ℂ) := by
  rw [deningerQ8FroehlichOddGaussianProduct_eq_neg_one,
    deningerQ8FroehlichFiniteSign_eq_neg_one]
  norm_num

end

end RHTower
