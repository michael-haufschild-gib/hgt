import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentLogEquiv
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentDimension
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Complete logarithmic coordinates for the actual finite clock gauge groups

The scalar character and the positive resonant coefficients of the normalized
matrix logarithm give a full group equivalence. The inverse is the literal
finite exponential followed by the literal scalar-matrix section.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Exact additive positive-resonance coordinates for the entire actual unipotent group. -/
def gomesTruncatedJetUnipotentCoordinates (n : ℕ) (z : ℂ) :
    gomesTruncatedJetUnipotentGroup n z ≃*
      Multiplicative (GomesTruncatedJetPositiveResonantIndex n z → ℂ) :=
  (gomesTruncatedJetUnipotentLogEquiv n z).trans
    (AddEquiv.toMultiplicative (gomesTruncatedJetNilpotentLinearEquiv n z).toAddEquiv)

/-- Every logarithmic coordinate is the actual positive resonant entry of the terminating matrix logarithm. -/
theorem gomesTruncatedJetUnipotentCoordinates_apply (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z u) k =
      (gomesTruncatedJetUnipotentLogarithm n z u).val.val 0 k.val.val := rfl

/-- The inverse positive-resonance chart is the literal finite exponential of the reconstructed nilpotent matrix. -/
theorem gomesTruncatedJetUnipotentCoordinates_symm (n : ℕ) (z : ℂ)
    (c : GomesTruncatedJetPositiveResonantIndex n z → ℂ) :
    (gomesTruncatedJetUnipotentCoordinates n z).symm (Multiplicative.ofAdd c) =
      gomesTruncatedJetUnipotentExponential n z ((gomesTruncatedJetNilpotentLinearEquiv n z).symm c) := by
  apply (gomesTruncatedJetUnipotentCoordinates n z).injective
  rw [MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  change c = gomesTruncatedJetNilpotentLinearEquiv n z
    (gomesTruncatedJetUnipotentLogarithm n z (gomesTruncatedJetUnipotentExponential n z
      ((gomesTruncatedJetNilpotentLinearEquiv n z).symm c)))
  rw [gomesTruncatedJetUnipotentLogarithm_exponential, LinearEquiv.apply_symm_apply]

/-- Matrix multiplication becomes coordinate addition on the whole unipotent group. -/
theorem gomesTruncatedJetUnipotentCoordinates_mul (n : ℕ) (z : ℂ)
    (u v : gomesTruncatedJetUnipotentGroup n z) :
    Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z (u * v)) =
      Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z u) +
      Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z v) :=
  congrArg Multiplicative.toAdd (map_mul (gomesTruncatedJetUnipotentCoordinates n z) u v)

/-- The full actual gauge group is nonzero complex scalars times the additive positive-resonance coordinate space. -/
def gomesTruncatedJetGaugeLogCoordinates (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z ≃*
      ℂˣ × Multiplicative (GomesTruncatedJetPositiveResonantIndex n z → ℂ) :=
  (gomesTruncatedJetGaugeSplitting n z).trans
    (MulEquiv.prodCongr (MulEquiv.refl ℂˣ) (gomesTruncatedJetUnipotentCoordinates n z))

/-- The first complete gauge coordinate is the actual scalar character. -/
theorem gomesTruncatedJetGaugeLogCoordinates_fst (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    (gomesTruncatedJetGaugeLogCoordinates n z u).1 = gomesTruncatedJetGaugeCharacter n z u := rfl

/-- The remaining complete gauge coordinates are the positive resonant entries of its normalized logarithm. -/
theorem gomesTruncatedJetGaugeLogCoordinates_snd (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    Multiplicative.toAdd (gomesTruncatedJetGaugeLogCoordinates n z u).2 k =
      (gomesTruncatedJetUnipotentLogarithm n z (gomesTruncatedJetUnipotentPart n z u)).val.val 0 k.val.val := rfl

/-- Arbitrary scalar and additive resonant coordinates reconstruct a unique actual gauge matrix by exponential and scalar section. -/
theorem gomesTruncatedJetGaugeLogCoordinates_symm (n : ℕ) (z : ℂ) (c : ℂˣ)
    (a : GomesTruncatedJetPositiveResonantIndex n z → ℂ) :
    (gomesTruncatedJetGaugeLogCoordinates n z).symm (c, Multiplicative.ofAdd a) =
      gomesTruncatedJetScalarSection n z c *
        (gomesTruncatedJetUnipotentExponential n z ((gomesTruncatedJetNilpotentLinearEquiv n z).symm a)).val := by
  change (gomesTruncatedJetGaugeSplitting n z).symm
    (c, (gomesTruncatedJetUnipotentCoordinates n z).symm (Multiplicative.ofAdd a)) = _
  rw [gomesTruncatedJetUnipotentCoordinates_symm, gomesTruncatedJetGaugeSplitting_symm]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
