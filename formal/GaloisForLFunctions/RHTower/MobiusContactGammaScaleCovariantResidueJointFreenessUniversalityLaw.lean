import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma scale/covariant-residue joint freeness universality

After the canonical pole-index shift, the negative finite contact defect is the reciprocal
signed-factorial germ. It is therefore jointly algebraically independent with the complete
countable family of intrinsic Gamma simple-zero covariant residues.
-/

open Filter

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance mobiusContactGammaNatGermAlgebra :
    Algebra ℂ GaloisForLFunctions.NatGerm :=
  GaloisForLFunctions.complexNatGerm.toAlgebra

/-- Pole-index germ of the negative finite Möbius contact defect, shifted so depth `N - 1`
corresponds to the signed-factorial index `N`. -/
def mobiusContactGammaReciprocalScaleGerm : GaloisForLFunctions.NatGerm :=
  fun N : ℕ => -((-2 - mobiusGammaContactPartialCharge (N - 1)) / 2)

theorem mobiusContactGammaReciprocalScaleGerm_eq_reciprocalSignedFactorialGerm :
    mobiusContactGammaReciprocalScaleGerm =
      GaloisForLFunctions.reciprocalSignedFactorialGerm := by
  change
    (↑(fun N : ℕ => -((-2 - mobiusGammaContactPartialCharge (N - 1)) / 2)) :
      GaloisForLFunctions.NatGerm) =
    (↑GaloisForLFunctions.reciprocalSignedFactorialSequence :
      GaloisForLFunctions.NatGerm)
  rw [Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨1, fun N hN => by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
    have hscale :
        (-2 - mobiusGammaContactPartialCharge n) / 2 =
          GaloisForLFunctions.reciprocalGammaFactorialScale n := by
      rw [mobiusGammaContactPartialCharge_eq]
      simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
      ring
    change -((-2 - mobiusGammaContactPartialCharge ((1 + n) - 1)) / 2) =
      GaloisForLFunctions.reciprocalSignedFactorialSequence (1 + n)
    rw [Nat.add_sub_cancel_left, hscale]
    simpa [Nat.add_comm] using
      (GaloisForLFunctions.reciprocalSignedFactorialSequence_succ_eq_neg_scale n).symm⟩

/-- The observable contact scale together with every complete covariant simple-zero residue. -/
def mobiusContactGammaScaleAndCovariantResidueFamily :
    Option ℕ → GaloisForLFunctions.NatGerm
  | none => mobiusContactGammaReciprocalScaleGerm
  | some j => GaloisForLFunctions.gammaSimpleZeroCovariantResidueGerm j

theorem mobiusContactGammaScaleAndCovariantResidueFamily_eq :
    mobiusContactGammaScaleAndCovariantResidueFamily =
      GaloisForLFunctions.gammaPoleScaleAndCovariantResidueFamily := by
  funext o
  rcases o with (_ | j)
  · exact mobiusContactGammaReciprocalScaleGerm_eq_reciprocalSignedFactorialGerm
  · rfl

/-- **Möbius-contact Gamma scale/covariant-residue joint freeness universality law.** No nonzero
finite polynomial relation over `ℂ` can couple the contact scale germ to any finite selection of
intrinsic simple-zero residue grades. -/
theorem algebraicIndependent_mobiusContactGammaScaleAndCovariantResidueFamily :
    AlgebraicIndependent ℂ mobiusContactGammaScaleAndCovariantResidueFamily := by
  rw [mobiusContactGammaScaleAndCovariantResidueFamily_eq]
  exact GaloisForLFunctions.algebraicIndependent_gammaPoleScaleAndCovariantResidueFamily

end

end GaloisForLFunctions.RHTower
