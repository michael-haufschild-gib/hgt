import GaloisForLFunctions.RHTower.CCMRationalAdelicAzumayaResidue
import GaloisForLFunctions.RHTower.ConnesTateLocalZeta

/-!
# Finite-residue Brauer obstruction for the local Tate source

The finite residue Brauer group at a rational Connes--Consani local factor is trivial, so every
additive complex-valued observable of that residue Brauer data vanishes.  By contrast, the local
Tate unit-ball integral is nonzero in the open right half-plane.  Thus a source-side comparison
with ABHN cannot factor only through the residue Brauer class: it must retain ramified, boundary,
or otherwise non-residual data.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

open IsDedekindDomain Rat.HeightOneSpectrum
open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Every additive complex-valued observable of a rational local residue Brauer group is zero. -/
theorem ccmRationalLocalResidueBrauerAddHom_eq_zero
    (v : HeightOneSpectrum ℤ)
    (f : BrauerGroup (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) →+ ℂ) :
    f = 0 := by
  letI : Subsingleton (BrauerGroup
      (IsLocalRing.ResidueField (CCMRationalLocalIntegers v))) :=
    finiteField_brauerGroup_subsingleton _
  ext x
  rw [Subsingleton.elim x 0, f.map_zero]
  rfl

/-- A finite-residue Brauer observable cannot equal the nonzero local Tate source term.
This is the precise obstruction to a direct residue-invariant specialization of the Connes/Tate
local factor. -/
theorem ccmRationalLocalResidueBrauerAddHom_apply_ne_connesPadicTateLocalZeta
    (v : HeightOneSpectrum ℤ)
    (f : BrauerGroup (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) →+ ℂ)
    (x : BrauerGroup (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)))
    {s : ℂ} (hs : 0 < s.re) :
    f x ≠ ∫ a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ,
      Set.indicator {b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ |
        ‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤ 1}
        (fun b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ =>
          ((‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ : ℝ) : ℂ) ^ s) a
        ∂fieldOnePadicMultiplicativeHaar (Rat.HeightOneSpectrum.primesEquiv v) := by
  rw [ccmRationalLocalResidueBrauerAddHom_eq_zero v f]
  exact (connes_padic_tate_local_zeta_ne_zero
    (Rat.HeightOneSpectrum.primesEquiv v) hs).symm

end

end GaloisForLFunctions.RHTower
