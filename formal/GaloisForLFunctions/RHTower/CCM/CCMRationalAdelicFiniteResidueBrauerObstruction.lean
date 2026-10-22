import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicAzumayaResidue
import GaloisForLFunctions.RHTower.ConnesTateLocalZeta
import GaloisForLFunctions.RHTower.ConnesWeilPrimeSide
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

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

/-- If the missing `p`-adic ABHN invariant is supplied, every additive complex-valued observable
of the full local Brauer group at a rational adelic factor is still zero.  This strengthens the
finite-residue obstruction: a nonzero Tate local term cannot arise from an additive complex
functional of the full Brauer invariant either. -/
theorem ccmRationalLocalBrauerAddHom_eq_zero_of_invariant
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt)
    (g : BrauerGroup (CCMRationalLocalField v) →+ ℂ) :
    g = 0 := by
  let e := ccmRationalLocalInvariantAddEquivOfPadic v invariant
  ext x
  obtain ⟨n, hn, hx⟩ := ratModInt_exists_nonzero_nsmul_eq_zero (e x)
  have hex : n • x = 0 := by
    apply e.injective
    rw [map_nsmul]
    change n • e x = 0 at hx
    simpa using hx
  have hnx : n • g x = 0 := by
    rw [← g.map_nsmul, hex, g.map_zero]
  exact (nsmul_eq_zero_iff_right hn).mp hnx

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

/-- Even after full local ABHN is available, no additive complex-valued Brauer observable can
equal the nonzero local Tate factor in the open right half-plane. -/
theorem ccmRationalLocalBrauerAddHom_apply_ne_connesPadicTateLocalZeta_of_invariant
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt)
    (g : BrauerGroup (CCMRationalLocalField v) →+ ℂ)
    (x : BrauerGroup (CCMRationalLocalField v)) {s : ℂ} (hs : 0 < s.re) :
    g x ≠ ∫ a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ,
      Set.indicator {b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ |
        ‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤ 1}
        (fun b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ =>
          ((‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ : ℝ) : ℂ) ^ s) a
        ∂fieldOnePadicMultiplicativeHaar (Rat.HeightOneSpectrum.primesEquiv v) := by
  rw [ccmRationalLocalBrauerAddHom_eq_zero_of_invariant v invariant g]
  exact (connes_padic_tate_local_zeta_ne_zero
    (Rat.HeightOneSpectrum.primesEquiv v) hs).symm

/-- The full additive-Brauer obstruction reaches the actual finite local term in Connes's Weil
explicit formula.  A future ABHN-to-Connes/Tate comparison must be nonlinear before the local
Weil term is formed. -/
theorem ccmRationalLocalBrauerAddHom_apply_ne_connesLocalWeilTerm_of_invariant
    (v : HeightOneSpectrum ℤ)
    (invariant : BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] ≃+ RatModInt)
    (g : BrauerGroup (CCMRationalLocalField v) →+ ℂ)
    (x : BrauerGroup (CCMRationalLocalField v)) {s : ℂ} (hs : 0 < s.re) :
    g x ≠ connesLocalWeilTerm (Rat.HeightOneSpectrum.primesEquiv v) s := by
  rw [ccmRationalLocalBrauerAddHom_eq_zero_of_invariant v invariant g]
  exact (connesLocalWeilTerm_ne_zero (Rat.HeightOneSpectrum.primesEquiv v) hs).symm

end

end GaloisForLFunctions.RHTower
