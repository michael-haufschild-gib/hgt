/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.RHTower.CCMRationalAdelicFiniteResidueBrauerObstruction
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalBrauerInvariant

/-!
# Full local Brauer obstruction for the Connes--Tate source

The nonarchimedean local Brauer isomorphism discharges the formerly conditional `p`-adic ABHN
premise in the rational Connes--Consani model.  Consequently every additive complex observable
of the full local Brauer group vanishes, while both the Tate local zeta integral and Connes local
Weil term are nonzero in the open right half-plane.  Any source comparison using Brauer data must
therefore be nonlinear before those local analytic terms are formed.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

open IsDedekindDomain Rat.HeightOneSpectrum
open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

theorem ccmRationalLocalBrauerAddHom_eq_zero
    (v : HeightOneSpectrum ℤ)
    (g : BrauerGroup (CCMRationalLocalField v) →+ ℂ) :
    g = 0 :=
  ccmRationalLocalBrauerAddHom_eq_zero_of_invariant v
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt
      ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) g

theorem ccmRationalLocalBrauerAddHom_apply_ne_connesPadicTateLocalZeta
    (v : HeightOneSpectrum ℤ)
    (g : BrauerGroup (CCMRationalLocalField v) →+ ℂ)
    (x : BrauerGroup (CCMRationalLocalField v)) {s : ℂ} (hs : 0 < s.re) :
    g x ≠ ∫ a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ,
      Set.indicator {b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ |
        ‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ ≤ 1}
        (fun b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v]ˣ =>
          ((‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ : ℝ) : ℂ) ^ s) a
        ∂fieldOnePadicMultiplicativeHaar (Rat.HeightOneSpectrum.primesEquiv v) :=
  ccmRationalLocalBrauerAddHom_apply_ne_connesPadicTateLocalZeta_of_invariant v
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt
      ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) g x hs

theorem ccmRationalLocalBrauerAddHom_apply_ne_connesLocalWeilTerm
    (v : HeightOneSpectrum ℤ)
    (g : BrauerGroup (CCMRationalLocalField v) →+ ℂ)
    (x : BrauerGroup (CCMRationalLocalField v)) {s : ℂ} (hs : 0 < s.re) :
    g x ≠ connesLocalWeilTerm (Rat.HeightOneSpectrum.primesEquiv v) s :=
  ccmRationalLocalBrauerAddHom_apply_ne_connesLocalWeilTerm_of_invariant v
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt
      ℚ_[Rat.HeightOneSpectrum.primesEquiv v]) g x hs

end

end GaloisForLFunctions.RHTower
