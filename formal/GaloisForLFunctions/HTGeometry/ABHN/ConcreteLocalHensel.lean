import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityCompletion
import GaloisForLFunctions.HTGeometry.ABHN.LaurentSeriesFiniteLocalField

/-!
# Hensel lifting in concrete local models

The generic simple-root lifting theorem for nonarchimedean local fields applies directly to every
completion model used by the global ABHN infrastructure.  This module records those applications
at finite and infinite function-field places and at finite number-field places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial LaurentSeries ValuativeRel

attribute [local instance] Ideal.Quotient.field

universe u

/-- A simple integral residue root lifts at every finite completion of a number field. -/
theorem numberFieldFinitePlace_hensel_lift
    (K : Type u) [Field K] [NumberField K] (v : NumberField.FinitePlace K)
    (f : Polynomial 𝒪[completion K (.finite v)]) (hf : f.Monic)
    (a₀ : 𝒪[completion K (.finite v)])
    (hroot : Ideal.Quotient.mk 𝓂[completion K (.finite v)] (f.eval a₀) = 0)
    (hsimple : Ideal.Quotient.mk 𝓂[completion K (.finite v)] (f.derivative.eval a₀) ≠ 0) :
    ∃ a : 𝒪[completion K (.finite v)], f.IsRoot a ∧ a - a₀ ∈ 𝓂[completion K (.finite v)] :=
  nonarchimedeanLocalField_hensel_lift (completion K (.finite v)) f hf a₀ hroot hsimple

/-- A simple integral residue root lifts at every finite completion of `ℚ`. -/
theorem rationalFinitePlace_hensel_lift
    (v : NumberField.FinitePlace ℚ)
    (f : Polynomial 𝒪[completion ℚ (.finite v)]) (hf : f.Monic)
    (a₀ : 𝒪[completion ℚ (.finite v)])
    (hroot : Ideal.Quotient.mk 𝓂[completion ℚ (.finite v)] (f.eval a₀) = 0)
    (hsimple : Ideal.Quotient.mk 𝓂[completion ℚ (.finite v)] (f.derivative.eval a₀) ≠ 0) :
    ∃ a : 𝒪[completion ℚ (.finite v)], f.IsRoot a ∧ a - a₀ ∈ 𝓂[completion ℚ (.finite v)] :=
  nonarchimedeanLocalField_hensel_lift (completion ℚ (.finite v)) f hf a₀ hroot hsimple

/-- A simple integral residue root lifts at every finite completion of a finite rational-function
field. -/
theorem rationalFunctionFinitePlace_hensel_lift
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X])
    (f : Polynomial 𝒪[rationalFunctionCompletion F (.finite v)]) (hf : f.Monic)
    (a₀ : 𝒪[rationalFunctionCompletion F (.finite v)])
    (hroot : Ideal.Quotient.mk 𝓂[rationalFunctionCompletion F (.finite v)] (f.eval a₀) = 0)
    (hsimple : Ideal.Quotient.mk 𝓂[rationalFunctionCompletion F (.finite v)]
      (f.derivative.eval a₀) ≠ 0) :
    ∃ a : 𝒪[rationalFunctionCompletion F (.finite v)], f.IsRoot a ∧
      a - a₀ ∈ 𝓂[rationalFunctionCompletion F (.finite v)] :=
  nonarchimedeanLocalField_hensel_lift (rationalFunctionCompletion F (.finite v))
    f hf a₀ hroot hsimple

/-- A simple integral residue root lifts at the infinite completion of a finite
rational-function field. -/
theorem rationalFunctionInfinitePlace_hensel_lift
    (F : Type u) [Field F] [Finite F]
    (f : Polynomial 𝒪[rationalFunctionCompletion F .infinite]) (hf : f.Monic)
    (a₀ : 𝒪[rationalFunctionCompletion F .infinite])
    (hroot : Ideal.Quotient.mk 𝓂[rationalFunctionCompletion F .infinite] (f.eval a₀) = 0)
    (hsimple : Ideal.Quotient.mk 𝓂[rationalFunctionCompletion F .infinite]
      (f.derivative.eval a₀) ≠ 0) :
    ∃ a : 𝒪[rationalFunctionCompletion F .infinite], f.IsRoot a ∧
      a - a₀ ∈ 𝓂[rationalFunctionCompletion F .infinite] :=
  nonarchimedeanLocalField_hensel_lift (rationalFunctionCompletion F .infinite)
    f hf a₀ hroot hsimple

/-- A simple integral residue root lifts in the finite-coefficient Laurent-series local field. -/
theorem laurentSeries_hensel_lift
    (F : Type u) [Field F] [Finite F] (f : Polynomial 𝒪[F⸨X⸩]) (hf : f.Monic)
    (a₀ : 𝒪[F⸨X⸩])
    (hroot : Ideal.Quotient.mk 𝓂[F⸨X⸩] (f.eval a₀) = 0)
    (hsimple : Ideal.Quotient.mk 𝓂[F⸨X⸩] (f.derivative.eval a₀) ≠ 0) :
    ∃ a : 𝒪[F⸨X⸩], f.IsRoot a ∧ a - a₀ ∈ 𝓂[F⸨X⸩] :=
  nonarchimedeanLocalField_hensel_lift F⸨X⸩ f hf a₀ hroot hsimple

end GaloisForLFunctions.HTGeometry.ABHN
