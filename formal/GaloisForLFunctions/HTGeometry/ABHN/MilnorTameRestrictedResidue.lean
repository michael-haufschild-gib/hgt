import GaloisForLFunctions.HTGeometry.MilnorKTameRestrictedProduct
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces

/-!
# Restricted finite tame residues for global fields

The Dedekind finite-support theorem for Milnor `K₂` specializes to the finite places of both a
number field and a rational function field over a finite field.  These are the Milnor-side
restricted-local sequences adjacent to the finite-ramification component of ABHN.

They do not identify Milnor `K₂` with a Brauer group, and do not supply the missing local
class-field-theory invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain NumberField

universe u

/-- The finite-place direct sum of tame residues for a number field. -/
noncomputable def numberFieldFiniteTameResidueDirectSum
    (K : Type u) [Field K] [NumberField K] :
    MilnorKDeg K 2 →+
      DirectSum (HeightOneSpectrum (RingOfIntegers K))
        (fun v => Additive (IsLocalRing.ResidueField (v.valuation K).valuationSubring)ˣ) :=
  tameResidueDirectSum (R := RingOfIntegers K) K

/-- The number-field finite tame-residue map is exact at `K₂^M`. -/
theorem numberFieldFiniteTameResidueDirectSum_exact
    (K : Type u) [Field K] [NumberField K] :
    Function.Exact
      (tameKernel (fun v : HeightOneSpectrum (RingOfIntegers K) => tameDataAtPlace K v)).subtype
      (numberFieldFiniteTameResidueDirectSum K) :=
  tameResidueDirectSum_exact (R := RingOfIntegers K) K

/-- Quotienting number-field `K₂^M` by its finite tame kernel gives the image of its restricted
finite tame-residue map. -/
noncomputable def numberFieldFiniteTameResidueQuotientTameKernelEquiv
    (K : Type u) [Field K] [NumberField K] :
    MilnorKDeg K 2 ⧸
        tameKernel (fun v : HeightOneSpectrum (RingOfIntegers K) => tameDataAtPlace K v) ≃+
      (numberFieldFiniteTameResidueDirectSum K).range :=
  tameResidueDirectSumQuotientTameKernelEquiv (R := RingOfIntegers K) K

/-- The finite-place direct sum of tame residues for the global function field `F(t)`. -/
noncomputable def rationalFunctionFiniteTameResidueDirectSum
    (F : Type u) [Field F] [Finite F] :
    MilnorKDeg (RatFunc F) 2 →+
      DirectSum (HeightOneSpectrum (Polynomial F))
        (fun v => Additive (IsLocalRing.ResidueField
          (v.valuation (RatFunc F)).valuationSubring)ˣ) :=
  tameResidueDirectSum (R := Polynomial F) (RatFunc F)

/-- The finite tame-residue map of `F(t)` is exact at `K₂^M(F(t))`. -/
theorem rationalFunctionFiniteTameResidueDirectSum_exact
    (F : Type u) [Field F] [Finite F] :
    Function.Exact
      (tameKernel (fun v : HeightOneSpectrum (Polynomial F) =>
        tameDataAtPlace (RatFunc F) v)).subtype
      (rationalFunctionFiniteTameResidueDirectSum F) :=
  tameResidueDirectSum_exact (R := Polynomial F) (RatFunc F)

/-- Quotienting `K₂^M(F(t))` by its finite tame kernel gives the image of its restricted finite
tame-residue map. -/
noncomputable def rationalFunctionFiniteTameResidueQuotientTameKernelEquiv
    (F : Type u) [Field F] [Finite F] :
    MilnorKDeg (RatFunc F) 2 ⧸
        tameKernel (fun v : HeightOneSpectrum (Polynomial F) =>
          tameDataAtPlace (RatFunc F) v) ≃+
      (rationalFunctionFiniteTameResidueDirectSum F).range :=
  tameResidueDirectSumQuotientTameKernelEquiv (R := Polynomial F) (RatFunc F)

end GaloisForLFunctions.HTGeometry.ABHN
