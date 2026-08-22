/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaFiniteResidueFiber
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFieldEquiv
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleHaar
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Finite residue Brauer fibers on the Connes--Consani rational adeles

The actual rational finite-adele Bruhat core is a restricted product of the local fields
`CCMRationalLocalField v`, with integral factors `CCMRationalLocalIntegers v`. This module proves
that each such factor has finite residue field and hence that every integral Azumaya coefficient
algebra has split residue Brauer fiber.

This is a genuine interface between the Connes--Tate local-place architecture and ABHN's
finite-residue endpoint. It does not construct a Brauer class from the Bruhat source, identify a
local invariant, or impose a condition on completed-Xi zeros.
-/

namespace GaloisForLFunctions.RHTower

open IsDedekindDomain Rat.HeightOneSpectrum
open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- The rational prime indexing a height-one prime of `ℤ` is prime.  Making this canonical fact
available lets the corresponding `p`-adic field occur directly in local transport types. -/
instance ccmRationalLocalPrimeFact (v : HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩

/-- The residue field of the rational local factor at `v` is canonically the prime field indexed
by `v`. This identifies the finite `q_v` residue layer of the Connes--Tate local factor with the
actual arithmetic field `𝔽_p`. -/
noncomputable def ccmRationalLocalResidueFieldEquivZMod
    (v : HeightOneSpectrum ℤ) :
    IsLocalRing.ResidueField (CCMRationalLocalIntegers v) ≃+*
      ZMod (Rat.HeightOneSpectrum.primesEquiv v) := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  letI : Algebra ℤ (CCMRationalLocalIntegers v) := Ring.toIntAlgebra _
  let e : CCMRationalLocalIntegers v ≃+* ℤ_[Rat.HeightOneSpectrum.primesEquiv v] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  exact (IsLocalRing.ResidueField.mapEquiv e).trans
    (PadicInt.residueField (p := Rat.HeightOneSpectrum.primesEquiv v))

/-- The Brauer group of a local factor in the actual rational finite-adele source is identified
with the Brauer group of its standard `p`-adic presentation. This is the field-level transport
needed before a future local invariant can be compared with the `p`-adic Tate integral. -/
noncomputable def ccmRationalLocalBrauerGroupAddEquivPadic
    (v : HeightOneSpectrum ℤ) :
    BrauerGroup (CCMRationalLocalField v) ≃+
      BrauerGroup ℚ_[Rat.HeightOneSpectrum.primesEquiv v] :=
  brauerGroupAddEquivOfRingEquiv
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv

/-- On Brauer classes, the rational-local-to-`p`-adic transport is scalar extension through the
canonical completion equivalence. -/
theorem ccmRationalLocalBrauerGroupAddEquivPadic_apply
    (v : HeightOneSpectrum ℤ) (x : BrauerGroup (CCMRationalLocalField v)) :
    ccmRationalLocalBrauerGroupAddEquivPadic v x =
      @scalarExtensionBrauerMap (CCMRationalLocalField v)
        ℚ_[Rat.HeightOneSpectrum.primesEquiv v] _ _
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom.toAlgebra x :=
  brauerGroupAddEquivOfRingEquiv_apply
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv x

/-- Every local integer ring in the rational finite-adele factorization has finite residue field.
The proof transports the standard `ℤₚ` residue field along Mathlib's canonical local-ring
equivalence. -/
noncomputable instance ccmRationalLocalIntegersFiniteResidueField
    (v : HeightOneSpectrum ℤ) :
    Finite (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact Finite.of_equiv
    (ZMod (Rat.HeightOneSpectrum.primesEquiv v))
    (ccmRationalLocalResidueFieldEquivZMod v).toEquiv.symm

/-- An integral Azumaya coefficient algebra at an actual rational Connes--Consani local factor
has split residue Brauer class. This is the finite-place residue endpoint compatible with the
finite-adele Bruhat core; it is not a local invariant for `CCMRationalLocalField v`. -/
theorem ccmRationalLocalAzumayaResidueBrauerClass_eq_split
    (v : HeightOneSpectrum ℤ) (A : Type) [Ring A]
    [Algebra (CCMRationalLocalIntegers v) A] [IsAzumaya (CCMRationalLocalIntegers v) A] :
    azumayaScalarExtensionBrauerClass (CCMRationalLocalIntegers v)
      (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) A =
      brauerSplitClass (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) := by
  exact azumayaResidueBrauerClass_eq_split (CCMRationalLocalIntegers v) A

/-- Pointwise Hasse-style residue vanishing across the finite local factors of the rational adelic
source. Any family of integral Azumaya coefficient algebras has split residue fiber at every
prime. -/
theorem ccmRationalFiniteAdeleAzumayaResidueBrauerClass_eq_split
    (A : (v : HeightOneSpectrum ℤ) → Type) [∀ v, Ring (A v)]
    [∀ v, Algebra (CCMRationalLocalIntegers v) (A v)]
    [∀ v, IsAzumaya (CCMRationalLocalIntegers v) (A v)] (v : HeightOneSpectrum ℤ) :
    azumayaScalarExtensionBrauerClass (CCMRationalLocalIntegers v)
      (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) (A v) =
      brauerSplitClass (IsLocalRing.ResidueField (CCMRationalLocalIntegers v)) := by
  exact ccmRationalLocalAzumayaResidueBrauerClass_eq_split v (A v)

end

end GaloisForLFunctions.RHTower
