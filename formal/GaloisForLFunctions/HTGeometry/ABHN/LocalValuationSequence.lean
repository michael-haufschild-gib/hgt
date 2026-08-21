/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.MilnorKResidueValuation

/-!
# Split valuation sequence for a discrete residue datum

A `ResidueData K k` packages an integer-valued valuation on `K`, its residue map on valuation-zero
units, and a chosen uniformizer.  The uniformizer supplies a closed splitting of the valuation:
the quotient of `Kˣ` by valuation-zero units is the integer value group.

This is the valuation/unit layer used before local class field theory.  It is not a local
reciprocity theorem and makes no Brauer-group or local-invariant assertion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

variable {K : Type u} [Field K] {k : Type v} [Field k] (D : ResidueData K k)

/-- The chosen uniformizer gives a multiplicative section of the integer-valued valuation. -/
noncomputable def residueDataValuationSection : Multiplicative ℤ →* Kˣ where
  toFun n := D.unif ^ Multiplicative.toAdd n
  map_one' := by simp
  map_mul' a b := by
    change D.unif ^ (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      D.unif ^ Multiplicative.toAdd a * D.unif ^ Multiplicative.toAdd b
    rw [zpow_add]

/-- The valuation of a residue datum is onto: a power of its uniformizer realizes every integer. -/
theorem residueDataValuation_surjective : Function.Surjective D.val := by
  intro n
  refine ⟨residueDataValuationSection D n, ?_⟩
  apply Multiplicative.toAdd.injective
  change D.toTameData.v (D.unif ^ Multiplicative.toAdd n) = Multiplicative.toAdd n
  rw [D.toTameData.v_zpow]
  change Multiplicative.toAdd n * D.val' D.unif = Multiplicative.toAdd n
  rw [D.val'_unif, mul_one]

/-- The uniformizer section is a right inverse to the valuation. -/
theorem residueDataValuationSection_rightInverse :
    Function.RightInverse (residueDataValuationSection D) D.val := by
  intro n
  apply Multiplicative.toAdd.injective
  change D.toTameData.v (D.unif ^ Multiplicative.toAdd n) = Multiplicative.toAdd n
  rw [D.toTameData.v_zpow]
  change Multiplicative.toAdd n * D.val' D.unif = Multiplicative.toAdd n
  rw [D.val'_unif, mul_one]

/-- Exactness of valuation-zero units, field units, and the additive transport of the value group.
The target is transported to an additive group solely because `Function.Exact` is additive. -/
theorem residueDataValuation_exact : Function.Exact
    (MonoidHom.toAdditive D.val.ker.subtype) (MonoidHom.toAdditive D.val) := by
  intro a
  change D.val a.toMul = 1 ↔ ∃ b : Additive D.val.ker, b.toMul.val = a.toMul
  constructor
  · intro h
    exact ⟨Additive.ofMul ⟨a.toMul, h⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.toMul.property

/-- The first-isomorphism description of the valuation sequence: field units modulo valuation-zero
units are the integer value group. -/
noncomputable def residueDataQuotientKerValuationEquiv :
    Kˣ ⧸ D.val.ker ≃* Multiplicative ℤ :=
  QuotientGroup.quotientKerEquivOfSurjective D.val (residueDataValuation_surjective D)

/-! ## Finite places of Dedekind domains -/

open IsDedekindDomain

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable (L : Type v) [Field L] [Algebra R L] [IsFractionRing R L]

/-- At every finite Dedekind place, powers of the chosen uniformizer realize all valuation values. -/
theorem finitePlaceValuation_surjective (p : HeightOneSpectrum R) :
    Function.Surjective (residueDataAtPlace L p).val :=
  residueDataValuation_surjective _

/-- The valuation-zero units give the exact kernel at every finite Dedekind place. -/
theorem finitePlaceValuation_exact (p : HeightOneSpectrum R) : Function.Exact
    (MonoidHom.toAdditive (residueDataAtPlace L p).val.ker.subtype)
    (MonoidHom.toAdditive (residueDataAtPlace L p).val) :=
  residueDataValuation_exact _

/-- At a finite Dedekind place, field units modulo valuation-zero units are the integer value
group. -/
noncomputable def finitePlaceQuotientKerValuationEquiv (p : HeightOneSpectrum R) :
    Lˣ ⧸ (residueDataAtPlace L p).val.ker ≃* Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

end GaloisForLFunctions.HTGeometry.ABHN
