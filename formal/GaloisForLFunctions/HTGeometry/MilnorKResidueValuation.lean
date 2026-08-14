import GaloisForLFunctions.HTGeometry.MilnorKResidueMap
import GaloisForLFunctions.HTGeometry.MilnorKTameDedekind

/-!
# The residue data of a valuation, and of a finite place

The residue homomorphism of Milnor `K`-theory needs, beyond the tame symbol data, a uniformizer and
the additivity of the residue map on `1 - a`.  The second is automatic: the residue map of a
valuation is induced by the quotient map of the valuation ring onto its residue field, which is a
ring homomorphism.  The first is a choice, and at a finite place of a Dedekind domain such a choice
exists because the adic valuation is surjective onto the integers.

* `residueDataOfValuation` : **the residue data of an integer-valued valuation with a chosen
  uniformizer.**
* `placeUniformizer` : a uniformizer at a finite place.
* `residueDataAtPlace` : **the residue data at a finite place of a Dedekind domain**, whose tame
  symbol data is the one already used for the tame kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open Valuation IsLocalRing IsDedekindDomain

section OfValuation

variable {K : Type*} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))

/-- **The residue data of an integer-valued valuation with a chosen uniformizer.** -/
noncomputable def residueDataOfValuation (π : Kˣ)
    (hπ : Multiplicative.toAdd (tameValHom v π) = 1) :
    ResidueData K (ResidueField v.valuationSubring) where
  toTameData := tameDataOfValuation v
  unif := π
  v_unif := hπ
  oneSub_res := by
    intro a ha h h'
    show ((tameResHom v ⟨oneSubUnit ha, h'⟩ : (ResidueField v.valuationSubring)ˣ) :
        ResidueField v.valuationSubring)
      = 1 - ((tameResHom v ⟨a, h⟩ : (ResidueField v.valuationSubring)ˣ) :
        ResidueField v.valuationSubring)
    rw [tameResHom_val, tameResHom_val]
    have hsub : (⟨((oneSubUnit ha : Kˣ) : K), tame_mem_valuationSubring v h'⟩ :
        v.valuationSubring)
        = 1 - ⟨(a : K), tame_mem_valuationSubring v h⟩ := Subtype.ext rfl
    rw [hsub, _root_.map_sub, map_one]

end OfValuation

section AtPlace

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A chosen uniformizer at a finite place. -/
noncomputable def placeUniformizer (v : HeightOneSpectrum R) : K :=
  (v.valuation_exists_uniformizer K).choose

theorem placeUniformizer_valuation (v : HeightOneSpectrum R) :
    v.valuation K (placeUniformizer K v) = WithZero.exp (-1 : ℤ) :=
  (v.valuation_exists_uniformizer K).choose_spec

theorem placeUniformizer_ne_zero (v : HeightOneSpectrum R) : placeUniformizer K v ≠ 0 := by
  intro h
  have hval := placeUniformizer_valuation K v
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- A chosen uniformizer at a finite place, as a unit. -/
noncomputable def placeUniformizerUnit (v : HeightOneSpectrum R) : Kˣ :=
  Units.mk0 (placeUniformizer K v) (placeUniformizer_ne_zero K v)

theorem placeUniformizer_tameVal (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (tameValHom (v.valuation K) (placeUniformizerUnit K v)) = 1 := by
  have hcoe : ((tameUnzero (v.valuation K) (placeUniformizerUnit K v) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact placeUniformizer_valuation K v
  have hun : tameUnzero (v.valuation K) (placeUniformizerUnit K v)
      = Multiplicative.ofAdd (-1 : ℤ) := WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- **The residue data at a finite place of a Dedekind domain.** -/
noncomputable def residueDataAtPlace (v : HeightOneSpectrum R) :
    ResidueData K (ResidueField (v.valuation K).valuationSubring) :=
  residueDataOfValuation (v.valuation K) (placeUniformizerUnit K v)
    (placeUniformizer_tameVal K v)

@[simp]
theorem residueDataAtPlace_toTameData (v : HeightOneSpectrum R) :
    (residueDataAtPlace K v).toTameData = tameDataAtPlace K v := rfl

end AtPlace

end GaloisForLFunctions.HTGeometry
