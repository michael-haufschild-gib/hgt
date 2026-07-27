import GaloisForLFunctions.RHTower.FieldOneFiniteStageHaarScaling
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Quotient

/-!
# Haar measure and the regular L² representation on finite-stage idele classes

For a finite set `S` of rational finite places, this file equips

`C_S = GL₁(A_S) / ℤ_Sˣ`

with its own left Haar measure and constructs the unitary left-regular
representation on `L²(C_S)`.  The construction uses only the quotient-group
topology and left invariance of Haar measure.

This is deliberately distinct from pushing additive Haar measure on `A_S`
through the orbit map `A_S → ℤ_Sˣ \ A_S`: such a pushforward need not be the
semilocal quotient measure.  No fundamental domain, Radon--Nikodym
normalization, full-measure comparison
`L²(ℤ_Sˣ \ A_S) ≃ L²(C_S)`, trace formula, or positivity theorem is asserted
here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory
open MeasureTheory.Measure

/-! ### Borel and Haar structures -/

/-- Units of the real place inherit second countability from `ℝ`. -/
noncomputable instance fieldOneRealUnitsSecondCountableTopology :
    SecondCountableTopology ℝˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- Units of every rational finite-place completion inherit second
countability from the completion. -/
noncomputable instance fieldOneAdicUnitsSecondCountableTopology
    (v : HeightOneSpectrum ℤ) :
    SecondCountableTopology (v.adicCompletion ℚ)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- The finite-stage idele-class group carries its Borel measurable space. -/
noncomputable instance fieldOneFiniteStageIdeleClassMeasurableSpace
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurableSpace (FieldOneFiniteStageIdeleClassGroup S) :=
  borel (FieldOneFiniteStageIdeleClassGroup S)

noncomputable instance fieldOneFiniteStageIdeleClassBorelSpace
    (S : Finset (HeightOneSpectrum ℤ)) :
    BorelSpace (FieldOneFiniteStageIdeleClassGroup S) :=
  ⟨rfl⟩

/-- Canonical left Haar measure on the finite-stage idele-class group.

This is an abbreviation so that mathlib's `IsHaarMeasure haar` instance
remains visible to typeclass inference. -/
noncomputable abbrev fieldOneFiniteStageIdeleClassHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdeleClassGroup S) :=
  haar

/-- The chosen measure is a nonzero regular left Haar measure. -/
theorem fieldOneFiniteStageIdeleClassHaar_isHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (fieldOneFiniteStageIdeleClassHaarMeasure S) :=
  inferInstance

/-- Complex `L²` on the finite-stage idele-class group. -/
abbrev FieldOneFiniteStageIdeleClassL2
    (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp (α := FieldOneFiniteStageIdeleClassGroup S)
    ℂ 2 (fieldOneFiniteStageIdeleClassHaarMeasure S)

/-! ### Left-regular unitary representation -/

/-- Left translation by `c` on functions, in the convention
`(λ(c)f)(x) = f(c⁻¹x)`, is unitary on `L²(C_S)`. -/
def fieldOneFiniteStageIdeleClassLeftRegular
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) :
    FieldOneFiniteStageIdeleClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageIdeleClassL2 S where
  __ :=
    Lp.compMeasurePreservingₗᵢ ℂ (c⁻¹ * ·)
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)
  invFun :=
    Lp.compMeasurePreserving (c * ·)
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c)
  left_inv f := by
    change
      Lp.compMeasurePreserving (c * ·)
          (measurePreserving_mul_left
            (fieldOneFiniteStageIdeleClassHaarMeasure S) c)
        (Lp.compMeasurePreserving (c⁻¹ * ·)
          (measurePreserving_mul_left
            (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c)]
    simp
    exact Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change
      Lp.compMeasurePreserving (c⁻¹ * ·)
          (measurePreserving_mul_left
            (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)
        (Lp.compMeasurePreserving (c * ·)
          (measurePreserving_mul_left
            (fieldOneFiniteStageIdeleClassHaarMeasure S) c) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c)
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)]
    simp
    exact Lp.compMeasurePreserving_id_apply f

@[simp]
theorem fieldOneFiniteStageIdeleClassLeftRegular_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S)
    (f : FieldOneFiniteStageIdeleClassL2 S) :
    fieldOneFiniteStageIdeleClassLeftRegular S c f =
      Lp.compMeasurePreserving (c⁻¹ * ·)
        (measurePreserving_mul_left
          (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹) f :=
  rfl

/-- The finite-stage idele-class group acts unitarily on its Haar `L²`
space by the left-regular representation. -/
def fieldOneFiniteStageIdeleClassLeftRegularRepresentation
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S →*
      (FieldOneFiniteStageIdeleClassL2 S ≃ₗᵢ[ℂ]
        FieldOneFiniteStageIdeleClassL2 S) where
  toFun := fieldOneFiniteStageIdeleClassLeftRegular S
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Lp.ext
    filter_upwards [
      Lp.coeFn_compMeasurePreserving f
        (measurePreserving_mul_left
          (fieldOneFiniteStageIdeleClassHaarMeasure S)
          (1 : FieldOneFiniteStageIdeleClassGroup S)⁻¹)
    ] with x hx
    simpa using hx
  map_mul' c d := by
    apply LinearIsometryEquiv.ext
    intro f
    change
      Lp.compMeasurePreserving ((c * d)⁻¹ * ·)
          (measurePreserving_mul_left
            (fieldOneFiniteStageIdeleClassHaarMeasure S) (c * d)⁻¹) f =
        Lp.compMeasurePreserving (c⁻¹ * ·)
            (measurePreserving_mul_left
              (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)
          (Lp.compMeasurePreserving (d⁻¹ * ·)
            (measurePreserving_mul_left
              (fieldOneFiniteStageIdeleClassHaarMeasure S) d⁻¹) f)
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) d⁻¹)
      (measurePreserving_mul_left
        (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)]
    congr 2
    funext x
    simp [mul_assoc]

/-- Concrete almost-everywhere formula for the regular action. -/
theorem fieldOneFiniteStageIdeleClassLeftRegular_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S)
    (f : FieldOneFiniteStageIdeleClassL2 S) :
    fieldOneFiniteStageIdeleClassLeftRegularRepresentation S c f
      =ᵐ[fieldOneFiniteStageIdeleClassHaarMeasure S]
        fun x => f (c⁻¹ * x) :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_mul_left
      (fieldOneFiniteStageIdeleClassHaarMeasure S) c⁻¹)

/-- Every regular translation preserves the `L²` norm. -/
@[simp]
theorem fieldOneFiniteStageIdeleClassLeftRegular_norm
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S)
    (f : FieldOneFiniteStageIdeleClassL2 S) :
    ‖fieldOneFiniteStageIdeleClassLeftRegularRepresentation S c f‖ = ‖f‖ :=
  (fieldOneFiniteStageIdeleClassLeftRegularRepresentation S c).norm_map f

end

end GaloisForLFunctions.RHTower
