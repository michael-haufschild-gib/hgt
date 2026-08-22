import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Coefficientwise automorphisms of Laurent series

An automorphism `φ` of the coefficient field extends coefficientwise to the power series ring and,
because it preserves the nonzero divisors, to the Laurent series field.  This is what turns the
block flip of a residue field into an automorphism of the field in which the deformed
characteristic polynomial splits, and hence into an element of a Galois group.

## Main results

* `psRingEquiv` — the coefficientwise automorphism of `PowerSeries L`.
* `laurentRingEquiv` — its extension to `LaurentSeries L`.
* `laurentRingEquiv_algebraMap` — the two agree on power series.
-/

open scoped nonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

variable {L : Type*} [Field L]

/-- A coefficientwise automorphism of the power series ring. -/
noncomputable def psRingEquiv (φ : L ≃+* L) : PowerSeries L ≃+* PowerSeries L where
  toFun := PowerSeries.map (φ : L →+* L)
  invFun := PowerSeries.map (φ.symm : L →+* L)
  left_inv := by
    intro f
    ext n
    simp [PowerSeries.coeff_map]
  right_inv := by
    intro f
    ext n
    simp [PowerSeries.coeff_map]
  map_mul' := by
    intro f g
    exact map_mul (PowerSeries.map (φ : L →+* L)) f g
  map_add' := by
    intro f g
    exact map_add (PowerSeries.map (φ : L →+* L)) f g

@[simp] theorem psRingEquiv_apply (φ : L ≃+* L) (f : PowerSeries L) :
    psRingEquiv φ f = PowerSeries.map (φ : L →+* L) f := rfl

/-- A ring automorphism of a domain preserves the nonzero divisors. -/
theorem map_nonZeroDivisors_of_ringEquiv {A : Type*} [CommRing A] [IsDomain A] (e : A ≃+* A) :
    Submonoid.map e.toMonoidHom A⁰ = A⁰ := by
  ext a
  simp only [Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · rintro ⟨b, hb, rfl⟩
    intro h
    exact hb ((EmbeddingLike.apply_eq_iff_eq e).mp (by simpa using h))
  · intro ha
    refine ⟨e.symm a, ?_, by simp⟩
    intro h
    exact ha (by rw [← e.apply_symm_apply a, h, map_zero])

/-- The extension of a coefficientwise automorphism to the Laurent series field. -/
noncomputable def laurentRingEquiv (φ : L ≃+* L) :
    LaurentSeries L ≃+* LaurentSeries L :=
  IsLocalization.ringEquivOfRingEquiv (M := (PowerSeries L)⁰) (LaurentSeries L)
    (LaurentSeries L) (psRingEquiv φ) (map_nonZeroDivisors_of_ringEquiv _)

@[simp] theorem laurentRingEquiv_algebraMap (φ : L ≃+* L) (f : PowerSeries L) :
    laurentRingEquiv φ (algebraMap (PowerSeries L) (LaurentSeries L) f)
      = algebraMap (PowerSeries L) (LaurentSeries L) (PowerSeries.map (φ : L →+* L) f) := by
  rw [laurentRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq]
  rfl

/-- **The extension fixes the coefficients coming from a subfield that `φ` fixes.**  If `ψ : E → L`
has image inside the fixed field of `φ`, then `laurentRingEquiv φ` fixes every Laurent series whose
coefficients come from `E` through `ψ`. -/
theorem laurentRingEquiv_fix_of_comp {E : Type*} [Field E] (φ : L ≃+* L) (ψ : E →+* L)
    (hψ : ∀ x : E, φ (ψ x) = ψ x) (g : PowerSeries E) :
    laurentRingEquiv φ
        (algebraMap (PowerSeries L) (LaurentSeries L) (PowerSeries.map ψ g))
      = algebraMap (PowerSeries L) (LaurentSeries L) (PowerSeries.map ψ g) := by
  rw [laurentRingEquiv_algebraMap]
  congr 1
  ext n
  simp [PowerSeries.coeff_map, hψ]

end GaloisForLFunctions.HTGeometry
