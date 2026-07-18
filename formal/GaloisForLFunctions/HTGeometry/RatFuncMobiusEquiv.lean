import GaloisForLFunctions.HTGeometry.RatFuncProjectiveAutomorphism

/-!
# Möbius automorphisms of a rational function field

This module constructs the coefficient-fixing automorphism of `K(X)` represented by every
determinant-nonzero two-by-two matrix.  The inverse-coordinate identity is proved directly, then
used to show that the Möbius coordinate is transcendental and generates the whole rational
function field.
-/

open IntermediateField Polynomial

noncomputable section

namespace RatFunc

variable {K : Type*} [Field K]

/-- A nondegenerate Möbius denominator is a nonzero rational function. -/
theorem mobius_denominator_ne_zero
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    algebraMap K (RatFunc K) c * X + algebraMap K (RatFunc K) d ≠ 0 := by
  have hpoly : Polynomial.C c * Polynomial.X + Polynomial.C d ≠ 0 := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        intro hd
        apply hdet
        simp [hc, hd]
      simpa [hc] using Polynomial.C_ne_zero.mpr hd
    · intro h
      apply hc
      have hcoeff := congrArg (fun p : K[X] => p.coeff 1) h
      simpa using hcoeff
  simpa using RatFunc.algebraMap_ne_zero hpoly

/-- The denominator appearing when the inverse Möbius coordinate is solved for `X`. -/
theorem mobius_inverse_denominator_eq
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    algebraMap K (RatFunc K) a -
        algebraMap K (RatFunc K) c * mobius a b c d =
      algebraMap K (RatFunc K) (a * d - b * c) /
        (algebraMap K (RatFunc K) c * X +
          algebraMap K (RatFunc K) d) := by
  have hden := mobius_denominator_ne_zero hdet
  rw [mobius]
  apply (eq_div_iff hden).2
  rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hden]
  push_cast
  ring

/-- The inverse Möbius denominator is nonzero. -/
theorem mobius_inverse_denominator_ne_zero
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    algebraMap K (RatFunc K) a -
        algebraMap K (RatFunc K) c * mobius a b c d ≠ 0 := by
  rw [mobius_inverse_denominator_eq hdet]
  exact div_ne_zero
    ((map_ne_zero (algebraMap K (RatFunc K))).2 hdet)
    (mobius_denominator_ne_zero hdet)

/-- Solving a nondegenerate Möbius coordinate for the original rational coordinate. -/
theorem mobius_inverse_formula
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    (algebraMap K (RatFunc K) d * mobius a b c d -
        algebraMap K (RatFunc K) b) /
      (algebraMap K (RatFunc K) a -
        algebraMap K (RatFunc K) c * mobius a b c d) = X := by
  have hden := mobius_denominator_ne_zero hdet
  have hinv := mobius_inverse_denominator_ne_zero hdet
  apply (div_eq_iff hinv).2
  rw [mobius_inverse_denominator_eq hdet]
  rw [mobius]
  have hright :
      X * (algebraMap K (RatFunc K) (a * d - b * c) /
          (algebraMap K (RatFunc K) c * X +
            algebraMap K (RatFunc K) d)) =
        (X * algebraMap K (RatFunc K) (a * d - b * c)) /
          (algebraMap K (RatFunc K) c * X +
            algebraMap K (RatFunc K) d) := by
    exact mul_div_assoc' _ _ _
  rw [hright]
  apply (eq_div_iff hden).2
  rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hden]
  push_cast
  ring

/-- A determinant-nonzero Möbius coordinate is not constant. -/
theorem mobius_ne_C
    {a b c d : K} (hdet : a * d - b * c ≠ 0) (k : K) :
    mobius a b c d ≠ C k := by
  intro h
  have hden := mobius_denominator_ne_zero hdet
  have hcross :
      algebraMap K (RatFunc K) a * X + algebraMap K (RatFunc K) b =
        algebraMap K (RatFunc K) k *
          (algebraMap K (RatFunc K) c * X +
            algebraMap K (RatFunc K) d) := by
    apply (div_eq_iff hden).mp
    simpa [mobius] using h
  have hpoly :
      Polynomial.C a * Polynomial.X + Polynomial.C b =
        Polynomial.C k *
          (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
    apply RatFunc.algebraMap_injective
    simpa using hcross
  have ha : a = k * c := by
    have hcoeff := congrArg (fun p : K[X] => p.coeff 1) hpoly
    simpa using hcoeff
  have hb : b = k * d := by
    have hcoeff := congrArg (fun p : K[X] => p.coeff 0) hpoly
    simpa using hcoeff
  apply hdet
  rw [ha, hb]
  ring

/-- A determinant-nonzero Möbius coordinate is transcendental over its coefficient field. -/
theorem mobius_transcendental
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    Transcendental K (mobius a b c d) :=
  (mobius a b c d).transcendental_of_ne_C
    (by simpa only [not_exists] using mobius_ne_C hdet)

/-- A determinant-nonzero Möbius coordinate generates the whole rational function field. -/
theorem adjoin_mobius_eq_top
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    K⟮mobius a b c d⟯ = ⊤ := by
  let f : RatFunc K := mobius a b c d
  let L : IntermediateField K (RatFunc K) := K⟮f⟯
  have hf : f ∈ L := by
    exact IntermediateField.subset_adjoin K ({f} : Set (RatFunc K))
      (Set.mem_singleton f)
  have hX : (X : RatFunc K) ∈ L := by
    rw [← mobius_inverse_formula hdet]
    exact L.div_mem
      (L.sub_mem (L.mul_mem (L.algebraMap_mem d) hf) (L.algebraMap_mem b))
      (L.sub_mem (L.algebraMap_mem a)
        (L.mul_mem (L.algebraMap_mem c) hf))
  apply top_unique
  rw [← RatFunc.adjoin_X]
  exact IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hX)

/-- The coefficient-fixing automorphism represented by a nondegenerate Möbius matrix. -/
def mobiusEquiv (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    RatFunc K ≃ₐ[K] RatFunc K :=
  (RatFunc.algEquivOfTranscendental (mobius a b c d)
      (mobius_transcendental hdet)).trans
    ((IntermediateField.equivOfEq (adjoin_mobius_eq_top hdet)).trans
      IntermediateField.topEquiv)

@[simp]
theorem mobiusEquiv_X
    (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    mobiusEquiv a b c d hdet X = mobius a b c d := by
  simp [mobiusEquiv, RatFunc.algEquivOfTranscendental_X]

end RatFunc

end
