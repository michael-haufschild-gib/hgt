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

/-- Two coefficient-fixing automorphisms of `K(X)` agree when they agree on `X`. -/
theorem algEquiv_ext_X
    {f g : RatFunc K ≃ₐ[K] RatFunc K}
    (hX : f X = g X) : f = g := by
  apply AlgEquiv.ext
  intro z
  have hring : f.toRingEquiv.toRingHom = g.toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    have hpoly :
        f.toRingEquiv.toRingHom.comp (algebraMap K[X] (RatFunc K)) =
          g.toRingEquiv.toRingHom.comp (algebraMap K[X] (RatFunc K)) := by
      apply Polynomial.ringHom_ext
      · intro k
        change f (algebraMap K (RatFunc K) k) =
          g (algebraMap K (RatFunc K) k)
        rw [f.commutes, g.commutes]
      · simpa [RatFunc.algebraMap_X] using hX
    exact DFunLike.congr_fun hpoly p
  exact DFunLike.congr_fun hring z

/-- The denominator appearing when the inverse Möbius coordinate is solved for `X`. -/
theorem mobius_inverse_denominator_eq
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    algebraMap K (RatFunc K) a -
        algebraMap K (RatFunc K) c * mobius a b c d =
      algebraMap K (RatFunc K) (a * d - b * c) /
        (algebraMap K (RatFunc K) c * X +
          algebraMap K (RatFunc K) d) := by
  have hden := mobius_den_ne_zero hdet
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
    (mobius_den_ne_zero hdet)

/-- Solving a nondegenerate Möbius coordinate for the original rational coordinate. -/
theorem mobius_inverse_formula
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    (algebraMap K (RatFunc K) d * mobius a b c d -
        algebraMap K (RatFunc K) b) /
      (algebraMap K (RatFunc K) a -
        algebraMap K (RatFunc K) c * mobius a b c d) = X := by
  have hden := mobius_den_ne_zero hdet
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
  have hden := mobius_den_ne_zero hdet
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

/-- Möbius automorphisms compose by matrix multiplication, with the matrix order dictated by
substitution: the right matrix multiplies the left matrix. -/
theorem mobiusEquiv_mul
    (a b c d A B C D : K)
    (hdet : a * d - b * c ≠ 0)
    (hDET : A * D - B * C ≠ 0) :
    mobiusEquiv a b c d hdet * mobiusEquiv A B C D hDET =
      mobiusEquiv
        (A * a + B * c) (A * b + B * d)
        (C * a + D * c) (C * b + D * d)
        (by
          have hfactor :
              (A * a + B * c) * (C * b + D * d) -
                  (A * b + B * d) * (C * a + D * c) =
                (A * D - B * C) * (a * d - b * c) := by
            ring
          rw [hfactor]
          exact mul_ne_zero hDET hdet) := by
  apply algEquiv_ext_X
  change mobiusEquiv a b c d hdet
      (mobiusEquiv A B C D hDET X) = _
  rw [mobiusEquiv_X, mobiusEquiv_X]
  rw [mobius]
  simp only [map_div₀, map_add, map_mul, AlgEquiv.commutes,
    mobiusEquiv_X]
  rw [mobius]
  have hden := mobius_den_ne_zero hdet
  have hres :
      (A * a + B * c) * (C * b + D * d) -
          (A * b + B * d) * (C * a + D * c) ≠ 0 := by
    have hfactor :
        (A * a + B * c) * (C * b + D * d) -
            (A * b + B * d) * (C * a + D * c) =
          (A * D - B * C) * (a * d - b * c) := by
      ring
    rw [hfactor]
    exact mul_ne_zero hDET hdet
  have hinner :
      algebraMap K (RatFunc K) C * mobius a b c d +
          algebraMap K (RatFunc K) D ≠ 0 := by
    have hsource := mobius_den_ne_zero hDET
    have hmapped := (map_ne_zero (mobiusEquiv a b c d hdet)).2 hsource
    change mobiusEquiv a b c d hdet
      (algebraMap K (RatFunc K) C * X +
        algebraMap K (RatFunc K) D) ≠ 0 at hmapped
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
      mobiusEquiv_X] at hmapped
    exact hmapped
  have hresden :
      algebraMap K (RatFunc K) (C * a + D * c) * X +
          algebraMap K (RatFunc K) (C * b + D * d) ≠ 0 :=
    mobius_den_ne_zero hres
  rw [mobius]
  apply (div_eq_div_iff hinner hresden).2
  rw [mobius]
  have hden' :
      X * algebraMap K (RatFunc K) c +
          algebraMap K (RatFunc K) d ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hden, hden']
  push_cast
  ring

end RatFunc

end
