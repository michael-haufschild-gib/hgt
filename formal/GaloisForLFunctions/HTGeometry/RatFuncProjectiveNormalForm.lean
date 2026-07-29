import GaloisForLFunctions.HTGeometry.RatFuncAffineNormalForm
import GaloisForLFunctions.HTGeometry.RatFuncMobiusEquiv
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Projective cyclic normal form on a rational coordinate

Over an algebraically closed coefficient field, every nondegenerate Möbius automorphism becomes
affine after one explicit change of rational coordinate.  Together with the affine normal-form
leaf, this is the projective parent needed by the complete scalar persistent-gauge theorem.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- The Möbius coordinate change sending a finite point `r` to infinity. -/
def ratFuncFixedPointToInfinityEquiv (r : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  RatFunc.mobiusEquiv 0 1 1 (-r) (by simp)

/-- The inverse coordinate change, `X ↦ r + 1/X`. -/
def ratFuncInfinityToFixedPointEquiv (r : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  RatFunc.mobiusEquiv r 1 1 0 (by simp)

@[simp]
theorem ratFuncFixedPointToInfinityEquiv_X (r : K) :
    ratFuncFixedPointToInfinityEquiv r RatFunc.X =
      1 / (RatFunc.X - algebraMap K (RatFunc K) r) := by
  rw [ratFuncFixedPointToInfinityEquiv, RatFunc.mobiusEquiv_X]
  simp [RatFunc.mobius, sub_eq_add_neg]

@[simp]
theorem ratFuncInfinityToFixedPointEquiv_X (r : K) :
    ratFuncInfinityToFixedPointEquiv r RatFunc.X =
      algebraMap K (RatFunc K) r + 1 / RatFunc.X := by
  rw [ratFuncInfinityToFixedPointEquiv, RatFunc.mobiusEquiv_X]
  simp only [RatFunc.mobius, map_zero, add_zero, map_one, one_mul]
  field_simp [RatFunc.X_ne_zero]

/-- The two explicit fixed-point coordinate changes are inverse automorphisms. -/
theorem ratFuncFixedPointToInfinityEquiv_mul_inverse (r : K) :
    ratFuncFixedPointToInfinityEquiv r *
        ratFuncInfinityToFixedPointEquiv r = 1 := by
  apply RatFunc.algEquiv_ext_X
  change ratFuncFixedPointToInfinityEquiv r
      (ratFuncInfinityToFixedPointEquiv r RatFunc.X) = RatFunc.X
  rw [ratFuncInfinityToFixedPointEquiv_X, map_add, AlgEquiv.commutes,
    map_div₀, map_one, ratFuncFixedPointToInfinityEquiv_X]
  field_simp [RatFunc.X_ne_zero]
  ring

/-- The inverse of the fixed-point-to-infinity coordinate change is the explicit inverse map. -/
theorem ratFuncFixedPointToInfinityEquiv_symm (r : K) :
    (ratFuncFixedPointToInfinityEquiv r).symm =
      ratFuncInfinityToFixedPointEquiv r := by
  have h := eq_inv_of_mul_eq_one_right
    (ratFuncFixedPointToInfinityEquiv_mul_inverse r)
  calc
    (ratFuncFixedPointToInfinityEquiv r).symm =
        (ratFuncFixedPointToInfinityEquiv r)⁻¹ :=
      (AlgEquiv.aut_inv _).symm
    _ = ratFuncInfinityToFixedPointEquiv r := h.symm

/-- A fractional-linear coefficient tuple with nonzero lower-left entry has a finite fixed point
over an algebraically closed field. -/
theorem exists_mobius_fixedPoint_of_c_ne_zero
    [IsAlgClosed K] {a b c d : K}
    (hc : c ≠ 0) :
    ∃ r : K, a * r + b = r * (c * r + d) := by
  let p : K[X] := C c * X ^ 2 + C (d - a) * X - C b
  have hpdegree : p.degree ≠ 0 := by
    intro hp
    have hpC := Polynomial.eq_C_of_degree_eq_zero hp
    have hcoeff := congrArg (fun q : K[X] => q.coeff 2) hpC
    apply hc
    simpa [p] using hcoeff
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hpdegree
  refine ⟨r, ?_⟩
  rw [Polynomial.IsRoot.def] at hr
  dsimp [p] at hr
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow] at hr
  linear_combination -hr

/-- If the lower-left coefficient vanishes, the Möbius automorphism is already affine. -/
theorem mobiusEquiv_eq_affine_of_c_eq_zero
    {a b c d : K} (hdet : a * d - b * c ≠ 0) (hc : c = 0) :
    ∃ (u : Kˣ) (β : K),
      RatFunc.mobiusEquiv a b c d hdet = ratFuncAffineEquiv u β := by
  subst c
  have ha : a ≠ 0 := by
    intro ha
    apply hdet
    simp [ha]
  have hd : d ≠ 0 := by
    intro hd
    apply hdet
    simp [hd]
  let u : Kˣ := Units.mk0 (a / d) (div_ne_zero ha hd)
  let β : K := b / d
  refine ⟨u, β, ?_⟩
  apply RatFunc.algEquiv_ext_X
  rw [RatFunc.mobiusEquiv_X, ratFuncAffineEquiv_X]
  dsimp [u, β]
  simp only [RatFunc.mobius, zero_mul, map_zero, zero_add]
  rw [map_div₀, map_div₀]
  field_simp [hd]
  change (RatFunc.C a * RatFunc.X + RatFunc.C b) * RatFunc.C d =
    RatFunc.C d * (RatFunc.X * RatFunc.C a + RatFunc.C b)
  ring

/-- Conjugating a Möbius automorphism by a finite fixed-point chart makes its lower-left
coefficient vanish and hence produces an explicit affine automorphism. -/
theorem exists_conjugate_affine_of_c_ne_zero
    [IsAlgClosed K] {a b c d : K}
    (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0) :
    ∃ (r : K) (u : Kˣ) (β : K),
      (ratFuncFixedPointToInfinityEquiv r).symm *
          RatFunc.mobiusEquiv a b c d hdet *
            ratFuncFixedPointToInfinityEquiv r =
        ratFuncAffineEquiv u β := by
  obtain ⟨r, hr⟩ := exists_mobius_fixedPoint_of_c_ne_zero
    (a := a) (b := b) (d := d) hc
  have hprod :
      (c * r + d) * (a - r * c) = a * d - b * c := by
    linear_combination c * hr
  have htop : c * r + d ≠ 0 := by
    intro h
    apply hdet
    rw [← hprod, h]
    simp
  have hbot : a - r * c ≠ 0 := by
    intro h
    apply hdet
    rw [← hprod, h]
    simp
  let u : Kˣ := Units.mk0 ((c * r + d) / (a - r * c))
    (div_ne_zero htop hbot)
  let β : K := c / (a - r * c)
  refine ⟨r, u, β, ?_⟩
  rw [ratFuncFixedPointToInfinityEquiv_symm]
  rw [ratFuncInfinityToFixedPointEquiv,
    ratFuncFixedPointToInfinityEquiv]
  rw [RatFunc.mobiusEquiv_mul, RatFunc.mobiusEquiv_mul]
  apply RatFunc.algEquiv_ext_X
  rw [RatFunc.mobiusEquiv_X, ratFuncAffineEquiv_X]
  have hzero : a * r + b - r * (c * r + d) = 0 := sub_eq_zero.mpr hr
  have hzeroAdd : a * r + b + -(r * (c * r + d)) = 0 := by
    simpa [sub_eq_add_neg] using hzero
  simp only [zero_mul, one_mul, mul_one, mul_zero, add_zero, zero_add,
    neg_mul, RatFunc.mobius]
  rw [hzeroAdd]
  simp only [map_zero, zero_mul, zero_add]
  rw [← sub_eq_add_neg]
  dsimp [u, β]
  rw [map_div₀, map_div₀]
  have hbot' : -(c * r) + a ≠ 0 := by
    simpa [sub_eq_add_neg, mul_comm, add_comm] using hbot
  have hbotMap : RatFunc.C (-(c * r) + a) ≠ 0 :=
    (_root_.map_ne_zero RatFunc.C).2 hbot'
  field_simp [hbot, hbot', hbotMap]

/-- Every nondegenerate Möbius automorphism over an algebraically closed field is conjugate to an
affine automorphism. -/
theorem exists_mobiusEquiv_conjugate_affine
    [IsAlgClosed K] {a b c d : K}
    (hdet : a * d - b * c ≠ 0) :
    ∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ) (β : K),
      h.symm * RatFunc.mobiusEquiv a b c d hdet * h =
        ratFuncAffineEquiv u β := by
  by_cases hc : c = 0
  · obtain ⟨u, β, heq⟩ := mobiusEquiv_eq_affine_of_c_eq_zero hdet hc
    refine ⟨AlgEquiv.refl, u, β, ?_⟩
    rw [AlgEquiv.refl_symm]
    have hrefl :
        (AlgEquiv.refl : RatFunc K ≃ₐ[K] RatFunc K) =
          (1 : RatFunc K ≃ₐ[K] RatFunc K) := rfl
    rw [hrefl, one_mul, mul_one]
    exact heq
  · obtain ⟨r, u, β, heq⟩ :=
      exists_conjugate_affine_of_c_ne_zero hdet hc
    exact ⟨ratFuncFixedPointToInfinityEquiv r, u, β, heq⟩

/-- The inverse of translation by `r` is translation by `-r`. -/
theorem ratFuncTranslationEquiv_symm (r : K) :
    (ratFuncTranslationEquiv r).symm = ratFuncTranslationEquiv (-r) := by
  have hmul :
      ratFuncTranslationEquiv (-r) * ratFuncTranslationEquiv r = 1 := by
    apply RatFunc.algEquiv_ext_X
    change ratFuncTranslationEquiv (-r)
      (ratFuncTranslationEquiv r RatFunc.X) = RatFunc.X
    rw [ratFuncTranslationEquiv_X, map_add,
      ratFuncTranslationEquiv_X, AlgEquiv.commutes]
    push_cast
    ring
  have h := eq_inv_of_mul_eq_one_left hmul
  calc
    (ratFuncTranslationEquiv r).symm =
        (ratFuncTranslationEquiv r)⁻¹ :=
      (AlgEquiv.aut_inv _).symm
    _ = ratFuncTranslationEquiv (-r) := h.symm

private theorem ratFunc_conjugate_mul
    (h k e a n : RatFunc K ≃ₐ[K] RatFunc K)
    (he : h.symm * e * h = a)
    (hk : k.symm * a * k = n) :
    (h * k).symm * e * (h * k) = n := by
  calc
    (h * k).symm * e * (h * k) =
        k.symm * (h.symm * e * h) * k := by
          change (h * k)⁻¹ * e * (h * k) =
            k⁻¹ * (h⁻¹ * e * h) * k
          group
    _ = k.symm * a * k := by rw [he]
    _ = n := hk

/-- Every nonidentity Möbius automorphism over an algebraically closed field is conjugate either
to a pure scaling or to unit translation. -/
theorem mobiusEquiv_normalForm
    [IsAlgClosed K] {a b c d : K} (hdet : a * d - b * c ≠ 0)
    (hne : RatFunc.mobiusEquiv a b c d hdet ≠ AlgEquiv.refl) :
    (∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ),
        h.symm * RatFunc.mobiusEquiv a b c d hdet * h =
          ratFuncUnitScaleEquiv u) ∨
      (∃ h : RatFunc K ≃ₐ[K] RatFunc K,
        h.symm * RatFunc.mobiusEquiv a b c d hdet * h =
          ratFuncTranslationEquiv 1) := by
  let e := RatFunc.mobiusEquiv a b c d hdet
  obtain ⟨h, u, β, he⟩ := exists_mobiusEquiv_conjugate_affine hdet
  have haffine : ratFuncAffineEquiv u β ≠ AlgEquiv.refl := by
    intro ha
    apply hne
    change e = AlgEquiv.refl
    calc
      e = h * (h.symm * e * h) * h.symm := by
        change e = h * (h⁻¹ * e * h) * h⁻¹
        group
      _ = h * ratFuncAffineEquiv u β * h.symm := by rw [he]
      _ = h * AlgEquiv.refl * h.symm := by rw [ha]
      _ = AlgEquiv.refl := by
        change h * 1 * h⁻¹ = 1
        group
  rcases ratFuncAffineEquiv_normalForm u β haffine with hscale | htrans
  · left
    obtain ⟨r, hr⟩ := hscale
    let k := ratFuncTranslationEquiv r
    refine ⟨h * k, u, ?_⟩
    have hk : k.symm * ratFuncAffineEquiv u β * k =
        ratFuncUnitScaleEquiv u := by
      dsimp [k]
      rw [ratFuncTranslationEquiv_symm]
      exact hr
    exact ratFunc_conjugate_mul h k e
      (ratFuncAffineEquiv u β) (ratFuncUnitScaleEquiv u) he hk
  · right
    obtain ⟨v, hv⟩ := htrans
    let k := (ratFuncUnitScaleEquiv v).symm
    refine ⟨h * k, ?_⟩
    have hk : k.symm * ratFuncAffineEquiv u β * k =
        ratFuncTranslationEquiv 1 := by
      have hscale :
          (ratFuncUnitScaleEquiv v).symm =
            ratFuncUnitScaleEquiv v⁻¹ := by
        calc
          (ratFuncUnitScaleEquiv v).symm =
              (ratFuncUnitScaleEquiv v)⁻¹ :=
            (AlgEquiv.aut_inv _).symm
          _ = ratFuncUnitScaleEquiv v⁻¹ :=
            (map_inv ratFuncUnitScaleAction v).symm
      dsimp only [k]
      rw [AlgEquiv.symm_symm, hscale]
      exact hv
    exact ratFunc_conjugate_mul h k e
      (ratFuncAffineEquiv u β) (ratFuncTranslationEquiv 1) he hk

/-- Every nonidentity coefficient-fixing automorphism of `K(X)` over an algebraically closed
field has the scaling-or-unit-translation projective normal form. -/
theorem ratFuncAlgEquiv_normalForm
    [IsAlgClosed K] (e : RatFunc K ≃ₐ[K] RatFunc K)
    (hne : e ≠ AlgEquiv.refl) :
    (∃ (h : RatFunc K ≃ₐ[K] RatFunc K) (u : Kˣ),
        h.symm * e * h = ratFuncUnitScaleEquiv u) ∨
      (∃ h : RatFunc K ≃ₐ[K] RatFunc K,
        h.symm * e * h = ratFuncTranslationEquiv 1) := by
  obtain ⟨a, b, c, d, hdet, hX⟩ := RatFunc.exists_mobius_image_X e
  have he : e = RatFunc.mobiusEquiv a b c d hdet := by
    apply RatFunc.algEquiv_ext_X
    rw [RatFunc.mobiusEquiv_X]
    exact hX
  subst e
  exact mobiusEquiv_normalForm hdet hne

end

end GaloisForLFunctions.HTGeometry
