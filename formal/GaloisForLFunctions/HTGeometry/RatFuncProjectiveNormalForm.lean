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
  simpa using h.symm

/-- A nondegenerate Möbius matrix with nonzero lower-left entry has a finite fixed point over an
algebraically closed field. -/
theorem exists_mobius_fixedPoint_of_c_ne_zero
    [IsAlgClosed K] {a b c d : K}
    (_hdet : a * d - b * c ≠ 0) (hc : c ≠ 0) :
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
  obtain ⟨r, hr⟩ := exists_mobius_fixedPoint_of_c_ne_zero hdet hc
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
    simpa using heq
  · obtain ⟨r, u, β, heq⟩ :=
      exists_conjugate_affine_of_c_ne_zero hdet hc
    exact ⟨ratFuncFixedPointToInfinityEquiv r, u, β, heq⟩

end

end GaloisForLFunctions.HTGeometry
