import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.GroupTheory.OrderOfElement

/-!
# Fixed fields of scalar actions on a rational coordinate

For a field `K` and a unit `u : Kˣ`, this file constructs the scalar automorphism
`X ↦ uX` of `K(X)` and computes the fixed field of the cyclic group it generates.

* If `u` has finite order `N > 0`, the fixed field is exactly `K(X^N)`.
* If `u` has infinite order, the fixed field is exactly `K`.

The proof avoids coefficient normal forms.  It combines the existing exact extension-degree
formula for `K(X) / K(f)` with the finite-group fixed-point dimension theorem.  In the
infinite-order case, a nonconstant fixed rational function would make the infinite cyclic group
embed in the finite automorphism group of `K(X) / K(f)`.
-/

open Polynomial IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Polynomial substitution `X ↦ uX` for a unit scalar `u`. -/
def polyUnitScaleHom {K : Type*} [Field K] (u : Kˣ) : K[X] →ₐ[K] K[X] :=
  aeval (C (u : K) * X)

@[simp]
theorem polyUnitScaleHom_X {K : Type*} [Field K] (u : Kˣ) :
    polyUnitScaleHom u X = C (u : K) * X := by
  simp [polyUnitScaleHom]

/-- Scalar polynomial substitutions compose according to multiplication of their unit scalars. -/
theorem polyUnitScaleHom_comp {K : Type*} [Field K] (u v : Kˣ) :
    (polyUnitScaleHom u).comp (polyUnitScaleHom v) = polyUnitScaleHom (u * v) := by
  apply Polynomial.algHom_ext
  simp [polyUnitScaleHom]
  ring

@[simp]
theorem polyUnitScaleHom_one {K : Type*} [Field K] :
    polyUnitScaleHom (1 : Kˣ) = AlgHom.id K K[X] := by
  apply Polynomial.algHom_ext
  simp [polyUnitScaleHom]

/-- The polynomial algebra automorphism `X ↦ uX`. -/
def polyUnitScaleEquiv {K : Type*} [Field K] (u : Kˣ) : K[X] ≃ₐ[K] K[X] :=
  AlgEquiv.ofAlgHom (polyUnitScaleHom u) (polyUnitScaleHom u⁻¹)
    (by rw [polyUnitScaleHom_comp]; simp)
    (by rw [polyUnitScaleHom_comp]; simp)

@[simp]
theorem polyUnitScaleEquiv_X {K : Type*} [Field K] (u : Kˣ) :
    polyUnitScaleEquiv u X = C (u : K) * X := by
  simp [polyUnitScaleEquiv]

/-- The scalar field automorphism `X ↦ uX` of `K(X)`. -/
def ratFuncUnitScaleEquiv {K : Type*} [Field K] (u : Kˣ) :
    RatFunc K ≃ₐ[K] RatFunc K :=
  IsLocalization.algEquivOfAlgEquiv (RatFunc K) (RatFunc K) (polyUnitScaleEquiv u)
    (MulEquivClass.map_nonZeroDivisors (polyUnitScaleEquiv u))

/-- Scalar substitution on a polynomial viewed inside `K(X)`. -/
theorem ratFuncUnitScaleEquiv_algebraMap {K : Type*} [Field K]
    (u : Kˣ) (p : K[X]) :
    ratFuncUnitScaleEquiv u (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (polyUnitScaleEquiv u p) := by
  rw [ratFuncUnitScaleEquiv, IsLocalization.algEquivOfAlgEquiv_eq]

@[simp]
theorem ratFuncUnitScaleEquiv_X {K : Type*} [Field K] (u : Kˣ) :
    ratFuncUnitScaleEquiv u RatFunc.X = algebraMap K (RatFunc K) (u : K) * RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratFuncUnitScaleEquiv_algebraMap, polyUnitScaleEquiv_X,
    map_mul, RatFunc.algebraMap_X, ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
theorem ratFuncUnitScaleEquiv_one {K : Type*} [Field K] :
    ratFuncUnitScaleEquiv (1 : Kˣ) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  have hring :
      (ratFuncUnitScaleEquiv (1 : Kˣ)).toRingEquiv.toRingHom =
        (AlgEquiv.refl : RatFunc K ≃ₐ[K] RatFunc K).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    change ratFuncUnitScaleEquiv (1 : Kˣ) (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p
    rw [ratFuncUnitScaleEquiv_algebraMap]
    change algebraMap K[X] (RatFunc K) (polyUnitScaleHom 1 p) = _
    rw [polyUnitScaleHom_one]
    rfl
  exact DFunLike.congr_fun hring x

/-- The faithful multiplicative action of `Kˣ` on the rational coordinate. -/
def ratFuncUnitScaleAction {K : Type*} [Field K] :
    Kˣ →* (RatFunc K ≃ₐ[K] RatFunc K) where
  toFun := ratFuncUnitScaleEquiv
  map_one' := ratFuncUnitScaleEquiv_one
  map_mul' u v := by
    apply AlgEquiv.ext
    intro x
    have hring :
        (ratFuncUnitScaleEquiv (u * v)).toRingEquiv.toRingHom =
          (ratFuncUnitScaleEquiv u * ratFuncUnitScaleEquiv v).toRingEquiv.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := K[X])
      intro p
      change ratFuncUnitScaleEquiv (u * v) (algebraMap K[X] (RatFunc K) p) =
        ratFuncUnitScaleEquiv u
          (ratFuncUnitScaleEquiv v (algebraMap K[X] (RatFunc K) p))
      rw [ratFuncUnitScaleEquiv_algebraMap, ratFuncUnitScaleEquiv_algebraMap,
        ratFuncUnitScaleEquiv_algebraMap]
      change algebraMap K[X] (RatFunc K)
        (polyUnitScaleHom (u * v) p) =
          algebraMap K[X] (RatFunc K) (polyUnitScaleHom u (polyUnitScaleHom v p))
      rw [← AlgHom.comp_apply, polyUnitScaleHom_comp]
    exact DFunLike.congr_fun hring x

@[simp]
theorem ratFuncUnitScaleAction_apply_X {K : Type*} [Field K] (u : Kˣ) :
    ratFuncUnitScaleAction u RatFunc.X = algebraMap K (RatFunc K) (u : K) * RatFunc.X :=
  ratFuncUnitScaleEquiv_X u

/-- The rational-coordinate scalar action is faithful. -/
theorem ratFuncUnitScaleAction_injective {K : Type*} [Field K] :
    Function.Injective (ratFuncUnitScaleAction : Kˣ → (RatFunc K ≃ₐ[K] RatFunc K)) := by
  intro u v huv
  have hX := DFunLike.congr_fun huv RatFunc.X
  simp only [ratFuncUnitScaleAction_apply_X] at hX
  have hX0 : (RatFunc.X : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact fun h => Polynomial.X_ne_zero (RatFunc.algebraMap_injective K (by simpa using h))
  have hc : algebraMap K (RatFunc K) (u : K) = algebraMap K (RatFunc K) (v : K) :=
    mul_right_cancel₀ hX0 hX
  exact Units.ext (RatFunc.C_injective hc)

/-- Scaling `K(X)` by `u` has exactly the multiplicative order of `u`. -/
theorem orderOf_ratFuncUnitScaleAction {K : Type*} [Field K] (u : Kˣ) :
    orderOf (ratFuncUnitScaleAction u) = orderOf u :=
  orderOf_injective ratFuncUnitScaleAction ratFuncUnitScaleAction_injective u

/-- A positive power of the rational coordinate is not constant. -/
theorem ratFunc_X_pow_not_constant {K : Type*} [Field K] {N : ℕ} (hN : 0 < N) :
    ¬ ∃ c : K, (RatFunc.X : RatFunc K) ^ N = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have hdegN : ratFuncDegree ((RatFunc.X : RatFunc K) ^ N) = N := by
    simp [ratFuncDegree, ← RatFunc.algebraMap_X, ← map_pow]
  have hdeg0 : ratFuncDegree ((RatFunc.X : RatFunc K) ^ N) = 0 := by
    rw [hc]
    simp [ratFuncDegree]
  omega

/-- The intermediate field `K(X^N)` inside `K(X)`. -/
def ratFuncPowerField (K : Type*) [Field K] (N : ℕ) :
    IntermediateField K (RatFunc K) :=
  IntermediateField.adjoin K ({(RatFunc.X : RatFunc K) ^ N} : Set (RatFunc K))

/-- **Finite scalar fixed field.** If `u` has positive order `N`, the cyclic scalar action on
`K(X)` fixes exactly `K(X^N)`. -/
theorem fixedField_zpowers_ratFuncUnitScaleAction
    {K : Type*} [Field K] (u : Kˣ) {N : ℕ}
    (hN : 0 < N) (hu : orderOf u = N) :
    IntermediateField.fixedField (Subgroup.zpowers (ratFuncUnitScaleAction u)) =
      ratFuncPowerField K N := by
  let P : RatFunc K := RatFunc.X ^ N
  let H : IntermediateField K (RatFunc K) := K⟮P⟯
  let σ : RatFunc K ≃ₐ[K] RatFunc K := ratFuncUnitScaleAction u
  let G : Subgroup (RatFunc K ≃ₐ[K] RatFunc K) := Subgroup.zpowers σ
  have huN : (u : K) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
    rfl
  have hσP : σ P = P := by
    simp only [σ, P, map_pow, ratFuncUnitScaleAction_apply_X]
    rw [mul_pow]
    have hmapu : (algebraMap K (RatFunc K) (u : K)) ^ N = 1 := by
      rw [← map_pow, huN, map_one]
    rw [hmapu, one_mul]
  have hσfix : σ ∈ H.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ IntermediateField.adjoin K ({P} : Set (RatFunc K)) at hx
    apply IntermediateField.adjoin_induction (F := K) (s := ({P} : Set (RatFunc K)))
      (p := fun y _ => σ y = y)
    · intro y hy
      have : y = P := Set.mem_singleton_iff.mp hy
      simpa [this] using hσP
    · intro c
      exact σ.commutes c
    · intro a b ha hb hfa hfb
      rw [map_add, hfa, hfb]
    · intro a ha hfa
      rw [map_inv₀, hfa]
    · intro a b ha hb hfa hfb
      rw [map_mul, hfa, hfb]
    · exact hx
  have hle : H ≤ IntermediateField.fixedField G := by
    apply (IntermediateField.le_iff_le (K := H) (H := G)).mpr
    exact (Subgroup.zpowers_le).mpr hσfix
  have hP : ¬ ∃ c : K, P = RatFunc.C c := by
    simpa [P] using ratFunc_X_pow_not_constant (K := K) hN
  letI : FiniteDimensional H H⟮(RatFunc.X : RatFunc K)⟯ :=
    IntermediateField.adjoin.finiteDimensional
      ((P.isAlgebraic_adjoin_simple_X hP).isIntegral)
  letI : FiniteDimensional H (RatFunc K) :=
    Module.Finite.equiv (RatFunc.IntermediateField.adjoinXEquiv H).toLinearEquiv
  have hfinrankH : Module.finrank H (RatFunc K) = N := by
    change Module.finrank K⟮P⟯ (RatFunc K) = N
    rw [RatFunc.finrank_eq_max_natDegree]
    simp [P, ← RatFunc.algebraMap_X, ← map_pow]
  have horderσ : orderOf σ = N := by
    simpa [σ, hu] using orderOf_ratFuncUnitScaleAction u
  have hcard : Nat.card G = N := by
    change Nat.card (Subgroup.zpowers σ) = N
    rw [Nat.card_zpowers, horderσ]
  letI : Finite G := Nat.finite_of_card_ne_zero (hcard.trans_ne hN.ne')
  letI : Fintype G := Fintype.ofFinite G
  have hFcard : Fintype.card G = N := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hfinrankFix :
      Module.finrank (IntermediateField.fixedField G) (RatFunc K) = N := by
    exact (FixedPoints.finrank_eq_card G (RatFunc K)).trans hFcard
  have heq : H = IntermediateField.fixedField G :=
    IntermediateField.eq_of_le_of_finrank_eq' hle (hfinrankH.trans hfinrankFix.symm)
  simpa [G, H, P, ratFuncPowerField] using heq.symm

/-- A rational function invariant under a scalar of infinite multiplicative order is constant. -/
theorem ratFuncUnitScale_fixed_eq_constant_of_infinite_order
    {K : Type*} [Field K] (u : Kˣ) (hu : orderOf u = 0)
    {r : RatFunc K} (hr : ratFuncUnitScaleAction u r = r) :
    ∃ c : K, r = RatFunc.C c := by
  by_contra hconst
  push Not at hconst
  let H : IntermediateField K (RatFunc K) := K⟮r⟯
  let σ : RatFunc K ≃ₐ[K] RatFunc K := ratFuncUnitScaleAction u
  let G : Subgroup (RatFunc K ≃ₐ[K] RatFunc K) := Subgroup.zpowers σ
  have hσfix : σ ∈ H.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ IntermediateField.adjoin K ({r} : Set (RatFunc K)) at hx
    apply IntermediateField.adjoin_induction (F := K) (s := ({r} : Set (RatFunc K)))
      (p := fun y _ => σ y = y)
    · intro y hy
      have : y = r := Set.mem_singleton_iff.mp hy
      simpa [σ, this] using hr
    · intro c
      exact σ.commutes c
    · intro a b ha hb hfa hfb
      rw [map_add, hfa, hfb]
    · intro a ha hfa
      rw [map_inv₀, hfa]
    · intro a b ha hb hfa hfb
      rw [map_mul, hfa, hfb]
    · exact hx
  have hGle : G ≤ H.fixingSubgroup := (Subgroup.zpowers_le).mpr hσfix
  have hrnc : ¬ ∃ c : K, r = RatFunc.C c := by
    simpa only [not_exists] using hconst
  letI : FiniteDimensional H H⟮(RatFunc.X : RatFunc K)⟯ :=
    IntermediateField.adjoin.finiteDimensional
      ((r.isAlgebraic_adjoin_simple_X hrnc).isIntegral)
  letI : FiniteDimensional H (RatFunc K) :=
    Module.Finite.equiv (RatFunc.IntermediateField.adjoinXEquiv H).toLinearEquiv
  letI : Finite (RatFunc K ≃ₐ[H] RatFunc K) := by infer_instance
  letI : Finite H.fixingSubgroup :=
    Finite.of_injective (H.fixingSubgroupEquiv : H.fixingSubgroup →
      (RatFunc K ≃ₐ[H] RatFunc K)) H.fixingSubgroupEquiv.injective
  let inclusion : G → H.fixingSubgroup := fun g => ⟨g, hGle g.2⟩
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : H.fixingSubgroup =>
      (x : RatFunc K ≃ₐ[K] RatFunc K)) hab
  letI : Finite G := Finite.of_injective inclusion hinclusion
  have hcardPos : 0 < Nat.card G := Nat.card_pos
  have horderσ : orderOf σ = 0 := by
    simpa [σ, hu] using orderOf_ratFuncUnitScaleAction u
  have hcardZero : Nat.card G = 0 := by
    change Nat.card (Subgroup.zpowers σ) = 0
    rw [Nat.card_zpowers, horderσ]
  exact hcardPos.ne' hcardZero

/-- **Infinite scalar fixed field.** If `u` has infinite multiplicative order, the cyclic scalar
action on `K(X)` fixes exactly the base field `K`. -/
theorem fixedField_zpowers_ratFuncUnitScaleAction_of_infinite_order
    {K : Type*} [Field K] (u : Kˣ) (hu : orderOf u = 0) :
    IntermediateField.fixedField (Subgroup.zpowers (ratFuncUnitScaleAction u)) = ⊥ := by
  apply le_antisymm
  · intro r hr
    rw [IntermediateField.mem_fixedField_iff] at hr
    have hfixed : ratFuncUnitScaleAction u r = r :=
      hr _ (Subgroup.mem_zpowers (ratFuncUnitScaleAction u))
    obtain ⟨c, hc⟩ := ratFuncUnitScale_fixed_eq_constant_of_infinite_order u hu hfixed
    rw [hc]
    exact (⊥ : IntermediateField K (RatFunc K)).algebraMap_mem c
  · exact bot_le

end

end GaloisForLFunctions.HTGeometry
