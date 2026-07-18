import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.GroupTheory.OrderOfElement

open Polynomial IntermediateField

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def polyTranslationHom {K : Type*} [Field K] (c : K) : K[X] →ₐ[K] K[X] :=
  aeval (X + C c)

@[simp]
theorem polyTranslationHom_X {K : Type*} [Field K] (c : K) :
    polyTranslationHom c X = X + C c := by
  simp [polyTranslationHom]

theorem polyTranslationHom_comp {K : Type*} [Field K] (c d : K) :
    (polyTranslationHom c).comp (polyTranslationHom d) =
      polyTranslationHom (c + d) := by
  apply Polynomial.algHom_ext
  simp [polyTranslationHom, add_assoc]

@[simp]
theorem polyTranslationHom_zero {K : Type*} [Field K] :
    polyTranslationHom (0 : K) = AlgHom.id K K[X] := by
  apply Polynomial.algHom_ext
  simp [polyTranslationHom]

def polyTranslationEquiv {K : Type*} [Field K] (c : K) : K[X] ≃ₐ[K] K[X] :=
  AlgEquiv.ofAlgHom (polyTranslationHom c) (polyTranslationHom (-c))
    (by rw [polyTranslationHom_comp]; simp)
    (by rw [polyTranslationHom_comp]; simp)

@[simp]
theorem polyTranslationEquiv_X {K : Type*} [Field K] (c : K) :
    polyTranslationEquiv c X = X + C c := by
  simp [polyTranslationEquiv]

def ratFuncTranslationEquiv {K : Type*} [Field K] (c : K) :
    RatFunc K ≃ₐ[K] RatFunc K :=
  IsLocalization.algEquivOfAlgEquiv (RatFunc K) (RatFunc K) (polyTranslationEquiv c)
    (MulEquivClass.map_nonZeroDivisors (polyTranslationEquiv c))

theorem ratFuncTranslationEquiv_algebraMap {K : Type*} [Field K]
    (c : K) (p : K[X]) :
    ratFuncTranslationEquiv c (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (polyTranslationEquiv c p) := by
  rw [ratFuncTranslationEquiv, IsLocalization.algEquivOfAlgEquiv_eq]

@[simp]
theorem ratFuncTranslationEquiv_X {K : Type*} [Field K] (c : K) :
    ratFuncTranslationEquiv c RatFunc.X =
      RatFunc.X + algebraMap K (RatFunc K) c := by
  rw [← RatFunc.algebraMap_X, ratFuncTranslationEquiv_algebraMap,
    polyTranslationEquiv_X, map_add, RatFunc.algebraMap_X,
    ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

@[simp]
theorem ratFuncTranslationEquiv_zero {K : Type*} [Field K] :
    ratFuncTranslationEquiv (0 : K) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  have hring :
      (ratFuncTranslationEquiv (0 : K)).toRingEquiv.toRingHom =
        (AlgEquiv.refl : RatFunc K ≃ₐ[K] RatFunc K).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    change ratFuncTranslationEquiv (0 : K)
        (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) p
    rw [ratFuncTranslationEquiv_algebraMap]
    change algebraMap K[X] (RatFunc K) (polyTranslationHom 0 p) = _
    rw [polyTranslationHom_zero]
    rfl
  exact DFunLike.congr_fun hring x

def ratFuncTranslationAction {K : Type*} [Field K] :
    Multiplicative K →* (RatFunc K ≃ₐ[K] RatFunc K) where
  toFun c := ratFuncTranslationEquiv c.toAdd
  map_one' := ratFuncTranslationEquiv_zero
  map_mul' c d := by
    apply AlgEquiv.ext
    intro x
    have hring :
        (ratFuncTranslationEquiv (c * d).toAdd).toRingEquiv.toRingHom =
          (ratFuncTranslationEquiv c.toAdd *
            ratFuncTranslationEquiv d.toAdd).toRingEquiv.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := K[X])
      intro p
      change ratFuncTranslationEquiv (c * d).toAdd
          (algebraMap K[X] (RatFunc K) p) =
        ratFuncTranslationEquiv c.toAdd
          (ratFuncTranslationEquiv d.toAdd
            (algebraMap K[X] (RatFunc K) p))
      rw [ratFuncTranslationEquiv_algebraMap,
        ratFuncTranslationEquiv_algebraMap,
        ratFuncTranslationEquiv_algebraMap]
      change algebraMap K[X] (RatFunc K)
          (polyTranslationHom (c * d).toAdd p) =
        algebraMap K[X] (RatFunc K)
          (polyTranslationHom c.toAdd (polyTranslationHom d.toAdd p))
      rw [← AlgHom.comp_apply, polyTranslationHom_comp]
      rfl
    exact DFunLike.congr_fun hring x

@[simp]
theorem ratFuncTranslationAction_apply_X {K : Type*} [Field K]
    (c : Multiplicative K) :
    ratFuncTranslationAction c RatFunc.X =
      RatFunc.X + algebraMap K (RatFunc K) c.toAdd := by
  change ratFuncTranslationEquiv c.toAdd RatFunc.X = _
  exact ratFuncTranslationEquiv_X c.toAdd

theorem ratFuncTranslationAction_injective {K : Type*} [Field K] :
    Function.Injective
      (ratFuncTranslationAction : Multiplicative K →
        (RatFunc K ≃ₐ[K] RatFunc K)) := by
  intro c d hcd
  have hX := DFunLike.congr_fun hcd RatFunc.X
  have hX' : RatFunc.X + algebraMap K (RatFunc K) c.toAdd =
      RatFunc.X + algebraMap K (RatFunc K) d.toAdd := by
    simpa only [ratFuncTranslationAction_apply_X] using hX
  have hc : c.toAdd = d.toAdd :=
    RatFunc.C_injective (add_left_cancel hX')
  exact Multiplicative.toAdd.injective hc

theorem orderOf_ratFuncTranslationAction {K : Type*} [Field K] (c : K) :
    orderOf (ratFuncTranslationAction (Multiplicative.ofAdd c)) =
      addOrderOf c := by
  have h := orderOf_injective
    (ratFuncTranslationAction : Multiplicative K →*
      (RatFunc K ≃ₐ[K] RatFunc K))
    (ratFuncTranslationAction_injective (K := K))
    (Multiplicative.ofAdd c)
  exact h.trans (orderOf_ofAdd_eq_addOrderOf c)

theorem addOrderOf_eq_zero_of_ne_zero
    {K : Type*} [Field K] [CharZero K] {c : K} (hc : c ≠ 0) :
    addOrderOf c = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n hn hnc
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  exact (mul_ne_zero hn0 hc) (by simpa [nsmul_eq_mul] using hnc)

theorem ratFuncTranslation_fixed_eq_constant
    {K : Type*} [Field K] [CharZero K] (c : K) (hc : c ≠ 0)
    {r : RatFunc K}
    (hr : ratFuncTranslationAction (Multiplicative.ofAdd c) r = r) :
    ∃ a : K, r = RatFunc.C a := by
  by_contra hconst
  push Not at hconst
  let H : IntermediateField K (RatFunc K) := K⟮r⟯
  let sigma : RatFunc K ≃ₐ[K] RatFunc K :=
    ratFuncTranslationAction (Multiplicative.ofAdd c)
  let G : Subgroup (RatFunc K ≃ₐ[K] RatFunc K) := Subgroup.zpowers sigma
  have hsigmaFix : sigma ∈ H.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ IntermediateField.adjoin K ({r} : Set (RatFunc K)) at hx
    apply IntermediateField.adjoin_induction (F := K)
      (s := ({r} : Set (RatFunc K))) (p := fun y _ => sigma y = y)
    · intro y hy
      have : y = r := Set.mem_singleton_iff.mp hy
      simpa [sigma, this] using hr
    · intro a
      exact sigma.commutes a
    · intro a b ha hb hfa hfb
      rw [map_add, hfa, hfb]
    · intro a ha hfa
      rw [map_inv₀, hfa]
    · intro a b ha hb hfa hfb
      rw [map_mul, hfa, hfb]
    · exact hx
  have hGle : G ≤ H.fixingSubgroup := (Subgroup.zpowers_le).mpr hsigmaFix
  have hrnc : ¬ ∃ a : K, r = RatFunc.C a := by
    simpa only [not_exists] using hconst
  letI : FiniteDimensional H H⟮(RatFunc.X : RatFunc K)⟯ :=
    IntermediateField.adjoin.finiteDimensional
      ((r.isAlgebraic_adjoin_simple_X hrnc).isIntegral)
  letI : FiniteDimensional H (RatFunc K) :=
    Module.Finite.equiv (RatFunc.IntermediateField.adjoinXEquiv H).toLinearEquiv
  letI : Finite (RatFunc K ≃ₐ[H] RatFunc K) := by infer_instance
  letI : Finite H.fixingSubgroup :=
    Finite.of_injective
      (H.fixingSubgroupEquiv : H.fixingSubgroup → (RatFunc K ≃ₐ[H] RatFunc K))
      H.fixingSubgroupEquiv.injective
  let inclusion : G → H.fixingSubgroup := fun g => ⟨g, hGle g.2⟩
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : H.fixingSubgroup =>
      (x : RatFunc K ≃ₐ[K] RatFunc K)) hab
  letI : Finite G := Finite.of_injective inclusion hinclusion
  have hcardPos : 0 < Nat.card G := Nat.card_pos
  have horderSigma : orderOf sigma = 0 := by
    simpa [sigma, addOrderOf_eq_zero_of_ne_zero hc] using
      orderOf_ratFuncTranslationAction c
  have hcardZero : Nat.card G = 0 := by
    change Nat.card (Subgroup.zpowers sigma) = 0
    rw [Nat.card_zpowers, horderSigma]
  exact hcardPos.ne' hcardZero

theorem fixedField_zpowers_ratFuncTranslationAction
    {K : Type*} [Field K] [CharZero K] (c : K) (hc : c ≠ 0) :
    IntermediateField.fixedField
      (Subgroup.zpowers
        (ratFuncTranslationAction (Multiplicative.ofAdd c))) = ⊥ := by
  apply le_antisymm
  · intro r hr
    rw [IntermediateField.mem_fixedField_iff] at hr
    have hfixed : ratFuncTranslationAction (Multiplicative.ofAdd c) r = r :=
      hr _ (Subgroup.mem_zpowers
        (ratFuncTranslationAction (Multiplicative.ofAdd c)))
    obtain ⟨a, ha⟩ := ratFuncTranslation_fixed_eq_constant c hc hfixed
    rw [ha]
    exact (⊥ : IntermediateField K (RatFunc K)).algebraMap_mem a
  · exact bot_le

end

end GaloisForLFunctions.HTGeometry
