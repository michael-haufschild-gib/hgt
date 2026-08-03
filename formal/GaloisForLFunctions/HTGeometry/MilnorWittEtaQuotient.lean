import GaloisForLFunctions.HTGeometry.MilnorWittKTheory

/-!
# Milnor `K`-theory is Milnor--Witt `K`-theory modulo `η`

The forgetful morphism `K^{MW}(F) → K^M(F)` kills `η`, and killing `η` is all it does: the
quotient of Milnor--Witt `K`-theory by the relation `η = 0` is Milnor `K`-theory.  Twisted
multiplicativity `[uv] = [u] + [v] + η[u][v]` collapses to ordinary additivity of the symbol
exactly when `η` dies, so the two presentations become the same one.

* `MilnorWittModEta` : `K^{MW}(F)/(η)`.
* `milnorWittEtaForget` : the forgetful morphism, descended to the quotient.
* `milnorEtaLift` : its inverse, sending the Milnor symbol to the Milnor--Witt symbol.
* `milnorWittEtaEquiv` : the resulting isomorphism `K^{MW}(F)/(η) ≅ K^M(F)`.
* `milnorWittForget_eq_zero_iff` : the kernel of the forgetful morphism is exactly what dies in
  the quotient by `η`.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittEta

variable (F : Type*) [Field F]

/-- The relation that kills `η`. -/
inductive MilnorWittEtaRel : MilnorWittK F → MilnorWittK F → Prop
  | eta : MilnorWittEtaRel (milnorWittEta F) 0

/-- **Milnor--Witt `K`-theory modulo `η`.** -/
abbrev MilnorWittModEta : Type _ := RingQuot (MilnorWittEtaRel F)

/-- The quotient map by `η`. -/
def milnorWittModEtaMk : MilnorWittK F →ₐ[ℤ] MilnorWittModEta F :=
  RingQuot.mkAlgHom ℤ (MilnorWittEtaRel F)

@[simp]
theorem milnorWittModEtaMk_eta : milnorWittModEtaMk F (milnorWittEta F) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (MilnorWittEtaRel.eta (F := F))
  rw [milnorWittModEtaMk, h, map_zero]

theorem milnorWittModEtaMk_surjective : Function.Surjective (milnorWittModEtaMk F) :=
  RingQuot.mkAlgHom_surjective ℤ _

/-! ### The forgetful morphism descends -/

theorem milnorWittForget_rel_eta :
    ∀ x y : MilnorWittK F, MilnorWittEtaRel F x y →
      milnorWittForget F x = milnorWittForget F y := by
  rintro _ _ ⟨⟩
  rw [milnorWittForget_eta, map_zero]

/-- **The forgetful morphism on the quotient by `η`.** -/
def milnorWittEtaForget : MilnorWittModEta F →ₐ[ℤ] MilnorK F :=
  RingQuot.liftAlgHom ℤ ⟨milnorWittForget F, milnorWittForget_rel_eta F⟩

@[simp]
theorem milnorWittEtaForget_mk (x : MilnorWittK F) :
    milnorWittEtaForget F (milnorWittModEtaMk F x) = milnorWittForget F x := by
  rw [milnorWittEtaForget, milnorWittModEtaMk, RingQuot.liftAlgHom_mkAlgHom_apply]

/-! ### The inverse -/

/-- The Milnor--Witt symbol, read in the quotient by `η`, is additive in its argument: the
correction term of twisted multiplicativity is a multiple of `η`. -/
def milnorWittModEtaSymbolHom : Additive Fˣ →+ MilnorWittModEta F :=
  AddMonoidHom.mk' (fun a => milnorWittModEtaMk F (milnorWittSymbol (Additive.toMul a))) <| by
    intro a b
    show milnorWittModEtaMk F (milnorWittSymbol (Additive.toMul a * Additive.toMul b)) =
      milnorWittModEtaMk F (milnorWittSymbol (Additive.toMul a)) +
        milnorWittModEtaMk F (milnorWittSymbol (Additive.toMul b))
    rw [milnorWittSymbol_mul, map_add, map_add, map_mul, map_mul, milnorWittModEtaMk_eta,
      zero_mul, zero_mul, add_zero]

/-- The same map, as a `ℤ`-linear map, so that it extends to the tensor algebra. -/
def milnorWittModEtaLin : Additive Fˣ →ₗ[ℤ] MilnorWittModEta F where
  toFun a := milnorWittModEtaSymbolHom F a
  map_add' a b := map_add _ a b
  map_smul' r a := by
    show milnorWittModEtaSymbolHom F (r • a) = r • milnorWittModEtaSymbolHom F a
    exact map_zsmul (milnorWittModEtaSymbolHom F) r a

/-- The extension to the tensor algebra on the unit group. -/
def milnorWittModEtaTensor : TensorAlgebra ℤ (Additive Fˣ) →ₐ[ℤ] MilnorWittModEta F :=
  TensorAlgebra.lift ℤ (milnorWittModEtaLin F)

@[simp]
theorem milnorWittModEtaTensor_ι (a : Fˣ) :
    milnorWittModEtaTensor F (TensorAlgebra.ι ℤ (Additive.ofMul a)) =
      milnorWittModEtaMk F (milnorWittSymbol a) := by
  rw [milnorWittModEtaTensor, TensorAlgebra.lift_ι_apply]
  rfl

theorem milnorWittModEtaTensor_rel :
    ∀ x y : TensorAlgebra ℤ (Additive Fˣ), MilnorKRel F x y →
      milnorWittModEtaTensor F x = milnorWittModEtaTensor F y := by
  rintro _ _ ⟨a, ha⟩
  rw [map_mul, map_zero, milnorWittModEtaTensor_ι, milnorWittModEtaTensor_ι, ← map_mul,
    milnorWittSymbol_mul_oneSub, map_zero]

/-- **The inverse of the forgetful morphism**: the Milnor symbol goes to the Milnor--Witt symbol.
The Steinberg relation is the same on both sides, and multiplicativity of the Milnor symbol is
twisted multiplicativity with `η` killed. -/
def milnorEtaLift : MilnorK F →ₐ[ℤ] MilnorWittModEta F :=
  RingQuot.liftAlgHom ℤ ⟨milnorWittModEtaTensor F, milnorWittModEtaTensor_rel F⟩

@[simp]
theorem milnorEtaLift_symbol (a : Fˣ) :
    milnorEtaLift F (milnorSymbol a) = milnorWittModEtaMk F (milnorWittSymbol a) := by
  rw [milnorEtaLift, milnorSymbol, milnorKMk, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact milnorWittModEtaTensor_ι F a

/-! ### The isomorphism -/

theorem milnorWittEtaForget_leftInverse (z : MilnorWittModEta F) :
    milnorEtaLift F (milnorWittEtaForget F z) = z := by
  obtain ⟨w, rfl⟩ := milnorWittModEtaMk_surjective F z
  obtain ⟨v, rfl⟩ := RingQuot.mkAlgHom_surjective ℤ (MilnorWittRel F) w
  induction v using FreeAlgebra.induction with
  | grade0 r => simp only [AlgHom.commutes]
  | grade1 x =>
    cases x with
    | eta =>
      rw [show (RingQuot.mkAlgHom ℤ (MilnorWittRel F)) (FreeAlgebra.ι ℤ (MWGen.eta (F := F))) =
          milnorWittEta F from rfl, milnorWittModEtaMk_eta, map_zero, map_zero]
    | sym u =>
      rw [show (RingQuot.mkAlgHom ℤ (MilnorWittRel F)) (FreeAlgebra.ι ℤ (MWGen.sym u)) =
          milnorWittSymbol u from rfl, milnorWittEtaForget_mk, milnorWittForget_symbol,
        milnorEtaLift_symbol]
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add, ha, hb]

theorem milnorWittEtaForget_rightInverse (z : MilnorK F) :
    milnorWittEtaForget F (milnorEtaLift F z) = z := by
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective ℤ (MilnorKRel F) z
  induction w using TensorAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes]
  | ι x =>
    rw [show (RingQuot.mkAlgHom ℤ (MilnorKRel F)) (TensorAlgebra.ι ℤ x) =
        milnorSymbol (Additive.toMul x) from rfl, milnorEtaLift_symbol, milnorWittEtaForget_mk,
      milnorWittForget_symbol]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- **`K^{MW}(F)/(η) ≅ K^M(F)`.**  Killing `η` turns twisted multiplicativity into ordinary
additivity of the symbol, which is the only difference between the two presentations. -/
def milnorWittEtaEquiv : MilnorWittModEta F ≃ₐ[ℤ] MilnorK F where
  toFun := milnorWittEtaForget F
  invFun := milnorEtaLift F
  left_inv := milnorWittEtaForget_leftInverse F
  right_inv := milnorWittEtaForget_rightInverse F
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' := AlgHom.commutes _

@[simp]
theorem milnorWittEtaEquiv_symbol (a : Fˣ) :
    milnorWittEtaEquiv F (milnorWittModEtaMk F (milnorWittSymbol a)) = milnorSymbol a := by
  show milnorWittEtaForget F (milnorWittModEtaMk F (milnorWittSymbol a)) = _
  rw [milnorWittEtaForget_mk, milnorWittForget_symbol]

/-- **The kernel of the forgetful morphism is exactly what `η` kills.**  Nothing beyond the
`η`-relation is lost on the way from Milnor--Witt to Milnor `K`-theory. -/
theorem milnorWittForget_eq_zero_iff (x : MilnorWittK F) :
    milnorWittForget F x = 0 ↔ milnorWittModEtaMk F x = 0 := by
  constructor
  · intro h
    have hx := milnorWittEtaForget_leftInverse F (milnorWittModEtaMk F x)
    rw [milnorWittEtaForget_mk, h, map_zero] at hx
    exact hx.symm
  · intro h
    rw [← milnorWittEtaForget_mk, h, map_zero]

end MilnorWittEta

end GaloisForLFunctions.HTGeometry
