import Mathlib
import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation

/-!
# Carriers built from a seed function by difference operators

A Stanley–Reisner realization assigns to each class a function on which the vertex coordinates act
as difference operators.  Every such assignment comes from a single seed: fix translation steps
`ω : α → E` and a function `F : E → ℂ`, let the variable `X v` act by the difference operator
`T_{ω v} − 1`, and send a polynomial `P` to `P(T − 1) F`.  The assignment descends to the
Stanley–Reisner ring exactly when the nonface products annihilate `F`.

The operator algebra is the additive group algebra `AddMonoidAlgebra ℂ E`, which is commutative and
acts on functions `E → ℂ` by translations.

* `shiftAlgHom` — the translation action of `AddMonoidAlgebra ℂ E` on `E → ℂ`;
* `polyShift ω` — the algebra map `X v ↦ T_{ω v} − 1`;
* `SeedAnnihilates` — the nonface products kill the seed;
* `seedCarrier` — the induced carrier map on the Stanley–Reisner ring, with
  `seedCarrier_srVertexX_mul` its difference-operator rule.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [AddCommMonoid E]

/-! ### The translation action -/

/-- Translation of functions on `E` by a step. -/
def shiftEnd (e : E) : Module.End ℂ (E → ℂ) where
  toFun f := fun z => f (z + e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shiftEnd_apply (e : E) (f : E → ℂ) (z : E) : shiftEnd e f z = f (z + e) := rfl

/-- Translations form a multiplicative family indexed by the additive group of steps. -/
def shiftMonoidHom : Multiplicative E →* Module.End ℂ (E → ℂ) where
  toFun e := shiftEnd (Multiplicative.toAdd e)
  map_one' := by
    ext f z
    show f (z + 0) = f z
    rw [add_zero]
  map_mul' a b := by
    ext f z
    show f (z + (Multiplicative.toAdd a + Multiplicative.toAdd b))
      = f (z + Multiplicative.toAdd a + Multiplicative.toAdd b)
    rw [add_assoc]

/-- The translation action of the additive group algebra on functions. -/
def shiftAlgHom : AddMonoidAlgebra ℂ E →ₐ[ℂ] Module.End ℂ (E → ℂ) :=
  AddMonoidAlgebra.lift ℂ (Module.End ℂ (E → ℂ)) E shiftMonoidHom

theorem shiftAlgHom_apply (a : AddMonoidAlgebra ℂ E) (f : E → ℂ) (z : E) :
    shiftAlgHom a f z = ∑ e ∈ a.coeff.support, a.coeff e * f (z + e) := by
  rw [shiftAlgHom, AddMonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  show (a.coeff e • shiftEnd e) f z = _
  simp [shiftEnd, smul_eq_mul]

@[simp] theorem shiftAlgHom_single (e : E) (c : ℂ) (f : E → ℂ) :
    shiftAlgHom (AddMonoidAlgebra.single e c) f = fun z => c * f (z + e) := by
  rw [shiftAlgHom, AddMonoidAlgebra.lift_single]
  funext z
  show (c • shiftEnd e) f z = c * f (z + e)
  simp [smul_eq_mul]

/-! ### Difference operators attached to steps -/

variable {α : Type*}

/-- The difference operator `T_{ω v} − 1` as an element of the group algebra. -/
def stepVar (ω : α → E) (v : α) : AddMonoidAlgebra ℂ E :=
  AddMonoidAlgebra.single (ω v) 1 - 1

theorem shiftAlgHom_stepVar (ω : α → E) (v : α) (f : E → ℂ) :
    shiftAlgHom (stepVar ω v) f = fun z => f (z + ω v) - f z := by
  rw [stepVar, map_sub]
  funext z
  show shiftAlgHom (AddMonoidAlgebra.single (ω v) 1) f z - shiftAlgHom 1 f z = _
  rw [map_one, shiftAlgHom_single]
  simp

/-- The algebra map sending each variable to its difference operator. -/
def polyShift (ω : α → E) : MvPolynomial α ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ E :=
  aeval (stepVar ω)

@[simp] theorem polyShift_X (ω : α → E) (v : α) : polyShift ω (X v) = stepVar ω v := by
  simp [polyShift]

/-- The carrier of a polynomial: the polynomial evaluated at the difference operators, applied to
the seed. -/
def seedCarrierPoly (ω : α → E) (F : E → ℂ) (P : MvPolynomial α ℂ) : E → ℂ :=
  shiftAlgHom (polyShift ω P) F

/-- The carrier assignment on polynomials is `ℂ`-linear. -/
def seedCarrierPolyₗ (ω : α → E) (F : E → ℂ) : MvPolynomial α ℂ →ₗ[ℂ] (E → ℂ) where
  toFun P := seedCarrierPoly ω F P
  map_add' P Q := by
    show shiftAlgHom (polyShift ω (P + Q)) F = _
    rw [map_add, map_add]
    rfl
  map_smul' c P := by
    show shiftAlgHom (polyShift ω (c • P)) F = _
    rw [map_smul, map_smul]
    rfl

@[simp] theorem seedCarrierPolyₗ_apply (ω : α → E) (F : E → ℂ) (P : MvPolynomial α ℂ) :
    seedCarrierPolyₗ ω F P = seedCarrierPoly ω F P := rfl

/-- **The difference-operator rule on polynomials.**  Multiplication by `X v` becomes the difference
operator along `ω v`. -/
theorem seedCarrierPoly_X_mul (ω : α → E) (F : E → ℂ) (v : α) (P : MvPolynomial α ℂ) :
    seedCarrierPoly ω F (X v * P)
      = fun z => seedCarrierPoly ω F P (z + ω v) - seedCarrierPoly ω F P z := by
  show shiftAlgHom (polyShift ω (X v * P)) F = _
  rw [map_mul, polyShift_X, map_mul]
  show shiftAlgHom (stepVar ω v) (shiftAlgHom (polyShift ω P) F) = _
  rw [shiftAlgHom_stepVar]
  rfl

theorem seedCarrierPoly_add (ω : α → E) (F : E → ℂ) (P Q : MvPolynomial α ℂ) :
    seedCarrierPoly ω F (P + Q) = seedCarrierPoly ω F P + seedCarrierPoly ω F Q :=
  (seedCarrierPolyₗ ω F).map_add P Q

theorem seedCarrierPoly_C (ω : α → E) (F : E → ℂ) (c : ℂ) :
    seedCarrierPoly ω F (C c) = fun z => c * F z := by
  show shiftAlgHom (polyShift ω (C c)) F = _
  rw [polyShift, aeval_C, AlgHom.commutes]
  funext z
  rw [Module.algebraMap_end_apply]
  rfl

/-- A vanishing step gives the zero difference operator. -/
theorem stepVar_eq_zero {ω : α → E} {v : α} (h : ω v = 0) : stepVar ω v = 0 := by
  rw [stepVar, h, AddMonoidAlgebra.one_def, sub_self]

/-- The carrier of a squarefree monomial is the corresponding product of difference operators
applied to the seed. -/
theorem seedCarrierPoly_prod_X (ω : α → E) (F : E → ℂ) (J : Finset α) :
    seedCarrierPoly ω F (∏ v ∈ J, X v) = shiftAlgHom (∏ v ∈ J, stepVar ω v) F := by
  show shiftAlgHom (polyShift ω (∏ v ∈ J, X v)) F = _
  rw [map_prod]
  simp

/-- The carrier of a sum of seeds is the sum of the carriers. -/
theorem seedCarrierPoly_sum {ι : Type*} (ω : α → E) (s : Finset ι) (F : ι → (E → ℂ))
    (P : MvPolynomial α ℂ) (z : E) :
    seedCarrierPoly ω (fun w => ∑ i ∈ s, F i w) P z
      = ∑ i ∈ s, seedCarrierPoly ω (F i) P z := by
  have hfun : (fun w => ∑ i ∈ s, F i w) = ∑ i ∈ s, F i := by
    funext w
    rw [Finset.sum_apply]
  show shiftAlgHom (polyShift ω P) (fun w => ∑ i ∈ s, F i w) z = _
  rw [hfun, map_sum, Finset.sum_apply]
  rfl

/-- A shift operator sends constants to constants. -/
theorem shiftAlgHom_const (A : AddMonoidAlgebra ℂ E) (C : ℂ) :
    shiftAlgHom A (fun _ : E => C) = fun _ => (∑ γ ∈ A.coeff.support, A.coeff γ) * C := by
  funext z
  rw [shiftAlgHom_apply, Finset.sum_mul]

/-- The carrier of a product is the outer operator applied to the inner carrier. -/
theorem seedCarrierPoly_mul (ω : α → E) (F : E → ℂ) (P Q : MvPolynomial α ℂ) :
    seedCarrierPoly ω F (P * Q) = shiftAlgHom (polyShift ω P) (seedCarrierPoly ω F Q) := by
  show shiftAlgHom (polyShift ω (P * Q)) F = _
  rw [map_mul, map_mul, Module.End.mul_apply]
  rfl

/-! ### Descent to the Stanley–Reisner ring -/

variable [DecidableEq α]

/-- The seed is annihilated by every nonface product of difference operators. -/
def SeedAnnihilates (ω : α → E) (facets : Finset (Finset α)) (F : E → ℂ) : Prop :=
  ∀ J : Finset α, ¬ IsFaceOf (↑facets : Set (Finset α)) J →
    shiftAlgHom (∏ v ∈ J, stepVar ω v) F = 0

omit [DecidableEq α] in
/-- A monomial whose support is a nonface has zero carrier: its operator factors through the nonface
product, and the group algebra is commutative. -/
theorem seedCarrierPoly_monomial_eq_zero {ω : α → E} {facets : Finset (Finset α)} {F : E → ℂ}
    (h : SeedAnnihilates ω facets F) {m : α →₀ ℕ}
    (hm : ¬ IsFaceOf (↑facets : Set (Finset α)) m.support) (c : ℂ) :
    seedCarrierPoly ω F (monomial m c) = 0 := by
  have hsplit : (m.prod fun i k => stepVar ω i ^ k)
      = (∏ v ∈ m.support, stepVar ω v ^ (m v - 1)) * ∏ v ∈ m.support, stepVar ω v := by
    rw [Finsupp.prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hv1 : 1 ≤ m v := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    rw [← pow_succ, Nat.sub_add_cancel hv1]
  show shiftAlgHom (polyShift ω (monomial m c)) F = 0
  rw [polyShift, aeval_monomial, hsplit, ← mul_assoc, map_mul]
  show shiftAlgHom _ (shiftAlgHom (∏ v ∈ m.support, stepVar ω v) F) = 0
  rw [h m.support hm, map_zero]

/-- Every element of the Stanley–Reisner ideal has zero carrier. -/
theorem seedCarrierPoly_eq_zero_of_mem {ω : α → E} {facets : Finset (Finset α)} {F : E → ℂ}
    (h : SeedAnnihilates ω facets F) {P : MvPolynomial α ℂ}
    (hP : P ∈ stanleyReisnerIdeal ℂ facets) : seedCarrierPoly ω F P = 0 := by
  have hsupp := (mem_stanleyReisnerIdeal_iff (R := ℂ) facets P).mp hP
  have hP' : P = ∑ m ∈ P.support, monomial m (coeff m P) := (support_sum_monomial_coeff P).symm
  have : seedCarrierPolyₗ ω F P = 0 := by
    rw [hP', map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    exact seedCarrierPoly_monomial_eq_zero h (hsupp m hm) _
  exact this

/-- **The carrier map on the Stanley–Reisner ring.**  The polynomial carrier descends because the
Stanley–Reisner ideal annihilates the seed. -/
def seedCarrier (ω : α → E) (facets : Finset (Finset α)) (F : E → ℂ)
    (h : SeedAnnihilates ω facets F) : stanleyReisnerRing ℂ facets →ₗ[ℂ] (E → ℂ) :=
  Submodule.liftQ ((stanleyReisnerIdeal ℂ facets).restrictScalars ℂ) (seedCarrierPolyₗ ω F)
    (fun _ hP => seedCarrierPoly_eq_zero_of_mem h hP)

@[simp] theorem seedCarrier_mk (ω : α → E) (facets : Finset (Finset α)) (F : E → ℂ)
    (h : SeedAnnihilates ω facets F) (P : MvPolynomial α ℂ) :
    seedCarrier ω facets F h (Ideal.Quotient.mk (stanleyReisnerIdeal ℂ facets) P)
      = seedCarrierPoly ω F P := rfl

/-- **The difference-operator rule on the Stanley–Reisner ring.** -/
theorem seedCarrier_srVertexX_mul (ω : α → E) (facets : Finset (Finset α)) (F : E → ℂ)
    (h : SeedAnnihilates ω facets F) (v : α) (q : stanleyReisnerRing ℂ facets) :
    seedCarrier ω facets F h (srVertexX ℂ facets v * q)
      = fun z => seedCarrier ω facets F h q (z + ω v) - seedCarrier ω facets F h q z := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := stanleyReisnerIdeal ℂ facets) q
  show seedCarrier ω facets F h (Ideal.Quotient.mk _ (X v * P)) = _
  rw [seedCarrier_mk, seedCarrier_mk, seedCarrierPoly_X_mul]

end

/-! ### Entire seeds give entire carriers -/

section Entire

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α : Type*}

theorem differentiable_shiftAlgHom (a : AddMonoidAlgebra ℂ E) {F : E → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (shiftAlgHom a F) := by
  have hEq : shiftAlgHom a F = fun z => ∑ e ∈ a.coeff.support, a.coeff e * F (z + e) :=
    funext fun z => shiftAlgHom_apply a F z
  rw [hEq]
  exact Differentiable.fun_sum fun e _ => (hF.comp (differentiable_id.add_const e)).const_mul _

theorem differentiable_seedCarrierPoly (ω : α → E) {F : E → ℂ} (hF : Differentiable ℂ F)
    (P : MvPolynomial α ℂ) : Differentiable ℂ (seedCarrierPoly ω F P) :=
  differentiable_shiftAlgHom _ hF

theorem differentiable_seedCarrier [DecidableEq α] (ω : α → E) (facets : Finset (Finset α))
    {F : E → ℂ} (hF : Differentiable ℂ F) (h : SeedAnnihilates ω facets F)
    (q : stanleyReisnerRing ℂ facets) : Differentiable ℂ (seedCarrier ω facets F h q) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := stanleyReisnerIdeal ℂ facets) q
  rw [seedCarrier_mk]
  exact differentiable_seedCarrierPoly ω hF P

end

end Entire

end GaloisForLFunctions.HTGeometry
