import GaloisForLFunctions.HTGeometry.SRDifferenceCarrier
import GaloisForLFunctions.HTGeometry.ExponentialSeedCarrier

/-!
# Exponential seeds along an additive phase

`expSeedHom L z = exp (exp (L z))` for an additive map `L : E →+ ℂ` is the seed attached to one
facet of a periodic pencil: `L` is `2πi` times the normalized facet form, so a step `ω v` with
`L (ω v) ∈ 2πi ℤ` leaves the seed invariant, while the other steps dilate the inner exponential.

Translating the argument by `γ` multiplies the inner exponential by `exp (L γ)`, so the carrier of a
polynomial is a finite combination of dilates of `exp`, read at `exp (L z)`.  Its Taylor
coefficients at the origin are the *symbols* of the polynomial, evaluated at the difference-operator
eigenvalues `exp (m · L (ω j)) − 1`.

* `symbHom ω L m P` — the symbol at level `m`;
* `seedCarrierPoly_expSeedHom` — the carrier as a dilate combination;
* `symbHom_eq_zero_of_carrier_const` — a constant carrier kills every symbol of positive level.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [AddCommMonoid E]

/-- The exponential seed of an additive phase. -/
def expSeedHom (L : E →+ ℂ) : E → ℂ := fun z => Complex.exp (Complex.exp (L z))

/-- The multiplicative character `γ ↦ exp (m · L γ)` of the additive group of shifts. -/
def dilateCharHom (L : E →+ ℂ) (t : ℂ) : Multiplicative E →* ℂ where
  toFun g := Complex.exp (t * L (Multiplicative.toAdd g))
  map_one' := by simp
  map_mul' a b := by
    show Complex.exp (t * L (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [map_add, mul_add, Complex.exp_add]

/-- The induced algebra map on the group algebra of shifts. -/
def evAlgHom (L : E →+ ℂ) (t : ℂ) : AddMonoidAlgebra ℂ E →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ E (dilateCharHom L t)

@[simp] theorem evAlgHom_single (L : E →+ ℂ) (t : ℂ) (γ : E) (c : ℂ) :
    evAlgHom L t (AddMonoidAlgebra.single γ c) = c * Complex.exp (t * L γ) := by
  rw [evAlgHom, AddMonoidAlgebra.lift_single]
  simp [dilateCharHom, smul_eq_mul]

variable {α : Type*}

/-- **The symbol of a polynomial along an additive phase.** -/
def symbHom (ω : α → E) (L : E →+ ℂ) (t : ℂ) (P : MvPolynomial α ℂ) : ℂ :=
  aeval (fun j => Complex.exp (t * L (ω j)) - 1) P

theorem evAlgHom_polyShift (ω : α → E) (L : E →+ ℂ) (t : ℂ) (P : MvPolynomial α ℂ) :
    evAlgHom L t (polyShift ω P) = symbHom ω L t P := by
  have h := MvPolynomial.comp_aeval (R := ℂ) (stepVar ω) (evAlgHom L t)
  have happ := congrArg (fun f => f P) h
  simp only [AlgHom.comp_apply] at happ
  have hpt : (fun i => evAlgHom L t (stepVar ω i))
      = fun j => Complex.exp (t * L (ω j)) - 1 := by
    funext j
    rw [stepVar, map_sub, evAlgHom_single, map_one, one_mul]
  rw [polyShift, happ, symbHom, hpt]

theorem symbHom_mul (ω : α → E) (L : E →+ ℂ) (t : ℂ) (P Q : MvPolynomial α ℂ) :
    symbHom ω L t (P * Q) = symbHom ω L t P * symbHom ω L t Q := by
  simp [symbHom]

theorem symbHom_X (ω : α → E) (L : E →+ ℂ) (t : ℂ) (v : α) :
    symbHom ω L t (X v) = Complex.exp (t * L (ω v)) - 1 := by
  simp [symbHom]

/-! ### The carrier as a combination of dilates -/

/-- A finite combination of dilates of `exp`, indexed by the shift parameters of an operator. -/
def dilateSumHom (A : AddMonoidAlgebra ℂ E) (L : E →+ ℂ) : ℂ → ℂ :=
  fun w => ∑ γ ∈ A.coeff.support, A.coeff γ * Complex.exp (Complex.exp (L γ) * w)

theorem differentiable_dilateSumHom (A : AddMonoidAlgebra ℂ E) (L : E →+ ℂ) :
    Differentiable ℂ (dilateSumHom A L) :=
  Differentiable.fun_sum fun _ _ =>
    (Complex.differentiable_exp.comp (differentiable_id.const_mul _)).const_mul _

/-- **The carrier of the exponential seed of a phase.** -/
theorem seedCarrierPoly_expSeedHom (ω : α → E) (L : E →+ ℂ) (P : MvPolynomial α ℂ) (z : E) :
    seedCarrierPoly ω (expSeedHom L) P z
      = dilateSumHom (polyShift ω P) L (Complex.exp (L z)) := by
  rw [seedCarrierPoly, shiftAlgHom_apply, dilateSumHom]
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  show Complex.exp (Complex.exp (L (z + γ))) = _
  rw [map_add, Complex.exp_add, mul_comm (Complex.exp (L z))]

theorem iteratedDeriv_dilateSumHom_zero (A : AddMonoidAlgebra ℂ E) (L : E →+ ℂ) (m : ℕ) :
    iteratedDeriv m (dilateSumHom A L) 0 = evAlgHom L (m : ℂ) A := by
  have hsum : iteratedDeriv m (dilateSumHom A L) 0
      = ∑ γ ∈ A.coeff.support, A.coeff γ * (Complex.exp (L γ)) ^ m := by
    have hfun : dilateSumHom A L
        = fun w => ∑ γ ∈ A.coeff.support,
            A.coeff γ * Complex.exp (Complex.exp (L γ) * w) := rfl
    rw [hfun, iteratedDeriv_eq_iteratedFDeriv]
    have hcd : ∀ γ ∈ A.coeff.support,
        ContDiff ℂ (m : ℕ∞) fun w : ℂ => A.coeff γ * Complex.exp (Complex.exp (L γ) * w) :=
      fun γ _ => contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    rw [iteratedFDeriv_sum hcd]
    simp only [Finset.sum_apply, _root_.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_constMul_expLinear]
    simp
  rw [hsum, evAlgHom, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  show A.coeff γ * Complex.exp (L γ) ^ m = A.coeff γ • Complex.exp ((m : ℂ) * L γ)
  rw [smul_eq_mul, Complex.exp_nat_mul]

/-! ### Constancy of the carrier kills the symbols -/

/-- **A constant carrier annihilates every symbol of positive level.**  The phase covers `ℂ`, so
`exp ∘ L` covers the punctured plane and the dilate combination is constant on all of `ℂ`; its
`m`-th derivative at the origin is the symbol at level `m`. -/
theorem symbHom_eq_zero_of_carrier_const (ω : α → E) {L : E →+ ℂ} (hL : Function.Surjective L)
    (P : MvPolynomial α ℂ)
    (hconst : ∀ z z' : E, seedCarrierPoly ω (expSeedHom L) P z
      = seedCarrierPoly ω (expSeedHom L) P z')
    {m : ℕ} (hm : 1 ≤ m) : symbHom ω L (m : ℂ) P = 0 := by
  classical
  set A := polyShift ω P with hA
  obtain ⟨z₀, hz₀⟩ := hL 0
  set C := dilateSumHom A L (Complex.exp (L z₀)) with hC
  have hpunct : ∀ w : ℂ, w ≠ 0 → dilateSumHom A L w = C := by
    intro w hw
    obtain ⟨z, hz⟩ : ∃ z : E, Complex.exp (L z) = w := by
      obtain ⟨z, hz⟩ := hL (Complex.log w)
      exact ⟨z, by rw [hz, Complex.exp_log hw]⟩
    rw [← hz, hC, ← seedCarrierPoly_expSeedHom, ← seedCarrierPoly_expSeedHom]
    exact hconst z z₀
  have hall : ∀ w, dilateSumHom A L w = C :=
    eq_of_eq_on_punctured (differentiable_dilateSumHom A L) hpunct
  have hfun : dilateSumHom A L = fun _ => C := funext hall
  have hderiv : iteratedDeriv m (dilateSumHom A L) 0 = 0 := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hfun, iteratedDeriv_succ']
    simp
  rw [← evAlgHom_polyShift, ← hA, ← iteratedDeriv_dilateSumHom_zero A L m, hderiv]

end

end GaloisForLFunctions.HTGeometry
