import GaloisForLFunctions.HTGeometry.SRDifferenceCarrier
import GaloisForLFunctions.HTGeometry.CompExpDescent

/-!
# The exponential seed and its difference-operator carriers

`doubleExpSeed a z = exp (exp (a z))` is entire and has period `2πi / a`, so a step `c` with
`a = 2πi / c` is annihilated by the difference operator it generates.  Translating the argument
dilates the inner exponential, so the carrier of a polynomial is a finite combination of dilates of
`exp`, read at `exp (a z)`:

`seedCarrierPoly step (doubleExpSeed a) P z = dilateSum (polyShift step P) a (exp (a z))`.

Because `exp (a ·)` is onto `ℂ ∖ {0}`, a constant carrier forces the dilate combination to be
constant on the whole plane, and its Taylor coefficients at the origin are exactly the values of the
polynomial at the *symbols* `exp (t · step j) − 1`.  That converts constancy of a carrier into the
vanishing of a whole arithmetic progression of symbol values.

* `symb step t P` — the symbol of `P` at the parameter `t`;
* `evAlg_polyShift` — the symbol is the character `⟨γ⟩ ↦ exp (t γ)` applied to the operator;
* `seedCarrierPoly_doubleExpSeed` — the carrier as a dilate combination;
* `symb_eq_zero_of_carrier_const` — a constant carrier kills every symbol at `t = m a`, `m ≥ 1`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The seed -/

/-- The exponential seed: entire, with period `2πi / a`. -/
def doubleExpSeed (a : ℂ) : ℂ → ℂ := fun z => Complex.exp (Complex.exp (a * z))

theorem differentiable_doubleExpSeed (a : ℂ) : Differentiable ℂ (doubleExpSeed a) :=
  Complex.differentiable_exp.comp (Complex.differentiable_exp.comp (differentiable_id.const_mul a))

theorem periodic_doubleExpSeed {a : ℂ} (ha : a ≠ 0) :
    Function.Periodic (doubleExpSeed a) (2 * Real.pi * Complex.I / a) :=
  periodic_comp_exp Complex.exp ha

/-! ### The character of a shift parameter -/

/-- The multiplicative character `γ ↦ exp (t γ)` of the additive group of shifts. -/
def dilateChar (t : ℂ) : Multiplicative ℂ →* ℂ where
  toFun g := Complex.exp (t * Multiplicative.toAdd g)
  map_one' := by simp
  map_mul' a b := by
    show Complex.exp (t * (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [mul_add, Complex.exp_add]

/-- The induced algebra map on the group algebra of shifts. -/
def evAlg (t : ℂ) : AddMonoidAlgebra ℂ ℂ →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ ℂ (dilateChar t)

@[simp] theorem evAlg_single (t γ c : ℂ) :
    evAlg t (AddMonoidAlgebra.single γ c) = c * Complex.exp (t * γ) := by
  rw [evAlg, AddMonoidAlgebra.lift_single]
  simp [dilateChar, smul_eq_mul]

/-- **The symbol of a polynomial.**  The value of `P` at the difference-operator eigenvalues
`exp (t · step j) − 1`. -/
def symb {α : Type*} (step : α → ℂ) (t : ℂ) (P : MvPolynomial α ℂ) : ℂ :=
  aeval (fun j => Complex.exp (t * step j) - 1) P

/-- The character evaluated on the operator of `P` is the symbol of `P`. -/
theorem evAlg_polyShift {α : Type*} (step : α → ℂ) (t : ℂ) (P : MvPolynomial α ℂ) :
    evAlg t (polyShift step P) = symb step t P := by
  have h := MvPolynomial.comp_aeval (R := ℂ) (stepVar step) (evAlg t)
  have happ := congrArg (fun f => f P) h
  simp only [AlgHom.comp_apply] at happ
  have hpt : (fun i => evAlg t (stepVar step i))
      = fun j => Complex.exp (t * step j) - 1 := by
    funext j
    rw [stepVar, map_sub, evAlg_single, map_one, one_mul]
  rw [polyShift, happ, symb, hpt]

theorem symb_mul {α : Type*} (step : α → ℂ) (t : ℂ) (P Q : MvPolynomial α ℂ) :
    symb step t (P * Q) = symb step t P * symb step t Q := by
  simp [symb]

theorem symb_prod_X {α : Type*} [DecidableEq α] (step : α → ℂ) (t : ℂ) (J : Finset α) :
    symb step t (∏ j ∈ J, X j) = ∏ j ∈ J, (Complex.exp (t * step j) - 1) := by
  simp [symb]

/-! ### The carrier as a combination of dilates -/

/-- A finite combination of dilates of `exp`, indexed by the shift parameters of an operator. -/
def dilateSum (A : AddMonoidAlgebra ℂ ℂ) (a : ℂ) : ℂ → ℂ :=
  fun w => ∑ γ ∈ A.coeff.support, A.coeff γ * Complex.exp (Complex.exp (a * γ) * w)

theorem differentiable_dilateSum (A : AddMonoidAlgebra ℂ ℂ) (a : ℂ) :
    Differentiable ℂ (dilateSum A a) :=
  Differentiable.fun_sum fun _ _ =>
    (Complex.differentiable_exp.comp (differentiable_id.const_mul _)).const_mul _

/-- **The carrier of the exponential seed.**  Translating the argument dilates the inner
exponential. -/
theorem seedCarrierPoly_doubleExpSeed {α : Type*} (step : α → ℂ) (a : ℂ) (P : MvPolynomial α ℂ)
    (z : ℂ) :
    seedCarrierPoly step (doubleExpSeed a) P z
      = dilateSum (polyShift step P) a (Complex.exp (a * z)) := by
  rw [seedCarrierPoly, shiftAlgHom_apply, dilateSum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1
  show Complex.exp (Complex.exp (a * (z + γ))) = _
  rw [mul_add, Complex.exp_add, mul_comm (Complex.exp (a * z))]

/-! ### Iterated derivatives at the origin -/

theorem iteratedDeriv_constMul_expLinear (c g : ℂ) (m : ℕ) :
    iteratedDeriv m (fun w : ℂ => c * Complex.exp (g * w))
      = fun w => c * g ^ m * Complex.exp (g * w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    have hd : HasDerivAt (fun w : ℂ => Complex.exp (g * w)) (g * Complex.exp (g * w)) w := by
      have h : HasDerivAt (fun w : ℂ => g * w) g w := by simpa using (hasDerivAt_id w).const_mul g
      simpa [mul_comm] using h.cexp
    rw [deriv_const_mul _ hd.differentiableAt, hd.deriv]
    ring

theorem iteratedDeriv_dilateSum_zero (A : AddMonoidAlgebra ℂ ℂ) (a : ℂ) (m : ℕ) :
    iteratedDeriv m (dilateSum A a) 0 = evAlg ((m : ℂ) * a) A := by
  have hsum : iteratedDeriv m (dilateSum A a) 0
      = ∑ γ ∈ A.coeff.support, A.coeff γ * (Complex.exp (a * γ)) ^ m := by
    have hfun : dilateSum A a
        = fun w => ∑ γ ∈ A.coeff.support,
            A.coeff γ * Complex.exp (Complex.exp (a * γ) * w) := rfl
    rw [hfun, iteratedDeriv_eq_iteratedFDeriv]
    have hcd : ∀ γ ∈ A.coeff.support,
        ContDiff ℂ (m : ℕ∞) fun w : ℂ => A.coeff γ * Complex.exp (Complex.exp (a * γ) * w) :=
      fun γ _ => contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    rw [iteratedFDeriv_sum hcd]
    simp only [Finset.sum_apply, _root_.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_constMul_expLinear]
    simp
  rw [hsum, evAlg, AddMonoidAlgebra.lift_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  show A.coeff γ * Complex.exp (a * γ) ^ m = A.coeff γ • Complex.exp ((m : ℂ) * a * γ)
  rw [smul_eq_mul, mul_assoc, Complex.exp_nat_mul]

/-! ### Constancy of the carrier kills the symbols -/

/-- An entire function constant off the origin is constant. -/
theorem eq_of_eq_on_punctured {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℂ}
    (h : ∀ w : ℂ, w ≠ 0 → f w = C) : ∀ w, f w = C := by
  intro w
  by_cases hw : w = 0
  · subst hw
    have hcont : ContinuousAt f 0 := (hf 0).continuousAt
    have h1 : Filter.Tendsto f (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (f 0)) :=
      hcont.continuousWithinAt.tendsto
    have h2 : Filter.Tendsto f (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds C) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (h x hx).symm
    exact tendsto_nhds_unique h1 h2
  · exact h w hw

/-- **A constant carrier annihilates every symbol along the arithmetic progression `m a`.**
Composition with `exp (a ·)` covers the punctured plane, so the dilate combination is constant on
all of `ℂ`, and its `m`-th derivative at the origin is the symbol at `m a`. -/
theorem symb_eq_zero_of_carrier_const {α : Type*} (step : α → ℂ) {a : ℂ} (ha : a ≠ 0)
    (P : MvPolynomial α ℂ)
    (hconst : ∀ z z' : ℂ, seedCarrierPoly step (doubleExpSeed a) P z
      = seedCarrierPoly step (doubleExpSeed a) P z')
    {m : ℕ} (hm : 1 ≤ m) : symb step ((m : ℂ) * a) P = 0 := by
  set A := polyShift step P with hA
  set C := dilateSum A a (Complex.exp (a * 0)) with hC
  have hpunct : ∀ w : ℂ, w ≠ 0 → dilateSum A a w = C := by
    intro w hw
    obtain ⟨z, hz⟩ : ∃ z : ℂ, Complex.exp (a * z) = w :=
      ⟨Complex.log w / a, by rw [mul_div_cancel₀ _ ha, Complex.exp_log hw]⟩
    rw [← hz, hC, ← seedCarrierPoly_doubleExpSeed, ← seedCarrierPoly_doubleExpSeed]
    exact hconst z 0
  have hall : ∀ w, dilateSum A a w = C :=
    eq_of_eq_on_punctured (differentiable_dilateSum A a) hpunct
  have hfun : dilateSum A a = fun _ => C := funext hall
  have hderiv : iteratedDeriv m (dilateSum A a) 0 = 0 := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hfun, iteratedDeriv_succ']
    simp
  rw [← evAlg_polyShift, ← hA, ← iteratedDeriv_dilateSum_zero A a m, hderiv]

end

end GaloisForLFunctions.HTGeometry
