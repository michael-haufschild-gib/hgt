import GaloisForLFunctions.HTGeometry.RationalPolarCalculus

/-!
# Functoriality of connection pullbacks, and the chart at infinity

The affine-connection pullback `P^*a = a(P)·P' + P''/P'` and the projective-connection pullback
`P^*γ = γ(P)·P'² + S(P)` are contravariantly functorial for composition of rational maps:

`(P ∘ Q)^* = Q^* ∘ P^*`,

by the chain rule for the derivative, the multiplicativity of the logarithmic derivative, and the
chain rule `S(P ∘ Q) = S(P)(Q)·Q'² + S(Q)` of the Schwarzian.  The identity pulls back trivially,
and
the inversion `ι(x) = 1/x` is an involution.  So the local data of a connection at `∞` are those of
`ι^*a` at `0`, and an `R`-invariant connection has `ι^*a` invariant under the conjugates of `R`.

At `0` the substitution `f(1/x)` has order `deg(denominator) − deg(numerator)`: the reversed
polynomial does not vanish at `0`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-! ### Composition -/

omit [CharZero K] in
theorem nonconst_subst {P Q : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (hQ : ¬ ∃ c : K, Q = RatFunc.C c) :
    ¬ ∃ c : K, ratFuncSubstitutionAlgHom Q hQ P = RatFunc.C c := by
  rintro ⟨c, hc⟩
  apply hP
  refine ⟨c, (ratFuncSubstitutionAlgHom Q hQ).toRingHom.injective ?_⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [hc, ratFuncSubstitutionAlgHom_C]

theorem logDerivRat_subst {Q : RatFunc K} (hQ : ¬ ∃ c : K, Q = RatFunc.C c) (f : RatFunc K) :
    logDerivRat (ratFuncSubstitutionAlgHom Q hQ f)
      = ratFuncSubstitutionAlgHom Q hQ (logDerivRat f) * ratFuncDeriv Q := by
  rw [logDerivRat, logDerivRat, ratFuncDeriv_substitution, map_div₀]
  ring

/-- **Functoriality of the affine-connection pullback.** -/
theorem connPull_comp {P Q : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (hQ : ¬ ∃ c : K, Q = RatFunc.C c)
    (hPQ : ¬ ∃ c : K, ratFuncSubstitutionAlgHom Q hQ P = RatFunc.C c)
    (hQd : ratFuncDeriv Q ≠ 0) (hPd : ratFuncDeriv P ≠ 0) (a : RatFunc K) :
    connPull (ratFuncSubstitutionAlgHom Q hQ P) hPQ a = connPull Q hQ (connPull P hP a) := by
  have hsubP : ratFuncSubstitutionAlgHom Q hQ (ratFuncDeriv P) ≠ 0 := by
    intro h
    exact hPd ((ratFuncSubstitutionAlgHom Q hQ).toRingHom.injective (by simpa using h))
  rw [connPull, connPull, connPull, ratFuncDeriv_substitution,
    ← ratFuncSubstitutionAlgHom_comp hQ hP hPQ, logDerivRat_mul hsubP hQd, logDerivRat_subst,
    map_add, map_mul]
  ring

/-- The Schwarzian chain rule. -/
theorem schwarzRat_comp {P Q : RatFunc K} (hQ : ¬ ∃ c : K, Q = RatFunc.C c)
    (hQd : ratFuncDeriv Q ≠ 0) (hPd : ratFuncDeriv P ≠ 0) :
    schwarzRat (ratFuncSubstitutionAlgHom Q hQ P)
      = ratFuncSubstitutionAlgHom Q hQ (schwarzRat P) * ratFuncDeriv Q ^ 2 + schwarzRat Q := by
  have hsubP : ratFuncSubstitutionAlgHom Q hQ (ratFuncDeriv P) ≠ 0 := by
    intro h
    exact hPd ((ratFuncSubstitutionAlgHom Q hQ).toRingHom.injective (by simpa using h))
  have hℓ : logDerivRat (ratFuncDeriv (ratFuncSubstitutionAlgHom Q hQ P))
      = ratFuncSubstitutionAlgHom Q hQ (logDerivRat (ratFuncDeriv P)) * ratFuncDeriv Q
        + logDerivRat (ratFuncDeriv Q) := by
    rw [ratFuncDeriv_substitution, logDerivRat_mul hsubP hQd, logDerivRat_subst]
  have hQ'' : ratFuncDeriv (ratFuncDeriv Q) = logDerivRat (ratFuncDeriv Q) * ratFuncDeriv Q := by
    rw [logDerivRat]; field_simp
  rw [schwarzRat, schwarzRat, schwarzRat, hℓ, ratFuncDeriv_add, ratFuncDeriv_mul,
    ratFuncDeriv_substitution, hQ'', map_sub, map_div₀, map_pow, map_ofNat]
  ring

/-- **Functoriality of the projective-connection pullback.** -/
theorem projPull_comp {P Q : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (hQ : ¬ ∃ c : K, Q = RatFunc.C c)
    (hPQ : ¬ ∃ c : K, ratFuncSubstitutionAlgHom Q hQ P = RatFunc.C c)
    (hQd : ratFuncDeriv Q ≠ 0) (hPd : ratFuncDeriv P ≠ 0) (γ : RatFunc K) :
    projPull (ratFuncSubstitutionAlgHom Q hQ P) hPQ γ = projPull Q hQ (projPull P hP γ) := by
  rw [projPull, projPull, projPull, ratFuncDeriv_substitution,
    ← ratFuncSubstitutionAlgHom_comp hQ hP hPQ, schwarzRat_comp hQ hQd hPd, map_add, map_mul,
    map_pow]
  ring

/-! ### The identity and the inversion -/

omit [CharZero K] in
theorem nonconst_X : ¬ ∃ c : K, (RatFunc.X : RatFunc K) = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have := congrArg (fun f : RatFunc K => f.num.natDegree) hc
  simp at this

omit [CharZero K] in
theorem subst_X_eq (f : RatFunc K) : ratFuncSubstitutionAlgHom RatFunc.X nonconst_X f = f := by
  have h : ratFuncSubstitutionAlgHom RatFunc.X (nonconst_X (K := K)) = AlgHom.id K _ :=
    ratFunc_algHom_ext (by simp)
  rw [h]
  rfl

theorem logDerivRat_one : logDerivRat (1 : RatFunc K) = 0 := by
  rw [logDerivRat, ← ratFuncDerivation_apply, Derivation.map_one_eq_zero, zero_div]

theorem connPull_X (a : RatFunc K) : connPull RatFunc.X nonconst_X a = a := by
  rw [connPull, subst_X_eq, ratFuncDeriv_X, mul_one, logDerivRat_one, add_zero]

theorem schwarzRat_X : schwarzRat (RatFunc.X : RatFunc K) = 0 := by
  rw [schwarzRat, ratFuncDeriv_X, logDerivRat_one, ← ratFuncDerivation_apply, map_zero]
  ring

theorem projPull_X (γ : RatFunc K) : projPull RatFunc.X nonconst_X γ = γ := by
  rw [projPull, subst_X_eq, ratFuncDeriv_X, one_pow, mul_one, schwarzRat_X, add_zero]

/-- The inversion `x ↦ 1/x`. -/
def invX : RatFunc K := RatFunc.X⁻¹

omit [CharZero K] in
theorem X_ne_zero' : (RatFunc.X : RatFunc K) ≠ 0 := by
  intro h
  have := congrArg (fun f : RatFunc K => f.num.natDegree) h
  simp at this

omit [CharZero K] in
theorem nonconst_invX : ¬ ∃ c : K, (invX : RatFunc K) = RatFunc.C c := by
  rintro ⟨c, hc⟩
  apply nonconst_X (K := K)
  refine ⟨c⁻¹, ?_⟩
  have hX : (RatFunc.X : RatFunc K) = (invX)⁻¹ := by simp [invX]
  rw [hX, hc, map_inv₀]

omit [CharZero K] in
theorem subst_invX_invX :
    ratFuncSubstitutionAlgHom invX nonconst_invX (invX : RatFunc K) = RatFunc.X := by
  calc ratFuncSubstitutionAlgHom invX nonconst_invX (invX : RatFunc K)
        = ratFuncSubstitutionAlgHom invX nonconst_invX ((RatFunc.X : RatFunc K)⁻¹) := rfl
    _ = (ratFuncSubstitutionAlgHom invX nonconst_invX (RatFunc.X : RatFunc K))⁻¹ := map_inv₀ _ _
    _ = (invX : RatFunc K)⁻¹ := by rw [ratFuncSubstitutionAlgHom_X]
    _ = RatFunc.X := by simp [invX]

theorem ratFuncDeriv_invX : ratFuncDeriv (invX : RatFunc K) = -(RatFunc.X ^ 2)⁻¹ := by
  show ratFuncDeriv ((RatFunc.X : RatFunc K)⁻¹) = _
  rw [inv_eq_one_div, ratFuncDeriv_div_general X_ne_zero', ratFuncDeriv_X,
    ← ratFuncDerivation_apply, Derivation.map_one_eq_zero]
  field_simp
  ring

theorem ratFuncDeriv_invX_ne_zero : ratFuncDeriv (invX : RatFunc K) ≠ 0 := by
  rw [ratFuncDeriv_invX]
  exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ X_ne_zero'))

/-- **The inversion is an involution for connections.** -/
theorem connPull_invX_invX (a : RatFunc K) :
    connPull invX nonconst_invX (connPull invX nonconst_invX a) = a := by
  rw [← connPull_comp nonconst_invX nonconst_invX (by rw [subst_invX_invX]; exact nonconst_X)
    ratFuncDeriv_invX_ne_zero ratFuncDeriv_invX_ne_zero]
  have h := connPull_X a
  convert h using 2
  exact subst_invX_invX

/-- **The inversion is an involution for projective connections.** -/
theorem projPull_invX_invX (γ : RatFunc K) :
    projPull invX nonconst_invX (projPull invX nonconst_invX γ) = γ := by
  rw [← projPull_comp nonconst_invX nonconst_invX (by rw [subst_invX_invX]; exact nonconst_X)
    ratFuncDeriv_invX_ne_zero ratFuncDeriv_invX_ne_zero]
  have h := projPull_X γ
  convert h using 2
  exact subst_invX_invX

/-! ### Orders at infinity -/

omit [CharZero K] in
theorem subst_invX_algebraMap (p : K[X]) :
    ratFuncSubstitutionAlgHom invX nonconst_invX (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) p.reverse * (RatFunc.X ^ p.natDegree)⁻¹ := by
  rw [ratFuncSubstitutionAlgHom_aeval]
  show Polynomial.aeval ((RatFunc.X : RatFunc K)⁻¹) p = _
  rw [← inv_pow]
  haveI : Invertible ((RatFunc.X : RatFunc K)⁻¹) := invertibleOfNonzero (inv_ne_zero X_ne_zero')
  have h := Polynomial.eval₂_reverse_mul_pow (algebraMap K (RatFunc K))
    ((RatFunc.X : RatFunc K)⁻¹) p
  rw [invOf_eq_inv, inv_inv] at h
  rw [Polynomial.aeval_def, ← h, algebraMap_eq_aeval_X, Polynomial.aeval_def]

omit [CharZero K] in
theorem ratOrder_reverse_zero {p : K[X]} (hp : p ≠ 0) :
    ratOrder (algebraMap K[X] (RatFunc K) p.reverse) 0 = 0 := by
  rw [ratOrder_algebraMap, Polynomial.rootMultiplicity_eq_zero]
  · rfl
  · rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp

omit [CharZero K] in
theorem ratOrder_X_pow_zero (m : ℕ) : ratOrder ((RatFunc.X : RatFunc K) ^ m) 0 = m := by
  have : (RatFunc.X : RatFunc K) ^ m = algebraMap K[X] (RatFunc K) (Polynomial.X ^ m) := by simp
  rw [this, ratOrder_algebraMap,
    show (Polynomial.X ^ m : K[X]) = (Polynomial.X - Polynomial.C 0) ^ m
    by simp, Polynomial.rootMultiplicity_X_sub_C_pow]

omit [CharZero K] in
/-- **The order at infinity.**  `f(1/x)` has order `deg(denominator) − deg(numerator)` at `0`. -/
theorem ratOrder_subst_invX {f : RatFunc K} (hf : f ≠ 0) :
    ratOrder (ratFuncSubstitutionAlgHom invX nonconst_invX f) 0
      = (f.denom.natDegree : ℤ) - f.num.natDegree := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hfeq : f = algebraMap K[X] (RatFunc K) f.num * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ :=
    eq_num_div_denom f
  have hr : ∀ p : K[X], p ≠ 0 → algebraMap K[X] (RatFunc K) p.reverse ≠ 0 := fun p hp =>
    algebraMap_ne_zero_of_ne_zero (fun h => hp (Polynomial.reverse_eq_zero.mp h))
  have hXp : ∀ m : ℕ, ((RatFunc.X : RatFunc K) ^ m)⁻¹ ≠ 0 := fun m =>
    inv_ne_zero (pow_ne_zero _ X_ne_zero')
  conv_lhs => rw [hfeq]
  rw [map_mul, map_inv₀, subst_invX_algebraMap, subst_invX_algebraMap, mul_inv, inv_inv,
    ratOrder_mul (mul_ne_zero (hr _ hnum) (hXp _))
      (mul_ne_zero (inv_ne_zero (hr _ hden)) (pow_ne_zero _ X_ne_zero')),
    ratOrder_mul (hr _ hnum) (hXp _),
    ratOrder_mul (inv_ne_zero (hr _ hden)) (pow_ne_zero _ X_ne_zero'),
    ratOrder_inv (hr _ hden), ratOrder_inv (pow_ne_zero _ X_ne_zero'),
    ratOrder_reverse_zero hnum, ratOrder_reverse_zero hden, ratOrder_X_pow_zero,
    ratOrder_X_pow_zero]
  ring

end

end GaloisForLFunctions.HTGeometry
