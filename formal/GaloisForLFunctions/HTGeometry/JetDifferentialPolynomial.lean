import GaloisForLFunctions.HTGeometry.Hypertranscendence
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The jet differential polynomial ring

Algebraic differential relations between the successive derivatives of a single function live in
the polynomial ring `ℂ[Y₀, Y₁, …]` in countably many jet variables, equipped with the derivation
`Yₖ ↦ Yₖ₊₁`.  Two realizations are used.  Substituting the jets of an entire function at a moving
point turns the derivation into `d/dz`.  Substituting the successive derivatives of a *polynomial*
keeps everything inside `ℂ[z]`, where degrees are available.

The degree realization yields the rigidity statement the reduction of exponential relations needs:
the jet ring contains no pair whose logarithmic derivative differs by a nonzero constant.  If
`g·𝒟f − f·𝒟g = μ·f·g` with `μ ≠ 0` and `g ≠ 0`, then `f = 0`.  Indeed the two sides realize as
polynomials in one variable of degrees `< deg + deg` and `= deg + deg`.

* `GaloisForLFunctions.HTGeometry.jetDeriv`;
* `GaloisForLFunctions.HTGeometry.hasDerivAt_eval_jetVector`;
* `GaloisForLFunctions.HTGeometry.eq_zero_of_jetLogDerivative_const`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- The derivation of the jet polynomial ring sending each jet variable to the next. -/
def jetDeriv : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun k => X (k + 1)

@[simp] theorem jetDeriv_X (k : ℕ) : jetDeriv (X k) = X (k + 1) :=
  MvPolynomial.mkDerivation_X ℂ _ k

theorem jetDeriv_mul_X (p : MvPolynomial ℕ ℂ) (k : ℕ) :
    jetDeriv (p * X k) = p * X (k + 1) + X k * jetDeriv p := by
  rw [Derivation.leibniz, jetDeriv_X, smul_eq_mul, smul_eq_mul]

/-! ### The polynomial realization -/

/-- Substituting the successive derivatives of a polynomial for the jet variables. -/
def polyJetSubst (f : Polynomial ℂ) : MvPolynomial ℕ ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun k => (⇑Polynomial.derivative)^[k] f

@[simp] theorem polyJetSubst_X (f : Polynomial ℂ) (k : ℕ) :
    polyJetSubst f (X k) = (⇑Polynomial.derivative)^[k] f := by
  simp [polyJetSubst]

@[simp] theorem polyJetSubst_C (f : Polynomial ℂ) (a : ℂ) :
    polyJetSubst f (C a) = Polynomial.C a := by
  simp [polyJetSubst]

/-- The jet derivation realizes as the derivative of the polynomial realization. -/
theorem derivative_polyJetSubst (f : Polynomial ℂ) (c : MvPolynomial ℕ ℂ) :
    Polynomial.derivative (polyJetSubst f c) = polyJetSubst f (jetDeriv c) := by
  induction c using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, hp, hq, map_add, map_add]
  | mul_X p k hp =>
      have hd : Polynomial.derivative ((⇑Polynomial.derivative)^[k] f)
          = (⇑Polynomial.derivative)^[k + 1] f := (Function.iterate_succ_apply' _ _ _).symm
      rw [map_mul, polyJetSubst_X, Polynomial.derivative_mul, hp, hd, jetDeriv_mul_X, map_add,
        map_mul, map_mul, polyJetSubst_X, polyJetSubst_X]
      ring

/-! ### The analytic realization -/

/-- The jet vector of a function at a point. -/
def jetVector (f : ℂ → ℂ) (z : ℂ) : ℕ → ℂ := fun k => iteratedDeriv k f z

/-- Along the jets of an entire function the jet derivation realizes as `d/dz`. -/
theorem hasDerivAt_eval_jetVector {f : ℂ → ℂ}
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f)) (c : MvPolynomial ℕ ℂ) (z : ℂ) :
    HasDerivAt (fun w => eval (jetVector f w) c) (eval (jetVector f z) (jetDeriv c)) z := by
  induction c using MvPolynomial.induction_on with
  | C a =>
      have h0 : eval (jetVector f z) (jetDeriv (C a : MvPolynomial ℕ ℂ)) = 0 := by simp
      rw [h0]
      simpa using (hasDerivAt_const z a)
  | add p q hp hq =>
      have := hp.add hq
      simpa [map_add] using this
  | mul_X p k hp =>
      have hk : HasDerivAt (fun w => iteratedDeriv k f w) (iteratedDeriv (k + 1) f z) z := by
        have h := (hf k z).hasDerivAt
        rw [iteratedDeriv_succ]
        exact h
      have hmul := hp.mul hk
      have hgoal : eval (jetVector f z) (jetDeriv (p * X k))
          = eval (jetVector f z) (jetDeriv p) * iteratedDeriv k f z
            + eval (jetVector f z) p * iteratedDeriv (k + 1) f z := by
        rw [jetDeriv_mul_X]
        simp only [map_add, map_mul, eval_X, jetVector]
        ring
      rw [hgoal]
      have hfun : (fun w => eval (jetVector f w) (p * X k))
          = fun w => eval (jetVector f w) p * iteratedDeriv k f w := by
        funext w
        simp [jetVector]
      rw [hfun]
      exact hmul

/-! ### Realizing a prescribed jet vector by a polynomial -/

/-- The polynomial whose successive derivatives at the origin are the prescribed jet values on a
finite index set. -/
def jetPoly (s : Finset ℕ) (y : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ s, Polynomial.C (y k / (k ! : ℂ)) * Polynomial.X ^ k

theorem coeff_jetPoly (s : Finset ℕ) (y : ℕ → ℂ) {j : ℕ} (hj : j ∈ s) :
    (jetPoly s y).coeff j = y j / (j ! : ℂ) := by
  classical
  rw [jetPoly, Polynomial.finset_sum_coeff, Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hbj]
  · intro h
    exact absurd hj h

theorem eval_zero_iterate_derivative_jetPoly (s : Finset ℕ) (y : ℕ → ℂ) {j : ℕ} (hj : j ∈ s) :
    Polynomial.eval 0 ((⇑Polynomial.derivative)^[j] (jetPoly s y)) = y j := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  rw [zero_add, Nat.descFactorial_self, nsmul_eq_mul, coeff_jetPoly s y hj]
  have hfac : ((j ! : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  field_simp

/-- Evaluating the polynomial realization at the origin is evaluation at the jet values. -/
theorem eval_zero_polyJetSubst (F : Polynomial ℂ) (c : MvPolynomial ℕ ℂ) :
    Polynomial.eval 0 (polyJetSubst F c)
      = eval (fun k => Polynomial.eval 0 ((⇑Polynomial.derivative)^[k] F)) c := by
  have hext :
      (Polynomial.evalRingHom (0 : ℂ)).comp ((polyJetSubst F : MvPolynomial ℕ ℂ →+* Polynomial ℂ))
        = (MvPolynomial.eval fun k => Polynomial.eval 0 ((⇑Polynomial.derivative)^[k] F)) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r; simp
    · intro i; simp
  exact RingHom.congr_fun hext c

/-! ### The rigidity statement -/

/-- **No jet pair has constant logarithmic-derivative difference.**  If `g·𝒟f − f·𝒟g = μ·f·g`
with `μ ≠ 0` and `g ≠ 0`, then `f = 0`: realizing both sides along the derivatives of a polynomial
makes the left side of strictly smaller degree than the right. -/
theorem eq_zero_of_jetLogDerivative_const {f g : MvPolynomial ℕ ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (hg : g ≠ 0) (hrel : g * jetDeriv f - f * jetDeriv g = C μ * (f * g)) :
    f = 0 := by
  classical
  have key : ∀ y : ℕ → ℂ, eval y f * eval y g = 0 := by
    intro y
    by_cases hgy : eval y g = 0
    · rw [hgy, mul_zero]
    set s : Finset ℕ := f.vars ∪ g.vars with hsdef
    set F : Polynomial ℂ := jetPoly s y with hFdef
    set y' : ℕ → ℂ := fun k => Polynomial.eval 0 ((⇑Polynomial.derivative)^[k] F) with hy'def
    have hy's : ∀ j ∈ s, y' j = y j := fun j hj =>
      eval_zero_iterate_derivative_jetPoly s y hj
    have hagree : ∀ c : MvPolynomial ℕ ℂ, c.vars ⊆ s → eval y' c = eval y c := by
      intro c hc
      refine MvPolynomial.eval₂_congr _ _ ?_
      intro i d hid hcd
      exact hy's i (hc (MvPolynomial.mem_vars i |>.2 ⟨d, Finsupp.mem_support_iff.2 hcd, hid⟩))
    set A : Polynomial ℂ := polyJetSubst F f with hAdef
    set B : Polynomial ℂ := polyJetSubst F g with hBdef
    have hpoly : B * Polynomial.derivative A - A * Polynomial.derivative B
        = Polynomial.C μ * (A * B) := by
      have := congrArg (polyJetSubst F) hrel
      simpa only [map_sub, map_mul, derivative_polyJetSubst, polyJetSubst_C, hAdef, hBdef]
        using this
    have hB0 : Polynomial.eval 0 B = eval y g := by
      rw [hBdef, eval_zero_polyJetSubst, ← hy'def]
      exact hagree g Finset.subset_union_right
    have hBne : B ≠ 0 := by
      intro h
      rw [h] at hB0
      exact hgy (by simpa using hB0.symm)
    have hA0 : Polynomial.eval 0 A = eval y f := by
      rw [hAdef, eval_zero_polyJetSubst, ← hy'def]
      exact hagree f Finset.subset_union_left
    have hAzero : A = 0 := by
      by_contra hAne
      have hdegB : B.degree ≠ ⊥ := by
        simpa [Polynomial.degree_eq_bot] using hBne
      have hdegA : A.degree ≠ ⊥ := by
        simpa [Polynomial.degree_eq_bot] using hAne
      have h1 : (B * Polynomial.derivative A).degree < A.degree + B.degree := by
        rw [Polynomial.degree_mul, add_comm A.degree B.degree]
        exact WithBot.add_lt_add_left hdegB (Polynomial.degree_derivative_lt hAne)
      have h2 : (A * Polynomial.derivative B).degree < A.degree + B.degree := by
        rw [Polynomial.degree_mul]
        exact WithBot.add_lt_add_left hdegA (Polynomial.degree_derivative_lt hBne)
      have hlt : (B * Polynomial.derivative A - A * Polynomial.derivative B).degree
          < A.degree + B.degree :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
      have heq : (Polynomial.C μ * (A * B)).degree = A.degree + B.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_C hμ, zero_add, Polynomial.degree_mul]
      rw [hpoly, heq] at hlt
      exact lt_irrefl _ hlt
    rw [← hA0, hAzero, Polynomial.eval_zero, zero_mul]
  have hfg : f * g = 0 := by
    refine MvPolynomial.funext ?_
    intro x
    rw [map_mul, key x, map_zero]
  rcases mul_eq_zero.mp hfg with h | h
  · exact h
  · exact absurd h hg

end

end GaloisForLFunctions.HTGeometry
