import GaloisForLFunctions.HTGeometry.Hypertranscendence
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# The jet differential polynomial ring

Differential relations between the successive derivatives of one function live in the polynomial
ring `ℂ[Y₀, Y₁, …]` in countably many jet variables, carrying the derivation `Yₖ ↦ Yₖ₊₁`.  Two
realizations of that ring are used here.  Substituting the jets of a smooth function at a moving
point turns the derivation into `d/dz`.  Substituting the jets of a *polynomial* keeps everything
inside `ℂ[z]`, where degrees are available, and every jet vector is realized by a polynomial.

The degree realization gives the central rigidity statement: the jet ring contains no element whose
logarithmic derivative is a nonzero constant.  Concretely, `g·𝒟f − f·𝒟g = μ·f·g` with `μ ≠ 0` and
`g ≠ 0` forces `f = 0`, because the corresponding identity between polynomials in one variable has
strictly smaller degree on the left than on the right.

* `GaloisForLFunctions.HTGeometry.JetRing.jetDeriv`;
* `GaloisForLFunctions.HTGeometry.JetRing.hasDerivAt_eval_jetVector`;
* `GaloisForLFunctions.HTGeometry.JetRing.eq_zero_of_jetLogDeriv_const`.
-/

namespace GaloisForLFunctions.HTGeometry.JetRing

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

/-- **The jet derivation is the derivative of the polynomial realization.** -/
theorem derivative_polyJetSubst (f : Polynomial ℂ) (c : MvPolynomial ℕ ℂ) :
    Polynomial.derivative (polyJetSubst f c) = polyJetSubst f (jetDeriv c) := by
  induction c using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
      have hd : Polynomial.derivative ((⇑Polynomial.derivative)^[k] f)
          = (⇑Polynomial.derivative)^[k + 1] f := (Function.iterate_succ_apply' _ _ _).symm
      rw [map_mul, polyJetSubst_X, Polynomial.derivative_mul, hp, hd, jetDeriv_mul_X, map_add,
        map_mul, map_mul, polyJetSubst_X, polyJetSubst_X]
      ring

/-! ### The analytic realization -/

/-- The jet vector of a function at a point. -/
def jetVector (f : ℂ → ℂ) (z : ℂ) : ℕ → ℂ := fun k => iteratedDeriv k f z

/-- **The jet derivation is differentiation of the analytic realization.**  For a function all of
whose iterated derivatives are differentiable, evaluating a jet polynomial along the moving jet
vector is differentiable, with derivative the evaluation of the jet derivative. -/
theorem hasDerivAt_eval_jetVector {f : ℂ → ℂ}
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f)) (c : MvPolynomial ℕ ℂ) (z : ℂ) :
    HasDerivAt (fun w => eval (jetVector f w) c) (eval (jetVector f z) (jetDeriv c)) z := by
  induction c using MvPolynomial.induction_on with
  | C a =>
      have h0 : jetDeriv (C a : MvPolynomial ℕ ℂ) = 0 := by simp
      simp only [eval_C, h0, map_zero]
      exact hasDerivAt_const z a
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p k hp =>
      have hk : HasDerivAt (fun w => iteratedDeriv k f w) (iteratedDeriv (k + 1) f z) z := by
        have h := (hf k z).hasDerivAt
        rw [iteratedDeriv_succ]
        exact h
      have hmul : HasDerivAt (fun w => (eval (jetVector f w) p) * iteratedDeriv k f w)
          (eval (jetVector f z) (jetDeriv p) * iteratedDeriv k f z
            + eval (jetVector f z) p * iteratedDeriv (k + 1) f z) z := hp.mul hk
      have hgoal : (fun w => eval (jetVector f w) (p * X k))
          = fun w => (eval (jetVector f w) p) * iteratedDeriv k f w := by
        funext w
        simp [jetVector]
      have hval : eval (jetVector f z) (jetDeriv (p * X k))
          = eval (jetVector f z) (jetDeriv p) * iteratedDeriv k f z
            + eval (jetVector f z) p * iteratedDeriv (k + 1) f z := by
        rw [jetDeriv_mul_X]
        simp only [map_add, eval_mul, eval_X, jetVector]
        ring
      rw [hgoal, hval]
      exact hmul

/-! ### Realizing a prescribed jet vector -/

/-- The polynomial whose jets at the origin are a prescribed vector on a finite index set. -/
def jetPoly (s : Finset ℕ) (y : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ s, Polynomial.C (y k / (Nat.factorial k : ℂ)) * Polynomial.X ^ k

theorem coeff_jetPoly (s : Finset ℕ) (y : ℕ → ℂ) {j : ℕ} (hj : j ∈ s) :
    (jetPoly s y).coeff j = y j / (Nat.factorial j : ℂ) := by
  classical
  rw [jetPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hbj]
  · intro h
    exact absurd hj h

theorem eval_zero_iterate_derivative_jetPoly (s : Finset ℕ) (y : ℕ → ℂ) {j : ℕ} (hj : j ∈ s) :
    Polynomial.eval 0 ((⇑Polynomial.derivative)^[j] (jetPoly s y)) = y j := by
  have hfac : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [coeff_jetPoly s y hj]
  field_simp

/-- Two jet vectors agreeing on the occurring variables give the same evaluation. -/
theorem eval_congr_vars {p : MvPolynomial ℕ ℂ} {y₁ y₂ : ℕ → ℂ}
    (h : ∀ i ∈ p.vars, y₁ i = y₂ i) : eval y₁ p = eval y₂ p := by
  show MvPolynomial.eval₂ (RingHom.id ℂ) y₁ p = MvPolynomial.eval₂ (RingHom.id ℂ) y₂ p
  refine MvPolynomial.eval₂_congr (RingHom.id ℂ) y₁ y₂ ?_
  intro i c hic hc
  exact h i (MvPolynomial.mem_vars_iff_mem_support i |>.2 ⟨c, MvPolynomial.mem_support_iff.2 hc, hic⟩)

/-- Evaluation at the origin of the polynomial realization is evaluation at the jets at the
origin. -/
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

/-! ### Rigidity of the logarithmic derivative -/

/-- **No jet polynomial has a nonzero constant logarithmic derivative.**  If `g ≠ 0` and
`g·𝒟f − f·𝒟g = μ·f·g` with `μ ≠ 0`, then `f = 0`.

Substituting the jets of a polynomial turns the identity into one between polynomials in a single
variable.  The left side is a difference of products in which one factor is differentiated, so it
has strictly smaller degree than the product on the right, which forces one of the two realizations
to vanish.  Since every jet vector is realized, `f` vanishes wherever `g` does not, and hence
everywhere. -/
theorem eq_zero_of_jetLogDeriv_const {f g : MvPolynomial ℕ ℂ} {μ : ℂ} (hμ : μ ≠ 0) (hg : g ≠ 0)
    (hrel : g * jetDeriv f - f * jetDeriv g = C μ * (f * g)) :
    f = 0 := by
  classical
  have key : ∀ y : ℕ → ℂ, eval y f * eval y g = 0 := by
    intro y
    by_cases hgy : eval y g = 0
    · rw [hgy, mul_zero]
    set s : Finset ℕ := f.vars ∪ g.vars with hs
    set F : Polynomial ℂ := jetPoly s y with hF
    set y' : ℕ → ℂ := fun k => Polynomial.eval 0 ((⇑Polynomial.derivative)^[k] F) with hy'
    have hy'mem : ∀ k ∈ s, y' k = y k := fun k hk =>
      eval_zero_iterate_derivative_jetPoly s y hk
    have hevalf : eval y' f = eval y f :=
      eval_congr_vars fun i hi => hy'mem i (Finset.mem_union_left _ hi)
    have hevalg : eval y' g = eval y g :=
      eval_congr_vars fun i hi => hy'mem i (Finset.mem_union_right _ hi)
    set A : Polynomial ℂ := polyJetSubst F f with hA
    set B : Polynomial ℂ := polyJetSubst F g with hB
    have hA0 : Polynomial.eval 0 A = eval y f := by
      rw [hA, eval_zero_polyJetSubst, ← hy', hevalf]
    have hB0 : Polynomial.eval 0 B = eval y g := by
      rw [hB, eval_zero_polyJetSubst, ← hy', hevalg]
    have hBne : B ≠ 0 := by
      intro h
      rw [h] at hB0
      simp only [Polynomial.eval_zero] at hB0
      exact hgy hB0.symm
    have hpoly : B * Polynomial.derivative A - A * Polynomial.derivative B
        = Polynomial.C μ * (A * B) := by
      have := congrArg (polyJetSubst F) hrel
      simpa only [map_sub, map_mul, derivative_polyJetSubst, polyJetSubst_C, hA, hB] using this
    have hAzero : A = 0 := by
      by_contra hAne
      have hdegB : B.degree ≠ ⊥ := Polynomial.degree_ne_bot.2 hBne
      have hdegA : A.degree ≠ ⊥ := Polynomial.degree_ne_bot.2 hAne
      have h1 : (B * Polynomial.derivative A).degree < B.degree + A.degree := by
        rw [Polynomial.degree_mul]
        exact WithBot.add_lt_add_left hdegB (Polynomial.degree_derivative_lt hAne)
      have h2 : (A * Polynomial.derivative B).degree < B.degree + A.degree := by
        rw [Polynomial.degree_mul]
        have := WithBot.add_lt_add_left hdegA (Polynomial.degree_derivative_lt hBne)
        calc A.degree + (Polynomial.derivative B).degree < A.degree + B.degree := this
          _ = B.degree + A.degree := add_comm _ _
      have hleft : (B * Polynomial.derivative A - A * Polynomial.derivative B).degree
          < B.degree + A.degree :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
      have hright : (Polynomial.C μ * (A * B)).degree = B.degree + A.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_C hμ, Polynomial.degree_mul, zero_add,
          add_comm]
      rw [hpoly, hright] at hleft
      exact lt_irrefl _ hleft
    rw [← hA0, hAzero, Polynomial.eval_zero, zero_mul]
  have hfg : f * g = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, key x, map_zero]
  rcases mul_eq_zero.1 hfg with h | h
  · exact h
  · exact absurd h hg

end

end GaloisForLFunctions.HTGeometry.JetRing
