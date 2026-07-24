import GaloisForLFunctions.HTGeometry.MultiplicativeMonomial
import GaloisForLFunctions.HTGeometry.ClockScalingCharacter
import GaloisForLFunctions.HTGeometry.ClockChargeFamilyMultiplicative

/-!
# Algebraic characters of `G_m` are monomials, and the charged clock is `λ^k`

The scaling character `e : C → C` of the diagonalized clock family
(`commuting_family_scaling_character`) is multiplicative.  When it is moreover *algebraic* — given
by a polynomial `e(λ) = P(λ)` — the monomial classification `multiplicative_polynomial_eq_X_pow`
forces `e(λ) = λ^k` with `k = deg P`.  This is the regular-character classification of the
multiplicative group and it delivers equation (2) of the clock-character law:
`ρ_λ q = λ^k · q`.

Chaining that into the charged-phase family rigidity `clock_charge_family_multiplicative` closes the
charged branch of the law end-to-end from the polynomial-character input: a persistent scalar
constraint commuting with an algebraically-varying clock cocharacter of positive charge is
multiplication by a single constant, `σ y = e · y`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **Multiplicative polynomial characters are monomials.**  Over an algebraically closed field, a
multiplicative map `e : C → C` given by a nonzero polynomial `e(λ) = P(λ)` is `e(λ) = λ^k`. -/
theorem multiplicative_eval_eq_pow {C : Type*} [Field C] [IsAlgClosed C]
    {P : Polynomial C} (hP : P ≠ 0) (e : C → C)
    (he : ∀ lam, e lam = P.eval lam)
    (hmul : ∀ lam mu, e (lam * mu) = e lam * e mu) :
    ∃ k : ℕ, ∀ lam, e lam = lam ^ k := by
  have hpmul : ∀ x y : C, P.eval (x * y) = P.eval x * P.eval y := by
    intro x y; rw [← he x, ← he y, ← he (x * y)]; exact hmul x y
  have hX : P = Polynomial.X ^ P.natDegree := multiplicative_polynomial_eq_X_pow hP hpmul
  refine ⟨P.natDegree, fun lam => ?_⟩
  rw [he lam]
  nth_rewrite 1 [hX]
  rw [Polynomial.eval_pow, Polynomial.eval_X]

/-- **Equation (2): the charged clock is `λ^k`.**  A clock family acting on `q` by scalings given by
a nonzero polynomial character `ρ_λ q = P(λ)·q`, and a homomorphism at `q`, acts by
`ρ_λ q = λ^k · q` with `k = deg P`. -/
theorem charged_clock_family_pow
    {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [Algebra C E]
    (ρ : C → (E →ₐ[C] E)) {q : E} (hq : q ≠ 0)
    {P : Polynomial C} (hP : P ≠ 0)
    (hpoly_scale : ∀ lam, ρ lam q = algebraMap C E (P.eval lam) * q)
    (hmul : ∀ lam mu, ρ (lam * mu) q = ρ lam (ρ mu q)) :
    ∃ k : ℕ, ∀ lam, ρ lam q = algebraMap C E (lam ^ k) * q := by
  have hpmul : ∀ x y : C, P.eval (x * y) = P.eval x * P.eval y := by
    have h := scaling_character_multiplicative ρ hq (fun lam => P.eval lam) hpoly_scale hmul
    intro x y; exact h x y
  have hX : P = Polynomial.X ^ P.natDegree := multiplicative_polynomial_eq_X_pow hP hpmul
  have hkey : ∀ lam, P.eval lam = lam ^ P.natDegree := by
    intro lam; nth_rewrite 1 [hX]; rw [Polynomial.eval_pow, Polynomial.eval_X]
  exact ⟨P.natDegree, fun lam => by rw [hpoly_scale lam, hkey lam]⟩

/-- **Charged branch, end-to-end.**  Let `σ` be a differential automorphism of a scalar free
differential field (the persistent constraint) and `ρ` a clock cocharacter, a homomorphism at the
generator `y`, whose scaling character is given by a polynomial of positive degree
`ρ_λ y = P(λ)·y`, and which commutes with `σ`.  Then `σ` is multiplication by a single constant,
`σ y = e · y`.

The polynomial character with `0 < deg P` is the positive-charge input (equation (2)); the
multiplicative-monomial classification turns it into `λ^k`, which the charged-phase family rigidity
then rigidifies to a single multiplication constant. -/
theorem charged_clock_polynomial_forces_multiplicative
    {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [CharZero E]
    [Differential C] [Differential E] [Algebra C E] [DifferentialAlgebra C E]
    (σ : E ≃ₐ[C] E) (ρ : C → (E →ₐ[C] E)) {y : E}
    (hy : HypertranscendentalOver C y)
    (hytop : differentialAdjoin C ({y} : Set E) = ⊤)
    (hderiv : ∀ w : E, σ w′ = (σ w)′)
    {P : Polynomial C} (hPdeg : 0 < P.natDegree)
    (hpoly_scale : ∀ lam, ρ lam y = algebraMap C E (P.eval lam) * y)
    (hmulρ : ∀ lam mu, ρ (lam * mu) y = ρ lam (ρ mu y))
    (hcomm : ∀ lam, σ.toAlgHom ((ρ lam) y) = (ρ lam) (σ.toAlgHom y)) :
    ∃ e : C, σ y = algebraMap C E e * y := by
  have htrans : Transcendental C y := by
    simpa using hypertranscendentalOver_jet_transcendental hy 0
  have hq : y ≠ 0 := by rintro rfl; exact htrans isAlgebraic_zero
  have hP : P ≠ 0 := by rintro rfl; simp at hPdeg
  have hpmul : ∀ x y : C, P.eval (x * y) = P.eval x * P.eval y := by
    have h := scaling_character_multiplicative ρ hq (fun lam => P.eval lam) hpoly_scale hmulρ
    intro x y; exact h x y
  have hX : P = Polynomial.X ^ P.natDegree := multiplicative_polynomial_eq_X_pow hP hpmul
  have hρpow : ∀ lam, ρ lam y = algebraMap C E (lam ^ P.natDegree) * y := by
    intro lam
    rw [hpoly_scale lam]
    congr 2
    nth_rewrite 1 [hX]
    rw [Polynomial.eval_pow, Polynomial.eval_X]
  exact clock_charge_family_multiplicative σ ρ hPdeg hy hytop hderiv hρpow hcomm

end GaloisForLFunctions.HTGeometry
