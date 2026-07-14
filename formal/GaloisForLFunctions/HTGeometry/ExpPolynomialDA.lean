import GaloisForLFunctions.HTGeometry.Hypertranscendence
import GaloisForLFunctions.HTGeometry.HypertranscendencePolynomial

/-!
# Exponential-times-polynomial is differentially algebraic

The differentially-algebraic direction of the signed-Gamma orbit-charge dichotomy
(`signed-archimedean-gamma-orbit-charge-phase-law`, §3, eqs. 8–10): when every shift-orbit charge
vanishes the product reduces to `G(s) = C₀·e^{βs}·R(s)` with `R` rational, which satisfies the
first-order linear differential equation `G' = (β + R'/R)·G` and is therefore differentially algebraic.

Here the polynomial case `R = P` is proved directly: `e^{βs}·P(s)` satisfies the order-1 relation
`P·G' − (β·P + P')·G = 0`, exhibited as the differential polynomial `P(X₀)·X₂ − (β·P(X₀) + P'(X₀))·X₁`
in `MvPolynomial (Fin 3) ℂ`.
-/

open scoped Polynomial

namespace GaloisForLFunctions

private theorem evalX0f3 (P : Polynomial ℂ) (g : Fin 3 → ℂ) :
    MvPolynomial.eval g (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ) P)
      = P.eval (g 0) := by
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp

/-- **`e^{βs}·P(s)` is differentially algebraic** for any polynomial `P` — the DA direction of the
orbit-charge dichotomy `(8)` in the polynomial case, via the order-1 relation `P·G' − (βP + P')·G = 0`. -/
theorem differentiallyAlgebraic_cexp_mul_polynomial (β : ℂ) (P : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun s => Complex.exp (β * s) * P.eval s) := by
  rcases eq_or_ne P 0 with hP0 | hP0
  · subst hP0; simpa using differentiallyAlgebraic_const 0
  have key : ∀ g : Fin 3 → ℂ, MvPolynomial.eval g
      ((Polynomial.aeval (MvPolynomial.X 0) P) * MvPolynomial.X 2
        - (MvPolynomial.C β * (Polynomial.aeval (MvPolynomial.X 0) P)
          + (Polynomial.aeval (MvPolynomial.X 0) P.derivative)) * MvPolynomial.X 1)
      = P.eval (g 0) * g 2 - (β * P.eval (g 0) + (P.derivative).eval (g 0)) * g 1 := by
    intro g
    simp only [map_sub, map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, evalX0f3]
  refine ⟨1, (Polynomial.aeval (MvPolynomial.X 0) P) * MvPolynomial.X 2
    - (MvPolynomial.C β * (Polynomial.aeval (MvPolynomial.X 0) P)
      + (Polynomial.aeval (MvPolynomial.X 0) P.derivative)) * MvPolynomial.X 1, ?_, ?_⟩
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℂ, P.eval x₀ ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hP0 (Polynomial.funext (fun x => by rw [hc x, Polynomial.eval_zero]))
    intro h
    apply hx₀
    have hev := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 0 then x₀ else
      if i = 2 then 1 else 0)) h
    rw [key, map_zero] at hev
    simpa using hev
  · intro z
    have hgderiv : HasDerivAt (fun s => Complex.exp (β * s) * P.eval s)
        (Complex.exp (β * z) * (β * P.eval z + (P.derivative).eval z)) z := by
      have hb : HasDerivAt (fun s : ℂ => β * s) β z := by simpa using (hasDerivAt_id z).const_mul β
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (β * s)) (β * Complex.exp (β * z)) z := by
        have := hb.cexp; rw [mul_comm] at this; convert this using 1
      have h2 : HasDerivAt (fun s : ℂ => P.eval s) ((P.derivative).eval z) z := P.hasDerivAt z
      have := h1.mul h2; convert this using 1; ring
    rw [key,
      show (2 : Fin 3) = Fin.succ 1 from rfl, show (1 : Fin 3) = Fin.succ 0 from rfl,
      Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]
    simp only [Fin.val_one, Fin.val_zero, iteratedDeriv_one, iteratedDeriv_zero, hgderiv.deriv]
    ring

/-- **`e^{P(s)}` is differentially algebraic** for any polynomial `P` — the exponential of a general
polynomial phase satisfies the order-1 relation `G' = P'·G`, i.e. `G' − P'·G = 0`, so it is
differentially algebraic (the phase-carrier `e^{κ s + ...}` of the orbit normal form when the phase is
polynomial rather than merely linear). -/
theorem differentiallyAlgebraic_exp_polynomial (P : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun s => Complex.exp (P.eval s)) := by
  have key : ∀ g : Fin 3 → ℂ, MvPolynomial.eval g
      (MvPolynomial.X 2 - (Polynomial.aeval (MvPolynomial.X 0) P.derivative) * MvPolynomial.X 1)
      = g 2 - (P.derivative).eval (g 0) * g 1 := by
    intro g
    simp only [map_sub, map_mul, MvPolynomial.eval_X, evalX0f3]
  refine ⟨1, MvPolynomial.X 2 - (Polynomial.aeval (MvPolynomial.X 0) P.derivative)
    * MvPolynomial.X 1, ?_, ?_⟩
  · intro h
    have hev := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then 1 else 0)) h
    rw [key, map_zero] at hev
    simp at hev
  · intro z
    have hgderiv : HasDerivAt (fun s => Complex.exp (P.eval s))
        ((P.derivative).eval z * Complex.exp (P.eval z)) z := by
      have h2 : HasDerivAt (fun s : ℂ => P.eval s) ((P.derivative).eval z) z := P.hasDerivAt z
      have := h2.cexp; convert this using 1; ring
    rw [key,
      show (2 : Fin 3) = Fin.succ 1 from rfl, show (1 : Fin 3) = Fin.succ 0 from rfl,
      Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]
    simp only [Fin.val_one, Fin.val_zero, iteratedDeriv_one, iteratedDeriv_zero, hgderiv.deriv]
    ring

/-- **`e^{P(s)}·Q(s)` is differentially algebraic** for polynomials `P, Q` — the general entire
DA carrier of the exponential-polynomial family, satisfying the order-1 relation
`Q·G' − (P'·Q + Q')·G = 0`.  Subsumes both `differentiallyAlgebraic_cexp_mul_polynomial` (linear phase
`P = β·s`) and `differentiallyAlgebraic_exp_polynomial` (`Q = 1`).  This is the DA exponential-rational
carrier of the orbit normal form `(9)` in the entire (polynomial-`R`, polynomial phase) case. -/
theorem differentiallyAlgebraic_exp_poly_mul_poly (P Q : Polynomial ℂ) :
    DifferentiallyAlgebraic (fun s => Complex.exp (P.eval s) * Q.eval s) := by
  rcases eq_or_ne Q 0 with hQ0 | hQ0
  · subst hQ0; simpa using differentiallyAlgebraic_const 0
  have key : ∀ g : Fin 3 → ℂ, MvPolynomial.eval g
      ((Polynomial.aeval (MvPolynomial.X 0) Q) * MvPolynomial.X 2
        - ((Polynomial.aeval (MvPolynomial.X 0) P.derivative)
            * (Polynomial.aeval (MvPolynomial.X 0) Q)
          + (Polynomial.aeval (MvPolynomial.X 0) Q.derivative)) * MvPolynomial.X 1)
      = Q.eval (g 0) * g 2
        - ((P.derivative).eval (g 0) * Q.eval (g 0) + (Q.derivative).eval (g 0)) * g 1 := by
    intro g
    simp only [map_sub, map_mul, map_add, MvPolynomial.eval_X, evalX0f3]
  refine ⟨1, (Polynomial.aeval (MvPolynomial.X 0) Q) * MvPolynomial.X 2
    - ((Polynomial.aeval (MvPolynomial.X 0) P.derivative) * (Polynomial.aeval (MvPolynomial.X 0) Q)
      + (Polynomial.aeval (MvPolynomial.X 0) Q.derivative)) * MvPolynomial.X 1, ?_, ?_⟩
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℂ, Q.eval x₀ ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hQ0 (Polynomial.funext (fun x => by rw [hc x, Polynomial.eval_zero]))
    intro h
    apply hx₀
    have hev := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 0 then x₀ else
      if i = 2 then 1 else 0)) h
    rw [key, map_zero] at hev
    simpa using hev
  · intro z
    have hgderiv : HasDerivAt (fun s => Complex.exp (P.eval s) * Q.eval s)
        (Complex.exp (P.eval z) * ((P.derivative).eval z * Q.eval z + (Q.derivative).eval z)) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (P.eval s))
          ((P.derivative).eval z * Complex.exp (P.eval z)) z := by
        have := (P.hasDerivAt z).cexp; convert this using 1; ring
      have h2 : HasDerivAt (fun s : ℂ => Q.eval s) ((Q.derivative).eval z) z := Q.hasDerivAt z
      have := h1.mul h2; convert this using 1; ring
    rw [key,
      show (2 : Fin 3) = Fin.succ 1 from rfl, show (1 : Fin 3) = Fin.succ 0 from rfl,
      Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]
    simp only [Fin.val_one, Fin.val_zero, iteratedDeriv_one, iteratedDeriv_zero, hgderiv.deriv]
    ring

/-- **First-order polynomial ODE ⟹ differentially algebraic.**  If `G` satisfies `Q(s)·G'(s) = P(s)·G(s)`
for polynomials `P, Q` with `Q ≠ 0` (i.e. its logarithmic derivative `G'/G = P/Q` is rational), then `G`
is differentially algebraic, via the order-1 differential polynomial `Q(X₀)·X₂ − P(X₀)·X₁` in
`MvPolynomial (Fin 3) ℂ`.  This is the bridge that closes the differential-algebraic direction of the
signed-archimedean orbit-charge dichotomy: once the charge collapse (`digamma_charge_collapse`) makes
`G'/G` rational, this lemma delivers `DifferentiallyAlgebraic G`. -/
theorem differentiallyAlgebraic_of_firstOrder_poly_ode {G : ℂ → ℂ} (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hode : ∀ s, Q.eval s * deriv G s = P.eval s * G s) :
    DifferentiallyAlgebraic G := by
  have key : ∀ g : Fin 3 → ℂ, MvPolynomial.eval g
      ((Polynomial.aeval (MvPolynomial.X 0) Q) * MvPolynomial.X 2
        - (Polynomial.aeval (MvPolynomial.X 0) P) * MvPolynomial.X 1)
      = Q.eval (g 0) * g 2 - P.eval (g 0) * g 1 := by
    intro g
    simp only [map_sub, map_mul, MvPolynomial.eval_X, evalX0f3]
  refine ⟨1, (Polynomial.aeval (MvPolynomial.X 0) Q) * MvPolynomial.X 2
    - (Polynomial.aeval (MvPolynomial.X 0) P) * MvPolynomial.X 1, ?_, ?_⟩
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℂ, Q.eval x₀ ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hQ (Polynomial.funext (fun x => by rw [hc x, Polynomial.eval_zero]))
    intro h
    apply hx₀
    have hev := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 0 then x₀ else
      if i = 2 then 1 else 0)) h
    rw [key, map_zero] at hev
    simpa using hev
  · intro z
    rw [key, show (2 : Fin 3) = Fin.succ 1 from rfl, show (1 : Fin 3) = Fin.succ 0 from rfl,
      Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]
    simp only [Fin.val_one, Fin.val_zero, iteratedDeriv_one, iteratedDeriv_zero]
    linear_combination hode z

end GaloisForLFunctions
