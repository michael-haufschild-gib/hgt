import Mathlib

/-!
# The separant of a minimal autonomous differential equation

An autonomous algebraic differential equation of order `n` for `f : ℂ → ℂ` is encoded as a
univariate polynomial over the ring of polynomials in the lower jets: the coefficients live in
`ℂ[y₀,…,y_{n−1}]` (evaluated at `f, f', …, f^{(n−1)}`) and the polynomial variable is the top
jet `f^{(n)}`.  The **separant** of the equation is its derivative with respect to the top jet.

Ritt's separant step is formalized here: among nonzero autonomous annihilators a
minimal-degree one exists (`exists_minimal_autonomousAnnihilator`), and the separant of a
degree-minimal equation cannot itself annihilate
(`separant_not_autonomousAnnihilator`) — in characteristic zero the separant is nonzero of
strictly smaller top-jet degree, so annihilation would contradict minimality.  When
additionally no annihilator is free of the top jet (the order-minimality of the equation),
the two combine: a minimal equation with genuinely present top derivative and
non-annihilating separant exists (`exists_minimal_with_separant`).  The nonvanishing of the
separant along the solution is the entry point to solving the equation locally for the top
derivative — the first step of every structure theorem for autonomous equations.
-/

namespace GaloisForLFunctions

/-- `P` is an autonomous differential annihilator of order `n` for `f`: evaluating the
coefficients at the lower jets `f, f', …, f^{(n−1)}` and the variable at the top jet `f^{(n)}`
yields the zero function. -/
def AutonomousAnnihilator (f : ℂ → ℂ) (n : ℕ)
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) : Prop :=
  ∀ z : ℂ, Polynomial.eval₂
    (MvPolynomial.eval fun j : Fin n => iteratedDeriv (j : ℕ) f z)
    (iteratedDeriv n f z) P = 0

/-- Among nonzero autonomous annihilators there is one of minimal top-jet degree. -/
theorem exists_minimal_autonomousAnnihilator {f : ℂ → ℂ} {n : ℕ}
    (h : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ AutonomousAnnihilator f n P) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ AutonomousAnnihilator f n P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → AutonomousAnnihilator f n Q →
        P.natDegree ≤ Q.natDegree := by
  obtain ⟨P₀, hP₀, hA₀⟩ := h
  set S : Set ℕ := {d | ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
    AutonomousAnnihilator f n P ∧ P.natDegree = d} with hSdef
  have hS : S.Nonempty := ⟨P₀.natDegree, P₀, hP₀, hA₀, rfl⟩
  obtain ⟨P, hP, hA, hPd⟩ := Nat.sInf_mem hS
  refine ⟨P, hP, hA, fun Q hQ hAQ => ?_⟩
  rw [hPd]
  exact Nat.sInf_le ⟨Q, hQ, hAQ, rfl⟩

/-- **The separant of a degree-minimal autonomous equation does not annihilate.**  In
characteristic zero the top-jet derivative of an equation of positive top-jet degree is
nonzero of strictly smaller degree, so its annihilation would contradict minimality. -/
theorem separant_not_autonomousAnnihilator {f : ℂ → ℂ} {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hdeg : P.natDegree ≠ 0)
    (hmin : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → AutonomousAnnihilator f n Q →
      P.natDegree ≤ Q.natDegree) :
    ¬ AutonomousAnnihilator f n (Polynomial.derivative P) := by
  intro hAd
  have hd0 : Polynomial.derivative P ≠ 0 := fun h0 =>
    hdeg (Polynomial.derivative_eq_zero.mp h0)
  exact absurd (hmin _ hd0 hAd) (not_le.mpr (Polynomial.natDegree_derivative_lt hdeg))

/-- **Ritt's separant step.**  If `f` satisfies some nonzero autonomous equation of order `n`,
and no such equation is free of the top jet (order minimality), then `f` satisfies a
degree-minimal equation with genuinely present top derivative whose separant does not
annihilate `f`. -/
theorem exists_minimal_with_separant {f : ℂ → ℂ} {n : ℕ}
    (h : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ AutonomousAnnihilator f n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 →
      AutonomousAnnihilator f n Q → Q.natDegree ≠ 0) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ AutonomousAnnihilator f n P ∧
      P.natDegree ≠ 0 ∧ ¬ AutonomousAnnihilator f n (Polynomial.derivative P) := by
  obtain ⟨P, hP, hA, hmin⟩ := exists_minimal_autonomousAnnihilator h
  exact ⟨P, hP, hA, horder P hP hA,
    separant_not_autonomousAnnihilator (horder P hP hA) hmin⟩

end GaloisForLFunctions
