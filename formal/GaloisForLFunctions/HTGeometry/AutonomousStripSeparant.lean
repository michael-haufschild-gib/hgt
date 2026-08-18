import GaloisForLFunctions.HTGeometry.AutonomousJetRelation
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# Ritt's separant step on a strip, read on the central line

An autonomous algebraic differential equation for a function holomorphic on a vertical strip is a
univariate polynomial over the ring of polynomials in the lower jets, whose evaluation along the jet
of the function vanishes on the strip.  Among nonzero such equations there is one of minimal top-jet
degree, and in characteristic zero the separant of a degree-minimal equation of positive top-jet
degree cannot vanish identically along the solution.

The relation evaluated along a holomorphic jet is holomorphic, so a function that does not vanish
identically on the strip does not vanish identically on the central line either.  The separant of a
minimal equation therefore has a nonzero value at a *real* time — which is the form the carrier
argument consumes, the carrier being built from the line restriction.
-/

namespace GaloisForLFunctions

open Polynomial

variable {σ R : ℝ} {n : ℕ}

/-! ### Holomorphy of the relation along a holomorphic solution -/

/-- Evaluating a multivariate polynomial at holomorphic coordinates is holomorphic. -/
theorem differentiableOn_mvEval_comp {m : ℕ} {U : Set ℂ} {v : Fin m → ℂ → ℂ}
    (hv : ∀ j, DifferentiableOn ℂ (v j) U) (Q : MvPolynomial (Fin m) ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => MvPolynomial.eval (fun j : Fin m => v j z) Q) U := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      have hrw : (fun z : ℂ => MvPolynomial.eval (fun j : Fin m => v j z) (MvPolynomial.C a))
          = fun _ : ℂ => a := by
        funext z
        simp
      rw [hrw]
      exact differentiableOn_const a
  | add p q hp hq =>
      have hrw : (fun z : ℂ => MvPolynomial.eval (fun j : Fin m => v j z) (p + q))
          = fun z : ℂ => MvPolynomial.eval (fun j : Fin m => v j z) p
              + MvPolynomial.eval (fun j : Fin m => v j z) q := by
        funext z
        simp
      rw [hrw]
      exact hp.fun_add hq
  | mul_X p i hp =>
      have hrw : (fun z : ℂ =>
            MvPolynomial.eval (fun j : Fin m => v j z) (p * MvPolynomial.X i))
          = fun z : ℂ => MvPolynomial.eval (fun j : Fin m => v j z) p * v i z := by
        funext z
        simp
      rw [hrw]
      exact hp.mul (hv i)

/-- **The relation along a holomorphic jet is holomorphic.**  It is a finite sum of products of
polynomial evaluations in the iterated derivatives, each of which is holomorphic where the function
is. -/
theorem differentiableOn_jetRelation_jets {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => jetRelation n P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Φ z))
      (verticalStrip σ R) := by
  classical
  have hjet : ∀ k : ℕ, DifferentiableOn ℂ (iteratedDeriv k Φ) (verticalStrip σ R) :=
    differentiableOn_iteratedDeriv_verticalStrip hΦ
  have hrw : (fun z : ℂ => jetRelation n P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Φ z))
      = fun z : ℂ => ∑ i ∈ P.support,
          MvPolynomial.eval (fun j : Fin n => iteratedDeriv (j : ℕ) Φ z) (P.coeff i)
            * (iteratedDeriv n Φ z) ^ i := by
    funext z
    rw [jetRelation_eq_sum]
    simp [Fin.val_last]
  rw [hrw]
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact (differentiableOn_mvEval_comp (fun j : Fin n => hjet (j : ℕ)) (P.coeff i)).mul
    ((hjet n).pow i)

/-- A holomorphic function on a strip that vanishes on the central line vanishes on the strip. -/
theorem eqZero_of_eqZero_line {g : ℂ → ℂ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R))
    (hline : ∀ t : ℝ, g ((σ : ℂ) + (t : ℂ) * Complex.I) = 0) :
    ∀ z ∈ verticalStrip σ R, g z = 0 := by
  intro z hz
  exact eqOn_of_eqOn_line hR hg (differentiableOn_const 0) hline hz


/-! ### Annihilators on a strip -/

/-- `P` annihilates `F` on the strip: the autonomous relation evaluated along the jet of `F`
vanishes at every point of the strip. -/
def StripAnnihilator (σ R : ℝ) (F : ℂ → ℂ) (n : ℕ)
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) : Prop :=
  ∀ z ∈ verticalStrip σ R, jetRelation n P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0

/-- Among nonzero strip annihilators there is one of minimal top-jet degree. -/
theorem exists_minimal_stripAnnihilator {F : ℂ → ℂ}
    (h : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
        P.natDegree ≤ Q.natDegree := by
  obtain ⟨P₀, hP₀, hA₀⟩ := h
  set S : Set ℕ := {d | ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
    StripAnnihilator σ R F n P ∧ P.natDegree = d} with hSdef
  have hS : S.Nonempty := ⟨P₀.natDegree, P₀, hP₀, hA₀, rfl⟩
  obtain ⟨P, hP, hA, hPd⟩ := Nat.sInf_mem hS
  refine ⟨P, hP, hA, fun Q hQ hAQ => ?_⟩
  rw [hPd]
  exact Nat.sInf_le ⟨Q, hQ, hAQ, rfl⟩

/-- **The separant of a degree-minimal strip equation does not annihilate on the strip.** -/
theorem separant_not_stripAnnihilator {F : ℂ → ℂ}
    {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hdeg : P.natDegree ≠ 0)
    (hmin : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      P.natDegree ≤ Q.natDegree) :
    ¬ StripAnnihilator σ R F n (Polynomial.derivative P) := by
  intro hAd
  have hd0 : Polynomial.derivative P ≠ 0 := fun h0 =>
    hdeg (Polynomial.derivative_eq_zero.mp h0)
  exact absurd (hmin _ hd0 hAd) (not_le.mpr (Polynomial.natDegree_derivative_lt hdeg))

/-- **Ritt's separant step on a strip, evaluated on the central line.**  If `F` satisfies some
nonzero autonomous equation of order `n` on the strip, and no such equation is free of the top jet,
then `F` satisfies a degree-minimal equation with genuinely present top derivative whose separant is
nonzero at some real time.

The passage from "not identically zero on the strip" to "nonzero at a real time" is the identity
theorem: the separant evaluated along the jet of `F` is holomorphic on the strip. -/
theorem exists_minimal_strip_separant_line {F : ℂ → ℂ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (h : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ P.natDegree ≠ 0 ∧
      StripAnnihilator σ R F n P ∧
      ∃ t : ℝ, jetRelation n (Polynomial.derivative P)
        (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  obtain ⟨P, hP, hA, hmin⟩ := exists_minimal_stripAnnihilator h
  have hdeg : P.natDegree ≠ 0 := horder P hP hA
  refine ⟨P, hP, hdeg, hA, ?_⟩
  by_contra hcon
  push Not at hcon
  refine separant_not_stripAnnihilator hdeg hmin ?_
  exact eqZero_of_eqZero_line hR
    (differentiableOn_jetRelation_jets hF (Polynomial.derivative P)) hcon

end GaloisForLFunctions
