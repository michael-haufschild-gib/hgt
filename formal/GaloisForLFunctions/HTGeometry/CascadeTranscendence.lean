import GaloisForLFunctions.HTGeometry.CascadeStateIndependence
import GaloisForLFunctions.HTGeometry.EntireOrderZeroTranscendence

/-!
# Every state of a cascade is transcendental

Algebraic independence of the states contains the transcendence of each of them: a polynomial
expression of a state in the coordinate is itself a relation between two states, and there are none.

Consequently no state of a cascade satisfies an order-zero algebraic differential equation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {f : ℕ → ℂ → ℂ}

/-- Evaluating a univariate polynomial planted in the first variable. -/
theorem eval_aeval_X_zero {n : ℕ} (σ : Fin (n + 1) → ℂ) (p : Polynomial ℂ) :
    MvPolynomial.eval σ (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) p)
      = p.eval (σ 0) := by
  have h := Polynomial.aeval_algHom_apply
    (MvPolynomial.aeval σ : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] ℂ)
    (MvPolynomial.X (0 : Fin (n + 1))) p
  simp [MvPolynomial.aeval_eq_eval] at h ⊢
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h.symm

/-- **Every state past the coordinate is transcendental entire.** -/
theorem transcendentalEntire_entireCascade (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    {n : ℕ} (hn : 0 < n) :
    TranscendentalEntire (entireCascade f n) := by
  have hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) (Set.univ : Set ℂ) := by
    intro i
    exact DifferentiableOn.analyticOnNhd
      (fun z _ => ((hall i).1 z).differentiableWithinAt) isOpen_univ
  refine ⟨fun z => (analyticOnNhd_entireCascade hfan n z (Set.mem_univ z)).differentiableAt, ?_⟩
  rintro ⟨p, hp⟩
  -- the alleged polynomial expression is a relation between the last state and the coordinate
  set P : MvPolynomial (Fin (n + 1)) ℂ :=
    MvPolynomial.X (Fin.last n) - Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) p with hP
  have hlast : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have h0 : ((0 : Fin (n + 1)) : ℕ) = ((Fin.last n : Fin (n + 1)) : ℕ) := by rw [h]
    simp at h0
    omega
  have hPne : P ≠ 0 := by
    intro h0
    -- evaluate at the indicator of the last coordinate and at the origin
    have h1 : MvPolynomial.eval (fun j : Fin (n + 1) => if j = Fin.last n then (1 : ℂ) else 0) P
        = 1 - p.eval 0 := by
      rw [hP]
      rw [map_sub, MvPolynomial.eval_X, eval_aeval_X_zero]
      simp [hlast]
    have h2 : MvPolynomial.eval (fun _ : Fin (n + 1) => (0 : ℂ)) P = 0 - p.eval 0 := by
      rw [hP]
      rw [map_sub, MvPolynomial.eval_X, eval_aeval_X_zero]
    rw [h0] at h1 h2
    simp only [map_zero] at h1 h2
    have : (1 : ℂ) = 0 := by
      have e1 : p.eval 0 = 1 := by linear_combination h1
      have e2 : p.eval 0 = 0 := by linear_combination h2
      rw [e1] at e2
      exact e2
    exact one_ne_zero this
  refine noRelation_entireCascade_of_transcendental (n + 1) f hall P hPne ?_
  intro z
  rw [hP, map_sub, MvPolynomial.eval_X, eval_aeval_X_zero]
  have hz : entireCascade f ((Fin.last n : Fin (n + 1)) : ℕ) z = p.eval z := by
    simpa using hp z
  have hz0 : entireCascade f ((0 : Fin (n + 1)) : ℕ) z = z := by simp
  rw [hz, hz0, sub_self]

/-- **No state of a cascade satisfies an order-zero equation.** -/
theorem not_differentiallyAlgebraicOfOrder_zero_entireCascade
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {n : ℕ} (hn : 0 < n) :
    ¬ DifferentiallyAlgebraicOfOrder (entireCascade f n) 0 := by
  intro hDA
  have ht := transcendentalEntire_entireCascade hall hn
  exact not_differentiallyAlgebraicOfOrder_zero_of_transcendental ht.1 ht.2 hDA

end GaloisForLFunctions.HTGeometry
