import GaloisForLFunctions.HTGeometry.JetRealization
import GaloisForLFunctions.RHTower.FiniteCompletedFluxPassportUnconditional

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Every finite derivative-coordinate completed-flux passport with residue `-1` is realized
simultaneously, without preselecting an envelope. -/
theorem exists_quartet_passport_flux_realizer_of_finite_jet_passport
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (α : J → ℂ) (N : J → ℕ) (c : J → ℕ → ℂ)
    (hc0 : ∀ j, c j 0 = -1)
    (hαre : ∀ j, (α j).re ≠ 0)
    (hinj : Function.Injective (fun i : J × Fin 4 => quartetVertex (α i.1) i.2)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ B : Polynomial ℂ,
      0 < B.degree ∧
      (∀ z : ℂ, quartetRealizer a₀ B (-z) = quartetRealizer a₀ B z) ∧
      (∀ z : ℂ, quartetRealizer a₀ B ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (quartetRealizer a₀ B z)) ∧
      (∀ y : ℝ, quartetRealizer a₀ B ((y : ℂ) * Complex.I) ≠ 0) ∧
      (∀ h : ℂ, Function.Periodic (quartetRealizer a₀ B) h → h = 0) ∧
      (∃ Kupper Klower R : ℝ,
        0 < Kupper ∧ 0 < Klower ∧
        (∀ z : ℂ, ‖quartetRealizer a₀ B z‖ ≤
          Kupper * (1 + ‖z‖) ^ B.natDegree * Real.exp (2 * ‖z‖)) ∧
        ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤ ‖quartetRealizer a₀ B (x : ℂ)‖) ∧
      (∀ j, quartetRealizer a₀ B (α j) = 0 ∧ deriv (quartetRealizer a₀ B) (α j) ≠ 0) ∧
      ∀ (j : J) (k : ℕ), k ≤ N j →
        iteratedDeriv k (fluxGerm (quartetRealizer a₀ B) (α j)) 0 = c j k := by
  let H : J → Polynomial ℂ := fun j => jetPolynomial (N j) (c j)
  have hH0 : ∀ j, (H j).coeff 0 = -1 := by
    intro j
    rw [show H j = jetPolynomial (N j) (c j) by rfl,
      coeff_jetPolynomial (c j) (Nat.zero_le _)]
    simpa using hc0 j
  obtain ⟨a₀, ha₀, B, hdeg, heven, hreal, haxis, hperiod, horder, hsimple, hflux⟩ :=
    exists_quartet_passport_flux_realizer_of_polynomial_passport_unconditional α N H hH0
      hαre hinj
  refine ⟨a₀, ha₀, B, hdeg, heven, hreal, haxis, hperiod, horder, hsimple, ?_⟩
  intro j k hk
  have hjet : iteratedDeriv k (fun x : ℂ => (H j).eval x) 0 = c j k := by
    rw [show H j = jetPolynomial (N j) (c j) by rfl,
      GaloisForLFunctions.HTGeometry.iteratedDeriv_polynomial_eval,
      eval_iterate_derivative_zero,
      coeff_jetPolynomial (c j) hk]
    have hfac : (k.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  calc
    iteratedDeriv k (fluxGerm (quartetRealizer a₀ B) (α j)) 0 =
        iteratedDeriv k (fun x => (H j).eval x) 0 := hflux j k hk
    _ = c j k := hjet

end RHTower
