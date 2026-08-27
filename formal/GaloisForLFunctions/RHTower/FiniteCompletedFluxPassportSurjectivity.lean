import GaloisForLFunctions.RHTower.FiniteCompletedFluxPassportCapstone
import GaloisForLFunctions.RHTower.FiniteCompletedFluxPassportTargets

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Every finite packet of polynomial completed-flux passports with the forced simple-zero
residue is realized simultaneously by a real-even, Schwarz-real, aperiodic exact-order-one
quartet realizer. -/
theorem exists_quartet_passport_flux_realizer_of_polynomial_passport
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (ha₀ : a₀ ≠ 0) (α : J → ℂ) (N : J → ℕ)
    (H : J → Polynomial ℂ) (hH0 : ∀ j, (H j).coeff 0 = -1)
    (hαre : ∀ j, (α j).re ≠ 0)
    (hAne : ∀ j, coshQuartetEnvelope a₀ (α j) ≠ 0)
    (hinj : Function.Injective (fun i : J × Fin 4 => quartetVertex (α i.1) i.2)) :
    ∃ B : Polynomial ℂ,
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
        iteratedDeriv k (fluxGerm (quartetRealizer a₀ B) (α j)) 0 =
          iteratedDeriv k (fun x => (H j).eval x) 0 := by
  let P : J → Polynomial ℂ := fun j => polynomialLogUnitForPassport (H j)
  let target : J → ℂ → ℂ := fun j => shiftedSimpleZeroExponentialRealizer (P j) (α j)
  have htargetDiff : ∀ j, Differentiable ℂ (target j) := by
    intro j
    exact shiftedSimpleZeroExponentialRealizer_differentiable (P j) (α j)
  have htargetzero : ∀ j, target j (α j) = 0 := by
    intro j
    exact shiftedSimpleZeroExponentialRealizer_zero (P j) (α j)
  have htargetderiv : ∀ j, deriv (target j) (α j) ≠ 0 := by
    intro j
    exact deriv_shiftedSimpleZeroExponentialRealizer_ne_zero (P j) (α j)
  obtain ⟨B, hdeg, heven, hreal, haxis, hperiod, horder, hsimple, hflux⟩ :=
    exists_quartet_passport_flux_realizer_of_target a₀ ha₀ α N target hαre hAne
      htargetDiff htargetzero htargetderiv hinj
  refine ⟨B, hdeg, heven, hreal, haxis, hperiod, horder, hsimple, ?_⟩
  intro j k hk
  have hpassport : polynomialCompletedFluxPassport (P j) = H j := by
    dsimp [P]
    exact polynomialCompletedFluxPassport_logUnit_eq (H j) (hH0 j)
  have htargetFlux : fluxGerm (target j) (α j) = fun x => (H j).eval x := by
    calc
      fluxGerm (target j) (α j) = fun x => (polynomialCompletedFluxPassport (P j)).eval x :=
        fluxGerm_shiftedSimpleZeroExponentialRealizer_eq_polynomialCompletedFluxPassport
          (P j) (α j)
      _ = fun x => (H j).eval x := by simp only [hpassport]
  calc
    iteratedDeriv k (fluxGerm (quartetRealizer a₀ B) (α j)) 0 =
        iteratedDeriv k (fluxGerm (target j) (α j)) 0 := hflux j k hk
    _ = iteratedDeriv k (fun x => (H j).eval x) 0 := by rw [htargetFlux]

end RHTower
