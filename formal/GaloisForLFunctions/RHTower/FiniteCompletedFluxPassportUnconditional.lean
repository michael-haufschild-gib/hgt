import GaloisForLFunctions.RHTower.FiniteCompletedFluxPassportSurjectivity
import GaloisForLFunctions.RHTower.QuartetEnvelopeFiniteAvoidance

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The finite completed-flux passport theorem needs no externally supplied envelope: an explicit
finite avoidance displacement simultaneously avoids all prescribed quartet centres. -/
theorem exists_quartet_passport_flux_realizer_of_polynomial_passport_unconditional
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (α : J → ℂ) (N : J → ℕ)
    (H : J → Polynomial ℂ) (hH0 : ∀ j, (H j).coeff 0 = -1)
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
        iteratedDeriv k (fluxGerm (quartetRealizer a₀ B) (α j)) 0 =
          iteratedDeriv k (fun x => (H j).eval x) 0 := by
  let a₀ : ℝ := finiteQuartetEnvelopeDisplacement α
  have ha₀pos : 0 < a₀ := finiteQuartetEnvelopeDisplacement_pos α
  refine ⟨a₀, ha₀pos, ?_⟩
  exact exists_quartet_passport_flux_realizer_of_polynomial_passport a₀ ha₀pos.ne' α N H hH0
    hαre (fun j => coshQuartetEnvelope_ne_zero_finiteQuartetEnvelopeDisplacement α j) hinj

end RHTower
