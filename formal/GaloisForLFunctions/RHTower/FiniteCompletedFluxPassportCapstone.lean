import GaloisForLFunctions.HTGeometry.SimpleZeroResidueFluxCongruence
import GaloisForLFunctions.RHTower.QuartetPassportCapstone

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Finite analytic simple-zero targets can be realized with every quartet guard while preserving
their completed-flux jets exactly.  One additional target jet is precisely what is needed to
control the flux jet of the simple zero. -/
theorem exists_quartet_passport_flux_realizer_of_target {J : Type} [Fintype J] [DecidableEq J]
    [Nonempty J] (a₀ : ℝ) (ha₀ : a₀ ≠ 0) (α : J → ℂ) (N : J → ℕ)
    (target : J → ℂ → ℂ) (hαre : ∀ j, (α j).re ≠ 0)
    (hAne : ∀ j, coshQuartetEnvelope a₀ (α j) ≠ 0)
    (htargetDiff : ∀ j, Differentiable ℂ (target j))
    (htargetzero : ∀ j, target j (α j) = 0)
    (htargetderiv : ∀ j, deriv (target j) (α j) ≠ 0)
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
          iteratedDeriv k (fluxGerm (target j) (α j)) 0 := by
  have htarget : ∀ j, AnalyticAt ℂ (target j) (α j) := by
    intro j
    exact (htargetDiff j).differentiableOn.analyticOnNhd isOpen_univ (α j) (by simp)
  obtain ⟨B, hdeg, heven, hreal, haxis, hperiod, hjet⟩ :=
    exists_quartet_passport_realizer_of_target a₀ ha₀ α N target hαre hAne htarget
      htargetzero hinj
  have hBne : B ≠ 0 := by
    intro hB
    rw [hB] at hdeg
    simp at hdeg
  refine ⟨B, hdeg, heven, hreal, haxis, hperiod,
    quartetRealizer_exact_order_one_bounds a₀ hBne, ?_, ?_⟩
  · intro j
    constructor
    · calc
        quartetRealizer a₀ B (α j) = target j (α j) := by simpa using hjet j 0 (by omega)
        _ = 0 := htargetzero j
    · have hderiv : deriv (quartetRealizer a₀ B) (α j) = deriv (target j) (α j) := by
        simpa only [iteratedDeriv_one] using hjet j 1 (by omega)
      rw [hderiv]
      exact htargetderiv j
  · intro j k hk
    apply GaloisForLFunctions.HTGeometry.fluxGerm_iteratedDeriv_jet_congr_of_simple_zero
      (K := N j) (quartetRealizer_differentiable a₀ B) (htargetDiff j)
    · calc
        quartetRealizer a₀ B (α j) = target j (α j) := by simpa using hjet j 0 (by omega)
        _ = 0 := htargetzero j
    · exact htargetzero j
    · have hderiv : deriv (quartetRealizer a₀ B) (α j) = deriv (target j) (α j) := by
        simpa only [iteratedDeriv_one] using hjet j 1 (by omega)
      rw [hderiv]
      exact htargetderiv j
    · exact htargetderiv j
    · intro n hn
      exact hjet j n (by omega)
    · exact hk

end RHTower
