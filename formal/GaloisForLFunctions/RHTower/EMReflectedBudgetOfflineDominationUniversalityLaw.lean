import GaloisForLFunctions.RHTower.EMRemainderReduction
import GaloisForLFunctions.RHTower.OfflineDominationDischarge

/-!
# Reflected-budget offline domination universality

The Euler--Maclaurin remainder reduction constructs finite-carrier closeness from elementary pole
and tail budgets plus one reflected Dirichlet-block estimate.  The offline discharge consumes that
closeness.  Their composition removes the last abstract AFE-closeness input from both raw and
completed finite-carrier domination.
-/

namespace RHTower

noncomputable section

/-- **Reflected-budget offline-domination universality law.**  Concrete pole, tail, and reflected
Dirichlet budgets imply the raw and completed carrier inequalities simultaneously. -/
theorem raw_completed_domination_of_em_reflected_budget
    {S : Set ℂ} {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {ε₁ δP δT Rχ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hP : ∀ z ∈ S, ‖emPole N z‖ ≤ δP)
    (hT : ∀ z ∈ S, ‖z‖ * (N : ℝ) ^ (-z.re) / z.re ≤ δT)
    (hχ : ∀ z ∈ S, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ Rχ)
    (hdom : ∀ z ∈ S,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ +
          (ε₁ + (ε₁ + (δP + δT + Rχ))) < ‖dirichletPoly N z‖) :
    (∀ z ∈ S,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖) ∧
      ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
  have hstripEM : ∀ z ∈ S, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    refine ⟨(hstrip z hz).1, ?_⟩
    intro hz1
    subst z
    have hlt := (hstrip 1 hz).2
    norm_num at hlt
  have hclose : ∀ z ∈ S,
      ‖emCarrier M z - gN N z‖ ≤ ε₁ + (δP + δT + Rχ) :=
    emCarrier_gN_close_on_of_reflected_budget hN hM hstripEM hE hP hT hχ
  exact ⟨
    raw_domination_of_emCarrier_close_pointwise_domination hE hclose hdom,
    completed_domination_of_emCarrier_close_pointwise_domination
      hM hstrip hE hclose hdom⟩

end

end RHTower
