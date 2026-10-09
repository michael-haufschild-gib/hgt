import GaloisForLFunctions.RHTower.WeilLogShiftGlobalResponseCost
import GaloisForLFunctions.RHTower.WeilLogShiftSharpDualReceiver

/-!
# One globally optimal shift for the normalized paired-kernel receiver

One normalization has an optimal shift independent of target response and
amplitude budget. Its global sensitivity gives exact feasibility and attained
minimum cost, expressed with convergence of the literal paired-kernel series.
-/

open Real
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

/-- A single shift realizes globally minimum amplitude cost for every feasible
response, under one fixed normalization on the actual regular subspace. -/
theorem exists_weilLogShift_globally_optimal_response_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E →ₗ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B : ℝ), 0 < B ∧
      ∃ Ψ : C₀(ℝ, (weilLogShiftFactorialSequenceSubmodule.comap R) →L[ℝ] ℝ),
        (∀ (a : weilLogShiftFactorialSequenceSubmodule.comap R) (y : ℝ),
          HasSum (fun n : ℕ => exp (-(B * n)) *
            (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) (Ψ y a)) ∧
        ∃ y₀ : ℝ, (∀ y : ℝ, ‖Ψ y‖ ≤ ‖Ψ y₀‖) ∧
          (∀ r A : ℝ,
            (∃ (y : ℝ) (a : weilLogShiftFactorialSequenceSubmodule.comap R),
              HasSum (fun n : ℕ => exp (-(B * n)) *
                (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r ∧
              ‖(a : E)‖ ≤ A) ↔ 0 ≤ A ∧ |r| ≤ A * ‖Ψ y₀‖) ∧
          ∀ r : ℝ,
            (∃ a : weilLogShiftFactorialSequenceSubmodule.comap R,
              HasSum (fun n : ℕ => exp (-(B * n)) *
                (R (a : E) n * pairedLogKernel y₀ n) / (n.factorial : ℝ) ^ m) r ∧
              ‖(a : E)‖ = |r| / ‖Ψ y₀‖ ∧
              ∀ (y : ℝ) (b : weilLogShiftFactorialSequenceSubmodule.comap R),
                HasSum (fun n : ℕ => exp (-(B * n)) *
                  (R (b : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r →
                ‖(a : E)‖ ≤ ‖(b : E)‖) ↔ r = 0 ∨ 0 < ‖Ψ y₀‖ := by
  obtain ⟨m, B, hB, Ψ, _, _, hvalue, _, _, _⟩ := exists_weilLogShift_sharp_dual_receiver R
  have hresponse (a : weilLogShiftFactorialSequenceSubmodule.comap R) (y r : ℝ) :
      HasSum (fun n : ℕ => exp (-(B * n)) *
        (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r ↔ Ψ y a = r := by
    constructor
    · intro h
      exact (hvalue a y).unique h
    · intro h
      rw [← h]
      exact hvalue a y
  obtain ⟨y₀, hy₀, hbudget, hminimum⟩ := exists_c0_dual_optimal_response_point Ψ
  refine ⟨m, B, hB, Ψ, hvalue, y₀, ?_, ?_, ?_⟩
  · intro y
    apply (Ψ y).opNorm_le_bound (norm_nonneg (Ψ y₀))
    intro a
    have h := (hbudget (Ψ y a) ‖a‖).mp ⟨y, a, rfl, le_rfl⟩
    simpa only [Real.norm_eq_abs, hy₀, mul_comm] using h.2
  · intro r A
    simpa only [hresponse, hy₀] using! hbudget r A
  · intro r
    simpa only [hresponse, hy₀] using! hminimum r

end RHTower
