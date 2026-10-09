import GaloisForLFunctions.RHTower.WeilLogShiftExactResponseCost
import GaloisForLFunctions.RHTower.WeilLogShiftSharpDualReceiver

/-!
# Exact budget and attained minimum cost for normalized paired-kernel responses

One common normalization and one nonnegative C₀ sensitivity profile classify
every response at every shift. Feasibility and minimization are expressed
using HasSum of the actual series on the actual regular coefficient subspace.
-/

open Real
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

/-- Exact response cost under a single normalization. The budget criterion
includes invisible shifts; the minimum is attained precisely when the response
is zero or the sensitivity is positive. No inner product norm is required. -/
theorem exists_weilLogShift_exact_response_cost
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E →ₗ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B : ℝ), 0 < B ∧ ∃ q : C₀(ℝ, ℝ), (∀ y, 0 ≤ q y) ∧
      (∀ y r A : ℝ,
        (∃ a : weilLogShiftFactorialSequenceSubmodule.comap R,
          HasSum (fun n : ℕ => exp (-(B * n)) *
            (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r ∧
          ‖(a : E)‖ ≤ A) ↔ 0 ≤ A ∧ |r| ≤ A * q y) ∧
      ∀ y r : ℝ,
        (∃ a : weilLogShiftFactorialSequenceSubmodule.comap R,
          HasSum (fun n : ℕ => exp (-(B * n)) *
            (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r ∧
          ‖(a : E)‖ = |r| / q y ∧
          ∀ b : weilLogShiftFactorialSequenceSubmodule.comap R,
            HasSum (fun n : ℕ => exp (-(B * n)) *
              (R (b : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r →
            ‖(a : E)‖ ≤ ‖(b : E)‖) ↔ r = 0 ∨ 0 < q y := by
  obtain ⟨m, B, hB, Ψ, q, hq, hvalue, _, _, _⟩ :=
    exists_weilLogShift_sharp_dual_receiver R
  have hresponse (a : weilLogShiftFactorialSequenceSubmodule.comap R) (y r : ℝ) :
      HasSum (fun n : ℕ => exp (-(B * n)) *
        (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) r ↔ Ψ y a = r := by
    constructor
    · intro h
      exact (hvalue a y).unique h
    · intro h
      rw [← h]
      exact hvalue a y
  refine ⟨m, B, hB, q, fun y => (hq y).symm ▸ norm_nonneg (Ψ y), ?_, ?_⟩
  · intro y r A
    simpa only [hresponse, hq] using! finiteDimensional_dual_response_budget_iff (Ψ y) r A
  · intro y r
    simpa only [hresponse, hq] using! finiteDimensional_dual_minimum_response_iff (Ψ y) r

end RHTower
