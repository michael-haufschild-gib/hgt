import GaloisForLFunctions.RHTower.WeilLogShiftSharpDualProfile

/-!
# A vanishing dual-valued receiver on the actual regular coefficient space

One common normalization realizes the paired-kernel series as evaluation of
a C₀ map into the dual of the regular amplitude subspace. The norm profile
is sharp, detects common invisibility, and forces amplitude escape for any
fixed positive response at escaping shifts.
-/

open Filter Topology Real
open scoped ZeroAtInfty

noncomputable section

namespace RHTower

/-- The actual regular subspace has a dual-valued C₀ receiver with a sharp
vanishing profile; every series assertion includes convergence. -/
theorem exists_weilLogShift_sharp_dual_receiver
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : E →ₗ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B : ℝ), 0 < B ∧
      ∃ Ψ : C₀(ℝ, (weilLogShiftFactorialSequenceSubmodule.comap R) →L[ℝ] ℝ),
        ∃ q : C₀(ℝ, ℝ), (∀ y, q y = ‖Ψ y‖) ∧
          (∀ (a : weilLogShiftFactorialSequenceSubmodule.comap R) (y : ℝ),
            HasSum (fun n : ℕ => exp (-(B * n)) *
              (R (a : E) n * pairedLogKernel y n) / (n.factorial : ℝ) ^ m) (Ψ y a)) ∧
          (∀ (y c : ℝ), 0 ≤ c → (q y ≤ c ↔
            ∀ a : weilLogShiftFactorialSequenceSubmodule.comap R,
              |Ψ y a| ≤ ‖(a : E)‖ * c)) ∧
          (∀ y, q y = 0 ↔
            ∀ a : weilLogShiftFactorialSequenceSubmodule.comap R, Ψ y a = 0) ∧
          ∀ (ε : ℝ), 0 < ε → ∀ A : ℝ, ∀ᶠ y in cocompact ℝ,
            ∀ a : weilLogShiftFactorialSequenceSubmodule.comap R,
              ε ≤ |Ψ y a| → A < ‖(a : E)‖ := by
  obtain ⟨m, B, _, hB, _, S, _, hvalue⟩ := exists_weilLogShift_uniform_c0_operator R
  refine ⟨m, B, hB, finiteDimensionalC0Dual S.toLinearMap,
    finiteDimensionalC0SharpProfile S.toLinearMap, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · exact hvalue
  · intro y c hc
    exact finiteDimensionalC0SharpProfile_le_iff S.toLinearMap y hc
  · intro y
    exact finiteDimensionalC0SharpProfile_eq_zero_iff S.toLinearMap y
  · intro ε hε A
    exact finiteDimensionalC0_response_cost_escapes S.toLinearMap ε hε A

end RHTower
