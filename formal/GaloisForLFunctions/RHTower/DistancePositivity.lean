import GaloisForLFunctions.RHTower.ArithmeticEvaluationObstruction
import GaloisForLFunctions.RHTower.UniformDistanceBound

/-!
# Every finite-section distance is strictly positive

`ArithmeticEvaluationObstruction` proves the arithmetic floor in the step-vector formulation, and
`StepFunctionCarrier` identifies the Báez-Duarte data with step vectors.  Composing the two transports the
floor to the distances themselves:

**`bdDistDiscrete_pos` — `0 < d_N` for every `N`**, with the explicit floor
`√(1/(N!·(N!+1))) ≤ d_N` (`bdDistDiscrete_ge_factorial_floor`).  No lower bound on `N` is needed: at `N = 0` the
span is `{0}` and the statement reads `√(1/2) ≤ ‖bdTarget‖ = 1`.

The mechanism is divisibility: every modulus of the section divides `N !`, so evaluation of the sequence at
`N !` annihilates every generator while the target has the value `1` there.

With `UniformDistanceBound.bdDistDiscrete_sq_le_quarter` this pins the sequence between two explicit
unconditional bounds — strictly positive for each `N`, and below a fixed constant from `N = 4` on — and leaves
exactly one question: is the infimum `0`?  That question is the Riemann hypothesis.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The factorial floor for a finite section.** -/
theorem bdDistDiscrete_ge_factorial_floor (N : ℕ) :
    Real.sqrt (1 / ((Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) + 1)))
      ≤ bdDistDiscrete N := by
  have hn₀ : 1 ≤ Nat.factorial N := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hdvd : ∀ i : {x // x ∈ Finset.range N}, (i.1 + 1) ∣ Nat.factorial N := by
    intro i
    have hi : i.1 + 1 ≤ N := by
      have := Finset.mem_range.mp i.2
      omega
    exact Nat.dvd_factorial (by omega) hi
  have hfam : (fun i : {x // x ∈ Finset.range N} => bdGen (bdDiscrete i.1))
      = fun i : {x // x ∈ Finset.range N} =>
        stepVec (fun n => ((n % (i.1 + 1) : ℕ) : ℝ) / (((i.1 + 1 : ℕ)) : ℝ))
          (abs_modSeq_le (i.1 + 1)) := by
    funext i
    exact bdGen_bdDiscrete_eq_stepVec i.1
  rw [bdDistDiscrete, bdDistFinset, bdDist]
  refine (Metric.le_infDist ⟨0, Submodule.zero_mem _⟩).mpr ?_
  intro G hG
  rw [dist_eq_norm]
  have hGmem : G ∈ (Submodule.span ℂ (Set.range (fun i : {x // x ∈ Finset.range N} =>
      stepVec (fun n => ((n % (i.1 + 1) : ℕ) : ℝ) / (((i.1 + 1 : ℕ)) : ℝ))
        (abs_modSeq_le (i.1 + 1))))).topologicalClosure := by
    have hGs : G ∈ Submodule.span ℂ (Set.range (fun i : {x // x ∈ Finset.range N} =>
        bdGen (bdDiscrete i.1))) := hG
    rw [hfam] at hGs
    exact Submodule.le_topologicalClosure _ hGs
  have hfloor := dist_floor_of_forall_dvd (n₀ := Nat.factorial N) hn₀
    (fun i : {x // x ∈ Finset.range N} => i.1 + 1) hdvd hGmem
  rw [← bdTarget_eq_stepVec] at hfloor
  exact hfloor

/-- **Every finite-section Báez-Duarte distance is strictly positive.** -/
theorem bdDistDiscrete_pos (N : ℕ) : 0 < bdDistDiscrete N := by
  refine lt_of_lt_of_le ?_ (bdDistDiscrete_ge_factorial_floor N)
  have hn₀ : (0 : ℝ) < (Nat.factorial N : ℝ) := by
    have : 0 < Nat.factorial N := Nat.factorial_pos N
    exact_mod_cast this
  exact Real.sqrt_pos.mpr (by positivity)

end RHTower

end
