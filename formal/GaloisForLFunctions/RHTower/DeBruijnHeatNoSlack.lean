import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative

/-!
# No slack in the heat parameter

Let `Λ_real = {λ | every zero of H_λ is real}` be the set of heat times at which the de Bruijn–Newman
deformation `H_λ` of `Ξ` has only real zeros.  Newman's theorem
(`riemannHeat_neg_nonreal_zeros_infinite`) says that `H_λ` has infinitely many non-real zeros for
every `λ < 0`.  Hence:

* `exists_mem_nonreal_zeros_infinite_of_isOpen`: every open set of heat times containing `0` contains
  a heat time with infinitely many non-real zeros.
* `zero_not_mem_interior_realZeroHeatTimes`: `0` is not an interior point of `Λ_real`.

So no condition on the source that is open in the heat parameter and holds at `λ = 0` can imply
that all zeros are real: a proof of the Riemann hypothesis through the deformation family cannot
rest on a positivity margin that survives small backward heat perturbations.
-/

open Complex Set

namespace RHTower

namespace DeBruijn

/-- Heat times `s ∈ ℝ`, of either sign, at which every zero of `H_s` is real.  Unlike
`realRootedTimes`, negative times are admitted, so the statement below is not automatic. -/
def realZeroHeatTimes : Set ℝ := {s | ∀ z : ℂ, riemannHeat s z = 0 → z.im = 0}

/-- **No open neighbourhood of `0` avoids non-real zeros.** -/
theorem exists_mem_nonreal_zeros_infinite_of_isOpen {S : Set ℝ} (hS : IsOpen S)
    (h0 : (0 : ℝ) ∈ S) :
    ∃ s ∈ S, s < 0 ∧ {z : ℂ | riemannHeat s z = 0 ∧ z.im ≠ 0}.Infinite := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS 0 h0
  refine ⟨-(ε / 2), hball ?_, by linarith, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]
    linarith
  · exact riemannHeat_neg_nonreal_zeros_infinite (by linarith)

/-- **`0` is not an interior point of the real-zero heat times.** -/
theorem zero_not_mem_interior_realZeroHeatTimes : (0 : ℝ) ∉ interior realZeroHeatTimes := by
  intro h
  obtain ⟨s, hsS, -, hinf⟩ :=
    exists_mem_nonreal_zeros_infinite_of_isOpen isOpen_interior h
  obtain ⟨z, hz, him⟩ := hinf.nonempty
  exact him (interior_subset hsS z hz)

end DeBruijn

end RHTower
