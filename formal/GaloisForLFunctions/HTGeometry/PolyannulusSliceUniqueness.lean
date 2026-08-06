import GaloisForLFunctions.HTGeometry.TorusOrbitPolyannulusUniqueness

/-!
# Torus uniqueness needs only one-variable holomorphy

The proof that the product torus is a uniqueness set for a polyannulus releases
one coordinate at a time and applies the one-variable identity theorem to each
slice.  It therefore never uses joint analyticity: separate holomorphy of every
coordinate slice is enough.

This is the form needed for functions produced by integration, where only
one-variable differentiation under the integral sign is available.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

omit [Fintype d] in
/-- **Coordinatewise release with slicewise holomorphy.** -/
theorem eqOn_zero_mixedAnnulus_of_slice {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {G : (d → ℂ) → ℂ}
    (hslice : ∀ z ∈ polyannulus ρ, ∀ i : d,
      AnalyticOnNhd ℂ (fun w => G (Function.update z i w)) (logAnnulus (ρ i)))
    (h0 : ∀ z ∈ unitTorus d, G z = 0) (T : Finset d) :
    ∀ z ∈ mixedAnnulus ρ T, G z = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      intro z hz
      rw [mixedAnnulus_empty] at hz
      exact h0 z hz
  | insert i T hi ih =>
      intro z hz
      have hzp : z ∈ polyannulus ρ := mixedAnnulus_subset_polyannulus hρ _ hz
      have hzi : z i ∈ logAnnulus (ρ i) := hz.1 i (Finset.mem_insert_self i T)
      have hg : AnalyticOnNhd ℂ (fun w : ℂ => G (Function.update z i w))
          (logAnnulus (ρ i)) := hslice z hzp i
      have hcircle : ∀ w : ℂ, ‖w‖ = 1 → G (Function.update z i w) = 0 := by
        intro w hw
        refine ih _ ⟨?_, ?_⟩
        · intro j hjT
          have hj : j ≠ i := by rintro rfl; exact hi hjT
          simp only [Function.update_apply, if_neg hj]
          exact hz.1 j (Finset.mem_insert_of_mem hjT)
        · intro j hjT
          by_cases hj : j = i
          · subst hj
            simpa using hw
          · simp only [Function.update_apply, if_neg hj]
            exact hz.2 j (by simp [hjT, hj])
      have := eqOn_zero_logAnnulus (hρ i) hg hcircle hzi
      simpa using this

/-- **The product torus is a uniqueness set for a polyannulus, slicewise
version.** -/
theorem eqOn_zero_polyannulus_of_slice {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {G : (d → ℂ) → ℂ}
    (hslice : ∀ z ∈ polyannulus ρ, ∀ i : d,
      AnalyticOnNhd ℂ (fun w => G (Function.update z i w)) (logAnnulus (ρ i)))
    (h0 : ∀ z ∈ unitTorus d, G z = 0) :
    ∀ z ∈ polyannulus ρ, G z = 0 := by
  intro z hz
  refine eqOn_zero_mixedAnnulus_of_slice hρ hslice h0 Finset.univ z ?_
  rwa [mixedAnnulus_univ]

/-- Two functions with holomorphic coordinate slices which agree on the torus
agree on the polyannulus. -/
theorem eqOn_polyannulus_of_slice {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {G H : (d → ℂ) → ℂ}
    (hslice : ∀ z ∈ polyannulus ρ, ∀ i : d,
      AnalyticOnNhd ℂ (fun w => G (Function.update z i w) - H (Function.update z i w))
        (logAnnulus (ρ i)))
    (h0 : ∀ z ∈ unitTorus d, G z = H z) :
    ∀ z ∈ polyannulus ρ, G z = H z := by
  have hzero := eqOn_zero_polyannulus_of_slice hρ (G := fun z => G z - H z) hslice
    (fun z hz => by rw [h0 z hz, sub_self])
  intro z hz
  have hzz : G z - H z = 0 := hzero z hz
  linear_combination hzz

end

end GaloisForLFunctions.HTGeometry
