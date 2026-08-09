import Mathlib

/-!
# A self-improving bound on a compact set forces vanishing

If on a compact set every bound `M` for `‖G‖` improves to the bound `θ·M` with `θ < 1`, then `G`
vanishes on that set: the maximum, which compactness supplies, satisfies `M ≤ θ·M`.

This is the mechanism of the periodicity step of a Siegel-type count.  There the compact set is a
fundamental parallelotope, the improvement comes from the Schwarz estimate on the small polydiscs
of a finite cover, and periodicity is what identifies the supremum over the small polydiscs with
the supremum over the large ones — without that identification the improvement is not available and
the counting argument is false.

* **`eqOn_zero_of_le_mul_bound`**.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **A self-improving bound forces vanishing.** -/
theorem eqOn_zero_of_le_mul_bound {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] {G : X → E} {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hG : ContinuousOn (fun x => ‖G x‖) K)
    {θ : ℝ} (hθ1 : θ < 1)
    (hbound : ∀ M : ℝ, (∀ y ∈ K, ‖G y‖ ≤ M) → ∀ x ∈ K, ‖G x‖ ≤ θ * M) :
    ∀ x ∈ K, G x = 0 := by
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hK.exists_isMaxOn hne hG
  set M : ℝ := ‖G x₀‖ with hM
  have hMbound : ∀ y ∈ K, ‖G y‖ ≤ M := fun y hy => hx₀max hy
  have hM0 : 0 ≤ M := norm_nonneg _
  have hstep : M ≤ θ * M := hbound M hMbound x₀ hx₀K
  have hMzero : M = 0 := by nlinarith
  intro x hx
  have hx' := hMbound x hx
  rw [hMzero] at hx'
  exact norm_le_zero_iff.mp hx'

end GaloisForLFunctions.HTGeometry
