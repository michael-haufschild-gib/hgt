/-
# `f_c^[n]` is a covering map on the escape-level subtypes

For `hlift` (the last topological input to the connected Böttcher branch) we need `f_c^[n+1]` to be a
covering `escapeLevel c(n+1) → escapeLevel c 0 = escapeOpen c`, so that a loop's lift through the
`ρ` tower is unique. Mathlib gives the single quadratic as a covering per level (Brick A,
`isCoveringMap_quadratic_escapeLevel_succ`); this file composes those via `isCoveringMap_comp`, with
the finite-fibre input supplied by `quadratic_iterate_fiber_finite` (roots of the degree-`2ⁿ`
iterate polynomial). Base case is a single quadratic (no identity-covering needed).
-/
import GaloisForLFunctions.Bottcher.ConnectedPi1
import GaloisForLFunctions.Bottcher.CoveringComp
import GaloisForLFunctions.Bottcher.BasinBranching

open Topology
namespace Bottcher
noncomputable section
variable {c : ℂ}

theorem iterate_quadratic_mapsTo (c : ℂ) (m n : ℕ) {z : ℂ} (hz : z ∈ escapeLevel c (m + n)) :
    (quadratic c)^[n] z ∈ escapeLevel c m := by
  have h : (quadratic c)^[m] ((quadratic c)^[n] z) ∈ escapeOpen c := by
    rw [← Function.iterate_add_apply]; exact hz
  exact h

/-- The subtype fibre of `f^[n] : escapeLevel c(m+n) → escapeLevel c m` is finite. -/
theorem iterMap_fiber_finite (c : ℂ) (m n : ℕ) (w : escapeLevel c m) :
    ((fun z : escapeLevel c (m + n) =>
      (⟨(quadratic c)^[n] (z : ℂ), iterate_quadratic_mapsTo c m n z.2⟩ : escapeLevel c m))
        ⁻¹' {w}).Finite := by
  refine Set.Finite.of_finite_image ?_ (Subtype.val_injective.injOn)
  apply (quadratic_iterate_fiber_finite c n (w : ℂ)).subset
  rintro u ⟨z, hz, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
  exact congrArg Subtype.val hz

/-- **`f^[n+1]` is a covering `escapeLevel c(m+n+1) → escapeLevel c m`.** Induction on `n`, base
`n=0` is the single-step Brick A covering, step peels one outer quadratic
(`isCoveringMap_comp` with the finite fibre `iterMap_fiber_finite`). -/
theorem isCoveringMap_iterate_succ (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) (m n : ℕ) :
    IsCoveringMap (fun z : escapeLevel c (m + n + 1) =>
      (⟨(quadratic c)^[n + 1] (z : ℂ), iterate_quadratic_mapsTo c m (n + 1) z.2⟩
        : escapeLevel c m)) := by
  induction n with
  | zero =>
    have hfun : (fun z : escapeLevel c (m + 0 + 1) =>
          (⟨(quadratic c)^[0 + 1] (z : ℂ), iterate_quadratic_mapsTo c m (0 + 1) z.2⟩
            : escapeLevel c m))
        = (fun z : escapeLevel c (m + 1) =>
          (⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c m z.2⟩ : escapeLevel c m)) := by
      funext z
      apply Subtype.ext
      show (quadratic c)^[0 + 1] (z : ℂ) = quadratic c (z : ℂ)
      rw [Function.iterate_one]
    rw [hfun]
    exact isCoveringMap_quadratic_escapeLevel_succ c m (hc m)
  | succ k ih =>
    -- f^[k+2] = f^[k+1] ∘ (single quadratic escapeLevel(m+k+2) → escapeLevel(m+k+1))
    have hfun : (fun z : escapeLevel c (m + (k + 1) + 1) =>
          (⟨(quadratic c)^[k + 1 + 1] (z : ℂ), iterate_quadratic_mapsTo c m (k + 1 + 1) z.2⟩
            : escapeLevel c m))
        = (fun z : escapeLevel c (m + k + 1) =>
            (⟨(quadratic c)^[k + 1] (z : ℂ), iterate_quadratic_mapsTo c m (k + 1) z.2⟩
              : escapeLevel c m))
          ∘ (fun z : escapeLevel c (m + (k + 1) + 1) =>
            (⟨quadratic c (z : ℂ), quadratic_mapsTo_escapeLevel c (m + k + 1) z.2⟩
              : escapeLevel c (m + k + 1))) := by
      funext z
      apply Subtype.ext
      show (quadratic c)^[k + 1 + 1] (z : ℂ) = (quadratic c)^[k + 1] (quadratic c (z : ℂ))
      rw [← Function.iterate_succ_apply]
    rw [hfun]
    exact isCoveringMap_comp
      (isCoveringMap_quadratic_escapeLevel_succ c (m + k + 1) (hc (m + k + 1)))
      ih
      (iterMap_fiber_finite c m (k + 1))

end
end Bottcher
