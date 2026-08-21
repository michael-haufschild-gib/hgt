import GaloisForLFunctions.HTGeometry.KleinbockMargulis.SmoothGoodCube
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivative chains along lines

For a `C^k` function `f` the directional derivatives
`F j t = D^j f (z + t u) (u, …, u)` form a derivative chain of length `k`: differentiating
`F j` along the line and using `iteratedFDeriv_succ_apply_left` produces `F (j+1)`.

Composing with an invertible linear map turns coordinate lines into arbitrary lines, so the
hypotheses of Lemma 3.3 for `f ∘ T` are bounds on the directional derivatives of `f` in the
directions given by the columns of `T`.

## Main results

* `isDerivChain_line` — the chain along a line.
* `sandwichedChains_comp_linear` — the hypotheses of Lemma 3.3 for `f ∘ T`.
-/

open Set

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d : ℕ}

theorem update_eq_add_smul_single (x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    Function.update x i t = Function.update x i 0 + t • (Pi.single i (1 : ℝ)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Differentiating the directional derivative of order `j` along the line gives the one of
order `j + 1`. -/
theorem hasDerivAt_line_iteratedFDeriv {k j : ℕ} (hj : j < k) {f : (Fin d → ℝ) → ℝ}
    {z u : Fin d → ℝ} {t : ℝ} (hf : ContDiffAt ℝ ((k : ℕ)) f (z + t • u)) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ j f (z + s • u) (fun _ => u))
      (iteratedFDeriv ℝ (j + 1) f (z + t • u) (fun _ => u)) t := by
  have hline : HasDerivAt (fun s : ℝ => z + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add z
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) (z + t • u) :=
    hf.differentiableAt_iteratedFDeriv (by exact_mod_cast hj)
  have hcomp : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ j f (z + s • u))
      (fderiv ℝ (iteratedFDeriv ℝ j f) (z + t • u) u) t :=
    HasFDerivAt.comp_hasDerivAt t hdiff.hasFDerivAt hline
  have hev := HasFDerivAt.comp_hasDerivAt t
    (ContinuousLinearMap.hasFDerivAt
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => (Fin d → ℝ)) ℝ (fun _ => u))) hcomp
  have hval : (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => (Fin d → ℝ)) ℝ (fun _ => u))
      (fderiv ℝ (iteratedFDeriv ℝ j f) (z + t • u) u)
      = iteratedFDeriv ℝ (j + 1) f (z + t • u) (fun _ => u) := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rw [hval] at hev
  exact hev

/-- The directional derivatives along a line form a derivative chain of length `k`. -/
theorem isDerivChain_line {k : ℕ} {f : (Fin d → ℝ) → ℝ} {U : Set (Fin d → ℝ)}
    (hf : ∀ y ∈ U, ContDiffAt ℝ ((k : ℕ)) f y) (z u : Fin d → ℝ) :
    IsDerivChain k (fun j t => iteratedFDeriv ℝ j f (z + t • u) (fun _ => u))
      {t | z + t • u ∈ U} :=
  fun _ hj _ ht => hasDerivAt_line_iteratedFDeriv hj (hf _ ht)

/-- **The hypotheses of Lemma 3.3 for `f ∘ T`.**  If `f` is `C^k` on `U` and its `k`-th
directional derivatives in the directions `T e_i` are bounded between `A₂` and `A₁` there, then
`f ∘ T` has sandwiched coordinate chains on `T⁻¹ U`. -/
theorem sandwichedChains_comp_linear {k : ℕ} {f : (Fin d → ℝ) → ℝ} {U : Set (Fin d → ℝ)}
    (hcont : ContinuousOn f U) (hf : ∀ y ∈ U, ContDiffAt ℝ ((k : ℕ)) f y)
    (T : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) {A₁ A₂ : ℝ}
    (hbd : ∀ y ∈ U, ∀ i : Fin d,
      |iteratedFDeriv ℝ k f y (fun _ => T (Pi.single i (1 : ℝ)))| ≤ A₁ ∧
      A₂ ≤ |iteratedFDeriv ℝ k f y (fun _ => T (Pi.single i (1 : ℝ)))|) :
    SandwichedChains k ((fun y => T y) ⁻¹' U) (f ∘ T) A₁ A₂ where
  cont := hcont.comp T.continuous.continuousOn fun _ hx => hx
  chain := by
    intro i x
    set u : Fin d → ℝ := T (Pi.single i (1 : ℝ)) with hu
    set z : Fin d → ℝ := T (Function.update x i 0) with hz
    have hTupd : ∀ t : ℝ, T (Function.update x i t) = z + t • u := by
      intro t
      rw [update_eq_add_smul_single x i t, map_add, map_smul, hz, hu]
    have hsets : {t : ℝ | Function.update x i t ∈ (fun y => T y) ⁻¹' U}
        = {t : ℝ | z + t • u ∈ U} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [hTupd t]
    refine ⟨fun j t => iteratedFDeriv ℝ j f (z + t • u) (fun _ => u), fun t => ?_, ?_, ?_⟩
    · show iteratedFDeriv ℝ 0 f (z + t • u) (fun _ => u) = (f ∘ T) (Function.update x i t)
      rw [iteratedFDeriv_zero_apply]
      show f (z + t • u) = f (T (Function.update x i t))
      rw [hTupd t]
    · rw [hsets]
      exact isDerivChain_line hf z u
    · intro t ht
      have htU : z + t • u ∈ U := by
        rw [← hTupd t]
        exact ht
      exact hbd _ htU i

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
