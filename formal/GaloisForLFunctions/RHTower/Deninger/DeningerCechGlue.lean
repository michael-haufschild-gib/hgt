import GaloisForLFunctions.RHTower.Deninger.DeningerCechHomotopy

/-!
# Degree zero of the Čech complex is the global sections

A zero-cochain killed by the Čech differential is a compatible family, and a compatible family of
continuous functions on an open cover glues to a single continuous function: the glued function is
locally one of the given ones, and any two glued functions agree.

Together with the exactness in positive degrees this is the whole computation of the Čech complex
of a fine coefficient: the global sections in degree zero and nothing above.

* `deningerCechGlue` : a compatible family glues.
* `deningerCechGlue_unique` : the glued function is unique.
* `deningerCechCocycle_zero_iff` : being a zero-cocycle is being a compatible family.
-/

namespace RHTower

open Set Topology

section Glue

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

omit [Fintype ι] in
/-- **A compatible family of continuous functions glues.** -/
theorem deningerCechGlue {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) {c : ι → X → ℝ} (hcont : ∀ i, ContinuousOn (c i) (U i))
    (hcompat : ∀ (i j : ι) (x : X), x ∈ U i → x ∈ U j → c i x = c j x) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ (i : ι) (x : X), x ∈ U i → g x = c i x := by
  classical
  refine ⟨fun x => c (hcov x).choose x, ?_, fun i x hx => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨i, hi⟩ := hcov x
    have hmem : U i ∈ 𝓝 x := (hU i).mem_nhds hi
    have heq : (fun y => c (hcov y).choose y) =ᶠ[𝓝 x] c i := by
      filter_upwards [hmem] with y hy
      exact hcompat (hcov y).choose i y (hcov y).choose_spec hy
    refine ContinuousAt.congr ?_ heq.symm
    exact (hcont i x hi).continuousAt hmem
  · exact hcompat (hcov x).choose i x (hcov x).choose_spec hx

omit [TopologicalSpace X] [Fintype ι] in
/-- **The glued function is unique.** -/
theorem deningerCechGlue_unique {U : ι → Set X} (hcov : ∀ x : X, ∃ i, x ∈ U i)
    {c : ι → X → ℝ} {g g' : X → ℝ}
    (hg : ∀ (i : ι) (x : X), x ∈ U i → g x = c i x)
    (hg' : ∀ (i : ι) (x : X), x ∈ U i → g' x = c i x) : g = g' := by
  funext x
  obtain ⟨i, hi⟩ := hcov x
  rw [hg i x hi, hg' i x hi]

omit [TopologicalSpace X] [Fintype ι] in
/-- **A zero-cochain is a cocycle exactly when it is a compatible family.**  The Čech differential
in degree zero is the difference of the two restrictions. -/
theorem deningerCechCocycle_zero_iff (c : DeningerCechCochain X ι 0) (σ : Fin 2 → ι) (x : X) :
    deningerCechD c σ x = c (fun _ => σ 1) x - c (fun _ => σ 0) x := by
  rw [deningerCechD, Fin.sum_univ_two]
  have h0 : (σ ∘ Fin.succAbove 0 : Fin 1 → ι) = fun _ => σ 1 := by
    funext s
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    have hface : (Fin.succAbove 0 (0 : Fin 1) : Fin 2) = 1 := by decide
    rw [Function.comp_apply, hface]
  have h1 : (σ ∘ Fin.succAbove 1 : Fin 1 → ι) = fun _ => σ 0 := by
    funext s
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    have hface : (Fin.succAbove 1 (0 : Fin 1) : Fin 2) = 0 := by decide
    rw [Function.comp_apply, hface]
  rw [h0, h1]
  simp
  ring

end Glue

end RHTower
