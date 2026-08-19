import Mathlib

/-!
# Gluing an exhausting family of half planes

A family of holomorphic functions, the `n`-th defined on `{Re s > A n}`, all agreeing on one fixed
half plane, is one entire function as soon as the abscissas `A n` are unbounded below.  The
agreement on the whole overlap is the identity theorem; the entire representative is obtained by
evaluating at the first admissible index.
-/

noncomputable section

open Filter

namespace GaloisForLFunctions.HTGeometry

/-- The first index whose half plane contains `s`. -/
def glueIndex (A : ℕ → ℝ) (hA : ∀ s : ℂ, ∃ n, A n < s.re) (s : ℂ) : ℕ := Nat.find (hA s)

theorem glueIndex_spec (A : ℕ → ℝ) (hA : ∀ s : ℂ, ∃ n, A n < s.re) (s : ℂ) :
    A (glueIndex A hA s) < s.re := Nat.find_spec (hA s)

/-- The glued function. -/
def glueSeq (A : ℕ → ℝ) (hA : ∀ s : ℂ, ∃ n, A n < s.re) (H : ℕ → ℂ → ℂ) : ℂ → ℂ :=
  fun s => H (glueIndex A hA s) s

theorem glueSeq_eq {A : ℕ → ℝ} {hA : ∀ s : ℂ, ∃ n, A n < s.re} {H : ℕ → ℂ → ℂ}
    (hcompat : ∀ m n : ℕ, ∀ s : ℂ, A m < s.re → A n < s.re → H m s = H n s) {n : ℕ} {s : ℂ}
    (hs : A n < s.re) : glueSeq A hA H s = H n s :=
  hcompat _ _ s (glueIndex_spec A hA s) hs

theorem differentiable_glueSeq {A : ℕ → ℝ} {hA : ∀ s : ℂ, ∃ n, A n < s.re} {H : ℕ → ℂ → ℂ}
    (hcompat : ∀ m n : ℕ, ∀ s : ℂ, A m < s.re → A n < s.re → H m s = H n s)
    (hdiff : ∀ n : ℕ, ∀ s : ℂ, A n < s.re → DifferentiableAt ℂ (H n) s) :
    Differentiable ℂ (glueSeq A hA H) := by
  intro s
  obtain ⟨n, hn⟩ := hA s
  have hopen : IsOpen {z : ℂ | A n < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : glueSeq A hA H =ᶠ[nhds s] H n := by
    filter_upwards [hopen.mem_nhds hn] with z hz
    exact glueSeq_eq hcompat hz
  exact (hdiff n s hn).congr_of_eventuallyEq hev

/-- **Continuation from an exhausting family.**  Holomorphic functions on half planes whose
abscissas tend to `-∞`, all agreeing on one base half plane, come from a single entire function. -/
theorem exists_entire_of_halfPlane_family {A : ℕ → ℝ} {H : ℕ → ℂ → ℂ} {A₀ : ℝ}
    (hA : ∀ C : ℝ, ∃ n, A n < C)
    (hdiff : ∀ n : ℕ, ∀ s : ℂ, A n < s.re → DifferentiableAt ℂ (H n) s)
    (hagree : ∀ n : ℕ, ∀ s : ℂ, A₀ < s.re → H n s = H 0 s) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ n : ℕ, ∀ s : ℂ, A n < s.re → g s = H n s := by
  have hAex : ∀ s : ℂ, ∃ n, A n < s.re := fun s => hA s.re
  have hcompat : ∀ m n : ℕ, ∀ s : ℂ, A m < s.re → A n < s.re → H m s = H n s := by
    intro m n s hm hn
    set B : ℝ := max (A m) (A n) with hBdef
    set U : Set ℂ := {z : ℂ | B < z.re} with hUdef
    have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUconv : Convex ℝ U := by
      refine convex_halfSpace_gt ?_ B
      exact { map_add := fun x y => Complex.add_re x y,
              map_smul := fun c x => by simp }
    have hUconn : IsPreconnected U := hUconv.isPreconnected
    have hmU : AnalyticOnNhd ℂ (H m) U := by
      refine DifferentiableOn.analyticOnNhd ?_ hUopen
      intro z hz
      exact ((hdiff m z (lt_of_le_of_lt (le_max_left _ _) hz)).differentiableWithinAt)
    have hnU : AnalyticOnNhd ℂ (H n) U := by
      refine DifferentiableOn.analyticOnNhd ?_ hUopen
      intro z hz
      exact ((hdiff n z (lt_of_le_of_lt (le_max_right _ _) hz)).differentiableWithinAt)
    -- a base point where the two agree on a neighbourhood
    set c : ℝ := max B A₀ + 1 with hcdef
    set z₀ : ℂ := (c : ℂ) with hz₀def
    have hz₀re : z₀.re = c := by
      rw [hz₀def, Complex.ofReal_re]
    have hz₀U : z₀ ∈ U := by
      rw [hUdef, Set.mem_setOf_eq, hz₀re, hcdef]
      have := le_max_left B A₀
      linarith
    have hVopen : IsOpen {z : ℂ | max B A₀ < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hz₀V : z₀ ∈ {z : ℂ | max B A₀ < z.re} := by
      rw [Set.mem_setOf_eq, hz₀re, hcdef]
      linarith
    have heq : H m =ᶠ[nhds z₀] H n := by
      filter_upwards [hVopen.mem_nhds hz₀V] with z hz
      have hzA₀ : A₀ < z.re := lt_of_le_of_lt (le_max_right B A₀) hz
      rw [hagree m z hzA₀, hagree n z hzA₀]
    have hEq := hmU.eqOn_of_preconnected_of_eventuallyEq hnU hUconn hz₀U heq
    refine hEq ?_
    rw [hUdef, Set.mem_setOf_eq, hBdef]
    exact max_lt hm hn
  refine ⟨glueSeq A hAex H, differentiable_glueSeq hcompat hdiff, ?_⟩
  intro n s hs
  exact glueSeq_eq hcompat hs

end GaloisForLFunctions.HTGeometry

end
