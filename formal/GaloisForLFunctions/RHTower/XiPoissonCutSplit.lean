import GaloisForLFunctions.RHTower.XiPoissonCutHalfPlaneDecay
import GaloisForLFunctions.RHTower.XiPoissonVerticalSplit

/-!
# Splitting a cut trace at its own bottom

Two splittings of the full trace -- below a height and at or below it -- differ by the finite shell at
that height, so subtracting them splits the cut trace into that shell and the strictly higher part.
Everything is a finite-set-plus-complement split of the *full* divisor, so no reasoning inside
subtypes is needed.

The strictly higher part is then controlled by the same weighted tail bound as before: the spectral
gap above the height beats the bottom-height weight, at a cost of `exp (|u|/2)` in the vertical
direction.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

theorem tsum_congr_set {s t : Set XiZeroCopy} (h : s = t) (f : XiZeroCopy → ℂ) :
    ∑' q : s, f (q : XiZeroCopy) = ∑' q : t, f (q : XiZeroCopy) := by
  subst h; rfl

theorem finite_xiPoissonStrictShell (g : ℝ) :
    {q : XiZeroCopy | (xiPoissonPoint q).re < g}.Finite := by
  refine (finite_xiPoissonShell g).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  exact le_of_lt hq

/-- The copies strictly below a height. -/
def xiPoissonStrictLower (g : ℝ) : Finset XiZeroCopy := (finite_xiPoissonStrictShell g).toFinset

/-- The copies at or below a height. -/
def xiPoissonLower (g : ℝ) : Finset XiZeroCopy := (finite_xiPoissonShell g).toFinset

/-- The copies strictly above a height. -/
def xiPoissonStrictAbove (g : ℝ) : Set XiZeroCopy := {q : XiZeroCopy | g < (xiPoissonPoint q).re}

theorem compl_xiPoissonStrictLower (g : ℝ) :
    ((xiPoissonStrictLower g : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ = xiPoissonCut g := by
  ext q
  simp only [Set.mem_compl_iff, Finset.mem_coe, xiPoissonStrictLower, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, xiPoissonCut, not_lt]

theorem compl_xiPoissonLower (g : ℝ) :
    ((xiPoissonLower g : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ = xiPoissonStrictAbove g := by
  ext q
  simp only [Set.mem_compl_iff, Finset.mem_coe, xiPoissonLower, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, xiPoissonStrictAbove, not_le]

theorem xiPoissonStrictLower_subset (g : ℝ) : xiPoissonStrictLower g ⊆ xiPoissonLower g := by
  intro q hq
  simp only [xiPoissonStrictLower, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
  simp only [xiPoissonLower, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact le_of_lt hq

/-- The strictly-above part of the trace. -/
def xiPoissonStrictAboveSum (g : ℝ) (τ : ℂ) : ℂ :=
  ∑' q : xiPoissonStrictAbove g, xiPoissonTerm τ (q : XiZeroCopy)

theorem xiPoissonTraceC_split_strictLower {τ : ℂ} (hτ : 0 < τ.re) (g : ℝ) :
    xiPoissonTraceC τ =
      (∑ q ∈ xiPoissonStrictLower g, xiPoissonTerm τ q) + xiPoissonCutTraceC g τ := by
  have hsum : Summable (fun q : XiZeroCopy => xiPoissonTerm τ q) :=
    (summable_norm_xiPoissonTerm hτ).of_norm
  have h := hsum.sum_add_tsum_compl (s := xiPoissonStrictLower g)
  have hset := tsum_congr_set (compl_xiPoissonStrictLower g) (fun q => xiPoissonTerm τ q)
  show (∑' q : XiZeroCopy, xiPoissonTerm τ q) = _
  rw [← h, hset]
  rfl

theorem xiPoissonTraceC_split_lower {τ : ℂ} (hτ : 0 < τ.re) (g : ℝ) :
    xiPoissonTraceC τ =
      (∑ q ∈ xiPoissonLower g, xiPoissonTerm τ q) + xiPoissonStrictAboveSum g τ := by
  have hsum : Summable (fun q : XiZeroCopy => xiPoissonTerm τ q) :=
    (summable_norm_xiPoissonTerm hτ).of_norm
  have h := hsum.sum_add_tsum_compl (s := xiPoissonLower g)
  have hset := tsum_congr_set (compl_xiPoissonLower g) (fun q => xiPoissonTerm τ q)
  show (∑' q : XiZeroCopy, xiPoissonTerm τ q) = _
  rw [← h, hset]
  rfl

/-- **The cut trace splits at its own bottom.**  The middle term is the shell at height exactly
`g`. -/
theorem xiPoissonCutTraceC_split {τ : ℂ} (hτ : 0 < τ.re) (g : ℝ) :
    xiPoissonCutTraceC g τ =
      (∑ q ∈ xiPoissonLower g \ xiPoissonStrictLower g, xiPoissonTerm τ q) +
        xiPoissonStrictAboveSum g τ := by
  have h1 := xiPoissonTraceC_split_strictLower hτ g
  have h2 := xiPoissonTraceC_split_lower hτ g
  have h3 := Finset.sum_sdiff (f := fun q => xiPoissonTerm τ q)
    (xiPoissonStrictLower_subset g)
  rw [h1] at h2
  rw [← h3] at h2
  linear_combination (norm := ring_nf) h2

/-- **The weighted tail bound above a height.** -/
theorem exp_mul_norm_xiPoissonStrictAboveSum_le {σ g g₂ : ℝ} (hσ : 0 < σ)
    (hg₂ : ∀ q ∈ xiPoissonStrictAbove g, g₂ ≤ (xiPoissonPoint q).re)
    {v : ℝ} (hv : 0 ≤ v) (u : ℝ) :
    Real.exp (g * v) *
        ‖xiPoissonStrictAboveSum g (((σ + v : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      Real.exp (|u| / 2) * Real.exp (-((g₂ - g) * v)) *
        ∑' q : xiPoissonStrictAbove g, xiPoissonWeight σ (q : XiZeroCopy) := by
  have hsv : 0 < σ + v := by linarith
  have hre : 0 < (((σ + v : ℝ) : ℂ) + (u : ℂ) * I).re := by rw [re_vertical]; exact hsv
  have hsumnorm := summable_norm_xiPoissonTerm hre
  have hsumσ : Summable (fun q : xiPoissonStrictAbove g => xiPoissonWeight σ (q : XiZeroCopy)) :=
    (summable_xiPoissonWeight hσ).subtype _
  have hterm : ∀ q : xiPoissonStrictAbove g,
      Real.exp (g * v) *
          ‖xiPoissonTerm (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ ≤
        Real.exp (|u| / 2) * Real.exp (-((g₂ - g) * v)) *
          xiPoissonWeight σ (q : XiZeroCopy) := by
    intro q
    have hR : g₂ ≤ (xiPoissonPoint (q : XiZeroCopy)).re := hg₂ _ q.2
    have hJ : |(xiPoissonPoint (q : XiZeroCopy)).im| < 1 / 2 :=
      abs_xiPoissonPoint_im_lt_half _
    rw [norm_xiPoissonTerm, re_vertical, im_vertical, xiPoissonWeight,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have huJ : u * (xiPoissonPoint (q : XiZeroCopy)).im ≤ |u| / 2 := by
      calc u * (xiPoissonPoint (q : XiZeroCopy)).im
          ≤ |u * (xiPoissonPoint (q : XiZeroCopy)).im| := le_abs_self _
        _ = |u| * |(xiPoissonPoint (q : XiZeroCopy)).im| := abs_mul _ _
        _ ≤ |u| * (1 / 2) := mul_le_mul_of_nonneg_left hJ.le (abs_nonneg _)
        _ = |u| / 2 := by ring
    nlinarith [hR, hv, huJ]
  calc Real.exp (g * v) * ‖xiPoissonStrictAboveSum g (((σ + v : ℝ) : ℂ) + (u : ℂ) * I)‖
      ≤ Real.exp (g * v) *
          ∑' q : xiPoissonStrictAbove g,
            ‖xiPoissonTerm (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ = ∑' q : xiPoissonStrictAbove g,
          Real.exp (g * v) *
            ‖xiPoissonTerm (((σ + v : ℝ) : ℂ) + (u : ℂ) * I) (q : XiZeroCopy)‖ :=
        (tsum_mul_left).symm
    _ ≤ ∑' q : xiPoissonStrictAbove g,
          Real.exp (|u| / 2) * Real.exp (-((g₂ - g) * v)) *
            xiPoissonWeight σ (q : XiZeroCopy) :=
        Summable.tsum_le_tsum hterm (((hsumnorm.subtype _)).mul_left _) (hsumσ.mul_left _)
    _ = Real.exp (|u| / 2) * Real.exp (-((g₂ - g) * v)) *
          ∑' q : xiPoissonStrictAbove g, xiPoissonWeight σ (q : XiZeroCopy) := tsum_mul_left

end

end RHTower
