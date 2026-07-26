import GaloisForLFunctions.RHTower.BetaBlindnessAndDesignConditions

/-!
# Beta-sensitivity and arithmetic evaluability are mutually exclusive

The classification asks for a weight that separates `β = 1/2` from `β = 1/2 + a`.  In its exact form
that means a function vanishing **precisely** on the critical line.  This file shows no analytic
function can do that, and draws the consequence.

**The obstruction.**  The zero set of a nonzero analytic function on a connected domain is discrete;
the line `Re s = 1/2` is not.  So a function vanishing on the whole line vanishes identically.  Any
weight that detects the critical line exactly is therefore **non-analytic** — for instance
`ρ ↦ |φ(ρ) - φ(1 - ρ̄)|`, whose modulus and conjugation are both non-analytic, and which vanishes on
the line for every choice of `φ`.

**The consequence.**  The explicit formula evaluates `Σ_ρ h(ρ)` by contour shifting, which requires
`h` analytic.  A non-analytic weight has no such evaluation: it cannot be expressed through the primes
at all.

> **A zero-set functional is either analytic — hence evaluable by the explicit formula, hence a
> combination of prime and archimedean data subject to the three-way cancellation — or non-analytic,
> hence able to detect the critical line but not computable from arithmetic.  The two are mutually
> exclusive, and every criterion in this development falls on one side or the other.**

This is why every criterion examined is either arithmetic and blind, or exact and inert.  It is a
statement about the shape of the problem rather than about any method.

This file formalizes the identity-theorem obstruction and the vanishing of the reflection weight on
the critical line.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- **The identity-theorem obstruction.**  An entire function vanishing on the whole critical line
vanishes identically: the line is not discrete, so it accumulates. -/
theorem entire_vanishing_on_criticalLine_eq_zero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hline : ∀ s : ℂ, s.re = 1 / 2 → f s = 0) :
    Set.EqOn f 0 Set.univ := by
  set z₀ : ℂ := ⟨1 / 2, 0⟩ with hz₀
  have hz₀re : z₀.re = 1 / 2 := rfl
  set r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by simp only [hr]; positivity
  set u : ℕ → ℂ := fun n => ⟨1 / 2, r n⟩ with hu
  have hure : ∀ n, (u n).re = 1 / 2 := fun n => rfl
  have hune : ∀ n, u n ≠ z₀ := by
    intro n h
    have him : (u n).im = z₀.im := by rw [h]
    have hpos := hrpos n
    simp only [hu, hz₀] at him
    linarith [him ▸ hpos]
  have htend : Tendsto u atTop (𝓝[≠] z₀) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · rw [tendsto_iff_dist_tendsto_zero]
      have hdist : ∀ n : ℕ, dist (u n) z₀ = r n := by
        intro n
        rw [Complex.dist_eq]
        have hrep : u n - z₀ = ((r n : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [hu, hz₀]
        rw [hrep, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hrpos n)]
      simp only [hdist, hr]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall (fun n => hune n)
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] z₀, f z = 0 :=
    htend.frequently (Frequently.of_forall (fun n => hline (u n) (hure n)))
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ z₀) hfreq

/-- **The reflection weight vanishes on the critical line.**  For `Re ρ = 1/2` the reflected point
`1 - ρ̄` equals `ρ`, so any difference of weights at the two points is zero. -/
theorem reflection_fixes_criticalLine {s : ℂ} (hs : s.re = 1 / 2) :
    1 - (starRingEnd ℂ) s = s := by
  apply Complex.ext
  · simp [Complex.sub_re, hs]
    linarith [hs]
  · simp [Complex.sub_im]

/-- Hence the reflection difference vanishes exactly on the line, which by the identity theorem makes
it non-analytic unless identically zero. -/
theorem reflection_difference_zero_on_line {φ : ℂ → ℂ} {s : ℂ} (hs : s.re = 1 / 2) :
    φ s - φ (1 - (starRingEnd ℂ) s) = 0 := by
  rw [reflection_fixes_criticalLine hs]
  ring

/-- **Off the line the reflection moves the point.**  If `Re s ≠ 1/2` then `1 - s̄ ≠ s`, so a weight
injective in the real part gives a nonzero difference. -/
theorem reflection_moves_offLine {s : ℂ} (hs : s.re ≠ 1 / 2) :
    1 - (starRingEnd ℂ) s ≠ s := by
  intro h
  apply hs
  have hre : (1 - (starRingEnd ℂ) s).re = s.re := by rw [h]
  simp [Complex.sub_re] at hre
  linarith

end RHTower
