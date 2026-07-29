import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The odd Dirichlet kernel

Summing the odd cosine harmonics telescopes:

```
2 sin θ · cos((2k+1)θ) = sin(2(k+1)θ) - sin(2kθ),
```

so away from the zeros of the sine

```
∑_{k < N} cos((2k+1)θ) = sin(2Nθ) / (2 sin θ),      ∑_{k < N} sin((2k+1)θ) = sin(Nθ)² / sin θ.
```

Both partial sums are therefore bounded uniformly in `N` by `1/(2|sin θ|)` and `1/|sin θ|`.  That
uniform bound is the Dirichlet-test input for the conditionally convergent odd harmonic series
`∑ sin((2k+1)θ)/(2k+1)`.

`RHTower.sum_cos_closed_form` gives the general arithmetic-progression cosine sum in polar form,
under a complex hypothesis identifying `e^{iβ}/(1 - e^{iθ})`; the closed forms here are the real
specialisation at `β = θ`, common difference `2θ`, and are proved directly by telescoping.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- Product-to-sum in the form used by the telescoping. -/
theorem two_mul_sin_mul_cos (A B : ℝ) :
    2 * Real.sin A * Real.cos B = Real.sin (A + B) - Real.sin (B - A) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- Product-to-sum for the sine telescoping. -/
theorem two_mul_sin_mul_sin (A B : ℝ) :
    2 * Real.sin A * Real.sin B = Real.cos (B - A) - Real.cos (A + B) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- **The odd cosine kernel.** -/
theorem sum_cos_odd {θ : ℝ} (hθ : Real.sin θ ≠ 0) (N : ℕ) :
    ∑ k ∈ range N, Real.cos ((2 * (k : ℝ) + 1) * θ)
      = Real.sin (2 * (N : ℝ) * θ) / (2 * Real.sin θ) := by
  have hne : (2 : ℝ) * Real.sin θ ≠ 0 := mul_ne_zero two_ne_zero hθ
  have hsum : (2 * Real.sin θ) * ∑ k ∈ range N, Real.cos ((2 * (k : ℝ) + 1) * θ)
      = Real.sin (2 * (N : ℝ) * θ) := by
    rw [Finset.mul_sum]
    have hcongr : ∀ k ∈ range N,
        2 * Real.sin θ * Real.cos ((2 * (k : ℝ) + 1) * θ)
          = (fun j : ℕ => Real.sin (2 * (j : ℝ) * θ)) (k + 1)
            - (fun j : ℕ => Real.sin (2 * (j : ℝ) * θ)) k := by
      intro k _
      rw [two_mul_sin_mul_cos]
      congr 2 <;> push_cast <;> ring
    rw [Finset.sum_congr rfl hcongr]
    exact (Finset.sum_range_sub (fun j : ℕ => Real.sin (2 * (j : ℝ) * θ)) N).trans (by simp)
  rw [eq_div_iff hne, mul_comm]
  exact hsum

/-- **The odd sine kernel.** -/
theorem sum_sin_odd {θ : ℝ} (hθ : Real.sin θ ≠ 0) (N : ℕ) :
    ∑ k ∈ range N, Real.sin ((2 * (k : ℝ) + 1) * θ)
      = Real.sin ((N : ℝ) * θ) ^ 2 / Real.sin θ := by
  have hne : (2 : ℝ) * Real.sin θ ≠ 0 := mul_ne_zero two_ne_zero hθ
  have hsum : (2 * Real.sin θ) * ∑ k ∈ range N, Real.sin ((2 * (k : ℝ) + 1) * θ)
      = 1 - Real.cos (2 * (N : ℝ) * θ) := by
    rw [Finset.mul_sum]
    have hcongr : ∀ k ∈ range N,
        2 * Real.sin θ * Real.sin ((2 * (k : ℝ) + 1) * θ)
          = (fun j : ℕ => -Real.cos (2 * (j : ℝ) * θ)) (k + 1)
            - (fun j : ℕ => -Real.cos (2 * (j : ℝ) * θ)) k := by
      intro k _
      rw [two_mul_sin_mul_sin]
      have h1 : (2 * (k : ℝ) + 1) * θ - θ = 2 * (k : ℝ) * θ := by ring
      have h2 : θ + (2 * (k : ℝ) + 1) * θ = 2 * ((k : ℝ) + 1) * θ := by ring
      rw [h1, h2]
      push_cast
      ring
    rw [Finset.sum_congr rfl hcongr]
    refine (Finset.sum_range_sub (fun j : ℕ => -Real.cos (2 * (j : ℝ) * θ)) N).trans ?_
    simp
    ring
  have hhalf : Real.cos (2 * (N : ℝ) * θ) = 1 - 2 * Real.sin ((N : ℝ) * θ) ^ 2 := by
    have := Real.cos_two_mul' ((N : ℝ) * θ)
    rw [show 2 * (N : ℝ) * θ = 2 * ((N : ℝ) * θ) by ring]
    linarith [Real.sin_sq_add_cos_sq ((N : ℝ) * θ), Real.cos_two_mul ((N : ℝ) * θ)]
  rw [eq_div_iff hθ]
  rw [hhalf] at hsum
  linarith [hsum]

/-- Uniform boundedness of the odd cosine partial sums: the Dirichlet-test input. -/
theorem abs_sum_cos_odd_le {θ : ℝ} (hθ : Real.sin θ ≠ 0) (N : ℕ) :
    |∑ k ∈ range N, Real.cos ((2 * (k : ℝ) + 1) * θ)| ≤ 1 / (2 * |Real.sin θ|) := by
  rw [sum_cos_odd hθ, abs_div, abs_mul]
  have habs : (0 : ℝ) < |Real.sin θ| := abs_pos.mpr hθ
  have hnum : |Real.sin (2 * (N : ℝ) * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hden : |(2 : ℝ)| = 2 := by norm_num
  rw [hden]
  gcongr

/-- Uniform boundedness of the odd sine partial sums. -/
theorem abs_sum_sin_odd_le {θ : ℝ} (hθ : Real.sin θ ≠ 0) (N : ℕ) :
    |∑ k ∈ range N, Real.sin ((2 * (k : ℝ) + 1) * θ)| ≤ 1 / |Real.sin θ| := by
  rw [sum_sin_odd hθ, abs_div]
  have habs : (0 : ℝ) < |Real.sin θ| := abs_pos.mpr hθ
  have hnum : |Real.sin ((N : ℝ) * θ) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.abs_sin_le_one ((N : ℝ) * θ), abs_nonneg (Real.sin ((N : ℝ) * θ)),
      sq_abs (Real.sin ((N : ℝ) * θ))]
  gcongr

/-! ## Convergence of the odd harmonic sine series -/

theorem antitone_oddReciprocal : Antitone (fun k : ℕ => 1 / (2 * (k : ℝ) + 1)) := by
  intro a b hab
  have hab' : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.mpr hab
  have ha : (0 : ℝ) < 2 * (a : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le ha (by linarith)

theorem tendsto_oddReciprocal : Filter.Tendsto (fun k : ℕ => 1 / (2 * (k : ℝ) + 1))
    Filter.atTop (nhds 0) := by
  have hnat : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlin : Filter.Tendsto (fun k : ℕ => 2 * (k : ℝ) + 1) Filter.atTop Filter.atTop := by
    have := (hnat.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) this
  simpa [one_div] using! hlin.inv_tendsto_atTop

/-- **Dirichlet test.**  The odd harmonic sine series has Cauchy partial sums off the zeros of the
sine.  It is only conditionally convergent, so this is a statement about partial sums, not a
`Summable` claim. -/
theorem cauchySeq_sum_oddHarmonicSine {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    CauchySeq fun N => ∑ k ∈ range N,
      (1 / (2 * (k : ℝ) + 1)) • Real.sin ((2 * (k : ℝ) + 1) * θ) := by
  refine antitone_oddReciprocal.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    tendsto_oddReciprocal (b := 1 / |Real.sin θ|) fun n => ?_
  simpa [Real.norm_eq_abs] using abs_sum_sin_odd_le hθ n

/-- The odd harmonic sine series converges off the zeros of the sine. -/
theorem exists_tendsto_sum_oddHarmonicSine {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N => ∑ k ∈ range N, Real.sin ((2 * (k : ℝ) + 1) * θ) / (2 * (k : ℝ) + 1))
      Filter.atTop (nhds L) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_sum_oddHarmonicSine hθ)
  refine ⟨L, hL.congr fun N => ?_⟩
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul]
  ring

end GaloisForLFunctions.HTGeometry
