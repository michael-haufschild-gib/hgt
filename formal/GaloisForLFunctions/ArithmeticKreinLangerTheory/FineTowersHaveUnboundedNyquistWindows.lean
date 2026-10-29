import GaloisForLFunctions.HeckeKreinToeplitz.LogarithmicCharactersAndTheArithmeticIndexFormula

/-!
# Fine towers have unbounded Nyquist windows

The tower of `p` samples ordinates at the Nyquist spacing `2π/log p` (HKT `TheNyquistLawOfAPrimeTower`).
In the archimedean completion the same law holds at every scale, and the window grows as the scale
shrinks: this is how the completion carries the index of every finite family.

**Nyquist at scale `t`** (`injective_logChar_of_scale_mul_lt`). On an element `u` of scale `t > 0`,
the characters `u ↦ e^{s_j log u}` of distinct exponents are distinct whenever every difference
satisfies `t |s_j − s_k| < 2π`: aliasing needs `t (s_j − s_k) ∈ 2πiℤ`.

**Every window is resolved** (`exists_scale_injective_logChar`). For a finite family of distinct
exponents there is `δ > 0` such that every element of scale in `(0, δ)` separates all of them. On a
group with arbitrarily small scales (`ℚ_{>0}`, any two-prime lattice) the fine towers therefore see
every finite family, whatever its ordinates.
-/

open Complex Finset
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G] (ℓ : G →* Multiplicative ℝ)

/-- **Nyquist at scale `t`.** Distinct exponents whose differences satisfy `t |s_j − s_k| < 2π`
give distinct characters at any `u` of scale `t > 0`. -/
theorem injective_logChar_of_scale_mul_lt {ι : Type*} {s : ι → ℂ} (hs : Function.Injective s)
    {u : G} (hu : 0 < scale ℓ u) (hwin : ∀ j k, scale ℓ u * ‖s j - s k‖ < 2 * π) :
    Function.Injective fun j => logChar ℓ (s j) u := by
  intro j k hjk
  simp only [logChar_apply, Complex.exp_eq_exp_iff_exists_int] at hjk
  obtain ⟨n, hn⟩ := hjk
  by_contra hne
  have hsne : s j - s k ≠ 0 := sub_ne_zero.mpr fun h => hne (hs h)
  -- `t (s_j − s_k) = 2πi n` with `n ≠ 0` forces `t |s_j − s_k| ≥ 2π`
  have hdiff : (s j - s k) * (scale ℓ u : ℂ) = n * (2 * π * I) := by linear_combination hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, mul_eq_zero, ofReal_eq_zero] at hdiff
    exact hdiff.elim hsne hu.ne'
  have hnorm := congrArg norm hdiff
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le, norm_mul, norm_mul,
    Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I,
    mul_one, Complex.norm_intCast] at hnorm
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  have := hwin j k
  nlinarith [Real.pi_pos]

/-- **Fine towers resolve every finite family.** For finitely many distinct exponents there is
`δ > 0` such that every element of scale in `(0, δ)` separates them. -/
theorem exists_scale_injective_logChar {ι : Type*} [Fintype ι] {s : ι → ℂ}
    (hs : Function.Injective s) :
    ∃ δ > 0, ∀ u : G, 0 < scale ℓ u → scale ℓ u < δ →
      Function.Injective fun j => logChar ℓ (s j) u := by
  set M : ℝ := ∑ j, ∑ k, ‖s j - s k‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  have hle : ∀ j k, ‖s j - s k‖ < M := fun j k => by
    have h1 := single_le_sum (f := fun k => ‖s j - s k‖) (fun _ _ => norm_nonneg _) (mem_univ k)
    have h2 := single_le_sum (f := fun j => ∑ k, ‖s j - s k‖)
      (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  refine ⟨2 * π / M, by positivity, fun u hu hδ => ?_⟩
  refine injective_logChar_of_scale_mul_lt ℓ hs hu fun j k => ?_
  calc scale ℓ u * ‖s j - s k‖ ≤ scale ℓ u * M := mul_le_mul_of_nonneg_left (hle j k).le hu.le
    _ < 2 * π / M * M := mul_lt_mul_of_pos_right hδ hM0
    _ = 2 * π := div_mul_cancel₀ _ hM0.ne'

end GaloisForLFunctions.ArithmeticKreinLangerTheory
