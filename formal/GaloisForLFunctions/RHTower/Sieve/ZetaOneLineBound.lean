import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# A quantitative lower bound for zeta on the one-line

Mathlib proves that `ζ` does not vanish on the closed half-plane `re s ≥ 1`
(`riemannZeta_ne_zero_of_one_le_re`).  Away from the pole at `s = 1` the function is continuous, so
on a compact range of frequencies bounded away from zero the modulus attains a positive minimum:

`∃ c > 0, ∀ t ∈ [ε, T], c ≤ ‖ζ(1 + it)‖`.

This is the form the Halász argument needs — the pointwise Euler-product estimate at frequency `t`
decays only when `∑_p cos(t log p)/p` is bounded below, and that sum is `log‖ζ(1+it)‖` up to a
bounded error.
-/

namespace RHTower.Sieve

open Complex

/-- On a compact frequency range away from the pole, `1 + it` is never `1`. -/
theorem one_add_mul_I_ne_one {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    (1 : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
  intro hcon
  have him : ((1 : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hcon] at him
  simp at him
  linarith [him, ht, hε]

/-- The one-line shift has real part one. -/
theorem one_le_re_one_add_mul_I (t : ℝ) : (1 : ℝ) ≤ ((1 : ℂ) + (t : ℂ) * Complex.I).re := by
  simp

/-- **Quantitative nonvanishing of zeta on a compact one-line range.** -/
theorem exists_pos_lower_bound_zeta_one_line {ε T : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) :
    ∃ c > 0, ∀ t ∈ Set.Icc ε T, c ≤ ‖riemannZeta (1 + (t : ℂ) * Complex.I)‖ := by
  have hcont : ContinuousOn (fun t : ℝ => ‖riemannZeta (1 + (t : ℂ) * Complex.I)‖)
      (Set.Icc ε T) := by
    intro t ht
    have hne : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 1 := one_add_mul_I_ne_one hε ht.1
    have hdiff : DifferentiableAt ℂ riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I) :=
      differentiableAt_riemannZeta hne
    have hmap : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) t := by
      fun_prop
    have hcomp : ContinuousAt (fun t : ℝ => riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)) t :=
      ContinuousAt.comp (g := riemannZeta)
        (f := fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) hdiff.continuousAt hmap
    exact (hcomp.norm).continuousWithinAt
  have hne : (Set.Icc ε T).Nonempty := Set.nonempty_Icc.2 hεT
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨‖riemannZeta (1 + (t₀ : ℂ) * Complex.I)‖, ?_, fun t ht => hmin ht⟩
  have hz : riemannZeta (1 + (t₀ : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (one_le_re_one_add_mul_I t₀)
  exact norm_pos_iff.2 hz

end RHTower.Sieve
