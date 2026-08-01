import GaloisForLFunctions.RHTower.TrigammaVertical

/-!
# The leading asymptotic of the trigamma function on a vertical line

The trigamma series `ψ′(s) = Σ (s+n)^{-2}` differs from the telescoping series
`Σ [(s+n)^{-1} − (s+n+1)^{-1}] = s^{-1}` term by term by `((s+n)^2 (s+n+1))^{-1}`.  On a vertical
line the modulus of `s+n` is bounded below both by the height and by the real part, so those terms
are dominated by a fixed summable sequence once multiplied by `s`, and each of them tends to zero.

Dominated convergence for series then gives the exact first-order law

`s · ψ′(s) → 1`,

the leading datum of the first digamma jet — the `O`-estimates in the corpus give only the order.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- The telescoping majorant on a shifted arithmetic progression. -/
theorem hasSum_one_div_shift_mul_succ {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun n : ℕ => 1 / ((σ + n) * (σ + n + 1))) (1 / σ) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  have hterm : ∀ n : ℕ, 1 / ((σ + n) * (σ + n + 1)) = 1 / (σ + n) - 1 / (σ + (n + 1 : ℕ)) := by
    intro n
    have h1 : (0 : ℝ) < σ + n := hpos n
    have h2 : (0 : ℝ) < σ + (n + 1 : ℕ) := by
      push_cast
      linarith
    push_cast
    field_simp
    ring
  have hpartial : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / ((σ + i) * (σ + i + 1))
      = 1 / σ - 1 / (σ + N) := by
    intro N
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / (σ + (i : ℝ))) N
    rw [Finset.sum_congr rfl (fun i _ => hterm i), this]
    push_cast
    simp
  have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((σ + n) * (σ + n + 1)) := by
    intro n
    have h1 : (0 : ℝ) < σ + n := hpos n
    positivity
  have hsummable : Summable (fun n : ℕ => 1 / ((σ + n) * (σ + n + 1))) := by
    refine summable_of_sum_range_le hnonneg (c := 1 / σ) (fun N => ?_)
    rw [hpartial N]
    have : (0 : ℝ) ≤ 1 / (σ + N) := by
      have := hpos N
      positivity
    linarith
  rw [hsummable.hasSum_iff_tendsto_nat]
  have hlim : Tendsto (fun N : ℕ => 1 / (σ + (N : ℝ))) atTop (nhds 0) := by
    have hdiv : Tendsto (fun N : ℕ => σ + (N : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
    exact Tendsto.congr (fun N => by simp [Pi.inv_apply, one_div]) hdiv.inv_tendsto_atTop
  have := (tendsto_const_nhds (x := 1 / σ) (f := atTop (α := ℕ))).sub hlim
  rw [sub_zero] at this
  exact this.congr (fun N => (hpartial N).symm)

variable {σ : ℝ}

/-- The real part bounds the modulus on a vertical line. -/
theorem norm_vertical_add_nat_ge_re (t : ℝ) (n : ℕ) :
    σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
  calc σ + (n : ℝ) = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := hre.symm
    _ ≤ |((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re| := le_abs_self _
    _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := Complex.abs_re_le_norm _

/-- The height bounds the modulus on a vertical line. -/
theorem norm_vertical_add_nat_ge_im (t : ℝ) (n : ℕ) :
    t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im = t := by simp
  calc t = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im := him.symm
    _ ≤ |((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im| := le_abs_self _
    _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := Complex.abs_im_le_norm _

end GaloisForLFunctions
