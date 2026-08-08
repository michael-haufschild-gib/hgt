import GaloisForLFunctions.RHTower.Sieve.ChebyshevPNT
import GaloisForLFunctions.RHTower.ChebyshevStieltjesMeasure

/-!
# Scaling form of the prime number theorem

The corpus proves `ψ(x)/x → 1` for the sharp Chebyshev sum.  Recorded here in the step-function
form `chebyshevPsiReal` used by the Chebyshev–Stieltjes measure, together with the two consequences
every dilation limit needs:

* `tendsto_chebyshevPsiReal_scaled` — `ψ(cT)/T → c` for each fixed `c > 0`, the value carried by a
  single block of a dilated step weight;
* `exists_chebyshevPsiReal_le_linear` — the global Chebyshev bound `ψ(x) ≤ C x`, which controls the
  tail of a dilated sum uniformly in the dilation parameter.
-/

open Filter ArithmeticFunction
open scoped Topology BigOperators

namespace RHTower

theorem sum_range_succ_vonMangoldt_eq_sum_Icc (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1), (vonMangoldt n : ℝ)
      = ∑ n ∈ Finset.Icc 1 k, (vonMangoldt n : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem chebyshevPsiReal_eq_sum_range (x : ℝ) :
    chebyshevPsiReal x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (vonMangoldt n : ℝ) := by
  rw [chebyshevPsiReal, chebyshevPsi, sum_range_succ_vonMangoldt_eq_sum_Icc]

/-- **The prime number theorem in step-function form.** -/
theorem tendsto_chebyshevPsiReal_div :
    Tendsto (fun x : ℝ => chebyshevPsiReal x / x) atTop (𝓝 1) := by
  refine Sieve.tendsto_sum_vonMangoldt_div.congr fun x => ?_
  rw [chebyshevPsiReal_eq_sum_range]

/-- **The dilated prime number theorem.**  For a fixed positive ratio, `ψ(cT)/T → c`. -/
theorem tendsto_chebyshevPsiReal_scaled {c : ℝ} (hc : 0 < c) :
    Tendsto (fun T : ℝ => chebyshevPsiReal (c * T) / T) atTop (𝓝 c) := by
  have hdil : Tendsto (fun T : ℝ => c * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  have h := tendsto_chebyshevPsiReal_div.comp hdil
  have hmul := h.const_mul c
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_apply]
  field_simp

theorem chebyshevPsiReal_nonneg (x : ℝ) : 0 ≤ chebyshevPsiReal x := by
  rw [chebyshevPsiReal_eq_sum_range]
  exact Finset.sum_nonneg fun n _ => vonMangoldt_nonneg

/-- **The Chebyshev linear bound.**  `ψ(x) ≤ C x` for all `x ≥ 1`, with an absolute constant. -/
theorem exists_chebyshevPsiReal_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → chebyshevPsiReal x ≤ C * x := by
  have hev : ∀ᶠ x : ℝ in atTop, chebyshevPsiReal x / x < 2 := by
    have := tendsto_chebyshevPsiReal_div.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
    exact this
  obtain ⟨x₀, hx₀⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists_forall_of_atTop
  set B : ℝ := chebyshevPsiReal x₀ + 2 with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    linarith [chebyshevPsiReal_nonneg x₀]
  refine ⟨B + 2, by linarith, fun x hx => ?_⟩
  rcases le_or_gt x x₀ with hle | hgt
  · have hmono : chebyshevPsiReal x ≤ chebyshevPsiReal x₀ := chebyshevPsiReal_mono hle
    have hxB : chebyshevPsiReal x₀ ≤ B := by rw [hBdef]; linarith
    nlinarith [hmono, hxB, hx]
  · have hx0pos : (0 : ℝ) < x := by linarith
    have hlt := (hx₀ x hgt.le).1
    rw [div_lt_iff₀ hx0pos] at hlt
    nlinarith [hlt, hB0, hx0pos]

end RHTower
