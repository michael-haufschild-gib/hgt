import GaloisForLFunctions.RHTower.ZetaPoissonJensenInequality

/-!
# A quantised gap for the Poisson–Jensen defect of `ζ`

For `s₀` with `Re s₀ > ½`, write
`E(s₀) = ∫ log |ζ(½ + iτ)| P_{s₀}(τ) dτ - log |ζ(s₀)| + log (|s₀|/|s₀ - 1|)`.
By the Poisson–Jensen inequality `E(s₀)` dominates `Σ log (|ρ + s̄₀ - 1|/|ρ - s₀|)` over zeros right
of the critical line.  If `ρ = β + iγ` is such a zero and `s₀ = 2β - ½ + iγ`, the Blaschke ratio is
exactly `3`: `ρ + s̄₀ - 1 = 3(β - ½)` and `ρ - s₀ = -(β - ½)`.  Following the doubling chain
`β_k = ½ + 2^k (β - ½)` at fixed ordinate to its last zero guarantees `ζ(s₀) ≠ 0`.  Hence:

* if the Riemann hypothesis fails, `E(s₀) ≥ log 3` at some admissible centre;
* if `E(s₀) < log 3` at every admissible centre, the Riemann hypothesis holds.
-/

open Complex Real MeasureTheory

namespace RHTower

noncomputable section

/-- The Poisson–Jensen defect `E(s₀)`. -/
def poissonJensenDefect (s0 : ℂ) : ℝ :=
  (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel s0 τ)
    - Real.log ‖riemannZeta s0‖ + Real.log (‖s0‖ / ‖s0 - 1‖)

/-- **The Blaschke ratio three.**  For a zero `β + iγ` with `β > ½` and `ζ(2β - ½ + iγ) ≠ 0`,
`E(2β - ½ + iγ) ≥ log 3`. -/
theorem log_three_le_poissonJensenDefect {β γ : ℝ} (hβ : 1 / 2 < β)
    (hz : riemannZeta ((β : ℂ) + (γ : ℂ) * I) = 0)
    (hz0 : riemannZeta (((2 * β - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) ≠ 0) :
    Real.log 3 ≤ poissonJensenDefect (((2 * β - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) := by
  set s0 : ℂ := ((2 * β - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I with hs0
  set ρ : ℂ := (β : ℂ) + (γ : ℂ) * I with hρ
  have hs0re : s0.re = 2 * β - 1 / 2 := by simp [hs0]
  have hρre : ρ.re = β := by simp [hρ]
  have hs0half : 1 / 2 < s0.re := by rw [hs0re]; linarith
  have hs01 : s0 ≠ 1 := by
    intro h
    have him : γ = 0 := by have := congrArg Complex.im h; simpa [hs0] using this
    have hre : 2 * β - 1 / 2 = 1 := by have := congrArg Complex.re h; simpa [hs0] using this
    have hβ' : β = 3 / 4 := by linarith
    apply riemannZeta_ne_zero_of_ofReal_mem_Ioo (σ := β) (by linarith) (by linarith)
    rw [← hz, hρ, him]
    simp
  have hle := (integrable_and_sum_log_blaschke_le hs0half hs01 hz0 (Z := {ρ})
    (fun x hx => by
      rw [Finset.mem_singleton] at hx; subst hx; exact ⟨hz, by rw [hρre]; exact hβ⟩)).2
  rw [Finset.sum_singleton] at hle
  have hnum : ρ + (starRingEnd ℂ) s0 - 1 = ((3 * (β - 1 / 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hρ, hs0]; ring
    · simp [hρ, hs0]
  have hden : ρ - s0 = ((-(β - 1 / 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hρ, hs0]; ring
    · simp [hρ, hs0]
  have hpos : 0 < β - 1 / 2 := by linarith
  rw [hnum, hden, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 3 * (β - 1 / 2)), abs_neg, abs_of_pos hpos,
    mul_div_assoc, div_self hpos.ne', mul_one] at hle
  exact hle

/-- **The quantised gap.**  If the Riemann hypothesis fails, some admissible centre has
Poisson–Jensen defect at least `log 3`. -/
theorem exists_log_three_le_poissonJensenDefect_of_not_riemannHypothesis
    (h : ¬ RiemannHypothesis) :
    ∃ s0 : ℂ, 1 / 2 < s0.re ∧ s0 ≠ 1 ∧ riemannZeta s0 ≠ 0 ∧
      Real.log 3 ≤ poissonJensenDefect s0 := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re] at h
  push Not at h
  obtain ⟨ρ, hρre, hρz⟩ := h
  set β : ℝ := ρ.re with hβ
  set γ : ℝ := ρ.im with hγ
  have hρeq : ρ = (β : ℂ) + (γ : ℂ) * I := (Complex.re_add_im ρ).symm
  set b : ℕ → ℝ := fun k => 1 / 2 + 2 ^ k * (β - 1 / 2) with hb
  have hb0 : b 0 = β := by simp [hb]
  have hbsucc : ∀ k, b (k + 1) = 2 * b k - 1 / 2 := by
    intro k; simp only [hb, pow_succ]; ring
  have hpos : 0 < β - 1 / 2 := by linarith
  have hexists : ∃ k, riemannZeta ((b k : ℂ) + (γ : ℂ) * I) ≠ 0 := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (β - 1 / 2)) (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, riemannZeta_ne_zero_of_one_le_re ?_⟩
    have : (1 / 2 : ℝ) ≤ 2 ^ k * (β - 1 / 2) := by
      rw [div_lt_iff₀ hpos] at hk
      linarith
    simp only [hb, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    linarith
  set m := Nat.find hexists with hm
  have hm_spec : riemannZeta ((b m : ℂ) + (γ : ℂ) * I) ≠ 0 := Nat.find_spec hexists
  have hm0 : m ≠ 0 := by
    intro h0
    apply hm_spec
    rw [h0, hb0, ← hρeq]
    exact hρz
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  rw [hk] at hm_spec
  have hk_zero : riemannZeta ((b k : ℂ) + (γ : ℂ) * I) = 0 := by
    by_contra hne
    exact Nat.find_min hexists (by omega : k < m) hne
  have hbk : 1 / 2 < b k := by
    simp only [hb]
    have : 0 < (2 : ℝ) ^ k * (β - 1 / 2) := by positivity
    linarith
  have hs0 : (((2 * b k - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) = (b (k + 1) : ℂ) + (γ : ℂ) * I := by
    rw [hbsucc]
  refine ⟨((2 * b k - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I, ?_, ?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    linarith
  · intro h1
    have him : γ = 0 := by have := congrArg Complex.im h1; simpa using this
    have hre : 2 * b k - 1 / 2 = 1 := by have := congrArg Complex.re h1; simpa using this
    apply riemannZeta_ne_zero_of_ofReal_mem_Ioo (σ := b k) (by linarith) (by linarith)
    rw [← hk_zero, him]
    simp
  · rw [hs0]; exact hm_spec
  · exact log_three_le_poissonJensenDefect hbk hk_zero (by rw [hs0]; exact hm_spec)

/-- **The gap criterion.**  If `E(s₀) < log 3` at every centre with `Re s₀ > ½`, `s₀ ≠ 1`,
`ζ(s₀) ≠ 0`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_forall_poissonJensenDefect_lt_log_three
    (h : ∀ s0 : ℂ, 1 / 2 < s0.re → s0 ≠ 1 → riemannZeta s0 ≠ 0 →
      poissonJensenDefect s0 < Real.log 3) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨s0, h1, h2, h3, h4⟩ :=
    exists_log_three_le_poissonJensenDefect_of_not_riemannHypothesis hRH
  exact absurd (h s0 h1 h2 h3) (not_lt.mpr h4)

end

end RHTower
