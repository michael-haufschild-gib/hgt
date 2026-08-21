import Mathlib

/-!
# Connes' Appendix II Lemma 3: the principal value under a change of basic character

Formalization of Lemma 3 of Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Theorem V.3 attaches to each basic character `α` of a local field `K` a canonical principal value
`∫'`.  Comparing it with Weil's `Pfw` requires knowing how `∫'` moves when `α` is replaced by
`α(x) = α₀(λ x)`: Connes' Lemma 3 states

  `∫'_K f(u) |1-u|^{-1} d^*u = log|λ| f(1) + Pfw ∫ f(u) |1-u|^{-1} d^*u`,

and its proof (55)-(57) is the following displacement law for the tempered distribution
`φ(u) = -log|u|`: the selfdual measure rescales by `|λ|^{1/2}`, the Fourier transform becomes
`f̂(x) = |λ|^{1/2} f̂⁰(λx)`, and therefore

  `⟨φ̂, f⟩_α = ⟨φ̂, f⟩_{α₀} + log|λ| f(0)`.

That displacement law is proved here at the real place, unconditionally, as an exact identity of
integrals; combined with Appendix II (54) — the equality `∫' = Pfw` for the *normalized* character,
which is `connes_nonArch_A_add_B_eq_zero` at a non-archimedean place and
`connes_integral_neg_log_abs_mul_gaussian` at the real place — it gives Lemma 3, and summing over
places with `log|d| = ∑_v log|d_v|` gives Theorem 6.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory

/-- **Appendix II (55)-(57), real place.**  Replacing the basic character `α₀` by
`α(x) = α₀(λ x)` displaces the logarithmic distribution by `log|λ|` times the mass. -/
theorem connes_logDistribution_character_rescale {lam : ℝ} (hlam : lam ≠ 0) (F : ℝ → ℂ)
    (hF : Integrable F)
    (hlogF : Integrable (fun v : ℝ => ((Real.log |v| : ℝ) : ℂ) * F v)) :
    (∫ u : ℝ, ((-(Real.log |u|) : ℝ) : ℂ) * (F (lam * u) * ((|lam| : ℝ) : ℂ)))
      = (∫ v : ℝ, ((-(Real.log |v|) : ℝ) : ℂ) * F v)
        + ((Real.log |lam| : ℝ) : ℂ) * ∫ v : ℝ, F v := by
  have hlampos : (0:ℝ) < |lam| := abs_pos.mpr hlam
  set H : ℝ → ℂ := fun v => ((-(Real.log |v|) : ℝ) : ℂ) * F v
      + ((Real.log |lam| : ℝ) : ℂ) * F v with hH
  have hHint : Integrable H := by
    refine Integrable.add ?_ (hF.const_mul _)
    have : Integrable (fun v : ℝ => -(((Real.log |v| : ℝ) : ℂ) * F v)) := hlogF.neg
    refine this.congr ?_
    filter_upwards with v
    push_cast
    ring
  have hpt : ∀ u : ℝ, u ≠ 0 → H (lam * u) = ((-(Real.log |u|) : ℝ) : ℂ) * F (lam * u) := by
    intro u hu
    have habs : |lam * u| = |lam| * |u| := abs_mul lam u
    have hlog : Real.log |lam * u| = Real.log |lam| + Real.log |u| := by
      rw [habs, Real.log_mul (ne_of_gt hlampos) (abs_ne_zero.mpr hu)]
    simp only [hH, hlog]
    push_cast
    ring
  have hae0 : ∀ᵐ u : ℝ, u ≠ 0 := by
    have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
    have := compl_mem_ae_iff.2 h0
    filter_upwards [this] with u hu
    simpa using hu
  have hshift : (∫ u : ℝ, H (lam * u)) = |lam|⁻¹ • ∫ v : ℝ, H v := by
    have h := Measure.integral_comp_mul_left H lam
    rwa [abs_inv] at h
  have hleft : (∫ u : ℝ, ((-(Real.log |u|) : ℝ) : ℂ) * (F (lam * u) * ((|lam| : ℝ) : ℂ)))
      = ((|lam| : ℝ) : ℂ) * ∫ u : ℝ, H (lam * u) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae0] with u hu
    rw [hpt u hu]
    ring
  rw [hleft, hshift, Complex.real_smul]
  have hHsplit : (∫ v : ℝ, H v)
      = (∫ v : ℝ, ((-(Real.log |v|) : ℝ) : ℂ) * F v)
        + ((Real.log |lam| : ℝ) : ℂ) * ∫ v : ℝ, F v := by
    have h1 : Integrable (fun v : ℝ => ((-(Real.log |v|) : ℝ) : ℂ) * F v) := by
      have : Integrable (fun v : ℝ => -(((Real.log |v| : ℝ) : ℂ) * F v)) := hlogF.neg
      refine this.congr ?_
      filter_upwards with v
      push_cast
      ring
    rw [hH, MeasureTheory.integral_add h1 (hF.const_mul _), integral_const_mul]
  rw [hHsplit]
  have hne : ((|lam| : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hlampos
  rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end

end GaloisForLFunctions.RHTower
