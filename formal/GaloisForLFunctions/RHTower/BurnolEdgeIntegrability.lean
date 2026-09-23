import GaloisForLFunctions.RHTower.MellinReflectionEquation
import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.SoninMixedPhysicalBlockNonvanishing
import GaloisForLFunctions.RHTower.SoninBandLimitedShellVanishing

/-!
# Integrability of Burnol's edge integrand on a vertical line

The vertical edges of Burnol's rectangle converge to integrals over full vertical lines.  This
module supplies the missing analytic fact: on a line `Re s = σ ≥ 2` (and, by the reflection, on
`Re s = 1 − σ`) the edge integrand

`M(f)(s)·ζ(s)⁻¹·(Z − s)⁻¹`

is Lebesgue integrable, being a product of two square-integrable factors — the `L²` datum of the
Hardy tail and the Cauchy kernel.

## Main results

* `riemannZeta_ne_zero_line_of_nonpos` — no zero of `ζ` on a non-integral vertical line left of `0`.
* `integrable_burnolEdgeIntegrand_right` — integrability on `Re s = σ ≥ 2`.
* `burnolEdgeIntegrand_reflect_line`, `integrable_burnolEdgeIntegrand_left`,
  `integral_burnolEdgeIntegrand_left` — the left line, through the functional equation.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Nonvanishing of `ζ` on a vertical line -/

theorem riemannZeta_ne_zero_line_of_nonpos {σ : ℝ} (hσ : σ ≤ 0) (hint : ∀ m : ℤ, (m : ℝ) ≠ σ)
    (t : ℝ) : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro hzero
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  rcases riemannZeta_zero_trivial_or_mem_strip hzero with ⟨n, hn⟩ | ⟨hpos, _⟩
  · refine hint (-(2 * ((n : ℤ) + 1))) ?_
    have hcast := congrArg Complex.re hn
    rw [hre] at hcast
    rw [hcast]
    simp
  · rw [hre] at hpos
    linarith

/-! ## Continuity on a vertical line -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

theorem continuous_extendedMellinContinuation_line (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ ≠ 1) :
    Continuous fun t : ℝ => extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I) := by
  have hpath : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by fun_prop
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hsre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have hs0 : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h; rw [h] at hsre; simp at hsre; exact hσ0 hsre.symm
  have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro h; rw [h] at hsre; simp at hsre; exact hσ1 hsre.symm
  have hg := (differentiableAt_extendedMellinContinuation ha hev hc hd hs0 hs1).continuousAt
  exact ContinuousAt.comp (g := extendedMellinContinuation a c d f)
    (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (x := t) hg hpath.continuousAt

theorem continuous_riemannZeta_inv_line {σ : ℝ} (hσ1 : σ ≠ 1)
    (hne : ∀ t : ℝ, riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0) :
    Continuous fun t : ℝ => (riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹ := by
  have hpath : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by fun_prop
  have hz : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h; rw [h] at hre; simp at hre; exact hσ1 hre.symm
    exact ContinuousAt.comp (g := riemannZeta)
      (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (x := t)
      (differentiableAt_riemannZeta hs1).continuousAt hpath.continuousAt
  exact hz.inv₀ hne

theorem continuous_cauchyKernel_line {Z : ℂ} {σ : ℝ} (hZ : Z.re < σ) :
    Continuous fun t : ℝ => (Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹ := by
  have hne : ∀ t : ℝ, Z - ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  exact Continuous.inv₀ (by fun_prop) hne

/-! ## Integrability on the right line -/

/-- The pointwise Cauchy--Schwarz bound behind the integrability of the edge integrand. -/
theorem norm_mul_mul_le_two_mul_sq_add_sq {A B C : ℂ} (hB : ‖B‖ ≤ 4) :
    ‖A * B * C‖ ≤ 2 * (‖A‖ ^ (2 : ℕ) + ‖C‖ ^ (2 : ℕ)) := by
  rw [norm_mul, norm_mul]
  nlinarith [norm_nonneg A, norm_nonneg B, norm_nonneg C, sq_nonneg (‖A‖ - ‖C‖),
    mul_nonneg (norm_nonneg A) (norm_nonneg C)]

theorem integrable_burnolEdgeIntegrand_right (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {σ : ℝ} (hσ : 2 ≤ σ) {Z : ℂ} (hZ : Z.re < σ) :
    Integrable (fun t : ℝ =>
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z ((σ : ℂ) + (t : ℂ) * I))
      volume := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨M, _, hM⟩ := exists_integral_norm_sq_extendedMellin_line_le ha hev hc hd
  obtain ⟨hGint, _⟩ := hM σ hσ
  have hσ0 : σ ≠ 0 := by intro h; rw [h] at hσ; linarith
  have hσ1 : σ ≠ 1 := by intro h; rw [h] at hσ; linarith
  have hζne : ∀ t : ℝ, riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    have h := norm_riemannZeta_ge_of_two_le_re (s := (σ : ℂ) + (t : ℂ) * I) (by rw [hre]; linarith)
    intro hzero
    rw [hzero] at h
    simp at h
    linarith
  have hcont : Continuous fun t : ℝ =>
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z ((σ : ℂ) + (t : ℂ) * I) := by
    have h1 := continuous_extendedMellinContinuation_line ha0 hev hc hd hσ0 hσ1
    have h2 := continuous_riemannZeta_inv_line hσ1 hζne
    have h3 := continuous_cauchyKernel_line (Z := Z) hZ
    exact (h1.mul h2).mul h3
  have hKsq : Integrable (fun t : ℝ => ‖(Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ (2 : ℕ)) volume :=
    integrable_norm_sq_cauchyKernel_line hZ
  have hmaj : Integrable (fun t : ℝ => 2 * (‖extendedMellinContinuation a c d f
      ((σ : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) + ‖(Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ (2 : ℕ))) volume := by
    simpa using (hGint.add hKsq).const_mul 2
  refine Integrable.mono' hmaj hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hζ4 : ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 4 := by
    refine norm_zeta_inv_le_of_two_le_re ?_
    simpa using hσ
  exact norm_mul_mul_le_two_mul_sq_add_sq hζ4

/-! ## The left line, through the functional equation -/

theorem fourierUnitary_band_of_reflect {a : ℝ} {f : SoninL2} {d : ℂ} (hev : f ∈ evenSubspace)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
  rw [fourierUnitary_fourierUnitary_of_mem_evenSubspace hev]
  exact hd

/-- **Burnol's reflection on a vertical line.**  Off the real axis, the edge integrand of `(f, Z)`
at `σ + it` with `σ < 1/2` is minus that of the Fourier-transformed datum at `(1−σ) − it`. -/
theorem burnolEdgeIntegrand_reflect_line (a : ℝ) (c d : ℂ) (f : SoninL2) (Z : ℂ) {σ t : ℝ}
    (hσ : σ < 1 / 2) (ht : t ≠ 0) :
    burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z ((σ : ℂ) + (t : ℂ) * I)
      = -burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f)) (1 - Z)
          (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  have hint : ∀ m : ℤ, ((σ : ℂ) + (t : ℂ) * I) ≠ (m : ℂ) := by
    intro m hm
    have := congrArg Complex.im hm
    rw [him] at this
    simp at this
    exact ht this
  have hkey := burnolEdgeIntegrand_reflect a c d f Z (s := (σ : ℂ) + (t : ℂ) * I)
    (by rw [hre]; exact hσ) hint
  rw [hkey]
  congr 2
  push_cast
  ring

theorem burnolEdgeIntegrand_reflect_line' (a : ℝ) (c d : ℂ) (f : SoninL2) (Z : ℂ) {σ t : ℝ}
    (hσ : 2 ≤ σ) (ht : t ≠ 0) :
    burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I)
      = (-1 : ℂ) * burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f))
          (1 - Z) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  have hlt : (1 - σ : ℝ) < 1 / 2 := by linarith
  have hkey := burnolEdgeIntegrand_reflect_line a c d f Z (σ := (1 - σ : ℝ)) (t := t) hlt ht
  rw [hkey, show ((1 - (1 - σ) : ℝ) : ℂ) = (σ : ℂ) by push_cast; ring]
  ring

theorem integrable_burnolEdgeIntegrand_left (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {σ : ℝ} (hσ : 2 ≤ σ) {Z : ℂ} (hZ : (1 - Z).re < σ) :
    Integrable (fun t : ℝ =>
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I)) volume := by
  have hright := integrable_burnolEdgeIntegrand_right (a := a) (c := d) (d := c)
    (f := fourierUnitary f) ha (fourierUnitary_mem_evenSubspace hev)
    (fourierUnitary_band_of_reflect hev hd) hc hσ hZ
  have h1 : Integrable (fun t : ℝ =>
      burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f)) (1 - Z)
        ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)) volume := by
    have h := hright.comp_neg
    refine h.congr ?_
    filter_upwards with t
    norm_num
  refine (h1.const_mul (-1 : ℂ)).congr ?_
  have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hnull] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  exact (burnolEdgeIntegrand_reflect_line' a c d f Z hσ ht0).symm

theorem integral_burnolEdgeIntegrand_left (a : ℝ) (c d : ℂ) (f : SoninL2) {σ : ℝ} (hσ : 2 ≤ σ)
    (Z : ℂ) :
    (∫ t : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I))
      = -∫ t : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f))
          (1 - Z) ((σ : ℂ) + (t : ℂ) * I) := by
  have hae : (fun t : ℝ => burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
      (((1 - σ : ℝ) : ℂ) + (t : ℂ) * I))
      =ᵐ[volume] fun t : ℝ =>
        (-1 : ℂ) * burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f))
          (1 - Z) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hnull] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    exact burnolEdgeIntegrand_reflect_line' a c d f Z hσ ht0
  rw [integral_congr_ae hae, integral_const_mul]
  have hswap : (∫ t : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f))
      (1 - Z) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I))
      = ∫ t : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f))
          (1 - Z) ((σ : ℂ) + (t : ℂ) * I) := by
    have h := integral_neg_eq_self
      (fun t : ℝ => burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f))
        (1 - Z) ((σ : ℂ) + (t : ℂ) * I)) volume
    refine Eq.trans ?_ h
    refine integral_congr_ae ?_
    filter_upwards with t
    norm_num
  rw [hswap]
  ring

end

end RHTower
