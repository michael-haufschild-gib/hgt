import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem

/-!
# Horizontal contour transport across finitely many poles

The arbitrary-order rectangle residue theorem is passed to infinite horizontal lines along any
escaping sequence on which both vertical sides vanish.  Integrability of the two horizontal lines
handles their symmetric truncations.  The resulting inverse-Fourier normalization contributes
exactly `I` times the finite sum of order-one Laurent coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped BigOperators Interval

noncomputable section

theorem horizontalIntegral_sub_eq_sum_laurentCoeff_of_vertical_tendsto_seq
    {f : ℂ → ℂ} {c d : ℝ} (hcd : c < d) {P : Finset ℂ}
    (hPim : ∀ p ∈ P, c < p.im ∧ p.im < d)
    (hmero : ∀ p ∈ P, MeromorphicAt f p)
    (hoff : ∀ s : ℂ, c ≤ s.im → s.im ≤ d → s ∉ P → AnalyticAt ℂ f s)
    (hc : Integrable fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I))
    (hd : Integrable fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hright : Tendsto (fun n => VIntegral f (T n) c d) atTop (𝓝 0))
    (hleft : Tendsto (fun n => VIntegral f (-(T n)) c d) atTop (𝓝 0)) :
    (∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
        (∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P, laurentCoeff f p (-1) := by
  let B : ℝ := (∑ p ∈ P, |p.re|) + 1
  have hBpos : 0 < B := by
    dsimp only [B]
    have hsum : 0 ≤ ∑ p ∈ P, |p.re| := Finset.sum_nonneg fun p _ => abs_nonneg p.re
    linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, B ≤ T n := (tendsto_atTop.1 hT) B
  have hres : ∀ᶠ n : ℕ in atTop,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (HIntegral f (-(T n)) (T n) c - HIntegral f (-(T n)) (T n) d +
          VIntegral f (T n) c d - VIntegral f (-(T n)) c d) =
        ∑ p ∈ P, laurentCoeff f p (-1) := by
    filter_upwards [hlarge] with n hn
    have hTpos : 0 < T n := lt_of_lt_of_le hBpos hn
    have hpRe : ∀ p ∈ P, -(T n) < p.re ∧ p.re < T n := by
      intro p hp
      have hpabs : |p.re| ≤ ∑ q ∈ P, |q.re| :=
        Finset.single_le_sum (fun q _ => abs_nonneg q.re) hp
      have habsT : |p.re| < T n := by
        dsimp only [B] at hn
        linarith
      exact ⟨by linarith [neg_abs_le p.re], by linarith [le_abs_self p.re]⟩
    let z : ℂ := (-(T n) : ℂ) + (c : ℂ) * Complex.I
    let w : ℂ := (T n : ℂ) + (d : ℂ) * Complex.I
    have hzre : z.re ≤ w.re := by dsimp [z, w]; simp; linarith
    have hzim : z.im ≤ w.im := by dsimp [z, w]; simp; exact hcd.le
    have hpNhd : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p := by
      intro p hp
      rw [rectangle_mem_nhds_iff]
      have hre := hpRe p hp
      have him := hPim p hp
      constructor
      · simpa [z, w, Set.uIoo_of_le (by linarith : -(T n) ≤ T n)] using hre
      · simpa [z, w, Set.uIoo_of_le hcd.le] using him
    have hoffRect : ∀ s ∈ Rectangle z w, s ∉ P → AnalyticAt ℂ f s := by
      intro s hs hsP
      have hsim : s.im ∈ Set.Icc c d := by
        have := hs.2
        simpa [z, w, Set.uIcc_of_le hcd.le] using this
      exact hoff s hsim.1 hsim.2 hsP
    have hr := rectangleIntegral'_eq_sum_laurentCoeff hzre hzim hpNhd hmero hoffRect
    simpa [z, w, RectangleIntegral, HIntegral, VIntegral] using hr
  have hbot : Tendsto (fun n => HIntegral f (-(T n)) (T n) c) atTop
      (𝓝 (∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I))) := by
    simpa [HIntegral] using intervalIntegral_tendsto_integral hc
      (tendsto_neg_atTop_atBot.comp hT) hT
  have htop : Tendsto (fun n => HIntegral f (-(T n)) (T n) d) atTop
      (𝓝 (∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I))) := by
    simpa [HIntegral] using intervalIntegral_tendsto_integral hd
      (tendsto_neg_atTop_atBot.comp hT) hT
  have hlim := (((hbot.sub htop).add hright).sub hleft).const_smul
    (1 / (2 * (Real.pi : ℂ) * Complex.I))
  have hlim' : Tendsto (fun n =>
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        (HIntegral f (-(T n)) (T n) c - HIntegral f (-(T n)) (T n) d +
          VIntegral f (T n) c d - VIntegral f (-(T n)) c d)) atTop
      (𝓝 ((1 / (2 * (Real.pi : ℂ) * Complex.I)) •
        ((∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
          ∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I)))) := by
    simpa using hlim
  have heq := tendsto_nhds_unique (hlim'.congr' hres) tendsto_const_nhds
  have hden : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hscale : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      ((∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
        ∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∑ p ∈ P, laurentCoeff f p (-1) := by
    simpa [smul_eq_mul] using heq
  calc
    (∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
          ∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
            ((∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
              ∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I))) := by field_simp
    _ = 2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ P, laurentCoeff f p (-1) := by
      rw [hscale]

/-- In inverse-Fourier normalization, a horizontal contour shift contributes `I` times the sum of
the crossed residues. -/
theorem horizontalIntegral_normalized_sub_eq_I_mul_sum_laurentCoeff_of_vertical_tendsto_seq
    {f : ℂ → ℂ} {c d : ℝ} (hcd : c < d) {P : Finset ℂ}
    (hPim : ∀ p ∈ P, c < p.im ∧ p.im < d)
    (hmero : ∀ p ∈ P, MeromorphicAt f p)
    (hoff : ∀ s : ℂ, c ≤ s.im → s.im ≤ d → s ∉ P → AnalyticAt ℂ f s)
    (hc : Integrable fun x : ℝ => f ((x : ℂ) + (c : ℂ) * Complex.I))
    (hd : Integrable fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hright : Tendsto (fun n => VIntegral f (T n) c d) atTop (𝓝 0))
    (hleft : Tendsto (fun n => VIntegral f (-(T n)) c d) atTop (𝓝 0)) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ x : ℝ, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ x : ℝ, f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      Complex.I * ∑ p ∈ P, laurentCoeff f p (-1) := by
  rw [← mul_sub,
    horizontalIntegral_sub_eq_sum_laurentCoeff_of_vertical_tendsto_seq
      hcd hPim hmero hoff hc hd hT hright hleft]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end

end GaloisForLFunctions.HTGeometry
