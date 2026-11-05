import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.FourierTail

/-!
# Convolution cameras with absolute Fourier tails

Convolution turns a normalized local camera image into one Fourier transform.
Aperture doubles; the isolating pair supplies local Taylor control and blindness,
while its decay bound gives an absolute weighted Fourier tail.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- A normalized camera convolution has twice the aperture, controlled local
Taylor data, exact local blindness, and an absolute Fourier tail. -/
theorem fourier_window_of_slow_pair {a D C₀ η ε r : ℝ} (J : ℕ)
    (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖)
    {k m : ℕ} (hk : 1 ≤ k)
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m)
    {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {z₀ : ℂ} (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hrD : r ≤ min (2 * D⁻¹ / 8) (1 / 2))
    (hrΛ : r * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 ≤ 1 / 2)
    (hiso : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀) :
    ∃ f : ℝ → ℂ, ApertureWindow (2 * a) f ∧
      (∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ ‖z - z₀‖ ≤ r →
        paperFT f (gammaOf z) = 0) ∧
      (∀ z : ℂ, ‖z - z₀‖ ≤ r →
        ‖paperFT f (gammaOf z) - (-I) ^ J * (gammaOf z - gammaOf z₀) ^ J‖ ≤
          r ^ (J + 1) * (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0)) ∧
      Summable (fourierFarTerm (multDiff Z Z') f z₀.im R) ∧
      (∑' z, fourierFarTerm (multDiff Z Z') f z₀.im R z) ≤
        (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 * Real.exp a *
          (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
          (∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z))) /
            windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c, c = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M,
      M = windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 := ⟨_, rfl⟩
  rw [← hΛ] at hrΛ
  have hh : (0 : ℝ) < 2 * D⁻¹ := by positivity
  have hL0 : 0 ≤ localSlack D C₀ := by unfold localSlack; positivity
  have hc0 : 0 < c := by rw [hcdef]; exact windowFloor_pos hh hL0 hη
  have ha : 0 ≤ a := by
    have hp : 0 < π * D / 2 := by positivity
    linarith only [hp, hε, hεa]
  have hCm0 : 0 ≤ Cm := by
    have h1 := hCm 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (by positivity) h1
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (windowGrowth_nonneg hh hL0) hCm0)
      hC00) (Real.exp_pos _).le
  have hΛ0 : 0 ≤ Λ := hΛ ▸ slowRate_nonneg hh hL0 hη hC00
  -- the slowly varying isolating pair, blind outside the disc
  obtain ⟨F₁, G₁, hF₁s, hG₁s, hF₁, hG₁, hblind, hF₁0, hG₁0, hF₁d, hG₁d, hF₁sl, hG₁sl⟩ :=
    exists_local_slow_pair (k := k + J) hD hη hε hεa hb hbs hb1 hm hCm hC0 Z Z' hz₀
      (fun z => ‖z - z₀‖ ≤ r) (fun z hcz hzR hnot => (hiso z hcz hzR).resolve_left hnot) hcount
  rw [← hcdef] at hF₁0 hG₁0
  rw [← hMdef] at hF₁d hG₁d
  rw [← hΛ] at hF₁sl hG₁sl
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount hblind hF₁0 hG₁0 hF₁sl hG₁sl
  -- the target
  obtain ⟨ω, hω⟩ : ∃ ω, ω = gammaOf z₀ - X := ⟨_, rfl⟩
  have hωre : ω.re = 0 := by
    rw [hω, Complex.sub_re, Complex.ofReal_re, gammaOf_re, hX, sub_self]
  have hωim' : ω.im = -(z₀.re - 1 / 2) := by
    rw [hω, Complex.sub_im, Complex.ofReal_im, sub_zero, gammaOf_im]
  have hωim : |ω.im| ≤ 1 / 2 := by rw [hωim', abs_neg]; exact hz₀
  have hconjω : conj ω = conj (gammaOf z₀) - X := by rw [hω, map_sub, Complex.conj_ofReal]
  rw [← hω] at hF₁sl hF₁0
  rw [← hconjω] at hG₁sl hG₁0
  obtain ⟨hAs, hAt, hAft⟩ := annihilatePow_props (κ := ω) hF₁s hF₁.hasCompactSupport J
  have hF₁jw : ApertureWindow a (annihilatePow ω J F₁) :=
    ⟨hAs.of_le (by norm_cast), hAt.trans hF₁.2⟩
  set F := localWindow X (annihilatePow ω J F₁) with hF
  set G := localWindow X G₁ with hG
  have hFw : ApertureWindow a F := apertureWindow_localWindow hF₁jw X
  have hGw : ApertureWindow a G := apertureWindow_localWindow hG₁ X
  have hFdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT F w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := by
    intro w hw
    rw [hF, paperFT_localWindow, hAft]
    have hv : ‖w - X - ω‖ ≤ 1 + |w.re - X| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, hωre, sub_zero, Complex.sub_im,
        Complex.sub_im, Complex.ofReal_im, sub_zero]
      have hdiff : |w.im - ω.im| ≤ 1 :=
        (abs_sub _ _).trans (by linarith only [hw, hωim])
      linarith only [hdiff]
    have hd := hF₁d (w - X) (by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hw)
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by
      linarith only [abs_nonneg (w.re - X)]
    have hj' : (1 + |w.re - X|) ^ J * (1 + |w.re - X|) ^ k ≤ (1 + |w.re - X|) ^ (k + J) := by
      rw [← pow_add]; exact pow_le_pow_right₀ h1 (by omega)
    calc ‖(-I * (w - X - ω)) ^ J * paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        = ‖w - X - ω‖ ^ J * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) := by
          rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul]; ring
      _ ≤ (1 + |w.re - X|) ^ J * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hv J) (by positivity)
      _ = ‖paperFT F₁ (w - X)‖ * ((1 + |w.re - X|) ^ J * (1 + |w.re - X|) ^ k) := by ring
      _ ≤ ‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ (k + J) :=
          mul_le_mul_of_nonneg_left hj' (norm_nonneg _)
      _ ≤ M := hd
      _ ≤ M * Real.exp (a * |w.im|) := le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity))
  have hGdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT G w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := by
    intro w hw
    rw [hG, paperFT_localWindow]
    have hd := hG₁d (w - X) (by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hw)
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by
      linarith only [abs_nonneg (w.re - X)]
    calc ‖paperFT G₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        ≤ ‖paperFT G₁ (w - X)‖ * (1 + |w.re - X|) ^ (k + J) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (norm_nonneg _)
      _ ≤ M := hd
      _ ≤ M * Real.exp (a * |w.im|) := le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity))
  -- the image of a point
  set Φ : ℂ → ℂ := fun w => paperFT F₁ w * conj (paperFT G₁ (conj w)) with hΦ
  have hconjX : ∀ z : ℂ, conj (gammaOf z) - (X : ℂ) = conj (gammaOf z - X) := fun z => by
    rw [map_sub, Complex.conj_ofReal]
  have hPI : ∀ z, pointImage F G z =
      (-I) ^ J * ((gammaOf z - gammaOf z₀) ^ J * Φ (gammaOf z - X)) := by
    intro z
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow, hAft, hconjX,
      show gammaOf z - (X : ℂ) - ω = gammaOf z - gammaOf z₀ by rw [hω]; ring, mul_pow]
    simp only [hΦ]
    ring
  have hzero_out : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - X| ≤ R → ¬ ‖z - z₀‖ ≤ r →
      Φ (gammaOf z - X) = 0 := by
    intro z hcz hzR hnot
    simp only [hΦ]
    rcases hblind z hcz hzR hnot with h0 | h0
    · rw [h0, zero_mul]
    · rw [← hconjX, h0, map_zero, mul_zero]
  have hΦnorm : ‖Φ ω‖ = ‖paperFT F₁ ω‖ * ‖paperFT G₁ (conj ω)‖ := by
    simp only [hΦ, norm_mul, Complex.norm_conj]
  have hfloor : c ^ 2 ≤ ‖Φ ω‖ := by
    rw [hΦnorm, sq]
    exact mul_le_mul hF₁0 hG₁0 hc0.le (hc0.le.trans hF₁0)
  have hΦpos : 0 < ‖Φ ω‖ := (pow_pos hc0 2).trans_le hfloor
  have hΦne : Φ ω ≠ 0 := norm_pos_iff.mp hΦpos
  have hconv : ApertureWindow (2 * a) (EF.weilTest F G) := by
    refine ⟨EF.weilTest_contDiff hFw.1 hGw.1.continuous hFw.hasCompactSupport, ?_⟩
    have hFa : tsupport F ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
      simpa only [show 2 * a / 2 = a by ring] using hFw.2
    have hGa : tsupport G ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
      simpa only [show 2 * a / 2 = a by ring] using hGw.2
    exact EF.tsupport_weilTest_subset hFa hGa
  set f : ℝ → ℂ := fun t => (Φ ω)⁻¹ * EF.weilTest F G t with hf
  have hfw : ApertureWindow (2 * a) f :=
    ⟨contDiff_const.mul hconv.1,
      (tsupport_mul_subset_right (f := fun _ => (Φ ω)⁻¹)).trans hconv.2⟩
  have hft (z : ℂ) : paperFT f (gammaOf z) = (Φ ω)⁻¹ * pointImage F G z := by
    rw [hf, paperFT_const_mul', EF.paperFT_weilTest hFw.1.continuous hGw.1.continuous
      hFw.hasCompactSupport hGw.hasCompactSupport]
    rfl
  have hslowΦ (z : ℂ) (hz : ‖z - z₀‖ ≤ r) :
      ‖Φ (gammaOf z - X) - Φ ω‖ ≤ 6 * (r * Λ) * ‖Φ ω‖ := by
    have hdz : ‖(gammaOf z - X) - ω‖ ≤ r := by
      rw [show (gammaOf z - X) - ω = gammaOf z - gammaOf z₀ by rw [hω]; ring,
        norm_gammaOf_sub]
      exact hz
    rw [hΦnorm]
    exact norm_pairImage_sub_le_slow (u := paperFT F₁) (v := paperFT G₁) hΛ0 hr hrΛ hrD
      hF₁sl hG₁sl hdz
  have hnorm (z : ℂ) : ‖paperFT f (gammaOf z)‖ = ‖pointImage F G z‖ / ‖Φ ω‖ := by
    rw [hft, norm_mul, norm_inv, div_eq_mul_inv, mul_comm]
  have hfar (z : ℂ) : fourierFarTerm (multDiff Z Z') f z₀.im R z =
      farTerm (multDiff Z Z') F G X R z / ‖Φ ω‖ := by
    unfold fourierFarTerm farTerm
    rw [← hX]
    split_ifs
    · rw [hnorm]; ring
    · rw [zero_div]
  obtain ⟨hfs, hfle⟩ := tsum_far_multDiff_le hZ hZ' hk ha hFdec hGdec hR
  refine ⟨f, hfw, ?_, ?_, ?_, ?_⟩
  · intro z hcz hzR hz
    rw [hft, hPI, hzero_out z hcz (by simpa only [hX] using hzR) hz, mul_zero, mul_zero, mul_zero]
  · intro z hz
    have he : paperFT f (gammaOf z) - (-I) ^ J * (gammaOf z - gammaOf z₀) ^ J =
        ((-I) ^ J * (gammaOf z - gammaOf z₀) ^ J) *
          ((Φ (gammaOf z - X) - Φ ω) / Φ ω) := by
      rw [hft, hPI]
      field_simp [hΦne]
    have hquot : ‖Φ (gammaOf z - X) - Φ ω‖ / ‖Φ ω‖ ≤ 6 * (r * Λ) :=
      (div_le_iff₀ hΦpos).mpr (hslowΦ z hz)
    have hdz : ‖gammaOf z - gammaOf z₀‖ ≤ r := by rw [norm_gammaOf_sub]; exact hz
    rw [he]
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul, norm_div]
    calc ‖gammaOf z - gammaOf z₀‖ ^ J * (‖Φ (gammaOf z - X) - Φ ω‖ / ‖Φ ω‖)
        ≤ r ^ J * (6 * (r * Λ)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hdz J) hquot
            (div_nonneg (norm_nonneg _) hΦpos.le) (pow_nonneg hr _)
      _ = r ^ (J + 1) * (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) := by
        rw [← hΛ]
        ring
  · exact (hfs.div_const ‖Φ ω‖).congr fun z => (hfar z).symm
  · have hbound0 : 0 ≤ M * M * Real.exp a *
        (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
          ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
      (tsum_nonneg fun z => show 0 ≤ farTerm (multDiff Z Z') F G X R z from by
        unfold farTerm; split_ifs <;> positivity).trans hfle
    rw [tsum_congr hfar, tsum_div_const]
    refine (div_le_div_of_nonneg_right hfle hΦpos.le).trans ?_
    rw [← hcdef, ← hMdef, ← hX, sq M]
    exact div_le_div_of_nonneg_left hbound0 (pow_pos hc0 2) hfloor

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.fourier_window_of_slow_pair
