import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget

/-!
# Moment cameras for arbitrary coefficients

The windows depend only on the carrier geometry. The same pair reads every
complex weighting whose absolute Lorentzian mass is summable. Local Taylor
error is proportional to absolute cluster mass; the far tail uses the full
absolute mass. No positive lower bound on nonzero coefficients is required.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- The camera image with arbitrary complex coefficients. -/
def weightedImage (weights : ℂ → ℂ) (f g : ℝ → ℂ) : ℂ :=
  ∑' z, weights z * pointImage f g z

/-- One pair of carrier-dependent windows reads every absolutely tempered choice of
coefficients on that carrier, with local error measured by absolute weighted mass. -/
theorem weighted_discMoment_readout_slow {a D C₀ η ε r : ℝ} {J : ℕ} (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hk : 1 ≤ k) (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m)
    {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z : ZeroConfig}
    {z₀ : ℂ}
    (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hrD : r ≤ min (2 * D⁻¹ / 8) (1 / 2))
    (hrΛ : r * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 ≤ 1 / 2)
    (hiso : ∀ z, z ∈ Z.carrier → |z.im - z₀.im| ≤ R → ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀)
    {s : Finset ℂ} (hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r)
    (hds : ∀ z, z ∈ Z.carrier → ‖z - z₀‖ ≤ r → z ∈ s) :
    ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow a F₁ ∧ ApertureWindow a G₁ ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≤
        ‖pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀‖ ∧
      ∀ weights : ℂ → ℂ, (∀ z, weights z ≠ 0 → z ∈ Z.carrier) →
      (Summable fun z => ‖weights z‖ / (1 + Complex.normSq (gammaOf z))) →
      ∀ j : ℕ, j ≤ J →
        ApertureWindow a (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
        ‖weightedImage weights (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁))
            (localWindow z₀.im G₁) -
          (-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ *
            ∑ z ∈ s, weights z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
          (∑ z ∈ s, ‖weights z‖) * r ^ (j + 1) *
              (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) *
              ‖pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀‖ +
            (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 * Real.exp a *
              (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
                ∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z)) := by
  classical
  have hmem (z : ℂ) : multDiff Z emptyZeroConfig z ≠ 0 ↔ z ∈ Z.carrier := by
    rw [multDiff_emptyZeroConfig]
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz]
      exact ⟨fun _ => hz,
        fun _ => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Z.one_le_mult z hz))⟩
    · rw [Set.indicator_of_notMem hz]
      exact ⟨fun h => False.elim (h rfl), fun h => False.elim (hz h)⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M,
      M = windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 := ⟨_, rfl⟩
  rw [← hcdef, ← hMdef, ← hΛ]
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
  obtain ⟨F₁, G₁, hF₁s, hG₁s, hF₁, hG₁, hblindRaw, hF₁0, hG₁0, hF₁d, hG₁d, hF₁sl, hG₁sl⟩ :=
    exists_local_slow_pair (k := k + J) hD hη hε hεa hb hbs hb1 hm hCm hC0 Z emptyZeroConfig hz₀
      (fun z => ‖z - z₀‖ ≤ r)
      (fun z hcz hzR hnot => (hiso z ((hmem z).mp hcz) hzR).resolve_left hnot)
      (fun s x y hxy hs => hcount s x y hxy fun z hz =>
        ⟨(hmem z).mp (hs z hz).1, (hs z hz).2⟩)
  have hblind : ∀ z ∈ Z.carrier, |z.im - z₀.im| ≤ R → ¬ ‖z - z₀‖ ≤ r →
      paperFT F₁ (gammaOf z - z₀.im) = 0 ∨
        paperFT G₁ (conj (gammaOf z) - z₀.im) = 0 :=
    fun z hz => hblindRaw z ((hmem z).mpr hz)
  rw [← hcdef] at hF₁0 hG₁0
  rw [← hMdef] at hF₁d hG₁d
  rw [← hΛ] at hF₁sl hG₁sl
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount hblind hF₁0 hG₁0 hF₁sl hG₁sl ⊢
  -- the target
  obtain ⟨ω, hω⟩ : ∃ ω, ω = gammaOf z₀ - X := ⟨_, rfl⟩
  have hωre : ω.re = 0 := by
    rw [hω, Complex.sub_re, Complex.ofReal_re, gammaOf_re, hX, sub_self]
  have hωim' : ω.im = -(z₀.re - 1 / 2) := by
    rw [hω, Complex.sub_im, Complex.ofReal_im, sub_zero, gammaOf_im]
  have hωim : |ω.im| ≤ 1 / 2 := by rw [hωim', abs_neg]; exact hz₀
  have hconjω : conj ω = conj (gammaOf z₀) - X := by rw [hω, map_sub, Complex.conj_ofReal]
  rw [← hω] at hF₁sl hF₁0 ⊢
  rw [← hconjω] at hG₁sl hG₁0
  have hPI0 : pointImage (localWindow X F₁) (localWindow X G₁) z₀ =
      paperFT F₁ ω * conj (paperFT G₁ (conj ω)) := by
    rw [pointImage, paperFT_localWindow, paperFT_localWindow, ← hω, hconjω]
  refine ⟨F₁, G₁, hF₁, hG₁, ?_, fun weights hweights hweightsSum j hj => ?_⟩
  · rw [hPI0, norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul hF₁0 hG₁0 hc0.le (hc0.le.trans hF₁0)
  -- the windows of order `j`, modulated to height `X`
  obtain ⟨hAs, hAt, hAft⟩ := annihilatePow_props (κ := ω) hF₁s hF₁.hasCompactSupport j
  have hF₁jw : ApertureWindow a (annihilatePow ω j F₁) :=
    ⟨hAs.of_le (by norm_cast), hAt.trans hF₁.2⟩
  set F := localWindow X (annihilatePow ω j F₁) with hF
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
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by linarith only [abs_nonneg (w.re - X)]
    have hj' : (1 + |w.re - X|) ^ j * (1 + |w.re - X|) ^ k ≤ (1 + |w.re - X|) ^ (k + J) := by
      rw [← pow_add]; exact pow_le_pow_right₀ h1 (by omega)
    calc ‖(-I * (w - X - ω)) ^ j * paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        = ‖w - X - ω‖ ^ j * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) := by
          rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul]; ring
      _ ≤ (1 + |w.re - X|) ^ j * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hv j) (by positivity)
      _ = ‖paperFT F₁ (w - X)‖ * ((1 + |w.re - X|) ^ j * (1 + |w.re - X|) ^ k) := by ring
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
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by linarith only [abs_nonneg (w.re - X)]
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
      (-I) ^ j * ((gammaOf z - gammaOf z₀) ^ j * Φ (gammaOf z - X)) := by
    intro z
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow, hAft, hconjX,
      show gammaOf z - (X : ℂ) - ω = gammaOf z - gammaOf z₀ by rw [hω]; ring, mul_pow]
    simp only [hΦ]
    ring
  have hzero_out : ∀ z, weights z ≠ 0 → |z.im - X| ≤ R → ¬ ‖z - z₀‖ ≤ r →
      Φ (gammaOf z - X) = 0 := by
    intro z hcz hzR hnot
    simp only [hΦ]
    rcases hblind z (hweights z hcz) hzR hnot with h0 | h0
    · rw [h0, zero_mul]
    · rw [← hconjX, h0, map_zero, mul_zero]
  have hsplit : ∀ z, weights z * pointImage F G z =
      (if z ∈ s then weights z * pointImage F G z else 0) +
        (if R < |z.im - X| then weights z * pointImage F G z else 0) := by
    intro z
    by_cases hzs : z ∈ s
    · have hle : |z.im - X| ≤ r := by
        have := hsd z hzs
        rw [hX, ← Complex.sub_im]
        exact (Complex.abs_im_le_norm _).trans this
      rw [if_pos hzs, if_neg (not_lt_of_ge (hle.trans hrR)), add_zero]
    · rw [if_neg hzs, zero_add]
      split_ifs with hfar
      · rfl
      · by_cases hcz : weights z = 0
        · rw [hcz, zero_mul]
        · have hnot : ¬ ‖z - z₀‖ ≤ r := fun h => hzs (hds z (hweights z hcz) h)
          rw [hPI, hzero_out z hcz (not_lt.mp hfar) hnot, mul_zero, mul_zero, mul_zero]
  obtain ⟨hfs, hfle⟩ := tsum_far_le
    (fun z hz => Z.strip z (hweights z hz)) hweightsSum hk ha hFdec hGdec hR
  have hfnorm : ∀ z, ‖(if R < |z.im - X| then weights z * pointImage F G z else 0)‖ =
      farTerm weights F G X R z := fun z => by
    unfold farTerm
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]
  have hfarS : Summable fun z =>
      if R < |z.im - X| then weights z * pointImage F G z else 0 :=
    Summable.of_norm (hfs.congr fun z => (hfnorm z).symm)
  have hdiscS : Summable fun z => if z ∈ s then weights z * pointImage F G z else 0 :=
    summable_of_ne_finset_zero (s := s) fun z hz => if_neg hz
  have hdisc_eq : ∑' z, (if z ∈ s then weights z * pointImage F G z else 0) =
      ∑ z ∈ s, weights z * pointImage F G z := by
    rw [tsum_eq_sum (s := s) fun z hz => if_neg hz]
    exact Finset.sum_congr rfl fun z hz => if_pos hz
  refine ⟨hFw, ?_⟩
  have hWdiff : weightedImage weights F G =
      (∑ z ∈ s, weights z * pointImage F G z) +
        ∑' z, (if R < |z.im - X| then weights z * pointImage F G z else 0) := by
    unfold weightedImage
    rw [tsum_congr hsplit, hdiscS.tsum_add hfarS, hdisc_eq]
  -- the far tail
  obtain ⟨Tl, hTl⟩ : ∃ Tl, Tl = M * M * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 /
      (1 + R) ^ (2 * k - 2)) * ∑' z, ‖weights z‖ / (1 + Complex.normSq (gammaOf z)) :=
    ⟨_, rfl⟩
  have hfarle : ‖∑' z, (if R < |z.im - X| then weights z * pointImage F G z else 0)‖ ≤
      Tl := hTl ▸
    (norm_tsum_le_tsum_norm (hfs.congr fun z => (hfnorm z).symm)).trans
      ((tsum_congr hfnorm).le.trans hfle)
  -- the moment and the relative error
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ z ∈ s, weights z * (gammaOf z - gammaOf z₀) ^ j :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ z ∈ s, weights z * (gammaOf z - gammaOf z₀) ^ j *
      (Φ (gammaOf z - X) - Φ ω) := ⟨_, rfl⟩
  have hsum_eq : ∑ z ∈ s, weights z * pointImage F G z = (-I) ^ j * (Φ ω * μ + E) := by
    rw [hμ, hE, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [hPI]; ring
  have hnormI : ‖(-I : ℂ) ^ j‖ = 1 := by rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hΦω : ‖Φ ω‖ = ‖paperFT F₁ ω‖ * ‖paperFT G₁ (conj ω)‖ := by
    simp only [hΦ]; rw [norm_mul, Complex.norm_conj]
  have hslowΦ : ∀ z ∈ s, ‖Φ (gammaOf z - X) - Φ ω‖ ≤ 6 * (r * Λ) * ‖Φ ω‖ := by
    intro z hz
    have hdz : ‖(gammaOf z - X) - ω‖ ≤ r := by
      rw [show (gammaOf z - X) - ω = gammaOf z - gammaOf z₀ by rw [hω]; ring, norm_gammaOf_sub]
      exact hsd z hz
    rw [hΦω]
    exact norm_pairImage_sub_le_slow (u := paperFT F₁) (v := paperFT G₁) hΛ0 hr hrΛ hrD hF₁sl
      hG₁sl hdz
  have hLip : ‖E‖ ≤ (∑ z ∈ s, ‖weights z‖) * r ^ (j + 1) * (6 * Λ) * ‖Φ ω‖ := by
    rw [hE]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => ?_
    have hdz : ‖gammaOf z - gammaOf z₀‖ ≤ r := by rw [norm_gammaOf_sub]; exact hsd z hz
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖weights z‖ * ‖gammaOf z - gammaOf z₀‖ ^ j * ‖Φ (gammaOf z - X) - Φ ω‖
        ≤ ‖weights z‖ * r ^ j * (6 * (r * Λ) * ‖Φ ω‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdz j)
            (norm_nonneg _)) (hslowΦ z hz) (norm_nonneg _) (by positivity)
      _ = ‖weights z‖ * r ^ (j + 1) * (6 * Λ) * ‖Φ ω‖ := by ring
  have hPI0' : pointImage (localWindow X F₁) G z₀ = Φ ω := by rw [hG, hPI0]
  rw [hWdiff, hsum_eq, hPI0', ← hμ]
  have e : (-I) ^ j * (Φ ω * μ + E) +
      ∑' z, (if R < |z.im - X| then weights z * pointImage F G z else 0) -
        (-I) ^ j * Φ ω * μ = (-I) ^ j * E +
      ∑' z, (if R < |z.im - X| then weights z * pointImage F G z else 0) := by ring
  rw [e]
  calc _ ≤ ‖(-I) ^ j * E‖ +
        ‖∑' z, (if R < |z.im - X| then weights z * pointImage F G z else 0)‖ :=
        norm_add_le _ _
    _ ≤ (∑ z ∈ s, ‖weights z‖) * r ^ (j + 1) * (6 * Λ) * ‖Φ ω‖ + Tl := by
        rw [norm_mul, hnormI, one_mul]; exact add_le_add hLip hfarle
    _ = _ := by rw [hTl]; ring

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weighted_discMoment_readout_slow
