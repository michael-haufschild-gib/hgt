import GaloisForLFunctions.ZeroConfigurationGeometry.TheLocalCameraFixesTheIsolatedZerosOfZeta

/-!
# Near-coincidences are read through their moments

The local camera (`one_add_pow_le_of_isolated_cancellation_of_bump`) sees an isolated point of a
cancelling cluster. A cluster of near-coincident points is not isolated, but the camera still reads
its first moments. Let `Z, Z'` be tempered mimics at aperture `a` and `z₀` a point at height `X`.
Suppose every cluster point with height in `[X − R, X + R]` lies in the disc `‖z − z₀‖ ≤ r` or at
distance `≥ η` from `z₀`. Write `c = m_Z − m_{Z'}`, `ω = γ_{z₀}`, and
`μ_j = Σ_{disc} c(z)(γ_z − ω)^j`.

**Theorem** (`norm_discMoment_le`). For `j ≤ 2`,
`c_η² ‖μ_j‖ ≤ N r^{j+1} · 4a²M² e^{a/2} + M² e^a (5/4)(1 + |X|)²/(1 + R)^{2k−2} · S`,
with `c_η = windowFloor`, `M` the strip decay of the isolating windows, `N = Σ_{disc} |c|` and
`S = Σ_z |c(z)|/(1 + |γ_z|²)`.

So the net multiplicity `μ₀` of the disc vanishes (`sum_multDiff_eq_zero_of_disc`). The first and second
moments vanish to orders `r²` and `r³`. For a pair `c ± w/2` of `Z` against `c' ± w'/2` of `Z'`
this fixes the centre to `O(r²)` and the squared gap `w²` to `O(r³)`, since
`w² − w'² = 2μ₂ − 2μ₁(p + p' − 2ω)` (`pair_moments`). The sign of `w²` (a real pair
for `w² > 0`, an FE pair of depth `δ` for `w² = −4δ²`) is therefore read from the image.

Proof. The windows of `exists_local_isolating_pair` are blind to the cluster outside the disc and
see `ω` with floor `c_η`. Multiplying the transform of `F` by `(−i(w − ω))^j` (`annihilatePow`) keeps
the aperture and costs `j` orders of decay. Mimicry gives `Σ_{disc} c(z)(−i(γ_z − ω))^j Φ(γ_z) = −tail`
for the pair image `Φ(w) = F̂(w) conj Ĝ(conj w)`. `Φ` is Lipschitz on the strip with constant
`4a²M² e^{a/2}` (`norm_pairImage_sub_le`): the window is bounded by `M/2` by Fourier inversion
(`norm_le_of_paperFT_decay`), and `|e^{iwu} − e^{iw'u}| ≤ 2|w − w'| |u| e^{a|Im w'|}`
(`norm_paperFT_sub_le_of_bounded`). Replacing `Φ(γ_z)` by `Φ(ω)` costs `r · Lip` per point.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### Annihilation to order `j` -/

/-- `j`-fold annihilation at `κ`: the transform is multiplied by `(−i(w − κ))^j`. -/
def annihilatePow (κ : ℂ) (j : ℕ) (g : ℝ → ℂ) : ℝ → ℂ := (annihilate κ)^[j] g

theorem annihilatePow_props {κ : ℂ} {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (annihilatePow κ j g) ∧ tsupport (annihilatePow κ j g) ⊆ tsupport g ∧
      ∀ w, paperFT (annihilatePow κ j g) w = (-I * (w - κ)) ^ j * paperFT g w := by
  induction j with
  | zero => exact ⟨hg, subset_rfl, fun w => by simp [annihilatePow]⟩
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hc : HasCompactSupport (annihilatePow κ j g) :=
      hgc.isCompact.of_isClosed_subset (isClosed_tsupport _) h2
    have e : annihilatePow κ (j + 1) g = annihilate κ (annihilatePow κ j g) := by
      simp only [annihilatePow]
      exact Function.iterate_succ_apply' _ _ _
    refine ⟨?_, ?_, fun w => ?_⟩
    · rw [e]; exact contDiff_annihilate h1
    · rw [e]; exact (tsupport_annihilate_subset κ _).trans h2
    · rw [e, paperFT_annihilate h1 hc, h3, pow_succ]
      ring

/-! ### Lipschitz control of the image -/

/-- **Lipschitz control of a transform.** For `F` bounded by `B` on `[−A, A]` and
`|w − w'| A ≤ 1`, `|F̂(w) − F̂(w')| ≤ |w − w'| · 4A²B e^{A|Im w'|}`. -/
theorem norm_paperFT_sub_le_of_bounded {F : ℝ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hFc : Continuous F)
    (hFs : tsupport F ⊆ Icc (-A) A) (hB : ∀ u, ‖F u‖ ≤ B) {w w' : ℂ} (hww : ‖w - w'‖ * A ≤ 1) :
    ‖paperFT F w - paperFT F w'‖ ≤ ‖w - w'‖ * (4 * A ^ 2 * B * Real.exp (A * |w'.im|)) := by
  have hFcs : HasCompactSupport F := isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hFs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hint : ∀ v : ℂ, Integrable fun u : ℝ => F u * cexp (I * v * u) := fun v =>
    (hFc.mul (by fun_prop)).integrable_of_hasCompactSupport hFcs.mul_right
  set G : ℝ → ℂ := fun u => F u * (cexp (I * (w - w') * u) - 1) with hG
  have hGs : tsupport G ⊆ Icc (-A) A := tsupport_mul_subset_left.trans hFs
  have hGB : ∀ u, ‖G u‖ ≤ B * (2 * (‖w - w'‖ * A)) := by
    intro u
    by_cases hu : F u = 0
    · rw [hG]; simp only [hu, zero_mul, norm_zero]; positivity
    · have hua : |u| ≤ A := abs_le.mpr (hFs (subset_tsupport _ hu))
      have hxe : ‖I * (w - w') * (u : ℂ)‖ ≤ ‖w - w'‖ * A := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hua (norm_nonneg _)
      have he := Complex.norm_exp_sub_one_le (hxe.trans hww)
      rw [hG]; simp only
      rw [norm_mul]
      calc ‖F u‖ * ‖cexp (I * (w - w') * u) - 1‖ ≤ B * (2 * ‖I * (w - w') * (u : ℂ)‖) :=
            mul_le_mul (hB u) he (norm_nonneg _) hB0
        _ ≤ B * (2 * (‖w - w'‖ * A)) := by gcongr
  have hdiff : paperFT F w - paperFT F w' = paperFT G w' := by
    rw [paperFT_def, paperFT_def, paperFT_def, ← integral_sub (hint w) (hint w')]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hG]
    have e : cexp (I * w * u) = cexp (I * (w - w') * u) * cexp (I * w' * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e]; ring
  rw [hdiff]
  calc ‖paperFT G w'‖ ≤ B * (2 * (‖w - w'‖ * A)) * Real.exp (A * |w'.im|) * (2 * A) :=
        norm_paperFT_le_of_tsupport hA hGs hGB w'
    _ = _ := by ring

/-- **The window is bounded by its transform.** A continuous compactly supported `F` with
`|F̂(x)|(1 + |x|)^k ≤ M` on the real line, `k ≥ 2`, has `|F| ≤ M/2`. -/
theorem norm_le_of_paperFT_decay {F : ℝ → ℂ} (hFc : Continuous F) (hFcs : HasCompactSupport F)
    {k : ℕ} (hk : 2 ≤ k) {M : ℝ} (hdec : ∀ x : ℝ, ‖paperFT F x‖ * (1 + |x|) ^ k ≤ M) (u : ℝ) :
    ‖F u‖ ≤ M / 2 := by
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport hFcs
  have hpt : ∀ x : ℝ, ‖paperFT F x‖ ≤ M * (1 + x ^ 2)⁻¹ := by
    intro x
    have h1 : 1 + x ^ 2 ≤ (1 + |x|) ^ k :=
      calc 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
        _ ≤ (1 + |x|) ^ k := pow_le_pow_right₀ (by linarith [abs_nonneg x]) hk
    have h2 : ‖paperFT F x‖ * (1 + x ^ 2) ≤ M :=
      (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (hdec x)
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h2
  have hcont : Continuous fun x : ℝ => paperFT F x :=
    ArithmeticCastelnuovoSeveri.continuous_paperFT_ofReal hFi
  have hint : Integrable fun x : ℝ => paperFT F x :=
    (integrable_inv_one_add_sq.const_mul M).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hpt)
  have hinv := ArithmeticCastelnuovoSeveri.eq_invFT_paperFT hFc hFi hint u
  have hb := ArithmeticCastelnuovoSeveri.norm_invFT_sub_le hint
    (integrable_zero ℝ ℂ volume) u
  have h0 : ArithmeticCastelnuovoSeveri.invFT (fun _ : ℝ => (0 : ℂ)) u = 0 := by
    simp [ArithmeticCastelnuovoSeveri.invFT]
  have hI : ∫ x : ℝ, ‖paperFT F x - 0‖ ≤ M * π := by
    rw [← integral_univ_inv_one_add_sq, ← integral_const_mul]
    refine integral_mono (hint.sub (integrable_zero ℝ ℂ volume)).norm
      (integrable_inv_one_add_sq.const_mul M) fun x => by
        show ‖paperFT F x - 0‖ ≤ M * (1 + x ^ 2)⁻¹
        rw [sub_zero]; exact hpt x
  rw [hinv]
  calc ‖ArithmeticCastelnuovoSeveri.invFT (fun x : ℝ => paperFT F x) u‖
      = ‖ArithmeticCastelnuovoSeveri.invFT (fun x : ℝ => paperFT F x) u -
          ArithmeticCastelnuovoSeveri.invFT (fun _ : ℝ => (0 : ℂ)) u‖ := by rw [h0, sub_zero]
    _ ≤ (2 * π)⁻¹ * ∫ x : ℝ, ‖paperFT F x - 0‖ := hb
    _ ≤ (2 * π)⁻¹ * (M * π) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M / 2 := by field_simp

/-- **The pair image is Lipschitz on the strip.** -/
theorem norm_pairImage_sub_le {F G : ℝ → ℂ} {A M : ℝ} (hA : 0 ≤ A) (hFc : Continuous F)
    (hGc : Continuous G) (hFs : tsupport F ⊆ Icc (-A) A) (hGs : tsupport G ⊆ Icc (-A) A)
    (hFB : ∀ u, ‖F u‖ ≤ M / 2) (hGB : ∀ u, ‖G u‖ ≤ M / 2)
    (hFw : ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT F w‖ ≤ M)
    (hGw : ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT G w‖ ≤ M) {w ω : ℂ} (hw : |w.im| ≤ 1 / 2)
    (hω : |ω.im| ≤ 1 / 2) (hwω : ‖w - ω‖ * A ≤ 1) :
    ‖paperFT F w * conj (paperFT G (conj w)) - paperFT F ω * conj (paperFT G (conj ω))‖ ≤
      ‖w - ω‖ * (4 * A ^ 2 * M ^ 2 * Real.exp (A / 2)) := by
  have hM0 : 0 ≤ M := by linarith [(norm_nonneg _).trans (hFB 0)]
  have hexp : Real.exp (A * |ω.im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp' : Real.exp (A * |(conj ω).im|) ≤ Real.exp (A / 2) := by
    rw [Complex.conj_im, abs_neg]; exact hexp
  have h1 := norm_paperFT_sub_le_of_bounded hA hFc hFs hFB hwω
  have hcc : ‖conj w - conj ω‖ = ‖w - ω‖ := by rw [← map_sub, Complex.norm_conj]
  have h2 := norm_paperFT_sub_le_of_bounded hA hGc hGs hGB (w := conj w) (w' := conj ω)
    (by rw [hcc]; exact hwω)
  rw [hcc] at h2
  have hG1 : ‖paperFT G (conj w)‖ ≤ M := hGw _ (by rw [Complex.conj_im, abs_neg]; exact hw)
  have hF1 : ‖paperFT F ω‖ ≤ M := hFw _ hω
  have e : paperFT F w * conj (paperFT G (conj w)) - paperFT F ω * conj (paperFT G (conj ω)) =
      (paperFT F w - paperFT F ω) * conj (paperFT G (conj w)) +
        paperFT F ω * conj (paperFT G (conj w) - paperFT G (conj ω)) := by
    rw [map_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hb1 : ‖paperFT F w - paperFT F ω‖ ≤ ‖w - ω‖ * (2 * A ^ 2 * M * Real.exp (A / 2)) := by
    refine h1.trans ?_
    have : 4 * A ^ 2 * (M / 2) * Real.exp (A * |ω.im|) ≤ 2 * A ^ 2 * M * Real.exp (A / 2) := by
      have := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2 * A ^ 2 * M)
      linarith
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have hb2 : ‖paperFT G (conj w) - paperFT G (conj ω)‖ ≤
      ‖w - ω‖ * (2 * A ^ 2 * M * Real.exp (A / 2)) := by
    refine h2.trans ?_
    have : 4 * A ^ 2 * (M / 2) * Real.exp (A * |(conj ω).im|) ≤
        2 * A ^ 2 * M * Real.exp (A / 2) := by
      have := mul_le_mul_of_nonneg_left hexp' (by positivity : (0 : ℝ) ≤ 2 * A ^ 2 * M)
      linarith
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  calc ‖paperFT F w - paperFT F ω‖ * ‖paperFT G (conj w)‖ +
        ‖paperFT F ω‖ * ‖paperFT G (conj w) - paperFT G (conj ω)‖
      ≤ ‖w - ω‖ * (2 * A ^ 2 * M * Real.exp (A / 2)) * M +
          M * (‖w - ω‖ * (2 * A ^ 2 * M * Real.exp (A / 2))) :=
        add_le_add (mul_le_mul hb1 hG1 (norm_nonneg _) (by positivity))
          (mul_le_mul hF1 hb2 (norm_nonneg _) hM0)
    _ = _ := by ring

/-! ### The moments of a near-coincident cluster -/

/-- **The camera reads the moments of a near-coincident cluster.** Let `Z, Z'` be tempered mimics at
aperture `a`. Suppose every cluster point with height within `R` of `X = Im z₀` lies in the disc
`‖z − z₀‖ ≤ r`, with `ra ≤ 1`, or at distance `≥ η` from `z₀`, with count bound `(D, C₀)` near `X`.
Then the moments `μ_j = Σ_{disc} c(z)(γ_z − γ_{z₀})^j`, `j ≤ 2`, satisfy
`c_η² ‖μ_j‖ ≤ N r^{j+1} · 4a²M² e^{a/2} + M² e^a (5/4)(1 + |X|)²/(1 + R)^{2k−2} · S`. -/
theorem norm_discMoment_le {a D C₀ η ε r : ℝ} (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hk : 1 ≤ k) (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + 2 : ℕ) : ℝ) ≤ m)
    {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {z₀ : ℂ}
    (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hra : r * a ≤ 1)
    (hiso : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀)
    {s : Finset ℂ} (hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r)
    (hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) {j : ℕ} (hj : j ≤ 2) :
    windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 *
        ‖∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
      (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) *
          (4 * a ^ 2 * (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 *
            Real.exp (a / 2)) +
        (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 * Real.exp a *
          (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
            ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c, c = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M,
      M = windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε := ⟨_, rfl⟩
  rw [← hcdef, ← hMdef]
  have hL0 : 0 ≤ localSlack D C₀ := by unfold localSlack; positivity
  have hc0 : 0 < c := by rw [hcdef]; exact windowFloor_pos (by positivity) hL0 hη
  have ha : 0 ≤ a := by nlinarith [Real.pi_pos]
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
    exact mul_nonneg (mul_nonneg (mul_nonneg (windowGrowth_nonneg (by positivity) hL0) hCm0)
      hC00) (Real.exp_pos _).le
  -- the isolating pair, blind outside the disc
  obtain ⟨F₁, G₁, hF₁s, hG₁s, hF₁, hG₁, hblind, hF₁0, hG₁0, hF₁d, hG₁d⟩ :=
    exists_local_isolating_pair (k := k + 2) hD hη hε hεa hb hbs hb1 hm hCm hC0 Z Z' hz₀
      (fun z => ‖z - z₀‖ ≤ r) (fun z hcz hzR hnot => (hiso z hcz hzR).resolve_left hnot) hcount
  rw [← hcdef] at hF₁0 hG₁0
  rw [← hMdef] at hF₁d hG₁d
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount hblind hF₁0 hG₁0 ⊢
  have hstrip : ∀ z, multDiff Z Z' z ≠ 0 → |z.re - 1 / 2| ≤ 1 / 2 := by
    intro z hz
    rcases mem_carrier_of_multDiff_ne_zero hz with h' | h'
    · obtain ⟨h1, h2⟩ := Z.strip _ h'
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h'
      rw [abs_le]; constructor <;> linarith
  -- the target and the strip bounds
  obtain ⟨ω, hω⟩ : ∃ ω, ω = gammaOf z₀ - X := ⟨_, rfl⟩
  have hωre : ω.re = 0 := by
    rw [hω, Complex.sub_re, Complex.ofReal_re, gammaOf_re, hX, sub_self]
  have hωim' : ω.im = -(z₀.re - 1 / 2) := by
    rw [hω, Complex.sub_im, Complex.ofReal_im, sub_zero, gammaOf_im]
  have hωim : |ω.im| ≤ 1 / 2 := by rw [hωim', abs_neg]; exact hz₀
  have hconjω : conj ω = conj (gammaOf z₀) - X := by rw [hω, map_sub, Complex.conj_ofReal]
  have hpow1 : ∀ w : ℂ, (1 : ℝ) ≤ (1 + |w.re|) ^ (k + 2) := fun w =>
    one_le_pow₀ (by linarith [abs_nonneg w.re])
  have hF₁w : ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT F₁ w‖ ≤ M := fun w hw =>
    (le_mul_of_one_le_right (norm_nonneg _) (hpow1 w)).trans (hF₁d w hw)
  have hG₁w : ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT G₁ w‖ ≤ M := fun w hw =>
    (le_mul_of_one_le_right (norm_nonneg _) (hpow1 w)).trans (hG₁d w hw)
  have hreal : ∀ {H : ℝ → ℂ}, (∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT H w‖ * (1 + |w.re|) ^ (k + 2) ≤ M) →
      ∀ x : ℝ, ‖paperFT H x‖ * (1 + |x|) ^ (k + 2) ≤ M := fun hH x => by
    have := hH (x : ℂ) (by rw [Complex.ofReal_im, abs_zero]; norm_num)
    rwa [Complex.ofReal_re] at this
  have hF₁B : ∀ u, ‖F₁ u‖ ≤ M / 2 :=
    norm_le_of_paperFT_decay hF₁.1.continuous hF₁.hasCompactSupport (by omega) (hreal hF₁d)
  have hG₁B : ∀ u, ‖G₁ u‖ ≤ M / 2 :=
    norm_le_of_paperFT_decay hG₁.1.continuous hG₁.hasCompactSupport (by omega) (hreal hG₁d)
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
      have : |w.im - ω.im| ≤ 1 := (abs_sub _ _).trans (by linarith)
      linarith
    have hd := hF₁d (w - X) (by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hw)
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by linarith [abs_nonneg (w.re - X)]
    have hj' : (1 + |w.re - X|) ^ j * (1 + |w.re - X|) ^ k ≤ (1 + |w.re - X|) ^ (k + 2) := by
      rw [← pow_add]; exact pow_le_pow_right₀ h1 (by omega)
    calc ‖(-I * (w - X - ω)) ^ j * paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        = ‖w - X - ω‖ ^ j * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) := by
          rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul]; ring
      _ ≤ (1 + |w.re - X|) ^ j * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hv j) (by positivity)
      _ = ‖paperFT F₁ (w - X)‖ * ((1 + |w.re - X|) ^ j * (1 + |w.re - X|) ^ k) := by ring
      _ ≤ ‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ (k + 2) :=
          mul_le_mul_of_nonneg_left hj' (norm_nonneg _)
      _ ≤ M := hd
      _ ≤ M * Real.exp (a * |w.im|) := le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity))
  have hGdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT G w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := by
    intro w hw
    rw [hG, paperFT_localWindow]
    have hd := hG₁d (w - X) (by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hw)
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by linarith [abs_nonneg (w.re - X)]
    calc ‖paperFT G₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        ≤ ‖paperFT G₁ (w - X)‖ * (1 + |w.re - X|) ^ (k + 2) :=
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
  -- blind outside the disc
  have hzero_out : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - X| ≤ R → ¬ ‖z - z₀‖ ≤ r →
      Φ (gammaOf z - X) = 0 := by
    intro z hcz hzR hnot
    simp only [hΦ]
    rcases hblind z hcz hzR hnot with h0 | h0
    · rw [h0, zero_mul]
    · rw [← hconjX, h0, map_zero, mul_zero]
  -- the split of the image
  have hsplit : ∀ z, multDiff Z Z' z * pointImage F G z =
      (if z ∈ s then multDiff Z Z' z * pointImage F G z else 0) +
        (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0) := by
    intro z
    by_cases hzs : z ∈ s
    · have hle : |z.im - X| ≤ r := by
        have := hsd z hzs
        rw [hX, ← Complex.sub_im]
        exact (Complex.abs_im_le_norm _).trans this
      rw [if_pos hzs, if_neg (by linarith), add_zero]
    · rw [if_neg hzs, zero_add]
      split_ifs with hfar
      · rfl
      · by_cases hcz : multDiff Z Z' z = 0
        · rw [hcz, zero_mul]
        · have hnot : ¬ ‖z - z₀‖ ≤ r := fun h => hzs (hds z hcz h)
          rw [hPI, hzero_out z hcz (not_lt.mp hfar) hnot, mul_zero, mul_zero, mul_zero]
  have htot := summable_multDiff_pointImage hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1
    hGw.hasCompactSupport
  have hzero : ∑' z, multDiff Z Z' z * pointImage F G z = 0 := by
    rw [← W_sub_W_eq_tsum hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1 hGw.hasCompactSupport,
      W_eq_of_mimic hZ hZ' hW hFw hGw, sub_self]
  have hdiscS : Summable fun z => if z ∈ s then multDiff Z Z' z * pointImage F G z else 0 :=
    summable_of_ne_finset_zero (s := s) fun z hz => if_neg hz
  have hfarS : Summable fun z => if R < |z.im - X| then multDiff Z Z' z * pointImage F G z
      else 0 :=
    (htot.sub hdiscS).congr fun z => sub_eq_of_eq_add' (hsplit z)
  have hdisc_eq : ∑' z, (if z ∈ s then multDiff Z Z' z * pointImage F G z else 0) =
      ∑ z ∈ s, multDiff Z Z' z * pointImage F G z := by
    rw [tsum_eq_sum (s := s) fun z hz => if_neg hz]
    exact Finset.sum_congr rfl fun z hz => if_pos hz
  rw [tsum_congr hsplit, hdiscS.tsum_add hfarS, hdisc_eq] at hzero
  -- the far tail
  obtain ⟨hfs, hfle⟩ := tsum_far_multDiff_le hZ hZ' hk ha hFdec hGdec hR
  have hfnorm : ∀ z, ‖(if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ =
      farTerm (multDiff Z Z') F G X R z := fun z => by
    unfold farTerm
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]
  have hfarle : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ ≤
      M * M * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    (norm_tsum_le_tsum_norm (hfs.congr fun z => (hfnorm z).symm)).trans
      ((tsum_congr hfnorm).le.trans hfle)
  have hDs : ‖∑ z ∈ s, multDiff Z Z' z * pointImage F G z‖ ≤
      M * M * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
    rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]; exact hfarle
  -- the moment and the Lipschitz error
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j *
      (Φ (gammaOf z - X) - Φ ω) := ⟨_, rfl⟩
  have hsum_eq : ∑ z ∈ s, multDiff Z Z' z * pointImage F G z = (-I) ^ j * (Φ ω * μ + E) := by
    rw [hμ, hE, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [hPI]; ring
  have hnormI : ‖(-I : ℂ) ^ j‖ = 1 := by rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hLip : ‖E‖ ≤ (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) *
      (4 * a ^ 2 * M ^ 2 * Real.exp (a / 2)) := by
    rw [hE]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => ?_
    by_cases hcz : multDiff Z Z' z = 0
    · rw [hcz]; simp
    · have hdz : ‖gammaOf z - gammaOf z₀‖ ≤ r := by rw [norm_gammaOf_sub]; exact hsd z hz
      have hwstrip : |(gammaOf z - X).im| ≤ 1 / 2 := by
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero, gammaOf_im, abs_neg]
        exact hstrip z hcz
      have hdiff : (gammaOf z - X) - ω = gammaOf z - gammaOf z₀ := by rw [hω]; ring
      have hwa : ‖(gammaOf z - X) - ω‖ * a ≤ 1 := by
        rw [hdiff]
        exact (mul_le_mul_of_nonneg_right hdz ha).trans hra
      have hL := norm_pairImage_sub_le ha hF₁.1.continuous hG₁.1.continuous hF₁.2 hG₁.2 hF₁B
        hG₁B hF₁w hG₁w hwstrip hωim hwa
      rw [hdiff] at hL
      rw [norm_mul, norm_mul, norm_pow]
      calc ‖multDiff Z Z' z‖ * ‖gammaOf z - gammaOf z₀‖ ^ j * ‖Φ (gammaOf z - X) - Φ ω‖
          ≤ ‖multDiff Z Z' z‖ * r ^ j * (r * (4 * a ^ 2 * M ^ 2 * Real.exp (a / 2))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdz j)
              (norm_nonneg _)) (hL.trans (mul_le_mul_of_nonneg_right hdz (by positivity)))
              (norm_nonneg _) (by positivity)
        _ = ‖multDiff Z Z' z‖ * r ^ (j + 1) * (4 * a ^ 2 * M ^ 2 * Real.exp (a / 2)) := by ring
  have hfloor : c * c ≤ ‖Φ ω‖ := by
    rw [← hω] at hF₁0
    simp only [hΦ]
    rw [norm_mul, Complex.norm_conj, hconjω]
    exact mul_le_mul hF₁0 hG₁0 hc0.le (hc0.le.trans hF₁0)
  have h1 : ‖Φ ω * μ‖ ≤ ‖Φ ω * μ + E‖ + ‖E‖ := by
    have := norm_sub_le (Φ ω * μ + E) E
    rwa [add_sub_cancel_right] at this
  have h2 : ‖Φ ω * μ + E‖ = ‖∑ z ∈ s, multDiff Z Z' z * pointImage F G z‖ := by
    rw [hsum_eq, norm_mul ((-I) ^ j), hnormI, one_mul]
  have hmain : ‖Φ ω‖ * ‖μ‖ ≤ ‖∑ z ∈ s, multDiff Z Z' z * pointImage F G z‖ + ‖E‖ := by
    rw [← norm_mul (Φ ω) μ, ← h2]; exact h1
  rw [← hμ, sq, sq]
  calc c * c * ‖μ‖ ≤ ‖Φ ω‖ * ‖μ‖ := mul_le_mul_of_nonneg_right hfloor (norm_nonneg _)
    _ ≤ _ := by
      have h1 := hmain.trans (add_le_add hDs hLip)
      have e : M * M = M ^ 2 := (sq M).symm
      rw [sq] at h1
      linarith

/-- **The net multiplicity of a near-coincident cluster vanishes.** Under the hypotheses of
`norm_discMoment_le` at `j = 0`, if the right-hand side is below `c_η²`, the cluster in the disc
has net multiplicity `0`: `Σ_{disc} m_Z = Σ_{disc} m_{Z'}`. -/
theorem sum_multDiff_eq_zero_of_disc {Z Z' : ZeroConfig} {s : Finset ℂ} {z₀ : ℂ} {c B : ℝ}
    (hc : 0 < c) (hB : c ^ 2 * ‖∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ 0‖ ≤ B)
    (hsmall : B < c ^ 2) : ∑ z ∈ s, multDiff Z Z' z = 0 := by
  classical
  have hint : ∀ z, ∃ m : ℤ, multDiff Z Z' z = m := fun z => by
    refine ⟨(if z ∈ Z.carrier then (Z.mult z : ℤ) else 0) -
      (if z ∈ Z'.carrier then (Z'.mult z : ℤ) else 0), ?_⟩
    simp only [multDiff, Set.indicator_apply]
    split_ifs <;> push_cast <;> ring
  choose m hm using hint
  have hsum : ∑ z ∈ s, multDiff Z Z' z = ((∑ z ∈ s, m z : ℤ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun z _ => hm z
  simp only [pow_zero, mul_one] at hB
  have hlt : ‖∑ z ∈ s, multDiff Z Z' z‖ < 1 := by
    by_contra hge
    push Not at hge
    have : c ^ 2 * 1 ≤ c ^ 2 * ‖∑ z ∈ s, multDiff Z Z' z‖ :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    linarith
  rw [hsum, Complex.norm_intCast] at hlt
  have h0 : (∑ z ∈ s, m z : ℤ) = 0 := by
    have : |((∑ z ∈ s, m z : ℤ) : ℝ)| < 1 := by exact_mod_cast hlt
    have h1 : |(∑ z ∈ s, m z : ℤ)| < 1 := by exact_mod_cast this
    have h2 := abs_lt.mp h1
    omega
  rw [hsum, h0, Int.cast_zero]

/-- **Pairs are read by the first two moments.** For a pair `p ± w/2` of one configuration against
`p' ± w'/2` of the other, the disc moments about `ω` are `μ₁ = 2(p − p')` and
`μ₂ = 2(p − ω)² + w²/2 − 2(p' − ω)² − w'²/2`. So `w² − w'² = 2μ₂ − 2μ₁(p + p' − 2ω)`. -/
theorem pair_moments (p w p' w' ω : ℂ) :
    ((p + w / 2 - ω) + (p - w / 2 - ω) - (p' + w' / 2 - ω) - (p' - w' / 2 - ω) = 2 * (p - p')) ∧
      w ^ 2 - w' ^ 2 = 2 * ((p + w / 2 - ω) ^ 2 + (p - w / 2 - ω) ^ 2 - (p' + w' / 2 - ω) ^ 2 -
        (p' - w' / 2 - ω) ^ 2) - 2 * (2 * (p - p')) * (p + p' - 2 * ω) :=
  ⟨by ring, by ring⟩

/-! ### The moments of a near-coincident cluster of `ζ` -/

/-- `(GC e^ε/F)² ≤ exp(2G' + 2 log C + 2ε + 2F')` from `log G ≤ G'` and `log F⁻¹ ≤ F'`. -/
theorem sq_div_floor_le_exp {G Cm F ε G' F' : ℝ} (hG : 0 < G) (hCm : 0 < Cm) (hF : 0 < F)
    (hG' : Real.log G ≤ G') (hF' : Real.log F⁻¹ ≤ F') :
    (G * Cm * 1 * Real.exp ε / F) ^ 2 ≤ Real.exp (2 * G' + 2 * Real.log Cm + 2 * ε + 2 * F') := by
  have hx : ∀ x : ℝ, Real.exp x ^ 2 = Real.exp (2 * x) := fun x => by
    rw [sq, ← Real.exp_add, two_mul]
  have e : (G * Cm * 1 * Real.exp ε / F) ^ 2 =
      Real.exp (2 * Real.log G + 2 * Real.log Cm + 2 * ε + 2 * Real.log F⁻¹) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, ← hx, ← hx, ← hx, ← hx, Real.exp_log hG,
      Real.exp_log hCm, Real.exp_log (inv_pos.mpr hF)]
    field_simp
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The Lipschitz part of the moment bound is `e^{O(L²)}`. -/
theorem disc_lipschitz_term_le {lam L a Ψ C : ℝ} (hL1 : 1 ≤ L) (hlam : 0 < lam)
    (ha : a = lam * L) (hΨ : Ψ ≤ (C - 4 * lam ^ 2 - lam) * L ^ 2) :
    4 * a ^ 2 * Real.exp (a / 2) * Real.exp Ψ ≤ Real.exp (C * L ^ 2) := by
  have h1 : 4 * a ^ 2 ≤ Real.exp (4 * a ^ 2) := by
    have := Real.add_one_le_exp (4 * a ^ 2); linarith
  have h2 : a / 2 ≤ lam * L ^ 2 := by
    rw [ha]; nlinarith
  calc 4 * a ^ 2 * Real.exp (a / 2) * Real.exp Ψ
      ≤ Real.exp (4 * a ^ 2) * Real.exp (a / 2) * Real.exp Ψ := by gcongr
    _ = Real.exp (4 * a ^ 2 + a / 2 + Ψ) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (C * L ^ 2) := by
        apply Real.exp_le_exp.mpr
        rw [ha] at *
        nlinarith

/-- **The camera reads the moments of every near-coincident cluster of `ζ`.** For a bandwidth
`λ > 1/4 + πμ/2`, `κ > 0` and `K ≥ 0` there are `C` and `X₀` with the following property. Let `X ≥ X₀`
and let `Z'` be a tempered mimic of `ζ` at aperture `λ log X`, of local density `≤ μ log X`. Let
`z₀` be a point of height `X` and `r λ log X ≤ 1`. Suppose the cluster near `X` lies in the disc
`‖z − z₀‖ ≤ r` or at distance `≥ exp(−κ log X/(1 + log log X))` from `z₀`. Then the moments of the
disc satisfy `‖μ_j‖ ≤ N r^{j+1} e^{C (log X)²} + e^{−K (log X)²}` for `j ≤ 2`. -/
theorem norm_discMoment_zeta_le {lam μ A' S' κ K : ℝ} (hlam : 1 / 4 + π * μ / 2 < lam)
    (hμ : 0 ≤ μ) (hA' : 0 ≤ A') (hκ : 0 < κ) (hK : 0 ≤ K) :
    ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ Z' : ZeroConfig, TemperedConfig Z' →
      (∀ f, ApertureWindow (lam * Real.log X) f → zetaZeroConfig.W f f = Z'.W f f) →
      ∑' z, ‖multDiff zetaZeroConfig Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S' →
      (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
        (∀ z ∈ s, z ∈ Z'.carrier ∧ |z.im - X| ≤ X / 2 ∧ z.im ∈ Icc x y) →
          (s.card : ℝ) ≤ μ * Real.log X * (y - x) + A' * Real.log X) →
      ∀ z₀ : ℂ, z₀.im = X → |z₀.re - 1 / 2| ≤ 1 / 2 → ∀ r : ℝ, 0 ≤ r →
      r * (lam * Real.log X) ≤ 1 →
      (∀ z, multDiff zetaZeroConfig Z' z ≠ 0 → |z.im - X| ≤ X / 2 →
        ‖z - z₀‖ ≤ r ∨ Real.exp (-(κ * Real.log X / (1 + Real.log (Real.log X)))) ≤ ‖z - z₀‖) →
      ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
      (∀ z, multDiff zetaZeroConfig Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) →
      ∀ j ≤ 2, ‖∑ z ∈ s, multDiff zetaZeroConfig Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
        (∑ z ∈ s, ‖multDiff zetaZeroConfig Z' z‖) * r ^ (j + 1) * Real.exp (C * Real.log X ^ 2) +
          Real.exp (-(K * Real.log X ^ 2)) := by
  classical
  obtain ⟨T₀, A, hT₀, hA, hζ⟩ := exists_card_le_sharp_centred
  have hπ := Real.pi_gt_three
  have hlam0 : 0 < lam := by nlinarith
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - 1 / 4 - π * μ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβlam : β ≤ lam := by rw [hβ]; nlinarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 3 + (2 * A + A' + 1) * π / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have hσ0 : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hg0 := growthRate_nonneg hℓ0
  have hf0 := floorRate_nonneg hℓ0
  obtain ⟨G₀, hG₀⟩ : ∃ G₀, G₀ = 2 * growthRate ℓ * lam ^ 2 := ⟨_, rfl⟩
  obtain ⟨F₀, hF₀⟩ : ∃ F₀, F₀ = floorRate ℓ * (4 * lam ^ 2 + κ * lam * (1 + |Real.log lam|)) :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * G₀ + 2 * F₀ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc, hG₀, hF₀]; positivity
  obtain ⟨K', hK'⟩ : ∃ K', K' = c + K + 1 := ⟨_, rfl⟩
  have hK'1 : 1 ≤ K' := by rw [hK']; linarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 4 * (e * lam + K' + 4) / β := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = Real.log (4 * (1 + ρ)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.log_nonneg (by linarith)
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S' 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  have hlS : 0 ≤ Real.log S'' := Real.log_nonneg hS''1
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = 2 * q * (e * lam + K' + 4) + 2 * lam + 3 := ⟨_, rfl⟩
  have hb₁0 : 0 ≤ b₁ := by rw [hb₁]; positivity
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max 1 (π / lam)) (max (1 / (2 * β))
      (b₁ + Real.log S'' + 4)) := ⟨_, rfl⟩
  refine ⟨4 * lam ^ 2 + lam + c + b₁ + 3, max (2 * T₀ + 16) (Real.exp L₀), ?_⟩
  intro X hX Z' hZ' hW hS hZ'count z₀ hz₀ hz₀re r hr hra hiso s hsd hds j hj
  have hX1 : 2 * T₀ + 16 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL] at hW hZ'count hiso hra ⊢
  have hLL₀ : L₀ ≤ L := by
    rw [hL, ← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hX)
  rw [hL₀] at hLL₀
  have hL1 : 1 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hLL₀
  have hLπ : π / lam ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hLL₀
  have hLβ : 1 / (2 * β) ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLL₀
  have hLb : b₁ + Real.log S'' + 4 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hLL₀
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hX0]
  -- the parameters
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * L / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨D, hD⟩ : ∃ D, D = (β / π + 1 / (2 * π) + μ) * L := ⟨_, rfl⟩
  have hDa : π * D / 2 + 2 * ε ≤ lam * L := by rw [hε]; exact camera_aperture_eq hβ hD
  have hDlow := camera_density_ge hμ hβ (by linarith) hD
  have hDup := camera_density_le hμ hβ hβ0 (by linarith) hD
  have hD1 : 1 ≤ D := by
    refine le_trans ?_ hDlow
    rw [le_div_iff₀ Real.pi_pos]
    have := (div_le_iff₀ hlam0).mp hLπ
    linarith only [this]
  have hD0 : 0 < D := by linarith
  obtain ⟨η, hη⟩ : ∃ η, η = Real.exp (-(κ * L / (1 + Real.log L))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact Real.exp_pos _
  have hη1 : η ≤ 1 := by
    have h0 : 0 ≤ κ * L / (1 + Real.log L) := by
      have := Real.log_nonneg hL1; positivity
    rw [hη]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hlogη : Real.log (1 / η) = κ * L / (1 + Real.log L) := by
    rw [hη, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  obtain ⟨C₀, hC₀ℓ, hcount⟩ := zeta_cluster_count hA hA' hμ hlam0 hζ hX1 hT₀ hL hL1
    (camera_density_count hβ0 hLβ hD) hDlow hℓ hZ'count
  -- the decay order and the bump
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈K' * L⌉₊ := ⟨_, rfl⟩
  have hkL : K' * L ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hkle : (k : ℝ) ≤ K' * L + 1 := by
    rw [hk]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℝ) ≤ K' * L := one_le_mul_of_one_le_of_one_le hK'1 hL1
    have : (1 : ℝ) ≤ k := h1.trans hkL
    exact_mod_cast this
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + (k + 2) := ⟨_, rfl⟩
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + 2 : ℕ) : ℝ) ≤ m := by
    rw [hmdef, ← hWdef]; push_cast; linarith [Nat.le_ceil W]
  have hmle : (m : ℝ) ≤ (e * lam + K' + 4) * L := by
    rw [hmdef]; push_cast
    have h1 : (⌈W⌉₊ : ℝ) ≤ W + 1 := (Nat.ceil_lt_add_one hW0).le
    have h2 : e * D ≤ e * (lam * L) := mul_le_mul_of_nonneg_left hDup he0
    have h3 : (e * lam + K' + 4) * L = e * (lam * L) + K' * L + 4 * L := by ring
    rw [h3]
    linarith only [h1, h2, hWle, hkle, hL1]
  have hmε : (m : ℝ) / ε ≤ ρ := by
    rw [div_le_iff₀ hε0, hρ, hε]
    have : 4 * (e * lam + K' + 4) / β * (β * L / 4) = (e * lam + K' + 4) * L := by
      field_simp
    rw [this]; exact hmle
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  have hCm0 : 0 < (4 * (1 + m / ε)) ^ m := by positivity
  have hlogCm : Real.log ((4 * (1 + m / ε)) ^ m) ≤ m * q := by
    rw [Real.log_pow, hq]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith))
      (Nat.cast_nonneg _)
  -- the moment bound
  have hrR : r ≤ X / 2 := by
    have h1 : 1 ≤ lam * L := by
      have := (div_le_iff₀ hlam0).mp hLπ; nlinarith
    have : r ≤ 1 := by nlinarith
    linarith
  have hiso' : ∀ z, multDiff zetaZeroConfig Z' z ≠ 0 → |z.im - z₀.im| ≤ X / 2 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖ := fun z hcz hzR => by
    rw [hη]; exact hiso z hcz (by rwa [hz₀] at hzR)
  have hmom := norm_discMoment_le (k := k) (C0 := 1) hD0 hη0 hε0 hDa hb hbs hb1 hk1 hm hbm
    (fun w => by rw [one_mul]; exact hb0 w) temperedConfig_zeta hZ' hW hz₀re
    (R := X / 2) (by positivity) hr hrR hra hiso'
    (fun t x y hxy ht => hcount t x y hxy (by rwa [hz₀] at ht)) hsd hds hj
  rw [hz₀] at hmom
  -- the size of the window constants
  obtain ⟨Gw, hGw⟩ : ∃ Gw, Gw = windowGrowth (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  obtain ⟨Fl, hFl⟩ : ∃ Fl, Fl = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  have hL0 := localSlack_nonneg (C₀ := C₀) hD0
  have hGw0 : 0 < Gw := by rw [hGw]; exact windowGrowth_pos (by positivity) hL0
  have hFl0 : 0 < Fl := by rw [hFl]; exact windowFloor_pos (by positivity) hL0 hη0
  rw [← hGw, ← hFl] at hmom
  have hGl : Real.log Gw ≤ G₀ * L ^ 2 := by
    rw [hGw, hG₀]; exact (log_windowGrowth_le hD1 hC₀ℓ).trans (growth_term_le hg0 hD1 hDup)
  have hFll : Real.log Fl⁻¹ ≤ F₀ * L ^ 2 := by
    have h := log_inv_windowFloor_le_of_le_one hD1 hC₀ℓ hη0 hη1
    rw [hlogη] at h
    rw [hFl, hF₀]
    exact h.trans (floor_term_le_of_small hf0 hD1 hlam0 hL1 hκ.le hDup)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = 2 * (G₀ * L ^ 2) + 2 * Real.log ((4 * (1 + m / ε)) ^ m) +
      2 * ε + 2 * (F₀ * L ^ 2) := ⟨_, rfl⟩
  have hratio := sq_div_floor_le_exp hGw0 hCm0 hFl0 hGl hFll
  rw [← hΨ] at hratio
  have hΨle : Ψ ≤ c * L ^ 2 + 2 * q * (e * lam + K' + 4) * L + β * L / 2 := by
    rw [hΨ, hc, hε]
    have : 2 * Real.log ((4 * (1 + m / ε)) ^ m) ≤ 2 * q * (e * lam + K' + 4) * L := by
      nlinarith [mul_le_mul_of_nonneg_right hmle hq0]
    linarith
  obtain ⟨Mw, hMw⟩ : ∃ Mw, Mw = Gw * (4 * (1 + m / ε)) ^ m * 1 * Real.exp ε := ⟨_, rfl⟩
  rw [← hMw] at hmom
  have hMw0 : 0 ≤ Mw := by rw [hMw]; positivity
  have hratio' : (Mw / Fl) ^ 2 ≤ Real.exp Ψ := by rw [hMw]; exact hratio
  -- divide by the floor
  have hFl2 : 0 < Fl ^ 2 := by positivity
  obtain ⟨N, hN⟩ : ∃ N, N = ∑ z ∈ s, ‖multDiff zetaZeroConfig Z' z‖ := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; exact Finset.sum_nonneg fun z _ => norm_nonneg _
  rw [← hN] at hmom ⊢
  obtain ⟨Sg, hSg⟩ : ∃ Sg,
      Sg = ∑' z, ‖multDiff zetaZeroConfig Z' z‖ / (1 + Complex.normSq (gammaOf z)) := ⟨_, rfl⟩
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]; exact tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf z); linarith)
  rw [← hSg] at hmom hS
  -- the Lipschitz term
  have hT1 : r ^ (j + 1) * (4 * (lam * L) ^ 2 * Mw ^ 2 * Real.exp (lam * L / 2)) / Fl ^ 2 ≤
      r ^ (j + 1) * Real.exp ((4 * lam ^ 2 + lam + c + b₁ + 3) * L ^ 2) := by
    have e1 : r ^ (j + 1) * (4 * (lam * L) ^ 2 * Mw ^ 2 * Real.exp (lam * L / 2)) / Fl ^ 2 =
        r ^ (j + 1) * (4 * (lam * L) ^ 2 * Real.exp (lam * L / 2) * (Mw / Fl) ^ 2) := by
      field_simp
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlip := disc_lipschitz_term_le (Ψ := Ψ) (C := 4 * lam ^ 2 + lam + c + b₁ + 3) hL1
      hlam0 rfl (by
        have h1 : 2 * q * (e * lam + K' + 4) * L ≤ b₁ * L ^ 2 := by
          have : 2 * q * (e * lam + K' + 4) ≤ b₁ := by rw [hb₁]; linarith
          nlinarith
        have h2 : β * L / 2 ≤ 3 * L ^ 2 := by nlinarith
        nlinarith)
    calc 4 * (lam * L) ^ 2 * Real.exp (lam * L / 2) * (Mw / Fl) ^ 2
        ≤ 4 * (lam * L) ^ 2 * Real.exp (lam * L / 2) * Real.exp Ψ :=
          mul_le_mul_of_nonneg_left hratio' (by positivity)
      _ ≤ _ := hlip
  -- the tail term
  have hT2 : Mw ^ 2 * Real.exp (lam * L) * (5 / 4 * (1 + |X|) ^ 2 / (1 + X / 2) ^ (2 * k - 2)) *
      Sg / Fl ^ 2 ≤ Real.exp (-(K * L ^ 2)) := by
    have hlow := camera_lower_bound hX0 hXL hk1
    have hpos : 0 < (1 + X / 2) ^ (2 * k - 2) := by positivity
    have hXim : (1 + |X|) ^ 2 ≤ 4 * Real.exp (2 * L) := by
      rw [abs_of_pos hX0, show 2 * L = L + L by ring, Real.exp_add, ← hXL]
      nlinarith
    have h5 : (5 : ℝ) ≤ Real.exp 2 := by
      have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have hSle : Sg ≤ Real.exp (Real.log S'') := by
      rw [Real.exp_log (by linarith)]; exact hS.trans (by rw [hS'']; exact le_max_left _ _)
    have e1 : Mw ^ 2 * Real.exp (lam * L) * (5 / 4 * (1 + |X|) ^ 2 / (1 + X / 2) ^ (2 * k - 2)) *
        Sg / Fl ^ 2 = (Mw / Fl) ^ 2 * Real.exp (lam * L) * (5 / 4 * (1 + |X|) ^ 2) * Sg /
          (1 + X / 2) ^ (2 * k - 2) := by
      field_simp
    rw [e1, div_le_iff₀ hpos]
    have hexp : (Mw / Fl) ^ 2 * Real.exp (lam * L) * (5 / 4 * (1 + |X|) ^ 2) * Sg ≤
        Real.exp (Ψ + lam * L + 2 * L + Real.log S'' + 2) := by
      calc (Mw / Fl) ^ 2 * Real.exp (lam * L) * (5 / 4 * (1 + |X|) ^ 2) * Sg
          ≤ Real.exp Ψ * Real.exp (lam * L) * (5 / 4 * (4 * Real.exp (2 * L))) *
              Real.exp (Real.log S'') := by
            gcongr
        _ = 5 * (Real.exp Ψ * Real.exp (lam * L) * Real.exp (2 * L) *
              Real.exp (Real.log S'')) := by ring
        _ ≤ Real.exp 2 * (Real.exp Ψ * Real.exp (lam * L) * Real.exp (2 * L) *
              Real.exp (Real.log S'')) := mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = Real.exp (Ψ + lam * L + 2 * L + Real.log S'' + 2) := by
            simp only [Real.exp_add]; ring
    refine hexp.trans ?_
    calc Real.exp (Ψ + lam * L + 2 * L + Real.log S'' + 2)
        ≤ Real.exp (-(K * L ^ 2)) * Real.exp (((k : ℝ) - 1) * L) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have h1 : (K' * L - 1) * L ≤ ((k : ℝ) - 1) * L :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          have h2 : (b₁ + Real.log S'' + 4) * L ≤ L * L := mul_le_mul_of_nonneg_right hLb
            (by linarith)
          have h3 : Real.log S'' + 4 ≤ (Real.log S'' + 4) * L := le_mul_of_one_le_right
            (by linarith) hL1
          have h4 : 2 * q * (e * lam + K' + 4) + β / 2 + lam + 2 ≤ b₁ := by rw [hb₁]; linarith
          have h5' : (2 * q * (e * lam + K' + 4) + β / 2 + lam + 2) * L ≤ b₁ * L :=
            mul_le_mul_of_nonneg_right h4 (by linarith)
          rw [hK'] at h1
          nlinarith
      _ ≤ Real.exp (-(K * L ^ 2)) * (1 + X / 2) ^ (2 * k - 2) :=
          mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
  -- combine
  have hfinal : Fl ^ 2 * ‖∑ z ∈ s, multDiff zetaZeroConfig Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
      Fl ^ 2 * (N * (r ^ (j + 1) * Real.exp ((4 * lam ^ 2 + lam + c + b₁ + 3) * L ^ 2)) +
        Real.exp (-(K * L ^ 2))) := by
    have hA1 := (div_le_iff₀ hFl2).mp hT1
    have hA2 := (div_le_iff₀ hFl2).mp hT2
    calc Fl ^ 2 * ‖∑ z ∈ s, multDiff zetaZeroConfig Z' z * (gammaOf z - gammaOf z₀) ^ j‖
        ≤ N * r ^ (j + 1) * (4 * (lam * L) ^ 2 * Mw ^ 2 * Real.exp (lam * L / 2)) +
            Mw ^ 2 * Real.exp (lam * L) *
              (5 / 4 * (1 + |X|) ^ 2 / (1 + X / 2) ^ (2 * k - 2)) * Sg := hmom
      _ ≤ N * (r ^ (j + 1) * Real.exp ((4 * lam ^ 2 + lam + c + b₁ + 3) * L ^ 2) * Fl ^ 2) +
            Real.exp (-(K * L ^ 2)) * Fl ^ 2 := by
          have := mul_le_mul_of_nonneg_left hA1 hN0
          nlinarith
      _ = _ := by ring
  have := le_of_mul_le_mul_left hfinal hFl2
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
