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

So the net multiplicity `μ₀` of the disc vanishes (`discMoment_zero_eq_zero`). The first and second
moments vanish to orders `r²` and `r³`. For a pair `c ± w/2` of `Z` against `c' ± w'/2` of `Z'`
this fixes the centre to `O(r²)` and the squared gap `w²` to `O(r³)`. The sign of `w²` (a real pair
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
    rw [← integral_inv_one_add_sq, ← integral_const_mul]
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
    _ = M / 2 := by field_simp; ring

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

end GaloisForLFunctions.ZeroConfigurationGeometry
