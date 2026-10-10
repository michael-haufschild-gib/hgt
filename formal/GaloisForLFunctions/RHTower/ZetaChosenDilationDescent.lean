import GaloisForLFunctions.RHTower.ZetaDilationHeightDescent
import GaloisForLFunctions.RHTower.KFreeExponentialCascade

/-!
# Chosen-branch dilation descent, and the fixed-`ε` closure of the `k`-free rungs

When the dilation can be **chosen** at each step, a band of real parts only has to be invariant
under the chosen map (`riemannZeta_ne_zero_of_chosenDilation`). The proof is the minimum-height
principle `riemannZeta_ne_zero_of_imDescent`.

**Fixed-`ε` closure.** At its RH-level exponent `1/(2k) + ε`, the smoothed `k`-free bound gives the
cascade band `(1/2 + kε, k/2 - k²ε)`. For `k ≥ 3` and small `ε` this band reaches beyond the 1-line,
so a single rung at one fixed `ε` excludes every zero with `Re s > 1/2 + kε`
(`riemannZeta_ne_zero_of_kBound_rhLevel`). Only the squarefree rung `k = 2`, with upper edge
`1 - 4ε`, needs every `ε`. Combining rungs with chosen branches
(`riemannZeta_ne_zero_of_squarefree_cubefree`) is therefore no stronger than the cubefree rung alone.
-/

open Complex

namespace RHTower.DilationCascade

noncomputable section

/-- **Chosen-branch dilation descent.** If every non-real zero with real part in `[a, b]` has a
dilation `k > 1` with `ζ(ρ/k) = 0` whose descendant `1 - Re ρ/k` stays in `[a, b]`, then `ζ` has
no zero with real part in `[a, b]`. -/
theorem riemannZeta_ne_zero_of_chosenDilation {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hstep : ∀ ρ : ℂ, riemannZeta ρ = 0 → a ≤ ρ.re → ρ.re ≤ b → ρ.im ≠ 0 →
      ∃ k : ℝ, 1 < k ∧ riemannZeta (ρ / k) = 0 ∧ a ≤ 1 - ρ.re / k ∧ 1 - ρ.re / k ≤ b)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) : riemannZeta s ≠ 0 := by
  by_cases him : s.im = 0
  · have hs : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hs]
    exact riemannZeta_ofReal_ne_zero (by linarith) (by linarith)
  set K : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ |s.im|} with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hc : IsClosed ({z : ℂ | a ≤ z.re} ∩ {z | z.re ≤ b} ∩ {z | |z.im| ≤ |s.im|}) :=
        ((isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
      convert hc using 1
      ext z
      simp only [hKdef, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |s.im|)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + |s.im| := by
            have : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
            linarith [hz.2.2]
  have h1K : (1 : ℂ) ∉ K := fun h => by
    have := h.2.1
    simp at this
    linarith
  refine riemannZeta_ne_zero_of_imDescent hKc h1K ?_ ⟨h1, h2, le_rfl⟩ him
  rintro z ⟨hza, hzb, hzs⟩ hz0 hzim
  obtain ⟨k, hk, hk0, hka, hkb⟩ := hstep z hz0 hza hzb hzim
  have hkpos : 0 < k := by linarith
  have hdre : (z / k).re = z.re / k := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_re]
  have hdim : (z / k).im = z.im / k := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_im]
  have hre0 : 0 < (z / k).re := by rw [hdre]; exact div_pos (by linarith) hkpos
  have hre1 : (z / k).re < 1 := by rw [hdre, div_lt_one hkpos]; linarith
  have hwim : (1 - z / k).im = -(z.im / k) := by
    simp only [Complex.sub_im, Complex.one_im, zero_sub, hdim]
  have habs : |(1 - z / k).im| = |z.im| / k := by
    rw [hwim, abs_neg, abs_div, abs_of_pos hkpos]
  have hzpos : 0 < |z.im| := abs_pos.mpr hzim
  refine ⟨1 - z / k, ⟨?_, ?_, ?_⟩, (riemannZeta_one_sub_eq_zero_iff hre0 hre1).mpr hk0, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re, hdre]; exact hka
  · simp only [Complex.sub_re, Complex.one_re, hdre]; exact hkb
  · rw [habs]; exact (div_le_self (abs_nonneg _) hk.le).trans hzs
  · rw [hwim]; exact neg_ne_zero.mpr (div_ne_zero hzim hkpos.ne')
  · rw [habs]; exact div_lt_self hzpos hk

/-- **Squarefree and cubefree together close the half-plane at a fixed `ε`.** -/
theorem riemannZeta_ne_zero_of_squarefree_cubefree {ε C C' : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 30)
    (hB₂ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |KFreeExponential.kProfile 2 t -
      KFreeExponential.kDensity 2 / t| ≤ C * t ^ (-(1 / 4 + ε)))
    (hB₃ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |KFreeExponential.kProfile 3 t -
      KFreeExponential.kDensity 3 / t| ≤ C' * t ^ (-(1 / 6 + ε)))
    {s : ℂ} (hs : 1 / 2 + 3 * ε < s.re) : riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with hs1 | hs1
  · exact riemannZeta_ne_zero_of_one_le_re hs1
  set a : ℝ := min ((s.re + (1 / 2 + 3 * ε)) / 2) (3 / 5) with hadef
  have ha1 : 1 / 2 + 3 * ε < a := by rw [hadef]; exact lt_min (by linarith) (by linarith)
  have has : a ≤ s.re := by rw [hadef]; exact (min_le_left _ _).trans (by linarith)
  have ha35 : a ≤ 3 / 5 := min_le_right _ _
  have ha2 : a < 1 := by linarith
  set b : ℝ := max s.re (max (1 - a / 2) ((1 + 2 * a) / 3)) with hbdef
  have hb1 : b < 1 := by
    rw [hbdef]
    refine max_lt hs1 (max_lt (by linarith) (by linarith))
  have hsb : s.re ≤ b := le_max_left _ _
  have hb2 : 1 - a / 2 ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
  have hb3 : (1 + 2 * a) / 3 ≤ b := le_trans (le_max_right _ _) (le_max_right _ _)
  have hε2 : 0 ≤ 1 / 4 + ε := by linarith
  have hε3 : 0 ≤ 1 / 6 + ε := by linarith
  refine riemannZeta_ne_zero_of_chosenDilation (a := a) (b := b) (by linarith) hb1 ?_ has hsb
  intro ρ hρ hρa hρb _
  have hρ1 : ρ.re < 1 := lt_of_le_of_lt hρb hb1
  rcases le_or_gt ρ.re (2 - 2 * a) with hx | hx
  · -- the halving step
    have h := KFreeExponential.riemannZeta_div_eq_zero_of_kBound (k := 2) le_rfl hε2
      (by linarith) hB₂ hρ (by push_cast; linarith) hρ1
    refine ⟨2, by norm_num, by exact_mod_cast h, by linarith, by linarith⟩
  · -- the third step
    have h := KFreeExponential.riemannZeta_div_eq_zero_of_kBound (k := 3) (by norm_num) hε3
      (by linarith) hB₃ hρ (by push_cast; linarith) hρ1
    refine ⟨3, by norm_num, by exact_mod_cast h, by linarith, by linarith⟩

/-- **Fixed-`ε` closure of a rung `k ≥ 3`.** If `|A_k(t) - c_k/t| ≤ C t^{-(1/(2k) + ε)}` on
`(0, 1]` with `k ≥ 3` and `2k²ε ≤ k - 2`, then `ζ` has no zero with `Re s > 1/2 + kε`. -/
theorem riemannZeta_ne_zero_of_kBound_rhLevel {k : ℕ} (hk : 3 ≤ k) {ε C : ℝ} (hε : 0 < ε)
    (hεk : 2 * (k : ℝ) ^ 2 * ε ≤ k - 2)
    (hB : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |KFreeExponential.kProfile k t -
      KFreeExponential.kDensity k / t| ≤ C * t ^ (-(1 / (2 * k) + ε)))
    {s : ℂ} (hs : 1 / 2 + k * ε < s.re) : riemannZeta s ≠ 0 := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rcases le_or_gt 1 s.re with hs1 | hs1
  · exact riemannZeta_ne_zero_of_one_le_re hs1
  have hα : (0 : ℝ) ≤ 1 / (2 * k) + ε := by positivity
  have hα1 : 1 / (2 * k) + ε ≤ 1 := by
    have h1 : 1 / (2 * (k : ℝ)) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h2 : ε ≤ 1 / 2 := by nlinarith
    linarith
  have hkα : (k : ℝ) * (1 / (2 * k) + ε) = 1 / 2 + k * ε := by field_simp
  refine KFreeExponential.riemannZeta_ne_zero_of_kBound (by omega) hα hα1 hB ?_ ?_
  · rw [hkα]; exact hs
  · rw [hkα, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hk0]
    nlinarith

end

end RHTower.DilationCascade
