import GaloisForLFunctions.RHTower.WeilFunctionalLineIntegral

/-!
# The explicit formula for an atomic Weil function

Let `lam` be real with `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1` its Weil
function is a positive atomic Herglotz series,

`Φ_lam(s) = Σ_i c_i (1/(s − ½ − iτ_i) + 1/(s − ½ + iτ_i))`,  `c_i ≥ 0`,  `Σ_i c_i/(1 + τ_i²) < ∞`,

over a countable index set.  Then for every `C²` compactly supported `f`

`W_lam(f ⋆ f̃) = Σ_i c_i (|f̂(τ_i)|² + |f̂(−τ_i)|²)`  (`weilFullFunctional_weilTest_eq_atomic`),

so `lam` is full-cone Weil-positive (`weilPositiveFull_of_atomic`).

**Proof.**  By `WeilLineIntegral.weilFullFunctional_eq_line_integral`, `W_lam(k)` is the line
integral of `(H(s) + H(1 − s))Φ_lam(s)` on `Re s = 5/4`.  For `k = f ⋆ f̃` the transform is a
product, so `|H(σ + it)| ≪ (1 + t²)^{−2}`.  With `w = s − ½`, `a = Re w`, each atom satisfies
`|g(s)| ≤ (|w|/a) Re g(s)` (AM–GM), so `Σ_i c_i |g_i(s)| ≤ (|w|/a) |Φ_lam(s)| ≪ (1 + |t|)²`; the
series may be integrated termwise, and each atom contributes `H(½ + iτ) + H(½ − iτ)` by the
two-line residue identity `WeilLineIntegral.two_line_pair`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open Zeta23 Zeta23.WeilEF

noncomputable section

namespace RHTower.WeilAtomic

open WeilLineIntegral

/-! ## One atom -/

/-- `|g(s)| ≤ (|w|/a) Re g(s)` for `g = 1/(w − iτ) + 1/(w + iτ)`, `w = s − ½`, `a = Re w > 0`. -/
theorem norm_gPair_le_re {τ : ℝ} {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖gPair (1 / 2 + τ * I) s‖ ≤ ‖s - 1 / 2‖ / (s.re - 1 / 2) * (gPair (1 / 2 + τ * I) s).re := by
  set w : ℂ := s - 1 / 2 with hw
  have ha : 0 < w.re := by rw [hw]; simp; linarith
  set u : ℂ := w - τ * I with hu
  set v : ℂ := w + τ * I with hv
  have hure : u.re = w.re := by simp [hu]
  have hvre : v.re = w.re := by simp [hv]
  have hu0 : u ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hure] at this; simp at this; linarith
  have hv0 : v ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hvre] at this; simp at this; linarith
  have hg : gPair (1 / 2 + τ * I) s = 1 / u + 1 / v := by
    simp only [gPair, hu, hv, hw]
    congr 2 <;> ring
  have hre_w : s.re - 1 / 2 = w.re := by rw [hw]; simp
  rw [hg, hre_w]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hsum : 1 / u + 1 / v = 2 * w / (u * v) := by
    field_simp
    simp only [hu, hv]
    ring
  have hreu : (1 / u).re = w.re / ‖u‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, hure]
  have hrev : (1 / v).re = w.re / ‖v‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, hvre]
  rw [Complex.add_re, hreu, hrev, hsum, norm_div, norm_mul, norm_mul,
    show ‖(2 : ℂ)‖ = 2 by norm_num]
  have key : 2 / (‖u‖ * ‖v‖) ≤ 1 / ‖u‖ ^ 2 + 1 / ‖v‖ ^ 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [sq_nonneg (‖u‖ - ‖v‖), mul_pos hnu hnv]
  calc 2 * ‖w‖ / (‖u‖ * ‖v‖) = ‖w‖ * (2 / (‖u‖ * ‖v‖)) := by ring
    _ ≤ ‖w‖ * (1 / ‖u‖ ^ 2 + 1 / ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = ‖w‖ / w.re * (w.re / ‖u‖ ^ 2 + w.re / ‖v‖ ^ 2) := by field_simp
theorem re_gPair_nonneg {τ : ℝ} {s : ℂ} (hs : 1 / 2 < s.re) :
    0 ≤ (gPair (1 / 2 + τ * I) s).re := by
  have h := norm_gPair_le_re (τ := τ) hs
  have hw : 0 < ‖s - 1 / 2‖ / (s.re - 1 / 2) := by
    refine div_pos (norm_pos_iff.mpr fun h0 => ?_) (by linarith)
    have := congrArg Complex.re h0
    simp at this
    linarith
  by_contra hneg
  have : ‖s - 1 / 2‖ / (s.re - 1 / 2) * (gPair (1 / 2 + τ * I) s).re < 0 :=
    mul_neg_of_pos_of_neg hw (lt_of_not_ge hneg)
  linarith [norm_nonneg (gPair (1 / 2 + τ * I) s)]

/-! ## Decay of an autocorrelation transform -/

/-- `H_{f⋆f̃}(s) = H_f(s) · conj H_f(1 − s̄)`, so `|H_{f⋆f̃}(σ + it)| ≪ (1 + t²)^{−2}` on
`−1 ≤ σ ≤ 2`. -/
theorem norm_Hfn_weilTest_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖Hfn (EF.weilTest f f) (σ + t * I)‖ ≤ C / (1 + t ^ 2) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hf hfc
  refine ⟨C * C, mul_nonneg hC0 hC0, fun σ t h1 h2 => ?_⟩
  have hfac : Hfn (EF.weilTest f f) (σ + t * I) =
      Hfn f (σ + t * I) * (starRingEnd ℂ) (Hfn f (((1 - σ : ℝ) : ℂ) + t * I)) := by
    unfold Hfn
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc]
    congr 3
    rw [map_div₀, Complex.conj_I, map_sub, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    field_simp
    ring
  rw [hfac, norm_mul, Complex.norm_conj, pow_two, ← div_mul_div_comm]
  exact mul_le_mul (hC σ t h1 h2) (hC (1 - σ) t (by linarith) (by linarith)) (norm_nonneg _)
    (div_nonneg hC0 (by positivity))

/-! ## Growth of the Weil function on a vertical line -/

theorem norm_gPair_zero_le {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ 1 / c + 1 / (c - 1) := by
  unfold gPair
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_one, sub_zero]
    refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    have hre : ((c : ℂ) + t * I).re = c := by simp
    rw [hre, abs_of_pos (by linarith)] at this
    exact this
  · rw [norm_div, norm_one]
    refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
    have := Complex.abs_re_le_norm ((c : ℂ) + t * I - (1 - 0))
    have hre : ((c : ℂ) + t * I - (1 - 0)).re = c - 1 := by simp
    rw [hre, abs_of_pos (show (0 : ℝ) < c - 1 by linarith)] at this
    exact this

/-- `|Φ_lam(c + it)| ≤ A (1 + |t|)` for `1 < c ≤ 3/2`. -/
theorem norm_weilFunction_le {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {c : ℝ} (hc1 : 1 < c)
    (hc2 : c ≤ 3 / 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, ‖WeilHerglotz.weilFunction lam (c + t * I)‖ ≤ A * (1 + |t|) := by
  obtain ⟨B, hB0, hB⟩ := Zeta23.WeilEF.norm_logDeriv_Gammaℝ_le
  have hsumL := lseriesSummable_lamC hsl hc1
  set S : ℝ := ∑' n, ‖LSeries.term (WeilHerglotz.lamC lam) c n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have hLb : ∀ t : ℝ, ‖LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)‖ ≤ S := by
    intro t
    have hs : LSeriesSummable (WeilHerglotz.lamC lam) ((c : ℂ) + t * I) :=
      (LSeriesSummable_iff_of_re_eq_re (by simp)).mpr hsumL
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hg0 : 0 ≤ 1 / c + 1 / (c - 1) := by
    have : 0 < c - 1 := by linarith
    positivity
  refine ⟨B + (1 / c + 1 / (c - 1)) + S, by positivity, fun t => ?_⟩
  rw [weilFunction_eq lam (by simp; linarith)]
  have hlog : Real.log (2 + |t|) ≤ 1 + |t| := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + |t| by positivity)
    linarith
  have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc ‖logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) + gPair 0 ((c : ℂ) + t * I) -
        LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)‖
      ≤ ‖logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)‖ + ‖gPair 0 ((c : ℂ) + t * I)‖ +
          ‖LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ B * Real.log (2 + |t|) + (1 / c + 1 / (c - 1)) + S := by
        gcongr
        · exact hB c t (by linarith) hc2
        · exact norm_gPair_zero_le hc1 t
        · exact hLb t
    _ ≤ B * (1 + |t|) + (1 / c + 1 / (c - 1)) * (1 + |t|) + S * (1 + |t|) := by
        gcongr
        · exact le_mul_of_one_le_right hg0 h1
        · exact le_mul_of_one_le_right hS0 h1
    _ = (B + (1 / c + 1 / (c - 1)) + S) * (1 + |t|) := by ring

/-! ## The explicit formula -/

/-- **The explicit formula for an atomic Weil function.**  If on `Re s > 1`
`Φ_lam(s) = Σ_i c_i g_{½ + iτ_i}(s)` with `c_i ≥ 0`, then
`W_lam(f ⋆ f̃) = Σ_i c_i (|f̂(τ_i)|² + |f̂(−τ_i)|²)`. -/
theorem weilFullFunctional_weilTest_eq_atomic {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {ι : Type*} [Countable ι] {c τ : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hΦ : ∀ s : ℂ, 1 < s.re →
      HasSum (fun i => (c i : ℂ) * gPair (1 / 2 + τ i * I) s) (WeilHerglotz.weilFunction lam s))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    HasSum (fun i => ((c i * (‖paperFT f (τ i)‖ ^ 2 + ‖paperFT f (-τ i)‖ ^ 2) : ℝ) : ℂ))
      (weilFullFunctional lam (EF.weilTest f f)) := by
  set k := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  set c₀ : ℝ := 5 / 4 with hc₀
  have hc1 : 1 < c₀ := by norm_num
  have hc2 : c₀ ≤ 3 / 2 := by norm_num
  have hline := weilFullFunctional_eq_line_integral hsl hkd hkc hc1 hc2
  obtain ⟨Ck, hCk0, hCk⟩ := norm_Hfn_le hkd hkc
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le hf hfc
  obtain ⟨A, hA0, hA⟩ := norm_weilFunction_le hsl hc1 hc2
  set F : ℝ → ℂ := fun t => Hfn k (c₀ + t * I) + Hfn k (1 - c₀ - t * I) with hF
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c₀ - t * I = ((1 - c₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c₀ t (by norm_num) (by norm_num)
    have h2 := hD (1 - c₀) (-t) (by norm_num) (by norm_num)
    rw [neg_sq] at h2
    rw [two_mul, add_div]
    exact add_le_add h1 h2
  have hFc : Continuous F := by
    have hm : ∀ t : ℝ, Hfn k (1 - c₀ - t * I) = Hfn (fun u => k (-u)) (c₀ + t * I) :=
      fun t => Hfn_mirror k c₀ t
    simp only [hF, hm]
    exact (continuous_Hfn_line hkd hkc c₀).add
      (continuous_Hfn_line (hkd.comp contDiff_neg) (hkc.comp_homeomorph (Homeomorph.neg ℝ)) c₀)
  set z : ι → ℂ := fun i => 1 / 2 + τ i * I with hz
  set G : ι → ℝ → ℂ := fun i t => F t * ((c i : ℂ) * gPair (z i) (c₀ + t * I)) with hG
  have hre : ∀ t : ℝ, ((c₀ : ℂ) + t * I).re = c₀ := fun t => by simp
  have hgcont : ∀ i, Continuous (fun t : ℝ => gPair (z i) ((c₀ : ℂ) + t * I)) := by
    intro i
    unfold gPair
    refine Continuous.add ?_ ?_
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp [hz, hc₀] at this; norm_num at this
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp [hz, hc₀] at this; norm_num at this
  -- the pointwise majorant
  set w : ℝ → ℝ := fun t => ‖((c₀ : ℂ) + t * I) - 1 / 2‖ / (c₀ - 1 / 2) with hw
  have hwb : ∀ t : ℝ, w t ≤ 2 * (1 + |t|) := by
    intro t
    simp only [hw]
    rw [div_le_iff₀ (show (0 : ℝ) < c₀ - 1 / 2 by norm_num [hc₀])]
    have e : ((c₀ : ℂ) + t * I) - 1 / 2 = ((3 / 4 : ℝ) : ℂ) + t * I := by
      rw [hc₀]; push_cast; ring
    rw [e]
    calc ‖((3 / 4 : ℝ) : ℂ) + t * I‖ ≤ ‖((3 / 4 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 3 / 4 + |t| := by simp
      _ ≤ 2 * (1 + |t|) * (c₀ - 1 / 2) := by rw [hc₀]; linarith [abs_nonneg t]
  have hpt : ∀ (u : Finset ι) (t : ℝ), ∑ i ∈ u, ‖G i t‖ ≤ 8 * D * A * (1 + t ^ 2)⁻¹ := by
    intro u t
    have hs : 1 / 2 < ((c₀ : ℂ) + t * I).re := by rw [hre]; norm_num [hc₀]
    have hreS : HasSum (fun i => c i * (gPair (z i) ((c₀ : ℂ) + t * I)).re)
        (WeilHerglotz.weilFunction lam (c₀ + t * I)).re := by
      have := Complex.hasSum_re (hΦ ((c₀ : ℂ) + t * I) (by rw [hre]; exact hc1))
      refine this.congr_fun fun i => ?_
      simp [hz]
    have hsumle : ∑ i ∈ u, c i * (gPair (z i) ((c₀ : ℂ) + t * I)).re ≤
        (WeilHerglotz.weilFunction lam (c₀ + t * I)).re := by
      rw [← hreS.tsum_eq]
      exact hreS.summable.sum_le_tsum u fun i _ => mul_nonneg (hc i) (re_gPair_nonneg hs)
    have hterm : ∀ i, ‖G i t‖ ≤ ‖F t‖ * w t * (c i * (gPair (z i) ((c₀ : ℂ) + t * I)).re) := by
      intro i
      simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc i)]
      have := norm_gPair_le_re (τ := τ i) hs
      rw [hre] at this
      calc ‖F t‖ * (c i * ‖gPair (z i) ((c₀ : ℂ) + t * I)‖)
          ≤ ‖F t‖ * (c i * (w t * (gPair (z i) ((c₀ : ℂ) + t * I)).re)) := by
            gcongr
            exact hc i
        _ = ‖F t‖ * w t * (c i * (gPair (z i) ((c₀ : ℂ) + t * I)).re) := by ring
    have hwt0 : 0 ≤ w t := by simp only [hw]; exact div_nonneg (norm_nonneg _) (by norm_num [hc₀])
    calc ∑ i ∈ u, ‖G i t‖
        ≤ ∑ i ∈ u, ‖F t‖ * w t * (c i * (gPair (z i) ((c₀ : ℂ) + t * I)).re) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ‖F t‖ * w t * ∑ i ∈ u, c i * (gPair (z i) ((c₀ : ℂ) + t * I)).re := by
          rw [Finset.mul_sum]
      _ ≤ ‖F t‖ * w t * (WeilHerglotz.weilFunction lam (c₀ + t * I)).re := by
          gcongr
      _ ≤ ‖F t‖ * w t * ‖WeilHerglotz.weilFunction lam (c₀ + t * I)‖ := by
          gcongr
          exact Complex.re_le_norm _
      _ ≤ (2 * D / (1 + t ^ 2) ^ 2) * (2 * (1 + |t|)) * (A * (1 + |t|)) := by
          gcongr
          · exact hFb t
          · exact hwb t
          · exact hA t
      _ = 4 * D * A * ((1 + |t|) ^ 2 / (1 + t ^ 2)) * (1 + t ^ 2)⁻¹ := by
          field_simp
          ring
      _ ≤ 4 * D * A * 2 * (1 + t ^ 2)⁻¹ := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
      _ = 8 * D * A * (1 + t ^ 2)⁻¹ := by ring
  have hmaj : Integrable (fun t : ℝ => 8 * D * A * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hGi : ∀ i, Integrable (G i) := by
    intro i
    refine hmaj.mono' (hFc.mul (continuous_const.mul (hgcont i))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have := hpt {i} t
    simpa using this
  have hsum : Summable fun i => ∫ t : ℝ, ‖G i t‖ := by
    refine summable_of_sum_le (c := ∫ t : ℝ, 8 * D * A * (1 + t ^ 2)⁻¹)
      (fun i => integral_nonneg fun t => norm_nonneg _) fun u => ?_
    rw [← integral_finsetSum u fun i _ => (hGi i).norm]
    exact integral_mono (integrable_finsetSum u fun i _ => (hGi i).norm) hmaj fun t => hpt u t
  have hHS := hasSum_integral_of_summable_integral_norm hGi hsum
  -- each atom
  have hatom : ∀ i, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, G i t =
      ((c i * (‖paperFT f (τ i)‖ ^ 2 + ‖paperFT f (-τ i)‖ ^ 2) : ℝ) : ℂ) := by
    intro i
    have h2 := two_line_pair (differentiable_Hfn hkd hkc) (c := c₀) (C := Ck)
      (fun σ t h1 h2 => hCk σ t (by norm_num [hc₀] at h1 ⊢; linarith)
        (by norm_num [hc₀] at h2 ⊢; linarith)) (z₀ := z i)
      (by simp [hz]; norm_num [hc₀]) (by simp [hz]; norm_num [hc₀])
    have hHz : Hfn k (z i) = ((‖paperFT f (τ i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hk, ← paperFT_weilTest_self_ofReal hf.continuous hfc]
      unfold Hfn
      congr 1
      simp only [hz]
      rw [div_I]
      ring_nf
      rw [I_sq]
      ring
    have hHz' : Hfn k (1 - z i) = ((‖paperFT f (-τ i)‖ ^ 2 : ℝ) : ℂ) := by
      have hneg := paperFT_weilTest_self_ofReal hf.continuous hfc (-τ i)
      rw [Complex.ofReal_neg] at hneg
      rw [hk, ← hneg]
      unfold Hfn
      congr 1
      simp only [hz]
      rw [div_I]
      ring_nf
      rw [I_sq]
      ring
    have e : (∫ t : ℝ, G i t) = (c i : ℂ) * ∫ t : ℝ, F t * gPair (z i) (c₀ + t * I) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hG]
      ring
    rw [e, mul_left_comm, h2, hHz, hHz']
    push_cast
    ring
  have hsum2 : (∫ t : ℝ, ∑' i, G i t) = ∫ t : ℝ, F t * WeilHerglotz.weilFunction lam (c₀ + t * I) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hG]
    rw [tsum_mul_left, (hΦ _ (by rw [hre]; exact hc1)).tsum_eq]
  rw [hline]
  have := hHS.mul_left (1 / (2 * Real.pi) : ℂ)
  rw [hsum2] at this
  exact this.congr_fun fun i => (hatom i).symm

/-- **Atomic Weil functions with nonnegative masses on the critical line are full-cone
Weil-positive.** -/
theorem weilPositiveFull_of_atomic {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {ι : Type*} [Countable ι] {c τ : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hΦ : ∀ s : ℂ, 1 < s.re →
      HasSum (fun i => (c i : ℂ) * gPair (1 / 2 + τ i * I) s) (WeilHerglotz.weilFunction lam s)) :
    WeilPositiveFull lam := by
  intro f hf hfc
  have h := Complex.hasSum_re (weilFullFunctional_weilTest_eq_atomic hsl hc hΦ hf hfc)
  rw [← h.tsum_eq]
  exact tsum_nonneg fun i => by
    simp only [Complex.ofReal_re]
    exact mul_nonneg (hc i) (by positivity)

end RHTower.WeilAtomic
