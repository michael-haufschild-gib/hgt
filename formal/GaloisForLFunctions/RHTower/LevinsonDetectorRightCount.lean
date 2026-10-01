import GaloisForLFunctions.RHTower.XiHermiteBiehlerCount
import GaloisForLFunctions.RHTower.LevinsonEntireDetector
import GaloisForLFunctions.RHTower.ArchLadderRegular
import GaloisForLFunctions.RHTower.PrimeBoundaryMonodromyEscape

/-!
# Levinson's detector has exactly the zeros of `ξ` to the right of the line

Let `G = ζ + λζ'` (`levinsonG`) with `λ > 0`, and let `A = archFactor'/archFactor`, so that
`ξ'/ξ = A + ζ'/ζ`. Then

`G = ζ · (1 + λζ'/ζ) = ζ · (1 − λA + λ ξ'/ξ)`.

For `0 < Re s ≤ 2` and `Im s ≥ 100`, `Re A(s) ≤ ½ log(Im s/2π) + 1/20`
(`re_logDeriv_archFactor_le_of_re_le_two`).

**Theorem** (`exists_levinsonG_count_right`). Let `λ > 0` with `λ(½ log(T₂/2π) + 1/20) < 1`, and let
`100 ≤ T₁ < T₂` be unshadowed heights. Then `ζ + λζ'` and `ξ` have the same number of zeros, with
multiplicity, in `1/2 < Re s < 2`, `T₁ < Im s < T₂`.

**Proof.**
- Put `c₀ = 1 − λ(½ log(T₂/2π) + 1/20) > 0`. Then `Re(1 + λζ'/ζ) ≥ c₀ + λ Re ξ'/ξ` on the window.
- On the horizontal edges and on `Re s = 2`, `Re ξ'/ξ > 0`.
- On `Re s = 1/2 + δ`, `Re ξ'/ξ > −c₀/λ` for small `δ` (`exists_xi_right_edge_re_logDeriv_gt`).
- The winding lemma, applied to the entire detector `(s − 1)²G` against `(s − 1)²ζ`, equates the
  counts. On the window `(s − 1)²ζ` and `ξ` differ by a zero-free analytic factor.

**Consequence.** In the range `0 < λ < 2/log(T/2π)` (approximately), the zeros of Levinson's
detector to the right of the critical line are exactly the off-line zeros of `ζ` there. The only
other zeros of `G` in `Re s ≥ 1/2` sit on the line, at the multiple zeros of `ξ`. Under RH, `G` has
no zeros in `1/2 < Re s ≤ 2`, `100 ≤ Im s ≤ T` (`levinsonG_ne_zero_right_of_re_zeros`).
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- `Re archFactor'/archFactor(w) ≤ ½ log(Im w/2π) + 1/20` for `0 < Re w ≤ 2`, `Im w ≥ 100`. -/
theorem re_logDeriv_archFactor_le_of_re_le_two {w : ℂ} (h0 : 0 < w.re) (h2 : w.re ≤ 2)
    (ht : 100 ≤ w.im) :
    (logDeriv archFactor w).re ≤ Real.log (w.im / (2 * Real.pi)) / 2 + 1 / 20 := by
  set t := w.im with htdef
  have ht0 : 0 < t := by linarith
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_im] at htdef; linarith
  rw [logDeriv_archFactor_closed h0 hw0 hw1, GaloisForLFunctions.gammaRealLogConnection]
  have hA : (1 / w).re ≤ 1 / 5000 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have hsq : 10000 ≤ w.im * w.im := by nlinarith
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith [sq_nonneg w.re]
  have hB : (1 / (w - 1)).re ≤ 1 / 10000 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have e1 : (w - 1).re = w.re - 1 := by simp
    have e2 : (w - 1).im = t := by simp [htdef]
    rw [e1, e2]
    have hsq : 10000 ≤ (w.re - 1) * (w.re - 1) + t * t := by nlinarith [sq_nonneg (w.re - 1)]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hre2 : 0 < (w / 2).re := by rw [Complex.div_re]; simp; positivity
  have hn : t / 2 ≤ ‖w / 2‖ := by
    have := Complex.abs_im_le_norm (w / 2)
    have e : (w / 2).im = t / 2 := by simp [htdef]
    rw [e, abs_of_pos (by linarith)] at this; exact this
  have hnu : ‖w / 2‖ ≤ (t + 2) / 2 := by
    rw [norm_div, Complex.norm_two]
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos h0, abs_of_pos ht0] at this
    linarith
  have hd := (abs_le.mp (abs_re_digamma_sub_log_norm_le hre2 (by linarith))).2
  have hl : Real.log ‖w / 2‖ ≤ Real.log ((t + 2) / 2) :=
    Real.log_le_log (by linarith) hnu
  have hl2 : Real.log ((t + 2) / 2) ≤ Real.log (t / 2) + 2 / t := by
    have e : (t + 2) / 2 = (t / 2) * (1 + 2 / t) := by field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 / t by positivity)
    linarith
  have hi : 3 / ‖w / 2‖ ≤ 3 / 50 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hit : 2 / t ≤ 1 / 50 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]; linarith
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_pos.ne']
  have hre : (1 / w + 1 / (w - 1) + (-(((Real.log Real.pi : ℝ) : ℂ) / 2) +
      Complex.digamma (w / 2) / 2)).re = (1 / w).re + (1 / (w - 1)).re -
        Real.log Real.pi / 2 + (Complex.digamma (w / 2)).re / 2 := by
    simp [Complex.add_re, Complex.neg_re]
    ring
  rw [hre, hlog]
  linarith

/-- For `Re s > 0`, `s ≠ 1`, `ζ(s) ≠ 0`: `ξ(s) ≠ 0` and `ξ'/ξ = archFactor'/archFactor + ζ'/ζ`. -/
theorem logDeriv_xi_eq_archFactor_add_of_re_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    xi s ≠ 0 ∧ logDeriv xi s = logDeriv archFactor s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hxi : xi s = archFactor s * riemannZeta s :=
    xi_eq_archFactor_mul_zeta hs0 h1 (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  have hA := archFactor_ne_zero_of_re_pos h0 h1
  refine ⟨by rw [hxi]; exact mul_ne_zero hA hζ, ?_⟩
  have hU : {z : ℂ | 0 < z.re ∧ z ≠ 1} ∈ 𝓝 s :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne).mem_nhds ⟨h0, h1⟩
  have hev : xi =ᶠ[𝓝 s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hU] with z hz
    exact xi_eq_archFactor_mul_zeta
      (fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz.1) hz.2
      (Complex.Gammaℝ_ne_zero_of_re_pos hz.1)
  rw [logDeriv_eq_of_germ_eq hev, logDeriv_mul s hA hζ
    (analyticAt_archFactor_of_re_pos h0).differentiableAt (differentiableAt_riemannZeta h1)]

/-- For `Re s > 0`, `s ≠ 1`: `ξ(s) = 0 ↔ ζ(s) = 0`. -/
theorem xi_eq_zero_iff_riemannZeta_of_re_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    xi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  rw [xi_eq_archFactor_mul_zeta hs0 h1 (Complex.Gammaℝ_ne_zero_of_re_pos h0), mul_eq_zero]
  simp [archFactor_ne_zero_of_re_pos h0 h1]

/-- **The Levinson ratio against `ξ'/ξ`.** For `λ > 0`, `0 < Re s ≤ 2`, `100 ≤ Im s ≤ T` and
`ζ(s) ≠ 0`: `Re(1 + λζ'/ζ) ≥ 1 − λ(½ log(T/2π) + 1/20) + λ Re ξ'/ξ`. -/
theorem re_one_add_logDeriv_riemannZeta_ge {lam T : ℝ} (hlam : 0 < lam) {s : ℂ}
    (h0 : 0 < s.re) (h2 : s.re ≤ 2) (ht : 100 ≤ s.im) (hT : s.im ≤ T)
    (hζ : riemannZeta s ≠ 0) :
    1 - lam * (Real.log (T / (2 * Real.pi)) / 2 + 1 / 20) + lam * (logDeriv xi s).re ≤
      (1 + (lam : ℂ) * logDeriv riemannZeta s).re := by
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_im] at ht; linarith
  obtain ⟨-, hsplit⟩ := logDeriv_xi_eq_archFactor_add_of_re_pos h0 hs1 hζ
  have hA := re_logDeriv_archFactor_le_of_re_le_two h0 h2 ht
  have hlogT : Real.log (s.im / (2 * Real.pi)) ≤ Real.log (T / (2 * Real.pi)) :=
    Real.log_le_log (div_pos (by linarith) (by positivity)) (by gcongr)
  have hA' : (logDeriv archFactor s).re ≤ Real.log (T / (2 * Real.pi)) / 2 + 1 / 20 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hA' hlam.le
  have e : logDeriv riemannZeta s = logDeriv xi s - logDeriv archFactor s := by
    rw [hsplit]; ring
  have hre : (1 + (lam : ℂ) * logDeriv riemannZeta s).re =
      1 + lam * (logDeriv xi s).re - lam * (logDeriv archFactor s).re := by
    rw [e]; simp; ring
  rw [hre]
  linarith

/-- `(s − 1)² ζ(s)`, extended to an entire function. -/
def zetaSqCleared (s : ℂ) : ℂ := (s - 1) * zetaEntire s

theorem differentiable_zetaSqCleared : Differentiable ℂ zetaSqCleared := by
  have h := differentiable_zetaEntire
  unfold zetaSqCleared
  fun_prop

theorem analyticOnNhd_zetaSqCleared : AnalyticOnNhd ℂ zetaSqCleared Set.univ :=
  differentiable_zetaSqCleared.differentiableOn.analyticOnNhd isOpen_univ

theorem zetaSqCleared_eq {s : ℂ} (hs : s ≠ 1) :
    zetaSqCleared s = (s - 1) ^ 2 * riemannZeta s := by
  rw [zetaSqCleared, zetaEntire_eq hs]; ring

/-- On `Re s > 0`, `s ≠ 1`, `(s − 1)²ζ` and `ξ` vanish to the same order. -/
theorem analyticOrderAt_zetaSqCleared_eq_xi {w : ℂ} (h0 : 0 < w.re) (h1 : w ≠ 1) :
    analyticOrderAt zetaSqCleared w = analyticOrderAt xi w := by
  have hA0 := archFactor_ne_zero_of_re_pos h0 h1
  have hAA := analyticAt_archFactor_of_re_pos h0
  set k : ℂ → ℂ := fun s => (s - 1) ^ 2 / archFactor s with hk
  have hkA : AnalyticAt ℂ k w :=
    (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ 2) w).div hAA hA0
  have hk0 : k w ≠ 0 := div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr h1)) hA0
  have hev : zetaSqCleared =ᶠ[𝓝 w] k * xi := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).inter
      isOpen_ne).mem_nhds (show w ∈ {z : ℂ | 0 < z.re ∧ z ≠ 1} from ⟨h0, h1⟩)] with s hs
    have hsre : 0 < s.re := hs.1
    have hs1 : s ≠ 1 := hs.2
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hsre; exact lt_irrefl 0 hsre
    have hAs := archFactor_ne_zero_of_re_pos hsre hs1
    simp only [Pi.mul_apply, hk]
    rw [zetaSqCleared_eq hs1,
      xi_eq_archFactor_mul_zeta hs0 hs1 (Complex.Gammaℝ_ne_zero_of_re_pos hsre)]
    field_simp
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hkA (xi_analyticOnNhd_univ w trivial),
    (analyticOrderAt_eq_zero (f := k) (z₀ := w)).mpr (Or.inr hk0), zero_add]

/-- The boundary relation for the entire detector `(s − 1)²(ζ + λζ')` against `(s − 1)²ζ`, with
`g = −(1 + λζ'/ζ)`. -/
theorem ratioLeftBoundary_levinsonGEntire {lam : ℝ} {z : ℂ} (hz1 : z ≠ 1)
    (hζ : riemannZeta z ≠ 0) (hpos : 0 < (1 + (lam : ℂ) * logDeriv riemannZeta z).re) :
    RatioLeftBoundary (levinsonGEntire (lam : ℂ)) zetaSqCleared
      (fun w => -(1 + (lam : ℂ) * logDeriv riemannZeta w)) z := by
  have hq0 : (1 + (lam : ℂ) * logDeriv riemannZeta z) ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hpos; exact lt_irrefl 0 hpos
  have hZA : AnalyticAt ℂ riemannZeta z :=
    DifferentiableOn.analyticAt (s := {w : ℂ | w ≠ 1})
      (fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
      (isOpen_ne.mem_nhds hz1)
  have hqA : AnalyticAt ℂ (fun w => 1 + (lam : ℂ) * logDeriv riemannZeta w) z :=
    analyticAt_const.add (analyticAt_const.mul (hZA.deriv.div hZA hζ))
  have hF₀ : zetaSqCleared z ≠ 0 := by
    rw [zetaSqCleared_eq hz1]; exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hz1)) hζ
  have hmul : ∀ w : ℂ, w ≠ 1 → riemannZeta w ≠ 0 → levinsonGEntire (lam : ℂ) w =
      zetaSqCleared w * (1 + (lam : ℂ) * logDeriv riemannZeta w) := by
    intro w hw hζw
    rw [levinsonGEntire_eq _ hw, zetaSqCleared_eq hw, levinsonG, logDeriv_apply]
    field_simp
  refine ⟨by rw [hmul z hz1 hζ]; exact mul_ne_zero hF₀ hq0, hF₀, hqA.neg,
    by simp only [Complex.neg_re]; linarith, ?_⟩
  have hev : levinsonGEntire (lam : ℂ) =ᶠ[𝓝 z]
      fun w => zetaSqCleared w * (1 + (lam : ℂ) * logDeriv riemannZeta w) := by
    filter_upwards [isOpen_ne.mem_nhds hz1, hZA.continuousAt.eventually_ne hζ] with w hw hζw
    exact hmul w hw hζw
  rw [logDeriv_eq_of_germ_eq hev,
    logDeriv_mul z hF₀ hq0 (differentiable_zetaSqCleared z) hqA.differentiableAt,
    logDeriv_neg_fun (fun w => 1 + (lam : ℂ) * logDeriv riemannZeta w)]
  ring

/-- **Levinson's detector counts exactly the off-line zeros.** For `λ > 0` with
`λ(½ log(T₂/2π) + 1/20) < 1` and unshadowed heights `100 ≤ T₁ < T₂`, `ζ + λζ'` and `ξ` have the
same number of zeros, with multiplicity, in `1/2 < Re s < 2`, `T₁ < Im s < T₂`. -/
theorem exists_levinsonG_count_right {lam T₁ T₂ : ℝ} (hlam : 0 < lam)
    (hlamT : lam * (Real.log (T₂ / (2 * Real.pi)) / 2 + 1 / 20) < 1)
    (h100 : 100 ≤ T₁) (hT : T₁ < T₂) (hu₁ : SpeiserUnshadowed T₁)
    (hu₂ : SpeiserUnshadowed T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ w : ℂ, w ∈ Z₁ ↔ rightHalfWindow T₁ T₂ w ∧ levinsonG (lam : ℂ) w = 0) ∧
      (∀ w : ℂ, w ∈ Z₀ ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0) ∧
      ∑ w ∈ Z₁, (analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat =
        ∑ w ∈ Z₀, (analyticOrderAt xi w).toNat := by
  classical
  set c₀ : ℝ := 1 - lam * (Real.log (T₂ / (2 * Real.pi)) / 2 + 1 / 20) with hc₀
  have hc₀0 : 0 < c₀ := by linarith
  -- the boundary condition from a lower bound on `Re ξ'/ξ`
  have hgood : ∀ s : ℂ, 0 < s.re → s.re ≤ 2 → T₁ ≤ s.im → s.im ≤ T₂ → xi s ≠ 0 →
      -(c₀ / lam) < (logDeriv xi s).re →
      RatioLeftBoundary (levinsonGEntire (lam : ℂ)) zetaSqCleared
        (fun w => -(1 + (lam : ℂ) * logDeriv riemannZeta w)) s := by
    intro s h0 h2 h3 h4 hxi hlow
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_im] at h3; linarith
    have hζ : riemannZeta s ≠ 0 := fun h =>
      hxi ((xi_eq_zero_iff_riemannZeta_of_re_pos h0 hs1).mpr h)
    have hge := re_one_add_logDeriv_riemannZeta_ge hlam h0 h2 (by linarith) h4 hζ
    have hm : lam * (-(c₀ / lam)) = -c₀ := by field_simp
    have hlow' : -c₀ < lam * (logDeriv xi s).re := by
      rw [← hm]; exact mul_lt_mul_of_pos_left hlow hlam
    exact ratioLeftBoundary_levinsonGEntire hs1 hζ (by rw [← hc₀] at hge; linarith)
  -- horizontal edges at unshadowed heights and the edge `Re s = 2`
  have hhor : ∀ T : ℝ, SpeiserUnshadowed T → ∀ x : ℝ, 1 / 2 < x →
      xi ((x : ℂ) + T * I) ≠ 0 ∧ 0 < (logDeriv xi ((x : ℂ) + T * I)).re := by
    intro T hu x hx
    have hre : ((x : ℂ) + T * I).re = x := by simp
    have him : ((x : ℂ) + T * I).im = T := by simp
    have hxi := xi_ne_zero_of_speiserUnshadowed (x := x) hu (ne_of_gt hx)
    refine ⟨hxi, re_logDeriv_xi_pos_of_disk_bound (by rw [hre]; exact hx) hxi fun q => ?_⟩
    have h1 := hu (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)
    rw [hre, him]
    have h2 : 0 < (x - 1 / 2) ^ 2 := by
      have : x - 1 / 2 ≠ 0 := by linarith
      positivity
    linarith
  have hneg : -(c₀ / lam) < 0 := by
    have : 0 < c₀ / lam := div_pos hc₀0 hlam
    linarith
  obtain ⟨δ₀, hδ₀, hedge⟩ := exists_xi_right_edge_re_logDeriv_gt (ε := c₀ / lam)
    (div_pos hc₀0 hlam) hT.le
  -- finitely many zeros of both entire functions in `[1/2, 2] × [T₁, T₂]`
  set V := levinsonGEntire (lam : ℂ) with hV
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hnV : ∃ z : ℂ, V z ≠ 0 := exists_levinsonGEntire_ne_zero hlamC
  have hnX : ∃ z : ℂ, zetaSqCleared z ≠ 0 := by
    refine ⟨2, ?_⟩
    rw [zetaSqCleared_eq (by norm_num)]
    exact mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  set b₁ : ℂ := ((1 / 2 : ℝ) : ℂ) + T₁ * I with hb₁
  set b₂ : ℂ := ((2 : ℝ) : ℂ) + T₂ * I with hb₂
  have hb : b₁.re = 1 / 2 ∧ b₂.re = 2 ∧ b₁.im = T₁ ∧ b₂.im = T₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hb₁, hb₂]
  have hfinV := entire_zeros_closedRectangle_finite (analyticOnNhd_levinsonGEntire _) hnV b₁ b₂
  have hfinX := entire_zeros_closedRectangle_finite analyticOnNhd_zetaSqCleared hnX b₁ b₂
  set W : Finset ℂ := (hfinV.toFinset ∪ hfinX.toFinset).filter (fun w => 1 / 2 < w.re) with hW
  obtain ⟨η₂, hη₂, hη₂le⟩ := exists_pos_le_of_finset W (fun w => w.re - 1 / 2)
    (fun w hw => by have := (Finset.mem_filter.mp hw).2; show 0 < w.re - 1 / 2; linarith)
  have hinW : ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 2 → T₁ ≤ w.im → w.im ≤ T₂ →
      (V w = 0 ∨ zetaSqCleared w = 0) → w ∈ W := by
    intro w h1 h2 h3 h4 hz
    have hbox : w ∈ (uIcc b₁.re b₂.re ×ℂ uIcc b₁.im b₂.im) := by
      rw [Complex.mem_reProdIm, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, uIcc_of_le (by norm_num),
        uIcc_of_le hT.le]
      exact ⟨⟨h1.le, h2⟩, ⟨h3, h4⟩⟩
    refine Finset.mem_filter.mpr ⟨?_, h1⟩
    rcases hz with hz | hz
    · exact Finset.mem_union_left _ (hfinV.mem_toFinset.mpr ⟨hbox, hz⟩)
    · exact Finset.mem_union_right _ (hfinX.mem_toFinset.mpr ⟨hbox, hz⟩)
  set δ : ℝ := min (min δ₀ η₂) (1 / 4) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδδ₀ : δ < δ₀ := by
    have := min_le_left (min δ₀ η₂) (1 / 4); have := min_le_left δ₀ η₂; linarith
  have hδη : δ < η₂ := by
    have := min_le_left (min δ₀ η₂) (1 / 4); have := min_le_right δ₀ η₂; linarith
  have hδ8 : δ ≤ 1 / 8 := by have := min_le_right (min δ₀ η₂) (1 / 4); linarith
  set c : ℝ := 1 / 2 + δ with hc
  have hc2 : c < 2 := by linarith
  have hpt : ∀ x t : ℝ, ((x : ℂ) + t * I).re = x ∧ ((x : ℂ) + t * I).im = t := fun x t => by
    constructor <;> simp
  have hedgeB : ∀ x t : ℝ, c ≤ x → x ≤ 2 → T₁ ≤ t → t ≤ T₂ →
      (t = T₁ ∨ t = T₂ ∨ x = 2 ∨ x = c) →
      RatioLeftBoundary V zetaSqCleared (fun w => -(1 + (lam : ℂ) * logDeriv riemannZeta w))
        ((x : ℂ) + t * I) := by
    intro x t hx1 hx2 ht1 ht2 hcase
    obtain ⟨hre, him⟩ := hpt x t
    have h0 : 0 < ((x : ℂ) + t * I).re := by rw [hre]; linarith
    have h2 : ((x : ℂ) + t * I).re ≤ 2 := by rw [hre]; exact hx2
    have h3 : T₁ ≤ ((x : ℂ) + t * I).im := by rw [him]; exact ht1
    have h4 : ((x : ℂ) + t * I).im ≤ T₂ := by rw [him]; exact ht2
    rcases hcase with rfl | rfl | rfl | rfl
    · obtain ⟨a, b⟩ := hhor _ hu₁ x (by linarith)
      exact hgood _ h0 h2 h3 h4 a (by linarith)
    · obtain ⟨a, b⟩ := hhor _ hu₂ x (by linarith)
      exact hgood _ h0 h2 h3 h4 a (by linarith)
    · have hone : (1 : ℝ) ≤ (((2 : ℝ) : ℂ) + t * I).re := by norm_num
      exact hgood _ h0 h2 h3 h4 (xi_ne_zero_of_one_le_re hone)
        (by linarith [re_logDeriv_xi_pos_of_one_le_re hone])
    · obtain ⟨a, b⟩ := hedge δ hδ0 hδδ₀ t ⟨ht1, ht2⟩
      exact hgood _ h0 h2 h3 h4 a b
  obtain ⟨Z₁, Z₀', hZ₁, hZ₀', hsum⟩ := sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg
    (analyticOnNhd_levinsonGEntire _) analyticOnNhd_zetaSqCleared hnV hnX hc2 hT
    (fun x hx => by
      rw [uIcc_of_le hc2.le] at hx
      exact hedgeB x T₁ hx.1 hx.2 le_rfl hT.le (Or.inl rfl))
    (fun x hx => by
      rw [uIcc_of_le hc2.le] at hx
      exact hedgeB x T₂ hx.1 hx.2 hT.le le_rfl (Or.inr (Or.inl rfl)))
    (fun t ht => by
      rw [uIcc_of_le hT.le] at ht
      exact hedgeB 2 t hc2.le le_rfl ht.1 ht.2 (Or.inr (Or.inr (Or.inl rfl))))
    (fun t ht => by
      rw [uIcc_of_le hT.le] at ht
      exact hedgeB c t le_rfl hc2.le ht.1 ht.2 (Or.inr (Or.inr (Or.inr rfl))))
  have hsplit : ∀ w : ℂ, w = (w.re : ℂ) + w.im * I := fun w => (Complex.re_add_im w).symm
  -- boundary points are not zeros
  have hbd : ∀ w : ℂ, w ∈ (uIcc c 2 ×ℂ uIcc T₁ T₂) → (V w = 0 ∨ zetaSqCleared w = 0) →
      rightHalfWindow T₁ T₂ w := by
    intro w hmem hz
    rw [Complex.mem_reProdIm, uIcc_of_le hc2.le, uIcc_of_le hT.le] at hmem
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hmem
    have hkill : (w.im = T₁ ∨ w.im = T₂ ∨ w.re = 2 ∨ w.re = c) → False := by
      intro hcase
      have hR := hedgeB w.re w.im h1 h2 h3 h4 hcase
      rw [← hsplit w] at hR
      rcases hz with hz | hz
      · exact hR.1 hz
      · exact hR.2.1 hz
    refine ⟨?_, lt_of_le_of_ne h2 fun h => hkill (Or.inr (Or.inr (Or.inl h))),
      lt_of_le_of_ne h3 fun h => hkill (Or.inl h.symm),
      lt_of_le_of_ne h4 fun h => hkill (Or.inr (Or.inl h))⟩
    have hc' : c < w.re := lt_of_le_of_ne h1 fun h => hkill (Or.inr (Or.inr (Or.inr h.symm)))
    linarith
  have hinside : ∀ w : ℂ, rightHalfWindow T₁ T₂ w → (V w = 0 ∨ zetaSqCleared w = 0) →
      w ∈ (uIcc c 2 ×ℂ uIcc T₁ T₂) := by
    intro w hw hz
    have hwW := hη₂le w (hinW w hw.1 hw.2.1.le hw.2.2.1.le hw.2.2.2.le hz)
    rw [Complex.mem_reProdIm, uIcc_of_le hc2.le, uIcc_of_le hT.le]
    exact ⟨⟨by linarith, hw.2.1.le⟩, ⟨hw.2.2.1.le, hw.2.2.2.le⟩⟩
  have hw1 : ∀ w : ℂ, rightHalfWindow T₁ T₂ w → w ≠ 1 := fun w hw h => by
    have := hw.2.2.1; rw [h, Complex.one_im] at this; linarith
  have hw0 : ∀ w : ℂ, rightHalfWindow T₁ T₂ w → 0 < w.re := fun w hw => by linarith [hw.1]
  have hX : ∀ w : ℂ, rightHalfWindow T₁ T₂ w → (zetaSqCleared w = 0 ↔ xi w = 0) := by
    intro w hw
    rw [zetaSqCleared_eq (hw1 w hw), mul_eq_zero,
      xi_eq_zero_iff_riemannZeta_of_re_pos (hw0 w hw) (hw1 w hw)]
    simp [sub_ne_zero.mpr (hw1 w hw)]
  have hZ₀mem : ∀ w : ℂ, w ∈ Z₀' ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0 := by
    intro w
    rw [hZ₀' w]
    exact ⟨fun ⟨hm, hz⟩ => have hw := hbd w hm (Or.inr hz); ⟨hw, (hX w hw).mp hz⟩,
      fun ⟨hw, hz⟩ => ⟨hinside w hw (Or.inr ((hX w hw).mpr hz)), (hX w hw).mpr hz⟩⟩
  refine ⟨Z₁, Z₀', fun w => ?_, hZ₀mem, ?_⟩
  · rw [hZ₁ w]
    constructor
    · rintro ⟨hm, hz⟩
      have hw := hbd w hm (Or.inl hz)
      exact ⟨hw, (levinsonGEntire_eq_zero_iff _ (hw1 w hw)).mp hz⟩
    · rintro ⟨hw, hz⟩
      have hz' := (levinsonGEntire_eq_zero_iff _ (hw1 w hw)).mpr hz
      exact ⟨hinside w hw (Or.inl hz'), hz'⟩
  · rw [hsum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hwin := ((hZ₀mem w).mp hw).1
    rw [analyticOrderAt_zetaSqCleared_eq_xi (hw0 w hwin) (hw1 w hwin)]

/-- **Under RH, Levinson's detector has no zeros right of the line** in `1/2 < Re s ≤ 2`,
`100 ≤ Im s ≤ T`, whenever `λ > 0` and `λ(½ log(T/2π) + 1/20) < 1`. -/
theorem levinsonG_ne_zero_right_of_re_zeros (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2)
    {lam T : ℝ} (hlam : 0 < lam) (hlamT : lam * (Real.log (T / (2 * Real.pi)) / 2 + 1 / 20) < 1)
    {s : ℂ} (h1 : 1 / 2 < s.re) (h2 : s.re ≤ 2) (ht : 100 ≤ s.im) (hT : s.im ≤ T) :
    levinsonG (lam : ℂ) s ≠ 0 := by
  have hxi : xi s ≠ 0 := fun h => by have := hRH s h; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_im] at ht; linarith
  have h0 : 0 < s.re := by linarith
  have hζ : riemannZeta s ≠ 0 := fun h =>
    hxi ((xi_eq_zero_iff_riemannZeta_of_re_pos h0 hs1).mpr h)
  have hpos : 0 < (logDeriv xi s).re := re_logDeriv_xi_pos_of_disk_bound h1 hxi fun q => by
    rw [hRH (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1), sub_self, zero_pow two_ne_zero]
    have : s.re - 1 / 2 ≠ 0 := by linarith
    have := pow_pos (abs_pos.mpr this) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (s.im - (q.1 : ℂ).im)]
  have hge := re_one_add_logDeriv_riemannZeta_ge hlam h0 h2 ht hT hζ
  have hq : 0 < (1 + (lam : ℂ) * logDeriv riemannZeta s).re := by nlinarith
  intro h0G
  have heq : levinsonG (lam : ℂ) s = riemannZeta s * (1 + (lam : ℂ) * logDeriv riemannZeta s) := by
    rw [levinsonG, logDeriv_apply]; field_simp
  rw [heq] at h0G
  rcases mul_eq_zero.mp h0G with h | h
  · exact hζ h
  · rw [h, Complex.zero_re] at hq; exact lt_irrefl 0 hq

/-- A point right of the line where `Re ξ'/ξ ≤ 0` lies in the closed Speiser disk of a zero. -/
theorem exists_xi_zero_disk_of_re_logDeriv_nonpos {s : ℂ} (hs : 1 / 2 < s.re)
    (hle : xi s ≠ 0 → (logDeriv xi s).re ≤ 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  by_cases hxi : xi s = 0
  · exact ⟨s, hxi, by simp⟩
  by_contra hno
  push Not at hno
  have hpos := re_logDeriv_xi_pos_of_disk_bound hs hxi fun q =>
    hno (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)
  linarith [hle hxi]

/-- **Right zeros of the Hermite–Biehler partners lie in Speiser disks.** For `λ > 0`, every zero
of `ξ + λξ'` with `Re s > 1/2` lies in the closed Speiser disk of a zero of `ξ`. -/
theorem exists_xi_zero_disk_of_xiHermiteBiehler_eq_zero {lam : ℝ} (hlam : 0 < lam) {s : ℂ}
    (hs : 1 / 2 < s.re) (hV : xiHermiteBiehler lam s = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  refine exists_xi_zero_disk_of_re_logDeriv_nonpos hs fun hxi => ?_
  rw [xiHermiteBiehler_eq_mul hxi] at hV
  have hq := (mul_eq_zero.mp hV).resolve_left hxi
  have hre := congrArg Complex.re hq
  have e : (1 + (lam : ℂ) * logDeriv xi s).re = 1 + lam * (logDeriv xi s).re := by simp
  rw [e, Complex.zero_re] at hre
  nlinarith

/-- **Right zeros of Levinson's detector lie in Speiser disks.** For `λ > 0` with
`λ(½ log(T/2π) + 1/20) < 1`, every zero of `ζ + λζ'` with `1/2 < Re s ≤ 2`, `100 ≤ Im s ≤ T`
lies in the closed Speiser disk of a zero of `ξ`. -/
theorem exists_xi_zero_disk_of_levinsonG_eq_zero {lam T : ℝ} (hlam : 0 < lam)
    (hlamT : lam * (Real.log (T / (2 * Real.pi)) / 2 + 1 / 20) < 1) {s : ℂ}
    (h1 : 1 / 2 < s.re) (h2 : s.re ≤ 2) (ht : 100 ≤ s.im) (hT : s.im ≤ T)
    (hG : levinsonG (lam : ℂ) s = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  refine exists_xi_zero_disk_of_re_logDeriv_nonpos h1 fun hxi => ?_
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_im] at ht; linarith
  have h0 : 0 < s.re := by linarith
  have hζ : riemannZeta s ≠ 0 := fun h =>
    hxi ((xi_eq_zero_iff_riemannZeta_of_re_pos h0 hs1).mpr h)
  have hge := re_one_add_logDeriv_riemannZeta_ge hlam h0 h2 ht hT hζ
  have heq : levinsonG (lam : ℂ) s =
      riemannZeta s * (1 + (lam : ℂ) * logDeriv riemannZeta s) := by
    rw [levinsonG, logDeriv_apply]; field_simp
  rw [heq] at hG
  have hq := (mul_eq_zero.mp hG).resolve_left hζ
  rw [hq, Complex.zero_re] at hge
  nlinarith

end

end RHTower
