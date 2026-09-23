/-
# Section-inverse identity below the anchor (mixed-pair wiring, step B4′)

The anchor exports `φ_c ∘ T = id` only beyond the anchor radius `Ra`, which is non-effective
in `c` (it dominates a compactness bound at level `≈ 4h + 1`), while the mixed-pair patch
localization needs the identity at level `4h − ½`.  No explicit anchor is needed: one
`f_c`-step forces every point of Green level above `½(log(‖c‖²+‖c‖)+1) ≈ 2h + ¾` into the
crude escape set, so `φ_c ∘ T` is analytic on the whole sub-annulus above that level and the
identity propagates down from the anchor zone by the identity theorem on the connected
annulus.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionTower
import GaloisForLFunctions.Bottcher.GreenSublevel
import GaloisForLFunctions.Bottcher.TowerSectionRestrict

open Complex Set

namespace Bottcher

/-- **Escape forcing by level.**  Above Green level `½(log(‖c‖²+‖c‖)+1)`, every point is in
the crude escape set: its image has norm at most `‖c‖² + ‖c‖`, so the crude/small-ball
ceiling at the image halves back below the given level. -/
theorem escapeOpen_of_green_gt_halfCeiling {c z : ℂ} (hc4 : (4:ℝ) ≤ ‖c‖)
    (hz : (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2 < greenFunctionDyn c z) :
    z ∈ escapeOpen c := by
  by_contra hcon
  have hmax : max 2 ‖c‖ = ‖c‖ := max_eq_right (by linarith)
  have hznorm : ‖z‖ ≤ ‖c‖ := by
    have h1 : ¬ (max 2 ‖c‖ < ‖z‖) := hcon
    push Not at h1
    rwa [hmax] at h1
  have hfz : ‖quadratic c z‖ ≤ ‖z‖ ^ (2 : ℕ) + ‖c‖ := by
    have h1 : ‖z ^ (2 : ℕ) + c‖ ≤ ‖z ^ (2 : ℕ)‖ + ‖c‖ := norm_add_le _ _
    rw [norm_pow] at h1
    simpa [quadratic] using h1
  have hfzc : ‖quadratic c z‖ ≤ ‖c‖ ^ (2 : ℕ) + ‖c‖ := by
    have h2 : ‖z‖ ^ (2 : ℕ) ≤ ‖c‖ ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg z) hznorm 2
    linarith
  have hGfz : greenFunctionDyn c (quadratic c z) ≤ Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1 := by
    rcases le_or_gt ‖quadratic c z‖ (max 2 ‖c‖) with hcase | hcase
    · have h1 := greenFunctionDyn_le_small (c := c) hcase
      rwa [hmax] at h1
    · have h1 : ‖c‖ ≤ ‖quadratic c z‖ := by
        have := le_max_right 2 ‖c‖
        linarith [hcase.le]
      have h2 : (2:ℝ) < ‖quadratic c z‖ := by
        have := le_max_left 2 ‖c‖
        linarith [hcase]
      have h3 := greenFunctionDyn_le_crude h1 h2
      have h4 : Real.log ‖quadratic c z‖ ≤ Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) := by
        apply Real.log_le_log (by linarith) hfzc
      linarith
  have hdd := greenFunctionDyn_quadratic c z
  rw [hdd] at hGfz
  linarith

/-- **Identity below the anchor.**  If the section inverts the Böttcher coordinate beyond the
anchor radius, it inverts it on the whole sub-annulus above Green level
`½(log(‖c‖²+‖c‖)+1)`: escape forcing makes `φ_c ∘ T` analytic there, and the identity
theorem propagates the far agreement down the connected annulus. -/
theorem sectionInverse_identity_of_level {c : ℂ} {rlo R₀ Ra : ℝ}
    (S : TowerSection c rlo R₀) (hc4 : (4:ℝ) ≤ ‖c‖)
    (hRa1 : 1 < Ra) (hRaR₀ : Ra < R₀)
    (hfar : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w)
    {r₄ : ℝ} (hr₄pos : 0 < r₄)
    (hr₄ : (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2 < Real.log r₄)
    (hr₄lo : rlo ≤ r₄) (hr₄R₀ : r₄ < R₀) :
    ∀ w : ℂ, r₄ < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w := by
  have hlogpos : (0:ℝ) < (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2 := by
    have h1 : (0:ℝ) ≤ Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) := Real.log_nonneg (by nlinarith)
    linarith
  set A₄ : Set ℂ := annulusSet r₄ R₀ with hA₄def
  have hA₄o : IsOpen A₄ := isOpen_annulusSet _ _
  have hA₄conn : IsConnected A₄ := isConnected_annulus hr₄pos hr₄R₀
  -- escape forcing on the sub-annulus
  have hTesc : ∀ w ∈ A₄, S.T w ∈ escapeOpen c := by
    intro w hw
    have hlev := S.level w ⟨lt_of_le_of_lt hr₄lo hw.1, hw.2⟩
    apply escapeOpen_of_green_gt_halfCeiling hc4
    rw [hlev]
    calc (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2 < Real.log r₄ := hr₄
      _ < Real.log ‖w‖ := Real.log_lt_log hr₄pos hw.1
  -- analyticity of the composite on the sub-annulus
  have hφT_an : AnalyticOnNhd ℂ (fun w => bottcherCoord c (S.T w)) A₄ := by
    intro w hw
    have h1 : AnalyticAt ℂ S.T w := S.an w ⟨lt_of_le_of_lt hr₄lo hw.1, hw.2⟩
    have h2 : AnalyticAt ℂ (bottcherCoord c) (S.T w) :=
      (differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c) _ (hTesc w hw)
    exact h2.comp h1
  have hid_an : AnalyticOnNhd ℂ (id : ℂ → ℂ) A₄ := fun w _ => analyticAt_id
  -- the far basepoint and agreement neighborhood
  set s : ℝ := max Ra r₄ with hsdef
  have hsR₀ : s < R₀ := max_lt hRaR₀ hr₄R₀
  have hspos : (0:ℝ) < s := lt_trans zero_lt_one (lt_of_lt_of_le hRa1 (le_max_left _ _))
  have hR₀pos : (0:ℝ) < R₀ := lt_trans (lt_trans zero_lt_one hRa1) hRaR₀
  set w₀ : ℂ := (((s + R₀) / 2 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = (s + R₀) / 2 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hw₀s : s < ‖w₀‖ := by
    rw [hw₀norm]
    linarith
  have hw₀R₀ : ‖w₀‖ < R₀ := by
    rw [hw₀norm]
    linarith
  have hw₀A₄ : w₀ ∈ A₄ := ⟨lt_of_le_of_lt (le_max_right _ _) hw₀s, hw₀R₀⟩
  have hOopen : IsOpen (annulusSet s R₀) := isOpen_annulusSet _ _
  have hev : (fun w => bottcherCoord c (S.T w)) =ᶠ[nhds w₀] (id : ℂ → ℂ) := by
    filter_upwards [hOopen.mem_nhds ⟨hw₀s, hw₀R₀⟩] with w hw
    exact hfar w (lt_of_le_of_lt (le_max_left _ _) hw.1) hw.2
  have heq := hφT_an.eqOn_of_preconnected_of_eventuallyEq hid_an
    hA₄conn.isPreconnected hw₀A₄ hev
  intro w h1 h2
  exact heq ⟨h1, h2⟩

/-- **Pointwise identity below the anchor**: at every single `w` above the ceiling, the
section inverts the Böttcher coordinate (midpoint instantiation of the level form). -/
theorem sectionInverse_identity_at {c : ℂ} {rlo R₀ Ra : ℝ}
    (S : TowerSection c rlo R₀) (hc4 : (4:ℝ) ≤ ‖c‖)
    (hRa1 : 1 < Ra) (hRaR₀ : Ra < R₀)
    (hfar : ∀ w : ℂ, Ra < ‖w‖ → ‖w‖ < R₀ → bottcherCoord c (S.T w) = w)
    (hrlo0 : 0 < rlo)
    (hrlo_ceiling : Real.log rlo ≤ (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2)
    {w : ℂ} (hw_lo : (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2 < Real.log ‖w‖)
    (hwR₀ : ‖w‖ < R₀) :
    bottcherCoord c (S.T w) = w := by
  set ceil : ℝ := (Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) + 1) / 2 with hceildef
  have hwpos : (0:ℝ) < ‖w‖ := by
    by_contra hcon
    push Not at hcon
    have h0 : ‖w‖ = 0 := le_antisymm hcon (norm_nonneg w)
    rw [h0, Real.log_zero] at hw_lo
    have h1 : (0:ℝ) ≤ Real.log (‖c‖ ^ (2 : ℕ) + ‖c‖) := Real.log_nonneg (by nlinarith)
    have h2 : (0:ℝ) < ceil := by rw [hceildef]; linarith
    linarith
  set r₄ : ℝ := Real.exp ((ceil + Real.log ‖w‖) / 2) with hr₄def
  have hr₄pos : (0:ℝ) < r₄ := Real.exp_pos _
  have hlogr₄ : Real.log r₄ = (ceil + Real.log ‖w‖) / 2 := by
    rw [hr₄def, Real.log_exp]
  have h1 : ceil < Real.log r₄ := by
    rw [hlogr₄]
    linarith
  have h2 : r₄ < ‖w‖ := by
    calc r₄ = Real.exp ((ceil + Real.log ‖w‖) / 2) := hr₄def
      _ < Real.exp (Real.log ‖w‖) := Real.exp_lt_exp.mpr (by linarith)
      _ = ‖w‖ := Real.exp_log hwpos
  have h3 : rlo ≤ r₄ := by
    calc rlo = Real.exp (Real.log rlo) := (Real.exp_log hrlo0).symm
      _ ≤ Real.exp (Real.log r₄) := Real.exp_le_exp.mpr (by rw [hlogr₄]; linarith)
      _ = r₄ := Real.exp_log hr₄pos
  exact sectionInverse_identity_of_level S hc4 hRa1 hRaR₀ hfar hr₄pos h1 h3
    (lt_trans h2 hwR₀) w h2 hwR₀

end Bottcher
