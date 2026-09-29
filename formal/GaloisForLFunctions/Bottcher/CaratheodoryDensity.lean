/-
# The Carathéodory density of a bounded planar domain and strict contraction

For an open `D ⊆ ℂ` and `z ∈ D`, the Carathéodory density is
`κ_D(z) = sup {‖h'(z)‖ : h holomorphic on D, h(D) ⊆ 𝔻, h(z) = 0}`.

* If `D ⊆ ball 0 B` then `1/(2B) ≤ κ_D(z)` (take `h(w) = (w - z)/(2B)`); if `ball z r ⊆ D` then
  `κ_D(z) ≤ 1/r` (Schwarz lemma).
* A holomorphic self-map `F` of `D` does not increase the density: `κ_D(F z)·‖F'(z)‖ ≤ κ_D(z)`,
  since `h ∘ F` competes at `z` whenever `h` competes at `F z`.
* **Strict contraction.**  If `g` maps `D` into a compact `L ⊆ D`, then for small `ε > 0` the map
  `F = g + ε(g - g(z))` still maps `D` into `D`, agrees with `g` at `z` and has derivative
  `(1 + ε) g'(z)` there; hence `κ_D(g z)·(1 + ε)·‖g'(z)‖ ≤ κ_D(z)`, with `ε` depending only on
  `D` and `L`.
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.MetricSpace.Thickening

open Complex Set Metric

namespace Bottcher

/-- The competitors for the Carathéodory density of `D` at `z`. -/
def caraSet (D : Set ℂ) (z : ℂ) : Set ℝ :=
  {r | ∃ h : ℂ → ℂ, DifferentiableOn ℂ h D ∧ MapsTo h D (ball 0 1) ∧ h z = 0 ∧ r = ‖deriv h z‖}

/-- The Carathéodory density `κ_D(z)`. -/
noncomputable def caraDensity (D : Set ℂ) (z : ℂ) : ℝ := sSup (caraSet D z)

section

variable {D : Set ℂ} {z : ℂ}

theorem caraSet_bddAbove (hDo : IsOpen D) (hz : z ∈ D) : BddAbove (caraSet D z) := by
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hDo z hz
  refine ⟨1 / r, ?_⟩
  rintro _ ⟨h, hd, hmaps, hz0, rfl⟩
  have := norm_deriv_le_div_of_mapsTo_ball (hd.mono hrD)
    (fun w hw => by rw [hz0]; exact ball_subset_closedBall (hmaps (hrD hw))) hr
  simpa using this

theorem caraSet_nonempty {B : ℝ} (hB : 0 < B) (hDB : D ⊆ ball 0 B) (hz : z ∈ D) :
    (caraSet D z).Nonempty := by
  refine ⟨‖deriv (fun w => (w - z) / (2 * B)) z‖, fun w => (w - z) / (2 * B),
    (by fun_prop : Differentiable ℂ fun w : ℂ => (w - z) / (2 * B)).differentiableOn, ?_, by simp,
    rfl⟩
  intro w hw
  have hwB := mem_ball_zero_iff.mp (hDB hw)
  have hzB := mem_ball_zero_iff.mp (hDB hz)
  rw [mem_ball_zero_iff, norm_div]
  have h2B : ‖(2 * B : ℂ)‖ = 2 * B := by
    rw [show (2 * B : ℂ) = ((2 * B : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2B, div_lt_one (by positivity)]
  calc ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
    _ < 2 * B := by linarith

theorem caraDensity_nonneg (D : Set ℂ) (z : ℂ) : 0 ≤ caraDensity D z := by
  apply Real.sSup_nonneg
  rintro _ ⟨h, -, -, -, rfl⟩
  exact norm_nonneg _

theorem norm_deriv_le_caraDensity (hDo : IsOpen D) (hz : z ∈ D) {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h D) (hmaps : MapsTo h D (ball 0 1)) (hz0 : h z = 0) :
    ‖deriv h z‖ ≤ caraDensity D z :=
  le_csSup (caraSet_bddAbove hDo hz) ⟨h, hd, hmaps, hz0, rfl⟩

/-- **Upper bound** by the Schwarz lemma. -/
theorem caraDensity_le {B : ℝ} (hB : 0 < B) (hDB : D ⊆ ball 0 B) {r : ℝ} (hr : 0 < r)
    (hrD : ball z r ⊆ D) : caraDensity D z ≤ 1 / r := by
  have hz : z ∈ D := hrD (mem_ball_self hr)
  apply csSup_le (caraSet_nonempty hB hDB hz)
  rintro _ ⟨h, hd, hmaps, hz0, rfl⟩
  have := norm_deriv_le_div_of_mapsTo_ball (hd.mono hrD)
    (fun w hw => by rw [hz0]; exact ball_subset_closedBall (hmaps (hrD hw))) hr
  simpa using this

/-- **Lower bound** from the size of `D`. -/
theorem le_caraDensity (hDo : IsOpen D) {B : ℝ} (hB : 0 < B) (hDB : D ⊆ ball 0 B) (hz : z ∈ D) :
    1 / (2 * B) ≤ caraDensity D z := by
  have hmaps : MapsTo (fun w => (w - z) / (2 * B)) D (ball 0 1) := by
    intro w hw
    have hwB := mem_ball_zero_iff.mp (hDB hw)
    have hzB := mem_ball_zero_iff.mp (hDB hz)
    rw [mem_ball_zero_iff, norm_div]
    have h2B : ‖(2 * B : ℂ)‖ = 2 * B := by
      rw [show (2 * B : ℂ) = ((2 * B : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2B, div_lt_one (by positivity)]
    calc ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
      _ < 2 * B := by linarith
  have h := norm_deriv_le_caraDensity hDo hz
    (by fun_prop : Differentiable ℂ fun w : ℂ => (w - z) / (2 * B)).differentiableOn hmaps
    (by simp)
  have hd : deriv (fun w : ℂ => (w - z) / (2 * B)) z = 1 / (2 * B) := by
    have h' : HasDerivAt (fun w : ℂ => (w - z) / (2 * B)) (1 / (2 * B)) z := by
      simpa using ((hasDerivAt_id z).sub_const z).div_const (2 * (B : ℂ))
    exact h'.deriv
  rw [hd] at h
  have h2B : ‖(1 / (2 * B) : ℂ)‖ = 1 / (2 * B) := by
    rw [show (1 / (2 * B) : ℂ) = ((1 / (2 * B) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rwa [h2B] at h

/-- **Holomorphic self-maps do not increase the density.** -/
theorem caraDensity_mul_norm_deriv_le (hDo : IsOpen D) {B : ℝ} (hB : 0 < B) (hDB : D ⊆ ball 0 B)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D) (hFD : MapsTo F D D) (hz : z ∈ D) :
    caraDensity D (F z) * ‖deriv F z‖ ≤ caraDensity D z := by
  have hFz : F z ∈ D := hFD hz
  rcases (norm_nonneg (deriv F z)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact caraDensity_nonneg D z
  rw [← le_div_iff₀ hpos]
  apply csSup_le (caraSet_nonempty hB hDB hFz)
  rintro _ ⟨h, hd, hmaps, hz0, rfl⟩
  rw [le_div_iff₀ hpos]
  have hcomp := norm_deriv_le_caraDensity hDo hz (hd.comp hF hFD) (hmaps.comp hFD)
    (by simp [hz0])
  rwa [deriv_comp z (hd.differentiableAt (hDo.mem_nhds hFz))
    (hF.differentiableAt (hDo.mem_nhds hz)), norm_mul] at hcomp

/-- **Strict contraction** of maps into a compact subset. -/
theorem exists_strict_caraDensity_contraction (hDo : IsOpen D) {B : ℝ} (hB : 0 < B)
    (hDB : D ⊆ ball 0 B) {L : Set ℂ} (hL : IsCompact L) (hLD : L ⊆ D) :
    ∃ ε > 0, ∀ g : ℂ → ℂ, DifferentiableOn ℂ g D → MapsTo g D L → ∀ z ∈ D,
      caraDensity D (g z) * ((1 + ε) * ‖deriv g z‖) ≤ caraDensity D z := by
  obtain ⟨δ, hδ, hδD⟩ := hL.exists_cthickening_subset_open hDo hLD
  obtain ⟨d, hd⟩ : ∃ d, ∀ x ∈ L, ‖x‖ ≤ d := hL.isBounded.exists_norm_le
  set d' := max d 0 with hd'def
  have hd'0 : 0 ≤ d' := le_max_right _ _
  set ε : ℝ := δ / (2 * (2 * d' + 1)) with hεdef
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, fun g hg hgL z hz => ?_⟩
  set F : ℂ → ℂ := fun w => g w + (ε : ℂ) * (g w - g z) with hFdef
  have hFd : DifferentiableOn ℂ F D := hg.add ((hg.sub_const (g z)).const_mul _)
  have hFD : MapsTo F D D := by
    intro w hw
    apply hδD
    apply mem_cthickening_of_dist_le (F w) (g w) δ L (hgL hw)
    rw [dist_eq_norm, hFdef]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε]
    have h1 : ‖g w - g z‖ ≤ 2 * d' := by
      calc ‖g w - g z‖ ≤ ‖g w‖ + ‖g z‖ := norm_sub_le _ _
        _ ≤ d' + d' := add_le_add ((hd _ (hgL hw)).trans (le_max_left _ _))
            ((hd _ (hgL hz)).trans (le_max_left _ _))
        _ = 2 * d' := by ring
    calc ε * ‖g w - g z‖ ≤ ε * (2 * d' + 1) := by
          apply mul_le_mul_of_nonneg_left _ hε.le; linarith
      _ = δ / 2 := by rw [hεdef]; field_simp
      _ ≤ δ := by linarith
  have hFz : F z = g z := by simp [hFdef]
  have hFderiv : deriv F z = (1 + ε) * deriv g z := by
    have hgd : HasDerivAt g (deriv g z) z := (hg.differentiableAt (hDo.mem_nhds hz)).hasDerivAt
    have h' : HasDerivAt F ((1 + ε) * deriv g z) z :=
      (hgd.add ((hgd.sub_const (g z)).const_mul (ε : ℂ))).congr_deriv (by ring)
    exact h'.deriv
  have key := caraDensity_mul_norm_deriv_le hDo hB hDB hFd hFD hz
  rw [hFz, hFderiv, norm_mul] at key
  have h1ε : ‖((1 : ℂ) + ε)‖ = 1 + ε := by
    rw [show ((1 : ℂ) + ε) = ((1 + ε : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rwa [h1ε] at key

end

end Bottcher
