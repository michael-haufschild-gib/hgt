import GaloisForLFunctions.ZeroConfigurationGeometry.TheZetaDensityBackgroundHasBoundedTrace
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheMinimalFaceCounterexampleHasZeroRelativeDensity

/-!
# Zeta density does not remove the minimal-face obstruction

Add the critical projection of the zeta divisor to the sparse
minimal-face tower. The leading ordinate density becomes zeta's,
while the bounded background trace preserves the arbitrarily high
floors on growing sub-logarithmic windows.
-/

open Complex Filter Topology Set
noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open SquareRootThreshold Zeta23 SurfaceOfSpecZ.ScaleLocality
open _root_.RHTower.LocalCountFalsifier

/-- The sparse off-line tower together with the exact critical zeta background. -/
def densityMatchedMinimalFace (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) : ZeroConfig :=
  superpose (minimalFaceCounterConfig γ_min C hΘ hΘ2) zetaDensityBackground

theorem minimalFace_offLine (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∀ ρ ∈ (minimalFaceCounterConfig γ_min C hΘ hΘ2).carrier, ρ.re ≠ 1 / 2 := by
  rintro _ ⟨⟨k, ⟨d, b, s⟩⟩, rfl⟩ he
  have hd := SplineTower.depth_pos hΘ k
  cases s
  · rw [facePt_false_re] at he
    linarith only [hd, he]
  · rw [facePt_true_re] at he
    linarith only [hd, he]

/-- The added critical background preserves temperedness. -/
theorem densityMatchedMinimalFace_tempered (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    TemperedConfig (densityMatchedMinimalFace γ_min C hΘ hΘ2) :=
  temperedConfig_superpose
    (disjoint_zetaDensityBackground_of_offLine (minimalFace_offLine γ_min C hΘ hΘ2))
    (temperedConfig_minimalFaceCounterConfig γ_min C hΘ hΘ2) zetaDensityBackground_tempered

/-- Both components retain a fixed gap around the real axis. -/
theorem densityMatchedMinimalFace_ordinate_gap (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∀ ρ ∈ (densityMatchedMinimalFace γ_min C hΘ hΘ2).carrier, 4 ≤ |ρ.im| := by
  intro ρ hρ
  rcases hρ with hρ | hρ
  · obtain ⟨idx, rfl⟩ := hρ
    have h := (facePt_im_bounds γ_min C Θ idx).1
    have hΓ : (4 : ℝ) ≤ faceBaseFreq γ_min C Θ idx.1 := by
      exact_mod_cast four_le_faceBaseFreq γ_min C Θ idx.1
    exact (hΓ.trans h.le).trans (le_abs_self _)
  · exact zetaDensityBackground_ordinate_gap ρ hρ

/-- Adding the background preserves a logarithmic local count bound. -/
theorem densityMatchedMinimalFace_localCount (γ_min : ℝ) {C Θ : ℝ}
    (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ,
      ((densityMatchedMinimalFace γ_min C hΘ hΘ2).N t (t + 1) : ℝ) ≤
        A * Real.log (|t| + 3) := by
  obtain ⟨A, hA, hcount⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨C + A, by linarith only [hC, hA], fun t => ?_⟩
  rw [densityMatchedMinimalFace, N_add_zetaDensityBackground, Nat.cast_add, add_mul]
  exact add_le_add (localCount_minimalFaceCounterConfig γ_min hC hΘ hΘ2 t) (hcount t)

/-- Exact counts differ from zeta's by `o(T log T)`. -/
theorem densityMatchedMinimalFace_counts (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T →
      |((densityMatchedMinimalFace γ_min C hΘ hΘ2).N 0 T : ℝ) -
        (zetaZeroConfig.N 0 T : ℝ)| ≤ ε * T * Real.log T := by
  obtain ⟨U, hU⟩ := minimalFace_count_small_relative_to_T_log_T γ_min C hΘ hΘ2 hε
  refine ⟨U, fun T hT => ?_⟩
  rw [densityMatchedMinimalFace, N_add_zetaDensityBackground, Nat.cast_add,
    add_sub_cancel_right, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hU T hT

/-- The top remains unattained, and its exact supremum is unchanged. -/
theorem densityMatchedMinimalFace_top (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    (∀ ρ ∈ (densityMatchedMinimalFace γ_min C hΘ hΘ2).carrier, ρ.re < 1 / 2 + Θ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ ∈ (densityMatchedMinimalFace γ_min C hΘ hΘ2).carrier,
        1 / 2 + Θ - ε < ρ.re := by
  constructor
  · intro ρ hρ
    rcases hρ with hρ | hρ
    · exact re_lt_half_add_minimalFaceCounterConfig γ_min C hΘ hΘ2 hρ
    · rw [criticalProjectionConfig_onLine zetaZeroConfig ρ hρ]
      linarith only [hΘ]
  · intro ε hε
    obtain ⟨ρ, hρ, hre⟩ := exists_re_gt_half_add_sub_minimalFaceCounterConfig γ_min C hΘ hΘ2 hε
    exact ⟨ρ, Or.inl hρ, hre⟩

/-- The background changes the cubic-spline trace by a fixed bounded amount. -/
theorem densityMatchedMinimalFace_trace (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (u : ℝ) :
    ‖lagStructure (densityMatchedMinimalFace γ_min C hΘ hΘ2) (boxSpline 1 3) u -
      lagStructure (minimalFaceCounterConfig γ_min C hΘ hΘ2) (boxSpline 1 3) u‖ ≤
        (lagStructure zetaDensityBackground (boxSpline 1 3) 0).re := by
  apply trace_sub_le_add_zetaDensityBackground
    (temperedConfig_minimalFaceCounterConfig γ_min C hΘ hΘ2)
    (minimalFace_offLine γ_min C hΘ hΘ2) (contDiff_boxSpline one_pos 2) (w := 4)
  intro v hv
  have h := boxSpline_support one_pos 3 v hv
  norm_num at h
  exact h

/-- Every fixed floor survives on arbitrarily late windows with the same growing radius. -/
theorem densityMatchedMinimalFace_windows (γ_min C : ℝ) {Θ : ℝ}
    (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (K U : ℝ) :
    ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ, |u - T| ≤ minimalFaceSubLogRadius γ_min C Θ T →
      K ≤ 2 * (lagStructure (densityMatchedMinimalFace γ_min C hΘ hΘ2) (boxSpline 1 3) u).re := by
  let B : ℝ := (lagStructure zetaDensityBackground (boxSpline 1 3) 0).re
  let k : ℕ := max ⌈max (K + 2 * B) 0⌉₊ ⌈max U 0⌉₊
  refine ⟨(winCenter γ_min C Θ (k + 1) : ℝ), ?_, fun u hu => ?_⟩
  · have hU : U ≤ (⌈max U 0⌉₊ : ℝ) := (le_max_left U 0).trans (Nat.le_ceil _)
    have hk : ⌈max U 0⌉₊ ≤ k := le_max_right _ _
    have hcenter := k_le_winCenter γ_min C Θ (k + 1)
    have hn : (⌈max U 0⌉₊ : ℝ) ≤ (winCenter γ_min C Θ (k + 1) : ℝ) := by
      exact_mod_cast hk.trans (by omega : k ≤ winCenter γ_min C Θ (k + 1))
    exact hU.trans hn
  · rw [minimalFaceSubLogRadius_winCenter] at hu
    have hfloor := k_add_one_le_two_re_lagStructure_on_window γ_min C hΘ hΘ2 k hu
    have hK : K + 2 * B ≤ (⌈max (K + 2 * B) 0⌉₊ : ℝ) :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    have hk : (⌈max (K + 2 * B) 0⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_left _ _
    have hnorm := densityMatchedMinimalFace_trace γ_min C hΘ hΘ2 u
    have habs := (Complex.abs_re_le_norm
      (lagStructure (densityMatchedMinimalFace γ_min C hΘ hΘ2) (boxSpline 1 3) u -
        lagStructure (minimalFaceCounterConfig γ_min C hΘ hΘ2) (boxSpline 1 3) u)).trans hnorm
    rw [Complex.sub_re] at habs
    have hlower := (abs_le.mp habs).1
    push_cast at hfloor
    nlinarith only [hfloor, hK, hk, hlower]

/-- Zeta-density configurations retain the complete sub-logarithmic obstruction. -/
theorem exists_zetaDensity_subLog_counterexample {Θ : ℝ} (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    ∃ (Z : ZeroConfig) (R : ℝ → ℝ), TemperedConfig Z ∧
      (∀ ρ ∈ Z.carrier, 4 ≤ |ρ.im|) ∧
      (∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ U : ℝ, ∀ T : ℝ, U ≤ T →
        |(Z.N 0 T : ℝ) - (zetaZeroConfig.N 0 T : ℝ)| ≤ ε * T * Real.log T) ∧
      (∀ ρ ∈ Z.carrier, ρ.re < 1 / 2 + Θ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ ρ ∈ Z.carrier, 1 / 2 + Θ - ε < ρ.re) ∧
      Monotone R ∧ Tendsto R atTop atTop ∧
      Tendsto (fun T => R T / Real.log T) atTop (𝓝 0) ∧
      ∀ K U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ, |u - T| ≤ R T →
        K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  exact ⟨densityMatchedMinimalFace 1 1 hΘ hΘ2, minimalFaceSubLogRadius 1 1 Θ,
    densityMatchedMinimalFace_tempered 1 1 hΘ hΘ2,
    densityMatchedMinimalFace_ordinate_gap 1 1 hΘ hΘ2,
    densityMatchedMinimalFace_localCount 1 zero_lt_one hΘ hΘ2,
    fun _ hε => densityMatchedMinimalFace_counts 1 1 hΘ hΘ2 hε,
    (densityMatchedMinimalFace_top 1 1 hΘ hΘ2).1,
    (densityMatchedMinimalFace_top 1 1 hΘ hΘ2).2,
    monotone_minimalFaceSubLogRadius 1 1 Θ, tendsto_minimalFaceSubLogRadius_atTop 1 1 Θ,
    tendsto_minimalFaceSubLogRadius_div_log 1 1 Θ,
    densityMatchedMinimalFace_windows 1 1 hΘ hΘ2⟩

#print axioms exists_zetaDensity_subLog_counterexample
#print axioms densityMatchedMinimalFace_trace

end GaloisForLFunctions.ZeroConfigurationGeometry
