/-
# The connected half of all-nonexceptional U0--Bottcher independence

For `b \in mandelbrot \ {0,-2}`, the global single-valued Böttcher branch is already
unconditional.  This file supplies the missing geometry needed to feed that branch to the U0
circle-window engine: an explicitly aligned unit-circle point has an outward radial ray contained
in the basin.  The unbounded component of the exterior basin therefore meets both the unit circle
and the canonical far carrier `escapeOpen b`.
-/
import GaloisForLFunctions.U0.U0AllNonexceptional
import GaloisForLFunctions.U0.U0PhiLargeCapstone
import GaloisForLFunctions.U0.U0MonotoneEscape
import GaloisForLFunctions.Bottcher.BottcherNotRational
import GaloisForLFunctions.Bottcher.ConnectedBranchMandelbrot
import GaloisForLFunctions.Bottcher.ConnectedTranscendenceUnconditional

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0NaturalBoundary U0MeroCarrier U0WindowNormalization U0PhiLargeCapstone
open U0MonotoneEscape

namespace U0AllNonexceptional

/-- The radial comparison orbit starts strictly above the larger fixed point as soon as the
parameter norm is positive. -/
theorem xStar_lt_add_one {B : ℝ} (hB : 0 < B) : xStar B < B + 1 := by
  have hright : 0 < 2 * B + 1 := by linarith
  have hsqrt : Real.sqrt (1 + 4 * B) < 2 * B + 1 := by
    rw [Real.sqrt_lt' hright]
    nlinarith [sq_pos_of_pos hB]
  rw [xStar]
  linarith

/-- Real lower comparison for a quadratic orbit.  If the initial complex norm dominates `t` and
`t` is above the larger fixed point of `s \mapsto s^(2 : ℕ)-B`, then every complex iterate dominates the
corresponding real comparison iterate. -/
theorem real_iterate_le_norm_quadratic_iterate {b w : ℂ} {t : ℝ}
    (hb : b ≠ 0) (ht : xStar ‖b‖ ≤ t) (htw : t ≤ ‖w‖) (n : ℕ) :
    (fun s : ℝ => s ^ (2 : ℕ) - ‖b‖)^[n] t ≤ ‖(quadratic b)^[n] w‖ := by
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  induction n with
  | zero => simpa using htw
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hreal : t ≤ (fun s : ℝ => s ^ (2 : ℕ) - ‖b‖)^[n] t := by
        have h := iterate_linear_growth (B := ‖b‖) (t := t) hB ht n
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hdelta : (0 : ℝ) ≤ t - xStar ‖b‖ := sub_nonneg.mpr ht
        exact le_trans (by nlinarith [mul_nonneg hn0 hdelta]) h
      have hreal0 : 0 ≤ (fun s : ℝ => s ^ (2 : ℕ) - ‖b‖)^[n] t := by
        have hx : 1 < xStar ‖b‖ := one_lt_xStar hB
        linarith
      have hrev : ‖(quadratic b)^[n] w‖ ^ (2 : ℕ) - ‖b‖ ≤
          ‖quadratic b ((quadratic b)^[n] w)‖ := by
        have h := norm_sub_norm_le (((quadratic b)^[n] w) ^ (2 : ℕ)) (-b)
        rw [norm_neg, sub_neg_eq_add, norm_pow] at h
        exact h
      have hsq : (fun s : ℝ => s ^ (2 : ℕ) - ‖b‖)^[n] t ^ (2 : ℕ) ≤
          ‖(quadratic b)^[n] w‖ ^ (2 : ℕ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ih)
          (add_nonneg (norm_nonneg ((quadratic b)^[n] w)) hreal0)]
      exact le_trans (sub_le_sub_right hsq _) hrev

/-- A point whose norm is strictly above `xStar ‖b‖` escapes the quadratic filled Julia set. -/
theorem not_mem_filledJulia_of_xStar_lt {b w : ℂ} (hb : b ≠ 0)
    (hw : xStar ‖b‖ < ‖w‖) : w ∉ filledJulia b := by
  rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le]
  push Not
  intro C
  obtain ⟨n, hn⟩ := exists_iterate_gt (B := ‖b‖) (t := ‖w‖)
    (norm_pos_iff.mpr hb) hw C
  refine ⟨(quadratic b)^[n] w, ⟨n, rfl⟩, lt_of_lt_of_le hn ?_⟩
  exact real_iterate_le_norm_quadratic_iterate hb hw.le (le_refl _) n

/-- For a nonzero parameter, choose a unit vector `z` whose square points in the parameter
direction.  Every outward radial multiple of `z` lies in the basin. -/
theorem exists_aligned_unit_radial_escape {b : ℂ} (hb : b ≠ 0) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ t : ℝ, 1 ≤ t → (t : ℂ) * z ∉ filledJulia b := by
  let B : ℝ := ‖b‖
  let u : ℂ := b / (B : ℂ)
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hBpos : 0 < B := by simpa [B] using hbnorm
  have hbnormC : (B : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hBpos)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hBpos]
    simpa [B] using div_self hbnorm.ne'
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ (2 : ℕ) = u :=
    IsAlgClosed.exists_pow_nat_eq u (by norm_num)
  have hznorm : ‖z‖ = 1 := by
    have h := congrArg norm hz
    rw [norm_pow, hu] at h
    nlinarith [norm_nonneg z]
  refine ⟨z, hznorm, ?_⟩
  intro t ht
  have hc : b = (B : ℂ) * u := by
    dsimp [u]
    field_simp
  have hq : quadratic b ((t : ℂ) * z) = ((t ^ (2 : ℕ) + B : ℝ) : ℂ) * u := by
    rw [quadratic_apply, mul_pow, hz]
    nth_rewrite 1 [hc]
    push_cast
    ring
  have hqnorm : ‖quadratic b ((t : ℂ) * z)‖ = t ^ (2 : ℕ) + ‖b‖ := by
    rw [hq, norm_mul, hu, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hstart : xStar ‖b‖ < ‖quadratic b ((t : ℂ) * z)‖ := by
    rw [hqnorm]
    have hx := xStar_lt_add_one hbnorm
    nlinarith
  exact (mem_filledJulia_iff_quadratic_mem b ((t : ℂ) * z)).not.mpr
    (not_mem_filledJulia_of_xStar_lt hb hstart)

/-- A connected window joining the canonical far carrier to an aligned unit-circle point.  Its
exterior part is exactly one connected component of the exterior basin, so relations propagate
from `escapeOpen b` to the circle-window lens. -/
theorem exists_connected_far_circle_window {b : ℂ} (hb : b ≠ 0) :
    ∃ (z₀ : ℂ) (Ω : Set ℂ),
      IsOpen Ω ∧ IsPreconnected Ω ∧ IsPreconnected (Ω ∩ U0NaturalBoundary.Ext) ∧
      z₀ ∈ Ω ∧ ‖z₀‖ = 1 ∧ Ω ⊆ (filledJulia b)ᶜ ∧
      escapeOpen b ⊆ Ω ∩ U0NaturalBoundary.Ext := by
  obtain ⟨z₀, hz₀norm, hzradial⟩ := exists_aligned_unit_radial_escape hb
  have hz₀basin : z₀ ∈ (filledJulia b)ᶜ := by
    simpa using hzradial 1 (le_refl 1)
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia b).isOpen_compl z₀ hz₀basin
  let r : ℝ := min r₀ (1 / 2)
  have hrpos : 0 < r := lt_min hr₀pos (by norm_num)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrhalf : r ≤ 1 / 2 := min_le_right _ _
  have hballbasin : ball z₀ r ⊆ (filledJulia b)ᶜ :=
    (ball_subset_ball hrr₀).trans hr₀sub
  let a : ℝ := 1 + r / 2
  let w₀ : ℂ := (a : ℂ) * z₀
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hw₀norm : ‖w₀‖ = a := by
    dsimp [w₀]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hz₀norm, mul_one]
  have hw₀ball : w₀ ∈ ball z₀ r := by
    rw [mem_ball, dist_eq_norm]
    dsimp [w₀]
    have heq : (a : ℂ) * z₀ - z₀ = ((r / 2 : ℝ) : ℂ) * z₀ := by
      dsimp [a]
      push_cast
      ring
    rw [heq, norm_mul, hz₀norm, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hw₀Ext : w₀ ∈ U0NaturalBoundary.Ext := by
    show 1 < ‖w₀‖
    rw [hw₀norm]
    exact ha1
  let S : Set ℂ := (filledJulia b)ᶜ ∩ U0NaturalBoundary.Ext
  have hSo : IsOpen S := (isClosed_filledJulia b).isOpen_compl.inter isOpen_Ext
  have hw₀S : w₀ ∈ S := ⟨hballbasin hw₀ball, hw₀Ext⟩
  let W : Set ℂ := connectedComponentIn S w₀
  have hWo : IsOpen W := hSo.connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWsubS : W ⊆ S := connectedComponentIn_subset S w₀
  have hw₀W : w₀ ∈ W := mem_connectedComponentIn hw₀S
  have hlens : IsPreconnected (ball z₀ r ∩ U0NaturalBoundary.Ext) := by
    rw [inter_comm]
    exact U0Transcendence.lens_preconnected z₀ hz₀norm hrpos hrhalf
  have hlensS : ball z₀ r ∩ U0NaturalBoundary.Ext ⊆ S := by
    rintro z ⟨hzball, hzExt⟩
    exact ⟨hballbasin hzball, hzExt⟩
  have hw₀lens : w₀ ∈ ball z₀ r ∩ U0NaturalBoundary.Ext := ⟨hw₀ball, hw₀Ext⟩
  have hlensW : ball z₀ r ∩ U0NaturalBoundary.Ext ⊆ W := by
    simpa [W] using hlens.subset_connectedComponentIn hw₀lens hlensS
  let T : ℝ := max 2 ‖b‖ + 2
  have haT : a ≤ T := by
    have hmax : (2 : ℝ) ≤ max 2 ‖b‖ := le_max_left _ _
    dsimp [a, T]
    linarith
  let ray : Set ℂ := (fun t : ℝ => (t : ℂ) * z₀) '' Set.Icc a T
  have hrayc : IsPreconnected ray := by
    exact isPreconnected_Icc.image _ (by fun_prop)
  have hrayS : ray ⊆ S := by
    rintro z ⟨t, ht, rfl⟩
    have ht1 : 1 ≤ t := le_trans ha1.le ht.1
    have htnorm : ‖(t : ℂ) * z₀‖ = t := by
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one (lt_of_lt_of_le ha1 ht.1)),
        hz₀norm, mul_one]
    refine ⟨hzradial t ht1, ?_⟩
    show 1 < ‖(t : ℂ) * z₀‖
    rw [htnorm]
    exact lt_of_lt_of_le ha1 ht.1
  have hw₀ray : w₀ ∈ ray := ⟨a, ⟨le_refl _, haT⟩, rfl⟩
  have hrayW : ray ⊆ W := by
    simpa [W] using hrayc.subset_connectedComponentIn hw₀ray hrayS
  let wfar : ℂ := (T : ℂ) * z₀
  have hwfarRay : wfar ∈ ray := ⟨T, ⟨haT, le_refl _⟩, rfl⟩
  have hwfarW : wfar ∈ W := hrayW hwfarRay
  have hTpos : 0 < T := by
    have hmax : (2 : ℝ) ≤ max 2 ‖b‖ := le_max_left _ _
    dsimp [T]
    linarith
  have hwfarNorm : ‖wfar‖ = T := by
    dsimp [wfar]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hTpos, hz₀norm, mul_one]
  have hwfarEsc : wfar ∈ escapeOpen b := by
    show max 2 ‖b‖ < ‖wfar‖
    rw [hwfarNorm]
    dsimp [T]
    linarith
  have hEscS : escapeOpen b ⊆ S := by
    intro z hz
    exact ⟨escapeOpen_subset_compl_filledJulia b hz,
      U0CardTheorems.escapeOpen_subset_U0Ext b hz⟩
  have hWEscPre : IsPreconnected (W ∪ escapeOpen b) :=
    hWc.union wfar hwfarW hwfarEsc (isConnected_escapeOpen b).isPreconnected
  have hWEscSubS : W ∪ escapeOpen b ⊆ S := union_subset hWsubS hEscS
  have hEscW : escapeOpen b ⊆ W := by
    have hsub : W ∪ escapeOpen b ⊆ W := by
      simpa [W] using hWEscPre.subset_connectedComponentIn (Or.inl hw₀W) hWEscSubS
    exact fun z hz => hsub (Or.inr hz)
  let Ω : Set ℂ := W ∪ ball z₀ r
  have hΩo : IsOpen Ω := hWo.union isOpen_ball
  have hΩc : IsPreconnected Ω :=
    hWc.union w₀ hw₀W hw₀ball (convex_ball z₀ r).isPreconnected
  have hΩExt : Ω ∩ U0NaturalBoundary.Ext = W := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzΩ, hzExt⟩
      rcases hzΩ with hzW | hzball
      · exact hzW
      · exact hlensW ⟨hzball, hzExt⟩
    · intro z hzW
      exact ⟨Or.inl hzW, (hWsubS hzW).2⟩
  have hΩbasin : Ω ⊆ (filledJulia b)ᶜ := by
    rintro z (hzW | hzball)
    · exact (hWsubS hzW).1
    · exact hballbasin hzball
  refine ⟨z₀, Ω, hΩo, hΩc, ?_, ?_, hz₀norm, hΩbasin, ?_⟩
  · rw [hΩExt]
    exact hWc
  · exact Or.inr (mem_ball_self hrpos)
  · intro z hz
    rw [hΩExt]
    exact hEscW hz

/-- **Connected all-parameter card, unconditional.**  For every connected nonexceptional quadratic
parameter, the actual canonical far Böttcher germ is algebraically independent from `u₀`.  The
global branch and its far-field normalization are theorems; the aligned radial window above supplies
the missing passage from the far relation to the unit-circle natural-boundary engine. -/
theorem u0_phi_independence_connected_canonical (b : ℂ) (hbM : b ∈ mandelbrot)
    (hb0 : b ≠ 0) (hb2 : b ≠ (-2 : ℂ)) : CanonicalPhiU0IndependenceAt b := by
  obtain ⟨β, hβan, hβesc, _hβne, _hβmod, _hβrest⟩ :=
    exists_global_branch_covering_bijective_of_mem_mandelbrot b hbM
  obtain ⟨z₀, Ω, hΩo, hΩc, hDc, hz₀Ω, hz₀norm, hΩbasin, hEscD⟩ :=
    exists_connected_far_circle_window hb0
  have hβΩ : AnalyticOnNhd ℂ β Ω := hβan.mono hΩbasin
  let U : Set ℂ := escapeOpen b
  have hUo : IsOpen U := isOpen_escapeOpen b
  have hUc : IsPreconnected U := (isConnected_escapeOpen b).isPreconnected
  have hUne : U.Nonempty := (isConnected_escapeOpen b).nonempty
  have hUinf : U.Infinite := BottcherNotRational.escapeOpen_infinite b
  have hUExt : U ⊆ U0NaturalBoundary.Ext := U0CardTheorems.escapeOpen_subset_U0Ext b
  have hUesc : U ⊆ escapeOpen b := subset_rfl
  refine ⟨U, hUo, hUc, hUne, hUinf, hUesc, ?_⟩
  refine u0_window_independence_of_transcendental_engine hUo hUc hUne hUinf hUExt
    (bottcherCoord b) (phiAnalytic b hUesc) rfl ?_ ?_
  · exact phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf
      hbM hb0 hb2 hUesc
  · intro P' j₀ hj₀ hnd hrel
    have hndβ : ∃ z ∈ Ω ∩ U0NaturalBoundary.Ext,
        coeffFun β (P'.coeff j₀) z ≠ 0 := by
      obtain ⟨z, hzU, hz⟩ := hnd
      refine ⟨z, hEscD hzU, ?_⟩
      simpa only [coeffFun, hβesc z hzU] using hz
    refine u0_windowed_no_relation_nondegenerate hΩo hΩc hDc hβΩ
      hz₀Ω hz₀norm P' hj₀ hndβ hUo hUne hEscD ?_
    intro z hzU
    rw [hβesc z hzU]
    exact hrel z hzU

end U0AllNonexceptional
