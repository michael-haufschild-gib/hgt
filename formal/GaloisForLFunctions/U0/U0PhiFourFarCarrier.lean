/-
# The far carrier for the `b = 4` window: `p(annW)` beyond the Böttcher far bound

The dyadic pullback chain (`U0PhiFourWindow.phiFour_pow_iterate`) connects the window branch
`phiFour` on the annulus `annW = {1 < ‖z‖ < 21/20}` to the genuine Böttcher coordinate at the
image of the polynomial map `pMap m = f^[m] ∘ f` (`f = quadratic 4`).  This file constructs the
far carrier that the far transcendence theorem (`Bottcher.bottcher_transcendental_far`) consumes:

* `zero_not_mem_filledJulia_four` — `c = 4` is an escape parameter (critical orbit `0 ↦ 4 ↦ 20`);
* `pMap m` is analytic with nowhere-vanishing derivative on `annW` (the chain-rule factors are
  far-field iterates, hence nonzero), so `pMap m '' annW` is **open**;
* the image is preconnected, nonempty, and infinite;
* `exists_far_carrier` — for `m` large the image clears `bottcherFarBound 4` (escape growth
  `farW_growth` + archimedean choice of `m`).
-/
import GaloisForLFunctions.U0.U0PhiFourWindow
import GaloisForLFunctions.Bottcher.BottcherTowerData

open Complex Set Metric Polynomial Bottcher U0NaturalBoundary U0PhiFourWindow

namespace U0PhiFourFarCarrier

/-- The window annulus `{1 < ‖z‖ < 21/20}` — the carrier of the `b = 4` capstone. -/
def annW : Set ℂ := Metric.ball (0 : ℂ) (21 / 20) ∩ Ext

theorem isOpen_annW : IsOpen annW := isOpen_ball.inter U0NaturalBoundary.isOpen_Ext

theorem isPreconnected_annW : IsPreconnected annW := isPreconnected_annulus

theorem annW_subset_ball : annW ⊆ Metric.ball (0 : ℂ) (21 / 20) := inter_subset_left

theorem annW_subset_Ext : annW ⊆ Ext := inter_subset_right

theorem annW_nonempty : annW.Nonempty := by
  refine ⟨(41 / 40 : ℂ), ?_, ?_⟩
  · simp only [mem_ball, dist_zero_right]
    rw [show ((41 / 40 : ℂ)) = ((41 / 40 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  · show 1 < ‖(41 / 40 : ℂ)‖
    rw [show ((41 / 40 : ℂ)) = ((41 / 40 : ℝ) : ℂ) by norm_num, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num

/-- A nonempty open subset of `ℂ` is infinite (it contains a real segment). -/
theorem infinite_of_isOpen_nonempty {S : Set ℂ} (hSo : IsOpen S) (hSne : S.Nonempty) :
    S.Infinite := by
  obtain ⟨z₀, hz₀⟩ := hSne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSo z₀ hz₀
  have himg : (fun t : ℝ => z₀ + (t : ℂ)) '' (Ioo 0 (ε / 2)) ⊆ S := by
    rintro w ⟨t, ⟨ht0, ht1⟩, rfl⟩
    apply hball
    rw [mem_ball, dist_eq_norm]
    have : z₀ + (t : ℂ) - z₀ = (t : ℂ) := by ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    linarith
  have hIoo : (Ioo (0 : ℝ) (ε / 2)).Infinite := Set.Ioo_infinite (by linarith)
  have hinj : InjOn (fun t : ℝ => z₀ + (t : ℂ)) (Ioo 0 (ε / 2)) := by
    intro a _ b _ hab
    have h1 : (a : ℂ) = (b : ℂ) := by
      have := congrArg (fun w : ℂ => w - z₀) hab
      simpa using this
    exact_mod_cast h1
  exact (hIoo.image hinj).mono himg

theorem annW_infinite : annW.Infinite :=
  infinite_of_isOpen_nonempty isOpen_annW annW_nonempty

/-- **`c = 4` is an escape parameter**: the critical orbit `0 ↦ 4 ↦ 20` leaves every bound. -/
theorem zero_not_mem_filledJulia_four : (0 : ℂ) ∉ filledJulia 4 := by
  intro h0
  have h2 : (quadratic 4)^[2] (0 : ℂ) ∈ filledJulia 4 := filledJulia_forward h0 2
  have hval : (quadratic 4)^[2] (0 : ℂ) = 20 := by
    have h1 : (quadratic 4)^[2] (0 : ℂ) = quadratic 4 ((quadratic 4)^[1] (0 : ℂ)) := by
      rw [Function.iterate_succ_apply']
    rw [h1, Function.iterate_one]
    simp only [quadratic_apply]
    norm_num
  rw [hval] at h2
  have h4 : ‖(4 : ℂ)‖ ≤ ‖(20 : ℂ)‖ := by
    rw [Complex.norm_ofNat, Complex.norm_ofNat]
    norm_num
  have h20 : (2 : ℝ) < ‖(20 : ℂ)‖ := by
    rw [Complex.norm_ofNat]
    norm_num
  exact not_mem_filledJulia h4 h20 h2

/-- The polynomial escape map `pMap m = f^[m] ∘ f` at `c = 4`: one quadratic step into the far
field, then `m` more. -/
noncomputable def pMap (m : ℕ) : ℂ → ℂ := fun z => (quadratic 4)^[m] (quadratic 4 z)

theorem pMap_mem_farW (m : ℕ) {z : ℂ} (hz : z ∈ annW) : pMap m z ∈ farW :=
  farW_iterate m (quadFour_mem_farW (annW_subset_ball hz))

/-- The dyadic pullback chain lands on `pMap`: on the annulus,
`phiFour^(2^(m+1)) = bottcherCoord 4 ∘ pMap m`. -/
theorem phiFour_pow_pMap (m : ℕ) {z : ℂ} (hz : z ∈ annW) :
    phiFour z ^ (2 ^ (m + 1)) = bottcherCoord 4 (pMap m z) :=
  phiFour_pow_iterate (annW_subset_ball hz) m

theorem quadratic_analyticOnNhd_univ : AnalyticOnNhd ℂ (quadratic (4 : ℂ)) univ := by
  have h : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (2 : ℕ) + 4) univ :=
    (analyticOnNhd_id.pow 2).add analyticOnNhd_const
  have he : (quadratic (4 : ℂ)) = fun z : ℂ => z ^ (2 : ℕ) + 4 := by
    funext z; exact quadratic_apply 4 z
  rw [he]
  exact h

theorem pMap_analyticOnNhd (m : ℕ) : AnalyticOnNhd ℂ (pMap m) univ := by
  induction m with
  | zero =>
    have he : pMap 0 = quadratic 4 := by
      funext z; simp [pMap]
    rw [he]
    exact quadratic_analyticOnNhd_univ
  | succ m ih =>
    have he : pMap (m + 1) = (quadratic 4) ∘ (pMap m) := by
      funext z
      simp only [pMap, Function.comp_apply]
      rw [Function.iterate_succ_apply']
    rw [he]
    exact quadratic_analyticOnNhd_univ.comp ih (mapsTo_univ _ _)

/-- The chain-rule derivative of `pMap m` is nonzero on the annulus: the first factor is `2z`
(`z ≠ 0` on `annW`), all later factors are `2·(far-field iterate)` (nonzero on `farW`). -/
theorem pMap_hasDerivAt_ne_zero (m : ℕ) {z : ℂ} (hz : z ∈ annW) :
    ∃ d : ℂ, HasDerivAt (pMap m) d z ∧ d ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ) < ‖z‖ := annW_subset_Ext hz
    rw [h0] at h1
    simp at h1
    linarith
  have hq : HasDerivAt (quadratic (4 : ℂ)) (2 * z) z := by
    have h : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + 4) ((2 : ℕ) * z ^ (2 - 1)) z :=
      (hasDerivAt_pow 2 z).add_const 4
    have he : (quadratic (4 : ℂ)) = fun w : ℂ => w ^ (2 : ℕ) + 4 := by
      funext w; exact quadratic_apply 4 w
    rw [he]
    convert h using 1
    push_cast
    ring
  induction m with
  | zero =>
    refine ⟨2 * z, ?_, by
      intro h
      rcases mul_eq_zero.mp h with h2 | h2
      · norm_num at h2
      · exact hz0 h2⟩
    have he : pMap 0 = quadratic 4 := by
      funext w; simp [pMap]
    rw [he]
    exact hq
  | succ m ih =>
    obtain ⟨d, hd, hdne⟩ := ih
    have hfar : pMap m z ∈ farW := pMap_mem_farW m hz
    have hne : pMap m z ≠ 0 := farW_ne_zero hfar
    have hqm : HasDerivAt (quadratic (4 : ℂ)) (2 * pMap m z) (pMap m z) := by
      have h : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + 4) ((2 : ℕ) * (pMap m z) ^ (2 - 1)) (pMap m z) :=
        (hasDerivAt_pow 2 (pMap m z)).add_const 4
      have he : (quadratic (4 : ℂ)) = fun w : ℂ => w ^ (2 : ℕ) + 4 := by
        funext w; exact quadratic_apply 4 w
      rw [he]
      convert h using 1
      push_cast
      ring
    refine ⟨2 * pMap m z * d, ?_, by
      intro h
      rcases mul_eq_zero.mp h with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact hne h3
      · exact hdne h2⟩
    have he : pMap (m + 1) = (quadratic 4) ∘ (pMap m) := by
      funext w
      simp only [pMap, Function.comp_apply]
      rw [Function.iterate_succ_apply']
    rw [he]
    exact hqm.comp z hd

theorem pMap_deriv_ne_zero (m : ℕ) {z : ℂ} (hz : z ∈ annW) : deriv (pMap m) z ≠ 0 := by
  obtain ⟨d, hd, hdne⟩ := pMap_hasDerivAt_ne_zero m hz
  rw [hd.deriv]
  exact hdne

/-- **The far image is open**: `pMap m` is analytic with nonvanishing derivative on the annulus. -/
theorem isOpen_pMap_image (m : ℕ) : IsOpen (pMap m '' annW) :=
  isOpen_image_of_analytic_dne isOpen_annW ((pMap_analyticOnNhd m).mono (subset_univ _))
    (fun _ hz => pMap_deriv_ne_zero m hz)

theorem isPreconnected_pMap_image (m : ℕ) : IsPreconnected (pMap m '' annW) :=
  isPreconnected_annW.image _ (((pMap_analyticOnNhd m).continuousOn).mono (subset_univ _))

theorem pMap_image_nonempty (m : ℕ) : (pMap m '' annW).Nonempty :=
  Set.Nonempty.image _ annW_nonempty

theorem pMap_image_infinite (m : ℕ) : (pMap m '' annW).Infinite :=
  infinite_of_isOpen_nonempty (isOpen_pMap_image m) (pMap_image_nonempty m)

/-- **The far carrier exists**: for `m` large enough, the open connected infinite image
`pMap m '' annW` lies entirely beyond the Böttcher far bound of `c = 4`. -/
theorem exists_far_carrier :
    ∃ m : ℕ, ∀ w ∈ pMap m '' annW,
      bottcherFarBound 4 zero_not_mem_filledJulia_four < ‖w‖ := by
  set B : ℝ := bottcherFarBound 4 zero_not_mem_filledJulia_four with hB
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (B / (289 / 100)) (show (1 : ℝ) < 3 / 2 by norm_num)
  refine ⟨m, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  have hqz : quadratic 4 z ∈ farW := quadFour_mem_farW (annW_subset_ball hz)
  have hgrow : (3 / 2 : ℝ) ^ m * ‖quadratic 4 z‖ ≤ ‖pMap m z‖ := farW_growth m hqz
  have hqnorm : (289 / 100 : ℝ) < ‖quadratic 4 z‖ := hqz
  have hpow : (0 : ℝ) < (3 / 2 : ℝ) ^ m := by positivity
  have h1 : B < (3 / 2 : ℝ) ^ m * (289 / 100) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 289 / 100)] at hm
    linarith
  calc B < (3 / 2 : ℝ) ^ m * (289 / 100) := h1
    _ ≤ (3 / 2 : ℝ) ^ m * ‖quadratic 4 z‖ := by nlinarith
    _ ≤ ‖pMap m z‖ := hgrow

end U0PhiFourFarCarrier
