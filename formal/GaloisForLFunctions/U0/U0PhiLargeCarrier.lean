/-
# The far carrier at every large parameter, and the exterior Julia geometry

Parameterization of the `b = 4` far carrier (`U0PhiFourFarCarrier`) over `‖b‖ ≥ 5`, plus the
geometry that large parameters buy for free:

* `zero_not_mem_filledJulia_large` — every `‖b‖ > 2` is an escape parameter;
* `filledJulia_exterior` — for `‖b‖ ≥ 4` the WHOLE filled Julia set lies outside the closed unit
  disk (`‖z‖ ≤ 1 ⟹ ‖f²(z)‖ ≥ (‖b‖−1)² − ‖b‖ ≥ ‖b‖ > 2`).  This is the enabling input for
  discharging the `GBExt` clause of the tower certificate: `u₀`'s natural boundary is `|z| = 1`,
  and for large `‖b‖` the tower's dynamical geometry (loops near the Julia set) lives entirely in
  `u₀`'s domain `{|z| > 1}`;
* `pMapB`, its nonvanishing derivative on the annulus, the open/preconnected/nonempty/infinite
  image, and `exists_far_carrier_B` — the carrier consumed by the parameterized descent.
-/
import GaloisForLFunctions.U0.U0PhiLargeWindow
import GaloisForLFunctions.U0.U0PhiFourFarCarrier
import GaloisForLFunctions.Bottcher.BottcherTowerData

open Complex Set Metric Polynomial Bottcher U0NaturalBoundary
open U0PhiLargeWindow U0PhiFourFarCarrier

namespace U0PhiLargeCarrier

/-- **Every `‖b‖ > 2` is an escape parameter**: `b = f_b(0)` itself already satisfies the
geometric escape criterion. -/
theorem zero_not_mem_filledJulia_large {b : ℂ} (hb : 2 < ‖b‖) : (0 : ℂ) ∉ filledJulia b := by
  intro h0
  have h1 : (quadratic b)^[1] (0 : ℂ) ∈ filledJulia b := filledJulia_forward h0 1
  have hval : (quadratic b)^[1] (0 : ℂ) = b := by
    rw [Function.iterate_one]
    show (0 : ℂ) ^ 2 + b = b
    ring
  rw [hval] at h1
  exact not_mem_filledJulia (le_refl ‖b‖) hb h1

/-- **The filled Julia set of a large parameter avoids the closed unit disk.**  For `‖b‖ ≥ 4` and
`‖z‖ ≤ 1`: `‖f(z)‖ ≥ ‖b‖ − 1`, so `‖f²(z)‖ ≥ (‖b‖−1)² − ‖b‖ ≥ ‖b‖ > 2` and the orbit escapes.
Hence every point of `K_b` has modulus `> 1` — the entire tower geometry at large `‖b‖` lives
inside `u₀`'s domain `{|z| > 1}`. -/
theorem filledJulia_exterior {b : ℂ} (hb : 4 ≤ ‖b‖) {z : ℂ} (hz : z ∈ filledJulia b) :
    1 < ‖z‖ := by
  by_contra hle
  push Not at hle
  have hfz : ‖b‖ - 1 ≤ ‖quadratic b z‖ := by
    have htri : ‖b‖ ≤ ‖z ^ 2 + b‖ + ‖z ^ 2‖ := by
      calc ‖b‖ = ‖z ^ 2 + b - z ^ 2‖ := by ring_nf
        _ ≤ ‖z ^ 2 + b‖ + ‖z ^ 2‖ := norm_sub_le _ _
    have hp : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
    show ‖b‖ - 1 ≤ ‖z ^ 2 + b‖
    nlinarith [htri, hle, norm_nonneg z]
  have hffz : ‖b‖ ≤ ‖quadratic b (quadratic b z)‖ ∧ 2 < ‖quadratic b (quadratic b z)‖ := by
    have htri : ‖(quadratic b z) ^ 2‖ ≤ ‖(quadratic b z) ^ 2 + b‖ + ‖b‖ :=
      norm_le_add_norm_add _ _
    have hp : ‖(quadratic b z) ^ 2‖ = ‖quadratic b z‖ ^ 2 := norm_pow _ 2
    have hgoal : ‖b‖ ≤ ‖(quadratic b z) ^ 2 + b‖ := by
      nlinarith [htri, hfz, hb]
    exact ⟨hgoal, by show (2 : ℝ) < ‖(quadratic b z) ^ 2 + b‖; nlinarith [hgoal, hb]⟩
  have h2 : (quadratic b)^[2] z ∈ filledJulia b := filledJulia_forward hz 2
  have hval : (quadratic b)^[2] z = quadratic b (quadratic b z) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [hval] at h2
  exact not_mem_filledJulia hffz.1 hffz.2 h2

/-! ## The parameterized escape map and its far image -/

/-- The escape map at parameter `b`: one step into the far field, then `m` more. -/
noncomputable def pMapB (b : ℂ) (m : ℕ) : ℂ → ℂ := fun z => (quadratic b)^[m] (quadratic b z)

theorem pMapB_mem_farB {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) {z : ℂ} (hz : z ∈ annW) :
    pMapB b m z ∈ farB b :=
  farB_iterate hb m (quadB_mem_farB hb (annW_subset_ball hz))

/-- The dyadic pullback chain lands on `pMapB`. -/
theorem phiB_pow_pMapB {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) {z : ℂ} (hz : z ∈ annW) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b (pMapB b m z) :=
  phiB_pow_iterate hb (annW_subset_ball hz) m

theorem quadratic_analyticOnNhd_univ_B (b : ℂ) : AnalyticOnNhd ℂ (quadratic b) univ := by
  have h : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2 + b) univ :=
    (analyticOnNhd_id.pow 2).add analyticOnNhd_const
  have he : (quadratic b) = fun z : ℂ => z ^ 2 + b := by
    funext z; exact quadratic_apply b z
  rw [he]
  exact h

theorem pMapB_analyticOnNhd (b : ℂ) (m : ℕ) : AnalyticOnNhd ℂ (pMapB b m) univ := by
  induction m with
  | zero =>
    have he : pMapB b 0 = quadratic b := by
      funext z; simp [pMapB]
    rw [he]
    exact quadratic_analyticOnNhd_univ_B b
  | succ m ih =>
    have he : pMapB b (m + 1) = (quadratic b) ∘ (pMapB b m) := by
      funext z
      simp only [pMapB, Function.comp_apply]
      rw [Function.iterate_succ_apply']
    rw [he]
    exact (quadratic_analyticOnNhd_univ_B b).comp ih (mapsTo_univ _ _)

/-- The chain-rule derivative of `pMapB` is nonzero on the annulus. -/
theorem pMapB_hasDerivAt_ne_zero {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) {z : ℂ} (hz : z ∈ annW) :
    ∃ d : ℂ, HasDerivAt (pMapB b m) d z ∧ d ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ) < ‖z‖ := annW_subset_Ext hz
    rw [h0] at h1
    simp at h1
    linarith
  have hq : HasDerivAt (quadratic b) (2 * z) z := by
    have h : HasDerivAt (fun w : ℂ => w ^ 2 + b) ((2 : ℕ) * z ^ (2 - 1)) z :=
      (hasDerivAt_pow 2 z).add_const b
    have he : (quadratic b) = fun w : ℂ => w ^ 2 + b := by
      funext w; exact quadratic_apply b w
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
    have he : pMapB b 0 = quadratic b := by
      funext w; simp [pMapB]
    rw [he]
    exact hq
  | succ m ih =>
    obtain ⟨d, hd, hdne⟩ := ih
    have hfar : pMapB b m z ∈ farB b := pMapB_mem_farB hb m hz
    have hne : pMapB b m z ≠ 0 := farB_ne_zero hb hfar
    have hqm : HasDerivAt (quadratic b) (2 * pMapB b m z) (pMapB b m z) := by
      have h : HasDerivAt (fun w : ℂ => w ^ 2 + b) ((2 : ℕ) * (pMapB b m z) ^ (2 - 1))
          (pMapB b m z) := (hasDerivAt_pow 2 (pMapB b m z)).add_const b
      have he : (quadratic b) = fun w : ℂ => w ^ 2 + b := by
        funext w; exact quadratic_apply b w
      rw [he]
      convert h using 1
      push_cast
      ring
    refine ⟨2 * pMapB b m z * d, ?_, by
      intro h
      rcases mul_eq_zero.mp h with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact hne h3
      · exact hdne h2⟩
    have he : pMapB b (m + 1) = (quadratic b) ∘ (pMapB b m) := by
      funext w
      simp only [pMapB, Function.comp_apply]
      rw [Function.iterate_succ_apply']
    rw [he]
    exact hqm.comp z hd

theorem pMapB_deriv_ne_zero {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) {z : ℂ} (hz : z ∈ annW) :
    deriv (pMapB b m) z ≠ 0 := by
  obtain ⟨d, hd, hdne⟩ := pMapB_hasDerivAt_ne_zero hb m hz
  rw [hd.deriv]
  exact hdne

theorem isOpen_pMapB_image {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) : IsOpen (pMapB b m '' annW) :=
  isOpen_image_of_analytic_dne isOpen_annW ((pMapB_analyticOnNhd b m).mono (subset_univ _))
    (fun _ hz => pMapB_deriv_ne_zero hb m hz)

theorem isPreconnected_pMapB_image (b : ℂ) (m : ℕ) : IsPreconnected (pMapB b m '' annW) :=
  isPreconnected_annW.image _ (((pMapB_analyticOnNhd b m).continuousOn).mono (subset_univ _))

theorem pMapB_image_nonempty (b : ℂ) (m : ℕ) : (pMapB b m '' annW).Nonempty :=
  Set.Nonempty.image _ annW_nonempty

theorem pMapB_image_infinite {b : ℂ} (hb : 5 ≤ ‖b‖) (m : ℕ) : (pMapB b m '' annW).Infinite :=
  infinite_of_isOpen_nonempty (isOpen_pMapB_image hb m) (pMapB_image_nonempty b m)

/-- **The far carrier exists at every large parameter**: for `m` large the image clears the
Böttcher far bound of `b`. -/
theorem exists_far_carrier_B {b : ℂ} (hb : 5 ≤ ‖b‖) :
    ∃ m : ℕ, ∀ w ∈ pMapB b m '' annW,
      bottcherFarBound b (zero_not_mem_filledJulia_large (by linarith)) < ‖w‖ := by
  set B : ℝ := bottcherFarBound b (zero_not_mem_filledJulia_large (by linarith)) with hB
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (B / (7 / 2)) (show (1 : ℝ) < 3 / 2 by norm_num)
  refine ⟨m, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  have hqz : quadratic b z ∈ farB b := quadB_mem_farB hb (annW_subset_ball hz)
  have hgrow : (3 / 2 : ℝ) ^ m * ‖quadratic b z‖ ≤ ‖pMapB b m z‖ := farB_growth hb m hqz
  have hqnorm : (7 / 2 : ℝ) ≤ ‖quadratic b z‖ := by
    have h1 : ‖b‖ - 3 / 2 < ‖quadratic b z‖ := hqz
    linarith
  have hpow : (0 : ℝ) < (3 / 2 : ℝ) ^ m := by positivity
  have h1 : B < (3 / 2 : ℝ) ^ m * (7 / 2) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 7 / 2)] at hm
    linarith
  calc B < (3 / 2 : ℝ) ^ m * (7 / 2) := h1
    _ ≤ (3 / 2 : ℝ) ^ m * ‖quadratic b z‖ := by nlinarith
    _ ≤ ‖pMapB b m z‖ := hgrow

end U0PhiLargeCarrier
