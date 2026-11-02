import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.BesselCepstrumEnergy
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.HeckeDefectCorridorAndRHDoorOpener

/-!
# The Bessel–Szegő certificate on centered theta windows and the logarithmic corridor

1. **Centered theta windows** (`centeredThetaWindow`): the zeros of `finiteThetaAmplitude N` in
   `[-1/2, 3/2] × [y₁, y₂]` with their orders form a reflection-closed window whose collision
   polynomial is `centeredThetaDifferencePoly`, and whose exponential sum is the source contour
   integral `centeredThetaExpSum y₁ y₂ N t = (2πi)⁻¹ ∮ e^{t(z-1/2)} (-A_N'/A_N)(z) dz`.
2. **Zero transfer** (`exists_xiZero_near_thetaZero`): on the Burnol window at height `m`, every
   zero of `A_N` lies within `r` of a zero of `ξ` as soon as the theta tail is below
   `c_good e^{-(m+3)} (r/8)^d`, `d` the window's zero count (minimum modulus of the peeled
   cofactor of `ξ`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Centered theta windows -/

/-- Source-pure window exponential sum `(2πi)⁻¹ ∮ e^{t(z-1/2)} (-A_N'/A_N)(z) dz` on
`[-1/2, 3/2] × [y₁, y₂]`. -/
def centeredThetaExpSum (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    _root_.RHTower.rectIntegral
      (fun z => cexp ((t : ℂ) * (z - 1 / 2)) *
        (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z))
      (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂)

private theorem analyticOnNhd_finiteThetaAmplitude (N : ℕ) :
    AnalyticOnNhd ℂ (_root_.RHTower.finiteThetaAmplitude N) Set.univ := fun w _ => by
  have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
    (funext (finiteThetaShellPencil_zero N)).symm
  rw [hfun]
  exact analyticOnNhd_finiteThetaShellPencil N 0 w (Set.mem_univ w)

private theorem finiteThetaAmplitude_order_ne_top (N : ℕ) (w : ℂ) :
    analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w ≠ ⊤ := by
  have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
    (funext (finiteThetaShellPencil_zero N)).symm
  rw [hfun]
  exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ w

private theorem order_toNat_pos_of_zero (N : ℕ) {w : ℂ}
    (hw : _root_.RHTower.finiteThetaAmplitude N w = 0) :
    0 < (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat := by
  have han := analyticOnNhd_finiteThetaAmplitude N w (Set.mem_univ w)
  have hne0 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w ≠ 0 := by
    intro h0
    rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz
    · exact hnot han
    · exact hnz hw
  have hcoe := ENat.coe_toNat (finiteThetaAmplitude_order_ne_top N w)
  by_contra hlt
  have hz : (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat = 0 := by omega
  rw [hz, ENat.coe_zero] at hcoe
  exact hne0 hcoe.symm

/-- The boundary-regular centered theta window as reflection-closed zero data. -/
def centeredThetaWindow {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) t) ≠ 0) :
    ReflectedWindow where
  Z := (eval_centeredThetaDifferencePoly_eq_prod hy N hbdry).choose
  mult w := (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
  mult_pos z hz :=
    order_toNat_pos_of_zero N
      (((eval_centeredThetaDifferencePoly_eq_prod hy N hbdry).choose_spec.1 z).mp hz).2
  refl_mem z hz := by
    have hmem := (eval_centeredThetaDifferencePoly_eq_prod hy N hbdry).choose_spec.1
    obtain ⟨⟨hx1, hx2, hy1, hy2⟩, hz0⟩ := (hmem z).mp hz
    refine (hmem _).mpr ⟨⟨by simp; linarith, by simp; linarith, by simpa using hy1,
      by simpa using hy2⟩, ?_⟩
    rw [finiteThetaAmplitude_one_sub]
    have hconj := finiteThetaAmplitude_conj N z
    rw [hz0] at hconj
    exact star_eq_zero.mp hconj
  refl_mult z _ := congrArg ENat.toNat (analyticOrderAt_finiteThetaAmplitude_one_sub_conj N z)

section CenteredWindow

variable {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
  (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
    (_root_.RHTower.rectangleBoundaryPath
      (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) t) ≠ 0)

theorem mem_centeredThetaWindow_iff (w : ℂ) :
    w ∈ (centeredThetaWindow hy N hbdry).Z ↔
      (-1 / 2 < w.re ∧ w.re < 3 / 2 ∧ y₁ < w.im ∧ w.im < y₂) ∧
        _root_.RHTower.finiteThetaAmplitude N w = 0 :=
  (eval_centeredThetaDifferencePoly_eq_prod hy N hbdry).choose_spec.1 w

theorem centeredThetaWindow_degree :
    (centeredThetaWindow hy N hbdry).degree = centeredThetaWindowDegree y₁ y₂ N :=
  (eval_centeredThetaDifferencePoly_eq_prod hy N hbdry).choose_spec.2.1.symm

theorem eval_centeredThetaDifferencePoly_eq_window (x : ℂ) :
    (centeredThetaDifferencePoly y₁ y₂ N).eval x =
      ∏ z ∈ (centeredThetaWindow hy N hbdry).Z, ∏ w ∈ (centeredThetaWindow hy N hbdry).Z,
        (x - (z - w)) ^ ((centeredThetaWindow hy N hbdry).mult z *
          (centeredThetaWindow hy N hbdry).mult w) :=
  (eval_centeredThetaDifferencePoly_eq_prod hy N hbdry).choose_spec.2.2 x

/-- **Source-pure exponential sum.** The window exponential sum of the centered theta window is
the contour integral `centeredThetaExpSum`. -/
theorem centeredThetaWindow_expSum (t : ℝ) :
    (centeredThetaWindow hy N hbdry).expSum t = centeredThetaExpSum y₁ y₂ N t := by
  have hre_le : (centeredWindowLowerLeft y₁).re ≤ (centeredWindowUpperRight y₂).re := by
    simp; norm_num
  have him_le : (centeredWindowLowerLeft y₁).im ≤ (centeredWindowUpperRight y₂).im := by
    simpa using hy
  obtain ⟨Z', hZ'mem, hsum⟩ := entire_rectIntegral_mul_logDeriv_eq_sum
    (analyticOnNhd_finiteThetaAmplitude N) (finiteThetaAmplitude_order_ne_top N)
    (g := fun z => cexp ((t : ℂ) * (z - 1 / 2)))
    (fun z _ => ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp)) hre_le him_le
    hbdry
  have hZ : Z' = (centeredThetaWindow hy N hbdry).Z := by
    ext w
    rw [hZ'mem, mem_centeredThetaWindow_iff]
    simp
  have hint_eq : (fun z : ℂ => cexp ((t : ℂ) * (z - 1 / 2)) *
      (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)) =
      fun z => cexp ((t : ℂ) * (z - 1 / 2)) * logDeriv (_root_.RHTower.finiteThetaAmplitude N) z := by
    funext z
    rw [logDeriv_apply, _root_.RHTower.deriv_finiteThetaAmplitude]
  unfold centeredThetaExpSum
  rw [hint_eq, hsum, hZ]
  rfl

end CenteredWindow

/-! ## §2 Theta zeros track ξ zeros -/

/-- Every point on the four edges of `[z₁.re, z₂.re] × [z₁.im, z₂.im]` lies on
`rectangleBoundaryPath z₁ z₂`. -/
private lemma exists_boundaryPath_eq_of_edges' {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (_ : z₁.im ≤ z₂.im)
    (hx : z₁.re ≤ z.re ∧ z.re ≤ z₂.re) (hy : z₁.im ≤ z.im ∧ z.im ≤ z₂.im)
    (hedge : z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) :
    ∃ t : ℝ, _root_.RHTower.rectangleBoundaryPath z₁ z₂ t = z := by
  by_cases hy1 : z.im = z₁.im
  · rcases eq_or_lt_of_le hre with hxeq | hxlt
    · refine ⟨0, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_zero, _root_.RHTower.rectangleEdgePath_zero]
      exact Complex.ext (by linarith [hx.1, hx.2]) hy1.symm
    · set τ : ℝ := (z.re - z₁.re) / (4 * (z₂.re - z₁.re))
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
      have hτ_nn : 0 ≤ τ := div_nonneg (by linarith [hx.1]) (by positivity)
      have hτ_le : τ ≤ 1 / 4 := by
        dsimp only [τ]
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.2]
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨hτ_nn, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_pos hτ_le]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero]
        dsimp only [τ]; field_simp [hdx.ne']; ring
      · simp [hy1]
  · have hy1_lt : z₁.im < z.im := lt_of_le_of_ne hy.1 (Ne.symm hy1)
    have hdy : 0 < z₂.im - z₁.im := by linarith [hy.2]
    by_cases hx2 : z.re = z₂.re
    · set τ : ℝ := 1 / 4 + (z.im - z₁.im) / (4 * (z₂.im - z₁.im))
      have hτ_gt : 1 / 4 < τ := by
        dsimp only [τ]
        linarith [div_pos (sub_pos.mpr hy1_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
      have hτ_le : τ ≤ 1 / 2 := by
        dsimp only [τ]
        have h1 : (z.im - z₁.im) / (4 * (z₂.im - z₁.im)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hy.2]
        linarith
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [hx2]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
        dsimp only [τ]; field_simp [hdy.ne']; ring
    · have hx2_lt : z.re < z₂.re := lt_of_le_of_ne hx.2 hx2
      have hdx : 0 < z₂.re - z₁.re := by linarith [hx.1]
      by_cases hy2 : z.im = z₂.im
      · set τ : ℝ := 1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))
        have hτ_gt : 1 / 2 < τ := by
          dsimp only [τ]
          linarith [div_pos (sub_pos.mpr hx2_lt) (by positivity : 0 < 4 * (z₂.re - z₁.re))]
        have hτ_le : τ ≤ 3 / 4 := by
          dsimp only [τ]
          have h1 : (z₂.re - z.re) / (4 * (z₂.re - z₁.re)) ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.1]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (not_le.mpr hτ_gt),
          if_pos hτ_le]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero]
          dsimp only [τ]; field_simp [hdx.ne']; ring
        · simp [hy2]
      · have hy2_lt : z.im < z₂.im := lt_of_le_of_ne hy.2 hy2
        have hx1 : z.re = z₁.re := by
          rcases hedge with h | h | h | h
          · exact h
          · exact absurd h hx2
          · exact absurd h hy1
          · exact absurd h hy2
        set τ : ℝ := 3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))
        have hτ_gt : 3 / 4 < τ := by
          dsimp only [τ]
          linarith [div_pos (sub_pos.mpr hy2_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
        have hτ_lt : τ < 1 := by
          dsimp only [τ]
          have h1 : (z₂.im - z.im) / (4 * (z₂.im - z₁.im)) < 1 / 4 := by
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [hy1_lt]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, hτ_lt⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.mpr hτ_gt)]
        apply Complex.ext
        · simp [hx1]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
          dsimp only [τ]; field_simp [hdy.ne']; ring

/-- **Zero transfer.** On the Burnol window at height `m`, if the theta tail is below
`c_good e^{-(m+3)} (r/8)^d` (`d` = total order of `ξ` on the window), every zero of
`finiteThetaAmplitude N` in the window lies within `r` of a zero of `ξ`: the peeled cofactor of
`ξ` has modulus `≥ c_good e^{-(m+3)}/8^d` by the minimum modulus principle. -/
theorem exists_xiZero_near_thetaZero (m N : ℕ) {r : ℝ} (hr : 0 < r)
    (htail : thetaStripTailBound N < burnolGoodLowerConst * Real.exp (-((m + 3 : ℕ) : ℝ)) *
      (r / 8) ^ (∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat))
    {z : ℂ}
    (hz : -1 / 2 < z.re ∧ z.re < 3 / 2 ∧ burnolUnitLower m < z.im ∧ z.im < burnolUnitUpper m)
    (hzero : _root_.RHTower.finiteThetaAmplitude N z = 0) :
    ∃ w ∈ burnolUnitXiZeros m, ‖z - w‖ ≤ r := by
  by_contra hfar
  simp only [not_exists, not_and, not_le] at hfar
  set c_good : ℝ := burnolGoodLowerConst
  have hc_pos : 0 < c_good := burnolGoodLowerConst_pos
  obtain ⟨hy₁_lo, hy₁_hi, hy₂_lo, hy₂_hi, hspan5⟩ := burnolUnit_coords m
  have hbdry_m := burnolUnit_xi_bdry_ge m
  have hZ_iff := mem_burnolUnitXiZeros_iff m
  set y₁ := burnolUnitLower m
  set y₂ := burnolUnitUpper m
  set Z_m := burnolUnitXiZeros m
  set d := ∑ w ∈ Z_m, (analyticOrderAt _root_.RHTower.xi w).toNat
  obtain ⟨m_ord, h_cof, hh_an, hm_ord_eq, hh_Z_nz, hxi_peel⟩ :=
    _root_.RHTower.exists_finite_peel isOpen_univ (_root_.RHTower.xi_analyticOnNhd Set.univ) Z_m
      (fun w _ => Set.mem_univ w) (fun w _ => _root_.RHTower.xi_orderAt_ne_top w)
  have hh_diff : Differentiable ℂ h_cof := fun z => (hh_an z (Set.mem_univ z)).differentiableAt
  have hd_sum_eq : ∑ w ∈ Z_m, m_ord w = d := Finset.sum_congr rfl hm_ord_eq
  let U_box : Set ℂ := Set.Ioo (-1 / 2 : ℝ) (3 / 2 : ℝ) ×ℂ Set.Ioo y₁ y₂
  have hy_lt : y₁ < y₂ := by linarith [hy₁_hi, hy₂_lo]
  have hre_lt : (-1 / 2 : ℝ) < (3 / 2 : ℝ) := by norm_num
  have hcl_box : closure U_box = Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ) ×ℂ Set.Icc y₁ y₂ := by
    rw [Complex.closure_reProdIm, closure_Ioo hre_lt.ne, closure_Ioo hy_lt.ne]
  have hbdd_box : Bornology.IsBounded U_box := by
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 + |y₁| + |y₂|)) ?_
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre_abs : |z.re| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hz.1.1], hz.1.2.le⟩
    have him_abs : |z.im| ≤ |y₁| + |y₂| :=
      abs_le.mpr ⟨by linarith [hz.2.1, neg_abs_le y₁, abs_nonneg y₂],
                  by linarith [hz.2.2, le_abs_self y₂, abs_nonneg y₁]⟩
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  have hfront_xi : ∀ z ∈ frontier U_box,
      c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤ ‖_root_.RHTower.xi z‖ := by
    intro z hz
    rw [Complex.frontier_reProdIm, closure_Ioo hre_lt.ne, frontier_Ioo hre_lt,
      closure_Ioo hy_lt.ne, frontier_Ioo hy_lt] at hz
    have hmem_edge : (-1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2) ∧ (y₁ ≤ z.im ∧ z.im ≤ y₂) ∧
        (z.re = -1 / 2 ∨ z.re = 3 / 2 ∨ z.im = y₁ ∨ z.im = y₂) := by
      rcases hz with hz1 | hz2
      · simp only [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz1
        rcases hz1.2 with hy_eq | hy_eq
        · exact ⟨hz1.1, ⟨le_of_eq hy_eq.symm, by linarith [hy_lt]⟩, Or.inr (Or.inr (Or.inl hy_eq))⟩
        · exact ⟨hz1.1, ⟨by linarith [hy_lt], le_of_eq hy_eq⟩, Or.inr (Or.inr (Or.inr hy_eq))⟩
      · simp only [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz2
        rcases hz2.1 with hx_eq | hx_eq
        · exact ⟨⟨le_of_eq hx_eq.symm, by linarith [hre_lt]⟩, hz2.2, Or.inl hx_eq⟩
        · exact ⟨⟨by linarith [hre_lt], le_of_eq hx_eq⟩, hz2.2, Or.inr (Or.inl hx_eq)⟩
    obtain ⟨t, ht⟩ := exists_boundaryPath_eq_of_edges'
      (z₁ := centeredWindowLowerLeft y₁) (z₂ := centeredWindowUpperRight y₂)
      (by simp; norm_num) (by simp [hy_lt.le])
      (by simpa using hmem_edge.1) (by simpa using hmem_edge.2.1)
      (by simpa using hmem_edge.2.2)
    rw [← ht]
    exact hbdry_m t
  have hh_cl_nz : ∀ z ∈ closure U_box, h_cof z ≠ 0 := by
    intro z hz h0
    by_cases hzZ : z ∈ Z_m
    · exact hh_Z_nz z hzZ h0
    · have hxi0 : _root_.RHTower.xi z = 0 := by
        rw [hxi_peel z (Set.mem_univ z), h0, mul_zero]
      by_cases hzU : z ∈ U_box
      · rw [Complex.mem_reProdIm] at hzU
        obtain ⟨hr0, hr1⟩ := _root_.RHTower.xi_zero_re_mem_open_unit hxi0
        exact hzZ ((hZ_iff z).mpr ⟨⟨hr0, hr1, hzU.2.1, hzU.2.2⟩, hxi0⟩)
      · have hzF : z ∈ frontier U_box := ⟨hz, fun h_int => hzU (interior_subset h_int)⟩
        have hb := hfront_xi z hzF
        rw [hxi0, norm_zero] at hb
        have : 0 < c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) := by positivity
        linarith
  have hprod_upper : ∀ z ∈ closure U_box, ‖∏ w ∈ Z_m, (z - w) ^ m_ord w‖ ≤ (8 : ℝ) ^ d := by
    intro z hz
    rw [hcl_box, Complex.mem_reProdIm] at hz
    rw [norm_prod]
    have hterm_le : ∀ w ∈ Z_m, ‖(z - w) ^ m_ord w‖ ≤ (8 : ℝ) ^ m_ord w := by
      intro w hw
      rw [norm_pow]
      obtain ⟨⟨hw_r0, hw_r1, hw_y1, hw_y2⟩, _⟩ := (hZ_iff w).mp hw
      have hzw_le : ‖z - w‖ ≤ 8 := by
        have hn := Complex.norm_le_abs_re_add_abs_im (z - w)
        have hre_d : |(z - w).re| ≤ 2 := by
          rw [Complex.sub_re]; exact abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
        have him_d : |(z - w).im| ≤ 5 := by
          rw [Complex.sub_im]; exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
        linarith
      exact pow_le_pow_left₀ (norm_nonneg _) hzw_le _
    calc ∏ w ∈ Z_m, ‖(z - w) ^ m_ord w‖
        ≤ ∏ w ∈ Z_m, (8 : ℝ) ^ m_ord w :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hterm_le
      _ = (8 : ℝ) ^ (∑ w ∈ Z_m, m_ord w) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = (8 : ℝ) ^ d := by rw [hd_sum_eq]
  have hh_inv_dc : DiffContOnCl ℂ (fun z => (h_cof z)⁻¹) U_box :=
    (hh_diff.differentiableOn).inv hh_cl_nz |>.diffContOnCl
  have hh_lower : ∀ z ∈ closure U_box,
      c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) / (8 : ℝ) ^ d ≤ ‖h_cof z‖ := by
    have hfront_inv : ∀ z ∈ frontier U_box,
        ‖(h_cof z)⁻¹‖ ≤ (8 : ℝ) ^ d / (c_good * Real.exp (-((m + 3 : ℕ) : ℝ))) := by
      intro z hzF
      have hzCl : z ∈ closure U_box := hzF.1
      have hxi_ge := hfront_xi z hzF
      have hpeel_norm : ‖_root_.RHTower.xi z‖ ≤ (8 : ℝ) ^ d * ‖h_cof z‖ := by
        rw [hxi_peel z (Set.mem_univ z), norm_mul]
        exact mul_le_mul_of_nonneg_right (hprod_upper z hzCl) (norm_nonneg _)
      have hh_pos : 0 < ‖h_cof z‖ := norm_pos_iff.mpr (hh_cl_nz z hzCl)
      rw [norm_inv, inv_le_comm₀ hh_pos (by positivity), inv_div]
      rw [div_le_iff₀ (by positivity)]
      linarith
    intro z hzCl
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd_box hh_inv_dc hfront_inv hzCl
    have hh_pos : 0 < ‖h_cof z‖ := norm_pos_iff.mpr (hh_cl_nz z hzCl)
    rw [norm_inv] at hmax
    have hflip := (inv_le_comm₀ hh_pos (by positivity)).mp hmax
    rwa [inv_div] at hflip
  -- lower bound for `|ξ(z)|` from the distance of `z` to every window zero of `ξ`
  have hz_cl : z ∈ closure U_box :=
    subset_closure (by rw [Complex.mem_reProdIm]; exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩)
  have hprod_low : r ^ d ≤ ‖∏ w ∈ Z_m, (z - w) ^ m_ord w‖ := by
    rw [norm_prod, ← hd_sum_eq, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun w hw => ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ hr.le (hfar w hw).le _
  have hxi_low : c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) * (r / 8) ^ d ≤ ‖_root_.RHTower.xi z‖ := by
    rw [hxi_peel z (Set.mem_univ z), norm_mul]
    calc c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) * (r / 8) ^ d
        = r ^ d * (c_good * Real.exp (-((m + 3 : ℕ) : ℝ)) / (8 : ℝ) ^ d) := by
          rw [div_pow]; ring
      _ ≤ ‖∏ w ∈ Z_m, (z - w) ^ m_ord w‖ * ‖h_cof z‖ :=
          mul_le_mul hprod_low (hh_lower z hz_cl) (by positivity) (norm_nonneg _)
  have hxi_up : ‖_root_.RHTower.xi z‖ ≤ thetaStripTailBound N := by
    have h := norm_finiteThetaAmplitude_sub_xi_le_strip N (R := 2) (by norm_num)
      (z := z) (abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2.1]⟩)
    rw [hzero, zero_sub, norm_neg] at h
    simpa only [thetaStripTailBound, mul_right_comm] using h
  linarith

/-! ## §3 The logarithmic stage -/

/-- Margin `η = 1 / (4 n)` of the certificate at stage `n = logDoorStage c m`. -/
def logStageMargin (c : ℝ) (m : ℕ) : ℝ :=
  1 / (4 * (logDoorStage c m : ℝ))

private theorem log_le_two_sqrt' {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.mul_self_sqrt hx.le]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  linarith

private theorem log_sq_le_sixteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h1 := log_le_two_sqrt' hs
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← Real.mul_self_sqrt hx0.le]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  have hle : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by linarith
  calc Real.log x ^ 2 ≤ (4 * Real.sqrt (Real.sqrt x)) ^ 2 := pow_le_pow_left₀ hlog_nn hle 2
    _ = 16 * Real.sqrt x := by rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]; ring

theorem six_le_logDoorStage_real (c : ℝ) (m : ℕ) : (6 : ℝ) ≤ (logDoorStage c m : ℝ) := by
  exact_mod_cast six_le_logDoorStage c m

theorem logDoorStage_le (c : ℝ) (hc : 0 < c) (m : ℕ) :
    (logDoorStage c m : ℝ) ≤ c * Real.log ((m + 5 : ℕ) : ℝ) + 7 := by
  have hlog : 0 ≤ Real.log ((m + 5 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 5 by omega))
  unfold logDoorStage
  rw [Nat.cast_max, Nat.cast_ofNat]
  refine max_le (by nlinarith) ?_
  have := Nat.ceil_lt_add_one (show 0 ≤ c * Real.log ((m + 5 : ℕ) : ℝ) by positivity)
  linarith

/-- At the logarithmic stage the theta tail beats the transfer threshold for radius
`r = 1 / (16 n)`, for every prefix `N ≥ doorSqrtPrefix m` and all large `m`. -/
theorem exists_logStage_tail_lt (c : ℝ) (hc : 0 < c) :
    ∃ m₁ : ℕ, ∀ m ≥ m₁, ∀ N ≥ doorSqrtPrefix m,
      thetaStripTailBound N < burnolGoodLowerConst * Real.exp (-((m + 3 : ℕ) : ℝ)) *
        ((1 / (16 * (logDoorStage c m : ℝ))) / 8) ^
          (∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat) := by
  set C₀ : ℝ := _root_.RHTower.thetaCuspIntegerTailConstant * _root_.RHTower.thetaAmplitudeEnvelope 2
  have hC₀ : 0 ≤ C₀ := mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg
    (_root_.RHTower.thetaAmplitudeEnvelope_nonneg 2)
  set cg : ℝ := burnolGoodLowerConst
  have hcg : 0 < cg := burnolGoodLowerConst_pos
  set Cu : ℝ := (burnolPrefixConst : ℝ)
  have hCu : 0 ≤ Cu := Nat.cast_nonneg _
  set L₀ : ℝ := |Real.log (C₀ + 1)| + |Real.log cg|
  have hL₀nn : 0 ≤ L₀ := by positivity
  set L₁ : ℝ := Real.log (128 * (c + 7))
  have hL₁ : 0 ≤ L₁ := Real.log_nonneg (by nlinarith)
  set Q : ℝ := Cu * (2 * L₁ + 16)
  have hQ : 0 ≤ Q := by positivity
  refine ⟨Nat.ceil ((Q + L₀ + 1) ^ 2), fun m hm N hN => ?_⟩
  set X : ℝ := ((m + 5 : ℕ) : ℝ) with hX
  have hX5 : 5 ≤ X := by rw [hX]; exact_mod_cast (show 5 ≤ m + 5 by omega)
  have hX0 : 0 < X := by linarith
  have hm_ge : (Q + L₀ + 1) ^ 2 ≤ X := by
    have h1 : (Q + L₀ + 1) ^ 2 ≤ (m : ℝ) := (Nat.ceil_le).mp hm
    rw [hX]; push_cast; linarith
  have hsqrt : Q + L₀ + 1 ≤ Real.sqrt X := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Q + L₀ + 1)]
    exact Real.sqrt_le_sqrt hm_ge
  have hsqrtX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  set n : ℝ := (logDoorStage c m : ℝ)
  have hn6 : 6 ≤ n := six_le_logDoorStage_real c m
  set d : ℕ := ∑ w ∈ burnolUnitXiZeros m, (analyticOrderAt _root_.RHTower.xi w).toNat
  have hd : (d : ℝ) ≤ Cu * Real.log X := burnolUnitXiZeros_totalOrder_le m
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  -- `log (128 n) ≤ L₁ + log X`
  have hn_le : n ≤ (c + 7) * X := by
    have h := logDoorStage_le c hc m
    have hlx : Real.log X ≤ X := (Real.log_le_sub_one_of_pos hX0).trans (by linarith)
    nlinarith
  have h128 : Real.log (128 * n) ≤ L₁ + Real.log X := by
    rw [← Real.log_mul (by positivity) hX0.ne']
    exact Real.log_le_log (by positivity) (by nlinarith)
  have h128_nn : 0 ≤ Real.log (128 * n) := Real.log_nonneg (by nlinarith)
  have hdlog : (d : ℝ) * Real.log (128 * n) ≤ X := by
    have h1 : (d : ℝ) * Real.log (128 * n) ≤ Cu * Real.log X * (L₁ + Real.log X) :=
      mul_le_mul hd h128 h128_nn (by positivity)
    have h2 : Real.log X ≤ 2 * Real.sqrt X := log_le_two_sqrt' hX0
    have h3 : Real.log X ^ 2 ≤ 16 * Real.sqrt X := log_sq_le_sixteen_sqrt (by linarith)
    have h4 : Cu * Real.log X * (L₁ + Real.log X) ≤ Q * Real.sqrt X := by
      have : Cu * Real.log X * (L₁ + Real.log X) = Cu * (L₁ * Real.log X + Real.log X ^ 2) := by
        ring
      rw [this]
      have h5 : L₁ * Real.log X + Real.log X ^ 2 ≤ (2 * L₁ + 16) * Real.sqrt X := by nlinarith
      calc Cu * (L₁ * Real.log X + Real.log X ^ 2) ≤ Cu * ((2 * L₁ + 16) * Real.sqrt X) :=
            mul_le_mul_of_nonneg_left h5 hCu
        _ = Q * Real.sqrt X := by ring
    have h6 : Q * Real.sqrt X ≤ X :=
      calc Q * Real.sqrt X ≤ Real.sqrt X * Real.sqrt X :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
        _ = X := hsqrtX
    linarith
  -- `(N + 1)² ≥ 16 (m + 1)`
  have hN16 : 16 * ((m : ℝ) + 1) ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
    have h4 : 4 * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_right _ four_le_doorOpenerSqrtConst).trans hN
    have hsq : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' m
    have h16 : 16 * (m + 1) ≤ (N + 1) ^ 2 := by nlinarith
    exact_mod_cast h16
  have hL₀ : Real.log (C₀ + 1) - Real.log cg ≤ L₀ := by
    have := le_abs_self (Real.log (C₀ + 1)); have := neg_abs_le (Real.log cg); linarith
  have hkey : Real.log (C₀ + 1) - ((N + 1 : ℕ) : ℝ) ^ 2 <
      Real.log cg - ((m + 3 : ℕ) : ℝ) - (d : ℝ) * Real.log (128 * n) := by
    have hmX : ((m + 3 : ℕ) : ℝ) = X - 2 := by rw [hX]; push_cast; ring
    have hL₀X : L₀ ≤ Real.sqrt X := by linarith
    have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sqrt_nonneg X]
    have hmX' : 16 * ((m : ℝ) + 1) = 16 * X - 64 := by rw [hX]; push_cast; ring
    rw [hmX]
    linarith
  have hpow : ((1 / (16 * n)) / 8) ^ d = Real.exp (-((d : ℝ) * Real.log (128 * n))) := by
    rw [show (1 / (16 * n)) / 8 = (128 * n)⁻¹ by field_simp; ring, ← Real.exp_log
      (by positivity : (0 : ℝ) < ((128 * n)⁻¹) ^ d), Real.log_pow, Real.log_inv]
    congr 1
    ring
  calc thetaStripTailBound N = C₀ * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) := rfl
    _ ≤ (C₀ + 1) * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = Real.exp (Real.log (C₀ + 1) - ((N + 1 : ℕ) : ℝ) ^ 2) := by
        rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_neg, div_eq_mul_inv]
    _ < Real.exp (Real.log cg - ((m + 3 : ℕ) : ℝ) - (d : ℝ) * Real.log (128 * n)) :=
        Real.exp_lt_exp.mpr hkey
    _ = cg * Real.exp (-((m + 3 : ℕ) : ℝ)) * ((1 / (16 * n)) / 8) ^ d := by
        rw [hpow, Real.exp_sub, Real.exp_sub, Real.exp_log hcg, Real.exp_neg, Real.exp_neg,
          div_eq_mul_inv, div_eq_mul_inv]


theorem zhukovskyMajorAxis_logDoorStage (c : ℝ) (m : ℕ) :
    zhukovskyMajorAxis (logDoorStage c m) = 1 / 2 - 1 / (2 * (logDoorStage c m : ℝ)) := by
  unfold zhukovskyMajorAxis
  rw [zhukovskyStage_eq_self (six_le_logDoorStage c m)]

/-- **Corridor transfer.** Under an `A / log|γ|` zero-free corridor for `ξ`, at stage
`n = logDoorStage (1/(32A)) m` every theta window of prefix `N ≥ doorSqrtPrefix m` is a stage-`n`
corridor window with margin `1/(4n)`, for all large `m`. -/
theorem exists_logStage_inCorridor {T₁ A : ℝ} (hT₁ : 2 ≤ T₁) (hA : 0 < A)
    (hcorr : ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
      |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im|) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
      ∀ hbdry : (∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
        (_root_.RHTower.rectangleBoundaryPath (centeredWindowLowerLeft (burnolUnitLower m))
          (centeredWindowUpperRight (burnolUnitUpper m)) t) ≠ 0),
        (centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry).InCorridor
          (logDoorStage (1 / (32 * A)) m) (logStageMargin (1 / (32 * A)) m) := by
  set c : ℝ := 1 / (32 * A) with hc_def
  have hc : 0 < c := by positivity
  obtain ⟨m₁, htail⟩ := exists_logStage_tail_lt c hc
  refine ⟨max m₁ (max 11 (max (Nat.ceil T₁ + 3) (Nat.ceil (Real.exp (1 + 224 * A)) + 3))),
    fun m hm N hN hbdry z hz => ?_⟩
  have hm₁ : m₁ ≤ m := le_of_max_le_left hm
  have hm11 : 11 ≤ m := (le_max_left _ _).trans (le_of_max_le_right hm)
  have hmT : Nat.ceil T₁ + 3 ≤ m :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_of_max_le_right hm)
  have hmE : Nat.ceil (Real.exp (1 + 224 * A)) + 3 ≤ m :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_of_max_le_right hm)
  set n : ℝ := (logDoorStage c m : ℝ) with hn_def
  have hn6 : 6 ≤ n := six_le_logDoorStage_real c m
  obtain ⟨hz_rect, hz_zero⟩ := (mem_centeredThetaWindow_iff _ N hbdry z).mp hz
  obtain ⟨w, hw, hdist⟩ := exists_xiZero_near_thetaZero m N (r := 1 / (16 * n)) (by positivity)
    (htail m hm₁ N hN) hz_rect hz_zero
  obtain ⟨⟨hw0, hw1, hwy1, hwy2⟩, hw_xi⟩ := (mem_burnolUnitXiZeros_iff m w).mp hw
  have hy₁ := sub_three_le_burnolUnitLower m
  have hmR : (Nat.ceil T₁ : ℝ) + 3 ≤ (m : ℝ) := by exact_mod_cast hmT
  have hT_le : T₁ ≤ (m : ℝ) - 3 := by linarith [Nat.le_ceil T₁]
  have hw_im : (m : ℝ) - 3 < w.im := by linarith
  have hw_im_pos : 0 < w.im := by linarith
  have hlog_pos : 0 < Real.log ((m : ℝ) - 3) := Real.log_pos (by linarith)
  have hw_corr : |w.re - 1 / 2| ≤ A / Real.log ((m : ℝ) - 3) := by
    have h := hcorr w hw_xi (by rw [abs_of_pos hw_im_pos]; linarith)
    rw [abs_of_pos hw_im_pos] at h
    exact h.trans (div_le_div_of_nonneg_left hA.le hlog_pos
      (Real.log_le_log (by linarith) hw_im.le))
  have hre_close : |z.re - w.re| ≤ 1 / (16 * n) := by
    have := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at this
    linarith
  -- `16 A n ≤ log (m - 3)`
  have hlogM : 1 + 224 * A ≤ Real.log ((m : ℝ) - 3) := by
    have hE : Real.exp (1 + 224 * A) ≤ (m : ℝ) - 3 := by
      have h1 : (Nat.ceil (Real.exp (1 + 224 * A)) : ℝ) + 3 ≤ (m : ℝ) := by exact_mod_cast hmE
      linarith [Nat.le_ceil (Real.exp (1 + 224 * A))]
    rw [← Real.log_exp (1 + 224 * A)]
    exact Real.log_le_log (Real.exp_pos _) hE
  have hlog5 : Real.log ((m + 5 : ℕ) : ℝ) ≤ 1 + Real.log ((m : ℝ) - 3) := by
    have hm11R : (11 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm11
    have h2 : ((m + 5 : ℕ) : ℝ) ≤ 2 * ((m : ℝ) - 3) := by push_cast; linarith
    have h3 : Real.log ((m + 5 : ℕ) : ℝ) ≤ Real.log (2 * ((m : ℝ) - 3)) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have h16 : 16 * A * n ≤ Real.log ((m : ℝ) - 3) := by
    have hn_le := logDoorStage_le c hc m
    rw [← hn_def] at hn_le
    have hcA : 16 * A * c = 1 / 2 := by rw [hc_def]; field_simp; ring
    have : 16 * A * n ≤ 16 * A * (c * Real.log ((m + 5 : ℕ) : ℝ) + 7) :=
      mul_le_mul_of_nonneg_left hn_le (by positivity)
    nlinarith
  have hAlog : 2 * (A / Real.log ((m : ℝ) - 3)) ≤ 1 / (8 * n) := by
    rw [show 2 * (A / Real.log ((m : ℝ) - 3)) = 2 * A / Real.log ((m : ℝ) - 3) by ring,
      div_le_div_iff₀ hlog_pos (by positivity)]
    nlinarith
  unfold logStageMargin
  rw [zhukovskyMajorAxis_logDoorStage, ← hn_def]
  have hzw : z.re - 1 / 2 ≤ |w.re - 1 / 2| + 1 / (16 * n) := by
    have h1 := le_abs_self (w.re - 1 / 2)
    have h2 := (abs_le.mp hre_close).2
    linarith
  have hfinal : 1 / 2 - (1 / 2 - 1 / (2 * n)) - 1 / (4 * n) = 2 * (1 / (16 * n)) + 1 / (8 * n) := by
    field_simp; ring
  rw [hfinal]
  linarith

/-- For a margin `0 < η < 1` and window degree `D`, some certificate order `K` satisfies
`2 D² (1 - η)^{K+1} / η < π / 2`. -/
theorem exists_certificate_order (D η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ K : ℕ, 2 * D ^ 2 * (1 - η) ^ (K + 1) / η < Real.pi / 2 := by
  have hε : 0 < Real.pi / 2 * η / (2 * D ^ 2 + 1) := by positivity
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by linarith : 1 - η < 1)
  refine ⟨K, ?_⟩
  have hpow : (1 - η) ^ (K + 1) ≤ (1 - η) ^ K :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_succ K)
  have hD : 0 ≤ 2 * D ^ 2 := by positivity
  have h1 : 2 * D ^ 2 * (1 - η) ^ (K + 1) / η ≤ 2 * D ^ 2 * (Real.pi / 2 * η / (2 * D ^ 2 + 1)) / η := by
    gcongr
    exact hpow.trans hK.le
  have h2 : 2 * D ^ 2 * (Real.pi / 2 * η / (2 * D ^ 2 + 1)) / η =
      Real.pi / 2 * (2 * D ^ 2 / (2 * D ^ 2 + 1)) := by
    field_simp
  have h3 : 2 * D ^ 2 / (2 * D ^ 2 + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hpi : 0 < Real.pi / 2 := by positivity
  rw [h2] at h1
  nlinarith

/-- **Bessel–Szegő certificate at the logarithmic stage ⇔ inverse-logarithmic corridor.**
`ξ` has a zero-free corridor `|Re ρ - 1/2| ≤ A / log |Im ρ|` iff, for some `c > 0` and all large
`m`, at stage `n = logDoorStage c m` and every prefix `N ≥ doorSqrtPrefix m`, the explicit order-`K`
Bessel–Szegő certificate built from the source energy `|𝒵_N(t)|²` makes the centered collision
loop sectorial for every `K` with `2 D² (1 - η)^{K+1} / η < π / 2`, `η = 1/(4n)`. -/
theorem logStage_besselSzego_iff_invLog_corridor :
    (∃ T₁ A : ℝ, 2 ≤ T₁ ∧ 0 < A ∧
      ∀ ρ : ℂ, _root_.RHTower.xi ρ = 0 → T₁ ≤ |ρ.im| →
        |ρ.re - 1 / 2| ≤ A / Real.log |ρ.im|) ↔
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m, ∀ K : ℕ,
      2 * (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) ^ 2 *
          (1 - logStageMargin c m) ^ (K + 1) / logStageMargin c m < Real.pi / 2 →
      ∀ u : HTGeometry.UnitCircle,
        0 < (besselSzegoCertificate (logDoorStage c m) K
            (fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2) u *
          centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
            (logDoorStage c m) N u).re := by
  constructor
  · rintro ⟨T₁, A, hT₁, hA, hcorr⟩
    obtain ⟨m₀, hm₀⟩ := exists_logStage_inCorridor hT₁ hA hcorr
    refine ⟨1 / (32 * A), by positivity, m₀, fun m hm N hN K hK u => ?_⟩
    have hbdry := burnolUnit_bdry_regular m ((burnolPrefix_le_doorSqrtPrefix m).trans hN)
    have hW := hm₀ m hm N hN hbdry
    have hn6 := six_le_logDoorStage_real (1 / (32 * A)) m
    have hη : 0 < logStageMargin (1 / (32 * A)) m := by unfold logStageMargin; positivity
    have hη2 : logStageMargin (1 / (32 * A)) m ≤ 1 / 2 := by
      unfold logStageMargin
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    rw [← centeredThetaWindow_degree (burnolUnitLower_le_upper m) N hbdry] at hK
    have h := hW.besselSzegoCertificate_mul_loop_pos
      (eval_centeredThetaDifferencePoly_eq_window (burnolUnitLower_le_upper m) N hbdry) hη hη2 hK u
    have hE : (fun t => ‖(centeredThetaWindow (burnolUnitLower_le_upper m) N hbdry).expSum t‖ ^ 2) =
        fun t => ‖centeredThetaExpSum (burnolUnitLower m) (burnolUnitUpper m) N t‖ ^ 2 := by
      funext t
      rw [centeredThetaWindow_expSum]
    rw [hE] at h
    exact h
  · rintro ⟨c, hc, m₀, hcert⟩
    have h3 : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ N ≥ doorSqrtPrefix m,
        ∃ F : ℂ → ℂ, IsDiskUnit F ∧
          ∀ u : HTGeometry.UnitCircle,
            0 < (F (u : ℂ) *
              centeredThetaLaurentLoop (burnolUnitLower m) (burnolUnitUpper m)
                (logDoorStage c m) N u).re := ⟨c, hc, m₀, fun m hm N hN => ?_⟩
    · exact (logStage_sqrtPrefix_szego_iff_invLog_corridor.out 2 0).mp h3
    have hn6 := six_le_logDoorStage_real c m
    have hη : 0 < logStageMargin c m := by unfold logStageMargin; positivity
    have hη1 : logStageMargin c m < 1 := by
      unfold logStageMargin
      rw [div_lt_one (by positivity)]
      linarith
    obtain ⟨K, hK⟩ := exists_certificate_order
      (centeredThetaWindowDegree (burnolUnitLower m) (burnolUnitUpper m) N : ℝ) _ hη hη1
    exact ⟨_, isDiskUnit_besselSzegoCertificate _ K _, hcert m hm N hN K hK⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision
