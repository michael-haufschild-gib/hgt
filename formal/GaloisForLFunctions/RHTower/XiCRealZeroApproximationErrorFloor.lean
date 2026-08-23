import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# Quantitative error floor for real-zero approximations of centered Xi

The qualitative zero-transfer theorem says that locally uniform approximation of `XiC` by entire
real-zero functions implies RH.  This module gives its local quantitative contrapositive.  Around
any nonreal zero of a differentiable limit, one isolating sphere has a positive error floor for
every differentiable approximant whose zeros are real.  Under false RH, the same sphere and floor
work simultaneously for every such approximant.

The proof uses the corpus sphere-domination zero-planting theorem.  Its factor `3` yields the
explicit floor `epsilon = min_{sphere} ‖XiC‖ / 3`.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- **[LEAN-PROVED] [OBSTRUCTION] [NOVELTY UNVERIFIED]** A nonreal zero forces a contour error
floor against every differentiable real-zero approximant.  The lower bound may be supplied by any
positive boundary modulus certificate; no convergence hypothesis is used. -/
theorem exists_sphere_error_floor_of_nonreal_zero
    {F G : ℂ → ℂ} {z : ℂ} {r delta : ℝ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hr : 0 < r) (hrim : r < |z.im|)
    (hz : F z = 0)
    (hlower : ∀ w ∈ sphere z r, delta ≤ ‖F w‖)
    (hreal : ∀ w, G w = 0 → w.im = 0) :
    ∃ w ∈ sphere z r, delta / 3 ≤ dist (F w) (G w) := by
  by_contra hfloor
  push Not at hfloor
  have hGz : G z ≠ 0 := by
    intro hzero
    have himzero := hreal z hzero
    rw [himzero, abs_zero] at hrim
    linarith
  let g : ℂ → ℂ := fun w => G w - F w
  have hg : Differentiable ℂ g := hG.sub hF
  have hg0 : g z ≠ 0 := by
    simp only [g, hz, sub_zero]
    exact hGz
  have hdom : ∀ w ∈ sphere z r, 3 * ‖g w‖ ≤ ‖F w‖ := by
    intro w hw
    have hclose := hfloor w hw
    have hmin := hlower w hw
    have hnorm : ‖g w‖ = dist (F w) (G w) := by
      simp only [g, dist_eq_norm]
      rw [norm_sub_rev]
    rw [hnorm]
    nlinarith
  obtain ⟨w, hw, hwzero⟩ := exists_zero_of_sphere_domination hr
    hg.diffContOnCl hF.diffContOnCl hz hg0 hdom
  have hGw : G w = 0 := by
    simpa only [g, sub_add_cancel] using hwzero
  have himw : w.im = 0 := hreal w hGw
  have himdist : |z.im| ≤ dist w z := by
    rw [dist_eq_norm]
    have h := Complex.abs_im_le_norm (w - z)
    simpa [himw, abs_neg] using h
  have hdist : dist w z ≤ r := Metric.mem_closedBall.mp hw
  linarith

/-- **[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]** An isolated nonreal zero of `XiC` constructs
one positive error floor, uniform over the entire class of differentiable real-zero functions. -/
theorem exists_XiC_realZero_approximant_sphere_error_floor
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hrim : r < |z.im|)
    (hz : XiC z = 0) (hsphere : ∀ w ∈ sphere z r, XiC w ≠ 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ G : ℂ → ℂ, Differentiable ℂ G →
        (∀ w, G w = 0 → w.im = 0) →
        ∃ w ∈ sphere z r, epsilon ≤ dist (XiC w) (G w) := by
  have hsphereNonempty : (sphere z r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hnormContinuous : ContinuousOn (fun w => ‖XiC w‖) (sphere z r) :=
    XiC_differentiable.continuous.continuousOn.norm
  obtain ⟨w0, hw0, hmin⟩ :=
    (isCompact_sphere z r).exists_isMinOn hsphereNonempty hnormContinuous
  have hminPos : 0 < ‖XiC w0‖ := norm_pos_iff.mpr (hsphere w0 hw0)
  refine ⟨‖XiC w0‖ / 3, div_pos hminPos (by norm_num), ?_⟩
  intro G hG hreal
  exact exists_sphere_error_floor_of_nonreal_zero
    XiC_differentiable hG hr hrim hz hmin hreal

/-- **[LEAN-PROVED] [OBSTRUCTION] [NOVELTY UNVERIFIED]** If RH is false, one fixed contour gives
a positive uniform error floor for every differentiable real-zero approximant to centered Xi.
Thus failure of a Connes-style real-zero approximation is quantitatively localized rather than
merely asserted by the qualitative zero-transfer criterion. -/
theorem exists_XiC_realZero_approximation_error_floor_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) :
    ∃ z : ℂ, ∃ r epsilon : ℝ,
      0 < r ∧ r < |z.im| ∧ XiC z = 0 ∧ 0 < epsilon ∧
        ∀ G : ℂ → ℂ, Differentiable ℂ G →
          (∀ w, G w = 0 → w.im = 0) →
          ∃ w ∈ sphere z r, epsilon ≤ dist (XiC w) (G w) := by
  have hnotRight : ¬ ∀ rho : ℂ, rho ∈ rightHalf → xi rho ≠ 0 := by
    intro hright
    exact hnot (rh_iff_xi_ne_zero_right.mpr hright)
  push Not at hnotRight
  obtain ⟨rho, hrho, hzero⟩ := hnotRight
  let z : ℂ := (rho - 1 / 2) * (-I)
  have hz : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = rho := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hzim : z.im = 1 / 2 - rho.re := by simp [z]
  have hzimNeg : z.im < 0 := by
    rw [hzim]
    exact sub_neg.mpr (mem_rightHalf.mp hrho)
  have hzimAbs : 0 < |z.im| := abs_pos.mpr (ne_of_lt hzimNeg)
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, XiC w = 0 := by
    intro hev
    have hall := XiC_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev (Set.mem_univ 0)
    exact XiC_zero_ne hall
  have hpunct : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
    (XiC_analytic z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnotEventuallyZero
  obtain ⟨delta, hdelta, hdeltasub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  let r : ℝ := min (|z.im| / 2) (delta / 2)
  have hr : 0 < r := lt_min (half_pos hzimAbs) (half_pos hdelta)
  have hrim : r < |z.im| :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hzimAbs)
  have hrdelta : r < delta :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self hdelta)
  have hsphere : ∀ w ∈ sphere z r, XiC w ≠ 0 := by
    intro w hw
    apply hdeltasub
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrdelta)
    · exact Set.mem_compl_singleton_iff.mpr
        (Metric.ne_of_mem_sphere hw hr.ne')
  obtain ⟨epsilon, hepsilon, hfloor⟩ :=
    exists_XiC_realZero_approximant_sphere_error_floor hr hrim hz hsphere
  exact ⟨z, r, epsilon, hr, hrim, hz, hepsilon, hfloor⟩

end RHTower
