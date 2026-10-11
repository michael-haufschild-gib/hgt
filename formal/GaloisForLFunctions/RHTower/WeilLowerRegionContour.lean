import GaloisForLFunctions.RHTower.WeilEvaporationLockRigidity

/-!
# The lower contour shift with regularity on the lower region only

The contour shift of Hamburger's radial integral from the lower critical line to `Re s = 3/2`
(`setIntegral_Iic_radial_eq_of_lower`) only ever evaluates the twisted producer at points with
`Im s ≤ −1`.  This file restates it with continuity on the closed strip `{½ ≤ Re s ≤ 3/2, Im s ≤ −1}` and complex
differentiability on the open strip `{½ < Re s < 3/2, Im s < −1}` instead of on the whole
half-plane.

This matters for lock twists whose natural holomorphic extension is defined only below the real
axis, such as `e^{iΘ(i(s−½)/2)}` with `Θ` built from `Log(i(s−½)/2 + e)`: their branch cut runs
along the upper critical line.  It also matters for exponential sums `Σ q_j ρ_j^{−(s−½)}` with
`ρ_j < 1`, which converge on the strip but not necessarily to its right.

**Theorem** (`setIntegral_Iic_radial_eq_of_lowerRegion`).  The identity
`∫_{t ≤ b} φ_H(t) k(2t, τ) dt = ½(∫_{y ≤ 2b} (F_H k_τ)(3/2 + iy) dy + i Top(2b))` holds under these
local hypotheses.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

theorem continuousAt_prodF_of_continuousAt {G : ℂ → ℂ} {s : ℂ} (hG : ContinuousAt G s)
    (hs : 1 / 2 ≤ s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) : ContinuousAt (prodF G) s := by
  have hc : ContinuousAt (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    (continuousAt_id.mul (continuousAt_id.sub continuousAt_const)).mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith)).continuousAt
  exact hG.div hc (denom_ne_zero (by linarith) h0 h1)

theorem differentiableAt_prodF_of_differentiableAt {G : ℂ → ℂ} {s : ℂ}
    (hG : DifferentiableAt ℂ G s) (hs : 1 / 2 < s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (prodF G) s := by
  have hc : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1) * Complex.Gammaℝ z) s :=
    (differentiableAt_id.mul (differentiableAt_id.sub (differentiableAt_const _))).mul
      (differentiableAt_Gammaℝ_of_re_pos (by linarith))
  exact hG.div hc (denom_ne_zero (by linarith) h0 h1)

/-- **Contour shift on a finite lower rectangle** with regularity on the lower strip. -/
theorem intervalIntegral_radial_eq_lowerRegion {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → s.re < 3 / 2 → s.im < -1 → DifferentiableAt ℂ G s) {τ : ℂ} (hτ0 : τ ≠ 0)
    {a b : ℝ} (hab : a ≤ b) (hb : b ≤ -1) :
    ∫ t in a..b, phiG G t * pairKernel (2 * t) τ = (1 / 2 : ℂ) *
      ((∫ y in (2 * a)..(2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I * (∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  set g : ℝ → ℂ := fun y => edgeIntegrand G τ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) with hg
  have hchange : ∫ t in a..b, phiG G t * pairKernel (2 * t) τ =
      (2 : ℝ)⁻¹ • ∫ y in (2 * a)..(2 * b), g y := by
    rw [← intervalIntegral.integral_comp_mul_left g (two_ne_zero' ℝ)]
    exact intervalIntegral.integral_congr fun t _ => phiG_mul_pairKernel_eq G τ t
  have h2ab : 2 * a ≤ 2 * b := by linarith
  have h2b : 2 * b ≤ -2 := by linarith
  set z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((2 * a : ℝ) : ℂ) * I with hz
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + ((2 * b : ℝ) : ℂ) * I with hw
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = 2 * a := by simp [hz]
  have hwre : w.re = 3 / 2 := by simp [hw]
  have hwim : w.im = 2 * b := by simp [hw]
  have hcont : ContinuousOn (edgeIntegrand G τ)
      (Set.uIcc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.uIcc (2 * a) (2 * b)) := by
    intro s hs
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le h2ab] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    have h0 : s ≠ 0 := fun h => by rw [h] at hi2; simp at hi2; linarith
    have h1 : s ≠ 1 := fun h => by rw [h] at hi2; simp at hi2; linarith
    exact ((continuousAt_prodF_of_continuousAt (hGc s hr1 hr2 (by linarith)) hr1 h0 h1).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℂ (edgeIntegrand G τ)
      (Set.Ioo (min (1 / 2 : ℝ) (3 / 2)) (max (1 / 2 : ℝ) (3 / 2)) ×ℂ
        Set.Ioo (min (2 * a) (2 * b)) (max (2 * a) (2 * b))) := by
    intro s hs
    rw [Complex.mem_reProdIm, min_eq_left (by norm_num), max_eq_right (by norm_num),
      min_eq_left h2ab, max_eq_right h2ab] at hs
    obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
    have h0 : s ≠ 0 := fun h => by rw [h] at hi2; simp at hi2; linarith
    have h1 : s ≠ 1 := fun h => by rw [h] at hi2; simp at hi2; linarith
    exact ((differentiableAt_prodF_of_differentiableAt (hGd s hr1 hr2 (by linarith)) hr1 h0 h1).mul
      (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (edgeIntegrand G τ) z w
    (by rw [hzre, hwre, hzim, hwim]; exact hcont) (by rw [hzre, hwre, hzim, hwim]; exact hdiff)
  rw [hzre, hwre, hzim, hwim] at hrect
  simp only [smul_eq_mul] at hrect
  rw [hchange, Complex.real_smul]
  have hL : ∫ y in (2 * a)..(2 * b), g y =
      (∫ y in (2 * a)..(2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I * (∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I) := by
    have hI2 : I * I = -1 := Complex.I_mul_I
    linear_combination I * hrect + ((∫ y in (2 * a)..(2 * b), g y) -
      ∫ y in (2 * a)..(2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) * hI2
  rw [hL]
  push_cast
  ring

/-- **The lower contour shift on a half-line** with regularity on the lower strip. -/
theorem setIntegral_Iic_radial_eq_of_lowerRegion {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → s.re < 3 / 2 → s.im < -1 → DifferentiableAt ℂ G s) {CF M : ℝ} (hCF : 0 ≤ CF)
    (hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ))
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖)
    (hedge : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      M * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))))
    {b : ℝ} (hb : b ≤ -1)
    (hfint : IntegrableOn (fun t => phiG G t * pairKernel (2 * t) τ) (Iic b)) :
    ∫ t in Iic b, phiG G t * pairKernel (2 * t) τ = (1 / 2 : ℂ) *
      ((∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre hτpos
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ with hK
  have hec : ContinuousOn (fun y : ℝ => edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (Iic (2 * b)) := by
    intro y hy
    have hy' : y ≤ 2 * b := hy
    have hre : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re = 3 / 2 := by simp
    have him : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).im ≤ -1 := by simp; linarith
    have h0 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have h1 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; norm_num at this
    refine (ContinuousAt.comp (g := edgeIntegrand G τ) ?_ (by fun_prop)).continuousWithinAt
    exact (continuousAt_prodF_of_continuousAt (hGc _ (by rw [hre]; norm_num) (by rw [hre]) him)
      (by rw [hre]; norm_num) h0 h1).mul
      (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num) (by rw [hre]; norm_num)).continuousAt
  have heint : IntegrableOn (fun y : ℝ => edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (Iic (2 * b)) := by
    have hdom : IntegrableOn (fun y : ℝ => M * K * ‖cexp ((δ : ℂ) * (y : ℂ))‖)
        (Iic (2 * b)) :=
      ((integrableOn_exp_mul_complex_Iic (a := (δ : ℂ)) (by simpa using hδ0) (2 * b)).norm).const_mul _
    refine hdom.mono' (hec.aestronglyMeasurable measurableSet_Iic) ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => ?_))
    have hy0 : y < 0 := by have : y ≤ 2 * b := hy; linarith
    have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; have : y ≤ 2 * b := hy; linarith
    have h := hedge y (by have : y ≤ 2 * b := hy; linarith)
    rw [Complex.norm_exp]
    have he : ((δ : ℂ) * (y : ℂ)).re = -(|y| * δ) := by
      rw [abs_of_neg hy0]; simp; ring
    rw [he]
    calc ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          M * (K * Real.exp (-(|y| * δ))) := h
      _ = M * K * Real.exp (-(|y| * δ)) := by ring
  -- the bottom edge vanishes
  have hbotb : ∀ a : ℝ, a ≤ -1 → ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)‖ ≤ CF * K * (2 / δ ^ 2) / |a| := by
    intro a ha
    have ha0 : 0 < |a| := by rw [abs_of_neg (by linarith)]; linarith
    have hu : 2 ≤ |2 * a| := by rw [abs_mul, abs_two]; rw [abs_of_neg (by linarith : a < 0)]; linarith
    have h := norm_horizontalEdge_le_lower hF hτre hτ1 (by linarith : 2 * a ≤ -2)
    set u : ℝ := |2 * a| with hu_def
    have hu1 : (1 + u) ^ (1 / 2 : ℝ) ≤ 1 + u := by
      calc (1 + u) ^ (1 / 2 : ℝ) ≤ (1 + u) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = 1 + u := Real.rpow_one _
    have hexp : Real.exp (-(u * δ)) ≤ 2 / (u * δ) ^ 2 := by
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u * δ by positivity)
      have hpos : 0 < u * δ := by positivity
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div,
        div_le_iff₀ (by norm_num)]
      nlinarith [sq_nonneg (u * δ)]
    have hua : u = 2 * |a| := by rw [hu_def, abs_mul, abs_two]
    calc _ ≤ CF * (1 + u) ^ (1 / 2 : ℝ) * (K * Real.exp (-(u * δ))) := h
      _ ≤ CF * (1 + u) * (K * (2 / (u * δ) ^ 2)) := by
          gcongr
      _ ≤ CF * K * (2 / δ ^ 2) / |a| := by
          rw [hua]
          have hK0 : 0 ≤ K := by positivity
          have e : CF * (1 + 2 * |a|) * (K * (2 / (2 * |a| * δ) ^ 2)) =
              CF * K * (2 / δ ^ 2) * ((1 + 2 * |a|) / (4 * |a| ^ 2)) := by
            field_simp; ring
          rw [e, div_eq_mul_one_div (CF * K * (2 / δ ^ 2))]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) ha0]
          nlinarith
  have hbot : Tendsto (fun a : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) atBot (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun a : ℝ => CF * K * (2 / δ ^ 2) / |a|) ?_ ?_
    · filter_upwards [eventually_le_atBot (-1 : ℝ)] with a ha using hbotb a ha
    · have := (tendsto_inv_atTop_zero.comp tendsto_abs_atBot_atTop).const_mul (CF * K * (2 / δ ^ 2))
      rw [mul_zero] at this
      exact this.congr fun a => by simp [div_eq_mul_inv]
  -- pass to the limit
  have h1 : Tendsto (fun a : ℝ => ∫ t in a..b, phiG G t * pairKernel (2 * t) τ) atBot
      (𝓝 (∫ t in Iic b, phiG G t * pairKernel (2 * t) τ)) :=
    intervalIntegral_tendsto_integral_Iic b hfint tendsto_id
  have h2 : Tendsto (fun a : ℝ => ∫ y in (2 * a)..(2 * b),
      edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) atBot
      (𝓝 (∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    intervalIntegral_tendsto_integral_Iic (2 * b) heint (tendsto_id.const_mul_atBot two_pos)
  set T : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)
    with hT
  have h3 := ((h2.sub (hbot.const_mul I)).add (tendsto_const_nhds (x := I * T))).const_mul
    (1 / 2 : ℂ)
  rw [mul_zero, sub_zero] at h3
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [eventually_le_atBot b] with a ha
  rw [intervalIntegral_radial_eq_lowerRegion hGc hGd hτ0 ha hb]




end

end AbelianTwist

end RHTower
