import GaloisForLFunctions.RHTower.ProlateForbiddenRegion

/-!
# Sharp endpoint tunneling across the prolate forbidden region

For `0 ≤ s < 1`, the radial WKB profile diverges at the singular endpoint while the logarithmic
derivative of every smooth endpoint-normalized solution has a finite limit.  The Riccati comparison
therefore starts automatically sufficiently close to the endpoint.  Passing that comparison to the
endpoint gives the strict action bound

`Phi (sqrt ((1+s)/2)) * exp (-c sqrt (1-s)) ≤ Phi 1`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Set Topology intervalIntegral MeasureTheory

open _root_.RHTower

/-- For positive bandwidth and radial separation below one, the WKB profile diverges at the right
singular endpoint. -/
theorem tendsto_prolateWKB_radial_at_one
    {c s : ℝ} (hc : 0 < c) (hs : s < 1) :
    Tendsto (prolateWKB c (-(s * c ^ (2 : ℕ)))) (nhdsWithin 1 (Iio 1)) atTop := by
  let l : Filter ℝ := nhdsWithin 1 (Iio 1)
  let d : ℝ → ℝ := fun y => 1 - y ^ (2 : ℕ)
  let N : ℝ → ℝ := fun y => -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)
  have hd0 : Tendsto d l (nhds 0) := by
    have h : Tendsto d (nhdsWithin 1 (Iio 1)) (nhds (d 1)) :=
      (show ContinuousAt d 1 by fun_prop).tendsto.mono_left inf_le_left
    simpa only [l, d, one_pow, sub_self] using h
  have hleft : ∀ᶠ y : ℝ in l, -1 < y := by
    change Ioi (-1 : ℝ) ∈ l
    exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  have hdpos : ∀ᶠ y : ℝ in l, 0 < d y := by
    filter_upwards [self_mem_nhdsWithin, hleft] with y hy hyl
    dsimp only [d]
    rw [show 1 - y ^ (2 : ℕ) = (1 - y) * (1 + y) by ring]
    exact mul_pos (sub_pos.mpr hy) (by linarith)
  have hdWithin : Tendsto d l (nhdsWithin 0 (Ioi 0)) :=
    (tendsto_nhdsWithin_iff.mpr ⟨hd0, hdpos⟩)
  have hinv : Tendsto (fun y => (d y)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp hdWithin
  have hN : Tendsto N l (nhds (c ^ (2 : ℕ) * (1 - s))) := by
    have h : Tendsto N (nhds 1) (nhds (N 1)) :=
      (show ContinuousAt N 1 by fun_prop).tendsto
    have hN1 : N 1 = c ^ (2 : ℕ) * (1 - s) := by dsimp only [N]; ring
    rw [hN1] at h
    change Tendsto N (nhds 1 ⊓ principal (Iio 1)) (nhds (c ^ (2 : ℕ) * (1 - s)))
    exact h.mono_left inf_le_left
  have hA : 0 < c ^ (2 : ℕ) * (1 - s) := by positivity
  have hNlower : ∀ᶠ y in l, c ^ (2 : ℕ) * (1 - s) / 2 < N y :=
    (tendsto_order.1 hN).1 _ (by linarith)
  have hlowerTop : Tendsto (fun y => (c ^ (2 : ℕ) * (1 - s) / 2) * (d y)⁻¹) l atTop :=
    hinv.const_mul_atTop (by positivity)
  have hquot : Tendsto (fun y => N y / d y) l atTop := by
    refine tendsto_atTop_mono' l ?_ hlowerTop
    filter_upwards [hNlower, hdpos] with y hNy hdy
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hNy.le (inv_nonneg.mpr hdy.le)
  have hsqrt := Real.tendsto_sqrt_atTop.comp hquot
  change Tendsto (fun y => Real.sqrt (N y / d y)) l atTop
  exact hsqrt

/-- The logarithmic derivative of a smooth endpoint-normalized solution converges to its finite
endpoint value. -/
theorem tendsto_prolateLogDeriv_at_one
    {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ1 : Φ 1 = 1) :
    Tendsto (prolateLogDeriv Φ) (nhdsWithin 1 (Iio 1))
      (nhds (prolateLogDeriv Φ 1)) := by
  have hΦ : Continuous Φ := hsm.continuous
  have hd : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2.continuous
  have hne : Φ 1 ≠ 0 := by rw [hΦ1]; norm_num
  have hcont : ContinuousAt (fun y => -(deriv Φ y / Φ y)) 1 :=
    (hd.continuousAt.div hΦ.continuousAt hne).neg
  change Tendsto (fun y => -(deriv Φ y / Φ y))
    (nhdsWithin 1 (Iio 1)) (nhds (-(deriv Φ 1 / Φ 1)))
  exact hcont.tendsto.mono_left inf_le_left

/-- Close enough to the right endpoint, the diverging WKB profile dominates the finite logarithmic
derivative, so the Riccati comparison has its required terminal inequality automatically. -/
theorem eventually_prolateLogDeriv_le_prolateWKB_radial_at_one
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ1 : Φ 1 = 1) :
    ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1),
      prolateLogDeriv Φ b ≤ prolateWKB c (-(s * c ^ (2 : ℕ))) b := by
  let L : ℝ := prolateLogDeriv Φ 1
  have hlog := tendsto_prolateLogDeriv_at_one hsm hΦ1
  have hlogUpper : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1),
      prolateLogDeriv Φ b < L + 1 :=
    (tendsto_order.1 hlog).2 (L + 1) (by dsimp only [L]; linarith)
  have hWKBLower : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1),
      L + 1 ≤ prolateWKB c (-(s * c ^ (2 : ℕ))) b :=
    (tendsto_prolateWKB_radial_at_one hc hs).eventually_ge_atTop (L + 1)
  filter_upwards [hlogUpper, hWKBLower] with b hb hWb
  exact hb.le.trans hWb

/-- **Sharp endpoint tunneling bound.**  Positive radial separation reduces the forbidden-region
action from `c` to `c sqrt (1-s)`. -/
theorem prolateOuterStart_mul_exp_neg_action_le_one
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) :
    Φ (prolateOuterStart s) * Real.exp (-(c * Real.sqrt (1 - s))) ≤ 1 := by
  let a : ℝ := prolateOuterStart s
  let l : Filter ℝ := nhdsWithin 1 (Iio 1)
  have haMem := prolateOuterStart_mem_Ico hs0 hs1
  have ha0 : 0 ≤ a := haMem.1
  have ha1 : a < 1 := haMem.2
  have hQnonneg : ∀ y ∈ Icc a 1, 0 ≤ -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    intro y hy
    have hsep := radial_separation_lt_sq_of_outerStart_le hs0 hs1 hy.1
    nlinarith [sq_pos_of_pos hc]
  have hpos : ∀ y ∈ Icc a 1, 0 < Φ y :=
    prolate_pos_on_right_forbidden_region hsm heig hΦ1 ha0 hQnonneg
  have hab : ∀ᶠ b : ℝ in l, a ≤ b := by
    change Ici a ∈ l
    exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ha1)
  have hb1 : ∀ᶠ b : ℝ in l, b < 1 := self_mem_nhdsWithin
  have hinit := eventually_prolateLogDeriv_le_prolateWKB_radial_at_one hc hs1 hsm hΦ1
  have hbound : ∀ᶠ b : ℝ in l,
      Φ a * Real.exp (-(c * Real.sqrt (1 - s))) ≤ Φ b := by
    filter_upwards [hab, hb1, hinit] with b habb hb hterminal
    have hQ : ∀ y ∈ Icc a b, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
      intro y hy
      have hsep := radial_separation_lt_sq_of_outerStart_le hs0 hs1 hy.1
      nlinarith [sq_pos_of_pos hc]
    have houter : ∀ y ∈ Icc a b,
        c ^ (2 : ℕ) * (1 - 2 * y ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)) := by
      intro y hy
      exact outer_sign_of_prolateOuterStart_le hs0 hy.1
    have hraw := le_endpoint_prolateWKB hsm heig habb ha0
      (by linarith : -1 < a) hb
      (fun y hy => hpos y ⟨hy.1, le_trans hy.2 hb.le⟩) hQ houter hterminal
    have haction := integral_prolateWKB_radial_le_aperture hc.le hs0 hs1.le
      habb ha0 (by linarith : -1 < a) hb
      (fun y hy => (radial_separation_lt_sq_of_outerStart_le hs0 hs1 hy.1).le)
    have hexp : Real.exp (-(c * Real.sqrt (1 - s))) ≤
        Real.exp (-∫ t in a..b, prolateWKB c (-(s * c ^ (2 : ℕ))) t) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hΦa : 0 < Φ a := hpos a (left_mem_Icc.mpr ha1.le)
    exact (mul_le_mul_of_nonneg_left hexp hΦa.le).trans hraw
  have hlim : Tendsto Φ l (nhds 1) := by
    have h : Tendsto Φ (nhdsWithin 1 (Iio 1)) (nhds (Φ 1)) :=
      hsm.continuous.continuousAt.tendsto.mono_left inf_le_left
    simpa only [l, hΦ1] using h
  exact ge_of_tendsto hlim hbound

end GaloisForLFunctions.RHTower

end
