import GaloisForLFunctions.RHTower.ProlateForbiddenEndpoint

/-!
# A global radial Riccati barrier

For a positive radial separation ratio `s`, the elementary profile

`V(y) = c sqrt(1-s) y / sqrt(1-y²)`

has more Riccati slack than the literal WKB square root.  Once `c*s ≥ 4`, that slack absorbs
the derivative defect throughout the right forbidden region, including the part below the outer
WKB threshold.  Its action from the turning point `sqrt s` to the endpoint is exactly `c(1-s)`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Set Topology intervalIntegral MeasureTheory

open _root_.RHTower

/-- Elementary radial barrier with exactly integrable action. -/
def prolateRadialBarrier (c s : ℝ) (y : ℝ) : ℝ :=
  c * Real.sqrt (1 - s) * y / Real.sqrt (1 - y ^ (2 : ℕ))

theorem hasDerivAt_prolateRadialBarrier
    {c s y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (prolateRadialBarrier c s)
      (c * Real.sqrt (1 - s) / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ)) y := by
  have hp : 0 < 1 - y ^ (2 : ℕ) := by nlinarith [hy.1, hy.2]
  have hr : 0 < Real.sqrt (1 - y ^ (2 : ℕ)) := Real.sqrt_pos.2 hp
  have hinner : HasDerivAt (fun t : ℝ => 1 - t ^ (2 : ℕ)) (-(2 * y)) y := by
    have h := (hasDerivAt_pow 2 y).const_sub (1 : ℝ)
    refine h.congr_deriv ?_
    norm_num
  have hroot := hinner.sqrt (ne_of_gt hp)
  have hquot := (hasDerivAt_id y).div hroot (ne_of_gt hr)
  have hrsq : Real.sqrt (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - y ^ (2 : ℕ) :=
    Real.sq_sqrt hp.le
  have hquotDeriv :
      (1 * Real.sqrt (1 - y ^ (2 : ℕ)) -
          y * (-(2 * y) / (2 * Real.sqrt (1 - y ^ (2 : ℕ))))) /
            Real.sqrt (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) =
        1 / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ) := by
    field_simp
    nlinarith
  have hquotFinal := hquot.congr_deriv (by
    simpa only [id_eq] using hquotDeriv)
  have hquotFun :
      (id / fun t : ℝ => Real.sqrt (1 - t ^ (2 : ℕ))) =
        fun t : ℝ => t / Real.sqrt (1 - t ^ (2 : ℕ)) := by
    funext t
    rfl
  rw [hquotFun] at hquotFinal
  have hscaled := hquotFinal.const_mul (c * Real.sqrt (1 - s))
  have hscaledFun :
      (fun t : ℝ => c * Real.sqrt (1 - s) *
        (t / Real.sqrt (1 - t ^ (2 : ℕ)))) = prolateRadialBarrier c s := by
    funext t
    rw [prolateRadialBarrier]
    ring
  rw [hscaledFun] at hscaled
  simpa only [div_eq_mul_inv, one_mul] using hscaled

theorem continuousOn_prolateRadialBarrier
    {c s a b : ℝ}
    (hp : ∀ y ∈ Icc a b, 0 < 1 - y ^ (2 : ℕ)) :
    ContinuousOn (prolateRadialBarrier c s) (Icc a b) := by
  unfold prolateRadialBarrier
  exact ((continuousOn_const.mul continuousOn_id).div
    (Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.sub (continuousOn_id.pow 2)))
    fun y hy => ne_of_gt (Real.sqrt_pos.2 (hp y hy)))

/-- For `c*s ≥ 4`, the elementary radial profile is a Riccati subsolution throughout the
positive half-band. -/
theorem prolateRadialBarrier_subsolution
    {c s y : ℝ} (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hcs : 4 ≤ c * s) (hy : y ∈ Ioo (0 : ℝ) 1) :
    c * Real.sqrt (1 - s) / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ) ≤
      (prolateRadialBarrier c s y) ^ (2 : ℕ) +
        (2 * y / (1 - y ^ (2 : ℕ))) * prolateRadialBarrier c s y -
          (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) := by
  let C : ℝ := c * Real.sqrt (1 - s)
  let d : ℝ := 1 - y ^ (2 : ℕ)
  let r : ℝ := Real.sqrt d
  have hd : 0 < d := by dsimp only [d]; nlinarith [hy.1, hy.2]
  have hr : 0 < r := by dsimp only [r]; exact Real.sqrt_pos.2 hd
  have hrsq : r ^ (2 : ℕ) = d := by
    dsimp only [r]
    exact Real.sq_sqrt hd.le
  have hroot0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hroot1 : Real.sqrt (1 - s) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - s ≤ 1 by linarith)
    simpa using h
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hCle : C ≤ c := by
    dsimp only [C]
    nlinarith
  have hCsq : C ^ (2 : ℕ) = c ^ (2 : ℕ) * (1 - s) := by
    dsimp only [C]
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - s)]
  have hidentity :
      (prolateRadialBarrier c s y) ^ (2 : ℕ) +
          (2 * y / (1 - y ^ (2 : ℕ))) * prolateRadialBarrier c s y -
            (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) =
        c ^ (2 : ℕ) * s + (2 * y / d) * (C * y / r) := by
    rw [prolateRadialBarrier]
    change (C * y / r) ^ (2 : ℕ) + (2 * y / d) * (C * y / r) -
      (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / d = _
    field_simp
    ring_nf
    rw [hCsq, hrsq]
    dsimp only [d]
    ring
  rw [hidentity]
  change C / r ^ (3 : ℕ) ≤ c ^ (2 : ℕ) * s + (2 * y / d) * (C * y / r)
  by_cases hhalf : (1 / 2 : ℝ) ≤ y ^ (2 : ℕ)
  · have hbarrier : C / r ^ (3 : ℕ) ≤ (2 * y / d) * (C * y / r) := by
      rw [div_le_iff₀ (pow_pos hr 3)]
      have hfac : 0 ≤ 2 * y ^ (2 : ℕ) - 1 := by linarith
      have hnum : C ≤ 2 * C * y ^ (2 : ℕ) := by
        nlinarith [mul_nonneg hC0 hfac]
      have hrewrite :
          (2 * y / d) * (C * y / r) * r ^ (3 : ℕ) = 2 * C * y ^ (2 : ℕ) := by
        field_simp
        rw [hrsq]
        ring
      rw [hrewrite]
      exact hnum
    exact hbarrier.trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg c) hs0))
  · have hyhalf : y ^ (2 : ℕ) < 1 / 2 := lt_of_not_ge hhalf
    have hdhalf : 1 / 2 < d := by dsimp only [d]; linarith
    have hrhalf : 1 / 2 ≤ r := by
      nlinarith [hrsq, Real.sqrt_nonneg d]
    have hdr : 1 / 4 ≤ d * r := by
      nlinarith [mul_le_mul hdhalf.le hrhalf (by norm_num : (0 : ℝ) ≤ 1 / 2) hd.le]
    have hr3 : r ^ (3 : ℕ) = d * r := by nlinarith [hrsq]
    have hderiv : C / r ^ (3 : ℕ) ≤ 4 * C := by
      rw [hr3, div_le_iff₀ (mul_pos hd hr)]
      have hmul : C * (1 / 4 : ℝ) ≤ C * (d * r) :=
        mul_le_mul_of_nonneg_left hdr hC0
      nlinarith
    have hclock : 4 * C ≤ c ^ (2 : ℕ) * s := by
      have hmul := mul_le_mul_of_nonneg_left hcs hc.le
      have h4 : 4 * C ≤ 4 * c := by nlinarith
      calc
        4 * C ≤ 4 * c := h4
        _ ≤ c ^ (2 : ℕ) * s := by nlinarith
    have htail : 0 ≤ (2 * y / d) * (C * y / r) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hy.1.le) hd.le)
        (div_nonneg (mul_nonneg hC0 hy.1.le) hr.le)
    exact hderiv.trans (hclock.trans (le_add_of_nonneg_right htail))

/-- Backward Riccati comparison using the global radial barrier. -/
theorem prolateLogDeriv_le_radialBarrier
    {c s a b : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1)
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hinit : prolateLogDeriv Φ b ≤ prolateRadialBarrier c s b) :
    ∀ y ∈ Icc a b, prolateLogDeriv Φ y ≤ prolateRadialBarrier c s y := by
  have hp : ∀ y ∈ Icc a b, 0 < 1 - y ^ (2 : ℕ) := by
    intro y hy
    nlinarith [ha, hy.1, hy.2, hb]
  refine HTGeometry.riccati_le_of_le_of_subsolution
    (u := prolateLogDeriv Φ) (U := prolateRadialBarrier c s)
    (u' := fun y => (prolateLogDeriv Φ y) ^ (2 : ℕ) +
      (2 * y / (1 - y ^ (2 : ℕ))) * prolateLogDeriv Φ y -
        (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
    (U' := fun y => c * Real.sqrt (1 - s) / Real.sqrt (1 - y ^ (2 : ℕ)) ^ (3 : ℕ))
    (bcoef := fun y => 2 * y / (1 - y ^ (2 : ℕ)))
    (q := fun y => (-(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
    hab (continuousOn_prolateLogDeriv hsm fun y hy => ne_of_gt (hpos y hy))
    (continuousOn_prolateRadialBarrier hp) ?_ ?_ ?_ ?_ ?_ hinit
  · intro y hy
    have hymem : y ∈ Icc a b := ⟨hy.1.le, hy.2.le⟩
    have hyband : y ∈ Ioo (-1 : ℝ) 1 := by
      constructor <;> nlinarith [ha, hy.1, hy.2, hb]
    exact hasDerivAt_prolateLogDeriv hsm heig hyband (ne_of_gt (hpos y hymem))
  · intro y hy
    have hyband : y ∈ Ioo (-1 : ℝ) 1 := by
      constructor <;> nlinarith [ha, hy.1, hy.2, hb]
    exact hasDerivAt_prolateRadialBarrier hyband
  · have hnum : ContinuousOn (fun y : ℝ => 2 * y) (Icc a b) := by fun_prop
    have hden : ContinuousOn (fun y : ℝ => 1 - y ^ (2 : ℕ)) (Icc a b) := by fun_prop
    exact hnum.div hden fun y hy => ne_of_gt (hp y hy)
  · intro _ _
    rfl
  · intro y hy
    have hypos : y ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨lt_trans ha hy.1, lt_trans hy.2 hb⟩
    exact prolateRadialBarrier_subsolution hc hs0 hs1 hcs hypos

/-- The barrier has the elementary antiderivative `-c sqrt(1-s) sqrt(1-y²)`. -/
theorem integral_prolateRadialBarrier
    {c s a b : ℝ} (hab : a ≤ b) (ha : -1 < a) (hb : b < 1) :
    (∫ y in a..b, prolateRadialBarrier c s y) =
      c * Real.sqrt (1 - s) *
        (Real.sqrt (1 - a ^ (2 : ℕ)) - Real.sqrt (1 - b ^ (2 : ℕ))) := by
  have hcont : ContinuousOn (prolateRadialBarrier c s) (Icc a b) := by
    apply continuousOn_prolateRadialBarrier
    intro y hy
    nlinarith [ha, hy.1, hy.2, hb]
  have hint : IntervalIntegrable (prolateRadialBarrier c s) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hcont.integrableOn_compact isCompact_Icc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => -(c * Real.sqrt (1 - s)) * Real.sqrt (1 - y ^ (2 : ℕ)))
    (f' := prolateRadialBarrier c s) (fun y hy => by
      rw [uIcc_of_le hab] at hy
      simpa only [prolateRadialBarrier] using
        hasDerivAt_negMulSqrt (c := c * Real.sqrt (1 - s))
          (show y ∈ Ioo (-1 : ℝ) 1 by
            exact ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩)) hint
  rw [hFTC]
  ring

/-- Near the singular endpoint, the finite logarithmic derivative lies below the radial barrier. -/
theorem eventually_prolateLogDeriv_le_radialBarrier_at_one
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ1 : Φ 1 = 1) :
    ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1),
      prolateLogDeriv Φ b ≤ prolateRadialBarrier c s b := by
  have hWKB := eventually_prolateLogDeriv_le_prolateWKB_radial_at_one hc hs1 hsm hΦ1
  have hnonneg : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1), 0 ≤ b := by
    exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds (by norm_num))
  have hturnNhds : ∀ᶠ b : ℝ in nhds 1, s < b ^ (2 : ℕ) :=
    (tendsto_order.1 ((continuousAt_id' (y := (1 : ℝ))).pow 2).tendsto).1 s
      (by simpa using hs1)
  have hturn : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1), s ≤ b ^ (2 : ℕ) :=
    (Filter.Eventually.filter_mono inf_le_left hturnNhds).mono fun _ h => h.le
  filter_upwards [hWKB, hnonneg, hturn, self_mem_nhdsWithin] with b hlog hb0 hbturn hb1
  exact hlog.trans (prolateWKB_le_radial_separation hc.le hs0 hs1.le
    ⟨by linarith, hb1⟩ hb0 hbturn)

/-- Endpoint passage for the global radial barrier on any positive zero-free interval. -/
theorem mul_exp_neg_radialBarrier_action_le_one
    {c s a : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (hpos : ∀ y ∈ Icc a 1, 0 < Φ y) :
    Φ a * Real.exp (-(c * Real.sqrt (1 - s) * Real.sqrt (1 - a ^ (2 : ℕ)))) ≤ 1 := by
  let l : Filter ℝ := nhdsWithin 1 (Iio 1)
  have hab : ∀ᶠ b : ℝ in l, a ≤ b := by
    exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ha1)
  have hb1 : ∀ᶠ b : ℝ in l, b < 1 := self_mem_nhdsWithin
  have hinit := eventually_prolateLogDeriv_le_radialBarrier_at_one hc hs0 hs1 hsm hΦ1
  have hbound : ∀ᶠ b : ℝ in l,
      Φ a * Real.exp (-(c * Real.sqrt (1 - s) * Real.sqrt (1 - a ^ (2 : ℕ)))) ≤ Φ b := by
    filter_upwards [hab, hb1, hinit] with b habb hb hterminal
    have hlog := prolateLogDeriv_le_radialBarrier hc hs0 hs1 hcs hsm heig
      habb ha0 hb (fun y hy => hpos y ⟨hy.1, hy.2.trans hb.le⟩) hterminal
    have hraw := le_endpoint_of_logDeriv_le habb
      (contDiff_infty_iff_deriv.mp hsm).1
      (continuousOn_prolateRadialBarrier fun y hy => by
        nlinarith [ha0, hy.1, hy.2, hb])
      (fun y hy => hpos y ⟨hy.1, hy.2.trans hb.le⟩)
      (fun y hy => hlog y ⟨hy.1.le, hy.2.le⟩)
    rw [integral_prolateRadialBarrier habb (by linarith) hb] at hraw
    have hsqrt0 : 0 ≤ Real.sqrt (1 - b ^ (2 : ℕ)) := Real.sqrt_nonneg _
    have hfac0 : 0 ≤ c * Real.sqrt (1 - s) := by positivity
    have hexp :
        Real.exp (-(c * Real.sqrt (1 - s) * Real.sqrt (1 - a ^ (2 : ℕ)))) ≤
          Real.exp (-(c * Real.sqrt (1 - s) *
            (Real.sqrt (1 - a ^ (2 : ℕ)) - Real.sqrt (1 - b ^ (2 : ℕ))))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hfac0 hsqrt0]
    exact (mul_le_mul_of_nonneg_left hexp (hpos a (left_mem_Icc.mpr ha1.le)).le).trans hraw
  have hlim : Tendsto Φ l (nhds 1) := by
    have h : Tendsto Φ (nhdsWithin 1 (Iio 1)) (nhds (Φ 1)) :=
      hsm.continuous.continuousAt.tendsto.mono_left inf_le_left
    simpa only [l, hΦ1] using h
  exact ge_of_tendsto hlim hbound

/-- **Turning-point tunneling law.**  For positive separation and `c*s ≥ 4`, the endpoint-normalized
solution has turning-point amplitude at most `exp(c(1-s))`. -/
theorem prolateTurningPoint_mul_exp_neg_action_le_one
    {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1,
      prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) :
    Φ (Real.sqrt s) * Real.exp (-(c * (1 - s))) ≤ 1 := by
  have hsqrt0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hsqrt1 : Real.sqrt s < 1 := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]
  have hQ : ∀ y ∈ Icc (Real.sqrt s) 1,
      0 ≤ -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    intro y hy
    have hsqrtSq : Real.sqrt s ^ (2 : ℕ) = s := Real.sq_sqrt hs0.le
    have hy0 : 0 ≤ y := hsqrt0.le.trans hy.1
    have hsq : Real.sqrt s ^ (2 : ℕ) ≤ y ^ (2 : ℕ) :=
      (sq_le_sq₀ hsqrt0.le hy0).2 hy.1
    nlinarith [sq_nonneg c]
  have hpos := prolate_pos_on_right_forbidden_region hsm heig hΦ1
    hsqrt0.le hQ
  have hmain := mul_exp_neg_radialBarrier_action_le_one hc hs0.le hs1 hcs
    hsqrt0 hsqrt1 hsm heig hΦ1 hpos
  have hsqrtSq : Real.sqrt s ^ (2 : ℕ) = s := Real.sq_sqrt hs0.le
  have hone : Real.sqrt (1 - s) ^ (2 : ℕ) = 1 - s := Real.sq_sqrt (by linarith)
  convert hmain using 1
  congr 3
  rw [hsqrtSq]
  calc
    c * (1 - s) = c * Real.sqrt (1 - s) ^ (2 : ℕ) :=
      congrArg (fun x : ℝ => c * x) hone.symm
    _ = c * Real.sqrt (1 - s) * Real.sqrt (1 - s) := by ring

end GaloisForLFunctions.RHTower

end
