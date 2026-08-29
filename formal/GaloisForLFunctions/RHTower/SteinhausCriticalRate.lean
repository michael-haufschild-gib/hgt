import GaloisForLFunctions.RHTower.SteinhausCriticalCumulant
import GaloisForLFunctions.RHTower.SteinhausRatePowerAsymptotic

/-!
# The critical regime of the rate function

At `α = 1/2` the cumulant is `Λ(λ) ∼ λ² log(1/λ)/8`, a power law with a slowly varying correction.
Its Legendre transform is therefore not a pure power: the optimal tilt is `λ = 4q/log(1/q)` and

`I_{1/2}(q) ∼ 2q²/log(1/q)`,

the card's `(23)`.  Both halves are explicit.  The lower half evaluates the single tilt
`λ = q/(2A log(1/q))`, whose value is *exactly* `q²/log(1/q)` times
`1/(4A) − (log log(1/q) + log 2A)/(4A log(1/q))`.  The upper half splits the tilt range at
`q/A`: below it the logarithm is at least `log(1/q) + log A`, which caps every tilt by
`q²/(4A(log(1/q)+log A))`; above it the value is already negative because `log(1/λ) ≥ 1`.
-/

open Filter Topology Set

namespace HTGeometry

noncomputable section

theorem tendsto_log_div_id_atTop : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- The exact value of the near-optimal critical tilt, as a multiple of `q²/log(1/q)`. -/
def critLowerProfile (A t : ℝ) : ℝ :=
  1 / (4 * A) - (Real.log t + Real.log (2 * A)) / (4 * A * t)

theorem tendsto_critLowerProfile {A : ℝ} (hA : 0 < A) :
    Tendsto (fun t : ℝ => critLowerProfile A t) atTop (𝓝 (1 / (4 * A))) := by
  have hA4 : (0 : ℝ) < 4 * A := by linarith
  have h1 : Tendsto (fun t : ℝ => Real.log t / (4 * A * t)) atTop (𝓝 0) := by
    have h := tendsto_log_div_id_atTop.div_const (4 * A)
    rw [zero_div] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  have h2 : Tendsto (fun t : ℝ => Real.log (2 * A) / (4 * A * t)) atTop (𝓝 0) := by
    have hden : Tendsto (fun t : ℝ => 4 * A * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hA4 tendsto_id
    exact hden.const_div_atTop _
  have hsum := h1.add h2
  rw [add_zero] at hsum
  have hlim := (tendsto_const_nhds (x := 1 / (4 * A)) (f := atTop (α := ℝ))).sub hsum
  rw [sub_zero] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [critLowerProfile]
  field_simp


/-- The near-optimal critical tilt. -/
def critTilt (A q : ℝ) : ℝ := q / (2 * A * Real.log (1 / q))

theorem tendsto_critTilt {A : ℝ} (hA0 : 0 < A) :
    Tendsto (fun q : ℝ => critTilt A q) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hq0 : Tendsto (fun q : ℝ => q) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun q : ℝ => 2 * A * Real.log (1 / q)) (𝓝[>] (0 : ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith) tendsto_logInv_atTop
  have hinv : Tendsto (fun q : ℝ => (2 * A * Real.log (1 / q))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hden.inv_tendsto_atTop
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hmul := hq0.mul hinv
    rw [mul_zero] at hmul
    refine Tendsto.congr' ?_ hmul
    filter_upwards with q
    simp only [critTilt]
    ring
  · have hlog : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / q) :=
      tendsto_logInv_atTop.eventually_gt_atTop 0
    filter_upwards [hlog, self_mem_nhdsWithin] with q hlg hq
    have hq0' : (0 : ℝ) < q := hq
    rw [mem_Ioi]
    simp only [critTilt]
    positivity

/-- The exact value of the critical tilt against the power law `A λ² log(1/λ)`. -/
theorem critTilt_value {A q : ℝ} (hA0 : 0 < A) (hq0 : 0 < q) (ht : 0 < Real.log (1 / q)) :
    critTilt A q * q - A * critTilt A q ^ 2 * Real.log (1 / critTilt A q)
      = q ^ 2 / Real.log (1 / q) * critLowerProfile A (Real.log (1 / q)) := by
  set t : ℝ := Real.log (1 / q) with hT
  have hden : (0 : ℝ) < 2 * A * t := by positivity
  have hlam : critTilt A q = q / (2 * A * t) := rfl
  have hlam0 : (0 : ℝ) < q / (2 * A * t) := by positivity
  have hlogq : Real.log q = -t := by
    rw [hT, one_div, Real.log_inv, neg_neg]
  have hlog : Real.log (1 / (q / (2 * A * t))) = Real.log (2 * A) + Real.log t + t := by
    rw [one_div, inv_div, Real.log_div hden.ne' hq0.ne', Real.log_mul (by positivity) ht.ne',
      hlogq]
    ring
  rw [hlam, hlog, critLowerProfile]
  field_simp
  ring

/-- **The critical rate from below.** -/
theorem eventually_critLowerProfile_le {A : ℝ} (hA0 : 0 < A)
    (h : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
        rvCumulant (1 / 2) lam ≤ A * lam ^ 2 * Real.log (1 / lam)) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      critLowerProfile A (Real.log (1 / q)) ≤ rvRate (1 / 2) q * Real.log (1 / q) / q ^ 2 := by
  have hpull := (tendsto_critTilt hA0).eventually h
  have hlog : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / q) :=
    tendsto_logInv_atTop.eventually_gt_atTop 0
  have hq1 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpull, hlog, hq1, self_mem_nhdsWithin] with q hcum ht hqlt hq
  have hq0 : (0 : ℝ) < q := hq
  have hlam0 : (0 : ℝ) < critTilt A q := by
    simp only [critTilt]
    positivity
  have hle := le_rvRate (α := (1 / 2 : ℝ)) (by norm_num) hqlt hlam0.le
  have hval := critTilt_value hA0 hq0 ht
  have hkey : q ^ 2 / Real.log (1 / q) * critLowerProfile A (Real.log (1 / q))
      ≤ rvRate (1 / 2) q := by
    rw [← hval]
    linarith
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < q ^ 2)]
  rw [div_mul_eq_mul_div, div_le_iff₀ ht] at hkey
  linarith [hkey]


/-- **The critical rate from above.** -/
theorem eventually_rvRate_crit_le_profile {A : ℝ} (hA0 : 0 < A)
    (h : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
        A * lam ^ 2 * Real.log (1 / lam) ≤ rvCumulant (1 / 2) lam) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ),
      rvRate (1 / 2) q * Real.log (1 / q) / q ^ 2
        ≤ Real.log (1 / q) / (4 * A * (Real.log (1 / q) + Real.log A)) := by
  obtain ⟨t, ht, htP⟩ := Filter.eventually_iff_exists_mem.1 h
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp ht
  have hu0 : (0 : ℝ) < u := hu
  set δ : ℝ := min (u / 2) (Real.exp (-1)) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (Real.exp_pos _)
  have hδu : δ < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδe : δ ≤ Real.exp (-1) := min_le_right _ _
  have hlow : ∀ lam : ℝ, 0 < lam → lam ≤ δ →
      A * lam ^ 2 * Real.log (1 / lam) ≤ rvCumulant (1 / 2) lam := by
    intro lam hlam0 hlamδ
    exact htP lam (hsub ⟨hlam0, lt_of_le_of_lt hlamδ hδu⟩)
  have hLone : ∀ lam : ℝ, 0 < lam → lam ≤ δ → 1 ≤ Real.log (1 / lam) := by
    intro lam hlam0 hlamδ
    have h1 : Real.log lam ≤ Real.log (Real.exp (-1)) :=
      Real.log_le_log hlam0 (le_trans hlamδ hδe)
    rw [Real.log_exp] at h1
    rw [one_div, Real.log_inv]
    linarith
  set m : ℝ := rvCumulant (1 / 2) δ / δ with hm
  have hm0 : 0 < m := div_pos (rvCumulant_pos (by norm_num) hδ0) hδ0
  have hqm : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < m :=
    (eventually_lt_nhds hm0).filter_mono nhdsWithin_le_nhds
  have hq1 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hqA : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < A * δ :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < A * δ)).filter_mono nhdsWithin_le_nhds
  have hLA : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / q) + Real.log A := by
    have := tendsto_logInv_atTop.eventually_gt_atTop (-Real.log A)
    filter_upwards [this] with q hq
    linarith
  filter_upwards [hqm, hq1, hqA, hLA, self_mem_nhdsWithin] with q hqm' hq1' hqA' hLA' hq
  have hq0 : (0 : ℝ) < q := hq
  set B : ℝ := A * (Real.log (1 / q) + Real.log A) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  have hqAδ : q / A ≤ δ := by
    rw [div_le_iff₀ hA0]
    nlinarith [hqA']
  have hlogQA : Real.log (1 / (q / A)) = Real.log (1 / q) + Real.log A := by
    rw [one_div, one_div, inv_div, Real.log_div hA0.ne' hq0.ne', Real.log_inv]
    ring
  have hsup : rvRate (1 / 2) q ≤ q ^ 2 / (4 * B) := by
    refine csSup_le (rvLegendreSet_nonempty _ _) ?_
    rintro y ⟨lam, hlam, rfl⟩
    have hRHS : (0 : ℝ) ≤ q ^ 2 / (4 * B) := by positivity
    rcases eq_or_lt_of_le hlam with hzero | hpos
    · rw [← hzero, rvCumulant_zero]
      simpa using hRHS
    · rcases le_or_gt lam (q / A) with hle | hgt
      · have hlamδ : lam ≤ δ := le_trans hle hqAδ
        have hLmono : Real.log (1 / (q / A)) ≤ Real.log (1 / lam) := by
          refine Real.log_le_log (by positivity) ?_
          rw [one_div, one_div]
          exact inv_anti₀ hpos hle
        rw [hlogQA] at hLmono
        have hΛ := hlow lam hpos hlamδ
        have hBd : B * lam ^ 2 ≤ rvCumulant (1 / 2) lam := by
          have : A * lam ^ 2 * (Real.log (1 / q) + Real.log A)
              ≤ A * lam ^ 2 * Real.log (1 / lam) := by
            have : (0 : ℝ) ≤ A * lam ^ 2 := by positivity
            nlinarith [hLmono]
          rw [hB]
          nlinarith [hΛ, this]
        have hyoung : lam * q - B * lam ^ 2 ≤ q ^ 2 / (4 * B) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (2 * B * lam - q)]
        linarith
      · rcases le_or_gt lam δ with hlamδ | hbig
        · have hΛ := hlow lam hpos hlamδ
          have hL1 := hLone lam hpos hlamδ
          have hstep : A * lam ^ 2 ≤ A * lam ^ 2 * Real.log (1 / lam) := by
            nlinarith [hL1, (by positivity : (0 : ℝ) ≤ A * lam ^ 2)]
          have hqlt : q < A * lam := by
            rw [div_lt_iff₀ hA0] at hgt
            linarith
          nlinarith [hΛ, hstep, hpos, hRHS]
        · have hslope := rvCumulant_slope_mono (α := (1 / 2 : ℝ)) (by norm_num) hδ0 hbig.le
          have hid : lam / δ * rvCumulant (1 / 2) δ = lam * m := by rw [hm]; field_simp
          rw [hid] at hslope
          nlinarith [hslope, hpos, hqm', hRHS]
  have hLq : (0 : ℝ) < Real.log (1 / q) := by
    rw [one_div, Real.log_inv, neg_pos]
    exact Real.log_neg hq0 hq1'
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hstep : rvRate (1 / 2) q * Real.log (1 / q) * (4 * A * (Real.log (1 / q) + Real.log A))
      ≤ (q ^ 2 / (4 * B)) * Real.log (1 / q) * (4 * B) := by
    have h4B : (0 : ℝ) < 4 * B := by positivity
    have : rvRate (1 / 2) q * Real.log (1 / q) ≤ (q ^ 2 / (4 * B)) * Real.log (1 / q) :=
      mul_le_mul_of_nonneg_right hsup hLq.le
    have heq : 4 * A * (Real.log (1 / q) + Real.log A) = 4 * B := by rw [hB]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right this h4B.le
  have hcancel : (q ^ 2 / (4 * B)) * Real.log (1 / q) * (4 * B)
      = Real.log (1 / q) * q ^ 2 := by
    field_simp
  linarith [hstep, hcancel]


theorem tendsto_critUpperProfile {A : ℝ} (hA0 : 0 < A) :
    Tendsto (fun t : ℝ => t / (4 * A * (t + Real.log A))) atTop (𝓝 (1 / (4 * A))) := by
  have hden : Tendsto (fun t : ℝ => t + Real.log A) atTop atTop :=
    tendsto_atTop_add_const_right atTop (Real.log A) tendsto_id
  have h1 : Tendsto (fun t : ℝ => Real.log A / (t + Real.log A)) atTop (𝓝 0) :=
    hden.const_div_atTop _
  have h2 := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub h1).div_const (4 * A)
  rw [sub_zero] at h2
  refine Tendsto.congr' ?_ h2
  filter_upwards [hden.eventually_gt_atTop 0] with t hpos
  field_simp
  ring

/-- The eventual upper power bound on the critical cumulant. -/
theorem eventually_rvCumulant_crit_le {A : ℝ} (hA : 1 / 8 < A) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      rvCumulant (1 / 2) lam ≤ A * lam ^ 2 * Real.log (1 / lam) := by
  have hlt := tendsto_rvCumulant_crit.eventually (eventually_lt_nhds hA)
  have hlog : ∀ᶠ lam in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / lam) :=
    tendsto_logInv_atTop.eventually_gt_atTop 0
  filter_upwards [hlt, hlog, self_mem_nhdsWithin] with lam hratio hL hlam
  have hlam0 : (0 : ℝ) < lam := hlam
  have hden : (0 : ℝ) < lam ^ 2 * Real.log (1 / lam) := by positivity
  rw [div_lt_iff₀ hden] at hratio
  nlinarith [hratio]

/-- The eventual lower power bound on the critical cumulant. -/
theorem eventually_le_rvCumulant_crit {A : ℝ} (hA : A < 1 / 8) :
    ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      A * lam ^ 2 * Real.log (1 / lam) ≤ rvCumulant (1 / 2) lam := by
  have hgt := tendsto_rvCumulant_crit.eventually (eventually_gt_nhds hA)
  have hlog : ∀ᶠ lam in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / lam) :=
    tendsto_logInv_atTop.eventually_gt_atTop 0
  filter_upwards [hgt, hlog, self_mem_nhdsWithin] with lam hratio hL hlam
  have hlam0 : (0 : ℝ) < lam := hlam
  have hden : (0 : ℝ) < lam ^ 2 * Real.log (1 / lam) := by positivity
  rw [lt_div_iff₀ hden] at hratio
  nlinarith [hratio]

/-- **The critical regime of the rate function**, the card's `(6)` middle line:
`I_{1/2}(q) ∼ 2q²/log(1/q)`. -/
theorem tendsto_rvRate_crit :
    Tendsto (fun q : ℝ => rvRate (1 / 2) q * Real.log (1 / q) / q ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have hq1 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hLq : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / q) :=
    tendsto_logInv_atTop.eventually_gt_atTop 0
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    rcases le_or_gt c 0 with hcneg | hc0
    · filter_upwards [hq1, hLq, self_mem_nhdsWithin] with q hqlt hL hq
      have hq0 : (0 : ℝ) < q := hq
      have hpos : 0 < rvRate (1 / 2) q :=
        rvRate_pos (by norm_num) (by norm_num) hq0 hqlt
      have : (0 : ℝ) < rvRate (1 / 2) q * Real.log (1 / q) / q ^ 2 := by positivity
      linarith
    · have hlt : (1 : ℝ) / 8 < 1 / (4 * c) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        linarith
      obtain ⟨A, hA1, hA2⟩ := exists_between hlt
      have hA0 : (0 : ℝ) < A := by linarith [(by norm_num : (0:ℝ) < 1/8)]
      have hcA : c < 1 / (4 * A) := by
        rw [lt_div_iff₀ (by positivity)]
        rw [lt_div_iff₀ (by positivity)] at hA2
        linarith
      have hlower := eventually_critLowerProfile_le hA0 (eventually_rvCumulant_crit_le hA1)
      have hprof := (tendsto_critLowerProfile hA0).comp tendsto_logInv_atTop
      have hev := hprof.eventually (eventually_gt_nhds hcA)
      filter_upwards [hlower, hev] with q h1 h2
      exact lt_of_lt_of_le h2 h1
  · intro c hc
    have hc0 : (0 : ℝ) < c := by linarith
    have hlt : (1 : ℝ) / (4 * c) < 1 / 8 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    obtain ⟨A, hA1, hA2⟩ := exists_between hlt
    have hA0 : (0 : ℝ) < A := by
      have : (0 : ℝ) < 1 / (4 * c) := by positivity
      linarith
    have hAc : 1 / (4 * A) < c := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hA1
      linarith
    have hupper := eventually_rvRate_crit_le_profile hA0 (eventually_le_rvCumulant_crit hA2)
    have hprof := (tendsto_critUpperProfile hA0).comp tendsto_logInv_atTop
    have hev := hprof.eventually (eventually_lt_nhds hAc)
    filter_upwards [hupper, hev] with q h1 h2
    exact lt_of_le_of_lt h1 h2

end

end HTGeometry
