import GaloisForLFunctions.RHTower.XiCenteredHeatBounds
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation

/-!
# The centered heat trace rises at every off-line zero

Let `z_q = −i(ρ_q − ½)` run over the Xi divisor with multiplicity, fix one copy with
`δ = |Im z_{q₀}| > 0` and centre `c = Re z_{q₀}` (its ordinate). The centered heat trace

  `H(t) = Re Σ_q e^{−t(z_q − c)²}`

is bounded by `B = 6(1 + c²)` at `t = 2`, and its exterior part (`|Re z_q − c| > 1`) is bounded by
`B` at every `t ≥ 1`. The finitely many copies of the unit window `|Re z_q − c| ≤ 1` are aligned by
Dirichlet recurrence: at some `t = kT`, `1 ≤ k ≤ 8^N`, every head phase `cos(2t r_q e_q)` is
nonnegative, and the selected copy alone gives `e^{tδ²} ≥ 4B + 4` once `T = δ⁻² log(4B + 4)`. No
depth comparison between distinct zeros is used: deeper neighbours only help.

The mean-value theorem then produces `s ∈ (2, U)`, `U = T 8^N`, with

  `Re Σ_q (z_q − c)² e^{−s(z_q − c)²} < −2/U`      (`exists_re_xiCenteredHeatMoment_lt`),

the negative heat derivative. `N` is the number of copies in the unit window, which the local zero
count bounds logarithmically in the height.
-/

open Complex Filter Set Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower

/-- The heat moment `Σ_q (z_q − c)² e^{−t(z_q − c)²}`, minus the time derivative of the heat
trace. -/
def xiCenteredHeatMoment (c t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (xiSpectralPoint q - c) ^ 2 * xiCenteredHeatTerm c t q

/-- The recurrence step `T = δ⁻² log(4B + 4)`. -/
def heatRecurrenceStep (c δ : ℝ) : ℝ := Real.log (4 * xiCenteredHeatBaseBound c + 4) / δ ^ 2

/-- The recurrence horizon `U = T · 8^N`, `N` the number of copies in the unit window at `c`. -/
def heatRecurrenceHorizon (c δ : ℝ) : ℝ :=
  heatRecurrenceStep c δ * 8 ^ (xiOrdinateWindow 1 c).ncard

theorem xiSpectralPoint_re (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint, Complex.mul_re]

/-! ### The time derivative -/

theorem hasDerivAt_xiCenteredHeatTerm (c : ℝ) (q : XiZeroCopy) (x : ℝ) :
    HasDerivAt (fun t : ℝ => xiCenteredHeatTerm c t q)
      (-((xiSpectralPoint q - c) ^ 2 * xiCenteredHeatTerm c x q)) x := by
  set w : ℂ := (xiSpectralPoint q - c) ^ 2
  have h1 : HasDerivAt (fun t : ℝ => -(t : ℂ) * w) (-w) x := by
    have := ((hasDerivAt_id x).ofReal_comp).neg.mul_const w
    simpa using this
  have h2 := h1.cexp
  unfold xiCenteredHeatTerm
  convert h2 using 1
  ring

/-- **The heat derivative.** On `t > 1`, `H'(t) = −Re Σ_q (z_q − c)² e^{−t(z_q − c)²}`. -/
theorem hasDerivAt_xiCenteredHeatTraceReal (c : ℝ) {y : ℝ} (hy : 1 < y) :
    HasDerivAt (xiCenteredHeatTraceReal c) (-(xiCenteredHeatMoment c y).re) y := by
  set V := y + 1
  have hmem : y ∈ Ioo 1 V := ⟨hy, by linarith⟩
  have hdom : ∀ (q : XiZeroCopy) (x : ℝ), x ∈ Ioo 1 V →
      ‖-((xiSpectralPoint q - c) ^ 2 * xiCenteredHeatTerm c x q)‖ ≤
        (15 * (1 + c ^ 2) * Real.exp (V / 4)) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    intro q x hx
    rw [norm_neg]
    refine (norm_xiCenteredHeatMomentTerm_le hx.1.le c q).trans ?_
    gcongr
    exact hx.2.le
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (xiSpectralPoint_inv_sq_summable.mul_left (15 * (1 + c ^ 2) * Real.exp (V / 4)))
    isOpen_Ioo isPreconnected_Ioo (fun q x _ => hasDerivAt_xiCenteredHeatTerm c q x) hdom hmem
    (summable_xiCenteredHeatTerm hy.le c) hmem
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hsum
  rw [tsum_neg] at hre
  simpa [xiCenteredHeatTraceReal, xiCenteredHeatTrace, xiCenteredHeatMoment] using hre

/-! ### Bounds at the base time and at a recurrence time -/

/-- At `t = 2` the heat trace is bounded by `B = 6(1 + c²)`. -/
theorem xiCenteredHeatTraceReal_two_le (c : ℝ) :
    xiCenteredHeatTraceReal c 2 ≤ xiCenteredHeatBaseBound c := by
  have hsum := (summable_xiCenteredHeatTerm (t := 2) (by norm_num) c).norm
  have hle : (∑' q, ‖xiCenteredHeatTerm c 2 q‖) ≤
      3 * (1 + c ^ 2) * Real.exp (2 / 4) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum (norm_xiCenteredHeatTerm_le (by norm_num) c)
      (xiSpectralPoint_inv_sq_summable.mul_left _)
  have hS := xiCenteredHeat_reciprocal_mass_lt_one
  have hS0 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
    tsum_nonneg fun _ => by positivity
  have he : Real.exp (2 / 4 : ℝ) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp (2 / 4 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (2 / 4 : ℝ)]
  have hc : 0 ≤ 3 * (1 + c ^ 2) := by positivity
  calc xiCenteredHeatTraceReal c 2 ≤ ‖xiCenteredHeatTrace c 2‖ := Complex.re_le_norm _
    _ ≤ ∑' q, ‖xiCenteredHeatTerm c 2 q‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ 3 * (1 + c ^ 2) * Real.exp (2 / 4) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := hle
    _ ≤ 3 * (1 + c ^ 2) * 2 * 1 := by gcongr
    _ = xiCenteredHeatBaseBound c := by unfold xiCenteredHeatBaseBound; ring

/-- **Aligned head.** If every copy in the unit window has a nonnegative heat phase at time
`t ≥ 1`, the trace is at least `e^{tδ²} − B` for any copy `q₀` at the centre. -/
theorem exp_sub_le_xiCenteredHeatTraceReal {c t : ℝ} (ht : 1 ≤ t) {q₀ : XiZeroCopy}
    (hq₀ : (xiSpectralPoint q₀).re = c)
    (hphase : ∀ q ∈ xiOrdinateWindow 1 c,
      0 ≤ Real.cos (-2 * t * ((xiSpectralPoint q).re - c) * (xiSpectralPoint q).im)) :
    Real.exp (t * (xiSpectralPoint q₀).im ^ 2) - xiCenteredHeatBaseBound c ≤
      xiCenteredHeatTraceReal c t := by
  classical
  set W := xiOrdinateWindow 1 c
  have hsum := summable_xiCenteredHeatTerm ht c
  have hW : ∀ q, q ∈ W ↔ |(xiSpectralPoint q).re - c| ≤ 1 := fun q => by
    rw [xiSpectralPoint_re]; exact Iff.rfl
  set f : XiZeroCopy → ℝ := fun q => (xiCenteredHeatTerm c t q).re
  set hd : XiZeroCopy → ℝ := fun q => if q ∈ W then f q else 0
  set tl : XiZeroCopy → ℝ := fun q => if q ∈ W then 0 else f q
  have hsplit : ∀ q, f q = hd q + tl q := fun q => by
    simp only [hd, tl]; split_ifs <;> simp
  have hfabs : ∀ q, |f q| ≤ ‖xiCenteredHeatTerm c t q‖ := fun q => Complex.abs_re_le_norm _
  have hhd_s : Summable hd := Summable.of_norm_bounded hsum.norm fun q => by
    simp only [hd, Real.norm_eq_abs]; split_ifs
    · exact hfabs q
    · simp
  have htl_s : Summable tl := Summable.of_norm_bounded hsum.norm fun q => by
    simp only [tl, Real.norm_eq_abs]; split_ifs
    · simp
    · exact hfabs q
  have hhd0 : ∀ q, 0 ≤ hd q := fun q => by
    simp only [hd, f]; split_ifs with h
    · rw [re_xiCenteredHeatTerm]
      exact mul_nonneg (Real.exp_pos _).le (hphase q h)
    · exact le_rfl
  have hq₀W : q₀ ∈ W := (hW q₀).mpr (by rw [hq₀, sub_self, abs_zero]; norm_num)
  have hhead : Real.exp (t * (xiSpectralPoint q₀).im ^ 2) ≤ ∑' q, hd q := by
    have h := hhd_s.le_tsum q₀ (fun q _ => hhd0 q)
    have hval : hd q₀ = Real.exp (t * (xiSpectralPoint q₀).im ^ 2) := by
      simp only [hd, f, if_pos hq₀W]
      rw [re_xiCenteredHeatTerm, hq₀]
      simp
    linarith
  have htail : -xiCenteredHeatBaseBound c ≤ ∑' q, tl q := by
    have hle : ∀ q, |tl q| ≤ ‖xiCenteredHeatTerm c 1 q‖ := fun q => by
      simp only [tl]; split_ifs with h
      · simp
      · refine (hfabs q).trans (norm_xiCenteredHeatTerm_le_one_of_far ht q ?_)
        have : ¬ |(xiSpectralPoint q).re - c| ≤ 1 := fun h' => h ((hW q).mpr h')
        linarith [not_le.mp this]
    have h1 : |∑' q, tl q| ≤ ∑' q, ‖xiCenteredHeatTerm c 1 q‖ := by
      have hn : Summable fun q => ‖tl q‖ := htl_s.norm
      calc |∑' q, tl q| = ‖∑' q, tl q‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' q, ‖tl q‖ := norm_tsum_le_tsum_norm hn
        _ ≤ ∑' q, ‖xiCenteredHeatTerm c 1 q‖ :=
          hn.tsum_le_tsum (fun q => by rw [Real.norm_eq_abs]; exact hle q)
            (summable_xiCenteredHeatTerm le_rfl c).norm
    have h2 := tsum_norm_xiCenteredHeatTerm_one_le c
    have h3 := neg_abs_le (∑' q, tl q)
    linarith
  have htot : xiCenteredHeatTraceReal c t = ∑' q, hd q + ∑' q, tl q := by
    rw [← hhd_s.tsum_add htl_s]
    unfold xiCenteredHeatTraceReal xiCenteredHeatTrace
    rw [Complex.re_tsum hsum]
    exact tsum_congr hsplit
  linarith

/-! ### Recurrence -/

theorem two_mul_pi_sq_div_sixtyFour_le : 2 * Real.pi ^ 2 / (8 : ℝ) ^ 2 ≤ 1 := by
  have h := Real.pi_lt_d2
  have hp := Real.pi_pos
  nlinarith

/-- **Dirichlet alignment of the unit window.** For every step `T`, some `t = kT`,
`1 ≤ k ≤ 8^N`, makes every heat phase of the unit window nonnegative. -/
theorem exists_aligned_heat_time (c T : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 8 ^ (xiOrdinateWindow 1 c).ncard ∧
      ∀ q ∈ xiOrdinateWindow 1 c, 0 ≤ Real.cos
        (-2 * (k * T) * ((xiSpectralPoint q).re - c) * (xiSpectralPoint q).im) := by
  classical
  have hfin := finite_xiOrdinateWindow 1 c
  set s := hfin.toFinset
  obtain ⟨k, hk1, hk8, hcos⟩ := HTGeometry.exists_dirichlet_phase
    (fun q : s => -2 * ((xiSpectralPoint q.1).re - c) * (xiSpectralPoint q.1).im) T 8
    (by norm_num)
  have hcard : Fintype.card s = (xiOrdinateWindow 1 c).ncard := by
    rw [Fintype.card_coe, Set.ncard_eq_toFinset_card _ hfin]
  refine ⟨k, hk1, hcard ▸ hk8, fun q hq => ?_⟩
  have hqs : q ∈ s := hfin.mem_toFinset.mpr hq
  have h := (hcos ⟨q, hqs⟩).1
  have hpi := two_mul_pi_sq_div_sixtyFour_le
  push_cast at h
  have e : -2 * ((xiSpectralPoint q).re - c) * (xiSpectralPoint q).im * (k * T) =
      -2 * (k * T) * ((xiSpectralPoint q).re - c) * (xiSpectralPoint q).im := by ring
  rw [e] at h
  linarith

theorem three_lt_log_twentyEight : 3 < Real.log 28 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have h0 := Real.exp_pos 1
  nlinarith [pow_le_pow_left₀ h0.le h.le 3]

theorem twelve_lt_heatRecurrenceStep (c : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ^ 2 < 1 / 4) :
    12 < heatRecurrenceStep c δ := by
  unfold heatRecurrenceStep
  have hB : 6 ≤ xiCenteredHeatBaseBound c := by
    unfold xiCenteredHeatBaseBound; nlinarith [sq_nonneg c]
  have hlog : 3 < Real.log (4 * xiCenteredHeatBaseBound c + 4) :=
    three_lt_log_twentyEight.trans_le (Real.log_le_log (by norm_num) (by linarith))
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- **An off-line zero makes the heat moment negative at a bounded time.** For every copy `q₀`
with `δ = |Im z_{q₀}| > 0` there is `s ∈ (2, U)`, `U` the recurrence horizon, with
`Re Σ_q (z_q − c)² e^{−s(z_q − c)²} < −2/U`, `c = Re z_{q₀}`. -/
theorem exists_re_xiCenteredHeatMoment_lt (q₀ : XiZeroCopy) (hq₀ : (xiSpectralPoint q₀).im ≠ 0) :
    ∃ s : ℝ, 2 < s ∧
      s < heatRecurrenceHorizon (xiSpectralPoint q₀).re |(xiSpectralPoint q₀).im| ∧
      (xiCenteredHeatMoment (xiSpectralPoint q₀).re s).re <
        -(2 / heatRecurrenceHorizon (xiSpectralPoint q₀).re |(xiSpectralPoint q₀).im|) := by
  set c := (xiSpectralPoint q₀).re
  set δ := |(xiSpectralPoint q₀).im|
  set B := xiCenteredHeatBaseBound c
  set T := heatRecurrenceStep c δ
  set U := heatRecurrenceHorizon c δ
  have hδ0 : 0 < δ := abs_pos.mpr hq₀
  have hδsq : δ ^ 2 = (xiSpectralPoint q₀).im ^ 2 := sq_abs _
  have hδq : δ ^ 2 < 1 / 4 := hδsq ▸ xiSpectralPoint_im_sq_lt_quarter q₀
  have hT : 12 < T := twelve_lt_heatRecurrenceStep c hδ0 hδq
  obtain ⟨k, hk1, hk8, hcos⟩ := exists_aligned_heat_time c T
  set t := (k : ℝ) * T
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hTt : T ≤ t := by nlinarith
  have hk8' : (k : ℝ) ≤ 8 ^ (xiOrdinateWindow 1 c).ncard := by exact_mod_cast hk8
  have htU : t ≤ U := by
    simp only [t, U, heatRecurrenceHorizon]
    rw [mul_comm (k : ℝ) T]
    exact mul_le_mul_of_nonneg_left hk8' (by linarith)
  have ht1 : 1 ≤ t := by linarith
  -- the heat trace is large at the aligned time
  have hrise := exp_sub_le_xiCenteredHeatTraceReal ht1 (q₀ := q₀) rfl hcos
  have hB : 0 < B := xiCenteredHeatBaseBound_pos c
  have hexp : 4 * B + 4 ≤ Real.exp (t * (xiSpectralPoint q₀).im ^ 2) := by
    have hlog : Real.log (4 * B + 4) ≤ t * (xiSpectralPoint q₀).im ^ 2 := by
      rw [← hδsq]
      have hT' : T * δ ^ 2 = Real.log (4 * B + 4) := by
        simp only [T, heatRecurrenceStep]
        field_simp
      nlinarith [sq_nonneg δ]
    calc 4 * B + 4 = Real.exp (Real.log (4 * B + 4)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  have hbase := xiCenteredHeatTraceReal_two_le c
  -- the mean-value step on `[2, t]`
  have h2t : (2 : ℝ) < t := by linarith
  have hderiv : ∀ x ∈ Ioo 2 t, HasDerivAt (xiCenteredHeatTraceReal c)
      (-(xiCenteredHeatMoment c x).re) x :=
    fun x hx => hasDerivAt_xiCenteredHeatTraceReal c (by linarith [hx.1])
  have hcont : ContinuousOn (xiCenteredHeatTraceReal c) (Icc 2 t) := fun x hx =>
    (hasDerivAt_xiCenteredHeatTraceReal c (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope (xiCenteredHeatTraceReal c)
    (fun x => -(xiCenteredHeatMoment c x).re) h2t hcont hderiv
  refine ⟨s, hs.1, hs.2.trans_le htU, ?_⟩
  have hU0 : 0 < U := by linarith
  have hgap : 2 * B + 4 ≤ xiCenteredHeatTraceReal c t - xiCenteredHeatTraceReal c 2 := by
    linarith
  have hslope' : 2 / U < -(xiCenteredHeatMoment c s).re := by
    rw [hslope]
    have ht2 : 0 < t - 2 := by linarith
    calc 2 / U ≤ 2 / (t - 2) := div_le_div_of_nonneg_left (by norm_num) ht2 (by linarith)
      _ < (2 * B + 4) / (t - 2) := div_lt_div_of_pos_right (by linarith) ht2
      _ ≤ _ := div_le_div_of_nonneg_right hgap ht2.le
  linarith

end GaloisForLFunctions.SquareRootThreshold
