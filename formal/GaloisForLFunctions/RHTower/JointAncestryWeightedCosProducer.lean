import GaloisForLFunctions.RHTower.JointAncestryWeightedProducer

/-!
# A doubly exponential dressing: budget `y^{1/(log log y)^θ}`

The dressing `g_κ(s) = exp(|κ|(1 − cos 3(s − ½)))` is entire, real on the real axis and even about
`½`.  At a zero `ρ = ½ + a + iγ`, `|a| < ½`,
`Re cos 3(ρ − ½) = cos(3a) cosh(3γ) ≥ cos(3/2) cosh(3γ)`, with `cos(3/2) > 0` since `3/2 < π/2`.
So `|g_κ(ρ)| ≤ e^{|κ|} exp(−|κ| cos(3/2) cosh 3γ)`, which decays doubly exponentially in the
height.  On the critical line `g_κ(½ + iγ) = exp(|κ|(1 − cosh 3γ)) > 0`.

**Theorem** (`exists_cosWeighted_positive_budget`).  There is `κ₀ > 0` such that for every
`0 < |κ| ≤ κ₀` and every `θ' > 2/3`, for all large `y` the `g_κ`-weighted JAS tests are positive at
every level `σ` on every finite set of primes `p > y` with
`Σ_P p^{−(σ−½)} ≤ exp(log y/(log log y)^{θ'})`.

The proof takes `T = log B` in the height split.  The tail above `T` is `≤ exp(−c e^{3T}) = exp(−c B³)`,
which beats `e^B`.  Below `T`, the Vinogradov–Korobov width `(log T)^{−θ} = (log log B)^{−θ}`
beats `log B / log y` as soon as `log B ≤ log y/(log log y)^{θ'}` with `θ' > θ > 2/3`.

So the weighted producer reaches every budget `y^{1/(log log y)^{θ'}}`, `θ' > 2/3`, while a budget
`y^λ` with fixed `λ > 0` is equivalent to a zero-free half-plane.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

theorem cos_three_halves_pos : 0 < Real.cos (3 / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩

theorem re_cos_add_mul_I (x y : ℝ) : (Complex.cos (x + y * I)).re = Real.cos x * Real.cosh y := by
  rw [Complex.cos_add_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

theorem three_mul_sub_half_eq (s : ℂ) :
    3 * (s - 1 / 2) = ((3 * (s.re - 1 / 2) : ℝ) : ℂ) + ((3 * s.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- `Re cos 3(ρ − ½) ≥ cos(3/2) cosh(3 Im ρ)` at every zero. -/
theorem re_cos_three_mul_sub_half_ge (q : XiZeroCopy) :
    Real.cos (3 / 2) * Real.cosh (3 * (q.1 : ℂ).im) ≤
      (Complex.cos (3 * ((q.1 : ℂ) - 1 / 2))).re := by
  rw [three_mul_sub_half_eq, re_cos_add_mul_I]
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hx : |3 * ((q.1 : ℂ).re - 1 / 2)| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hc : Real.cos (3 / 2) ≤ Real.cos (3 * ((q.1 : ℂ).re - 1 / 2)) := by
    rw [← Real.cos_abs (3 * ((q.1 : ℂ).re - 1 / 2))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three]) hx
  exact mul_le_mul_of_nonneg_right hc (Real.cosh_pos _).le

/-- The dressing `g_κ(s) = exp(|κ|(1 − cos 3(s − ½)))`. -/
def cosDressing (κ : ℝ) : LagDressing where
  g s := Complex.exp (|κ| * (1 - Complex.cos (3 * (s - 1 / 2))))
  K := Real.exp |κ|
  K_nonneg := (Real.exp_pos _).le
  norm_le q := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (((|κ| : ℝ) : ℂ) * (1 - Complex.cos (3 * ((q.1 : ℂ) - 1 / 2)))).re =
        |κ| * (1 - (Complex.cos (3 * ((q.1 : ℂ) - 1 / 2))).re) := by
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
    rw [hre]
    have h1 := re_cos_three_mul_sub_half_ge q
    have h2 : 0 ≤ Real.cos (3 / 2) * Real.cosh (3 * (q.1 : ℂ).im) :=
      mul_nonneg cos_three_halves_pos.le (Real.cosh_pos _).le
    have h3 := abs_nonneg κ
    nlinarith
  ne_zero q := Complex.exp_ne_zero _
  conj_eq s := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, map_sub, map_one, ← Complex.cos_conj]
    congr 3
    simp [map_ofNat]
  reflect_eq s := by
    congr 2
    rw [show (3 : ℂ) * (1 - s - 1 / 2) = -(3 * (s - 1 / 2)) by ring, Complex.cos_neg]

theorem norm_cosDressing_g_le (κ : ℝ) (q : XiZeroCopy) :
    ‖(cosDressing κ).g (q.1 : ℂ)‖ ≤
      Real.exp |κ| * Real.exp (-(|κ| * (Real.cos (3 / 2) * Real.cosh (3 * (q.1 : ℂ).im)))) := by
  change ‖Complex.exp (|κ| * (1 - Complex.cos (3 * ((q.1 : ℂ) - 1 / 2))))‖ ≤ _
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((|κ| : ℝ) : ℂ) * (1 - Complex.cos (3 * ((q.1 : ℂ) - 1 / 2)))).re =
      |κ| * (1 - (Complex.cos (3 * ((q.1 : ℂ) - 1 / 2))).re) := by
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  rw [hre]
  have h1 := re_cos_three_mul_sub_half_ge q
  have h3 := abs_nonneg κ
  nlinarith

/-- Above height `T ≥ 0`: `|g_κ(ρ)| ≤ e^{|κ|} exp(−|κ| cos(3/2) e^{3T}/2)`. -/
theorem norm_cosDressing_g_le_of_lt (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (q : XiZeroCopy)
    (hq : T < |(q.1 : ℂ).im|) :
    ‖(cosDressing κ).g (q.1 : ℂ)‖ ≤
      Real.exp |κ| * Real.exp (-(|κ| * Real.cos (3 / 2) * Real.exp (3 * T) / 2)) := by
  refine (norm_cosDressing_g_le κ q).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  apply Real.exp_le_exp.mpr
  have hc := cos_three_halves_pos
  have hcosh : Real.exp (3 * T) / 2 ≤ Real.cosh (3 * (q.1 : ℂ).im) := by
    have h1 : Real.cosh (3 * T) ≤ Real.cosh (3 * (q.1 : ℂ).im) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3),
        abs_of_nonneg hT]
      linarith
    have h2 : Real.exp (3 * T) / 2 ≤ Real.cosh (3 * T) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(3 * T))]
    linarith
  have h3 := abs_nonneg κ
  have h4 := mul_le_mul_of_nonneg_left hcosh (mul_nonneg h3 hc.le)
  nlinarith

theorem cosDressing_positiveOnLine (κ : ℝ) : (cosDressing κ).PositiveOnLine := by
  intro q hq
  change 0 < (Complex.exp (|κ| * (1 - Complex.cos (3 * ((q.1 : ℂ) - 1 / 2))))).re
  have e : 3 * ((q.1 : ℂ) - 1 / 2) = ((0 : ℝ) : ℂ) + ((3 * (q.1 : ℂ).im : ℝ) : ℂ) * I := by
    rw [three_mul_sub_half_eq, hq]; simp
  have hcos : Complex.cos (3 * ((q.1 : ℂ) - 1 / 2)) = (Real.cosh (3 * (q.1 : ℂ).im) : ℂ) := by
    rw [e, Complex.cos_add_mul_I]
    simp only [Complex.ofReal_zero, Complex.cos_zero, Complex.sin_zero, one_mul, zero_mul,
      sub_zero]
    rw [Complex.ofReal_cosh]
  rw [hcos, show ((|κ| : ℝ) : ℂ) * (1 - (Real.cosh (3 * (q.1 : ℂ).im) : ℂ)) =
    ((|κ| * (1 - Real.cosh (3 * (q.1 : ℂ).im)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Complex.ofReal_re]
  exact Real.exp_pos _

/-- `Φ_{g_κ}(0) → Φ(0)` as `κ → 0`. -/
theorem tendsto_dLagReal_cosDressing_zero :
    Tendsto (fun κ : ℝ => dLagReal (cosDressing κ) 0) (𝓝 0) (𝓝 poleSharpConstant) := by
  have hlim : Tendsto (fun κ : ℝ => ∑' q : XiZeroCopy, (cosDressing κ).weight q) (𝓝 0)
      (𝓝 (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun q =>
      Real.exp 1 * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
      (summable_inv_mul_one_sub.norm.mul_left _) (fun q => ?_) ?_
    · have hc : Continuous fun κ : ℝ => (cosDressing κ).weight q := by
        unfold LagDressing.weight
        change Continuous fun κ : ℝ =>
          Complex.exp (|κ| * (1 - Complex.cos (3 * ((q.1 : ℂ) - 1 / 2)))) /
            ((q.1 : ℂ) * (1 - (q.1 : ℂ)))
        fun_prop
      have := hc.tendsto 0
      convert this using 2
      change 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        Complex.exp (|(0 : ℝ)| * (1 - Complex.cos (3 * ((q.1 : ℂ) - 1 / 2)))) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))
      simp
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with κ hκ q
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hκ
      refine ((cosDressing κ).norm_weight_le q).trans ?_
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hκ.le) (norm_nonneg _)
  have h1 := (Complex.continuous_re.tendsto _).comp hlim
  rw [tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_re] at h1
  refine h1.congr fun κ => ?_
  simp only [Function.comp]
  unfold dLagReal
  rw [dLag_zero]

theorem exists_cosDressing_dLagReal_zero_ge :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, |κ| ≤ κ₀ → poleSharpConstant / 2 ≤ dLagReal (cosDressing κ) 0 := by
  have hΦ := poleSharpConstant_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (tendsto_dLagReal_cosDressing_zero.eventually (Ioi_mem_nhds (show poleSharpConstant / 2 <
      poleSharpConstant by linarith)))
  refine ⟨δ / 2, by positivity, fun κ hκ => ?_⟩
  have : dist κ 0 < δ := by rw [Real.dist_eq, sub_zero]; linarith
  exact (hball this).le

/-! ## Asymptotics -/

/-- `v (log v)^{−a} → ∞`. -/
theorem tendsto_mul_log_rpow_neg_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun v : ℝ => v * Real.log v ^ (-a)) atTop atTop := by
  have hr : (0 : ℝ) < 1 / (2 * a) := by positivity
  have hlo := (isLittleO_log_rpow_atTop hr).bound (show (0 : ℝ) < 1 by norm_num)
  refine tendsto_atTop_mono' _ ?_ (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hlo, eventually_ge_atTop (Real.exp 1)] with v hv hv1
  have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos 1) hv1
  have hlog : 1 ≤ Real.log v := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hv1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (Real.rpow_nonneg hv0.le _), one_mul] at hv
  have h1 : Real.log v ^ a ≤ v ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow (by linarith) hv ha.le
    rwa [← Real.rpow_mul hv0.le, show 1 / (2 * a) * a = 1 / 2 by field_simp] at this
  have hla : 0 < Real.log v ^ a := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hla]
  have e : v = v ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hv0]; norm_num
  calc v ^ (1 / 2 : ℝ) * Real.log v ^ a ≤ v ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hv0.le _)
    _ = v := e.symm

/-- The asymptotic conditions of the cos producer, in `v = log y` and `L = v (log v)^{−θ'}`. -/
theorem eventually_cos_budget_conditions {θ θ' η₀ t₁ K₀ c H : ℝ} (hθ : 0 < θ) (hθθ' : θ < θ')
    (hη₀ : 0 < η₀) (ht₁ : 0 < t₁) (hK₀ : 0 < K₀) (hc : 0 < c) :
    ∀ᶠ v : ℝ in atTop, Real.exp 1 ≤ v ∧ H ≤ v * Real.log v ^ (-θ') ∧
      1 < v * Real.log v ^ (-θ') ∧ v * Real.log v ^ (-θ') ≤ v ∧
      Real.log (v * Real.log v ^ (-θ')) ^ (-θ) ≤ η₀ ∧
      Real.exp (-(v * Real.log v ^ (-θ))) * Real.exp (v * Real.log v ^ (-θ')) ≤ t₁ ∧
      Real.exp (Real.exp (v * Real.log v ^ (-θ'))) *
        Real.exp (-(c * Real.exp (3 * (v * Real.log v ^ (-θ'))) / 2)) ≤ K₀ := by
  have hθ'0 : 0 < θ' := by linarith
  have hL := tendsto_mul_log_rpow_neg_atTop hθ'0
  have hM := tendsto_mul_log_rpow_neg_atTop hθ
  have hlogv := Real.tendsto_log_atTop
  -- `(log v)^{θ − θ'} ≤ 1/2` eventually
  have hratio : ∀ᶠ v : ℝ in atTop, Real.log v ^ (θ - θ') ≤ 1 / 2 :=
    hlogv.eventually ((tendsto_rpow_neg_atTop (show 0 < θ' - θ by linarith)).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)) |>.mono fun x hx => by
        rwa [show -(θ' - θ) = θ - θ' by ring] at hx)
  -- conditions on `L` alone
  have hLlog : ∀ᶠ L : ℝ in atTop, Real.log L ^ (-θ) ≤ η₀ :=
    hlogv.eventually ((tendsto_rpow_neg_atTop hθ).eventually (ge_mem_nhds hη₀))
  have hLtail : ∀ᶠ L : ℝ in atTop,
      Real.exp (Real.exp L) * Real.exp (-(c * Real.exp (3 * L) / 2)) ≤ K₀ := by
    have hX : Tendsto (fun L : ℝ => Real.exp L * (c * Real.exp (2 * L) / 2 - 1)) atTop atTop := by
      refine Tendsto.atTop_mul_atTop₀ Real.tendsto_exp_atTop ?_
      refine tendsto_atTop_add_const_right _ _ ?_
      refine Tendsto.atTop_div_const (by norm_num) (Tendsto.const_mul_atTop hc ?_)
      exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hX)
    filter_upwards [h2.eventually (ge_mem_nhds hK₀)] with L hL'
    simp only [Function.comp] at hL'
    refine le_trans (le_of_eq ?_) hL'
    rw [← Real.exp_add]
    congr 1
    have e : Real.exp (3 * L) = Real.exp L * Real.exp (2 * L) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]; ring
  have hdecay : ∀ᶠ v : ℝ in atTop, Real.exp (-(v * Real.log v ^ (-θ) / 2)) ≤ t₁ := by
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hM.atTop_div_const
      (show (0 : ℝ) < 2 by norm_num)))
    filter_upwards [h2.eventually (ge_mem_nhds ht₁)] with v hv
    simpa [Function.comp] using hv
  filter_upwards [eventually_ge_atTop (Real.exp 1), hL.eventually_ge_atTop H,
    hL.eventually_gt_atTop 1, hL.eventually hLlog, hL.eventually hLtail, hratio, hdecay]
    with v hv1 hvH hvL1 hvlog hvtail hvr hvd
  have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos 1) hv1
  have hlog : 1 ≤ Real.log v := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hv1
  have hLv : v * Real.log v ^ (-θ') ≤ v := by
    have : Real.log v ^ (-θ') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)
    nlinarith
  refine ⟨hv1, hvH, hvL1, hLv, hvlog, ?_, hvtail⟩
  -- the low-height condition
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = v * Real.log v ^ (-θ') := ⟨_, rfl⟩
  rw [← hLdef] at hvL1 hLv ⊢
  have h2 : L ≤ v * Real.log v ^ (-θ) / 2 := by
    have e : Real.log v ^ (-θ') = Real.log v ^ (-θ) * Real.log v ^ (θ - θ') := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    rw [hLdef, e]
    have hp : 0 ≤ v * Real.log v ^ (-θ) := mul_nonneg hv0.le (Real.rpow_nonneg (by linarith) _)
    nlinarith
  rw [← Real.exp_add]
  refine le_trans (Real.exp_le_exp.mpr ?_) hvd
  linarith

/-! ## The producer -/

theorem width_of_vk_le {θ t₀ η₀ T : ℝ} (hθ0 : 0 < θ) (ht₀ : 1 < t₀)
    (hvk : ∀ q : XiZeroCopy, t₀ ≤ |(q.1 : ℂ).im| →
      |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - 1 * Real.log |(q.1 : ℂ).im| ^ (-θ))
    (hlow : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ t₀ → |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - η₀)
    (hω : Real.log T ^ (-θ) ≤ η₀) (q : XiZeroCopy) (hq : |(q.1 : ℂ).im| ≤ T) :
    Real.log T ^ (-θ) ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2| := by
  rcases le_or_gt t₀ |(q.1 : ℂ).im| with h0 | h0
  · have h1 := hvk q h0
    have hlog0 : 0 < Real.log |(q.1 : ℂ).im| := Real.log_pos (by linarith)
    have hlogT : Real.log |(q.1 : ℂ).im| ≤ Real.log T := Real.log_le_log (by linarith) hq
    have h2 : Real.log T ^ (-θ) ≤ Real.log |(q.1 : ℂ).im| ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos hlog0 hlogT (by linarith)
    linarith
  · linarith [hlow q h0.le]

theorem cosDressing_tail_le {κ L K₀ : ℝ}
    (hK : Real.exp (Real.exp L) * Real.exp (-(|κ| * Real.cos (3 / 2) * Real.exp (3 * L) / 2)) ≤ K₀)
    (hK₀def : K₀ = poleSharpConstant / (4 * (Real.exp |κ| * lagWeightTotal))) :
    (Real.exp (Real.exp L) - 1) *
      (Real.exp |κ| * Real.exp (-(|κ| * Real.cos (3 / 2) * Real.exp (3 * L) / 2)) * lagWeightTotal) ≤
        poleSharpConstant / 4 := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (Real.exp L) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = Real.exp (-(|κ| * Real.cos (3 / 2) * Real.exp (3 * L) / 2)) :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = Real.exp |κ| * lagWeightTotal := ⟨_, rfl⟩
  rw [← hE, ← hF] at hK ⊢
  have hG0 : 0 < G := by rw [hG]; exact mul_pos (Real.exp_pos _) lagWeightTotal_pos
  have hF0 : 0 ≤ F := by rw [hF]; exact (Real.exp_pos _).le
  have e1 : (E - 1) * (Real.exp |κ| * F * lagWeightTotal) = G * ((E - 1) * F) := by
    rw [hG]; ring
  rw [e1]
  have h1 : G * ((E - 1) * F) ≤ G * K₀ := by
    refine mul_le_mul_of_nonneg_left ?_ hG0.le
    nlinarith
  have h2 : G * K₀ = poleSharpConstant / 4 := by
    rw [hK₀def, ← hG]; field_simp
  linarith

/-- **The doubly-exponentially weighted JAS producer.**  There is `κ₀ > 0` such that for every
`0 < |κ| ≤ κ₀` and every `θ' > 2/3`, for all large `y` the `g_κ`-weighted tests are positive at
every level `σ` on every finite set of primes `p > y` with budget
`Σ_P p^{−(σ−½)} ≤ exp(log y · (log log y)^{−θ'})`. -/
theorem exists_cosWeighted_positive_budget :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < |κ| → |κ| ≤ κ₀ → ∀ θ' : ℝ, 2 / 3 < θ' →
      ∃ Y : ℝ, 1 < Y ∧ ∀ (σ y : ℝ), Y ≤ y → ∀ P : Finset Nat.Primes,
        (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
        ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤
          Real.exp (Real.log y * Real.log (Real.log y) ^ (-θ')) →
        ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
          (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
            (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * (cosDressing κ).weight q).re := by
  obtain ⟨κ₀, hκ₀, hΦ⟩ := exists_cosDressing_dLagReal_zero_ge
  refine ⟨κ₀, hκ₀, fun κ hκ0 hκ θ' hθ' => ?_⟩
  have hΦ0 : poleSharpConstant / 2 ≤ dLagReal (cosDressing κ) 0 := hΦ κ hκ
  have hpsc := poleSharpConstant_pos
  have hV := (cosDressing κ).total_nonneg
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = (2 / 3 + θ') / 2 := ⟨_, rfl⟩
  have hθ : 2 / 3 < θ := by rw [hθdef]; linarith
  have hθθ' : θ < θ' := by rw [hθdef]; linarith
  have hθ0 : 0 < θ := by linarith
  obtain ⟨t₀, ht₀, hvk⟩ := exists_powerLog_width_vk hθ
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width_at t₀
  obtain ⟨t₁, ht₁def⟩ : ∃ t : ℝ,
      t = Real.log (1 + poleSharpConstant / (4 * ((cosDressing κ).total + 1))) := ⟨_, rfl⟩
  have hq0 : 0 < poleSharpConstant / (4 * ((cosDressing κ).total + 1)) := by positivity
  have ht₁ : 0 < t₁ := by rw [ht₁def]; exact Real.log_pos (by linarith)
  have hexpt : (Real.exp t₁ - 1) * (cosDressing κ).total ≤ dLagReal (cosDressing κ) 0 / 2 := by
    rw [ht₁def, Real.exp_log (by linarith), add_sub_cancel_left]
    have h1 : poleSharpConstant / (4 * ((cosDressing κ).total + 1)) * (cosDressing κ).total ≤
        poleSharpConstant / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨K₀, hK₀def⟩ : ∃ K : ℝ, K = poleSharpConstant / (4 * (Real.exp |κ| * lagWeightTotal)) :=
    ⟨_, rfl⟩
  have hK₀ : 0 < K₀ := by rw [hK₀def]; have := lagWeightTotal_pos; positivity
  have hc : 0 < |κ| * Real.cos (3 / 2) := mul_pos hκ0 cos_three_halves_pos
  obtain ⟨v₀, hv₀⟩ := eventually_atTop.mp (eventually_cos_budget_conditions (H := t₀) hθ0 hθθ'
    hη₀ ht₁ hK₀ hc)
  refine ⟨Real.exp (max v₀ 1), by linarith [Real.add_one_le_exp (max v₀ 1), le_max_right v₀ 1],
    fun σ y hy P hP hB z => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hvge : max v₀ 1 ≤ Real.log y := by
    rw [← Real.log_exp (max v₀ 1)]; exact Real.log_le_log (Real.exp_pos _) hy
  obtain ⟨hv1, hLt, hL1, hLv, hω, hC3, hC4⟩ := hv₀ (Real.log y) (le_trans (le_max_left _ _) hvge)
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log y * Real.log (Real.log y) ^ (-θ') := ⟨_, rfl⟩
  rw [← hLdef] at hLt hL1 hLv hω hC3 hC4 hB
  have hv0 : 0 < Real.log y := lt_of_lt_of_le (Real.exp_pos 1) hv1
  have hlogv : 1 ≤ Real.log (Real.log y) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hv1
  have hlogL0 : 0 < Real.log L := Real.log_pos hL1
  have hlogLv : Real.log L ≤ Real.log (Real.log y) := Real.log_le_log (by linarith) hLv
  have hωv : Real.log (Real.log y) ^ (-θ) ≤ Real.log L ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos hlogL0 hlogLv (by linarith)
  have hlow' : Real.exp (-(Real.log L ^ (-θ) * Real.log y)) * Real.exp L ≤ t₁ := by
    refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le) hC3
    nlinarith
  have htail := cosDressing_tail_le hC4 hK₀def
  exact weightedAggregate_re_nonneg_of_heightSplit (cosDressing κ) hy0
    (Real.rpow_nonneg hlogL0.le _) P hP hB
    (width_of_vk_le hθ0 ht₀ hvk (fun q hq => hlow q hq) hω)
    (fun q hq => norm_cosDressing_g_le_of_lt κ (by linarith) q hq) (by positivity)
    ht₁.le hexpt hlow' (by linarith) z

end

end RHTower
