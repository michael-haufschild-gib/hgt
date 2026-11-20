import GaloisForLFunctions.HagedornBootstrap.EdgeFunction

/-!
# The shape of the zero law and the Cardy deficit

**Zero law.** Beyond the tip the zero density `ρ_U(x) = (4/3π) arcosh(sinh πx)` has slope
`ρ_U'(x) = (4/3) cosh πx/√(sinh²πx − 1)`, which decreases strictly and stays above `4/3`. Hence
`ρ_U` is strictly concave on `[x*, ∞)` and `(4/3)(x − x*) ≤ ρ_U(x) ≤ (4/3)x`: asymptotically the
double zeros of an optimal functional have density `4/3` per unit `x` on each lip.

**Cardy deficit.** On the real axis inside the lobe the extremal potential is
`U(x) = U₀ − (4/3)∫₀^{|x|} arcsin(sinh πs) ds`, normalized so that `U(x*) = −L(x*)` with the
Cardy line `L(x) = (2π/3)|x|`. Then

  `U(x) + L(x) = −(4/3) ∫_{|x|}^{x*} (π/2 − arcsin(sinh πs)) ds < 0`   for `|x| < x*`,

so every functional stays strictly below the Cardy line on the lobe interval. The deficit
`κ(δ) = −(U + L)(x* − δ)` is positive and increasing in `δ`, and `U₀ = −κ(x*)`.
-/

noncomputable section

open Real Set

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The zero law beyond the tip -/

/-- The slope of the zero law. -/
def zeroLawSlope (x : ℝ) : ℝ := 4 / 3 * Real.cosh (π * x) / √(Real.sinh (π * x) ^ 2 - 1)

theorem one_lt_sinh_of_tip_lt' {x : ℝ} (h : bootstrapTip < x) : 1 < Real.sinh (π * x) := by
  have hx : 0 < x := bootstrapTip_pos.trans h
  have := one_lt_sinh_of_tip_lt (x := x) (by rwa [abs_of_pos hx])
  rwa [abs_of_pos hx] at this

theorem hasDerivAt_zeroLaw {x : ℝ} (h : bootstrapTip < x) :
    HasDerivAt zeroLaw (zeroLawSlope x) x := by
  have hx : 0 < x := bootstrapTip_pos.trans h
  have hs := one_lt_sinh_of_tip_lt' h
  have hev : zeroLaw =ᶠ[nhds x] fun y => 4 / (3 * π) * Real.arcosh (Real.sinh (π * y)) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp [zeroLaw, abs_of_pos hy]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hsinh : HasDerivAt (fun y => Real.sinh (π * y)) (Real.cosh (π * x) * π) x := by
    have h := (Real.hasDerivAt_sinh (π * x)).comp x ((hasDerivAt_id x).const_mul π)
    exact h.congr_deriv (by simp)
  refine ((((Real.hasDerivAt_arcosh (mem_Ioi.mpr hs)).comp x hsinh)).const_mul (4 / (3 * π))).congr_deriv ?_
  unfold zeroLawSlope
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hq : 0 < √(Real.sinh (π * x) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  field_simp

theorem zeroLawSlope_pos {x : ℝ} (h : bootstrapTip < x) : 0 < zeroLawSlope x := by
  have hs := one_lt_sinh_of_tip_lt' h
  have hq : 0 < √(Real.sinh (π * x) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  unfold zeroLawSlope
  have := Real.cosh_pos (π * x)
  positivity

/-- `ρ_U' > 4/3` beyond the tip. -/
theorem four_thirds_lt_zeroLawSlope {x : ℝ} (h : bootstrapTip < x) : 4 / 3 < zeroLawSlope x := by
  have hs := one_lt_sinh_of_tip_lt' h
  have hq : 0 < √(Real.sinh (π * x) ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hlt : √(Real.sinh (π * x) ^ 2 - 1) < Real.cosh (π * x) := by
    rw [show Real.cosh (π * x) = √(Real.cosh (π * x) ^ 2) by
      rw [Real.sqrt_sq (Real.cosh_pos _).le]]
    apply Real.sqrt_lt_sqrt (by nlinarith)
    rw [Real.cosh_sq]; linarith
  unfold zeroLawSlope
  rw [lt_div_iff₀ hq]
  nlinarith

/-- The slope decreases strictly beyond the tip. -/
theorem zeroLawSlope_strictAntiOn : StrictAntiOn zeroLawSlope (Ioi bootstrapTip) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  have hsa := one_lt_sinh_of_tip_lt' ha
  have hsb := one_lt_sinh_of_tip_lt' hb
  have hlt : Real.sinh (π * a) < Real.sinh (π * b) :=
    Real.sinh_strictMono (mul_lt_mul_of_pos_left hab Real.pi_pos)
  set sa := Real.sinh (π * a)
  set sb := Real.sinh (π * b)
  have hqa : 0 < sa ^ 2 - 1 := by nlinarith
  have hqb : 0 < sb ^ 2 - 1 := by nlinarith
  -- compare squares: `cosh²/(sinh² − 1) = 1 + 2/(sinh² − 1)`
  have key : Real.cosh (π * b) ^ 2 / (sb ^ 2 - 1) < Real.cosh (π * a) ^ 2 / (sa ^ 2 - 1) := by
    rw [Real.cosh_sq, Real.cosh_sq, div_lt_div_iff₀ hqb hqa]
    nlinarith
  unfold zeroLawSlope
  have pa : 0 < 4 / 3 * Real.cosh (π * a) / √(sa ^ 2 - 1) := by
    have := Real.cosh_pos (π * a); have := Real.sqrt_pos.mpr hqa; positivity
  have pb : 0 < 4 / 3 * Real.cosh (π * b) / √(sb ^ 2 - 1) := by
    have := Real.cosh_pos (π * b); have := Real.sqrt_pos.mpr hqb; positivity
  rw [← sq_lt_sq₀ pb.le pa.le, div_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hqa.le,
    Real.sq_sqrt hqb.le, mul_div_assoc, mul_div_assoc]
  exact mul_lt_mul_of_pos_left key (by norm_num)

theorem continuousOn_zeroLaw : ContinuousOn zeroLaw (Ici bootstrapTip) := by
  unfold zeroLaw
  apply ContinuousOn.mul continuousOn_const
  apply Real.continuousOn_arcosh.comp (by fun_prop)
  intro x hx
  simp only [mem_Ici] at hx ⊢
  rw [← sinh_pi_mul_bootstrapTip]
  apply Real.sinh_le_sinh.mpr
  have hx0 : 0 ≤ x := bootstrapTip_pos.le.trans hx
  rw [abs_of_nonneg hx0]
  exact mul_le_mul_of_nonneg_left hx Real.pi_pos.le

theorem deriv_zeroLaw_eqOn : EqOn (deriv zeroLaw) zeroLawSlope (Ioi bootstrapTip) :=
  fun _ hx => (hasDerivAt_zeroLaw hx).deriv

/-- **The zero law is strictly concave beyond the tip.** -/
theorem zeroLaw_strictConcaveOn : StrictConcaveOn ℝ (Ici bootstrapTip) zeroLaw := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici _) continuousOn_zeroLaw
  rw [interior_Ici]
  exact zeroLawSlope_strictAntiOn.congr deriv_zeroLaw_eqOn.symm

theorem hasDerivAt_zeroLaw_sub_linear {y : ℝ} (hy : bootstrapTip < y) :
    HasDerivAt (fun y => zeroLaw y - 4 / 3 * (y - bootstrapTip)) (zeroLawSlope y - 4 / 3) y := by
  have := (hasDerivAt_zeroLaw hy).sub (((hasDerivAt_id y).sub_const bootstrapTip).const_mul (4 / 3))
  exact this.congr_deriv (by simp)

/-- **Linear lower bound:** `(4/3)(x − x*) ≤ ρ_U(x)`. -/
theorem zeroLaw_ge_linear {x : ℝ} (h : bootstrapTip ≤ x) : 4 / 3 * (x - bootstrapTip) ≤ zeroLaw x := by
  have hmono : MonotoneOn (fun y => zeroLaw y - 4 / 3 * (y - bootstrapTip)) (Ici bootstrapTip) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact continuousOn_zeroLaw.sub (by fun_prop)
    · intro y hy
      rw [interior_Ici] at hy
      exact (hasDerivAt_zeroLaw_sub_linear hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hasDerivAt_zeroLaw_sub_linear hy).deriv]
      linarith [four_thirds_lt_zeroLawSlope hy]
  have := hmono Set.self_mem_Ici (mem_Ici.mpr h) h
  simp only [sub_self, mul_zero, zeroLaw_tip] at this
  linarith

/-- `arcosh(sinh u) ≤ u` wherever `sinh u ≥ 1`. -/
theorem arcosh_sinh_le {u : ℝ} (hu : 1 ≤ Real.sinh u) : Real.arcosh (Real.sinh u) ≤ u := by
  unfold Real.arcosh
  have hsq : √(Real.sinh u ^ 2 - 1) ≤ Real.sinh u :=
    calc √(Real.sinh u ^ 2 - 1) ≤ √(Real.sinh u ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sinh u := Real.sqrt_sq (by linarith)
  have hpos : 0 < Real.sinh u + √(Real.sinh u ^ 2 - 1) := by
    have := Real.sqrt_nonneg (Real.sinh u ^ 2 - 1); linarith
  rw [Real.log_le_iff_le_exp hpos]
  have : 2 * Real.sinh u ≤ Real.exp u := by
    rw [Real.sinh_eq]; have := Real.exp_pos (-u); linarith
  linarith

/-- **Linear upper bound:** `ρ_U(x) ≤ (4/3)|x|` on the slits. -/
theorem zeroLaw_le_linear {x : ℝ} (h : bootstrapTip ≤ |x|) : zeroLaw x ≤ 4 / 3 * |x| := by
  have h1 : 1 ≤ Real.sinh (π * |x|) := by
    rw [← sinh_pi_mul_bootstrapTip]
    exact Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left h Real.pi_pos.le)
  have := arcosh_sinh_le h1
  unfold zeroLaw
  have hπ := Real.pi_pos
  calc 4 / (3 * π) * Real.arcosh (Real.sinh (π * |x|)) ≤ 4 / (3 * π) * (π * |x|) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 4 / 3 * |x| := by field_simp

/-! ### The Cardy deficit -/

/-- The Cardy line `L(x) = (2π/3)|x|`. -/
def cardyLine (x : ℝ) : ℝ := 2 * π / 3 * |x|

/-- The integrand `π/2 − arcsin(sinh πs)` of the deficit. -/
def deficitIntegrand (s : ℝ) : ℝ := π / 2 - Real.arcsin (Real.sinh (π * s))

theorem continuous_arcsin_sinh : Continuous fun s : ℝ => Real.arcsin (Real.sinh (π * s)) := by
  fun_prop

/-- The value of the extremal potential at the origin. -/
def axisU0 : ℝ := -cardyLine bootstrapTip + 4 / 3 * ∫ s in (0 : ℝ)..bootstrapTip, Real.arcsin (Real.sinh (π * s))

/-- The extremal potential on the real axis inside the lobe. -/
def axisU (x : ℝ) : ℝ := axisU0 - 4 / 3 * ∫ s in (0 : ℝ)..|x|, Real.arcsin (Real.sinh (π * s))

/-- **The deficit identity:** `U(x) + L(x) = −(4/3)∫_{|x|}^{x*}(π/2 − arcsin sinh πs) ds`. -/
theorem axisU_add_cardyLine (x : ℝ) :
    axisU x + cardyLine x = -(4 / 3 * ∫ s in |x|..bootstrapTip, deficitIntegrand s) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s => Real.arcsin (Real.sinh (π * s))) MeasureTheory.volume a b :=
    fun a b => continuous_arcsin_sinh.intervalIntegrable a b
  have hsplit : (∫ s in (0 : ℝ)..bootstrapTip, Real.arcsin (Real.sinh (π * s))) -
      ∫ s in (0 : ℝ)..|x|, Real.arcsin (Real.sinh (π * s)) =
      ∫ s in |x|..bootstrapTip, Real.arcsin (Real.sinh (π * s)) :=
    intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)
  have hdef : ∫ s in |x|..bootstrapTip, deficitIntegrand s =
      (bootstrapTip - |x|) * (π / 2) - ∫ s in |x|..bootstrapTip, Real.arcsin (Real.sinh (π * s)) := by
    unfold deficitIntegrand
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hi _ _), intervalIntegral.integral_const,
      smul_eq_mul]
  unfold axisU axisU0 cardyLine
  rw [hdef, abs_of_pos bootstrapTip_pos]
  linarith

theorem axisU_tip : axisU bootstrapTip = -cardyLine bootstrapTip := by
  have := axisU_add_cardyLine bootstrapTip
  rw [abs_of_pos bootstrapTip_pos, intervalIntegral.integral_same, mul_zero, neg_zero] at this
  linarith

/-- **Strictly below the Cardy line:** `U(x) + L(x) < 0` for `|x| < x*`. -/
theorem axisU_add_cardyLine_neg {x : ℝ} (h : |x| < bootstrapTip) : axisU x + cardyLine x < 0 := by
  rw [axisU_add_cardyLine]
  have hpos : 0 < ∫ s in |x|..bootstrapTip, deficitIntegrand s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (continuous_const.sub continuous_arcsin_sinh).intervalIntegrable _ _
    · intro s hs; exact deficit_integrand_pos hs.2
    · exact h
  linarith

theorem deficitIntegrand_nonneg {s : ℝ} (h : s ≤ bootstrapTip) : 0 ≤ deficitIntegrand s := by
  rcases h.lt_or_eq with h | rfl
  · exact (deficit_integrand_pos h).le
  · exact deficit_integrand_tip.ge

/-- The Cardy deficit `κ(δ) = (4/3)∫_{x*−δ}^{x*}(π/2 − arcsin sinh πs) ds`. -/
def cardyDeficit (δ : ℝ) : ℝ := 4 / 3 * ∫ s in (bootstrapTip - δ)..bootstrapTip, deficitIntegrand s

theorem cardyDeficit_eq {δ : ℝ} (h1 : δ ≤ bootstrapTip) :
    cardyDeficit δ = -(axisU (bootstrapTip - δ) + cardyLine (bootstrapTip - δ)) := by
  rw [axisU_add_cardyLine, abs_of_nonneg (by linarith), neg_neg]; rfl

/-- **The Cardy deficit is positive** for `0 < δ ≤ x*`. -/
theorem cardyDeficit_pos {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ bootstrapTip) : 0 < cardyDeficit δ := by
  rw [cardyDeficit_eq h1]
  have := axisU_add_cardyLine_neg (x := bootstrapTip - δ) (by
    rw [abs_of_nonneg (by linarith)]; linarith)
  linarith

/-- The deficit grows with `δ`. -/
theorem cardyDeficit_mono {δ δ' : ℝ} (h0 : 0 ≤ δ) (hδ : δ ≤ δ') :
    cardyDeficit δ ≤ cardyDeficit δ' := by
  unfold cardyDeficit
  have hi : ∀ a b : ℝ, IntervalIntegrable deficitIntegrand MeasureTheory.volume a b :=
    fun a b => (continuous_const.sub continuous_arcsin_sinh).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (bootstrapTip - δ') (bootstrapTip - δ))
    (hi _ bootstrapTip)]
  have : 0 ≤ ∫ s in (bootstrapTip - δ')..(bootstrapTip - δ), deficitIntegrand s := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro s hs
    exact deficitIntegrand_nonneg (by linarith [hs.2])
  linarith

/-- The extremal potential at the origin is `U₀ = −κ(x*) < 0`. -/
theorem axisU0_eq : axisU0 = -cardyDeficit bootstrapTip := by
  rw [cardyDeficit_eq le_rfl, sub_self]
  have h := axisU_add_cardyLine 0
  have h0 : axisU 0 = axisU0 := by simp [axisU]
  have hL : cardyLine 0 = 0 := by simp [cardyLine]
  rw [h0, hL, add_zero, neg_neg]

theorem axisU0_neg : axisU0 < 0 := by
  rw [axisU0_eq]; linarith [cardyDeficit_pos bootstrapTip_pos le_rfl]

end GaloisForLFunctions.HagedornBootstrap
