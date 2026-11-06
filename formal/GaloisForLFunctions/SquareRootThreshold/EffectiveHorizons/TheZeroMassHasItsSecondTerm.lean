import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.XiZeroMass

/-!
# The symmetric ξ-zero mass with its second term

**Theorem** (`abs_xiSymmetricMass_sub_sharp_le`). For `T ≥ 8`,
`|M(T) - (T/π)(log T - log 2 - log π - 1)| ≤ 80 + 65 log T`.

The vertical contour integral is the rational head, the Gamma phase and the ζ-integral. The first and
last are bounded by `π`. The Gamma phase is `t log t - t` up to a bounded remainder, because its
derivative differs from `log t` by at most `8/t²`. Only the horizontal sides cost `log T`.

Two consequences hold from the small height `e¹²`: `M(X) ≤ 0.33 X log X`
(`xiSymmetricMass_le_of_exp_twelve_le`) and `M(2T) - M(T) ≥ 0.27 T log T`
(`le_xiSymmetricMass_band_of_exp_twelve_le`).
-/

open Complex intervalIntegral MeasureTheory Set

noncomputable section

namespace RHTower

/-- The bounded remainder of the Gamma phase on the line through one. -/
theorem abs_gammaVerticalPhaseRemainder_one_le {t : ℝ} (ht : 2 ≤ t) :
    |gammaVerticalPhaseRemainder 1 t| ≤ 16 := by
  have ht0 : 0 < t := by linarith only [ht]
  let e : ℝ → ℝ := fun u => (Complex.digamma ((1 : ℂ) + (u : ℂ) * I)).re - Real.log u
  have hecont : ContinuousOn e (Set.uIcc 2 t) := by
    refine (continuous_digammaVerticalRe (by norm_num : (0 : ℝ) < 1)).continuousOn.sub ?_
    refine Real.continuousOn_log.mono fun u hu => ?_
    rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu
    exact Set.mem_compl_singleton_iff.mpr (by linarith only [hu.1])
  have hint : (∫ u in (2 : ℝ)..t, e u) =
      gammaVerticalPhaseRemainder 1 t - gammaVerticalPhaseRemainder 1 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu
      simpa only [e, Complex.ofReal_one] using
        hasDerivAt_gammaVerticalPhaseRemainder (σ := 1) (by norm_num) (by linarith only [hu.1])
    · exact hecont.intervalIntegrable
  -- The majorant `8/u²` has primitive `-8/u`.
  have hgcont : ContinuousOn (fun u : ℝ => 8 * (u ^ 2)⁻¹) (Set.uIcc 2 t) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun u hu => ?_)
    rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu
    have : 0 < u := by linarith only [hu.1]
    positivity
  have hmaj : (∫ u in (2 : ℝ)..t, 8 * (u ^ 2)⁻¹) = (-8) * t⁻¹ - (-8) * (2 : ℝ)⁻¹ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le ht, Set.mem_Icc] at hu
      have hu0 : u ≠ 0 := by
        have : 0 < u := by linarith only [hu.1]
        exact this.ne'
      have h := (hasDerivAt_inv hu0).const_mul (-8 : ℝ)
      refine h.congr_deriv ?_
      ring
    · exact hgcont.intervalIntegrable
  have hb : ‖∫ u in (2 : ℝ)..t, e u‖ ≤ ∫ u in (2 : ℝ)..t, 8 * (u ^ 2)⁻¹ := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ hgcont.intervalIntegrable
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [Real.norm_eq_abs]
    have he : |e u| ≤ 8 / u ^ 2 := abs_re_digamma_one_sub_log_le hu.1.le
    rwa [div_eq_mul_inv] at he
  rw [hmaj, Real.norm_eq_abs, hint] at hb
  have hbase : |gammaVerticalPhaseRemainder 1 2| ≤ 12 := by
    have := abs_gammaVerticalPhase_one_sub_main_le_six_mul (t := 2) le_rfl
    change |gammaVerticalPhaseRemainder 1 2| ≤ 6 * 2 at this
    linarith only [this]
  have hinv : 0 ≤ t⁻¹ := by positivity
  have h1 := abs_le.mp hb
  have h2 := abs_le.mp hbase
  rw [abs_le]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, hinv]

/-- The constant of the second term. -/
def massKappa : ℝ := Real.log 2 + Real.log Real.pi + 1

/-- The vertical contour integral with its second term. -/
theorem abs_vertical_xi_sub_sharp_le {T : ℝ} (hT : 4 ≤ T) :
    |(∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re) -
      1 / 2 * (T * (Real.log T - massKappa))| ≤ 2 * Real.pi + 16 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hγ := abs_gammaVerticalPhaseRemainder_one_le (t := T / 2) (by linarith only [hT])
  have hrat := abs_integral_rational_head_le T
  have hζ := abs_integral_re_logDeriv_zeta_two_le T
  have hsplit : (∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re) -
        1 / 2 * (T * (Real.log T - massKappa)) =
      (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2))) +
        gammaVerticalPhaseRemainder 1 (T / 2) +
        ∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re := by
    rw [integral_re_logDeriv_xi_two, gammaVerticalPhaseRemainder,
      Real.log_div hT0.ne' (by norm_num), massKappa]
    ring
  rw [hsplit]
  have h1 := abs_le.mp hrat
  have h2 := abs_le.mp hγ
  have h3 := abs_le.mp hζ
  rw [abs_le]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

private theorem two_div_pi_le : 2 / Real.pi ≤ 16 / 25 := by
  rw [div_le_iff₀ Real.pi_pos]
  have := Real.pi_gt_d2
  linarith only [this]

/-- The sharp mass on an admissible contour. -/
theorem abs_xiSymmetricMass_sub_sharp_admissible {T : ℝ} (hT : 4 ≤ T)
    (hne : ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |(xiSymmetricMass T : ℝ) - 1 / Real.pi * (T * (Real.log T - massKappa))| ≤
      15 + 64 * Real.log T := by
  have hT0 : 0 < T := by linarith only [hT]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have hπ := Real.pi_pos
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re :=
    ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im :=
    ⟨_, rfl⟩
  have hv := abs_vertical_xi_sub_sharp_le hT
  have hh := abs_horizontal_xi_le_hundred_log hT hne
  have hmass := two_pi_mul_xiSymmetricMass hT0.le hne
  rw [← hV] at hv hmass
  rw [← hH] at hh hmass
  have heq : (xiSymmetricMass T : ℝ) - 1 / Real.pi * (T * (Real.log T - massKappa)) =
      2 / Real.pi * (V - 1 / 2 * (T * (Real.log T - massKappa)) - H) := by
    field_simp
    linarith only [hmass]
  have hscale0 : 0 < 2 / Real.pi := by positivity
  rw [heq, abs_mul, abs_of_pos hscale0]
  have hsum : |V - 1 / 2 * (T * (Real.log T - massKappa)) - H| ≤
      2 * Real.pi + 16 + 100 * Real.log T := by
    refine (abs_sub _ _).trans ?_
    linarith only [hv, hh]
  have hπu : 2 / Real.pi * (2 * Real.pi) = 4 := by field_simp; norm_num
  calc 2 / Real.pi * |V - 1 / 2 * (T * (Real.log T - massKappa)) - H|
      ≤ 2 / Real.pi * (2 * Real.pi + 16 + 100 * Real.log T) :=
        mul_le_mul_of_nonneg_left hsum hscale0.le
    _ = 4 + 2 / Real.pi * (16 + 100 * Real.log T) := by
        rw [add_assoc, mul_add, hπu]
    _ ≤ 4 + 16 / 25 * (16 + 100 * Real.log T) := by
        have := mul_le_mul_of_nonneg_right two_div_pi_le
          (by positivity : 0 ≤ 16 + 100 * Real.log T)
        linarith only [this]
    _ ≤ 15 + 64 * Real.log T := by linarith only [hlog]

private theorem massKappa_nonneg : 0 ≤ massKappa := by
  unfold massKappa
  have h1 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h2 := Real.log_nonneg (by linarith only [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
  linarith only [h1, h2]

/-- **The sharp mass at every height.** -/
theorem abs_xiSymmetricMass_sub_sharp_le {T : ℝ} (hT : 8 ≤ T) :
    |(xiSymmetricMass T : ℝ) - 1 / Real.pi * (T * (Real.log T - massKappa))| ≤
      80 + 65 * Real.log T := by
  have hT0 : 0 < T := by linarith only [hT]
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have hκ := massKappa_nonneg
  have hP0 : 0 ≤ 1 / Real.pi := by positivity
  have hP1 : 1 / Real.pi ≤ 8 / 25 := by
    have := two_div_pi_le
    have e : 2 / Real.pi = 2 * (1 / Real.pi) := by ring
    rw [e] at this
    linarith only [this]
  obtain ⟨T₂, hT₂mem, hT₂adm⟩ := exists_admissible_height (a := T) (b := T + 1) (by linarith only [])
  obtain ⟨T₃, hT₃mem, hT₃adm⟩ := exists_admissible_height (a := T - 1) (b := T) (by linarith only [])
  have hT₂0 : 0 < T₂ := by linarith only [hT₂mem.1, hT]
  have hT₃0 : 0 < T₃ := by linarith only [hT₃mem.1, hT]
  rw [abs_le]
  constructor
  · -- Lower bound through an admissible height just below `T`.
    have hmono : xiSymmetricMass T₃ ≤ xiSymmetricMass T :=
      xiSymmetricMass_mono (by linarith only [hT₃mem.1, hT]) hT₃mem.2.le
    have hmono' : (xiSymmetricMass T₃ : ℝ) ≤ (xiSymmetricMass T : ℝ) := by exact_mod_cast hmono
    have hb := abs_le.mp (abs_xiSymmetricMass_sub_sharp_admissible
      (by linarith only [hT₃mem.1, hT]) hT₃adm)
    have hL3 : Real.log T₃ ≤ Real.log T := Real.log_le_log hT₃0 hT₃mem.2.le
    have h1 : T * Real.log T - Real.log T - 2 ≤ T₃ * Real.log T₃ :=
      (pred_mul_log_ge (by linarith only [hT])).trans
        (mul_log_mono (by linarith only [hT]) hT₃mem.1.le)
    have h2 : T * (Real.log T - massKappa) - (Real.log T + 2) ≤
        T₃ * (Real.log T₃ - massKappa) := by
      have := mul_le_mul_of_nonneg_right hT₃mem.2.le hκ
      nlinarith only [h1, this]
    have h3 := mul_le_mul_of_nonneg_left h2 hP0
    have h4 : 1 / Real.pi * (Real.log T + 2) ≤ 8 / 25 * (Real.log T + 2) :=
      mul_le_mul_of_nonneg_right hP1 (by positivity)
    have e : 1 / Real.pi * (T * (Real.log T - massKappa) - (Real.log T + 2)) =
        1 / Real.pi * (T * (Real.log T - massKappa)) - 1 / Real.pi * (Real.log T + 2) := by ring
    rw [e] at h3
    linarith only [hmono', hb.1, h3, h4, hL3, hL0]
  · -- Upper bound through an admissible height just above `T`.
    have hmono : xiSymmetricMass T ≤ xiSymmetricMass T₂ :=
      xiSymmetricMass_mono hT0.le hT₂mem.1.le
    have hmono' : (xiSymmetricMass T : ℝ) ≤ (xiSymmetricMass T₂ : ℝ) := by exact_mod_cast hmono
    have hb := abs_le.mp (abs_xiSymmetricMass_sub_sharp_admissible
      (by linarith only [hT₂mem.1, hT]) hT₂adm)
    have hL2 : Real.log T₂ ≤ Real.log T + 1 := by
      have h1 : Real.log T₂ ≤ Real.log (T + 1) := Real.log_le_log hT₂0 hT₂mem.2.le
      have h2 : Real.log (T + 1) ≤ Real.log T + 1 := by
        rw [show T + 1 = T * (1 + 1 / T) by field_simp, Real.log_mul hT0.ne' (by positivity)]
        have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / T by positivity)
        have h4 : 1 / T ≤ 1 := by
          rw [div_le_one hT0]
          linarith only [hT]
        linarith only [h3, h4]
      linarith only [h1, h2]
    have h1 : T₂ * Real.log T₂ ≤ T * Real.log T + Real.log T + 2 :=
      (mul_log_mono (by linarith only [hT₂mem.1, hT]) hT₂mem.2.le).trans
        (succ_mul_log_le (by linarith only [hT]))
    have h2 : T₂ * (Real.log T₂ - massKappa) ≤
        T * (Real.log T - massKappa) + (Real.log T + 2) := by
      have := mul_le_mul_of_nonneg_right hT₂mem.1.le hκ
      nlinarith only [h1, this]
    have h3 := mul_le_mul_of_nonneg_left h2 hP0
    have h4 : 1 / Real.pi * (Real.log T + 2) ≤ 8 / 25 * (Real.log T + 2) :=
      mul_le_mul_of_nonneg_right hP1 (by positivity)
    have e : 1 / Real.pi * (T * (Real.log T - massKappa) + (Real.log T + 2)) =
        1 / Real.pi * (T * (Real.log T - massKappa)) + 1 / Real.pi * (Real.log T + 2) := by ring
    rw [e] at h3
    linarith only [hmono', hb.2, h3, h4, hL2, hL0]

/-! ## The floor `e¹²` -/

private theorem exp_twelve_ge : (162754 : ℝ) ≤ Real.exp 12 := by
  have h2 : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (162754 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 12

theorem four_le_of_exp_twelve_le {X : ℝ} (hX : Real.exp 12 ≤ X) : 4 ≤ X := by
  have := exp_twelve_ge
  linarith only [this, hX]

/-- Above `e¹²`, `log X` is at most `11 + X/e¹²` and at least `12`. -/
private theorem log_facts_of_floor {X : ℝ} (hX : Real.exp 12 ≤ X) :
    12 ≤ Real.log X ∧ Real.log X ≤ 11 + X / 162754 := by
  have hE := Real.exp_pos 12
  have hX0 : 0 < X := by linarith only [hE, hX]
  have hE1 := exp_twelve_ge
  refine ⟨(Real.le_log_iff_exp_le hX0).mpr hX, ?_⟩
  have h1 := Real.log_le_sub_one_of_pos (show 0 < X / Real.exp 12 by positivity)
  rw [Real.log_div hX0.ne' hE.ne', Real.log_exp] at h1
  have h2 : X / Real.exp 12 ≤ X / 162754 :=
    div_le_div_of_nonneg_left hX0.le (by norm_num) hE1
  linarith only [h1, h2]

private theorem one_div_pi_bounds : 318 / 1000 ≤ 1 / Real.pi ∧ 1 / Real.pi ≤ 319 / 1000 := by
  constructor
  · rw [le_div_iff₀ Real.pi_pos]
    have := Real.pi_lt_d4
    linarith only [this]
  · rw [div_le_iff₀ Real.pi_pos]
    have := Real.pi_gt_d2
    linarith only [this]

/-- The upper mass law from `e¹²`. -/
theorem xiSymmetricMass_le_of_exp_twelve_le {X : ℝ} (hX : Real.exp 12 ≤ X) :
    (xiSymmetricMass X : ℝ) ≤ 33 / 100 * (X * Real.log X) := by
  obtain ⟨hL, hLu⟩ := log_facts_of_floor hX
  have hE1 := exp_twelve_ge
  have hX1 : (162754 : ℝ) ≤ X := hE1.trans hX
  have hX0 : 0 < X := by linarith only [hX1]
  have h := (abs_le.mp (abs_xiSymmetricMass_sub_sharp_le (T := X) (by linarith only [hX1]))).2
  obtain ⟨_, hP⟩ := one_div_pi_bounds
  have hP0 : 0 ≤ 1 / Real.pi := by positivity
  have hκ := massKappa_nonneg
  have h1 : 1 / Real.pi * (X * (Real.log X - massKappa)) ≤ 319 / 1000 * (X * Real.log X) := by
    have h2 : X * (Real.log X - massKappa) ≤ X * Real.log X := by
      nlinarith only [mul_nonneg hX0.le hκ]
    have h3 : 0 ≤ X * Real.log X := mul_nonneg hX0.le (by linarith only [hL])
    calc _ ≤ 1 / Real.pi * (X * Real.log X) := mul_le_mul_of_nonneg_left h2 hP0
      _ ≤ _ := mul_le_mul_of_nonneg_right hP h3
  have h4 : 12 * X ≤ X * Real.log X := by nlinarith only [mul_le_mul_of_nonneg_left hL hX0.le]
  linarith only [h, h1, h4, hLu, hX1]

/-- The band law from `e¹²`. -/
theorem le_xiSymmetricMass_band_of_exp_twelve_le {T : ℝ} (hT : Real.exp 12 ≤ T) :
    27 / 100 * (T * Real.log T) ≤ (xiSymmetricMass (2 * T) : ℝ) - (xiSymmetricMass T : ℝ) := by
  obtain ⟨hL, hLu⟩ := log_facts_of_floor hT
  have hE1 := exp_twelve_ge
  have hT1 : (162754 : ℝ) ≤ T := hE1.trans hT
  have hT0 : 0 < T := by linarith only [hT1]
  have hup := (abs_le.mp (abs_xiSymmetricMass_sub_sharp_le (T := T) (by linarith only [hT1]))).2
  have hlo := (abs_le.mp (abs_xiSymmetricMass_sub_sharp_le (T := 2 * T)
    (by linarith only [hT1]))).1
  rw [Real.log_mul (by norm_num) hT0.ne'] at hlo
  obtain ⟨hP, _⟩ := one_div_pi_bounds
  -- `log π ≤ π/e ≤ 1.16`, so the second term is at most `1.51 T/π`.
  have hlogπ : Real.log Real.pi ≤ 116 / 100 := by
    have h1 := Real.log_le_sub_one_of_pos
      (show 0 < Real.pi / Real.exp 1 by have := Real.pi_pos; positivity)
    rw [Real.log_div Real.pi_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    have h2 : Real.pi / Real.exp 1 ≤ 116 / 100 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      have h3 := Real.exp_one_gt_d9
      have h4 := Real.pi_lt_d4
      linarith only [h3, h4]
    linarith only [h1, h2]
  have hlog2 : 69 / 100 ≤ Real.log 2 ∧ Real.log 2 ≤ 7 / 10 := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_two_lt_d9
    constructor <;> linarith only [h1, h2]
  have hdiff : 318 / 1000 * (T * (Real.log T - 151 / 100)) ≤
      1 / Real.pi * (2 * T * (Real.log 2 + Real.log T - massKappa)) -
        1 / Real.pi * (T * (Real.log T - massKappa)) := by
    have h1 : 2 * T * (Real.log 2 + Real.log T - massKappa) - T * (Real.log T - massKappa) =
        T * (Real.log T + 2 * Real.log 2 - massKappa) := by ring
    have h2 : Real.log T - 151 / 100 ≤ Real.log T + 2 * Real.log 2 - massKappa := by
      unfold massKappa
      linarith only [hlogπ, hlog2.1]
    have h3 : 0 ≤ T * (Real.log T - 151 / 100) :=
      mul_nonneg hT0.le (by linarith only [hL])
    rw [← mul_sub, h1]
    calc 318 / 1000 * (T * (Real.log T - 151 / 100))
        ≤ 1 / Real.pi * (T * (Real.log T - 151 / 100)) := mul_le_mul_of_nonneg_right hP h3
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hT0.le) (by positivity)
  have h4 : 12 * T ≤ T * Real.log T := by nlinarith only [mul_le_mul_of_nonneg_left hL hT0.le]
  have e1 : 318 / 1000 * (T * (Real.log T - 151 / 100)) =
      318 / 1000 * (T * Real.log T) - 318 / 1000 * (151 / 100) * T := by ring
  rw [e1] at hdiff
  linarith only [hup, hlo, hdiff, h4, hLu, hlog2.2, hT1]

end RHTower
