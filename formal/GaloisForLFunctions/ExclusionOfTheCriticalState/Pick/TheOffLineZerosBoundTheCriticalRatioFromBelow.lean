import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesDecideTheCriticalRatio

/-!
# The off-line zeros bound the critical ratio from below

On a probe sum `P = Σ_k c_k e_{k+7}` the bare form is the Krein form `Re⟨R y, y⟩` of the zero
coordinates `y(ρ) = √m_ρ ∫ P(u) e^{(ρ−½)u} du` (`probeSumVec_apply_eq_integral`). On-line zeros
contribute `|y(ρ)|² ≥ 0`; an off-line zero contributes at least `−|y(ρ)||y(1−ρ̄)|`; and Cauchy–Schwarz in
`L²(e^{−8u})` gives `|y(ρ)| ≤ √m_ρ ‖P‖_{W₈}/√(8 + 2x_ρ)`, `x_ρ = Re ρ − ½`
(`norm_integral_probeSum_mul_cexp_le`). So `Q_R ≥ 0` on all probe sums once
`a(R) ≥ Σ_{ρ off the line} m_ρ/√((8 + 2x_ρ)(8 − 2x_ρ))`, and the Pick form of the critical ratio gives

* **The critical ratio is bounded below by the off-line zeros**
  (`criticalAliasCoefficient_le_offLineWeight`, `sqrt_sixtyThree_mul_criticalAliasCoefficient_le`).
  Off RH, `a(W₀) ≤ Σ_{off-line ρ} m_ρ/√((8 + 2x_ρ)(8 − 2x_ρ)) ≤ N_off/√63`, where `N_off` counts the
  zeros off the line with multiplicity (in `[0, ∞]`); since `a(W₀) = a(1)/W₀`, a small critical ratio
  needs many zeros off the line.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate lp ENNReal

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry Zeta23
  _root_.RHTower

/-! ### Zero coordinates of a probe sum -/

theorem probeSum_of_nonneg {N : ℕ} (p c : Fin N → ℝ) {u : ℝ} (hu : 0 ≤ u) : probeSum p c u = 0 := by
  simp [probeSum, probe_of_nonneg hu]

theorem measurable_probeSum {N : ℕ} (p c : Fin N → ℝ) : Measurable (probeSum p c) := by
  unfold probeSum
  exact Finset.measurable_sum _ fun k _ => (measurable_probe (p k)).const_mul (c k)

/-- The zero coordinate of a probe sum is the zero transform of the profile. -/
theorem probeSumVec_apply_eq_integral {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k)
    (c : Fin N → ℝ) (τ : zetaZeroConfig.carrier) :
    probeSumVec hp c τ = ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) *
      ∫ u : ℝ, (probeSum p c u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u) := by
  have hre : ∀ k, 0 < p k + ((τ : ℂ) - 1 / 2).re := fun k => by
    linarith [hp k, re_carrier_sub_half_ge τ]
  have hPi : ∀ k, Integrable (fun u : ℝ =>
      (c k : ℂ) * ((probe (p k) u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u))) :=
    fun k => (integrable_ofReal_probe_mul_cexp (hre k)).const_mul _
  have hfun : (fun u : ℝ => (probeSum p c u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)) =
      fun u => ∑ k, (c k : ℂ) * ((probe (p k) u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)) := by
    funext u
    simp only [probeSum]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hfun, integral_finsetSum _ fun k _ => hPi k, probeSumVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, ← zeroCoord_probe_eq (hp k), zeroCoord_cx_eq]
  ring

/-- **Cauchy–Schwarz for the zero transform**: `|∫ P e^{zu}| ≤ ‖P‖_{W₈}/√(2 Re z + 8)`. -/
theorem norm_integral_probeSum_mul_cexp_le {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 4 < p k)
    (c : Fin N → ℝ) {z : ℂ} (hz : -4 < z.re) :
    ‖∫ u : ℝ, (probeSum p c u : ℂ) * cexp (z * u)‖ ≤
      Real.sqrt (∫ u, probeSum p c u ^ 2 * Real.exp (-(8 * u))) / Real.sqrt (2 * z.re + 8) := by
  set f : ℝ → ℝ := fun u => |probeSum p c u| * Real.exp (-(4 * u)) with hf
  set g : ℝ → ℝ := (Iio (0 : ℝ)).indicator fun u => Real.exp ((z.re + 4) * u) with hg
  have ha : 0 < 2 * z.re + 8 := by linarith
  have hfg : ∀ u, ‖(probeSum p c u : ℂ) * cexp (z * u)‖ = f u * g u := by
    intro u
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    by_cases hu : u < 0
    · simp only [f, g, indicator_of_mem (mem_Iio.mpr hu), Real.norm_eq_abs]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    · rw [probeSum_of_nonneg p c (not_lt.mp hu)]
      simp [f, g, indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]
  have hP2 := integrable_probeSum_sq_mul_exp hp c
  have he4 : ∀ u : ℝ, Real.exp (-(4 * u)) ^ 2 = Real.exp (-(8 * u)) := fun u => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have heg : ∀ u : ℝ, Real.exp ((z.re + 4) * u) ^ 2 = Real.exp ((2 * z.re + 8) * u) := fun u => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hf2 : Integrable fun u => f u ^ 2 := hP2.congr (Eventually.of_forall fun u => by
    simp only [f]
    rw [mul_pow, sq_abs, he4])
  have hgI : IntegrableOn (fun u : ℝ => Real.exp ((2 * z.re + 8) * u)) (Iio 0) :=
    (integrableOn_exp_mul_Iic ha 0).mono_set Iio_subset_Iic_self
  have hg2 : Integrable fun u => g u ^ 2 := by
    refine (hgI.integrable_indicator measurableSet_Iio).congr (Eventually.of_forall fun u => ?_)
    by_cases hu : u < 0
    · simp only [g, indicator_of_mem (mem_Iio.mpr hu)]
      rw [heg]
    · simp [g, indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]
  have hfm : AEStronglyMeasurable f volume :=
    ((measurable_probeSum p c).abs.mul (by fun_prop)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g volume :=
    ((by fun_prop : Measurable fun u : ℝ => Real.exp ((z.re + 4) * u)).indicator
      measurableSet_Iio).aestronglyMeasurable
  have hCS := abs_integral_mul_le_sqrt hfm hgm hf2 hg2
  have hf2eq : ∫ u, f u ^ 2 = ∫ u, probeSum p c u ^ 2 * Real.exp (-(8 * u)) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [f]
    rw [mul_pow, sq_abs, he4]
  have hg2eq : ∫ u, g u ^ 2 = 1 / (2 * z.re + 8) := by
    have h1 : (fun u => g u ^ 2) = (Iio (0 : ℝ)).indicator fun u => Real.exp ((2 * z.re + 8) * u) := by
      funext u
      by_cases hu : u < 0
      · simp only [g, indicator_of_mem (mem_Iio.mpr hu)]
        rw [heg]
      · simp [g, indicator_of_notMem (show u ∉ Iio (0 : ℝ) from hu)]
    rw [h1, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
      integral_exp_mul_Iic ha 0, mul_zero, Real.exp_zero]
  have hnorm : ‖∫ u : ℝ, (probeSum p c u : ℂ) * cexp (z * u)‖ ≤ ∫ u, f u * g u := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    exact integral_congr_ae (Eventually.of_forall hfg)
  have hfg0 : 0 ≤ ∫ u, f u * g u := integral_nonneg fun u =>
    mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  rw [abs_of_nonneg hfg0, hf2eq, hg2eq, Real.sqrt_div' _ ha.le, Real.sqrt_one] at hCS
  calc ‖∫ u : ℝ, (probeSum p c u : ℂ) * cexp (z * u)‖ ≤ ∫ u, f u * g u := hnorm
    _ ≤ _ := hCS
    _ = _ := by rw [mul_one_div]

/-! ### The off-line weight -/

/-- The weight of a zero: `m_ρ/√((8 + 2x)(8 − 2x))` off the line, `0` on it, `x = Re ρ − ½`. -/
def offLineWeight (τ : zetaZeroConfig.carrier) : ℝ :=
  if ((τ : ℂ) - 1 / 2).re = 0 then 0 else
    (zetaZeroConfig.mult τ : ℝ) /
      Real.sqrt ((8 + 2 * ((τ : ℂ) - 1 / 2).re) * (8 - 2 * ((τ : ℂ) - 1 / 2).re))

theorem offLineWeight_nonneg (τ : zetaZeroConfig.carrier) : 0 ≤ offLineWeight τ := by
  unfold offLineWeight
  split_ifs
  · exact le_rfl
  · positivity

theorem re_reflectCarrier_sub_half (τ : zetaZeroConfig.carrier) :
    (((reflectCarrier zetaZeroConfig τ : zetaZeroConfig.carrier) : ℂ) - 1 / 2).re =
      -((τ : ℂ) - 1 / 2).re := by
  show ((reflect (τ : ℂ)) - 1 / 2).re = _
  simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
  norm_num
  ring

/-- **The Krein form of a probe sum is at least minus the off-line weight.** -/
theorem re_inner_reflect_probeSumVec_ge {N : ℕ} (c : Fin N → ℝ)
    (hp : ∀ k : Fin N, 1 ≤ (k : ℝ) + 7) (hs : Summable offLineWeight) :
    -((∑' τ, offLineWeight τ) *
        ∫ u, probeSum (fun k : Fin N => (k : ℝ) + 7) c u ^ 2 * Real.exp (-(8 * u))) ≤
      (inner ℂ (reflectVec zetaZeroConfig (probeSumVec hp c)) (probeSumVec hp c)).re := by
  have hp4 : ∀ k : Fin N, 4 < (k : ℝ) + 7 := fun k => by
    linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  set y := probeSumVec hp c
  set I := ∫ u, probeSum (fun k : Fin N => (k : ℝ) + 7) c u ^ 2 * Real.exp (-(8 * u))
  have hI : 0 ≤ I := integral_nonneg fun u => by positivity
  have hsum := lp.summable_inner (𝕜 := ℂ) (reflectVec zetaZeroConfig y) y
  rw [lp.inner_eq_tsum, Complex.re_tsum hsum]
  have hbound : ∀ τ : zetaZeroConfig.carrier, ‖y τ‖ ≤ Real.sqrt (zetaZeroConfig.mult τ) *
      (Real.sqrt I / Real.sqrt (2 * ((τ : ℂ) - 1 / 2).re + 8)) := by
    intro τ
    rw [probeSumVec_apply_eq_integral hp c τ, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_integral_probeSum_mul_cexp_le hp4 c
      (by linarith [re_carrier_sub_half_ge τ])) (Real.sqrt_nonneg _)
  have hterm : ∀ τ : zetaZeroConfig.carrier, -(offLineWeight τ * I) ≤
      (inner ℂ ((reflectVec zetaZeroConfig y) τ) (y τ)).re := by
    intro τ
    rw [RCLike.inner_apply', reflectVec_apply]
    by_cases h0 : ((τ : ℂ) - 1 / 2).re = 0
    · have hfix : reflectCarrier zetaZeroConfig τ = τ := by
        apply Subtype.ext
        show reflect (τ : ℂ) = τ
        apply Complex.ext
        · simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
          simp only [Complex.sub_re] at h0; norm_num at h0 ⊢; linarith
        · simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
      rw [hfix, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, offLineWeight, if_pos h0,
        zero_mul, neg_zero]
      exact Complex.normSq_nonneg _
    · have hx := abs_le.mp (abs_re_carrier_sub_half τ)
      have hm : zetaZeroConfig.mult (reflect (τ : ℂ)) = zetaZeroConfig.mult τ :=
        zetaZeroConfig.mult_reflect _ τ.2
      have h1 := hbound τ
      have h2 := hbound (reflectCarrier zetaZeroConfig τ)
      rw [re_reflectCarrier_sub_half] at h2
      have hm' : (zetaZeroConfig.mult ((reflectCarrier zetaZeroConfig τ : zetaZeroConfig.carrier) :
          ℂ) : ℝ) = zetaZeroConfig.mult τ := by
        show (zetaZeroConfig.mult (reflect (τ : ℂ)) : ℝ) = _
        rw [hm]
      rw [hm'] at h2
      have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult τ := Nat.cast_nonneg _
      have hprod : ‖y (reflectCarrier zetaZeroConfig τ)‖ * ‖y τ‖ ≤ offLineWeight τ * I := by
        rw [offLineWeight, if_neg h0]
        generalize ((τ : ℂ) - 1 / 2).re = x at h1 h2 hx ⊢
        have hA : 0 < 2 * x + 8 := by linarith
        have hB : 0 < 2 * -x + 8 := by linarith
        have hAB : Real.sqrt (2 * x + 8) * Real.sqrt (2 * -x + 8) =
            Real.sqrt ((8 + 2 * x) * (8 - 2 * x)) := by
          rw [← Real.sqrt_mul hA.le]; congr 1; ring
        have hApos := Real.sqrt_pos.mpr hA
        have hBpos := Real.sqrt_pos.mpr hB
        calc ‖y (reflectCarrier zetaZeroConfig τ)‖ * ‖y τ‖
            ≤ (Real.sqrt (zetaZeroConfig.mult τ) * (Real.sqrt I / Real.sqrt (2 * -x + 8))) *
                (Real.sqrt (zetaZeroConfig.mult τ) * (Real.sqrt I / Real.sqrt (2 * x + 8))) :=
              mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
          _ = (Real.sqrt (zetaZeroConfig.mult τ) * Real.sqrt (zetaZeroConfig.mult τ)) *
                (Real.sqrt I * Real.sqrt I) /
                (Real.sqrt (2 * x + 8) * Real.sqrt (2 * -x + 8)) := by
              field_simp
          _ = (zetaZeroConfig.mult τ : ℝ) / Real.sqrt ((8 + 2 * x) * (8 - 2 * x)) * I := by
              rw [Real.mul_self_sqrt hm0, Real.mul_self_sqrt hI, hAB]
              ring
      have hre := (abs_le.mp (Complex.abs_re_le_norm
        ((starRingEnd ℂ) (y (reflectCarrier zetaZeroConfig τ)) * y τ))).1
      rw [norm_mul, Complex.norm_conj] at hre
      linarith
  calc -((∑' τ, offLineWeight τ) * I) = ∑' τ, -(offLineWeight τ * I) := by
        rw [tsum_neg, tsum_mul_right]
    _ ≤ ∑' τ, (inner ℂ ((reflectVec zetaZeroConfig y) τ) (y τ)).re :=
        Summable.tsum_le_tsum hterm (hs.mul_right I).neg (Complex.reCLM.summable hsum)

/-! ### The bound on the critical ratio -/

/-- **The off-line zeros bound the critical ratio from below.** Off RH,
`a(W₀) ≤ Σ_{ρ off the line} m_ρ/√((8 + 2x_ρ)(8 − 2x_ρ))` whenever the right side converges. -/
theorem criticalAliasCoefficient_le_offLineWeight {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hs : Summable offLineWeight) :
    criticalAliasCoefficient W₀ ≤ ∑' τ, offLineWeight τ := by
  set S := ∑' τ, offLineWeight τ
  have hS : 0 ≤ S := tsum_nonneg offLineWeight_nonneg
  have ha1 : 0 < criticalAliasCoefficient 1 := criticalAliasCoefficient_positive one_pos
  -- every ratio whose confinement dominates the off-line weight is at most `W₀`
  have key : ∀ R : ℝ, 0 < R → S ≤ criticalAliasCoefficient R → R ≤ W₀ := by
    intro R hR hSR
    have hpick : ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c := by
      intro N c
      have hp : ∀ k : Fin N, 1 ≤ (k : ℝ) + 7 := fun k => by
        linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
      have hp4 : ∀ k : Fin N, 4 < (k : ℝ) + 7 := fun k => by
        linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
      have hK := re_inner_reflect_probeSumVec_ge c hp hs
      have hIio : (∫ u in Iio (0 : ℝ), probeSum (fun k : Fin N => (k : ℝ) + 7) c u ^ 2 *
          Real.exp (-(8 * u))) =
          ∫ u, probeSum (fun k : Fin N => (k : ℝ) + 7) c u ^ 2 * Real.exp (-(8 * u)) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
          rw [probeSum_of_nonneg _ c (not_lt.mp hu)]; ring
      rw [confinedPickForm_eq R c hp, sum_div_eq_integral_probeSum_sq hp4 c, hIio]
      have hI : 0 ≤ ∫ u, probeSum (fun k : Fin N => (k : ℝ) + 7) c u ^ 2 * Real.exp (-(8 * u)) :=
        integral_nonneg fun u => by positivity
      nlinarith
    have h := (confinedPick_nonneg_iff hR).mp hpick
    rw [hthreshold, EReal.coe_le_coe_iff] at h
    exact h
  by_contra hlt
  push Not at hlt
  set S' := (S + criticalAliasCoefficient W₀) / 2
  have hS'pos : 0 < S' := by
    have := criticalAliasCoefficient_positive hW
    simp only [S']; linarith
  have hR := key (criticalAliasCoefficient 1 / S') (div_pos ha1 hS'pos) (by
    rw [criticalAliasCoefficient_eq_div, div_div_cancel₀ ha1.ne']
    simp only [S']; linarith)
  have hW' : criticalAliasCoefficient W₀ = criticalAliasCoefficient 1 / W₀ :=
    criticalAliasCoefficient_eq_div W₀
  have : criticalAliasCoefficient 1 / S' > W₀ := by
    rw [gt_iff_lt, lt_div_iff₀ hS'pos]
    have h2 : S' < criticalAliasCoefficient W₀ := by simp only [S']; linarith
    rw [hW', lt_div_iff₀ hW] at h2
    linarith
  linarith

/-- **Unconditional form in `[0, ∞]`.** Off RH,
`a(W₀) ≤ Σ_{ρ off the line} m_ρ/√((8 + 2x_ρ)(8 − 2x_ρ))`. -/
theorem ofReal_criticalAliasCoefficient_le_tsum_offLineWeight {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ENNReal.ofReal (criticalAliasCoefficient W₀) ≤ ∑' τ, ENNReal.ofReal (offLineWeight τ) := by
  by_cases htop : ∑' τ, ENNReal.ofReal (offLineWeight τ) = ⊤
  · rw [htop]; exact le_top
  · have hs : Summable offLineWeight := by
      have := ENNReal.summable_toReal htop
      exact this.congr fun τ => ENNReal.toReal_ofReal (offLineWeight_nonneg τ)
    rw [← ENNReal.ofReal_tsum_of_nonneg offLineWeight_nonneg hs]
    exact ENNReal.ofReal_le_ofReal (criticalAliasCoefficient_le_offLineWeight hW hthreshold hs)

/-- The off-line multiplicity: `m_ρ` off the line, `0` on it. -/
def offLineMultiplicity (τ : zetaZeroConfig.carrier) : ℝ :=
  if ((τ : ℂ) - 1 / 2).re = 0 then 0 else (zetaZeroConfig.mult τ : ℝ)

theorem offLineWeight_le (τ : zetaZeroConfig.carrier) :
    offLineWeight τ ≤ offLineMultiplicity τ / Real.sqrt 63 := by
  unfold offLineWeight offLineMultiplicity
  split_ifs with h0
  · simp
  · have hx := abs_le.mp (abs_re_carrier_sub_half τ)
    set x := ((τ : ℂ) - 1 / 2).re
    have h63 : Real.sqrt 63 ≤ Real.sqrt ((8 + 2 * x) * (8 - 2 * x)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) h63

/-- **A small critical ratio needs many zeros off the line.** Off RH,
`√63 · a(W₀) ≤ N_off`, where `N_off = Σ_{ρ off the line} m_ρ ∈ [0, ∞]`; with `a(W₀) = a(1)/W₀` this
is `W₀ ≥ √63 a(1)/N_off`. -/
theorem sqrt_sixtyThree_mul_criticalAliasCoefficient_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    ENNReal.ofReal (Real.sqrt 63 * criticalAliasCoefficient W₀) ≤
      ∑' τ, ENNReal.ofReal (offLineMultiplicity τ) := by
  have h := ofReal_criticalAliasCoefficient_le_tsum_offLineWeight hW hthreshold
  have h63 : (0 : ℝ) < Real.sqrt 63 := by positivity
  calc ENNReal.ofReal (Real.sqrt 63 * criticalAliasCoefficient W₀)
      = ENNReal.ofReal (Real.sqrt 63) * ENNReal.ofReal (criticalAliasCoefficient W₀) :=
        ENNReal.ofReal_mul h63.le
    _ ≤ ENNReal.ofReal (Real.sqrt 63) * ∑' τ, ENNReal.ofReal (offLineWeight τ) := by gcongr
    _ = ∑' τ, ENNReal.ofReal (Real.sqrt 63 * offLineWeight τ) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun τ => (ENNReal.ofReal_mul h63.le).symm
    _ ≤ ∑' τ, ENNReal.ofReal (offLineMultiplicity τ) := by
        refine ENNReal.tsum_le_tsum fun τ => ENNReal.ofReal_le_ofReal ?_
        have := offLineWeight_le τ
        rw [le_div_iff₀ h63] at this
        linarith

#print axioms ofReal_criticalAliasCoefficient_le_tsum_offLineWeight
#print axioms sqrt_sixtyThree_mul_criticalAliasCoefficient_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
