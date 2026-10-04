import GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape
import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure
import GaloisForLFunctions.RHTower.PrimeArchThetaRawMomentRatioVanishing

/-!
# The real theta generator and its logarithmic slope

On the real line the normalized actual generator is `Φ(x) = Σ_j c_j x^{2j}`, `c_j = ν_j/(2j)!`, with
derivative `Φ'(x) = Σ_j δ_j c_j x^{2j+1}` (`δ_j c_j = (2j+2) c_{j+1}`).  Since the theta moments are
`ν_j = (2/R₀) ∫_0^∞ y^{2j} k(y) dy` of the strictly positive full source `k`, termwise integration
gives the hyperbolic representations

`Φ(x) = (2/R₀) ∫_0^∞ cosh(xy) k(y) dy`,  `Φ'(x) = (2/R₀) ∫_0^∞ y sinh(xy) k(y) dy`.

Two opposite logarithmic-slope laws follow:

* `Φ'(x)/(xΦ(x)) → 0` as `x → ∞`, because `δ_j → 0`: a finite head is a polynomial dominated by one
  higher term of `Φ`, and the full tail is at most `ε Φ`;
* `Φ'(x)/Φ(x) → ∞`, because the source has positive mass beyond every level: for `y ≥ 2A`,
  `y sinh(xy) ≥ 2A(cosh(xy) - e^{-2Ax})`, while the cosh-mass of `y ≤ 2A` is `O(e^{2Ax})` and the
  mass on `[2A+1, 2A+2]` makes `Φ(x) ≥ c e^{(2A+1)x}`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The real generator and its derivative -/

/-- `Φ(x) = Σ_j c_j x^{2j}`. -/
def liClockThetaGeneratorReal (x : ℝ) : ℝ :=
  ∑' j : ℕ, liClockThetaGeneratorCoeff j * x ^ (2 * j)

/-- `Φ'(x) = Σ_j δ_j c_j x^{2j+1}`. -/
def liClockThetaGeneratorRealDeriv (x : ℝ) : ℝ :=
  ∑' j : ℕ, liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j * x ^ (2 * j + 1)

theorem liClockThetaMomentRatio_mul_coeff (j : ℕ) :
    liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j =
      (2 * j + 2) * liClockThetaGeneratorCoeff (j + 1) := by
  have hν := (thetaCuspNormalizedEvenMoment_pos j).ne'
  have hf : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hj : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  unfold liClockThetaMomentRatio liClockThetaGeneratorCoeff
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

private theorem coeff_le_exp (j : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    liClockThetaGeneratorCoeff j * r ^ j ≤ ((32 / 303) * r) ^ j / (j.factorial : ℝ) := by
  have h := liClockThetaGeneratorCoeff_le j
  calc liClockThetaGeneratorCoeff j * r ^ j ≤ (32 / 303 : ℝ) ^ j / (j.factorial : ℝ) * r ^ j :=
        mul_le_mul_of_nonneg_right h (pow_nonneg hr j)
    _ = ((32 / 303) * r) ^ j / (j.factorial : ℝ) := by rw [mul_pow]; ring

theorem summable_liClockThetaGeneratorReal_term (x : ℝ) :
    Summable fun j : ℕ => liClockThetaGeneratorCoeff j * x ^ (2 * j) := by
  refine (Real.summable_pow_div_factorial ((32 / 303) * x ^ 2)).of_nonneg_of_le
    (fun j => mul_nonneg (liClockThetaGeneratorCoeff_pos j).le (by rw [pow_mul]; positivity))
    fun j => ?_
  rw [pow_mul]
  exact coeff_le_exp j (x ^ 2) (sq_nonneg x)

theorem liClockThetaGenerator_ofReal (x : ℝ) :
    liClockThetaGenerator (x : ℂ) = (liClockThetaGeneratorReal x : ℂ) := by
  unfold liClockThetaGenerator liClockThetaGeneratorReal
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun j => by push_cast; rfl

theorem one_le_liClockThetaGeneratorReal (x : ℝ) : 1 ≤ liClockThetaGeneratorReal x := by
  have h := le_hasSum (summable_liClockThetaGeneratorReal_term x).hasSum 0
    fun j _ => mul_nonneg (liClockThetaGeneratorCoeff_pos j).le (by rw [pow_mul]; positivity)
  unfold liClockThetaGeneratorReal
  simpa [liClockThetaGeneratorCoeff_zero] using h

theorem liClockThetaGeneratorCoeff_mul_le_real (J : ℕ) (x : ℝ) :
    liClockThetaGeneratorCoeff J * x ^ (2 * J) ≤ liClockThetaGeneratorReal x :=
  le_hasSum (summable_liClockThetaGeneratorReal_term x).hasSum J
    fun j _ => mul_nonneg (liClockThetaGeneratorCoeff_pos j).le (by rw [pow_mul]; positivity)

private theorem summable_deg_term (r : ℝ) :
    Summable fun j : ℕ => (2 * (j : ℝ)) * (((32 / 303) * r) ^ j / (j.factorial : ℝ)) := by
  have h := (Real.summable_pow_div_factorial ((32 / 303) * r)).mul_left (2 * ((32 / 303) * r))
  rw [← summable_nat_add_iff 1]
  refine h.congr fun j => ?_
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  field_simp

/-- `Φ' ` is the derivative of `Φ` at every real point. -/
theorem hasDerivAt_liClockThetaGeneratorReal (x : ℝ) :
    HasDerivAt liClockThetaGeneratorReal (liClockThetaGeneratorRealDeriv x) x := by
  set T : ℝ := |x| + 1
  have hT : 1 ≤ T := by simp only [T]; linarith [abs_nonneg x]
  have hg : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      HasDerivAt (fun z => liClockThetaGeneratorCoeff j * z ^ (2 * j))
        (liClockThetaGeneratorCoeff j * ((2 * j : ℕ) * y ^ (2 * j - 1))) y := fun j y _ =>
    (hasDerivAt_pow (2 * j) y).const_mul _
  have hbound : ∀ (j : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) T →
      ‖liClockThetaGeneratorCoeff j * ((2 * j : ℕ) * y ^ (2 * j - 1))‖ ≤
        (2 * (j : ℝ)) * (((32 / 303) * T ^ 2) ^ j / (j.factorial : ℝ)) := by
    intro j y hy
    have hy' : |y| ≤ T := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy; exact hy.le
    have hc := (liClockThetaGeneratorCoeff_pos j).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc, abs_pow, Nat.abs_cast]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    have hyT : |y| ^ (2 * j - 1) ≤ T ^ (2 * j) :=
      (pow_le_pow_left₀ (abs_nonneg y) hy' _).trans (pow_le_pow_right₀ hT (by omega))
    have h1 := coeff_le_exp j (T ^ 2) (by positivity)
    rw [← pow_mul] at h1
    push_cast
    calc liClockThetaGeneratorCoeff j * ((2 * (j : ℝ)) * |y| ^ (2 * j - 1)) ≤
        liClockThetaGeneratorCoeff j * ((2 * (j : ℝ)) * T ^ (2 * j)) := by gcongr
      _ = (2 * (j : ℝ)) * (liClockThetaGeneratorCoeff j * T ^ (2 * j)) := by ring
      _ ≤ (2 * (j : ℝ)) * (((32 / 303) * T ^ 2) ^ j / (j.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have h0T : (0 : ℝ) ∈ Metric.ball (0 : ℝ) T := Metric.mem_ball_self (by linarith)
  have hxT : x ∈ Metric.ball (0 : ℝ) T := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; simp only [T]; linarith
  have h : HasDerivAt (fun z => ∑' j : ℕ, liClockThetaGeneratorCoeff j * z ^ (2 * j))
      (∑' j : ℕ, liClockThetaGeneratorCoeff j * ((2 * j : ℕ) * x ^ (2 * j - 1))) x :=
    hasDerivAt_tsum_of_isPreconnected (g := fun j z => liClockThetaGeneratorCoeff j * z ^ (2 * j))
      (g' := fun j y => liClockThetaGeneratorCoeff j * ((2 * j : ℕ) * y ^ (2 * j - 1)))
      (summable_deg_term (T ^ 2)) Metric.isOpen_ball
      (convex_ball (0 : ℝ) T).isPreconnected hg hbound h0T
      (summable_liClockThetaGeneratorReal_term 0) hxT
  have hval : ∑' j : ℕ, liClockThetaGeneratorCoeff j * ((2 * j : ℕ) * x ^ (2 * j - 1)) =
      liClockThetaGeneratorRealDeriv x := by
    have hs : Summable fun j : ℕ => liClockThetaGeneratorCoeff j * ((2 * j : ℕ) * x ^ (2 * j - 1)) :=
      (summable_deg_term (T ^ 2)).of_norm_bounded fun j => hbound j x hxT
    rw [hs.tsum_eq_zero_add]
    simp only [mul_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add]
    unfold liClockThetaGeneratorRealDeriv
    refine tsum_congr fun j => ?_
    rw [liClockThetaMomentRatio_mul_coeff, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    push_cast; ring
  rw [hval] at h
  exact h

/-! ## The decay law `Φ'(x)/(xΦ(x)) → 0` -/

theorem tendsto_liClockThetaMomentRatio : Tendsto liClockThetaMomentRatio atTop (𝓝 0) := by
  have h := tendsto_thetaCuspRawEvenMoment_oddScaledRatio_zero
  refine h.congr fun j => ?_
  unfold liClockThetaMomentRatio thetaCuspNormalizedEvenMoment
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  have hj := (thetaCuspRawEvenMoment_pos j).ne'
  push_cast
  field_simp

theorem summable_liClockThetaGeneratorRealDeriv_div (x : ℝ) :
    Summable fun j : ℕ => liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j * x ^ (2 * j) := by
  refine ((summable_liClockThetaGeneratorReal_term x).mul_left 1).of_nonneg_of_le
    (fun j => mul_nonneg (mul_nonneg (liClockThetaMomentRatio_pos j).le
      (liClockThetaGeneratorCoeff_pos j).le) (by rw [pow_mul]; positivity)) fun j => ?_
  have hδ := liClockThetaMomentRatio_le j
  have hδ1 : liClockThetaMomentRatio j ≤ 1 := by
    refine hδ.trans ?_
    have : 1 / (303 * (2 * (j : ℝ) + 1)) ≤ 1 / 303 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hc := mul_nonneg (liClockThetaGeneratorCoeff_pos j).le
    (by rw [pow_mul]; positivity : (0 : ℝ) ≤ x ^ (2 * j))
  nlinarith

theorem liClockThetaGeneratorRealDeriv_eq_mul (x : ℝ) :
    liClockThetaGeneratorRealDeriv x =
      x * ∑' j : ℕ, liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j * x ^ (2 * j) := by
  unfold liClockThetaGeneratorRealDeriv
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- **Vanishing relative slope.**  `Φ'(x)/(xΦ(x)) → 0` as `x → ∞`. -/
theorem tendsto_liClockThetaGeneratorRealDeriv_div :
    Tendsto (fun x => liClockThetaGeneratorRealDeriv x / (x * liClockThetaGeneratorReal x))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 tendsto_liClockThetaMomentRatio) (ε / 2) (by positivity)
  set H := ∑ j ∈ Finset.range (J + 1), liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j
  have hH : 0 ≤ H := Finset.sum_nonneg fun j _ =>
    mul_nonneg (liClockThetaMomentRatio_pos j).le (liClockThetaGeneratorCoeff_pos j).le
  set cJ := liClockThetaGeneratorCoeff (J + 1)
  have hcJ : 0 < cJ := liClockThetaGeneratorCoeff_pos _
  refine ⟨max 1 (Real.sqrt (2 * H / (ε * cJ)) + 1), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxs : Real.sqrt (2 * H / (ε * cJ)) < x := by
    have := (le_max_right _ _).trans hx; linarith
  have hΦ := one_le_liClockThetaGeneratorReal x
  have hΦ0 : 0 < liClockThetaGeneratorReal x := by linarith
  set Ψ := ∑' j : ℕ, liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j * x ^ (2 * j)
  have hΨ0 : 0 ≤ Ψ := tsum_nonneg fun j => mul_nonneg (mul_nonneg (liClockThetaMomentRatio_pos j).le
    (liClockThetaGeneratorCoeff_pos j).le) (by rw [pow_mul]; positivity)
  rw [liClockThetaGeneratorRealDeriv_eq_mul, Real.dist_eq, sub_zero,
    show x * Ψ / (x * liClockThetaGeneratorReal x) = Ψ / liClockThetaGeneratorReal x by
      field_simp, abs_of_nonneg (div_nonneg hΨ0 hΦ0.le), div_lt_iff₀ hΦ0]
  -- split head and tail
  have hs := summable_liClockThetaGeneratorRealDeriv_div x
  have hsplit := hs.sum_add_tsum_nat_add (J + 1)
  have htail : ∑' j : ℕ, liClockThetaMomentRatio (j + (J + 1)) *
      liClockThetaGeneratorCoeff (j + (J + 1)) * x ^ (2 * (j + (J + 1))) ≤
        ε / 2 * liClockThetaGeneratorReal x := by
    have hle : ∀ j : ℕ, liClockThetaMomentRatio (j + (J + 1)) *
        liClockThetaGeneratorCoeff (j + (J + 1)) * x ^ (2 * (j + (J + 1))) ≤
          ε / 2 * (liClockThetaGeneratorCoeff (j + (J + 1)) * x ^ (2 * (j + (J + 1)))) := by
      intro j
      have hd := hJ (j + (J + 1)) (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_pos (liClockThetaMomentRatio_pos _)] at hd
      have hc := mul_nonneg (liClockThetaGeneratorCoeff_pos (j + (J + 1))).le
        (by rw [pow_mul]; positivity : (0 : ℝ) ≤ x ^ (2 * (j + (J + 1))))
      nlinarith
    have hsΦ := (summable_nat_add_iff (f := fun j : ℕ => liClockThetaGeneratorCoeff j * x ^ (2 * j))
      (J + 1)).2 (summable_liClockThetaGeneratorReal_term x)
    have hsΨ := (summable_nat_add_iff (f := fun j : ℕ => liClockThetaMomentRatio j *
      liClockThetaGeneratorCoeff j * x ^ (2 * j)) (J + 1)).2 hs
    refine (Summable.tsum_le_tsum hle hsΨ (hsΦ.mul_left _)).trans ?_
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := (summable_liClockThetaGeneratorReal_term x).sum_add_tsum_nat_add (J + 1)
    have hfin : 0 ≤ ∑ i ∈ Finset.range (J + 1), liClockThetaGeneratorCoeff i * x ^ (2 * i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (liClockThetaGeneratorCoeff_pos i).le
        (by rw [pow_mul]; positivity)
    unfold liClockThetaGeneratorReal
    linarith
  have hhead : ∑ i ∈ Finset.range (J + 1), liClockThetaMomentRatio i *
      liClockThetaGeneratorCoeff i * x ^ (2 * i) ≤ H * x ^ (2 * J) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hp : x ^ (2 * i) ≤ x ^ (2 * J) := pow_le_pow_right₀ hx1 (by omega)
    exact mul_le_mul_of_nonneg_left hp (mul_nonneg (liClockThetaMomentRatio_pos i).le
      (liClockThetaGeneratorCoeff_pos i).le)
  have hlow := liClockThetaGeneratorCoeff_mul_le_real (J + 1) x
  have hHx : H * x ^ (2 * J) < ε / 2 * liClockThetaGeneratorReal x := by
    have hsq : 2 * H / (ε * cJ) < x ^ 2 := by
      have h0 : 0 ≤ 2 * H / (ε * cJ) := by positivity
      calc 2 * H / (ε * cJ) = Real.sqrt (2 * H / (ε * cJ)) ^ 2 := (Real.sq_sqrt h0).symm
        _ < x ^ 2 := pow_lt_pow_left₀ hxs (Real.sqrt_nonneg _) (by norm_num)
    rw [div_lt_iff₀ (by positivity)] at hsq
    have hxJ : 0 < x ^ (2 * J) := by positivity
    have e : x ^ (2 * (J + 1)) = x ^ 2 * x ^ (2 * J) := by
      rw [show 2 * (J + 1) = 2 + 2 * J by ring, pow_add]
    rw [e] at hlow
    nlinarith
  have hΨ : Ψ = _ := hsplit.symm
  rw [hΨ]
  linarith

/-! ## Hyperbolic representation over the theta source -/

private theorem continuous_source : Continuous thetaCuspFullSource :=
  contDiff_thetaCuspFullSource.continuous

private theorem integrableOn_cosh_mul_source (x : ℝ) :
    IntegrableOn (fun y => Real.cosh (x * y) * thetaCuspFullSource y) (Ioi 0) := by
  have h1 := HedenmalmThetaSource.integrableOn_exp_mul_thetaCuspFullSource x
  have h2 := HedenmalmThetaSource.integrableOn_exp_mul_thetaCuspFullSource (-x)
  have h3 : IntegrableOn (fun y => (1 / 2 : ℝ) * (Real.exp (x * y) * thetaCuspFullSource y +
      Real.exp (-x * y) * thetaCuspFullSource y)) (Ioi 0) := (h1.add h2).const_mul _
  refine h3.congr_fun (fun y _ => ?_) measurableSet_Ioi
  rw [Real.cosh_eq]
  ring_nf

private theorem abs_mul_sinh_le {x y : ℝ} (hy : 0 ≤ y) :
    |y * Real.sinh (x * y)| ≤ Real.exp ((|x| + 1) * y) := by
  have h2 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have h3 : |Real.sinh (x * y)| ≤ Real.exp (|x| * y) := by
    rw [Real.sinh_eq, abs_div, abs_two, div_le_iff₀ two_pos]
    have ha : Real.exp (x * y) ≤ Real.exp (|x| * y) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self x) hy)
    have hb : Real.exp (-(x * y)) ≤ Real.exp (|x| * y) :=
      Real.exp_le_exp.2 (by nlinarith [neg_abs_le x])
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    linarith
  rw [abs_mul, abs_of_nonneg hy]
  calc y * |Real.sinh (x * y)| ≤ Real.exp y * Real.exp (|x| * y) :=
        mul_le_mul h2 h3 (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((|x| + 1) * y) := by rw [← Real.exp_add]; ring_nf

private theorem integrableOn_mul_sinh_mul_source (x : ℝ) :
    IntegrableOn (fun y => y * Real.sinh (x * y) * thetaCuspFullSource y) (Ioi 0) := by
  refine (HedenmalmThetaSource.integrableOn_exp_mul_thetaCuspFullSource (|x| + 1)).mono'
    (((continuous_id.mul (by fun_prop : Continuous fun y : ℝ => Real.sinh (x * y))).mul
      continuous_source).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
  have hk := (thetaCuspFullSource_pos y).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_right (abs_mul_sinh_le (le_of_lt hy)) hk

private theorem integral_pow_mul_source (j : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * j) * thetaCuspFullSource y = thetaCuspRawEvenMoment j / 2 := by
  unfold thetaCuspRawEvenMoment; ring

private theorem rawMoment_eq (j : ℕ) :
    thetaCuspRawEvenMoment j / 2 = thetaCuspRawEvenMoment 0 / 2 *
      (liClockThetaGeneratorCoeff j * ((2 * j).factorial : ℝ)) := by
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  have hf : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  unfold liClockThetaGeneratorCoeff thetaCuspNormalizedEvenMoment
  field_simp

/-- **Hyperbolic representation.**  `Φ(x) = (2/R₀) ∫_0^∞ cosh(xy) k(y) dy`. -/
theorem liClockThetaGeneratorReal_eq_integral (x : ℝ) :
    liClockThetaGeneratorReal x = 2 / thetaCuspRawEvenMoment 0 *
      ∫ y in Ioi (0 : ℝ), Real.cosh (x * y) * thetaCuspFullSource y := by
  have hR0 := thetaCuspRawEvenMoment_pos 0
  set F : ℕ → ℝ → ℝ := fun j y => (x * y) ^ (2 * j) / ((2 * j).factorial : ℝ) *
    thetaCuspFullSource y with hFdef
  have hFnn : ∀ j y, 0 ≤ F j y := fun j y => by
    simp only [hFdef]
    have := (thetaCuspFullSource_pos y).le
    rw [pow_mul]; positivity
  have hint : ∀ j, Integrable (F j) (volume.restrict (Ioi 0)) := by
    intro j
    refine (integrableOn_cosh_mul_source x).mono' ((by fun_prop : Continuous fun y : ℝ =>
      (x * y) ^ (2 * j) / ((2 * j).factorial : ℝ)).mul continuous_source).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn j y)]
    simp only [hFdef]
    refine mul_le_mul_of_nonneg_right ?_ (thetaCuspFullSource_pos y).le
    exact le_hasSum (Real.hasSum_cosh (x * y)) j fun i _ => by rw [pow_mul]; positivity
  have hval : ∀ j, ∫ y in Ioi (0 : ℝ), F j y = thetaCuspRawEvenMoment 0 / 2 *
      (liClockThetaGeneratorCoeff j * x ^ (2 * j)) := by
    intro j
    have hf : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have e : ∀ y, F j y = x ^ (2 * j) / ((2 * j).factorial : ℝ) * (y ^ (2 * j) *
        thetaCuspFullSource y) := fun y => by simp only [hFdef]; rw [mul_pow]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_pow_mul_source, rawMoment_eq]
    field_simp
  have hnorm : ∀ j, ∫ y in Ioi (0 : ℝ), ‖F j y‖ = ∫ y in Ioi (0 : ℝ), F j y := fun j =>
    setIntegral_congr_fun measurableSet_Ioi fun y _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn j y)]
  have hsum : Summable fun j => ∫ y in Ioi (0 : ℝ), ‖F j y‖ := by
    simp_rw [hnorm, hval]
    exact (summable_liClockThetaGeneratorReal_term x).mul_left _
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hfun : (fun y => ∑' j, F j y) = fun y => Real.cosh (x * y) * thetaCuspFullSource y := by
    funext y
    simp only [hFdef]
    rw [tsum_mul_right, (Real.hasSum_cosh (x * y)).tsum_eq]
  simp_rw [hval] at h
  rw [hfun] at h
  rw [← h.tsum_eq, tsum_mul_left]
  unfold liClockThetaGeneratorReal
  field_simp

private theorem integrableOn_pow_mul_source (n : ℕ) :
    IntegrableOn (fun y => y ^ n * thetaCuspFullSource y) (Ioi 0) := by
  refine ((HedenmalmThetaSource.integrableOn_exp_mul_thetaCuspFullSource 1).const_mul (n.factorial : ℝ)).mono'
    ((by fun_prop : Continuous fun y : ℝ => y ^ n).mul continuous_source).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
  have hk := (thetaCuspFullSource_pos y).le
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have he := Real.pow_div_factorial_le_exp y hy0 n
  rw [div_le_iff₀ hf] at he
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hk, one_mul]
  calc y ^ n * thetaCuspFullSource y ≤ Real.exp y * (n.factorial : ℝ) * thetaCuspFullSource y :=
        mul_le_mul_of_nonneg_right he hk
    _ = (n.factorial : ℝ) * (Real.exp y * thetaCuspFullSource y) := by ring

private theorem fac_succ_two (j : ℕ) :
    ((2 * (j + 1)).factorial : ℝ) = (2 * j + 2) * ((2 * j + 1).factorial : ℝ) := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ]; push_cast; ring

/-- **Hyperbolic representation of the derivative.**
`Φ'(x) = (2/R₀) ∫_0^∞ y sinh(xy) k(y) dy`. -/
theorem liClockThetaGeneratorRealDeriv_eq_integral (x : ℝ) :
    liClockThetaGeneratorRealDeriv x = 2 / thetaCuspRawEvenMoment 0 *
      ∫ y in Ioi (0 : ℝ), y * Real.sinh (x * y) * thetaCuspFullSource y := by
  have hR0 := thetaCuspRawEvenMoment_pos 0
  set F : ℕ → ℝ → ℝ := fun j y => x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) *
    (y ^ (2 * (j + 1)) * thetaCuspFullSource y) with hFdef
  have hint : ∀ j, Integrable (F j) (volume.restrict (Ioi 0)) := fun j =>
    (integrableOn_pow_mul_source (2 * (j + 1))).const_mul _
  have hval : ∀ j, ∫ y in Ioi (0 : ℝ), F j y = thetaCuspRawEvenMoment 0 / 2 *
      (liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j * x ^ (2 * j + 1)) := by
    intro j
    simp only [hFdef]
    rw [integral_const_mul, integral_pow_mul_source, rawMoment_eq,
      liClockThetaMomentRatio_mul_coeff, fac_succ_two]
    have hf : ((2 * j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  have hnorm : ∀ j, ∫ y in Ioi (0 : ℝ), ‖F j y‖ =
      thetaCuspRawEvenMoment 0 / 2 * (liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j *
        |x| ^ (2 * j + 1)) := by
    intro j
    have e : ∀ y ∈ Ioi (0 : ℝ), ‖F j y‖ = |x| ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) *
        (y ^ (2 * (j + 1)) * thetaCuspFullSource y) := fun y hy => by
      have hk := (thetaCuspFullSource_pos y).le
      have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
      simp only [hFdef]
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ (2 * (j + 1)) * thetaCuspFullSource y)]
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, integral_pow_mul_source,
      rawMoment_eq, liClockThetaMomentRatio_mul_coeff, fac_succ_two]
    have hf : ((2 * j + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  have hsum : Summable fun j => ∫ y in Ioi (0 : ℝ), ‖F j y‖ := by
    simp_rw [hnorm]
    refine Summable.mul_left _ ?_
    have h := summable_liClockThetaGeneratorRealDeriv_div |x|
    refine (h.mul_left |x|).congr fun j => ?_
    rw [pow_succ]; ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hfun : (fun y => ∑' j, F j y) =
      fun y => y * Real.sinh (x * y) * thetaCuspFullSource y := by
    funext y
    have hs := Real.hasSum_sinh (x * y)
    rw [show (fun j => F j y) = fun j => (x * y) ^ (2 * j + 1) /
        ((2 * j + 1).factorial : ℝ) * (y * thetaCuspFullSource y) from funext fun j => by
          simp only [hFdef]; rw [mul_pow, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ y];
          ring]
    rw [tsum_mul_right, hs.tsum_eq]
    ring
  simp_rw [hval] at h
  rw [hfun] at h
  rw [← h.tsum_eq, tsum_mul_left]
  unfold liClockThetaGeneratorRealDeriv
  field_simp

/-! ## The growth law `Φ'(x)/Φ(x) → ∞` -/

private theorem integral_source_eq : ∫ y in Ioi (0 : ℝ), thetaCuspFullSource y =
    thetaCuspRawEvenMoment 0 / 2 := by
  have := integral_pow_mul_source 0
  simpa using this

/-- **Unbounded logarithmic slope.**  `Φ'(x)/Φ(x) → ∞` as `x → ∞`. -/
theorem tendsto_liClockThetaGeneratorRealDeriv_div_atTop :
    Tendsto (fun x => liClockThetaGeneratorRealDeriv x / liClockThetaGeneratorReal x)
      atTop atTop := by
  rw [tendsto_atTop]
  intro A
  set A' := max A 1
  have hA' : 0 < A' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set R0 := thetaCuspRawEvenMoment 0
  have hR0 : 0 < R0 := thetaCuspRawEvenMoment_pos 0
  set a := 2 * A'
  set m := ∫ y in Icc (a + 1) (a + 2), thetaCuspFullSource y
  have hm : 0 < m := by
    simp only [m]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (continuous_source.intervalIntegrable _ _)
      (fun y _ => thetaCuspFullSource_pos y) (by linarith)
  have hsrc : ∀ y, 0 ≤ thetaCuspFullSource y := fun y => (thetaCuspFullSource_pos y).le
  -- lower bound for the cosh integral
  have hlowΦ : ∀ x, 0 ≤ x → m * Real.exp ((a + 1) * x) / 2 ≤
      ∫ y in Ioi (0 : ℝ), Real.cosh (x * y) * thetaCuspFullSource y := by
    intro x hx
    have hsub : Icc (a + 1) (a + 2) ⊆ Ioi (0 : ℝ) := fun y hy => by
      have := hy.1; simp only [mem_Ioi]; linarith
    calc m * Real.exp ((a + 1) * x) / 2 = ∫ y in Icc (a + 1) (a + 2),
        Real.exp ((a + 1) * x) / 2 * thetaCuspFullSource y := by
          rw [integral_const_mul]; ring
      _ ≤ ∫ y in Icc (a + 1) (a + 2), Real.cosh (x * y) * thetaCuspFullSource y := by
          refine setIntegral_mono_on ((continuous_const.mul continuous_source).integrableOn_Icc)
            ((integrableOn_cosh_mul_source x).mono_set hsub) measurableSet_Icc fun y hy => ?_
          refine mul_le_mul_of_nonneg_right ?_ (hsrc y)
          rw [Real.cosh_eq]
          have h1 : Real.exp ((a + 1) * x) ≤ Real.exp (x * y) :=
            Real.exp_le_exp.2 (by nlinarith [hy.1])
          linarith [Real.exp_pos (-(x * y))]
      _ ≤ ∫ y in Ioi (0 : ℝ), Real.cosh (x * y) * thetaCuspFullSource y :=
          setIntegral_mono_set (integrableOn_cosh_mul_source x)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ =>
              mul_nonneg (Real.cosh_pos _).le (hsrc y))
            (Eventually.of_forall fun y hy => hsub hy)
  -- upper bound for the prefix cosh mass
  have hprefix : ∀ x, 0 ≤ x → ∫ y in Ioc (0 : ℝ) a, Real.cosh (x * y) * thetaCuspFullSource y ≤
      Real.cosh (a * x) * (R0 / 2) := by
    intro x hx
    calc ∫ y in Ioc (0 : ℝ) a, Real.cosh (x * y) * thetaCuspFullSource y ≤
        ∫ y in Ioc (0 : ℝ) a, Real.cosh (a * x) * thetaCuspFullSource y := by
          refine setIntegral_mono_on ((integrableOn_cosh_mul_source x).mono_set Ioc_subset_Ioi_self)
            ((continuous_const.mul continuous_source).integrableOn_Ioc) measurableSet_Ioc
            fun y hy => mul_le_mul_of_nonneg_right ?_ (hsrc y)
          rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hx hy.1.le),
            abs_of_nonneg (mul_nonneg (by positivity) hx)]
          nlinarith [hy.2]
      _ = Real.cosh (a * x) * ∫ y in Ioc (0 : ℝ) a, thetaCuspFullSource y := integral_const_mul _ _
      _ ≤ Real.cosh (a * x) * (R0 / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.cosh_pos _).le
          rw [← integral_source_eq]
          exact setIntegral_mono_set ((integrableOn_pow_mul_source 0).congr_fun
            (fun y _ => by simp) measurableSet_Ioi)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => hsrc y)
            (Eventually.of_forall fun y hy => Ioc_subset_Ioi_self hy)
  -- the derivative lower bound
  have hk_int : IntegrableOn thetaCuspFullSource (Ioi 0) :=
    (integrableOn_pow_mul_source 0).congr_fun (fun y _ => by simp) measurableSet_Ioi
  have hderiv : ∀ x, 0 ≤ x → a * ((∫ y in Ioi (0 : ℝ), Real.cosh (x * y) * thetaCuspFullSource y) -
      2 * Real.cosh (a * x) * (R0 / 2)) ≤
        ∫ y in Ioi (0 : ℝ), y * Real.sinh (x * y) * thetaCuspFullSource y := by
    intro x hx
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hsplitC := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_cosh_mul_source x).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_cosh_mul_source x).mono_set (Ioi_subset_Ioi ha0))
    rw [Ioc_union_Ioi_eq_Ioi ha0] at hsplitC
    have hsplitS := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_mul_sinh_mul_source x).mono_set Ioc_subset_Ioi_self)
      ((integrableOn_mul_sinh_mul_source x).mono_set (Ioi_subset_Ioi ha0))
    rw [Ioc_union_Ioi_eq_Ioi ha0] at hsplitS
    have hS0 : 0 ≤ ∫ y in Ioc (0 : ℝ) a, y * Real.sinh (x * y) * thetaCuspFullSource y :=
      setIntegral_nonneg measurableSet_Ioc fun y hy =>
        mul_nonneg (mul_nonneg hy.1.le (Real.sinh_nonneg_iff.2 (mul_nonneg hx hy.1.le))) (hsrc y)
    have hkIoi : ∫ y in Ioi a, thetaCuspFullSource y ≤ R0 / 2 := by
      rw [← integral_source_eq]
      exact setIntegral_mono_set hk_int (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ => hsrc y)
        (Eventually.of_forall fun y hy => Ioi_subset_Ioi ha0 hy)
    have htail : a * ((∫ y in Ioi a, Real.cosh (x * y) * thetaCuspFullSource y) -
        ∫ y in Ioi a, thetaCuspFullSource y) ≤
          ∫ y in Ioi a, y * Real.sinh (x * y) * thetaCuspFullSource y := by
      have hint1 := (integrableOn_cosh_mul_source x).mono_set (Ioi_subset_Ioi ha0)
      have hint2 := hk_int.mono_set (Ioi_subset_Ioi ha0)
      rw [← integral_sub hint1 hint2, ← integral_const_mul]
      refine setIntegral_mono_on ((hint1.sub hint2).const_mul a)
        ((integrableOn_mul_sinh_mul_source x).mono_set (Ioi_subset_Ioi ha0)) measurableSet_Ioi
        fun y hy => ?_
      have hy' : a < y := hy
      have hxy : 0 ≤ x * y := mul_nonneg hx (by linarith)
      have hsinh : Real.cosh (x * y) - 1 ≤ Real.sinh (x * y) := by
        have := Real.cosh_sub_sinh (x * y)
        have : Real.exp (-(x * y)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        linarith
      have hs0 : 0 ≤ Real.sinh (x * y) := Real.sinh_nonneg_iff.2 hxy
      have hk := hsrc y
      calc a * (Real.cosh (x * y) * thetaCuspFullSource y - thetaCuspFullSource y) =
          a * (Real.cosh (x * y) - 1) * thetaCuspFullSource y := by ring
        _ ≤ y * Real.sinh (x * y) * thetaCuspFullSource y := by
            refine mul_le_mul_of_nonneg_right ?_ hk
            calc a * (Real.cosh (x * y) - 1) ≤ a * Real.sinh (x * y) :=
                  mul_le_mul_of_nonneg_left hsinh ha0
              _ ≤ y * Real.sinh (x * y) := mul_le_mul_of_nonneg_right hy'.le hs0
    have hmid := hprefix x hx
    have hcosh1 : R0 / 2 ≤ Real.cosh (a * x) * (R0 / 2) :=
      le_mul_of_one_le_left (by positivity) (Real.one_le_cosh _)
    nlinarith
  -- conclusion
  set x₀ := max 0 (Real.log (8 * R0 / m))
  rw [eventually_atTop]
  refine ⟨x₀, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
  have hexp : 8 * R0 / m ≤ Real.exp x := by
    rw [← Real.exp_log (by positivity : 0 < 8 * R0 / m)]
    exact Real.exp_le_exp.2 ((le_max_right _ _).trans hx)
  have h4 : 8 * R0 ≤ m * Real.exp x := by rw [div_le_iff₀ hm] at hexp; linarith
  have hC := hlowΦ x hx0
  have hS := hderiv x hx0
  rw [liClockThetaGeneratorRealDeriv_eq_integral, liClockThetaGeneratorReal_eq_integral,
    mul_div_mul_left _ _ (by positivity : (2 / R0) ≠ 0)]
  set C := ∫ y in Ioi (0 : ℝ), Real.cosh (x * y) * thetaCuspFullSource y
  set S := ∫ y in Ioi (0 : ℝ), y * Real.sinh (x * y) * thetaCuspFullSource y
  have hcoshexp : Real.cosh (a * x) ≤ Real.exp (a * x) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(a * x)) ≤ Real.exp (a * x) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ a) hx0])
    linarith
  have e1 : Real.exp ((a + 1) * x) = Real.exp (a * x) * Real.exp x := by
    rw [← Real.exp_add]; ring_nf
  have hbig : R0 * Real.cosh (a * x) ≤ C / 4 := by
    have h1 : 8 * R0 * Real.exp (a * x) ≤ m * Real.exp ((a + 1) * x) := by
      rw [e1]; nlinarith [Real.exp_pos (a * x)]
    have h2 : R0 * Real.cosh (a * x) ≤ R0 * Real.exp (a * x) :=
      mul_le_mul_of_nonneg_left hcoshexp hR0.le
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le (by positivity) hC
  rw [le_div_iff₀ hCpos]
  have hA'le : A ≤ A' := le_max_left _ _
  have h3 : A * C ≤ A' * C := mul_le_mul_of_nonneg_right hA'le hCpos.le
  have h5 : a * (C - C / 4) ≤ a * (C - 2 * Real.cosh (a * x) * (R0 / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h6 : 0 ≤ A' * C := (mul_pos hA' hCpos).le
  simp only [a] at h5 hS
  linarith

end RHTower
