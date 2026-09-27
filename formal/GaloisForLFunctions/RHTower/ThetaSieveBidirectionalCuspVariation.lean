import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape

/-!
# Prime sieving forces bidirectional signed variation at the theta cusp

Let `δ_j = k_{S_j} - h` be the residual of a cofinal sequence of literal prime deletions of the
completed theta source.  For every fixed `R` its escaped signed moments on `x < -R` converge to
`d_w = (1/2 - w) Γ(w/2 + 5/4) π^{-(w/2+1/4)} > 0`; consequently its positive and negative
variations on `x < -R` are bounded below by `d_w e^{wR}` and `(d_w e^{wR} - d_0)/2`, both
variations of `δ_j` and of `k_{S_j}` diverge, and at the critical scale `w = 1/2 - 1/R` the two-sign
lower bound grows like `e^{R/2}/R`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

/-- The residual `δ = k_S - h` of a finite literal prime deletion. -/
noncomputable def thetaSieveResidual (S : Finset ℕ) (x : ℝ) : ℝ :=
  thetaPrimeDeletion S thetaCuspFullSource x - thetaCuspSourceTerm x 1

/-- The escaped moment `d_w = (1/2 - w) Γ(w/2 + 5/4) π^{-(w/2+1/4)}`. -/
noncomputable def thetaEscapedMoment (w : ℝ) : ℝ :=
  (1 / 2 - w) * Real.Gamma (w / 2 + 5 / 4) * Real.pi ^ (-(w / 2 + 1 / 4))

theorem thetaEscapedMoment_pos {w : ℝ} (hw : -(5 / 2) < w) (hw' : w < 1 / 2) :
    0 < thetaEscapedMoment w := by
  unfold thetaEscapedMoment
  have hΓ : 0 < Real.Gamma (w / 2 + 5 / 4) := Real.Gamma_pos_of_pos (by linarith)
  have hπ : 0 < Real.pi ^ (-(w / 2 + 1 / 4)) := Real.rpow_pos_of_pos Real.pi_pos _
  have : 0 < 1 / 2 - w := by linarith
  positivity

theorem continuous_thetaSieveResidual (S : Finset ℕ) : Continuous (thetaSieveResidual S) :=
  (continuous_thetaPrimeDeletion S continuous_thetaCuspFullSource).sub
    (continuous_thetaCuspSourceTerm 1)

theorem integrable_exp_mul_thetaSeedAtom {w : ℝ} (hw : -(5 / 2) < w) :
    Integrable (fun x : ℝ => Real.exp (w * x) * thetaCuspSourceTerm x 1) :=
  integrable_exp_mul_of_integrable_cexp_mul w
    (integrable_cexp_mul_thetaCuspSourceTerm (w : ℂ) (by simpa using hw) 1 one_pos)

theorem integrable_exp_mul_thetaSieveResidual (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p)
    {w : ℝ} (hw : -(5 / 2) < w) :
    Integrable (fun x : ℝ => Real.exp (w * x) * thetaSieveResidual S x) := by
  have h := (integrable_exp_mul_thetaPrimeDeletion S hS w).sub
    (integrable_exp_mul_thetaSeedAtom hw)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply, thetaSieveResidual]
  ring

theorem integrable_thetaSieveResidual (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    Integrable (thetaSieveResidual S) := by
  simpa using integrable_exp_mul_thetaSieveResidual S hS (w := 0) (by norm_num)

/-- **Weighted residual on right-closed rays.**  For `w > -5/2` and every `R`, the weighted
residual integral over `[-R, ∞)` tends to zero. -/
theorem PrimeExhaustion.tendsto_setIntegral_Ici_exp_mul_thetaSieveResidual
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) {w : ℝ} (hw : -(5 / 2) < w) (R : ℝ) :
    Tendsto (fun j => ∫ x in Set.Ici (-R), Real.exp (w * x) * thetaSieveResidual (S j) x)
      atTop (𝓝 0) := by
  set R' := |R|
  set C := ∑' m, thetaCuspSourceMajorant R' m
  have hC : 0 ≤ C := tsum_nonneg fun m => thetaCuspSourceMajorant_nonneg R' m
  let bound : ℝ → ℝ := fun x => (Set.Icc (-R') 0).indicator (fun _ => Real.exp (|w| * R') * C) x +
    (Real.exp (w * x) * thetaCuspFullSource x + |Real.exp (w * x) * thetaCuspSourceTerm x 1|)
  have hbound : Integrable bound (volume.restrict (Set.Ici (-R))) := by
    apply Integrable.integrableOn
    apply Integrable.add
    · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    · exact (HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource w).add
        (integrable_exp_mul_thetaSeedAtom hw).abs
  have hlim : (∫ _x in Set.Ici (-R), (0 : ℝ)) = 0 := integral_zero _ _
  rw [← hlim]
  apply tendsto_integral_of_dominated_convergence bound
  · intro j
    exact ((by fun_prop : Continuous fun x : ℝ => Real.exp (w * x)).mul
      (continuous_thetaSieveResidual (S j))).aestronglyMeasurable
  · exact hbound
  · intro j
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    by_cases hx0 : x ≤ 0
    · have hmem : x ∈ Set.Icc (-R') 0 :=
        ⟨le_trans (neg_le_neg (le_abs_self R)) (Set.mem_Ici.mp hx), hx0⟩
      have hmem' : x ∈ Set.Icc (-R') R' := ⟨hmem.1, hx0.trans (abs_nonneg R)⟩
      simp only [bound, Set.indicator_of_mem hmem]
      have hres := abs_thetaPrimeDeletion_sub_seed_le (S j) (hS.prime j) hmem'
      have hexp : Real.exp (w * x) ≤ Real.exp (|w| * R') := by
        apply Real.exp_le_exp.mpr
        have : |x| ≤ R' := abs_le.mpr ⟨hmem.1, hx0.trans (abs_nonneg R)⟩
        calc w * x ≤ |w * x| := le_abs_self _
          _ = |w| * |x| := abs_mul _ _
          _ ≤ |w| * R' := mul_le_mul_of_nonneg_left this (abs_nonneg w)
      have h1 : Real.exp (w * x) * |thetaSieveResidual (S j) x| ≤ Real.exp (|w| * R') * C :=
        mul_le_mul hexp hres (abs_nonneg _) (Real.exp_pos _).le
      have h2 : 0 ≤ Real.exp (w * x) * thetaCuspFullSource x :=
        mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos_all x).le
      have h3 := abs_nonneg (Real.exp (w * x) * thetaCuspSourceTerm x 1)
      linarith
    · have hx0' : 0 ≤ x := le_of_lt (not_le.mp hx0)
      have hmem : x ∉ Set.Icc (-R') 0 := fun h => hx0 h.2
      simp only [bound, Set.indicator_of_notMem hmem, zero_add]
      obtain ⟨_, h2⟩ := thetaCuspSourceTerm_one_le_thetaPrimeDeletion (S j) (hS.prime j) hx0'
      have hD := (thetaPrimeDeletion_pos_of_nonneg (S j) (hS.prime j) hx0').le
      have habs : |thetaSieveResidual (S j) x| ≤
          thetaCuspFullSource x + |thetaCuspSourceTerm x 1| := by
        unfold thetaSieveResidual
        calc
          |thetaPrimeDeletion (S j) thetaCuspFullSource x - thetaCuspSourceTerm x 1| ≤
              |thetaPrimeDeletion (S j) thetaCuspFullSource x| + |thetaCuspSourceTerm x 1| :=
            abs_sub _ _
          _ ≤ thetaCuspFullSource x + |thetaCuspSourceTerm x 1| := by
            rw [abs_of_nonneg hD]
            linarith
      rw [abs_mul, abs_of_pos (Real.exp_pos (w * x))]
      nlinarith [Real.exp_pos (w * x)]
  · filter_upwards with x
    have h := ((hS.tendsto_thetaPrimeDeletion x).sub_const (thetaCuspSourceTerm x 1)).const_mul
      (Real.exp (w * x))
    rw [sub_self, mul_zero] at h
    exact h

/-- The full-line weighted residual tends to the escaped moment `d_w`. -/
theorem PrimeExhaustion.tendsto_integral_exp_mul_thetaSieveResidual
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) {w : ℝ} (hw : -(1 / 2) < w) (hw' : w ≤ 1 / 2) :
    Tendsto (fun j => ∫ x : ℝ, Real.exp (w * x) * thetaSieveResidual (S j) x)
      atTop (𝓝 (thetaEscapedMoment w)) := by
  have hseed := integral_exp_mul_thetaSeedAtom w (by linarith)
  have h := (hS.tendsto_integral_exp_mul_thetaPrimeDeletion hw hw').sub_const
    (∫ x : ℝ, Real.exp (w * x) * thetaCuspSourceTerm x 1)
  rw [hseed, zero_sub] at h
  have heq : (fun j => ∫ x : ℝ, Real.exp (w * x) * thetaSieveResidual (S j) x) =
      fun j => (∫ x : ℝ, Real.exp (w * x) * thetaPrimeDeletion (S j) thetaCuspFullSource x) -
        (w - 1 / 2) * Real.Gamma (w / 2 + 5 / 4) * Real.pi ^ (-(w / 2 + 1 / 4)) := by
    funext j
    rw [← hseed, ← integral_sub (integrable_exp_mul_thetaPrimeDeletion (S j)
      (fun p hp => (hS.prime j p hp).pos) w) (integrable_exp_mul_thetaSeedAtom (by linarith))]
    apply integral_congr_ae
    filter_upwards with x
    simp only [thetaSieveResidual]
    ring
  rw [heq]
  convert h using 2
  unfold thetaEscapedMoment
  ring

/-- **Escaped signed moments (1).**  For every fixed `R`, the weighted residual on `x < -R`
tends to `d_w`. -/
theorem PrimeExhaustion.tendsto_setIntegral_Iio_exp_mul_thetaSieveResidual
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) {w : ℝ} (hw : -(1 / 2) < w) (hw' : w ≤ 1 / 2)
    (R : ℝ) :
    Tendsto (fun j => ∫ x in Set.Iio (-R), Real.exp (w * x) * thetaSieveResidual (S j) x)
      atTop (𝓝 (thetaEscapedMoment w)) := by
  have hfull := hS.tendsto_integral_exp_mul_thetaSieveResidual hw hw'
  have hright := hS.tendsto_setIntegral_Ici_exp_mul_thetaSieveResidual (w := w) (by linarith) R
  have h := hfull.sub hright
  rw [sub_zero] at h
  refine h.congr (fun j => ?_)
  have hsplit := integral_add_compl (measurableSet_Ici (a := -R))
    (integrable_exp_mul_thetaSieveResidual (S j) (fun p hp => (hS.prime j p hp).pos)
      (w := w) (by linarith))
  rw [Set.compl_Ici] at hsplit
  linarith


/-! ## Positive and negative variations at the negative cusp -/

/-- Positive variation `P(R) = ∫_{x<-R} δ_+`. -/
noncomputable def thetaCuspPositiveVariation (S : Finset ℕ) (R : ℝ) : ℝ :=
  ∫ x in Set.Iio (-R), max (thetaSieveResidual S x) 0

/-- Negative variation `N(R) = ∫_{x<-R} δ_-`. -/
noncomputable def thetaCuspNegativeVariation (S : Finset ℕ) (R : ℝ) : ℝ :=
  ∫ x in Set.Iio (-R), max (-thetaSieveResidual S x) 0

private theorem integrableOn_pos_neg (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (R : ℝ) :
    IntegrableOn (fun x => max (thetaSieveResidual S x) 0) (Set.Iio (-R)) ∧
      IntegrableOn (fun x => max (-thetaSieveResidual S x) 0) (Set.Iio (-R)) :=
  ⟨(integrable_thetaSieveResidual S hS).pos_part.integrableOn,
    (integrable_thetaSieveResidual S hS).neg_part.integrableOn⟩

theorem thetaCuspVariation_sub (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (R : ℝ) :
    thetaCuspPositiveVariation S R - thetaCuspNegativeVariation S R =
      ∫ x in Set.Iio (-R), thetaSieveResidual S x := by
  obtain ⟨h1, h2⟩ := integrableOn_pos_neg S hS R
  rw [thetaCuspPositiveVariation, thetaCuspNegativeVariation, ← integral_sub h1 h2]
  congr 1
  funext x
  exact max_zero_sub_eq_self _

theorem thetaCuspVariation_add (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (R : ℝ) :
    thetaCuspPositiveVariation S R + thetaCuspNegativeVariation S R =
      ∫ x in Set.Iio (-R), |thetaSieveResidual S x| := by
  obtain ⟨h1, h2⟩ := integrableOn_pos_neg S hS R
  rw [thetaCuspPositiveVariation, thetaCuspNegativeVariation, ← integral_add h1 h2]
  congr 1
  funext x
  rcases le_total 0 (thetaSieveResidual S x) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]
    ring

/-- For `w ≥ 0` the weighted moment on `x < -R` is controlled by `e^{-wR}(P + N)`. -/
theorem abs_setIntegral_Iio_exp_mul_le (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) {w : ℝ}
    (hw : 0 ≤ w) (R : ℝ) :
    |∫ x in Set.Iio (-R), Real.exp (w * x) * thetaSieveResidual S x| ≤
      Real.exp (-(w * R)) *
        (thetaCuspPositiveVariation S R + thetaCuspNegativeVariation S R) := by
  rw [thetaCuspVariation_add S hS R, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  apply setIntegral_mono_on
  · exact ((integrable_exp_mul_thetaSieveResidual S hS (w := w) (by linarith)).abs).integrableOn
  · exact ((integrable_thetaSieveResidual S hS).abs.const_mul _).integrableOn
  · exact measurableSet_Iio
  · intro x hx
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have : x < -R := hx
    nlinarith

/-- **Two-sign lower bound (2).**  For `0 ≤ w ≤ 1/2`, eventually `P + N ≥ d_w e^{wR} - ε`. -/
theorem PrimeExhaustion.eventually_variation_add_ge {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1 / 2) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, thetaEscapedMoment w * Real.exp (w * R) - ε ≤
      thetaCuspPositiveVariation (S j) R + thetaCuspNegativeVariation (S j) R := by
  have hlim := hS.tendsto_setIntegral_Iio_exp_mul_thetaSieveResidual (by linarith) hw' R
  have hδ : 0 < ε * Real.exp (-(w * R)) := mul_pos hε (Real.exp_pos _)
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds _ hδ)] with j hj
  rw [Real.dist_eq] at hj
  have hbound := abs_setIntegral_Iio_exp_mul_le (S j) (fun p hp => (hS.prime j p hp).pos) hw R
  have hlow : thetaEscapedMoment w - ε * Real.exp (-(w * R)) ≤
      |∫ x in Set.Iio (-R), Real.exp (w * x) * thetaSieveResidual (S j) x| := by
    have := (abs_lt.mp hj).1
    linarith [le_abs_self (∫ x in Set.Iio (-R), Real.exp (w * x) * thetaSieveResidual (S j) x)]
  have hexp : Real.exp (w * R) * Real.exp (-(w * R)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_left (hlow.trans hbound) (Real.exp_pos (w * R)).le
  have e1 : Real.exp (w * R) * (thetaEscapedMoment w - ε * Real.exp (-(w * R))) =
      thetaEscapedMoment w * Real.exp (w * R) - ε := by
    rw [mul_sub, ← mul_assoc, mul_comm (Real.exp (w * R)) ε, mul_assoc, hexp]
    ring
  have e2 : Real.exp (w * R) * (Real.exp (-(w * R)) *
      (thetaCuspPositiveVariation (S j) R + thetaCuspNegativeVariation (S j) R)) =
      thetaCuspPositiveVariation (S j) R + thetaCuspNegativeVariation (S j) R := by
    rw [← mul_assoc, hexp, one_mul]
  linarith

/-- **Signed limit (2).**  `P - N → d_0`. -/
theorem PrimeExhaustion.tendsto_variation_sub {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    (R : ℝ) :
    Tendsto (fun j => thetaCuspPositiveVariation (S j) R - thetaCuspNegativeVariation (S j) R)
      atTop (𝓝 (thetaEscapedMoment 0)) := by
  have h := hS.tendsto_setIntegral_Iio_exp_mul_thetaSieveResidual (w := 0) (by norm_num)
    (by norm_num) R
  refine h.congr (fun j => ?_)
  rw [thetaCuspVariation_sub (S j) (fun p hp => (hS.prime j p hp).pos)]
  simp

/-- **Both variations are large (3).**  Eventually `min(P,N) ≥ (d_w e^{wR} - d_0)/2 - ε`. -/
theorem PrimeExhaustion.eventually_variation_min_ge {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {w : ℝ} (hw : 0 ≤ w) (hw' : w ≤ 1 / 2) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, (thetaEscapedMoment w * Real.exp (w * R) - thetaEscapedMoment 0) / 2 - ε ≤
      min (thetaCuspPositiveVariation (S j) R) (thetaCuspNegativeVariation (S j) R) := by
  filter_upwards [hS.eventually_variation_add_ge hw hw' R hε,
    (hS.tendsto_variation_sub R).eventually (Metric.ball_mem_nhds _ hε)] with j hadd hsub
  rw [Real.dist_eq] at hsub
  have := abs_lt.mp hsub
  have hd0 : 0 < thetaEscapedMoment 0 := thetaEscapedMoment_pos (by norm_num) (by norm_num)
  rcases le_total (thetaCuspPositiveVariation (S j) R) (thetaCuspNegativeVariation (S j) R)
    with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- **Both total variations of the residual diverge.** -/
theorem PrimeExhaustion.tendsto_residual_variations {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    (M : ℝ) :
    ∀ᶠ j in atTop, M ≤ (∫ x : ℝ, max (thetaSieveResidual (S j) x) 0) ∧
      M ≤ ∫ x : ℝ, max (-thetaSieveResidual (S j) x) 0 := by
  set d := thetaEscapedMoment (1 / 4)
  have hd : 0 < d := thetaEscapedMoment_pos (by norm_num) (by norm_num)
  have hgrow : Tendsto (fun R : ℝ => d * Real.exp ((1 / 4) * R)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).const_mul_atTop hd
  obtain ⟨R, hR⟩ := (hgrow.eventually_ge_atTop (2 * (M + 1) + thetaEscapedMoment 0)).exists
  filter_upwards [hS.eventually_variation_min_ge (w := 1 / 4) (by norm_num) (by norm_num) R
    one_pos] with j hj
  have hint := integrable_thetaSieveResidual (S j) (fun p hp => (hS.prime j p hp).pos)
  have hmin : M ≤ min (thetaCuspPositiveVariation (S j) R) (thetaCuspNegativeVariation (S j) R) := by
    linarith
  constructor
  · refine (hmin.trans (min_le_left _ _)).trans ?_
    exact setIntegral_le_integral hint.pos_part (Eventually.of_forall fun x => le_max_right _ _)
  · refine (hmin.trans (min_le_right _ _)).trans ?_
    exact setIntegral_le_integral hint.neg_part (Eventually.of_forall fun x => le_max_right _ _)

/-- **The deleted sources themselves have divergent two-sign variation**, while their signed
ordinary mass tends to zero. -/
theorem PrimeExhaustion.tendsto_thetaPrimeDeletion_variations {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (M : ℝ) :
    ∀ᶠ j in atTop, M ≤ (∫ x : ℝ, max (thetaPrimeDeletion (S j) thetaCuspFullSource x) 0) ∧
      M ≤ ∫ x : ℝ, max (-thetaPrimeDeletion (S j) thetaCuspFullSource x) 0 := by
  have hh : Integrable (fun x : ℝ => |thetaCuspSourceTerm x 1|) :=
    integrable_thetaCuspSourceTerm_one.abs
  filter_upwards [hS.tendsto_residual_variations (M + ∫ x : ℝ, |thetaCuspSourceTerm x 1|)]
    with j hj
  have hint := integrable_thetaPrimeDeletion (S j) (fun p hp => (hS.prime j p hp).pos)
  have hres := integrable_thetaSieveResidual (S j) (fun p hp => (hS.prime j p hp).pos)
  constructor
  · have hle : (∫ x : ℝ, max (thetaSieveResidual (S j) x) 0) - ∫ x : ℝ, |thetaCuspSourceTerm x 1| ≤
        ∫ x : ℝ, max (thetaPrimeDeletion (S j) thetaCuspFullSource x) 0 := by
      rw [← integral_sub hres.pos_part hh]
      apply integral_mono (hres.pos_part.sub hh) hint.pos_part
      intro x
      simp only [Pi.sub_apply, thetaSieveResidual]
      rcases le_total 0 (thetaPrimeDeletion (S j) thetaCuspFullSource x -
        thetaCuspSourceTerm x 1) with h | h
      · rw [max_eq_left h]
        have := neg_abs_le (thetaCuspSourceTerm x 1)
        exact le_trans (by linarith) (le_max_left _ _)
      · rw [max_eq_right h]
        exact le_trans (by linarith [abs_nonneg (thetaCuspSourceTerm x 1)]) (le_max_right _ _)
    linarith [hj.1]
  · have hle : (∫ x : ℝ, max (-thetaSieveResidual (S j) x) 0) -
        ∫ x : ℝ, |thetaCuspSourceTerm x 1| ≤
        ∫ x : ℝ, max (-thetaPrimeDeletion (S j) thetaCuspFullSource x) 0 := by
      rw [← integral_sub hres.neg_part hh]
      apply integral_mono (hres.neg_part.sub hh) hint.neg_part
      intro x
      simp only [Pi.sub_apply, thetaSieveResidual]
      rcases le_total 0 (-(thetaPrimeDeletion (S j) thetaCuspFullSource x -
        thetaCuspSourceTerm x 1)) with h | h
      · rw [max_eq_left h]
        have := le_abs_self (thetaCuspSourceTerm x 1)
        exact le_trans (by linarith) (le_max_left _ _)
      · rw [max_eq_right h]
        exact le_trans (by linarith [abs_nonneg (thetaCuspSourceTerm x 1)]) (le_max_right _ _)
    linarith [hj.2]


/-! ## The critical half-density scale -/

/-- The Gamma factor `G(w) = Γ(w/2 + 5/4) π^{-(w/2+1/4)}`, so `d_w = (1/2 - w) G(w)`. -/
noncomputable def thetaAtomGammaFactor (w : ℝ) : ℝ :=
  Real.Gamma (w / 2 + 5 / 4) * Real.pi ^ (-(w / 2 + 1 / 4))

theorem thetaEscapedMoment_eq (w : ℝ) :
    thetaEscapedMoment w = (1 / 2 - w) * thetaAtomGammaFactor w := by
  unfold thetaEscapedMoment thetaAtomGammaFactor
  ring

/-- `G` has a strictly positive minimum on `[0, 1/2]`. -/
theorem exists_thetaAtomGammaFactor_lower_bound :
    ∃ c > 0, ∀ w ∈ Set.Icc (0 : ℝ) (1 / 2), c ≤ thetaAtomGammaFactor w := by
  have hcont : ContinuousOn thetaAtomGammaFactor (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    unfold thetaAtomGammaFactor
    apply ContinuousAt.mul
    · have hΓ : ContinuousAt Real.Gamma (w / 2 + 5 / 4) := by
        apply (Real.differentiableAt_Gamma _).continuousAt
        intro m hm
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith [hw.1]
      exact hΓ.comp (f := fun w : ℝ => w / 2 + 5 / 4) (by fun_prop)
    · exact (Real.continuousAt_const_rpow Real.pi_ne_zero).comp (by fun_prop)
  obtain ⟨w₀, hw₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) hcont
  refine ⟨thetaAtomGammaFactor w₀, ?_, fun w hw => hmin hw⟩
  unfold thetaAtomGammaFactor
  exact mul_pos (Real.Gamma_pos_of_pos (by linarith [hw₀.1]))
    (Real.rpow_pos_of_pos Real.pi_pos _)

/-- **Critical-scale lower bound (4).**  If `c ≤ G` on `[0,1/2]` and `R > 2`, then eventually
`P + N ≥ c e^{R/2}/(eR) - ε` and `min(P,N) ≥ (c e^{R/2}/(eR) - d_0)/2 - ε`. -/
theorem PrimeExhaustion.eventually_variation_critical_scale {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) {c : ℝ} (hc : ∀ w ∈ Set.Icc (0 : ℝ) (1 / 2), c ≤ thetaAtomGammaFactor w)
    {R : ℝ} (hR : 2 < R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      c / (Real.exp 1 * R) * Real.exp (R / 2) - ε ≤
          thetaCuspPositiveVariation (S j) R + thetaCuspNegativeVariation (S j) R ∧
        (c / (Real.exp 1 * R) * Real.exp (R / 2) - thetaEscapedMoment 0) / 2 - ε ≤
          min (thetaCuspPositiveVariation (S j) R) (thetaCuspNegativeVariation (S j) R) := by
  have hR0 : 0 < R := by linarith
  set wR : ℝ := 1 / 2 - 1 / R
  have hw0 : 0 ≤ wR := by
    have : 1 / R < 1 / 2 := by rw [div_lt_div_iff₀ hR0 (by norm_num)]; linarith
    simp only [wR]; linarith
  have hw1 : wR ≤ 1 / 2 := by
    have : 0 < 1 / R := by positivity
    simp only [wR]; linarith
  have hkey : c / (Real.exp 1 * R) * Real.exp (R / 2) ≤
      thetaEscapedMoment wR * Real.exp (wR * R) := by
    rw [thetaEscapedMoment_eq, show 1 / 2 - wR = 1 / R by simp only [wR]; ring,
      show wR * R = R / 2 - 1 by simp only [wR]; field_simp, Real.exp_sub]
    have hG := hc wR ⟨hw0, hw1⟩
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hE : 0 < Real.exp (R / 2) := Real.exp_pos _
    rw [show c / (Real.exp 1 * R) * Real.exp (R / 2) = c * (1 / R * (Real.exp (R / 2) /
        Real.exp 1)) by field_simp,
      show 1 / R * thetaAtomGammaFactor wR * (Real.exp (R / 2) / Real.exp 1) =
        thetaAtomGammaFactor wR * (1 / R * (Real.exp (R / 2) / Real.exp 1)) by ring]
    exact mul_le_mul_of_nonneg_right hG (by positivity)
  filter_upwards [hS.eventually_variation_add_ge hw0 hw1 R hε,
    hS.eventually_variation_min_ge hw0 hw1 R hε] with j h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The critical two-sign scale diverges like `e^{R/2}/R`. -/
theorem tendsto_critical_variation_scale {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => c / (Real.exp 1 * R) * Real.exp (R / 2)) atTop atTop := by
  have h := (Real.tendsto_exp_div_pow_atTop 1).comp (tendsto_id.atTop_div_const (by norm_num :
    (0 : ℝ) < 2))
  have h2 := h.const_mul_atTop (show 0 < c / (2 * Real.exp 1) by positivity)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  simp only [Function.comp_apply, id, pow_one]
  field_simp

end RHTower
