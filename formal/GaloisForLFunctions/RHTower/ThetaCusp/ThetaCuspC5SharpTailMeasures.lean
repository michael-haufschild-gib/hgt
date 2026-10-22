import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegimeOneCurvatureSigns

/-!
# Sharp tail data for the theta-cusp likelihood: the second atom and the deep tail

The higher-likelihood spectral measure is the sum of the atom measures `n ≥ 2`.  This module
splits off the second atom (`n = 2`, support edge `3`) from the deep tail (`n ≥ 3`, support
edge `8`), proves the closed forms of the second-atom tilted moments
`M⁽²⁾_j(B) = e^{-9/2} e^{-3B} N_j(B) / B^{j+1}` for `j ≤ 7`, and the sharp support comparison
`M⁽³⁾_m(B) ≤ 8^m e^{-8(B-B₀)} M⁽³⁾_0(B₀)` for the deep tail.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## The two components of the higher spectral measure -/

/-- The second-atom spectral measure. -/
def thetaCuspSecondAtomSpectralMeasure : Measure ℝ := thetaCuspAtomLikelihoodSpectralMeasure 2

/-- The deep-tail spectral measure (atoms `n ≥ 3`). -/
def thetaCuspDeepTailSpectralMeasure : Measure ℝ :=
  Measure.sum fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k + 3)

theorem thetaCuspHigherLikelihoodSpectralMeasure_eq_second_add_deep :
    thetaCuspHigherLikelihoodSpectralMeasure =
      thetaCuspSecondAtomSpectralMeasure + thetaCuspDeepTailSpectralMeasure := by
  ext s hs
  rw [thetaCuspHigherLikelihoodSpectralMeasure, Measure.sum_apply _ hs, Measure.add_apply,
    thetaCuspDeepTailSpectralMeasure, Measure.sum_apply _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  rfl

theorem thetaCuspSecondAtomSpectralMeasure_le :
    thetaCuspSecondAtomSpectralMeasure ≤ thetaCuspHigherLikelihoodSpectralMeasure := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure_eq_second_add_deep]
  exact Measure.le_add_right le_rfl

theorem thetaCuspDeepTailSpectralMeasure_le :
    thetaCuspDeepTailSpectralMeasure ≤ thetaCuspHigherLikelihoodSpectralMeasure := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure_eq_second_add_deep]
  exact Measure.le_add_left le_rfl

theorem ae_nonneg_thetaCuspSecondAtomSpectralMeasure :
    ∀ᵐ t ∂thetaCuspSecondAtomSpectralMeasure, 0 ≤ t :=
  ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure.filter_mono
    (ae_mono thetaCuspSecondAtomSpectralMeasure_le)

theorem ae_nonneg_thetaCuspDeepTailSpectralMeasure :
    ∀ᵐ t ∂thetaCuspDeepTailSpectralMeasure, 0 ≤ t :=
  ae_nonneg_thetaCuspHigherLikelihoodSpectralMeasure.filter_mono
    (ae_mono thetaCuspDeepTailSpectralMeasure_le)

/-- The deep tail has the sharp lower support edge `8`. -/
theorem ae_eight_le_thetaCuspDeepTailSpectralMeasure :
    ∀ᵐ t ∂thetaCuspDeepTailSpectralMeasure, 8 ≤ t := by
  rw [thetaCuspDeepTailSpectralMeasure, Measure.ae_sum_iff]
  intro k
  have hgap : (8 : ℝ) ≤ thetaCuspLikelihoodGap (k + 3) := by
    unfold thetaCuspLikelihoodGap
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [thetaCuspAtomLikelihoodSpectralMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff measurableSet_Ici]
    exact hgap
  · apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hgap.trans ht.le

theorem integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure (m : ℕ) {B : ℝ}
    (hB : 0 < B) :
    Integrable (fun t : ℝ => t ^ m * Real.exp (-B * t)) thetaCuspSecondAtomSpectralMeasure :=
  (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB).mono_measure
    thetaCuspSecondAtomSpectralMeasure_le

theorem integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure (m : ℕ) {B : ℝ}
    (hB : 0 < B) :
    Integrable (fun t : ℝ => t ^ m * Real.exp (-B * t)) thetaCuspDeepTailSpectralMeasure :=
  (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB).mono_measure
    thetaCuspDeepTailSpectralMeasure_le

/-! ## Generic moment derivative law -/

/-- Tilted moments of any measure carried by `[0, ∞)` with all polynomial-exponential moments
integrable differentiate to minus the successor moment. -/
theorem hasDerivAt_tiltedMoment_of_measure {ν : Measure ℝ}
    (hint : ∀ (m : ℕ) {c : ℝ}, 0 < c → Integrable (fun t : ℝ => t ^ m * Real.exp (-c * t)) ν)
    (hae : ∀ᵐ t ∂ν, 0 ≤ t) (m : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q : ℝ => ∫ t, t ^ m * Real.exp (-q * t) ∂ν)
      (-∫ t, t ^ (m + 1) * Real.exp (-B * t) ∂ν) B := by
  let s : Set ℝ := Metric.ball B (B / 2)
  let bound : ℝ → ℝ := fun t => t ^ (m + 1) * Real.exp (-(B / 2) * t)
  have hs : s ∈ nhds B := Metric.ball_mem_nhds B (half_pos hB)
  have hpositive : ∀ z ∈ s, B / 2 < z := by
    intro z hz
    have habs : |z - B| < B / 2 := by
      simpa [s, Real.dist_eq] using hz
    have hneg : -(B / 2) < z - B := neg_lt_of_abs_lt habs
    linarith
  have hFmeas : ∀ᶠ z in nhds B,
      AEStronglyMeasurable (fun t : ℝ => t ^ m * Real.exp (-z * t)) ν := by
    filter_upwards with z
    exact (by fun_prop : Continuous (fun t : ℝ => t ^ m * Real.exp (-z * t))).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun t : ℝ => -(t ^ (m + 1)) * Real.exp (-B * t)) ν :=
    (by fun_prop : Continuous (fun t : ℝ => -(t ^ (m + 1)) * Real.exp (-B * t))).aestronglyMeasurable
  have hboundInt : Integrable bound ν := by
    simpa [bound] using hint (m + 1) (half_pos hB)
  have hdom : ∀ᵐ t ∂ν, ∀ z ∈ s, ‖-(t ^ (m + 1)) * Real.exp (-z * t)‖ ≤ bound t := by
    filter_upwards [hae] with t ht
    intro z hz
    have hzLower := hpositive z hz
    have hexp : Real.exp (-z * t) ≤ Real.exp (-(B / 2) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg ht _),
      abs_of_pos (Real.exp_pos _)]
    dsimp [bound]
    exact mul_le_mul_of_nonneg_left hexp (pow_nonneg ht _)
  have hdiff : ∀ᵐ t ∂ν, ∀ z ∈ s,
      HasDerivAt (fun q : ℝ => t ^ m * Real.exp (-q * t)) (-(t ^ (m + 1)) * Real.exp (-z * t)) z := by
    filter_upwards with t z hz
    have hinner : HasDerivAt (fun q : ℝ => -q * t) (-t) z := by
      simpa using (hasDerivAt_id z).neg.mul_const t
    have hexp : HasDerivAt (fun q : ℝ => Real.exp (-q * t)) (-t * Real.exp (-z * t)) z := by
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp (-z * t)).comp z hinner
    have hmul := (hasDerivAt_const z (t ^ m)).mul hexp
    exact hmul.congr_deriv (by rw [pow_succ]; ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun z t : ℝ => t ^ m * Real.exp (-z * t))
    (F' := fun z t : ℝ => -(t ^ (m + 1)) * Real.exp (-z * t))
    (bound := bound) hs hFmeas (hint m hB) hF'meas hdom hboundInt hdiff
  exact hmain.2.congr_deriv (by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    ring)

/-! ## The two moment families -/

/-- Tilted moments of the second atom. -/
def thetaCuspSecondAtomMoment (B : ℝ) (m : ℕ) : ℝ :=
  ∫ t, t ^ m * Real.exp (-B * t) ∂thetaCuspSecondAtomSpectralMeasure

/-- Tilted moments of the deep tail. -/
def thetaCuspDeepTailMoment (B : ℝ) (m : ℕ) : ℝ :=
  ∫ t, t ^ m * Real.exp (-B * t) ∂thetaCuspDeepTailSpectralMeasure

theorem thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep {B : ℝ} (hB : 0 < B) (m : ℕ) :
    thetaCuspHigherLikelihoodSpectralMoment B m =
      thetaCuspSecondAtomMoment B m + thetaCuspDeepTailMoment B m := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral, thetaCuspSecondAtomMoment,
    thetaCuspDeepTailMoment, thetaCuspHigherLikelihoodSpectralMeasure_eq_second_add_deep,
    integral_add_measure (integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure m hB)
      (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure m hB)]

theorem thetaCuspSecondAtomMoment_nonneg (B : ℝ) (m : ℕ) : 0 ≤ thetaCuspSecondAtomMoment B m := by
  unfold thetaCuspSecondAtomMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_nonneg_thetaCuspSecondAtomSpectralMeasure] with t ht
  positivity

theorem thetaCuspDeepTailMoment_nonneg (B : ℝ) (m : ℕ) : 0 ≤ thetaCuspDeepTailMoment B m := by
  unfold thetaCuspDeepTailMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_nonneg_thetaCuspDeepTailSpectralMeasure] with t ht
  positivity

theorem hasDerivAt_thetaCuspSecondAtomMoment (m : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q => thetaCuspSecondAtomMoment q m) (-thetaCuspSecondAtomMoment B (m + 1)) B :=
  hasDerivAt_tiltedMoment_of_measure
    (fun m _ hc => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure m hc)
    ae_nonneg_thetaCuspSecondAtomSpectralMeasure m hB

theorem hasDerivAt_thetaCuspDeepTailMoment (m : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q => thetaCuspDeepTailMoment q m) (-thetaCuspDeepTailMoment B (m + 1)) B :=
  hasDerivAt_tiltedMoment_of_measure
    (fun m _ hc => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure m hc)
    ae_nonneg_thetaCuspDeepTailSpectralMeasure m hB

/-! ## Second-atom closed forms -/

/-- Derivative of an explicit polynomial of degree at most eight. -/
theorem hasDerivAt_poly8 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ B : ℝ) :
    HasDerivAt (fun x : ℝ => a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 +
        a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8)
      (a₁ + 2 * a₂ * B + 3 * a₃ * B ^ 2 + 4 * a₄ * B ^ 3 + 5 * a₅ * B ^ 4 + 6 * a₆ * B ^ 5 +
        7 * a₇ * B ^ 6 + 8 * a₈ * B ^ 7) B := by
  have h := ((((((((hasDerivAt_const B a₀).add ((hasDerivAt_id B).const_mul a₁)).add
    ((hasDerivAt_pow 2 B).const_mul a₂)).add ((hasDerivAt_pow 3 B).const_mul a₃)).add
    ((hasDerivAt_pow 4 B).const_mul a₄)).add ((hasDerivAt_pow 5 B).const_mul a₅)).add
    ((hasDerivAt_pow 6 B).const_mul a₆)).add ((hasDerivAt_pow 7 B).const_mul a₇)).add
    ((hasDerivAt_pow 8 B).const_mul a₈)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- Derivative of `e^{-9/2} e^{-3q} N(q) / q^{k+1}`. -/
theorem expProfile_hasDerivAt {N N' : ℝ → ℝ} (hN : ∀ q, HasDerivAt N (N' q) q) (k : ℕ) {B : ℝ}
    (hB : 0 < B) :
    HasDerivAt (fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (N q / q ^ (k + 1))))
      (Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * B) *
        ((N' B - 3 * N B) / B ^ (k + 1) - (k + 1) * N B / B ^ (k + 2)))) B := by
  have h1 : HasDerivAt (fun q : ℝ => -3 * q) (-3) B := by
    simpa using (hasDerivAt_id B).const_mul (-3 : ℝ)
  have h2 : HasDerivAt (fun q : ℝ => Real.exp (-3 * q)) (Real.exp (-3 * B) * -3) B :=
    (Real.hasDerivAt_exp _).comp B h1
  have h3 : HasDerivAt (fun q : ℝ => N q / q ^ (k + 1))
      ((N' B * B ^ (k + 1) - N B * (((k + 1 : ℕ) : ℝ) * B ^ (k + 1 - 1))) / (B ^ (k + 1)) ^ 2) B :=
    (hN B).div (hasDerivAt_pow (k + 1) B) (pow_ne_zero _ hB.ne')
  have h4 := (h2.mul h3).const_mul (Real.exp (-(9 / 2 : ℝ)))
  refine h4.congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- Polynomial numerators of the second-atom moment profiles. -/
noncomputable def secondAtomNumerator0 (B : ℝ) : ℝ := 18 + 16 * B
noncomputable def secondAtomNumerator1 (B : ℝ) : ℝ := 18 + 54 * B + 48 * B ^ 2
noncomputable def secondAtomNumerator2 (B : ℝ) : ℝ := 36 + 108 * B + 162 * B ^ 2 + 144 * B ^ 3
noncomputable def secondAtomNumerator3 (B : ℝ) : ℝ := 108 + 324 * B + 486 * B ^ 2 + 486 * B ^ 3 + 432 * B ^ 4
noncomputable def secondAtomNumerator4 (B : ℝ) : ℝ := 432 + 1296 * B + 1944 * B ^ 2 + 1944 * B ^ 3 + 1458 * B ^ 4 + 1296 * B ^ 5
noncomputable def secondAtomNumerator5 (B : ℝ) : ℝ := 2160 + 6480 * B + 9720 * B ^ 2 + 9720 * B ^ 3 + 7290 * B ^ 4 + 4374 * B ^ 5 + 3888 * B ^ 6
noncomputable def secondAtomNumerator6 (B : ℝ) : ℝ := 12960 + 38880 * B + 58320 * B ^ 2 + 58320 * B ^ 3 + 43740 * B ^ 4 + 26244 * B ^ 5 + 13122 * B ^ 6 + 11664 * B ^ 7
noncomputable def secondAtomNumerator7 (B : ℝ) : ℝ := 90720 + 272160 * B + 408240 * B ^ 2 + 408240 * B ^ 3 + 306180 * B ^ 4 + 183708 * B ^ 5 + 91854 * B ^ 6 + 39366 * B ^ 7 + 34992 * B ^ 8

/-- The second-atom moment profile `r_j(B) = N_j(B) / B^{j+1}`. -/
noncomputable def secondAtomProfile : ℕ → ℝ → ℝ
  | 0, B => secondAtomNumerator0 B / B ^ 1
  | 1, B => secondAtomNumerator1 B / B ^ 2
  | 2, B => secondAtomNumerator2 B / B ^ 3
  | 3, B => secondAtomNumerator3 B / B ^ 4
  | 4, B => secondAtomNumerator4 B / B ^ 5
  | 5, B => secondAtomNumerator5 B / B ^ 6
  | 6, B => secondAtomNumerator6 B / B ^ 7
  | 7, B => secondAtomNumerator7 B / B ^ 8
  | _, _ => 0


/-- The second-atom moment profile including its exponential prefactors. -/
def secondAtomMomentProfile (j : ℕ) (B : ℝ) : ℝ :=
  Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * B) * secondAtomProfile j B)

theorem thetaCuspLikelihoodGap_two : thetaCuspLikelihoodGap 2 = 3 := by
  unfold thetaCuspLikelihoodGap; norm_num

theorem thetaCuspSecondAtomMoment_zero {B : ℝ} (hB : 0 < B) :
    thetaCuspSecondAtomMoment B 0 = secondAtomMomentProfile 0 B := by
  unfold thetaCuspSecondAtomMoment thetaCuspSecondAtomSpectralMeasure
  simp only [pow_zero, one_mul]
  rw [integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure le_rfl hB]
  unfold thetaCuspAtomLikelihoodSpectralTerm secondAtomMomentProfile
  simp only [secondAtomProfile, secondAtomNumerator0, thetaCuspLikelihoodGap_two]
  have hne : B ≠ 0 := hB.ne'
  have e1 : Real.exp (-(3 / 2 : ℝ) * 3) = Real.exp (-(9 / 2 : ℝ)) := by norm_num
  rw [e1]
  push_cast
  field_simp
  ring

theorem hasDerivAt_secondAtomNumerator0 (B : ℝ) :
    HasDerivAt secondAtomNumerator0 (16) B := by
  have h := hasDerivAt_poly8 18 16 0 0 0 0 0 0 0 B
  unfold secondAtomNumerator0
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator1 (B : ℝ) :
    HasDerivAt secondAtomNumerator1 (54 + 96 * B) B := by
  have h := hasDerivAt_poly8 18 54 48 0 0 0 0 0 0 B
  unfold secondAtomNumerator1
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator2 (B : ℝ) :
    HasDerivAt secondAtomNumerator2 (108 + 324 * B + 432 * B ^ 2) B := by
  have h := hasDerivAt_poly8 36 108 162 144 0 0 0 0 0 B
  unfold secondAtomNumerator2
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator3 (B : ℝ) :
    HasDerivAt secondAtomNumerator3 (324 + 972 * B + 1458 * B ^ 2 + 1728 * B ^ 3) B := by
  have h := hasDerivAt_poly8 108 324 486 486 432 0 0 0 0 B
  unfold secondAtomNumerator3
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator4 (B : ℝ) :
    HasDerivAt secondAtomNumerator4 (1296 + 3888 * B + 5832 * B ^ 2 + 5832 * B ^ 3 + 6480 * B ^ 4) B := by
  have h := hasDerivAt_poly8 432 1296 1944 1944 1458 1296 0 0 0 B
  unfold secondAtomNumerator4
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator5 (B : ℝ) :
    HasDerivAt secondAtomNumerator5 (6480 + 19440 * B + 29160 * B ^ 2 + 29160 * B ^ 3 + 21870 * B ^ 4 + 23328 * B ^ 5) B := by
  have h := hasDerivAt_poly8 2160 6480 9720 9720 7290 4374 3888 0 0 B
  unfold secondAtomNumerator5
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator6 (B : ℝ) :
    HasDerivAt secondAtomNumerator6 (38880 + 116640 * B + 174960 * B ^ 2 + 174960 * B ^ 3 + 131220 * B ^ 4 + 78732 * B ^ 5 + 81648 * B ^ 6) B := by
  have h := hasDerivAt_poly8 12960 38880 58320 58320 43740 26244 13122 11664 0 B
  unfold secondAtomNumerator6
  convert h using 1 <;> first | (funext x; ring) | ring

theorem hasDerivAt_secondAtomNumerator7 (B : ℝ) :
    HasDerivAt secondAtomNumerator7 (272160 + 816480 * B + 1224720 * B ^ 2 + 1224720 * B ^ 3 + 918540 * B ^ 4 + 551124 * B ^ 5 + 275562 * B ^ 6 + 279936 * B ^ 7) B := by
  have h := hasDerivAt_poly8 90720 272160 408240 408240 306180 183708 91854 39366 34992 B
  unfold secondAtomNumerator7
  convert h using 1 <;> first | (funext x; ring) | ring

theorem profile_step_0 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 0)
      (-(secondAtomMomentProfile 1 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator0) 0 hB
  have hfun : secondAtomMomentProfile 0 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator0 q / q ^ 1)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator0, secondAtomNumerator1]
  field_simp
  ring

theorem profile_step_1 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 1)
      (-(secondAtomMomentProfile 2 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator1) 1 hB
  have hfun : secondAtomMomentProfile 1 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator1 q / q ^ 2)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator1, secondAtomNumerator2]
  field_simp
  ring

theorem profile_step_2 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 2)
      (-(secondAtomMomentProfile 3 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator2) 2 hB
  have hfun : secondAtomMomentProfile 2 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator2 q / q ^ 3)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator2, secondAtomNumerator3]
  field_simp
  ring

theorem profile_step_3 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 3)
      (-(secondAtomMomentProfile 4 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator3) 3 hB
  have hfun : secondAtomMomentProfile 3 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator3 q / q ^ 4)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator3, secondAtomNumerator4]
  field_simp
  ring

theorem profile_step_4 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 4)
      (-(secondAtomMomentProfile 5 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator4) 4 hB
  have hfun : secondAtomMomentProfile 4 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator4 q / q ^ 5)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator4, secondAtomNumerator5]
  field_simp
  ring

theorem profile_step_5 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 5)
      (-(secondAtomMomentProfile 6 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator5) 5 hB
  have hfun : secondAtomMomentProfile 5 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator5 q / q ^ 6)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator5, secondAtomNumerator6]
  field_simp
  ring

theorem profile_step_6 {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile 6)
      (-(secondAtomMomentProfile 7 B)) B := by
  have h := expProfile_hasDerivAt (hasDerivAt_secondAtomNumerator6) 6 hB
  have hfun : secondAtomMomentProfile 6 = fun q => Real.exp (-(9 / 2 : ℝ)) * (Real.exp (-3 * q) * (secondAtomNumerator6 q / q ^ 7)) := by
    funext q; simp only [secondAtomMomentProfile, secondAtomProfile]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [secondAtomMomentProfile, secondAtomProfile, secondAtomNumerator6, secondAtomNumerator7]
  field_simp
  ring

theorem hasDerivAt_secondAtomMomentProfile (j : ℕ) (hj : j ≤ 6) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (secondAtomMomentProfile j) (-(secondAtomMomentProfile (j + 1) B)) B := by
  interval_cases j
  · exact profile_step_0 hB
  · exact profile_step_1 hB
  · exact profile_step_2 hB
  · exact profile_step_3 hB
  · exact profile_step_4 hB
  · exact profile_step_5 hB
  · exact profile_step_6 hB

/-- **Closed forms of the second-atom moments** for `j ≤ 7`. -/
theorem thetaCuspSecondAtomMoment_eq_profile :
    ∀ j : ℕ, j ≤ 7 → ∀ B : ℝ, 0 < B →
      thetaCuspSecondAtomMoment B j = secondAtomMomentProfile j B := by
  intro j
  induction j with
  | zero => intro _ B hB; exact thetaCuspSecondAtomMoment_zero hB
  | succ j ih =>
    intro hj B hB
    have hF := ih (by omega)
    have h1 := hasDerivAt_thetaCuspSecondAtomMoment j hB
    have h2 : HasDerivAt (fun q => thetaCuspSecondAtomMoment q j)
        (-(secondAtomMomentProfile (j + 1) B)) B :=
      (hasDerivAt_secondAtomMomentProfile j (by omega) hB).congr_of_eventuallyEq (by
        filter_upwards [Ioi_mem_nhds hB] with q hq
        exact hF q hq)
    have := h1.unique h2
    linarith

/-! ## Deep-tail support comparison at edge `8` -/

theorem ae_eight_le_thetaCuspDeepTail_tilted_integrand :
    ∀ᵐ t ∂thetaCuspDeepTailSpectralMeasure, 8 ≤ t :=
  ae_eight_le_thetaCuspDeepTailSpectralMeasure

/-- **Sharp support comparison for the deep tail.**  A tilt gap `δ = B - B₀ ≥ m/8` transports the
`m`-th deep-tail moment with the factor `8^m e^{-8δ}`. -/
theorem thetaCuspDeepTailMoment_le_eight_pow_mul_exp_support_comparison (m : ℕ) {B₀ B : ℝ}
    (hB₀ : 0 < B₀) (hδ : (m : ℝ) / 8 ≤ B - B₀) :
    thetaCuspDeepTailMoment B m ≤
      8 ^ m * Real.exp (-(8 * (B - B₀))) * thetaCuspDeepTailMoment B₀ 0 := by
  have hm8 : (0 : ℝ) ≤ (m : ℝ) / 8 := by positivity
  have hB : 0 < B := by linarith
  unfold thetaCuspDeepTailMoment
  have hleft := integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure m hB
  have hright := (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure 0 hB₀).const_mul
    (8 ^ m * Real.exp (-(8 * (B - B₀))))
  rw [← integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
  simp only [pow_zero, one_mul]
  have key := pow_mul_exp_neg_le_of_le (m := m) (δ := B - B₀) (a := 8) (t := t)
    (by norm_num) hδ ht
  have hsplit : Real.exp (-B * t) = Real.exp (-((B - B₀) * t)) * Real.exp (-B₀ * t) := by
    rw [← Real.exp_add]
    ring_nf
  have hsplit' : Real.exp (-(8 * (B - B₀))) = Real.exp (-((B - B₀) * 8)) := by ring_nf
  rw [hsplit, hsplit', ← mul_assoc]
  exact mul_le_mul_of_nonneg_right key (Real.exp_pos _).le

theorem thetaCuspDeepTailMoment_zero_le_higher {B : ℝ} (hB : 0 < B) :
    thetaCuspDeepTailMoment B 0 ≤ thetaCuspHigherLikelihoodSpectralMoment B 0 := by
  rw [thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hB]
  linarith [thetaCuspSecondAtomMoment_nonneg B 0]

/-- **Regime-I deep-tail majorant.**  For `A(x) ≥ 6` and `m ≤ 7`:
`M⁽³⁾_m ≤ 8^m e^{-8(A(x) - π)} / 399`. -/
theorem thetaCuspDeepTailMoment_le_regimeOne {x : ℝ} (m : ℕ) (hm : m ≤ 7)
    (hA : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) m ≤
      8 ^ m * Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) / 399 := by
  have hx : 0 ≤ x := (regimeOne_pos_of_six_le hA).le
  have hB₀ : 0 < thetaCuspLikelihoodCoordinate 0 := thetaCuspLikelihoodCoordinate_pos le_rfl
  have hm' : (m : ℝ) ≤ 7 := by exact_mod_cast hm
  have hδ : (m : ℝ) / 8 ≤ thetaCuspLikelihoodCoordinate x - thetaCuspLikelihoodCoordinate 0 := by
    rw [thetaCuspLikelihoodCoordinate_sub_zero]
    have := Real.pi_lt_four
    linarith
  have hcmp := thetaCuspDeepTailMoment_le_eight_pow_mul_exp_support_comparison m hB₀ hδ
  rw [thetaCuspLikelihoodCoordinate_sub_zero] at hcmp
  have hcal := thetaCuspHigherLikelihoodSpectralMoment_zero_coordinate_zero_lt
  have h0 := thetaCuspDeepTailMoment_zero_le_higher hB₀
  have h8 : (0 : ℝ) ≤ 8 ^ m * Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) := by
    positivity
  calc thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) m
      ≤ 8 ^ m * Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) *
          thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate 0) 0 := hcmp
    _ ≤ 8 ^ m * Real.exp (-(8 * (thetaCuspSingleAtomReflectionScale 1 x - Real.pi))) * (1 / 399) :=
        mul_le_mul_of_nonneg_left (h0.trans hcal.le) h8
    _ = _ := by ring

end

end RHTower
