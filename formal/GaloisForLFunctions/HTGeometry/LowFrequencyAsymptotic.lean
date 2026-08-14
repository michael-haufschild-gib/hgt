import GaloisForLFunctions.HTGeometry.WatsonScaling
import GaloisForLFunctions.HTGeometry.OscillatoryIntegrationByParts

/-!
# The low-frequency half-log asymptotic

For a Lipschitz amplitude the half-power oscillatory integral has the exact leading term

`∫₀^A f(η) η^{-1/2} e^{iηL} dη = f(0) √π e^{iπ/4} L^{-1/2} + O(L^{-1})`.

The constant part of the amplitude produces the Watson term by scaling; the remaining part carries
a factor `η` that cancels the half-power singularity, so one integration by parts against the
oscillation gives it a full power of `L`.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {f f' : ℝ → ℂ} {K : ℝ}

/-- The centred amplitude carried by the half-power weight. -/
def centredAmplitude (f : ℝ → ℂ) (η : ℝ) : ℂ := (f η - f 0) * ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ)

theorem norm_centredAmplitude_le
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η) {η : ℝ} (hη : 0 < η) :
    ‖centredAmplitude f η‖ ≤ K * η ^ ((1:ℝ)/2) := by
  rw [centredAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hη _)]
  have hpow : η * η ^ (-(1:ℝ)/2) = η ^ ((1:ℝ)/2) := by
    have h1 : η = η ^ (1:ℝ) := (Real.rpow_one η).symm
    calc η * η ^ (-(1:ℝ)/2) = η ^ (1:ℝ) * η ^ (-(1:ℝ)/2) := by rw [← h1]
      _ = η ^ ((1:ℝ) + -(1:ℝ)/2) := (Real.rpow_add hη _ _).symm
      _ = η ^ ((1:ℝ)/2) := by ring_nf
  calc ‖f η - f 0‖ * η ^ (-(1:ℝ)/2)
      ≤ (K * η) * η ^ (-(1:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right (hlip η hη.le) (Real.rpow_pos_of_pos hη _).le
    _ = K * (η * η ^ (-(1:ℝ)/2)) := by ring
    _ = K * η ^ ((1:ℝ)/2) := by rw [hpow]

/-- The derivative of the centred amplitude. -/
def centredAmplitudeDeriv (f f' : ℝ → ℂ) (η : ℝ) : ℂ :=
  f' η * ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ)
    + (f η - f 0) * ((-(1:ℝ)/2 * η ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)

theorem hasDerivAt_centredAmplitude
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (centredAmplitude f) (centredAmplitudeDeriv f f' η) η := by
  have h1 : HasDerivAt (fun x : ℝ => f x - f 0) (f' η) η := (hderiv η hη).sub_const _
  have h2 : HasDerivAt (fun x : ℝ => ((x ^ (-(1:ℝ)/2) : ℝ) : ℂ))
      (((-(1:ℝ)/2 * η ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) η := hasDerivAt_ofReal_rpow hη
  have hmul := h1.mul h2
  have hfun : centredAmplitude f
      = fun x : ℝ => (f x - f 0) * ((x ^ (-(1:ℝ)/2) : ℝ) : ℂ) := rfl
  rw [hfun, centredAmplitudeDeriv]
  exact hmul

theorem norm_centredAmplitudeDeriv_le
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η)
    (hbound : ∀ η : ℝ, 0 < η → ‖f' η‖ ≤ K) {η : ℝ} (hη : 0 < η) :
    ‖centredAmplitudeDeriv f f' η‖ ≤ (3/2 : ℝ) * K * η ^ (-(1:ℝ)/2) := by
  have hpow0 : (0:ℝ) < η ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hη _
  have hpow1 : (0:ℝ) < η ^ (-(1:ℝ)/2 - 1) := Real.rpow_pos_of_pos hη _
  have hsplit : η * η ^ (-(1:ℝ)/2 - 1) = η ^ (-(1:ℝ)/2) := by
    have h1 : η = η ^ (1:ℝ) := (Real.rpow_one η).symm
    calc η * η ^ (-(1:ℝ)/2 - 1) = η ^ (1:ℝ) * η ^ (-(1:ℝ)/2 - 1) := by rw [← h1]
      _ = η ^ ((1:ℝ) + (-(1:ℝ)/2 - 1)) := (Real.rpow_add hη _ _).symm
      _ = η ^ (-(1:ℝ)/2) := by ring_nf
  have hterm₁ : ‖f' η * ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ)‖ ≤ K * η ^ (-(1:ℝ)/2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow0]
    exact mul_le_mul_of_nonneg_right (hbound η hη) hpow0.le
  have hterm₂ : ‖(f η - f 0) * ((-(1:ℝ)/2 * η ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)‖
      ≤ (1/2 : ℝ) * K * η ^ (-(1:ℝ)/2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |(-(1:ℝ)/2 * η ^ (-(1:ℝ)/2 - 1))| = (1/2 : ℝ) * η ^ (-(1:ℝ)/2 - 1) := by
      rw [abs_of_nonpos (by nlinarith [hpow1])]
      ring
    rw [habs]
    have hstep : ‖f η - f 0‖ * ((1/2 : ℝ) * η ^ (-(1:ℝ)/2 - 1))
        ≤ (K * η) * ((1/2 : ℝ) * η ^ (-(1:ℝ)/2 - 1)) := by
      apply mul_le_mul_of_nonneg_right (hlip η hη.le) (by positivity)
    calc ‖f η - f 0‖ * ((1/2 : ℝ) * η ^ (-(1:ℝ)/2 - 1))
        ≤ (K * η) * ((1/2 : ℝ) * η ^ (-(1:ℝ)/2 - 1)) := hstep
      _ = (1/2 : ℝ) * K * (η * η ^ (-(1:ℝ)/2 - 1)) := by ring
      _ = (1/2 : ℝ) * K * η ^ (-(1:ℝ)/2) := by rw [hsplit]
  have htri := norm_add_le (f' η * ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ))
    ((f η - f 0) * ((-(1:ℝ)/2 * η ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ))
  rw [centredAmplitudeDeriv]
  linarith [htri, hterm₁, hterm₂]

/-- The centred amplitude is interval integrable away from the origin. -/
theorem intervalIntegrable_centredAmplitudeDeriv
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hcont : ContinuousOn f' (Set.Ioi (0:ℝ))) {a A : ℝ} (ha : 0 < a) (hab : a ≤ A) :
    IntervalIntegrable (centredAmplitudeDeriv f f') volume a A := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hx0 : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hf : ContinuousAt f x := (hderiv x hx0).continuousAt
  have hf' : ContinuousWithinAt f' (Set.Ioi (0:ℝ)) x := hcont x hx0
  have hf'at : ContinuousAt f' x := by
    have hmem : Set.Ioi (0:ℝ) ∈ nhds x := (isOpen_Ioi).mem_nhds hx0
    exact (continuousWithinAt_iff_continuousAt hmem).mp hf'
  have hpow : ContinuousAt (fun y : ℝ => ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ)) x :=
    (Complex.continuous_ofReal.continuousAt).comp
      (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0)))
  have hpow' : ContinuousAt
      (fun y : ℝ => ((-(1:ℝ)/2 * y ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ)) x :=
    (Complex.continuous_ofReal.continuousAt).comp
      (continuousAt_const.mul (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0))))
  have : ContinuousAt (centredAmplitudeDeriv f f') x := by
    rw [show centredAmplitudeDeriv f f'
        = fun y : ℝ => f' y * ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ)
          + (f y - f 0) * ((-(1:ℝ)/2 * y ^ (-(1:ℝ)/2 - 1) : ℝ) : ℂ) from rfl]
    exact (hf'at.mul hpow).add ((hf.sub continuousAt_const).mul hpow')
  exact this.continuousWithinAt

/-- **The variable part of the amplitude is subcritical.** -/
theorem norm_integral_centredAmplitude_le {a A L : ℝ} (hL : 0 < L) (ha : 0 < a) (hab : a ≤ A)
    (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hcont : ContinuousOn f' (Set.Ioi (0:ℝ)))
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η)
    (hbound : ∀ η : ℝ, 0 < η → ‖f' η‖ ≤ K) :
    ‖∫ η in a..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
      ≤ (K * A ^ ((1:ℝ)/2) + K * a ^ ((1:ℝ)/2) + 3 * K * A ^ ((1:ℝ)/2)) / L := by
  have hA : 0 < A := lt_of_lt_of_le ha hab
  have hderiv' : ∀ x ∈ Set.uIcc a A,
      HasDerivAt (centredAmplitude f) (centredAmplitudeDeriv f f' x) x := by
    intro x hx
    have hx0 : 0 < x := by
      rw [Set.uIcc_of_le hab] at hx
      exact lt_of_lt_of_le ha hx.1
    exact hasDerivAt_centredAmplitude hderiv hx0
  have hint := intervalIntegrable_centredAmplitudeDeriv hderiv hcont ha hab
  have hparts := norm_integral_oscillatory_le (g := centredAmplitude f)
    (g' := centredAmplitudeDeriv f f') hL hab hderiv' hint
  have hmajor : IntervalIntegrable (fun η : ℝ => (3/2 : ℝ) * K * η ^ (-(1:ℝ)/2)) volume a A :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hderivbound : (∫ η in a..A, ‖centredAmplitudeDeriv f f' η‖)
      ≤ 3 * K * A ^ ((1:ℝ)/2) := by
    have hle : (∫ η in a..A, ‖centredAmplitudeDeriv f f' η‖)
        ≤ ∫ η in a..A, (3/2 : ℝ) * K * η ^ (-(1:ℝ)/2) := by
      refine intervalIntegral.integral_mono_on hab hint.norm hmajor ?_
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      exact norm_centredAmplitudeDeriv_le hlip hbound hx0
    have hvalue : (∫ η in a..A, (3/2 : ℝ) * K * η ^ (-(1:ℝ)/2))
        = 3 * K * (A ^ ((1:ℝ)/2) - a ^ ((1:ℝ)/2)) := by
      have hzero : (0:ℝ) ∉ Set.uIcc a A := by
        rw [Set.uIcc_of_le hab]
        intro hcon
        exact absurd hcon.1 (not_le.mpr ha)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
      have hexp : -(1:ℝ)/2 + 1 = (1:ℝ)/2 := by ring
      rw [hexp]
      field_simp
    rw [hvalue] at hle
    have hpos : (0:ℝ) ≤ a ^ ((1:ℝ)/2) := (Real.rpow_pos_of_pos ha _).le
    nlinarith [hle, hK, hpos]
  have hgA : ‖centredAmplitude f A‖ ≤ K * A ^ ((1:ℝ)/2) :=
    norm_centredAmplitude_le hlip hA
  have hga : ‖centredAmplitude f a‖ ≤ K * a ^ ((1:ℝ)/2) :=
    norm_centredAmplitude_le hlip ha
  refine le_trans hparts ?_
  apply div_le_div_of_nonneg_right ?_ hL.le
  linarith [hgA, hga, hderivbound]

/-- The full oscillatory integrand is interval integrable through the origin. -/
theorem intervalIntegrable_centredAmplitude_mul {A L : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η) :
    IntervalIntegrable
      (fun η => centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)) volume 0 A := by
  have hmajor : IntervalIntegrable (fun η : ℝ => K * η ^ ((1:ℝ)/2)) volume 0 A :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
  have hmeas : AEStronglyMeasurable
      (fun η => centredAmplitude f η * Complex.exp ((η * L : ℝ) * I))
      (volume.restrict (Set.uIoc 0 A)) := by
    have hcontOn : ContinuousOn
        (fun η => centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)) (Set.Ioo 0 A) := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hf : ContinuousAt f x := (hderiv x hx0).continuousAt
      have hpow : ContinuousAt (fun y : ℝ => ((y ^ (-(1:ℝ)/2) : ℝ) : ℂ)) x :=
        (Complex.continuous_ofReal.continuousAt).comp
          (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt hx0)))
      have hosc : ContinuousAt (fun y : ℝ => Complex.exp ((y * L : ℝ) * I)) x := by
        apply Continuous.continuousAt
        fun_prop
      have hprod : ContinuousAt
          (fun η => centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)) x := by
        rw [show (fun η : ℝ => centredAmplitude f η * Complex.exp ((η * L : ℝ) * I))
            = fun η : ℝ => ((f η - f 0) * ((η ^ (-(1:ℝ)/2) : ℝ) : ℂ))
              * Complex.exp ((η * L : ℝ) * I) from rfl]
        exact (((hf.sub continuousAt_const).mul hpow).mul hosc)
      exact hprod.continuousWithinAt
    have hIoo : (volume.restrict (Set.uIoc (0:ℝ) A))
        = volume.restrict (Set.Ioo 0 A) := by
      rw [Set.uIoc_of_le hA.le]
      exact Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
    rw [hIoo]
    exact hcontOn.aestronglyMeasurable measurableSet_Ioo
  refine IntervalIntegrable.mono_fun hmajor hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_uIoc : MeasurableSet (Set.uIoc (0:ℝ) A))] with η hη
  have hη0 : 0 < η := by
    rw [Set.uIoc_of_le hA.le] at hη
    exact hη.1
  have hval : ‖centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
      = ‖centredAmplitude f η‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  rw [hval, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ K * η ^ ((1:ℝ)/2))]
  exact norm_centredAmplitude_le hlip hη0

/-- **The low-frequency half-log asymptotic.**  Against a Lipschitz amplitude the half-power
oscillatory integral is the Watson term plus `O(L^{-1})`. -/
theorem norm_lowFrequency_asymptotic {A L : ℝ} (hA : 0 < A) (hL : 0 < L) (hK : 0 ≤ K)
    (hderiv : ∀ η : ℝ, 0 < η → HasDerivAt f (f' η) η)
    (hcont : ContinuousOn f' (Set.Ioi (0:ℝ)))
    (hlip : ∀ η : ℝ, 0 ≤ η → ‖f η - f 0‖ ≤ K * η)
    (hbound : ∀ η : ℝ, 0 < η → ‖f' η‖ ≤ K) :
    ‖(∫ η in (0:ℝ)..A, f η * scaledFresnel L η)
        - f 0 * (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
          * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))‖
      ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
        + (4 * K * A ^ ((1:ℝ)/2)) / L := by
  have hintScaled : IntervalIntegrable (scaledFresnel L) volume 0 A := by
    have hbase : IntervalIntegrable (fun u : ℝ => u ^ (-(1:ℝ)/2)) volume 0 A :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hmeas : AEStronglyMeasurable (scaledFresnel L) (volume.restrict (Set.uIoc 0 A)) := by
      apply Measurable.aestronglyMeasurable
      unfold scaledFresnel
      fun_prop
    refine IntervalIntegrable.mono_fun hbase hmeas ?_
    filter_upwards with η
    have hval : ‖scaledFresnel L η‖ = |η ^ (-(1:ℝ)/2)| := by
      rw [scaledFresnel, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      simp
    rw [hval, Real.norm_eq_abs]
  have hintCentred := intervalIntegrable_centredAmplitude_mul (L := L) hA hK hderiv hlip
  have hsplit : (∫ η in (0:ℝ)..A, f η * scaledFresnel L η)
      = f 0 * (∫ η in (0:ℝ)..A, scaledFresnel L η)
        + ∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hintScaled.const_mul (f 0)) hintCentred]
    refine intervalIntegral.integral_congr fun η hη => ?_
    show f η * scaledFresnel L η
      = f 0 * scaledFresnel L η + centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)
    rw [scaledFresnel, centredAmplitude]
    ring
  have hleading := norm_integral_scaledFresnel_sub_watson_le hL hA
  have htail : ‖∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
      ≤ (4 * K * A ^ ((1:ℝ)/2)) / L := by
    have hstep : ∀ a : ℝ, 0 < a → a ≤ A →
        ‖∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
          ≤ (K * A ^ ((1:ℝ)/2) + K * a ^ ((1:ℝ)/2) + 3 * K * A ^ ((1:ℝ)/2)) / L
            + (2/3 : ℝ) * K * a ^ ((3:ℝ)/2) := by
      intro a ha haA
      have hadd : (∫ η in (0:ℝ)..a, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I))
          + (∫ η in a..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I))
          = ∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I) :=
        intervalIntegral.integral_add_adjacent_intervals
          (hintCentred.mono_set (by
            rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le hA.le]
            exact Set.Icc_subset_Icc le_rfl haA))
          (hintCentred.mono_set (by
            rw [Set.uIcc_of_le haA, Set.uIcc_of_le hA.le]
            exact Set.Icc_subset_Icc ha.le le_rfl))
      have hhead : ‖∫ η in (0:ℝ)..a, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
          ≤ (2/3 : ℝ) * K * a ^ ((3:ℝ)/2) := by
        have hmajor : IntervalIntegrable (fun η : ℝ => K * η ^ ((1:ℝ)/2)) volume 0 a :=
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
        have hle : ‖∫ η in (0:ℝ)..a, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
            ≤ ∫ η in (0:ℝ)..a, K * η ^ ((1:ℝ)/2) := by
          refine intervalIntegral.norm_integral_le_of_norm_le ha.le ?_ hmajor
          filter_upwards with η hη
          have hη0 : 0 < η := hη.1
          have hval : ‖centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
              = ‖centredAmplitude f η‖ := by
            rw [norm_mul, Complex.norm_exp]
            simp
          rw [hval]
          exact norm_centredAmplitude_le hlip hη0
        have hvalue : (∫ η in (0:ℝ)..a, K * η ^ ((1:ℝ)/2)) = (2/3 : ℝ) * K * a ^ ((3:ℝ)/2) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
          have hexp : (1:ℝ)/2 + 1 = (3:ℝ)/2 := by ring
          rw [hexp, Real.zero_rpow (by norm_num)]
          ring
        rw [hvalue] at hle
        exact hle
      have hmid := norm_integral_centredAmplitude_le hL ha haA hK hderiv hcont hlip hbound
      have htri : ‖∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
          ≤ ‖∫ η in (0:ℝ)..a, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖
            + ‖∫ η in a..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I)‖ := by
        rw [← hadd]
        exact norm_add_le _ _
      linarith [htri, hhead, hmid]
    have hlim : Tendsto (fun a : ℝ =>
        (K * A ^ ((1:ℝ)/2) + K * a ^ ((1:ℝ)/2) + 3 * K * A ^ ((1:ℝ)/2)) / L
          + (2/3 : ℝ) * K * a ^ ((3:ℝ)/2)) (𝓝[>] (0:ℝ))
        (𝓝 ((4 * K * A ^ ((1:ℝ)/2)) / L)) := by
      have hhalf : Tendsto (fun a : ℝ => a ^ ((1:ℝ)/2)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
        have htend : Tendsto (fun a : ℝ => a ^ ((1:ℝ)/2)) (𝓝 (0:ℝ))
            (𝓝 ((0:ℝ) ^ ((1:ℝ)/2))) :=
          (Real.continuousAt_rpow_const (0:ℝ) ((1:ℝ)/2) (Or.inr (by norm_num)))
        rw [Real.zero_rpow (by norm_num)] at htend
        exact htend.mono_left nhdsWithin_le_nhds
      have hthree : Tendsto (fun a : ℝ => a ^ ((3:ℝ)/2)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
        have htend : Tendsto (fun a : ℝ => a ^ ((3:ℝ)/2)) (𝓝 (0:ℝ))
            (𝓝 ((0:ℝ) ^ ((3:ℝ)/2))) :=
          (Real.continuousAt_rpow_const (0:ℝ) ((3:ℝ)/2) (Or.inr (by norm_num)))
        rw [Real.zero_rpow (by norm_num)] at htend
        exact htend.mono_left nhdsWithin_le_nhds
      have h1 : Tendsto (fun a : ℝ =>
          (K * A ^ ((1:ℝ)/2) + K * a ^ ((1:ℝ)/2) + 3 * K * A ^ ((1:ℝ)/2)) / L)
          (𝓝[>] (0:ℝ)) (𝓝 ((K * A ^ ((1:ℝ)/2) + K * 0 + 3 * K * A ^ ((1:ℝ)/2)) / L)) := by
        exact (((tendsto_const_nhds.add (hhalf.const_mul K)).add tendsto_const_nhds)).div_const L
      have h2 : Tendsto (fun a : ℝ => (2/3 : ℝ) * K * a ^ ((3:ℝ)/2)) (𝓝[>] (0:ℝ))
          (𝓝 (0:ℝ)) := by
        have := hthree.const_mul ((2/3 : ℝ) * K)
        rw [mul_zero] at this
        exact this
      have hsum := h1.add h2
      rw [add_zero] at hsum
      have hval : (K * A ^ ((1:ℝ)/2) + K * 0 + 3 * K * A ^ ((1:ℝ)/2)) / L
          = (4 * K * A ^ ((1:ℝ)/2)) / L := by
        ring_nf
      rw [hval] at hsum
      exact hsum
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Filter.eventually_of_mem (Iio_mem_nhds hA)
          (fun a (ha : a ∈ Set.Iio A) => le_of_lt (Set.mem_Iio.mp ha)))] with a ha haA
    exact hstep a ha haA
  rw [hsplit]
  have hexpand : f 0 * (∫ η in (0:ℝ)..A, scaledFresnel L η)
        + (∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I))
      - f 0 * (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))
      = f 0 * ((∫ η in (0:ℝ)..A, scaledFresnel L η)
          - ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
            * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))
        + ∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I) := by
    ring
  rw [hexpand]
  have htri := norm_add_le (f 0 * ((∫ η in (0:ℝ)..A, scaledFresnel L η)
      - ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I))))
    (∫ η in (0:ℝ)..A, centredAmplitude f η * Complex.exp ((η * L : ℝ) * I))
  have hfirst : ‖f 0 * ((∫ η in (0:ℝ)..A, scaledFresnel L η)
      - ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
        * (((Real.pi : ℂ) ^ ((1:ℂ)/2)) * Complex.exp ((Real.pi/4 : ℝ) * I)))‖
      ≤ ‖f 0‖ * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ))) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hleading (norm_nonneg _)
  linarith [htri, hfirst, htail]

end

end GaloisForLFunctions.HTGeometry
