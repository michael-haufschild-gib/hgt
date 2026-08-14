import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelCompactMellinCoupledSystem
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma48Exterior

/-!
# Physical-to-log bridge for Suzuki's compact Mellin transforms

The logarithmic half-density unitary is identified with the literal physical Mellin integral,
including exact representatives and the exponential Jacobian.  This closes the coordinate seam
between the strong aperture differential system and Suzuki's meromorphic continuations.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- A symmetric-cutoff fixed logarithmic image of interval data has compact Fourier transform
equal to the literal physical Mellin pairing of that interval data. -/
theorem suzukiCompactL2Fourier_positiveLogUnitary_fixed_eq_intervalPairing
    {a : ℝ} (ha : 0 < a) (f : IntervalL2 0 a)
    (hfixed :
      suzukiCutoff (Real.log a)
          (suzukiPositiveLogUnitary
            (suzukiPhysicalIntervalPositiveIsometry a f)) =
        suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a f))
    (z : ℂ) :
    suzukiCompactL2Fourier (Real.log a)
        (suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a f)) z =
      ∫ x : ClosedInterval 0 a,
        suzukiMellinDensity z (x : ℝ) * f x ∂volume := by
  let u : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a f
  let q : SoninL2 := suzukiPositiveLogUnitary u
  let F : ℝ → ℂ := fun x =>
    suzukiMellinDensity z x * suzukiPhysicalIntervalZeroExtendFun f x
  have hcarrier : suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) = u := by
    change suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm
        (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm u))) = u
    rw [logEvenUnitary.symm_apply_apply,
      suzukiPositiveHalfLineUnitary.apply_symm_apply]
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae q
  rw [hcarrier] at hcoord
  have hcoordWhole := (ae_restrict_iff' measurableSet_Ioi).mp hcoord
  have hcoordExp := realExp_quasiMeasurePreserving.ae hcoordWhole
  have hinputWhole := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hinputExp := realExp_quasiMeasurePreserving.ae hinputWhole
  have hrep : (q : ℝ → ℂ) =ᵐ[volume] l2MeasurableRep q :=
    (l2MeasurableRep_ae q).symm
  have hlog :
      (∫ t : ℝ, (q : ℝ → ℂ) t *
        Complex.exp (I * z * (t : ℂ))) =
        ∫ t : ℝ, Real.exp t • F (Real.exp t) := by
    apply integral_congr_ae
    filter_upwards [hcoordExp, hinputExp, hrep] with t hcoord hinput hrep
    have hcoord' : u (Real.exp t) =
        (Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t := by
      simpa only [Real.log_exp] using hcoord (Real.exp_pos t)
    have hinput' : u (Real.exp t) =
        suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) := by
      exact hinput (Real.exp_pos t)
    have hweight : (Real.exp (t / 2) : ℂ) *
        (Real.exp (-t / 2) : ℂ) = 1 := by
      norm_cast
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    have hq : (q : ℝ → ℂ) t =
        (Real.exp (t / 2) : ℂ) *
          suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) := by
      rw [hrep]
      calc
        l2MeasurableRep q t =
            (Real.exp (t / 2) : ℂ) *
              ((Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t) := by
          rw [← mul_assoc, hweight, one_mul]
        _ = (Real.exp (t / 2) : ℂ) * u (Real.exp t) := by rw [hcoord']
        _ = _ := by rw [hinput']
    have hexp : (Real.exp (t / 2) : ℂ) *
        Complex.exp (I * z * (t : ℂ)) =
      (Real.exp t : ℂ) * suzukiMellinDensity z (Real.exp t) := by
      rw [suzukiMellinDensity, Real.log_exp, Complex.ofReal_exp,
        Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hq]
    dsimp only [F]
    rw [Complex.real_smul]
    calc
      (Real.exp (t / 2) : ℂ) *
            suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) *
            Complex.exp (I * z * (t : ℂ)) =
          ((Real.exp (t / 2) : ℂ) *
              Complex.exp (I * z * (t : ℂ))) *
            suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) := by ring
      _ = ((Real.exp t : ℂ) * suzukiMellinDensity z (Real.exp t)) *
            suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) := by
          rw [hexp]
      _ = _ := by ring
  have hphysical :
      (∫ x : ℝ in Ioi (0 : ℝ), F x) =
        ∫ x : ClosedInterval 0 a,
          suzukiMellinDensity z (x : ℝ) * f x ∂volume := by
    calc
      (∫ x : ℝ in Ioi (0 : ℝ), F x) =
          ∫ x : ℝ in Ioc 0 a, F x := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (fun _ hx => hx.1)
        intro x hx
        dsimp only [F]
        rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem, mul_zero]
        exact fun hIcc => hx.2 ⟨hx.1, hIcc.2⟩
      _ = ∫ x : ℝ in Icc 0 a, F x := integral_Icc_eq_integral_Ioc.symm
      _ = ∫ x : ClosedInterval 0 a,
          suzukiMellinDensity z (x : ℝ) * f x ∂volume := by
        rw [← integral_subtype measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [suzukiPhysicalIntervalRepresentative_ae f] with x hx
        dsimp only [F]
        rw [suzukiPhysicalIntervalZeroExtendFun_apply, hx]
  have hsubst := integral_Ioi_eq_integral_exp_smul_hankel F
  change suzukiCutoff (Real.log a) q = q at hfixed
  calc
    suzukiCompactL2Fourier (Real.log a) q z =
        ∫ t : ℝ, (q : ℝ → ℂ) t *
          Complex.exp (I * z * (t : ℂ)) := by
      rw [suzukiCompactL2Fourier]
      change (∫ t : ℝ,
          ((suzukiCutoff (Real.log a) q : SoninL2) : ℝ → ℂ) t *
            Complex.exp (I * z * (t : ℂ))) = _
      rw [hfixed]
    _ = ∫ t : ℝ, Real.exp t • F (Real.exp t) := hlog
    _ = ∫ x : ℝ in Ioi (0 : ℝ), F x := hsubst.symm
    _ = _ := hphysical

/-! ## Exact Suzuki Hankel specializations -/

/-- The physical Mellin pairing of the finite Fredholm sum is the sum of the two literal compact
Mellin transforms.  This statement closes the representative seam between the interval `L²`
solutions and their global continuous representatives. -/
theorem suzukiHankelPhiSum_intervalPairing_eq_compactMellin_sum
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (∫ x : ClosedInterval 0 a,
        suzukiMellinDensity z (x : ℝ) *
          suzukiHankelPhiSum omega a homega ha x ∂volume) =
      suzukiHankelCompactMellin SuzukiHankelSign.positive
          omega a homega ha z +
        suzukiHankelCompactMellin SuzukiHankelSign.negative
          omega a homega ha z := by
  let p : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha
  let m : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha
  let P : ℝ → ℂ :=
    suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha
  let M : ℝ → ℂ :=
    suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha
  let W : ℝ → ℂ := suzukiClampedMellinWeightValue (1 / a) z
  have hrep : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      suzukiHankelPhiSum omega a homega ha x = P (x : ℝ) + M (x : ℝ) := by
    filter_upwards [Lp.coeFn_add p m,
      suzukiHankelPhiContinuous_ae SuzukiHankelSign.positive homega ha,
      suzukiHankelPhiContinuous_ae SuzukiHankelSign.negative homega ha] with
        x hadd hp hm
    change (p + m) x = P (x : ℝ) + M (x : ℝ)
    rw [hadd]
    change p x + m x = P (x : ℝ) + M (x : ℝ)
    rw [← hp, ← hm]
    dsimp only [P, M]
    rw [suzukiHankelPhiGlobal_eq_continuousRepresentative
        SuzukiHankelSign.positive homega ha x,
      suzukiHankelPhiGlobal_eq_continuousRepresentative
        SuzukiHankelSign.negative homega ha x]
  have hweight : EqOn
      (fun x : ℝ => suzukiMellinDensity z x * (P x + M x))
      (fun x : ℝ => W x * (P x + M x)) (uIcc 0 a) := by
    intro x hx
    rw [uIcc_of_le (show 0 ≤ a by linarith)] at hx
    change suzukiMellinDensity z x * (P x + M x) =
      W x * (P x + M x)
    by_cases hxc : x ≤ 1 / a
    · have hp0 : P x = 0 :=
        suzukiHankelPhiGlobal_eq_zero_below_reciprocal
          SuzukiHankelSign.positive homega ha hx.1 hxc
      have hm0 : M x = 0 :=
        suzukiHankelPhiGlobal_eq_zero_below_reciprocal
          SuzukiHankelSign.negative homega ha hx.1 hxc
      rw [hp0, hm0, zero_add, mul_zero, mul_zero]
    · have hcx : 1 / a < x := lt_of_not_ge hxc
      change suzukiMellinDensity z x * (P x + M x) =
        suzukiClampedMellinWeightValue (1 / a) z x * (P x + M x)
      rw [suzukiMellinDensity, suzukiClampedMellinWeightValue,
        max_eq_right hcx.le]
  have hW : ContinuousOn W (uIcc 0 a) := by
    have hmax : Continuous (fun x : ℝ => max (1 / a) x) :=
      continuous_const.max continuous_id
    have hlog : Continuous (fun x : ℝ => Real.log (max (1 / a) x)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hcomp := ContinuousAt.comp
        (f := fun y : ℝ => max (1 / a) y)
        (g := Real.log)
        (Real.continuousAt_log
          (ne_of_gt (lt_of_lt_of_le (show 0 < 1 / a by positivity)
            (le_max_left (1 / a) x))))
        hmax.continuousAt
      change ContinuousAt (Real.log ∘ fun y : ℝ => max (1 / a) y) x
      exact hcomp
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hlog))).continuousOn
  have hP : ContinuousOn P (uIcc 0 a) := by
    rw [uIcc_of_le (show 0 ≤ a by linarith)]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative
      SuzukiHankelSign.positive homega ha).mono fun _ hx => hx.1
  have hM : ContinuousOn M (uIcc 0 a) := by
    rw [uIcc_of_le (show 0 ≤ a by linarith)]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative
      SuzukiHankelSign.negative homega ha).mono fun _ hx => hx.1
  have hWP : IntervalIntegrable (fun x => W x * P x) volume 0 a :=
    (hW.mul hP).intervalIntegrable
  have hWM : IntervalIntegrable (fun x => W x * M x) volume 0 a :=
    (hW.mul hM).intervalIntegrable
  calc
    (∫ x : ClosedInterval 0 a,
        suzukiMellinDensity z (x : ℝ) *
          suzukiHankelPhiSum omega a homega ha x ∂volume) =
        ∫ x : ClosedInterval 0 a,
          suzukiMellinDensity z (x : ℝ) * (P (x : ℝ) + M (x : ℝ))
            ∂volume := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx]
    _ = ∫ x in (0 : ℝ)..a, suzukiMellinDensity z x * (P x + M x) :=
      integral_subtype_closedInterval_eq_intervalIntegral
        (show 0 ≤ a by linarith)
        (fun x : ℝ => suzukiMellinDensity z x * (P x + M x))
    _ = ∫ x in (0 : ℝ)..a, W x * (P x + M x) :=
      intervalIntegral.integral_congr hweight
    _ = (∫ x in (0 : ℝ)..a, W x * P x) +
          ∫ x in (0 : ℝ)..a, W x * M x := by
      simp_rw [mul_add]
      exact intervalIntegral.integral_add hWP hWM
    _ = _ := rfl

/-- Exact coordinate bridge for Suzuki's compact Fredholm sum transform. -/
theorem suzukiCompactL2Fourier_hankelPhiSumLog_eq_compactMellin_sum
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) z =
      suzukiHankelCompactMellin SuzukiHankelSign.positive
          omega a homega ha z +
        suzukiHankelCompactMellin SuzukiHankelSign.negative
          omega a homega ha z := by
  calc
    suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) z =
        ∫ x : ClosedInterval 0 a,
          suzukiMellinDensity z (x : ℝ) *
            suzukiHankelPhiSum omega a homega ha x ∂volume := by
      simpa [suzukiHankelPhiSumLog, suzukiHankelPhiSumPositive] using
        (suzukiCompactL2Fourier_positiveLogUnitary_fixed_eq_intervalPairing
          (show 0 < a by linarith)
          (suzukiHankelPhiSum omega a homega ha)
          (suzukiHankelPhiSum_log_compact homega ha) z)
    _ = _ := suzukiHankelPhiSum_intervalPairing_eq_compactMellin_sum homega ha z

/-- The compact logarithmic Fredholm difference is a fixed point of the symmetric aperture
projection.  This follows from its exact identification as one application of that projection,
not from an informal support assertion. -/
theorem suzukiHankelPhiDifferenceCompactLog_compact
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiCutoff (Real.log a)
        (suzukiHankelPhiDifferenceCompactLog omega a homega ha) =
      suzukiHankelPhiDifferenceCompactLog omega a homega ha := by
  rw [suzukiHankelPhiDifferenceCompactLog_eq_cutoff_global homega ha]
  have hidem := indicatorCutoff_idempotent
    (Icc (-Real.log a) (Real.log a)) measurableSet_Icc
  rw [isIdempotentElem_iff] at hidem
  exact congrArg
    (fun T : SoninL2 →L[ℂ] SoninL2 =>
      T (suzukiHankelPhiDifferenceLog omega a homega ha)) hidem

/-- The physical Mellin pairing of the finite Fredholm difference is the difference of the two
literal compact Mellin transforms. -/
theorem suzukiHankelPhiDifference_intervalPairing_eq_compactMellin_difference
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    (∫ x : ClosedInterval 0 a,
        suzukiMellinDensity z (x : ℝ) *
          suzukiHankelPhiDifference omega a homega ha x ∂volume) =
      suzukiHankelCompactMellin SuzukiHankelSign.positive
          omega a homega ha z -
        suzukiHankelCompactMellin SuzukiHankelSign.negative
          omega a homega ha z := by
  let p : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha
  let m : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha
  let P : ℝ → ℂ :=
    suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha
  let M : ℝ → ℂ :=
    suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha
  let W : ℝ → ℂ := suzukiClampedMellinWeightValue (1 / a) z
  have hrep : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      suzukiHankelPhiDifference omega a homega ha x = P (x : ℝ) - M (x : ℝ) := by
    filter_upwards [Lp.coeFn_sub p m,
      suzukiHankelPhiContinuous_ae SuzukiHankelSign.positive homega ha,
      suzukiHankelPhiContinuous_ae SuzukiHankelSign.negative homega ha] with
        x hsub hp hm
    change (p - m) x = P (x : ℝ) - M (x : ℝ)
    rw [hsub]
    change p x - m x = P (x : ℝ) - M (x : ℝ)
    rw [← hp, ← hm]
    dsimp only [P, M]
    rw [suzukiHankelPhiGlobal_eq_continuousRepresentative
        SuzukiHankelSign.positive homega ha x,
      suzukiHankelPhiGlobal_eq_continuousRepresentative
        SuzukiHankelSign.negative homega ha x]
  have hweight : EqOn
      (fun x : ℝ => suzukiMellinDensity z x * (P x - M x))
      (fun x : ℝ => W x * (P x - M x)) (uIcc 0 a) := by
    intro x hx
    rw [uIcc_of_le (show 0 ≤ a by linarith)] at hx
    change suzukiMellinDensity z x * (P x - M x) =
      W x * (P x - M x)
    by_cases hxc : x ≤ 1 / a
    · have hp0 : P x = 0 :=
        suzukiHankelPhiGlobal_eq_zero_below_reciprocal
          SuzukiHankelSign.positive homega ha hx.1 hxc
      have hm0 : M x = 0 :=
        suzukiHankelPhiGlobal_eq_zero_below_reciprocal
          SuzukiHankelSign.negative homega ha hx.1 hxc
      rw [hp0, hm0, sub_self, mul_zero, mul_zero]
    · have hcx : 1 / a < x := lt_of_not_ge hxc
      change suzukiMellinDensity z x * (P x - M x) =
        suzukiClampedMellinWeightValue (1 / a) z x * (P x - M x)
      rw [suzukiMellinDensity, suzukiClampedMellinWeightValue,
        max_eq_right hcx.le]
  have hW : ContinuousOn W (uIcc 0 a) := by
    have hmax : Continuous (fun x : ℝ => max (1 / a) x) :=
      continuous_const.max continuous_id
    have hlog : Continuous (fun x : ℝ => Real.log (max (1 / a) x)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hcomp := ContinuousAt.comp
        (f := fun y : ℝ => max (1 / a) y)
        (g := Real.log)
        (Real.continuousAt_log
          (ne_of_gt (lt_of_lt_of_le (show 0 < 1 / a by positivity)
            (le_max_left (1 / a) x))))
        hmax.continuousAt
      change ContinuousAt (Real.log ∘ fun y : ℝ => max (1 / a) y) x
      exact hcomp
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hlog))).continuousOn
  have hP : ContinuousOn P (uIcc 0 a) := by
    rw [uIcc_of_le (show 0 ≤ a by linarith)]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative
      SuzukiHankelSign.positive homega ha).mono fun _ hx => hx.1
  have hM : ContinuousOn M (uIcc 0 a) := by
    rw [uIcc_of_le (show 0 ≤ a by linarith)]
    exact (continuousOn_suzukiHankelPhiGlobal_nonnegative
      SuzukiHankelSign.negative homega ha).mono fun _ hx => hx.1
  have hWP : IntervalIntegrable (fun x => W x * P x) volume 0 a :=
    (hW.mul hP).intervalIntegrable
  have hWM : IntervalIntegrable (fun x => W x * M x) volume 0 a :=
    (hW.mul hM).intervalIntegrable
  calc
    (∫ x : ClosedInterval 0 a,
        suzukiMellinDensity z (x : ℝ) *
          suzukiHankelPhiDifference omega a homega ha x ∂volume) =
        ∫ x : ClosedInterval 0 a,
          suzukiMellinDensity z (x : ℝ) * (P (x : ℝ) - M (x : ℝ))
            ∂volume := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx]
    _ = ∫ x in (0 : ℝ)..a, suzukiMellinDensity z x * (P x - M x) :=
      integral_subtype_closedInterval_eq_intervalIntegral
        (show 0 ≤ a by linarith)
        (fun x : ℝ => suzukiMellinDensity z x * (P x - M x))
    _ = ∫ x in (0 : ℝ)..a, W x * (P x - M x) :=
      intervalIntegral.integral_congr hweight
    _ = (∫ x in (0 : ℝ)..a, W x * P x) -
          ∫ x in (0 : ℝ)..a, W x * M x := by
      simp_rw [mul_sub]
      exact intervalIntegral.integral_sub hWP hWM
    _ = _ := rfl

/-- Exact coordinate bridge for the compact Fredholm difference. -/
theorem suzukiCompactL2Fourier_hankelPhiDifferenceCompactLog_eq_compactMellin_difference
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiDifferenceCompactLog omega a homega ha) z =
      suzukiHankelCompactMellin SuzukiHankelSign.positive
          omega a homega ha z -
        suzukiHankelCompactMellin SuzukiHankelSign.negative
          omega a homega ha z := by
  calc
    suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiDifferenceCompactLog omega a homega ha) z =
        ∫ x : ClosedInterval 0 a,
          suzukiMellinDensity z (x : ℝ) *
            suzukiHankelPhiDifference omega a homega ha x ∂volume := by
      simpa [suzukiHankelPhiDifferenceCompactLog] using
        (suzukiCompactL2Fourier_positiveLogUnitary_fixed_eq_intervalPairing
          (show 0 < a by linarith)
          (suzukiHankelPhiDifference omega a homega ha)
          (suzukiHankelPhiDifferenceCompactLog_compact homega ha) z)
    _ = _ :=
      suzukiHankelPhiDifference_intervalPairing_eq_compactMellin_difference
        homega ha z

/-- Exact coordinate bridge for Suzuki's compact transform of the global Hankel image. -/
theorem suzukiCompactL2Fourier_hankelPhiSumHankelLog_eq_compactMellin_difference
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumHankelLog omega a homega ha) z =
      suzukiHankelCompactMellin SuzukiHankelSign.negative
          omega a homega ha z -
        suzukiHankelCompactMellin SuzukiHankelSign.positive
          omega a homega ha z := by
  have hupper := suzukiHankelPhiDifferenceCompact_upperTransform
    homega ha (-z)
  have hcompact := suzukiUpperFourierLaplace_eq_compactL2Fourier_neg_of_fixed
    (suzukiHankelPhiDifferenceCompactLog_upper homega ha)
    (suzukiHankelPhiDifferenceCompactLog_compact homega ha) (-z)
  have hphysical :=
    suzukiCompactL2Fourier_hankelPhiDifferenceCompactLog_eq_compactMellin_difference
      homega ha z
  rw [neg_neg] at hcompact
  rw [hcompact] at hupper
  rw [hphysical] at hupper
  simp only [neg_neg] at hupper
  linear_combination hupper

end RHTower
