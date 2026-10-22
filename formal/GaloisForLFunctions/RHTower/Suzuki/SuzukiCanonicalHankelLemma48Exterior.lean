import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma48
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelGlobalKernel

/-!
# Suzuki (2012), Lemma 4.8: identification of the original exterior star integral

Lemma 4.8 is not complete until the meromorphic formula is identified with the second literal
integral in equation (4.20).  This module closes that seam.  The proof uses the global physical
kernel theorem, equation (4.24), Proposition 1's absolutely convergent Mellin transform, and the
exact logarithmic Hankel transform identity (4.01).
-/

open Complex Real MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace


/-! ## The arithmetic term in equation (4.24) -/

/-- Half-density logarithmic lift of the dilated arithmetic source `x ↦ h_ω(a x)`. -/
def suzukiHankelScaledSourceLog (omega a : ℝ) (t : ℝ) : ℂ :=
  (Real.exp (t / 2) : ℂ) *
    suzukiSourceHFinite omega (a * Real.exp t)

/-- Exact Mellin transform of the dilated source on Suzuki's high half-plane. -/
theorem integral_exp_mul_suzukiHankelScaledSourceLog
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 1 / 2 + omega < z.im) :
    (∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) *
        suzukiHankelScaledSourceLog omega a t) =
      (a : ℂ) ^ (-(1 / 2 + z * I)) * suzukiCanonicalTheta omega z := by
  let s : ℂ := 1 / 2 + z * I
  have hM := suzuki2012_proposition_one (show 0 < omega by linarith) hz
  have hscale : MellinConvergent
      (fun x : ℝ => suzukiSourceHFinite omega (a * x)) s :=
    (MellinConvergent.comp_mul_left (f := suzukiSourceHFinite omega)
      (s := s) (show 0 < a by linarith)).2 hM.1
  calc
    (∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) *
        suzukiHankelScaledSourceLog omega a t) =
        mellin (fun x : ℝ => suzukiSourceHFinite omega (a * x)) s := by
      rw [mellin_eq_integral_exp_mul_log]
      apply integral_congr_ae
      filter_upwards with t
      rw [suzukiHankelScaledSourceLog, Complex.ofReal_exp, ← mul_assoc,
        ← Complex.exp_add]
      congr 2
      dsimp only [s]
      push_cast
      ring
    _ = (a : ℂ) ^ (-s) *
          mellin (suzukiSourceHFinite omega) s := by
      simpa only [smul_eq_mul] using
        mellin_comp_mul_left (suzukiSourceHFinite omega) s
          (show 0 < a by linarith)
    _ = (a : ℂ) ^ (-(1 / 2 + z * I)) *
          suzukiCanonicalTheta omega z := by
      rw [hM.2]

/-- Absolute convergence of the full scaled arithmetic transform on Suzuki's high half-plane. -/
theorem integrable_exp_mul_suzukiHankelScaledSourceLog
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 1 / 2 + omega < z.im) :
    Integrable (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) *
      suzukiHankelScaledSourceLog omega a t) := by
  let s : ℂ := 1 / 2 + z * I
  have hM := suzuki2012_proposition_one (show 0 < omega by linarith) hz
  have hscale : MellinConvergent
      (fun x : ℝ => suzukiSourceHFinite omega (a * x)) s :=
    (MellinConvergent.comp_mul_left (f := suzukiSourceHFinite omega)
      (s := s) (show 0 < a by linarith)).2 hM.1
  rw [MellinConvergent] at hscale
  have hlog := (suzuki_integrableOn_Ioi_iff_integrable_exp_smul
    (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      suzukiSourceHFinite omega (a * x))).mp hscale
  apply hlog.congr
  filter_upwards with t
  simp only [smul_eq_mul]
  rw [suzukiHankelScaledSourceLog, Complex.ofReal_exp]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_nonneg])]
  rw [Complex.real_smul, Complex.ofReal_exp]
  rw [show Complex.exp (t : ℂ) *
      (Complex.exp ((t : ℂ) * (s - 1)) *
        suzukiSourceHFinite omega (a * Real.exp t)) =
      (Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * (s - 1))) *
        suzukiSourceHFinite omega (a * Real.exp t) by ring,
    ← Complex.exp_add]
  rw [Complex.ofReal_exp]
  rw [show Complex.exp (I * z * (t : ℂ)) *
      (Complex.exp ((t / 2 : ℝ) : ℂ) *
        suzukiSourceHFinite omega (a * Real.exp t)) =
      (Complex.exp (I * z * (t : ℂ)) *
        Complex.exp ((t / 2 : ℝ) : ℂ)) *
          suzukiSourceHFinite omega (a * Real.exp t) by ring,
    ← Complex.exp_add]
  congr 2
  dsimp only [s]
  push_cast
  ring

/-- The `sqrt(a)` coefficient in equation (4.20) exactly cancels the half-density part of
Mellin dilation. -/
theorem sqrt_mul_cpow_neg_half_add_eq_suzukiHankelAiz_neg
    {a : ℝ} (ha : 1 < a) (z : ℂ) :
    ((Real.sqrt a : ℝ) : ℂ) * (a : ℂ) ^ (-(1 / 2 + z * I)) =
      suzukiHankelAiz a (-z) := by
  have ha0 : 0 < a := by linarith
  have hsqrt : Real.exp (Real.log a / 2) = Real.sqrt a := by
    rw [← Real.log_sqrt ha0.le,
      Real.exp_log (Real.sqrt_pos.mpr ha0)]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha0.ne')]
  rw [← Complex.ofReal_log ha0.le]
  rw [show ((Real.sqrt a : ℝ) : ℂ) =
      Complex.exp (((Real.log a / 2 : ℝ) : ℂ)) by
    rw [← Complex.ofReal_exp, hsqrt]]
  rw [← Complex.exp_add]
  unfold suzukiHankelAiz
  congr 1
  push_cast
  ring

/-- High-line transform of `2 h_ω(a·)` with Suzuki's equation (4.20) coefficient. -/
theorem coefficient_mul_two_scaledSourceTransform
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 1 / 2 + omega < z.im) :
    suzukiHankelTildeCoefficient a *
        (2 * ∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) *
          suzukiHankelScaledSourceLog omega a t) =
      suzukiCanonicalTheta omega z * suzukiHankelAiz a (-z) := by
  rw [integral_exp_mul_suzukiHankelScaledSourceLog homega ha hz]
  rw [suzukiHankelTildeCoefficient]
  have hsqrt := sqrt_mul_cpow_neg_half_add_eq_suzukiHankelAiz_neg ha z
  calc
    ((Real.sqrt a / 2 : ℝ) : ℂ) *
        (2 * ((a : ℂ) ^ (-(1 / 2 + z * I)) *
          suzukiCanonicalTheta omega z)) =
        (((Real.sqrt a : ℝ) : ℂ) *
          (a : ℂ) ^ (-(1 / 2 + z * I))) *
            suzukiCanonicalTheta omega z := by push_cast; ring
    _ = suzukiCanonicalTheta omega z * suzukiHankelAiz a (-z) := by
      rw [hsqrt]
      ring

/-! ## Exact logarithmic form of equation (4.24) -/

/-- Logarithmic half-density of the compactly projected Fredholm difference. -/
def suzukiHankelPhiDifferenceCompactLog
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  suzukiPositiveLogUnitary
    (suzukiPhysicalIntervalPositiveIsometry a
      (suzukiHankelPhiDifference omega a homega ha))

/-- Global canonical Hankel image of the compact Fredholm difference. -/
def suzukiHankelPhiDifferenceCompactHankelLog
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  suzukiCanonicalLogHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt (by linarith))
    (suzukiHankelPhiDifferenceCompactLog omega a homega ha)

/-- Pointwise logarithmic half-density of the global Fredholm sum. -/
def suzukiHankelPhiGlobalSumLogPointwise
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (t : ℝ) : ℂ :=
  (Real.exp (t / 2) : ℂ) *
    (suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha (Real.exp t) +
      suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha (Real.exp t))

/-- The compact difference has sharp logarithmic upper support at `log a`. -/
theorem suzukiHankelPhiDifferenceCompactLog_upper
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    logHalflineCutoff (Real.log a)
        (suzukiHankelPhiDifferenceCompactLog omega a homega ha) =
      suzukiHankelPhiDifferenceCompactLog omega a homega ha := by
  exact logHalflineCutoff_suzukiPhysicalIntervalPositive
    (show 0 < a by linarith) (suzukiHankelPhiDifference omega a homega ha)

/-- The compact Fredholm difference is exactly the shell projection of its global equation
(4.22) representative. -/
theorem suzukiHankelPhiDifferenceCompactLog_eq_cutoff_global
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelPhiDifferenceCompactLog omega a homega ha =
      suzukiCutoff (Real.log a)
        (suzukiHankelPhiDifferenceLog omega a homega ha) := by
  let q := suzukiHankelPhiSumLog omega a homega ha
  let p := suzukiHankelPhiSumHankelLog omega a homega ha
  let u := suzukiHankelPhiDifferencePositive omega a homega ha
  have hqUpper : logHalflineCutoff (Real.log a) q = q := by
    exact logHalflineCutoff_suzukiPhysicalIntervalPositive (by linarith)
      (suzukiHankelPhiSum omega a homega ha)
  have hpLower : logLowerHalflineCutoff (-Real.log a) p = p := by
    exact suzukiCanonicalLogHankelUnitary_maps_upper_to_reflected_lower
      (show 1 / 2 < omega by linarith) q hqUpper
  have hdLower : logLowerHalflineCutoff (-Real.log a)
      (suzukiHankelPhiDifferenceLog omega a homega ha) =
        suzukiHankelPhiDifferenceLog omega a homega ha := by
    change logLowerHalflineCutoff (-Real.log a) (-p) = -p
    rw [map_neg, hpLower]
  have hlogu : suzukiPositiveLogUnitary u =
      suzukiHankelPhiDifferenceLog omega a homega ha :=
    suzukiHankelPhiDifferenceLog_eq_positive homega ha
  have huLower : logLowerHalflineCutoff (-Real.log a)
      (suzukiPositiveLogUnitary u) = suzukiPositiveLogUnitary u := by
    rw [hlogu]
    exact hdLower
  have hproject := suzukiPositiveLogUnitary_extension_restriction_eq_cutoff
    ha u huLower
  have hrestrict := suzuki2012_equation_four_two_two_restriction homega ha
  rw [suzukiHankelPhiDifferenceCompactLog]
  calc
    suzukiPositiveLogUnitary
        (suzukiPhysicalIntervalPositiveIsometry a
          (suzukiHankelPhiDifference omega a homega ha)) =
        suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a
            (suzukiPositiveIntervalRestriction a u)) := by rw [hrestrict]
    _ = suzukiCutoff (Real.log a) (suzukiPositiveLogUnitary u) := hproject
    _ = _ := by rw [hlogu]

/-- The compact difference transform in equation (4.24) is the negative compact transform of the
global Hankel image of the Fredholm sum. -/
theorem suzukiHankelPhiDifferenceCompact_upperTransform
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiUpperFourierLaplace (Real.log a)
        (suzukiHankelPhiDifferenceCompactLog omega a homega ha) z =
      -suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumHankelLog omega a homega ha) (-z) := by
  let A := Real.log a
  let p := suzukiHankelPhiSumHankelLog omega a homega ha
  have hA : 0 ≤ A := (Real.log_pos ha).le
  have hEq : suzukiHankelPhiDifferenceCompactLog omega a homega ha =
      -suzukiCutoff A p := by
    rw [suzukiHankelPhiDifferenceCompactLog_eq_cutoff_global homega ha]
    change suzukiCutoff A (-p) = -suzukiCutoff A p
    exact map_neg
      (indicatorCutoff (Icc (-A) A) measurableSet_Icc) p
  rw [hEq]
  rw [suzukiUpperFourierLaplace]
  unfold suzukiUpperFourierLaplaceIntegrand
  rw [suzukiCompactL2Fourier]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [indicatorCutoff_ae (Icc (-A) A) measurableSet_Icc p,
    Lp.coeFn_neg (suzukiCutoff A p)] with t hcut hneg
  change (Iic A).indicator
      (fun t => Complex.exp (-I * z * (t : ℂ)) * (-suzukiCutoff A p) t) t = _
  rw [show suzukiCutoff A p t =
      (Icc (-A) A).indicator (fun s => p s) t by
        simpa only [Function.comp_apply] using hcut]
  by_cases ht : t ∈ Icc (-A) A
  · rw [indicator_of_mem
        (show t ∈ Iic A from ht.2), hneg, Pi.neg_apply, hcut,
      indicator_of_mem ht]
    have hexp : (-I) * z * (t : ℂ) = I * (-z) * (t : ℂ) := by ring
    rw [hexp]
    ring
  · rw [indicator_of_notMem ht]
    by_cases htA : t ∈ Iic A
    · rw [indicator_of_mem htA, hneg, Pi.neg_apply, hcut,
        indicator_of_notMem ht]
      simp
    · rw [indicator_of_notMem htA]
      simp

/-- Equation (4.01) for the compact Fredholm difference. -/
theorem suzukiHankelPhiDifferenceCompact_transform
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 0 < z.im) :
    suzukiLowerFourierLaplace (-Real.log a)
        (suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha) z =
      suzukiCanonicalTheta omega z *
        suzukiUpperFourierLaplace (Real.log a)
          (suzukiHankelPhiDifferenceCompactLog omega a homega ha) z := by
  exact suzuki2012_equation_four_zero_one (show 1 / 2 < omega by linarith)
    (suzukiHankelPhiDifferenceCompactLog omega a homega ha)
    (suzukiHankelPhiDifferenceCompactLog_upper homega ha) hz

/-- **Equation (4.24), exact logarithmic a.e. form.** -/
theorem suzuki2012_equation_four_two_four_log_ae
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    (suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha : ℝ → ℂ)
      =ᵐ[volume] fun t =>
        2 * suzukiHankelScaledSourceLog omega a t -
          suzukiHankelPhiGlobalSumLogPointwise omega a homega ha t := by
  have hkernel := suzukiCanonicalLogHankel_intervalSource_ae
    (show 1 / 2 < omega by linarith) ha
    (suzukiHankelPhiDifference omega a homega ha)
  have hkernel' :
      (suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha : ℝ → ℂ)
        =ᵐ[volume] fun t => (Real.exp (t / 2) : ℂ) *
          ∫ y : ClosedInterval 0 a,
            suzukiSourceHFinite omega (Real.exp t * (y : ℝ)) *
              suzukiHankelPhiDifference omega a homega ha y ∂volume := by
    simpa [suzukiHankelPhiDifferenceCompactHankelLog,
      suzukiHankelPhiDifferenceCompactLog] using hkernel
  filter_upwards [hkernel'] with t ht
  rw [ht]
  have h424 := suzuki2012_equation_four_two_four homega ha (Real.exp_pos t)
  have h424' :
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (Real.exp t * (y : ℝ)) *
          suzukiHankelPhiDifference omega a homega ha y ∂volume) =
        2 * suzukiSourceHFinite omega (a * Real.exp t) -
          suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha
            (Real.exp t) -
          suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha
            (Real.exp t) := by
    simpa [suzukiHankelPhiDifference] using h424
  rw [h424']
  rw [suzukiHankelScaledSourceLog, suzukiHankelPhiGlobalSumLogPointwise]
  ring

/-- On the compact aperture, the `L²` logarithmic Fredholm sum has the literal global continuous
representative used in equation (4.20). -/
theorem suzukiHankelPhiSumLog_ae_eq_global_on_aperture
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    (suzukiHankelPhiSumLog omega a homega ha : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ).restrict
        (Icc (-Real.log a) (Real.log a))]
        suzukiHankelPhiGlobalSumLogPointwise omega a homega ha := by
  let p : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha
  let m : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha
  let s : IntervalL2 0 a := p + m
  let u : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a s
  let q : SoninL2 := suzukiPositiveLogUnitary u
  have hq : q = suzukiHankelPhiSumLog omega a homega ha := by
    rfl
  have hclass : suzukiPositiveIntervalRestriction a u = s := by
    exact suzukiPositiveIntervalRestriction_extension a s
  have hres := suzukiPositiveIntervalRestriction_value_ae (a := a) u
  have hadd := Lp.coeFn_add p m
  have hp := suzukiHankelPhiContinuous_ae
    SuzukiHankelSign.positive homega ha
  have hm := suzukiHankelPhiContinuous_ae
    SuzukiHankelSign.negative homega ha
  have hsub : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      u (x : ℝ) =
        suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha (x : ℝ) +
          suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha (x : ℝ) := by
    filter_upwards [hres, hadd, hp, hm] with x hres hadd hp hm
    have hclassPoint := congrFun (congrArg
      (fun v : IntervalL2 0 a => (v : ClosedInterval 0 a → ℂ)) hclass) x
    rw [hres] at hclassPoint
    calc
      u (x : ℝ) = s x := hclassPoint
      _ = p x + m x := hadd
      _ = suzukiHankelPhiContinuous SuzukiHankelSign.positive
            omega a homega ha x +
          suzukiHankelPhiContinuous SuzukiHankelSign.negative
            omega a homega ha x := by rw [hp, hm]
      _ = _ := by
        rw [← suzukiHankelPhiGlobal_eq_continuousRepresentative
          SuzukiHankelSign.positive homega ha x,
          ← suzukiHankelPhiGlobal_eq_continuousRepresentative
          SuzukiHankelSign.negative homega ha x]
  have hreal : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 a),
      u x =
        suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha x +
          suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha x :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hsub
  have hrealWhole := (ae_restrict_iff' measurableSet_Icc).mp hreal
  have hrealExp := realExp_quasiMeasurePreserving.ae hrealWhole
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
  have hrep : (q : ℝ → ℂ) =ᵐ[volume] l2MeasurableRep q :=
    (l2MeasurableRep_ae q).symm
  have hall : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Icc (-Real.log a) (Real.log a) →
        q t = suzukiHankelPhiGlobalSumLogPointwise omega a homega ha t := by
    filter_upwards [hrealExp, hcoordExp, hrep] with t hreal hcoord hrep
    intro ht
    have hexpIcc : Real.exp t ∈ Icc (0 : ℝ) a := by
      constructor
      · exact (Real.exp_pos t).le
      · rw [← Real.exp_log (show 0 < a by linarith)]
        exact Real.exp_le_exp.mpr ht.2
    have hreal' := hreal hexpIcc
    have hcoord' : u (Real.exp t) =
        (Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t := by
      simpa only [Real.log_exp] using hcoord (Real.exp_pos t)
    have hweight : (Real.exp (t / 2) : ℂ) *
        (Real.exp (-t / 2) : ℂ) = 1 := by
      norm_cast
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [hrep, suzukiHankelPhiGlobalSumLogPointwise]
    calc
      l2MeasurableRep q t =
          (Real.exp (t / 2) : ℂ) *
            ((Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t) := by
        rw [← mul_assoc, hweight, one_mul]
      _ = (Real.exp (t / 2) : ℂ) * u (Real.exp t) := by rw [hcoord']
      _ = _ := by rw [hreal']
  rw [← hq]
  exact (ae_restrict_iff' measurableSet_Icc).2 hall

/-- The second literal exterior integral in Suzuki's equation (4.20), in exact logarithmic
half-density coordinates. -/
def suzukiHankelTildeEStar
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiHankelTildeCoefficient a *
    ∫ t : ℝ, (Ici (Real.log a)).indicator
      (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) *
        suzukiHankelPhiGlobalSumLogPointwise omega a homega ha t) t

/-- The original exterior-star integral equals the three exact transforms exposed by equation
(4.24): arithmetic source, global Hankel image of the compact difference, and compact Fredholm
sum.  This is the analytic heart of Suzuki's proof of Lemma 4.8. -/
theorem suzukiHankelTildeEStar_eq_transform_decomposition
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 1 / 2 + omega < z.im) :
    suzukiHankelTildeEStar omega a homega ha z =
      suzukiHankelTildeCoefficient a *
        (2 * (∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) *
            suzukiHankelScaledSourceLog omega a t) -
          suzukiLowerFourierLaplace (-Real.log a)
            (suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha) z -
          suzukiCompactL2Fourier (Real.log a)
            (suzukiHankelPhiSumLog omega a homega ha) z) := by
  let A := Real.log a
  let S : ℝ → ℂ := suzukiHankelScaledSourceLog omega a
  let H : SoninL2 := suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha
  let Q : SoninL2 := suzukiHankelPhiSumLog omega a homega ha
  let G : ℝ → ℂ := suzukiHankelPhiGlobalSumLogPointwise omega a homega ha
  let fS : ℝ → ℂ := fun t => Complex.exp (I * z * (t : ℂ)) * S t
  let fH : ℝ → ℂ := fun t => (Ici (-A)).indicator
    (fun t => Complex.exp (I * z * (t : ℂ)) * H t) t
  let fQ : ℝ → ℂ := fun t =>
    (suzukiCutoff A Q) t * Complex.exp (I * z * (t : ℂ))
  let fG : ℝ → ℂ := fun t => (Ici A).indicator
    (fun t => Complex.exp (I * z * (t : ℂ)) * G t) t
  have hA : 0 ≤ A := (Real.log_pos ha).le
  have hz0 : 0 < z.im := by linarith
  have h424 : (H : ℝ → ℂ) =ᵐ[volume] fun t => 2 * S t - G t := by
    simpa only [H, S, G] using
      suzuki2012_equation_four_two_four_log_ae homega ha
  have hQap := suzukiHankelPhiSumLog_ae_eq_global_on_aperture homega ha
  have hQwhole : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (-A) A → Q t = G t := by
    simpa only [A, Q, G] using (ae_restrict_iff' measurableSet_Icc).mp hQap
  have hcut := indicatorCutoff_ae (Icc (-A) A) measurableSet_Icc Q
  have hend : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({-A, A} : Set ℝ) :=
    compl_mem_ae_iff.mpr
      ((Set.toFinite ({-A, A} : Set ℝ)).countable.measure_zero volume)
  have hpoint : fG =ᵐ[volume] fun t => 2 * fS t - fH t - fQ t := by
    filter_upwards [h424, hQwhole, hcut, hend] with t h424 hQ hcut hend
    have htneNeg : t ≠ -A := by
      intro ht
      exact hend (by simp [ht])
    have htnePos : t ≠ A := by
      intro ht
      exact hend (by simp [ht])
    dsimp only [fG, fS, fH, fQ]
    rw [show suzukiCutoff A Q t =
        (Icc (-A) A).indicator (fun s => Q s) t by
      simpa only [Function.comp_apply] using hcut]
    by_cases htLower : -A < t
    · by_cases htUpper : t < A
      · have hminusMem : t ∈ Ici (-A) := htLower.le
        have hplusNot : t ∉ Ici A := not_le_of_gt htUpper
        have hshellMem : t ∈ Icc (-A) A := ⟨htLower.le, htUpper.le⟩
        simp only [fG, fS, fH, fQ, indicator_of_notMem hplusNot,
          indicator_of_mem hminusMem, indicator_of_mem hshellMem, zero_mul]
        rw [h424, hQ hshellMem]
        ring
      · have htA : A < t :=
          lt_of_le_of_ne (le_of_not_gt htUpper) (Ne.symm htnePos)
        have hminusMem : t ∈ Ici (-A) :=
          le_trans (by linarith) htA.le
        have hplusMem : t ∈ Ici A := htA.le
        have hshellNot : t ∉ Icc (-A) A := fun h => (not_le_of_gt htA) h.2
        simp only [fG, fS, fH, fQ, indicator_of_mem hplusMem,
          indicator_of_mem hminusMem, indicator_of_notMem hshellNot, zero_mul]
        rw [h424]
        ring
    · have htNegA : t < -A :=
        lt_of_le_of_ne (le_of_not_gt htLower) htneNeg
      have hminusNot : t ∉ Ici (-A) := not_le_of_gt htNegA
      have hplusNot : t ∉ Ici A := by
        intro ht
        exact (not_le_of_gt htNegA) (le_trans (by linarith [hA]) ht)
      have hshellNot : t ∉ Icc (-A) A := fun h => (not_le_of_gt htNegA) h.1
      have hsourceArg : a * Real.exp t ≤ 1 := by
        calc
          a * Real.exp t = Real.exp (Real.log a + t) := by
            rw [Real.exp_add, Real.exp_log (show 0 < a by linarith)]
          _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
          _ = 1 := Real.exp_zero
      have hSzero : S t = 0 := by
        change suzukiHankelScaledSourceLog omega a t = 0
        rw [suzukiHankelScaledSourceLog, suzukiSourceHFinite,
          if_neg (not_lt_of_ge hsourceArg), mul_zero]
      simp only [fG, fS, fH, fQ, indicator_of_notMem hplusNot,
        indicator_of_notMem hminusNot, indicator_of_notMem hshellNot,
        hSzero, mul_zero]
      ring
  have hfS : Integrable fS := by
    simpa only [fS, S] using
      integrable_exp_mul_suzukiHankelScaledSourceLog homega ha hz
  have hfH : Integrable fH := by
    simpa only [fH, H] using
      integrable_suzukiLowerFourierLaplace_integrand (-A)
        (suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha) hz0
  have hfQ : Integrable fQ := by
    simpa only [fQ] using
      integrable_suzukiCompactL2Fourier_integrand hA Q z
  have hrhs : Integrable (fun t => 2 * fS t - fH t - fQ t) :=
    ((hfS.const_mul 2).sub hfH).sub hfQ
  have hfG : Integrable fG := hrhs.congr hpoint.symm
  have hintegral : (∫ t : ℝ, fG t) =
      2 * (∫ t : ℝ, fS t) - (∫ t : ℝ, fH t) - (∫ t : ℝ, fQ t) := by
    rw [integral_congr_ae hpoint]
    calc
      (∫ t : ℝ, 2 * fS t - fH t - fQ t) =
          (∫ t : ℝ, 2 * fS t - fH t) - (∫ t : ℝ, fQ t) :=
        integral_sub ((hfS.const_mul 2).sub hfH) hfQ
      _ = (2 * (∫ t : ℝ, fS t) - (∫ t : ℝ, fH t)) -
          (∫ t : ℝ, fQ t) := by
        rw [integral_sub (hfS.const_mul 2) hfH, integral_const_mul]
  unfold suzukiHankelTildeEStar
  rw [show (∫ t : ℝ, (Ici (Real.log a)).indicator
      (fun t => Complex.exp (I * z * (t : ℂ)) * G t) t) =
      ∫ t : ℝ, fG t by rfl]
  rw [hintegral]
  rw [suzukiLowerFourierLaplace_eq_integral, suzukiCompactL2Fourier]

/-- The second literal equation (4.20) integral agrees with its meromorphic continuation on the
half-plane where Suzuki originally defines it. -/
theorem suzukiHankelTildeEStar_eq_continuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 1 / 2 + omega < z.im) :
    suzukiHankelTildeEStar omega a homega ha z =
      suzukiHankelTildeEStarContinuation omega a homega ha z := by
  let sourceTransform : ℂ :=
    ∫ t : ℝ, Complex.exp (I * z * (t : ℂ)) *
      suzukiHankelScaledSourceLog omega a t
  let Htransform : ℂ :=
    suzukiLowerFourierLaplace (-Real.log a)
      (suzukiHankelPhiDifferenceCompactHankelLog omega a homega ha) z
  let dTransform : ℂ :=
    suzukiUpperFourierLaplace (Real.log a)
      (suzukiHankelPhiDifferenceCompactLog omega a homega ha) z
  let pTransform : ℂ :=
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha) (-z)
  let qTransform : ℂ :=
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumLog omega a homega ha) z
  have hdecomp := suzukiHankelTildeEStar_eq_transform_decomposition homega ha hz
  have hsource := coefficient_mul_two_scaledSourceTransform homega ha hz
  have h401 := suzukiHankelPhiDifferenceCompact_transform homega ha
    (show 0 < z.im by linarith)
  have hd := suzukiHankelPhiDifferenceCompact_upperTransform homega ha z
  change suzukiHankelTildeEStar omega a homega ha z = _
  rw [hdecomp]
  change suzukiHankelTildeCoefficient a *
      (2 * sourceTransform - Htransform - qTransform) = _
  have hsource' : suzukiHankelTildeCoefficient a * (2 * sourceTransform) =
      suzukiCanonicalTheta omega z * suzukiHankelAiz a (-z) := by
    simpa only [sourceTransform] using hsource
  have h401' : Htransform = suzukiCanonicalTheta omega z * dTransform := by
    simpa only [Htransform, dTransform] using h401
  have hd' : dTransform = -pTransform := by
    simpa only [dTransform, pTransform] using hd
  rw [h401', hd']
  unfold suzukiHankelTildeEStarContinuation
  change suzukiHankelTildeCoefficient a *
      (2 * sourceTransform -
        suzukiCanonicalTheta omega z * -pTransform - qTransform) =
    -suzukiHankelTildeCoefficient a * qTransform +
      suzukiCanonicalTheta omega z *
        (suzukiHankelAiz a (-z) +
          suzukiHankelTildeCoefficient a * pTransform)
  calc
    _ = suzukiHankelTildeCoefficient a * (2 * sourceTransform) +
        suzukiHankelTildeCoefficient a *
          (suzukiCanonicalTheta omega z * pTransform) -
        suzukiHankelTildeCoefficient a * qTransform := by ring
    _ = _ := by rw [hsource']; ring

/-- The original pair of equation (4.20) integrals satisfies Suzuki's functional equation on its
literal high-half-plane domain. -/
theorem suzukiHankelTildeEStar_eq_theta_mul_tildeE_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 1 / 2 + omega < z.im)
    (hzreg : suzukiCanonicalE omega z ≠ 0)
    (hnegreg : suzukiCanonicalE omega (-z) ≠ 0) :
    suzukiHankelTildeEStar omega a homega ha z =
      suzukiCanonicalTheta omega z *
        suzukiHankelTildeEContinuation omega a homega ha (-z) := by
  rw [suzukiHankelTildeEStar_eq_continuation homega ha hz]
  exact suzukiHankelTildeEStarContinuation_eq_theta_mul_neg
    homega ha z hzreg hnegreg

/-- **Suzuki (2012), Lemma 4.8, full closed theorem.**  Both literal functions from equation
(4.20) are identified with their meromorphic continuations on their defining half-plane; the
continuations are analytic in the upper half-plane, obey the functional equation on the quotient
regular locus, and possess explicit entire pole-cleared numerators. -/
theorem suzuki2012_lemma_four_eight :
    ∀ (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a),
      (∀ z : ℂ, 1 / 2 + omega < z.im →
        suzukiHankelTildeE omega a homega ha z =
          suzukiHankelTildeEContinuation omega a homega ha z) ∧
      (∀ z : ℂ, 1 / 2 + omega < z.im →
        suzukiHankelTildeEStar omega a homega ha z =
          suzukiHankelTildeEStarContinuation omega a homega ha z) ∧
      MeromorphicOn (suzukiHankelTildeEContinuation omega a homega ha) Set.univ ∧
      MeromorphicOn (suzukiHankelTildeEStarContinuation omega a homega ha) Set.univ ∧
      AnalyticOnNhd ℂ (suzukiHankelTildeEContinuation omega a homega ha)
        suzukiUpperHalfPlane ∧
      AnalyticOnNhd ℂ (suzukiHankelTildeEStarContinuation omega a homega ha)
        suzukiUpperHalfPlane ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiCanonicalE omega (-z) ≠ 0 →
        suzukiHankelTildeEStarContinuation omega a homega ha z =
          suzukiCanonicalTheta omega z *
            suzukiHankelTildeEContinuation omega a homega ha (-z)) ∧
      Differentiable ℂ (suzukiHankelTildeECleared omega a homega ha) ∧
      Differentiable ℂ (suzukiHankelTildeEStarCleared omega a homega ha) ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiHankelTildeECleared omega a homega ha z =
          suzukiCanonicalE omega z *
            suzukiHankelTildeEContinuation omega a homega ha z) ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiHankelTildeEStarCleared omega a homega ha z =
          suzukiCanonicalE omega z *
            suzukiHankelTildeEStarContinuation omega a homega ha z) := by
  intro omega a homega ha
  exact ⟨fun z hz => suzukiHankelTildeE_eq_continuation homega ha (by linarith),
    fun z hz => suzukiHankelTildeEStar_eq_continuation homega ha hz,
    meromorphicOn_suzukiHankelTildeEContinuation homega ha,
    meromorphicOn_suzukiHankelTildeEStarContinuation homega ha,
    analyticOnNhd_suzukiHankelTildeEContinuation homega ha,
    analyticOnNhd_suzukiHankelTildeEStarContinuation homega ha,
    fun z hz hneg =>
      suzukiHankelTildeEStarContinuation_eq_theta_mul_neg homega ha z hz hneg,
    differentiable_suzukiHankelTildeECleared homega ha,
    differentiable_suzukiHankelTildeEStarCleared homega ha,
    fun z hz => suzukiHankelTildeECleared_eq_E_mul homega ha z hz,
    fun z hz => suzukiHankelTildeEStarCleared_eq_E_mul homega ha z hz⟩

end RHTower
