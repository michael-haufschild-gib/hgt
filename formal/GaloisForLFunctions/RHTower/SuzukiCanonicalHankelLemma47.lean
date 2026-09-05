import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma46
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma401Continuation
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma43
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Suzuki (2012), Lemma 4.7

This module proves the exact continuation seam used in Suzuki's construction of the canonical
system.  The two signed Fredholm equations imply the global identity

`phi_a^+ - phi_a^- = -H_omega P_a (phi_a^+ + phi_a^-)`.

After passage to logarithmic half-density coordinates, the source is supported in
`[-log a, log a]`.  Splitting the Hankel output at `log a` and applying equation (4.01) gives
Suzuki's equation (4.22.1): the exterior Mellin integral is a meromorphic-inner multiplier times
one entire compact `L²` Fourier transform plus a second entire compact `L²` Fourier transform.

No continuation, support, or boundary-value statement is assumed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform

noncomputable section


namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-! ## The signed Fredholm sum and difference -/

def suzukiHankelPhiSum
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : IntervalL2 0 a :=
  suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha +
    suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha

def suzukiHankelPhiDifference
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : IntervalL2 0 a :=
  suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha -
    suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha

/-- Exact finite-interval algebra behind Suzuki's equation (4.22). -/
theorem suzukiHankelPhiSum_compressed_eq_neg_difference
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiCompressedHankelOperator omega a (by linarith)
        (suzukiHankelPhiSum omega a homega ha) =
      -suzukiHankelPhiDifference omega a homega ha := by
  let T := suzukiCompressedHankelOperator omega a (by linarith : 1 / 2 < omega)
  let p := suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha
  let m := suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha
  have hp0 := suzukiHankelPhi_resolvent_equation
    SuzukiHankelSign.positive (show 1 / 2 < omega by linarith) ha
  have hm0 := suzukiHankelPhi_resolvent_equation
    SuzukiHankelSign.negative (show 1 / 2 < omega by linarith) ha
  have hp : p + T p = suzukiHankelBoundarySource omega a (by linarith) ha := by
    simpa [p, T, suzukiHankelResolventOperator] using hp0
  have hm : m - T m = suzukiHankelBoundarySource omega a (by linarith) ha := by
    simpa [m, T, suzukiHankelResolventOperator, sub_eq_add_neg] using hm0
  change T (p + m) = -(p - m)
  rw [map_add]
  rw [eq_neg_iff_add_eq_zero]
  calc
    T p + T m + (p - m) = (p + T p) - (m - T m) := by module
    _ = 0 := by rw [hp, hm, sub_self]

/-- The compact physical source `P_a (phi_a^+ + phi_a^-)`. -/
def suzukiHankelPhiSumPositive
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SuzukiPositiveL2 :=
  suzukiPhysicalIntervalPositiveIsometry a
    (suzukiHankelPhiSum omega a homega ha)

/-- The global physical difference, defined by the right side of Suzuki's equation (4.22). -/
def suzukiHankelPhiDifferencePositive
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SuzukiPositiveL2 :=
  -(suzukiCanonicalPositiveHankelUnitary omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt (by linarith))
      (suzukiHankelPhiSumPositive omega a homega ha))

/-- Equation (4.22) restricts to the literal finite Fredholm difference. -/
theorem suzuki2012_equation_four_two_two_restriction
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiPositiveIntervalRestriction a
        (suzukiHankelPhiDifferencePositive omega a homega ha) =
      suzukiHankelPhiDifference omega a homega ha := by
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt
      (show 1 / 2 < omega by linarith))
  let E := suzukiPhysicalIntervalPositiveIsometry a
  let R := suzukiPositiveIntervalRestriction a
  let T := suzukiCompressedHankelOperator omega a (by linarith : 1 / 2 < omega)
  let s := suzukiHankelPhiSum omega a homega ha
  let d := suzukiHankelPhiDifference omega a homega ha
  have hT : T s = -d :=
    suzukiHankelPhiSum_compressed_eq_neg_difference homega ha
  have hcompression :=
    suzukiCanonicalPositiveHankelCompression_eq_compressedHankel
      (show 1 / 2 < omega by linarith) (show 0 < a by linarith)
  have hRH : R (H (E s)) = T s := by
    exact DFunLike.congr_fun hcompression s
  change R (-(H (E s))) = d
  rw [map_neg, hRH, hT, neg_neg]

/-- **Suzuki (2012), equation (4.22), exact global `L²` form.**  On every finite window containing
the aperture, the canonical global Hankel image is the difference of the two extended Fredholm
solutions.  Quantifying over all `b` is the literal half-line statement, not only its compression
to `(0,a)`. -/
theorem suzuki2012_equation_four_two_two
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ∀ {b : ℝ} (hab : a ≤ b),
      suzukiPositiveIntervalRestriction b
          (suzukiHankelPhiDifferencePositive omega a homega ha) =
        suzukiHankelPhiExtended SuzukiHankelSign.positive omega a b
            (by linarith) ha hab -
          suzukiHankelPhiExtended SuzukiHankelSign.negative omega a b
            (by linarith) ha hab := by
  intro b hab
  let homegaHalf : 1 / 2 < omega := by linarith
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homegaHalf)
  let s := suzukiHankelPhiSum omega a homega ha
  let inc := suzukiPhysicalIntervalInclusion a b
  let T := suzukiCompressedHankelOperator omega b homegaHalf
  have hsource : suzukiPhysicalIntervalPositiveIsometry a s =
      suzukiPhysicalIntervalPositiveIsometry b (inc s) := by
    exact (suzukiPhysicalIntervalInclusion_positiveExtension
      (show 0 < a by linarith) hab s).symm
  have hcompression :=
    suzukiCanonicalPositiveHankelCompression_eq_compressedHankel
      homegaHalf (show 0 < b by linarith)
  have hrestrict : suzukiPositiveIntervalRestriction b
      (H (suzukiPhysicalIntervalPositiveIsometry a s)) = T (inc s) := by
    rw [hsource]
    exact DFunLike.congr_fun hcompression (inc s)
  change suzukiPositiveIntervalRestriction b
      (-(H (suzukiPhysicalIntervalPositiveIsometry a s))) = _
  rw [map_neg, hrestrict]
  simp only [suzukiHankelPhiExtended, SuzukiHankelSign.coeff_positive,
    SuzukiHankelSign.coeff_negative, one_smul, neg_smul, sub_neg_eq_add]
  change -T (inc s) =
    (suzukiHankelExtendedBoundary omega a b homegaHalf ha hab -
        T (inc (suzukiHankelPhi SuzukiHankelSign.positive omega a homegaHalf ha))) -
      (suzukiHankelExtendedBoundary omega a b homegaHalf ha hab +
        T (inc (suzukiHankelPhi SuzukiHankelSign.negative omega a homegaHalf ha)))
  have hinc : inc s =
      inc (suzukiHankelPhi SuzukiHankelSign.positive omega a homegaHalf ha) +
        inc (suzukiHankelPhi SuzukiHankelSign.negative omega a homegaHalf ha) := by
    dsimp only [inc, s, suzukiHankelPhiSum]
    rw [map_add]
  rw [hinc, map_add]
  module

/-- Pointwise-a.e. physical form of equation (4.22) on every compact half-line window. -/
theorem suzuki2012_equation_four_two_two_ae_global
    {omega a b : ℝ} (homega : 1 < omega) (ha : 1 < a) (hab : a ≤ b) :
    ∀ᵐ x : ClosedInterval 0 b ∂volume,
      suzukiHankelPhiDifferencePositive omega a homega ha (x : ℝ) =
        suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha (x : ℝ) -
          suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha (x : ℝ) := by
  have h422 := suzuki2012_equation_four_two_two homega ha hab
  have hres := suzukiPositiveIntervalRestriction_value_ae
    (a := b) (suzukiHankelPhiDifferencePositive omega a homega ha)
  have hplusL2 := suzukiHankelPhiGlobalContinuous_restrictionL2
    SuzukiHankelSign.positive homega ha hab
  have hminusL2 := suzukiHankelPhiGlobalContinuous_restrictionL2
    SuzukiHankelSign.negative homega ha hab
  have hplusRep := suzukiGlobalContinuousRestrictionL2_ae b
    (suzukiHankelPhiGlobalContinuous SuzukiHankelSign.positive omega a homega ha)
  have hminusRep := suzukiGlobalContinuousRestrictionL2_ae b
    (suzukiHankelPhiGlobalContinuous SuzukiHankelSign.negative omega a homega ha)
  have hsub := Lp.coeFn_sub
    (suzukiHankelPhiExtended SuzukiHankelSign.positive omega a b
      (by linarith) ha hab)
    (suzukiHankelPhiExtended SuzukiHankelSign.negative omega a b
      (by linarith) ha hab)
  filter_upwards [hres, hplusRep, hminusRep, hsub] with x hres hplus hminus hsub
  have h422x := congrFun (congrArg
    (fun f : IntervalL2 0 b => (f : ClosedInterval 0 b → ℂ)) h422) x
  rw [hres] at h422x
  rw [hsub, Pi.sub_apply] at h422x
  rw [← hplusL2, ← hminusL2] at h422x
  rw [hplus, hminus] at h422x
  exact h422x

/-! ## Exact lower support of the compact source in logarithmic coordinates -/

/-- If an interval vector vanishes below `c`, its logarithmic zero extension is supported above
`log c`.  This is the lower-support counterpart of
`logHalflineCutoff_suzukiPhysicalIntervalPositive`. -/
theorem logLowerHalflineCutoff_suzukiPhysicalIntervalPositive_of_ae_zero_below
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hca : c ≤ a)
    (f : IntervalL2 0 a)
    (hzero : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (x : ℝ) ≤ c → f x = 0) :
    logLowerHalflineCutoff (Real.log c)
        (suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a f)) =
      suzukiPositiveLogUnitary
        (suzukiPhysicalIntervalPositiveIsometry a f) := by
  let u : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a f
  let q : SoninL2 := suzukiPositiveLogUnitary u
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
  have hzeroRepSub : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (x : ℝ) ≤ c → suzukiPhysicalIntervalRepresentative f x = 0 := by
    filter_upwards [hzero, suzukiPhysicalIntervalRepresentative_ae f] with x hx hrep
    intro hxc
    rw [hrep, hx hxc]
  have hzeroReal : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 a),
      x ≤ c → suzukiPhysicalIntervalZeroExtendFun f x = 0 := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [hzeroRepSub] with x hx
    intro hxc
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hx hxc]
  have hzeroWhole := (ae_restrict_iff' measurableSet_Icc).mp hzeroReal
  have hzeroExp := realExp_quasiMeasurePreserving.ae hzeroWhole
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Ici (Real.log c)) measurableSet_Ici q,
    l2MeasurableRep_ae q, hcoordExp, hinputExp, hzeroExp] with
      t hcut hrep hcoord hinput hzeroAt
  change logLowerHalflineCutoff (Real.log c) q t = q t
  rw [show logLowerHalflineCutoff (Real.log c) q t =
      (Ici (Real.log c)).indicator (fun s => q s) t by
        simpa [logLowerHalflineCutoff] using hcut]
  by_cases ht : Real.log c ≤ t
  · rw [indicator_of_mem (show t ∈ Ici (Real.log c) from ht)]
  · rw [indicator_of_notMem (show t ∉ Ici (Real.log c) from ht)]
    have hexp : Real.exp t < c := by
      rw [← Real.exp_log hc]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge ht)
    have hexpIcc : Real.exp t ∈ Icc (0 : ℝ) a :=
      ⟨(Real.exp_pos t).le, le_trans hexp.le hca⟩
    have huZero : u (Real.exp t) = 0 := by
      change suzukiPhysicalIntervalPositiveL2 f (Real.exp t) = 0
      rw [hinput (Real.exp_pos t)]
      exact hzeroAt hexpIcc hexp.le
    have hcoord' : u (Real.exp t) =
        (Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t := by
      simpa only [Real.log_exp] using hcoord (Real.exp_pos t)
    have hweight : (Real.exp (-t / 2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_ne_zero (-t / 2))
    have hrepZero : l2MeasurableRep q t = 0 := by
      exact (mul_eq_zero.mp (by rw [← hcoord', huZero])).resolve_left hweight
    rw [← hrep, hrepZero]

/-- The logarithmic Fredholm source is exactly compactly supported in
`[-log a, log a]`. -/
theorem suzukiHankelPhiSum_log_compact
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiCutoff (Real.log a)
        (suzukiPositiveLogUnitary
          (suzukiHankelPhiSumPositive omega a homega ha)) =
      suzukiPositiveLogUnitary
        (suzukiHankelPhiSumPositive omega a homega ha) := by
  let s := suzukiHankelPhiSum omega a homega ha
  let q := suzukiPositiveLogUnitary
    (suzukiPhysicalIntervalPositiveIsometry a s)
  have hupper : logHalflineCutoff (Real.log a) q = q :=
    logHalflineCutoff_suzukiPhysicalIntervalPositive (by linarith) s
  have hplus := suzukiHankelPhi_ae_zero_below_reciprocal
    SuzukiHankelSign.positive (show 1 / 2 < omega by linarith) ha
  have hminus := suzukiHankelPhi_ae_zero_below_reciprocal
    SuzukiHankelSign.negative (show 1 / 2 < omega by linarith) ha
  have hsumZero : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      (x : ℝ) ≤ 1 / a → s x = 0 := by
    filter_upwards [hplus, hminus, Lp.coeFn_add
      (suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha)
      (suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha)] with
      x hp hm hadd
    intro hx
    change (suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha +
      suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha) x = 0
    rw [hadd, Pi.add_apply, hp hx, hm hx, zero_add]
  have hlower0 :=
    logLowerHalflineCutoff_suzukiPhysicalIntervalPositive_of_ae_zero_below
      (show 0 < a by linarith) (show 0 < 1 / a by positivity)
      (show 1 / a ≤ a by
        rw [div_le_iff₀ (show 0 < a by linarith)]
        nlinarith) s hsumZero
  have hlogInv : Real.log (1 / a) = -Real.log a := by
    rw [one_div, Real.log_inv]
  rw [hlogInv] at hlower0
  exact suzukiCutoff_eq_self_of_logHalfline_fixed hupper hlower0

/-! ## Exterior transform and equation (4.22.1) -/

def suzukiHankelPhiSumLog
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  suzukiPositiveLogUnitary (suzukiHankelPhiSumPositive omega a homega ha)

def suzukiHankelPhiSumHankelLog
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  suzukiCanonicalLogHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt (by linarith))
    (suzukiHankelPhiSumLog omega a homega ha)

def suzukiHankelPhiDifferenceLog
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  -suzukiHankelPhiSumHankelLog omega a homega ha

/-- The logarithmic global difference is the logarithmic image of the physical equation (4.22). -/
theorem suzukiHankelPhiDifferenceLog_eq_positive
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    suzukiPositiveLogUnitary
        (suzukiHankelPhiDifferencePositive omega a homega ha) =
      suzukiHankelPhiDifferenceLog omega a homega ha := by
  rw [suzukiHankelPhiDifferencePositive, map_neg,
    suzukiPositiveLogUnitary_canonicalHankel]
  rfl

/-- Suzuki's exterior Mellin integral (4.21), in exact logarithmic half-density coordinates. -/
def suzukiHankelPsi
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiLowerFourierLaplace (Real.log a)
    (suzukiHankelPhiDifferenceLog omega a homega ha) z

/-- The right side of Suzuki's meromorphic continuation formula (4.22.1). -/
def suzukiHankelPsiContinuation
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  -suzukiCanonicalTheta omega z *
      suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) (-z) +
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha) z

/-- Absolute convergence of a lower-supported Fourier--Laplace integral in the strict upper
half-plane. -/
theorem integrable_suzukiLowerFourierLaplace_integrand
    (B : ℝ) (q : SoninL2) {z : ℂ} (hz : 0 < z.im) :
    Integrable fun t : ℝ => (Ici B).indicator
      (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * q t) t := by
  let w : ℝ → ℂ := suzukiLowerFourierLaplaceJetWeight B 0 z.im
  have hw := suzukiLowerFourierLaplaceJetWeight_memLp B 0 hz
  have hprod : Integrable (fun t : ℝ => w t * q t) :=
    MemLp.integrable_mul hw (Lp.memLp q)
  apply hprod.mono
  · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      (Lp.memLp q).1).indicator measurableSet_Ici
  · filter_upwards with t
    by_cases ht : t ∈ Ici B
    · have hre : (I * z * (t : ℂ)).re = -z.im * t := by
        simp [Complex.mul_re]
      dsimp only [w]
      rw [indicator_of_mem ht, suzukiLowerFourierLaplaceJetWeight,
        indicator_of_mem ht, norm_mul, norm_mul, Complex.norm_exp, hre]
      simp only [abs_pow, pow_zero, one_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact le_rfl
    · simp [w, suzukiLowerFourierLaplaceJetWeight, ht]

/-- Splitting a lower-supported transform at the opposite endpoint isolates the compact middle
shell. -/
theorem suzukiLowerFourierLaplace_split_compact
    {A : ℝ} (hA : 0 ≤ A) (p : SoninL2)
    (hp : logLowerHalflineCutoff (-A) p = p)
    {z : ℂ} (hz : 0 < z.im) :
    suzukiLowerFourierLaplace (-A) p z =
      suzukiLowerFourierLaplace A p z + suzukiCompactL2Fourier A p z := by
  rw [suzukiLowerFourierLaplace_eq_integral,
    suzukiLowerFourierLaplace_eq_integral, suzukiCompactL2Fourier]
  let fminus : ℝ → ℂ := fun t => (Ici (-A)).indicator
    (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * p t) t
  let fplus : ℝ → ℂ := fun t => (Ici A).indicator
    (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * p t) t
  let fshell : ℝ → ℂ := fun t =>
    (suzukiCutoff A p) t * Complex.exp (I * z * (t : ℂ))
  have hfminus : Integrable fminus :=
    integrable_suzukiLowerFourierLaplace_integrand (-A) p hz
  have hfplus : Integrable fplus :=
    integrable_suzukiLowerFourierLaplace_integrand A p hz
  have hfshell : Integrable fshell := by
    simpa only [fshell, mul_comm] using
      integrable_suzukiCompactL2Fourier_integrand hA p z
  rw [← integral_add hfplus hfshell]
  apply integral_congr_ae
  have hcut := indicatorCutoff_ae (Icc (-A) A) measurableSet_Icc p
  have hlower := indicatorCutoff_ae (Ici (-A)) measurableSet_Ici p
  have heq : (logLowerHalflineCutoff (-A) p : ℝ → ℂ) = (p : ℝ → ℂ) :=
    congrArg (fun q : SoninL2 => (q : ℝ → ℂ)) hp
  filter_upwards [hcut, hlower,
    compl_mem_ae_iff.mpr (show (volume : Measure ℝ) ({-A, A} : Set ℝ) = 0 by
      exact (Set.toFinite ({-A, A} : Set ℝ)).countable.measure_zero volume)] with
      t hcut hlower htend
  change fminus t = fplus t + fshell t
  have hlowerPoint : logLowerHalflineCutoff (-A) p t = p t := congrFun heq t
  have hpZero (ht : t < -A) : p t = 0 := by
    rw [← hlowerPoint]
    simpa [logLowerHalflineCutoff, not_le_of_gt ht] using hlower
  have htneNeg : t ≠ -A := by
    intro h
    exact htend (by simp [h])
  have htnePos : t ≠ A := by
    intro h
    exact htend (by simp [h])
  by_cases htLower : -A < t
  · by_cases htUpper : t < A
    · have hminusMem : t ∈ Ici (-A) := htLower.le
      have hplusNot : t ∉ Ici A := not_le_of_gt htUpper
      have hshellMem : t ∈ Icc (-A) A := ⟨htLower.le, htUpper.le⟩
      simp only [fminus, fplus, fshell, indicator_of_mem hminusMem,
        indicator_of_notMem hplusNot, zero_add]
      rw [show suzukiCutoff A p t =
          (Icc (-A) A).indicator (fun s => p s) t by
            simpa only [Function.comp_apply] using hcut,
        indicator_of_mem hshellMem]
      ring
    · have htA : A < t := lt_of_le_of_ne (le_of_not_gt htUpper) (Ne.symm htnePos)
      have hminusMem : t ∈ Ici (-A) := htLower.le
      have hplusMem : t ∈ Ici A := htA.le
      have hshellNot : t ∉ Icc (-A) A := fun h => (not_le_of_gt htA) h.2
      simp only [fminus, fplus, fshell, indicator_of_mem hminusMem,
        indicator_of_mem hplusMem]
      rw [show suzukiCutoff A p t =
          (Icc (-A) A).indicator (fun s => p s) t by
            simpa only [Function.comp_apply] using hcut,
        indicator_of_notMem hshellNot, zero_mul, add_zero]
  · have htNegA : t < -A := lt_of_le_of_ne (le_of_not_gt htLower) htneNeg
    have hminusNot : t ∉ Ici (-A) := not_le_of_gt htNegA
    have hplusNot : t ∉ Ici A := by
      intro h
      exact (not_le_of_gt (lt_of_lt_of_le htNegA (by linarith))) h
    have hshellNot : t ∉ Icc (-A) A := fun h => (not_le_of_gt htNegA) h.1
    simp only [fminus, fplus, fshell, indicator_of_notMem hminusNot,
      indicator_of_notMem hplusNot]
    rw [show suzukiCutoff A p t =
        (Icc (-A) A).indicator (fun s => p s) t by
          simpa only [Function.comp_apply] using hcut,
      indicator_of_notMem hshellNot, zero_mul, add_zero]

/-- A compactly supported logarithmic source has its upper transform equal to its entire compact
Fourier transform with reversed spectral variable. -/
theorem suzukiUpperFourierLaplace_eq_compactL2Fourier_neg_of_fixed
    {A : ℝ} {q : SoninL2} (hqUpper : logHalflineCutoff A q = q)
    (hqCompact : suzukiCutoff A q = q) (z : ℂ) :
    suzukiUpperFourierLaplace A q z = suzukiCompactL2Fourier A q (-z) := by
  rw [suzukiUpperFourierLaplace, suzukiCompactL2Fourier]
  unfold suzukiUpperFourierLaplaceIntegrand
  have hupperEq : (logHalflineCutoff A q : ℝ → ℂ) = (q : ℝ → ℂ) :=
    congrArg (fun p : SoninL2 => (p : ℝ → ℂ)) hqUpper
  have hcompactEq : (suzukiCutoff A q : ℝ → ℂ) = (q : ℝ → ℂ) :=
    congrArg (fun p : SoninL2 => (p : ℝ → ℂ)) hqCompact
  apply integral_congr_ae
  filter_upwards [indicatorCutoff_ae (Iic A) measurableSet_Iic q] with t hcut
  have hupperPoint : logHalflineCutoff A q t = q t := congrFun hupperEq t
  have hcompactPoint : suzukiCutoff A q t = q t := congrFun hcompactEq t
  rw [hcompactPoint]
  by_cases ht : t ∈ Iic A
  · rw [indicator_of_mem ht]
    rw [show (-I) * z * (t : ℂ) = I * (-z) * (t : ℂ) by ring]
    ring
  · have hqZero : q t = 0 := by
      rw [← hupperPoint]
      simpa [logHalflineCutoff, ht] using hcut
    rw [indicator_of_notMem ht, hqZero, zero_mul]

/-- Exact equation (4.22.1) on the strict upper half-plane. -/
theorem suzuki2012_equation_four_two_two_one
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 0 < z.im) :
    suzukiHankelPsi omega a homega ha z =
      suzukiHankelPsiContinuation omega a homega ha z := by
  let A := Real.log a
  let q := suzukiHankelPhiSumLog omega a homega ha
  let p := suzukiHankelPhiSumHankelLog omega a homega ha
  let H := suzukiCanonicalLogHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt
      (show 1 / 2 < omega by linarith))
  have hA : 0 ≤ A := (Real.log_pos ha).le
  have hqUpper : logHalflineCutoff A q = q := by
    exact logHalflineCutoff_suzukiPhysicalIntervalPositive (by linarith)
      (suzukiHankelPhiSum omega a homega ha)
  have hqCompact : suzukiCutoff A q = q :=
    suzukiHankelPhiSum_log_compact homega ha
  have hpLower : logLowerHalflineCutoff (-A) p = p := by
    exact suzukiCanonicalLogHankelUnitary_maps_upper_to_reflected_lower
      (show 1 / 2 < omega by linarith) q hqUpper
  have hsplit := suzukiLowerFourierLaplace_split_compact hA p hpLower hz
  have h401 := suzuki2012_equation_four_zero_one
    (show 1 / 2 < omega by linarith) q hqUpper hz
  have hsource :=
    suzukiUpperFourierLaplace_eq_compactL2Fourier_neg_of_fixed
      hqUpper hqCompact z
  have h401' : suzukiLowerFourierLaplace (-A) p z =
      suzukiCanonicalTheta omega z * suzukiUpperFourierLaplace A q z := by
    simpa only [p, q, suzukiHankelPhiSumHankelLog] using h401
  have hsplit' : suzukiLowerFourierLaplace A p z =
      suzukiLowerFourierLaplace (-A) p z - suzukiCompactL2Fourier A p z :=
    (eq_sub_iff_add_eq).2 hsplit.symm
  change suzukiLowerFourierLaplace A (-p) z =
    -suzukiCanonicalTheta omega z * suzukiCompactL2Fourier A q (-z) +
      suzukiCompactL2Fourier A p z
  rw [suzukiLowerFourierLaplace_eq_CLM A (-p) z hz,
    map_neg, ← suzukiLowerFourierLaplace_eq_CLM A p z hz,
    hsplit', h401', hsource]
  ring

/-- Suzuki's continuation formula is meromorphic on the whole plane. -/
theorem meromorphicOn_suzukiHankelPsiContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    MeromorphicOn (suzukiHankelPsiContinuation omega a homega ha) Set.univ := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  have hsourceDiff : Differentiable ℂ (fun z : ℂ =>
      suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) (-z)) :=
    (differentiable_suzukiCompactL2Fourier hA _).comp (by fun_prop)
  have houtDiff : Differentiable ℂ (suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha)) :=
    differentiable_suzukiCompactL2Fourier hA _
  have hsource : AnalyticOnNhd ℂ (fun z : ℂ =>
      suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) (-z)) Set.univ :=
    hsourceDiff.differentiableOn.analyticOnNhd isOpen_univ
  have hout : AnalyticOnNhd ℂ (suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha)) Set.univ :=
    houtDiff.differentiableOn.analyticOnNhd isOpen_univ
  exact ((meromorphicOn_suzukiCanonicalTheta omega).neg.mul hsource.meromorphicOn).add
    hout.meromorphicOn

/-- The continuation has no poles in the upper half-plane. -/
theorem analyticOnNhd_suzukiHankelPsiContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    AnalyticOnNhd ℂ (suzukiHankelPsiContinuation omega a homega ha)
      suzukiUpperHalfPlane := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  have htheta : AnalyticOnNhd ℂ (suzukiCanonicalTheta omega)
      suzukiUpperHalfPlane := by
    exact (suzukiCanonicalTheta_meromorphicInner_of_half_lt
      (show 1 / 2 < omega by linarith)).2.1
  have hsourceAll : AnalyticOnNhd ℂ (fun z : ℂ =>
      suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) (-z)) Set.univ :=
    ((differentiable_suzukiCompactL2Fourier hA _).comp (by fun_prop)).differentiableOn
      |>.analyticOnNhd isOpen_univ
  have houtAll : AnalyticOnNhd ℂ (suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha)) Set.univ :=
    (differentiable_suzukiCompactL2Fourier hA _).differentiableOn
      |>.analyticOnNhd isOpen_univ
  exact (htheta.neg.mul (hsourceAll.mono (subset_univ _))).add
    (houtAll.mono (subset_univ _))

/-! ## The `L²` boundary value in Lemma 4.7 -/

/-- A uniformly bounded damping symbol.  The `max` makes it bounded for every real parameter;
on the source-relevant half-line `y ≥ 0`, it is exactly `exp (-y max(t,0))`. -/
def suzukiNonnegativeDampingSymbol (y t : ℝ) : ℂ :=
  (Real.exp (-(max y 0) * max t 0) : ℝ)

theorem measurable_suzukiNonnegativeDampingSymbol (y : ℝ) :
    Measurable (suzukiNonnegativeDampingSymbol y) := by
  exact (show Continuous (fun t : ℝ =>
      ((Real.exp (-(max y 0) * max t 0) : ℝ) : ℂ)) by fun_prop).measurable

theorem norm_suzukiNonnegativeDampingSymbol_le_one (y t : ℝ) :
    ‖suzukiNonnegativeDampingSymbol y t‖ ≤ 1 := by
  rw [suzukiNonnegativeDampingSymbol, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (le_max_right y 0)) (le_max_right t 0))

def suzukiNonnegativeDampingCLM (y : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_suzukiNonnegativeDampingSymbol y) (C := 1) (by norm_num)
    (norm_suzukiNonnegativeDampingSymbol_le_one y)

/-- Exterior source whose ordinary Fourier transform is the horizontal line
`z = u + i y` of Suzuki's integral. -/
def suzukiHankelPsiDampedSource
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (y : ℝ) : SoninL2 :=
  suzukiNonnegativeDampingCLM y
    (logLowerHalflineCutoff (Real.log a)
      (suzukiHankelPhiDifferenceLog omega a homega ha))

def suzukiHankelPsiBoundarySource
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  logLowerHalflineCutoff (Real.log a)
    (suzukiHankelPhiDifferenceLog omega a homega ha)

/-- Damping tends strongly to the exterior source as `y → 0`. -/
theorem tendsto_suzukiHankelPsiDampedSource
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Tendsto (suzukiHankelPsiDampedSource omega a homega ha)
      (𝓝 0) (𝓝 (suzukiHankelPsiBoundarySource omega a homega ha)) := by
  let q := suzukiHankelPsiBoundarySource omega a homega ha
  have hpt (t : ℝ) : Tendsto
      (fun y : ℝ => suzukiNonnegativeDampingSymbol y t)
      (𝓝 0) (𝓝 (1 : ℂ)) := by
    simpa [suzukiNonnegativeDampingSymbol] using
      (show ContinuousAt (fun y : ℝ =>
        ((Real.exp (-(max y 0) * max t 0) : ℝ) : ℂ)) 0 by fun_prop).tendsto
  have hraw := MeasureTheory.tendsto_lpBoundedMulCLM_apply
    (φ := fun y : ℝ => suzukiNonnegativeDampingSymbol y)
    (ψ := fun _ : ℝ => (1 : ℂ))
    (fun y => measurable_suzukiNonnegativeDampingSymbol y) measurable_const
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun y t => norm_suzukiNonnegativeDampingSymbol_le_one y t)
    (fun _ => by norm_num) hpt q
  have htarget :
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) measurable_const
          (C := 1) (by norm_num)
          (fun _ : ℝ => show ‖(1 : ℂ)‖ ≤ 1 by norm_num) q = q := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (p := 2)
      (μ := (volume : Measure ℝ)) measurable_const (C := 1) (by norm_num)
      (fun _ : ℝ => show ‖(1 : ℂ)‖ ≤ 1 by norm_num) q] with t ht
    rw [ht]
    simp
  rw [htarget] at hraw
  convert hraw using 1 <;>
    rfl

/-- Positive scaling converting mathlib's Fourier frequency to Suzuki's real spectral variable. -/
def suzukiFourierToSpectralScale : ℝ := 1 / (2 * Real.pi)

theorem suzukiFourierToSpectralScale_pos : 0 < suzukiFourierToSpectralScale := by
  rw [suzukiFourierToSpectralScale]
  positivity

/-- Exact `L²` reparametrization `F(w) ↦ F(-u/(2π))`, including its Jacobian normalization. -/
def suzukiFourierToSpectralL2 (F : SoninL2) : SoninL2 :=
  ((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹) •
    l2Reflection
      (dilationUnitary suzukiFourierToSpectralScale
        suzukiFourierToSpectralScale_pos F)

theorem suzukiFourierToSpectralL2_ae (F : SoninL2) :
    (suzukiFourierToSpectralL2 F : ℝ → ℂ) =ᵐ[volume]
      fun u => F (-suzukiFourierToSpectralScale * u) := by
  have hsmul := Lp.coeFn_smul
    ((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹)
    (l2Reflection
      (dilationUnitary suzukiFourierToSpectralScale
        suzukiFourierToSpectralScale_pos F))
  have href := l2Reflection_ae
    (dilationUnitary suzukiFourierToSpectralScale
      suzukiFourierToSpectralScale_pos F)
  have hdil := (dilation_ae suzukiFourierToSpectralScale
    suzukiFourierToSpectralScale_pos F).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hsmul, href, hdil] with u hsmul href hdil
  change (((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹) •
      l2Reflection
        (dilationUnitary suzukiFourierToSpectralScale
          suzukiFourierToSpectralScale_pos F) : SoninL2) u = _
  rw [hsmul, Pi.smul_apply, smul_eq_mul, href]
  have hdil' :
      (dilationUnitary suzukiFourierToSpectralScale
        suzukiFourierToSpectralScale_pos F) (-u) =
        (Real.sqrt suzukiFourierToSpectralScale : ℂ) *
          F (suzukiFourierToSpectralScale * -u) := by
    simpa only [dilationUnitary_apply, Function.comp_apply] using hdil
  rw [hdil']
  have hsqrt : (Real.sqrt suzukiFourierToSpectralScale : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr suzukiFourierToSpectralScale_pos)
  rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]
  congr 1
  ring

def suzukiHankelPsiL2Line
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (y : ℝ) : SoninL2 :=
  suzukiFourierToSpectralL2
    (fourierUnitary (suzukiHankelPsiDampedSource omega a homega ha y))

def suzukiHankelPsiL2Boundary
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) : SoninL2 :=
  suzukiFourierToSpectralL2
    (fourierUnitary (suzukiHankelPsiBoundarySource omega a homega ha))

/-- The horizontal interior lines converge in `L²(ℝ,du)` to Suzuki's boundary value. -/
theorem tendsto_suzukiHankelPsiL2Line
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Tendsto (suzukiHankelPsiL2Line omega a homega ha)
      (𝓝 0) (𝓝 (suzukiHankelPsiL2Boundary omega a homega ha)) := by
  have hsource := tendsto_suzukiHankelPsiDampedSource homega ha
  have hfourier := (fourierUnitary.continuous.tendsto
    (suzukiHankelPsiBoundarySource omega a homega ha)).comp hsource
  have hdilation := ((dilationUnitary suzukiFourierToSpectralScale
    suzukiFourierToSpectralScale_pos).continuous.tendsto
      (fourierUnitary (suzukiHankelPsiBoundarySource omega a homega ha))).comp hfourier
  have hreflection := (l2Reflection.continuous.tendsto
      (dilationUnitary suzukiFourierToSpectralScale
        suzukiFourierToSpectralScale_pos
        (fourierUnitary (suzukiHankelPsiBoundarySource omega a homega ha)))).comp hdilation
  exact hreflection.const_smul
    ((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹)

/-- Pointwise representative of the damped exterior source for `y ≥ 0`. -/
theorem suzukiHankelPsiDampedSource_ae
    {omega a y : ℝ} (homega : 1 < omega) (ha : 1 < a) (hy : 0 ≤ y) :
    (suzukiHankelPsiDampedSource omega a homega ha y : ℝ → ℂ) =ᵐ[volume]
      fun t => (Ici (Real.log a)).indicator (fun t : ℝ =>
        (Real.exp (-y * t) : ℂ) *
          suzukiHankelPhiDifferenceLog omega a homega ha t) t := by
  let A := Real.log a
  let q := suzukiHankelPhiDifferenceLog omega a homega ha
  let p := logLowerHalflineCutoff A q
  have hmul := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (measurable_suzukiNonnegativeDampingSymbol y) (C := 1) (by norm_num)
    (norm_suzukiNonnegativeDampingSymbol_le_one y) p
  have hcut := indicatorCutoff_ae (Ici A) measurableSet_Ici q
  filter_upwards [hmul, hcut] with t hmul hcut
  change suzukiNonnegativeDampingCLM y p t = _
  rw [show suzukiNonnegativeDampingCLM y p t =
      suzukiNonnegativeDampingSymbol y t * p t by
        simpa only [suzukiNonnegativeDampingCLM] using hmul]
  change suzukiNonnegativeDampingSymbol y t *
      logLowerHalflineCutoff A q t = _
  rw [show logLowerHalflineCutoff A q t =
      (Ici A).indicator (fun s => q s) t by
        simpa [logLowerHalflineCutoff] using hcut]
  by_cases ht : t ∈ Ici A
  · have hA : 0 ≤ A := (Real.log_pos ha).le
    have ht0 : 0 ≤ t := le_trans hA ht
    rw [indicator_of_mem ht, indicator_of_mem ht,
      suzukiNonnegativeDampingSymbol, max_eq_left hy, max_eq_left ht0]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]

/-- For `y>0` the damped exterior source is both `L¹` and `L²`; this is the absolute-convergence
part of Lemma 4.7 packaged for Plancherel. -/
theorem integrable_suzukiHankelPsiDampedSource
    {omega a y : ℝ} (homega : 1 < omega) (ha : 1 < a) (hy : 0 < y) :
    Integrable (suzukiHankelPsiDampedSource omega a homega ha y : ℝ → ℂ) := by
  let A := Real.log a
  let q := suzukiHankelPhiDifferenceLog omega a homega ha
  let z : ℂ := (y : ℂ) * I
  have hz : 0 < z.im := by simp [z, hy]
  have hbase := integrable_suzukiLowerFourierLaplace_integrand A q hz
  have hliteral : Integrable fun t : ℝ => (Ici A).indicator (fun t : ℝ =>
      (Real.exp (-y * t) : ℂ) * q t) t := by
    apply hbase.congr
    filter_upwards with t
    by_cases ht : t ∈ Ici A
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      have hexp : Complex.exp (I * z * (t : ℂ)) =
          (Real.exp (-y * t) : ℂ) := by
        rw [show I * z * (t : ℂ) = ((-y * t : ℝ) : ℂ) by
          dsimp only [z]
          ring_nf
          rw [I_sq]
          push_cast
          ring, Complex.ofReal_exp]
      rw [hexp]
    · simp [ht]
  exact hliteral.congr
    (suzukiHankelPsiDampedSource_ae homega ha hy.le).symm

theorem two_pi_mul_suzukiFourierToSpectralScale :
    2 * Real.pi * suzukiFourierToSpectralScale = 1 := by
  rw [suzukiFourierToSpectralScale]
  field_simp [Real.pi_ne_zero]

/-- Classical Fourier integral of the damped source, at the exactly rescaled frequency, is
Suzuki's horizontal-line value. -/
theorem fourier_suzukiHankelPsiDampedSource
    {omega a y : ℝ} (homega : 1 < omega) (ha : 1 < a) (hy : 0 ≤ y)
    (u : ℝ) :
    FourierTransform.fourier
        (suzukiHankelPsiDampedSource omega a homega ha y : ℝ → ℂ)
        (-suzukiFourierToSpectralScale * u) =
      suzukiHankelPsi omega a homega ha ((u : ℂ) + (y : ℂ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, suzukiHankelPsi,
    suzukiLowerFourierLaplace_eq_integral]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [suzukiHankelPsiDampedSource_ae homega ha hy] with t ht
  rw [ht]
  by_cases htA : t ∈ Ici (Real.log a)
  · rw [indicator_of_mem htA, indicator_of_mem htA]
    rw [Complex.ofReal_exp]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    rw [suzukiFourierToSpectralScale]
    field_simp
    ring_nf
    rw [I_sq]
    push_cast
    ring
  · simp [htA]

/-- For every `y>0`, the `L²` line has the literal pointwise representative
`u ↦ Psi_a(u+i y)`. -/
theorem suzukiHankelPsiL2Line_ae
    {omega a y : ℝ} (homega : 1 < omega) (ha : 1 < a) (hy : 0 < y) :
    (suzukiHankelPsiL2Line omega a homega ha y : ℝ → ℂ) =ᵐ[volume]
      fun u => suzukiHankelPsi omega a homega ha ((u : ℂ) + (y : ℂ) * I) := by
  let d := suzukiHankelPsiDampedSource omega a homega ha y
  have hdInt : Integrable (d : ℝ → ℂ) :=
    integrable_suzukiHankelPsiDampedSource homega ha hy
  have hfourier :
      ((fourierUnitary d : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        FourierTransform.fourier (d : ℝ → ℂ) := by
    have h := GaloisForLFunctions.RHTower.coeFn_fourier_toLp hdInt (Lp.memLp d)
    rw [Lp.toLp_coeFn d (Lp.memLp d)] at h
    exact h
  have hscale := hfourier.comp_tendsto
    (realMul_quasiMeasurePreserving
      (-suzukiFourierToSpectralScale)
      (neg_ne_zero.mpr (ne_of_gt suzukiFourierToSpectralScale_pos))).tendsto_ae
  have hreparam := suzukiFourierToSpectralL2_ae (fourierUnitary d)
  filter_upwards [hreparam, hscale] with u hreparam hscale
  change suzukiFourierToSpectralL2 (fourierUnitary d) u = _
  have hscale' :
      fourierUnitary d (-suzukiFourierToSpectralScale * u) =
        FourierTransform.fourier (d : ℝ → ℂ)
          (-suzukiFourierToSpectralScale * u) := by
    simpa only [Function.comp_apply] using hscale
  rw [hreparam, hscale']
  exact fourier_suzukiHankelPsiDampedSource homega ha hy.le u

/-- Uniform horizontal-line `L²` bound in Suzuki's Lemma 4.7.  Together with
`analyticOnNhd_suzukiHankelPsiContinuation` and `suzukiHankelPsiL2Line_ae`, this is the
upper-half-plane Hardy `H²` assertion used in Suzuki's proof. -/
theorem norm_suzukiHankelPsiL2Line_le
    {omega a y : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ‖suzukiHankelPsiL2Line omega a homega ha y‖ ≤
      ‖((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹)‖ *
        ‖suzukiHankelPsiBoundarySource omega a homega ha‖ := by
  let q := suzukiHankelPsiBoundarySource omega a homega ha
  let M := suzukiNonnegativeDampingCLM y
  have hM : ‖M‖ ≤ 1 := by
    exact norm_lpBoundedMulCLM_le
      (measurable_suzukiNonnegativeDampingSymbol y) (by norm_num)
      (norm_suzukiNonnegativeDampingSymbol_le_one y)
  have hMq : ‖M q‖ ≤ ‖q‖ := by
    calc
      ‖M q‖ ≤ ‖M‖ * ‖q‖ := M.le_opNorm q
      _ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg q)
      _ = ‖q‖ := one_mul _
  have href (f : SoninL2) : ‖l2Reflection f‖ = ‖f‖ := by
    exact l2ReflectionIsometry.norm_map f
  change ‖((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹) •
      l2Reflection
        (dilationUnitary suzukiFourierToSpectralScale
          suzukiFourierToSpectralScale_pos
          (fourierUnitary (M q)))‖ ≤ _
  rw [norm_smul, href,
    (dilationUnitary suzukiFourierToSpectralScale
      suzukiFourierToSpectralScale_pos).norm_map,
    fourierUnitary.norm_map]
  exact mul_le_mul_of_nonneg_left hMq (norm_nonneg _)

/-- **Suzuki (2012), Lemma 4.7, closed formal statement.**

Every source condition from the paper is quantified inside the proposition.  The conclusion contains
the literal global equation (4.22), absolute convergence of (4.21), the Hardy `H²` line bound and
`L²` boundary convergence, the exact continuation formula (4.22.1), meromorphic continuation on
the whole plane, and analyticity on the strict upper half-plane. -/
theorem suzuki2012_lemma_four_seven :
    ∀ (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a),
      (∀ {b : ℝ} (hab : a ≤ b),
        suzukiPositiveIntervalRestriction b
            (suzukiHankelPhiDifferencePositive omega a homega ha) =
          suzukiHankelPhiExtended SuzukiHankelSign.positive omega a b
              (by linarith) ha hab -
            suzukiHankelPhiExtended SuzukiHankelSign.negative omega a b
              (by linarith) ha hab) ∧
      (∀ z : ℂ, 0 < z.im →
        Integrable fun t : ℝ => (Ici (Real.log a)).indicator
          (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) *
            suzukiHankelPhiDifferenceLog omega a homega ha t) t) ∧
      (∀ y : ℝ, 0 < y →
        (suzukiHankelPsiL2Line omega a homega ha y : ℝ → ℂ)
          =ᵐ[volume] fun u =>
            suzukiHankelPsi omega a homega ha
              ((u : ℂ) + (y : ℂ) * I)) ∧
      Tendsto (suzukiHankelPsiL2Line omega a homega ha)
        (nhds 0) (nhds (suzukiHankelPsiL2Boundary omega a homega ha)) ∧
      (∀ y : ℝ,
        ‖suzukiHankelPsiL2Line omega a homega ha y‖ ≤
          ‖((Real.sqrt suzukiFourierToSpectralScale : ℂ)⁻¹)‖ *
            ‖suzukiHankelPsiBoundarySource omega a homega ha‖) ∧
      (∀ z : ℂ, 0 < z.im →
        suzukiHankelPsi omega a homega ha z =
          suzukiHankelPsiContinuation omega a homega ha z) ∧
      MeromorphicOn
        (suzukiHankelPsiContinuation omega a homega ha) Set.univ ∧
      AnalyticOnNhd ℂ
        (suzukiHankelPsiContinuation omega a homega ha)
        suzukiUpperHalfPlane := by
  intro omega a homega ha
  refine ⟨suzuki2012_equation_four_two_two homega ha, ?_, ?_,
    tendsto_suzukiHankelPsiL2Line homega ha, ?_, ?_,
    meromorphicOn_suzukiHankelPsiContinuation homega ha,
    analyticOnNhd_suzukiHankelPsiContinuation homega ha⟩
  · intro z hz
    exact integrable_suzukiLowerFourierLaplace_integrand
      (Real.log a) (suzukiHankelPhiDifferenceLog omega a homega ha) hz
  · intro y hy
    exact suzukiHankelPsiL2Line_ae homega ha hy
  · intro y
    exact norm_suzukiHankelPsiL2Line_le homega ha
  · intro z hz
    exact suzuki2012_equation_four_two_two_one homega ha hz

end RHTower
