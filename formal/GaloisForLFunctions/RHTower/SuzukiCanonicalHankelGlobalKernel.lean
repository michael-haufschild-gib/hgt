import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemma47

/-!
# Global physical kernel formula for interval-supported Suzuki data

Suzuki's finite-compression theorem identifies the canonical spectral Hankel unitary only after
restriction to one compact interval.  Lemma 4.8 needs the corresponding physical kernel formula
almost everywhere on the whole positive ray.  This module derives that global statement by a
countable compact exhaustion; no pointwise representative of an arbitrary `L²` class is assumed.
-/

open Complex Real MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

set_option maxHeartbeats 1000000

/-- Exhausting compact endpoint used to globalize the finite compression. -/
def suzukiHankelKernelExhaustionEndpoint (a : ℝ) (n : ℕ) : ℝ :=
  a + n + 1

theorem one_lt_suzukiHankelKernelExhaustionEndpoint
    {a : ℝ} (ha : 1 < a) (n : ℕ) :
    1 < suzukiHankelKernelExhaustionEndpoint a n := by
  rw [suzukiHankelKernelExhaustionEndpoint]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem le_suzukiHankelKernelExhaustionEndpoint
    (a : ℝ) (n : ℕ) :
    a ≤ suzukiHankelKernelExhaustionEndpoint a n := by
  rw [suzukiHankelKernelExhaustionEndpoint]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- On one exhaustion window, the global canonical Hankel output of an interval-supported vector
has the literal kernel representative. -/
theorem suzukiCanonicalPositiveHankel_intervalSource_ae_on_window
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) (n : ℕ) :
    ∀ᵐ x : ClosedInterval 0 (suzukiHankelKernelExhaustionEndpoint a n) ∂volume,
      suzukiCanonicalPositiveHankelUnitary omega
          (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
          (suzukiPhysicalIntervalPositiveIsometry a f) (x : ℝ) =
        ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  let b := suzukiHankelKernelExhaustionEndpoint a n
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
  let inc := suzukiPhysicalIntervalInclusion a b f
  have hb : 1 < b := one_lt_suzukiHankelKernelExhaustionEndpoint ha n
  have hab : a ≤ b := le_suzukiHankelKernelExhaustionEndpoint a n
  have hinput : suzukiPhysicalIntervalPositiveIsometry b inc =
      suzukiPhysicalIntervalPositiveIsometry a f :=
    suzukiPhysicalIntervalInclusion_positiveExtension (by linarith) hab f
  have hcompression :=
    suzukiCanonicalPositiveHankelCompression_eq_compressedHankel
      homega (show 0 < b by linarith)
  have hclass : suzukiPositiveIntervalRestriction b
      (H (suzukiPhysicalIntervalPositiveIsometry a f)) =
        suzukiCompressedHankelOperator omega b homega inc := by
    rw [← hinput]
    exact DFunLike.congr_fun hcompression inc
  have hres := suzukiPositiveIntervalRestriction_value_ae (a := b)
    (H (suzukiPhysicalIntervalPositiveIsometry a f))
  have hT := suzukiCompressedHankelOperator_coeFn omega b homega
    (show 0 < b by linarith) inc
  have hne : ∀ᵐ x : ClosedInterval 0 b ∂volume, (x : ℝ) ≠ 0 := by
    let hmp : MeasurePreserving ((↑) : ClosedInterval 0 b → ℝ)
        (volume : Measure (ClosedInterval 0 b))
        ((volume : Measure ℝ).restrict (Icc 0 b)) :=
      measurePreserving_subtype_coe measurableSet_Icc
    exact hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  filter_upwards [hres, hT, hne] with x hres hT hx0
  have hclassPoint := congrFun (congrArg
    (fun q : IntervalL2 0 b => (q : ClosedInterval 0 b → ℂ)) hclass) x
  rw [hres, hT] at hclassPoint
  have hx : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx0)
  rw [hclassPoint]
  exact suzukiIntegral_physicalIntervalInclusion homega (show 0 < a by linarith)
    hb hab f x hx

/-- **Global physical kernel formula.**  For every interval-supported `L²` source, the canonical
spectral Hankel unitary agrees almost everywhere on `(0,∞)` with Suzuki's literal integral
kernel. -/
theorem suzukiCanonicalPositiveHankel_intervalSource_ae
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) :
    (suzukiCanonicalPositiveHankelUnitary omega
        (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
        (suzukiPhysicalIntervalPositiveIsometry a f) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ).restrict (Ioi 0)]
        fun x => ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (x * (y : ℝ)) * f y ∂volume := by
  let Hf : SuzukiPositiveL2 :=
    suzukiCanonicalPositiveHankelUnitary omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
      (suzukiPhysicalIntervalPositiveIsometry a f)
  have hwindow : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Icc 0 (suzukiHankelKernelExhaustionEndpoint a n) →
        Hf x = ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (x * (y : ℝ)) * f y ∂volume := by
    intro n
    have hsub := suzukiCanonicalPositiveHankel_intervalSource_ae_on_window
      homega ha f n
    have hreal : ∀ᵐ x ∂(volume : Measure ℝ).restrict
        (Icc 0 (suzukiHankelKernelExhaustionEndpoint a n)),
        Hf x = ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (x * (y : ℝ)) * f y ∂volume :=
      (ae_restrict_iff_subtype
        (measurableSet_Icc : MeasurableSet
          (Icc 0 (suzukiHankelKernelExhaustionEndpoint a n)))).2 hsub
    exact (ae_restrict_iff' measurableSet_Icc).mp hreal
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      x ∈ Icc 0 (suzukiHankelKernelExhaustionEndpoint a n) →
        Hf x = ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (x * (y : ℝ)) * f y ∂volume :=
    ae_all_iff.mpr hwindow
  have hallPos : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioi 0), ∀ n : ℕ,
      x ∈ Icc 0 (suzukiHankelKernelExhaustionEndpoint a n) →
        Hf x = ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (x * (y : ℝ)) * f y ∂volume :=
    ae_restrict_of_ae hall
  filter_upwards [hallPos, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
  obtain ⟨n, hn⟩ := exists_nat_gt (x - a)
  apply hx n
  constructor
  · exact hxpos.le
  · rw [suzukiHankelKernelExhaustionEndpoint]
    have hn' : x - a ≤ (n : ℝ) := hn.le
    linarith

/-- Logarithmic half-density form of the global physical kernel theorem.  This is the exact
coordinate statement needed to Mellin-transform the global output without selecting an
unjustified pointwise representative of an `L²` class. -/
theorem suzukiCanonicalLogHankel_intervalSource_ae
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a)
    (f : IntervalL2 0 a) :
    (suzukiCanonicalLogHankelUnitary omega
        (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
        (suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a f)) : ℝ → ℂ)
      =ᵐ[volume] fun t => (Real.exp (t / 2) : ℂ) *
        ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (Real.exp t * (y : ℝ)) * f y ∂volume := by
  let u : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a f
  let q : SoninL2 := suzukiPositiveLogUnitary u
  let p : SoninL2 := suzukiCanonicalLogHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q
  let Hu : SuzukiPositiveL2 := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) u
  have hp : p = suzukiPositiveLogUnitary Hu := by
    dsimp only [p, q, Hu]
    exact (suzukiPositiveLogUnitary_canonicalHankel omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) u).symm
  have hcarrier : suzukiPositiveHalfLineUnitary (logEvenUnitary.symm p) = Hu := by
    rw [hp]
    change suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm
        (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm Hu))) = Hu
    rw [logEvenUnitary.symm_apply_apply,
      suzukiPositiveHalfLineUnitary.apply_symm_apply]
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae p
  rw [hcarrier] at hcoord
  have hcoordWhole := (ae_restrict_iff' measurableSet_Ioi).mp hcoord
  have hcoordExp := realExp_quasiMeasurePreserving.ae hcoordWhole
  have hkernel := suzukiCanonicalPositiveHankel_intervalSource_ae homega ha f
  have hkernelWhole := (ae_restrict_iff' measurableSet_Ioi).mp hkernel
  have hkernelExp := realExp_quasiMeasurePreserving.ae hkernelWhole
  have hrep : (p : ℝ → ℂ) =ᵐ[volume] l2MeasurableRep p :=
    (l2MeasurableRep_ae p).symm
  change (p : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [hrep, hcoordExp, hkernelExp] with t hrep hcoord hkernel
  rw [hrep]
  have hcoord' : Hu (Real.exp t) =
      (Real.exp (-t / 2) : ℂ) * l2MeasurableRep p t := by
    simpa only [Real.log_exp] using hcoord (Real.exp_pos t)
  have hkernel' : Hu (Real.exp t) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (Real.exp t * (y : ℝ)) * f y ∂volume := by
    simpa using hkernel (Real.exp_pos t)
  rw [hkernel'] at hcoord'
  have hweight : (Real.exp (t / 2) : ℂ) * (Real.exp (-t / 2) : ℂ) = 1 := by
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
    exact Real.exp_zero
  calc
    l2MeasurableRep p t =
        (Real.exp (t / 2) : ℂ) *
          ((Real.exp (-t / 2) : ℂ) * l2MeasurableRep p t) := by
      rw [← mul_assoc, hweight, one_mul]
    _ = _ := by rw [← hcoord']

/-! ## Exact shell projection in logarithmic coordinates -/

/-- Restricting a positive-ray `L²` vector to `(0,a)`, extending it by zero, and passing to
logarithmic half-density coordinates is exactly the sharp shell cutoff `[-log a, log a]`, provided
the original logarithmic vector already has the lower support forced by a Hankel image. -/
theorem suzukiPositiveLogUnitary_extension_restriction_eq_cutoff
    {a : ℝ} (ha : 1 < a) (u : SuzukiPositiveL2)
    (hlower : logLowerHalflineCutoff (-Real.log a)
        (suzukiPositiveLogUnitary u) = suzukiPositiveLogUnitary u) :
    suzukiPositiveLogUnitary
        (suzukiPhysicalIntervalPositiveIsometry a
          (suzukiPositiveIntervalRestriction a u)) =
      suzukiCutoff (Real.log a) (suzukiPositiveLogUnitary u) := by
  let f : IntervalL2 0 a := suzukiPositiveIntervalRestriction a u
  let v : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a f
  let q : SoninL2 := suzukiPositiveLogUnitary u
  let r : SoninL2 := suzukiPositiveLogUnitary v
  have hcarrierQ : suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) = u := by
    change suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm
        (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm u))) = u
    rw [logEvenUnitary.symm_apply_apply,
      suzukiPositiveHalfLineUnitary.apply_symm_apply]
  have hcarrierR : suzukiPositiveHalfLineUnitary (logEvenUnitary.symm r) = v := by
    change suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm
        (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm v))) = v
    rw [logEvenUnitary.symm_apply_apply,
      suzukiPositiveHalfLineUnitary.apply_symm_apply]
  have hcoordQ := suzukiPositiveHalfLineUnitary_logEven_symm_ae q
  rw [hcarrierQ] at hcoordQ
  have hcoordQExp := realExp_quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioi).mp hcoordQ)
  have hcoordR := suzukiPositiveHalfLineUnitary_logEven_symm_ae r
  rw [hcarrierR] at hcoordR
  have hcoordRExp := realExp_quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioi).mp hcoordR)
  have hqrep : (q : ℝ → ℂ) =ᵐ[volume] l2MeasurableRep q :=
    (l2MeasurableRep_ae q).symm
  have hrrep : (r : ℝ → ℂ) =ᵐ[volume] l2MeasurableRep r :=
    (l2MeasurableRep_ae r).symm
  have hcut := indicatorCutoff_ae
    (Icc (-Real.log a) (Real.log a)) measurableSet_Icc q
  have hlowerAe := indicatorCutoff_ae (Ici (-Real.log a)) measurableSet_Ici q
  have hlowerPoint :
      (logLowerHalflineCutoff (-Real.log a) q : ℝ → ℂ) = (q : ℝ → ℂ) :=
    congrArg (fun p : SoninL2 => (p : ℝ → ℂ)) hlower
  have hres := suzukiPositiveIntervalRestriction_value_ae (a := a) u
  have hrepF := suzukiPhysicalIntervalRepresentative_ae f
  have hresRep : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      suzukiPhysicalIntervalRepresentative f x = u (x : ℝ) := by
    filter_upwards [hrepF, hres] with x hrepF hres
    rw [hrepF, hres]
  have hresReal : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc 0 a),
      suzukiPhysicalIntervalZeroExtendFun f x = u x := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [hresRep] with x hx
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hx]
  have hresWhole := (ae_restrict_iff' measurableSet_Icc).mp hresReal
  have hresExp := realExp_quasiMeasurePreserving.ae hresWhole
  have hv := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hvExp := realExp_quasiMeasurePreserving.ae hv
  apply Lp.ext
  change (r : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [hcoordQExp, hcoordRExp, hqrep, hrrep, hcut, hlowerAe,
    hresExp, hvExp] with t hcoordQ hcoordR hqrep hrrep hcut hlowerAe hres hv
  rw [hrrep]
  have hcoordQ' : u (Real.exp t) =
      (Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t := by
    simpa only [Real.log_exp] using hcoordQ (Real.exp_pos t)
  have hcoordR' : v (Real.exp t) =
      (Real.exp (-t / 2) : ℂ) * l2MeasurableRep r t := by
    simpa only [Real.log_exp] using hcoordR (Real.exp_pos t)
  have hweight : (Real.exp (t / 2) : ℂ) *
      (Real.exp (-t / 2) : ℂ) = 1 := by
    norm_cast
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hrFromPhysical : l2MeasurableRep r t =
      (Real.exp (t / 2) : ℂ) * v (Real.exp t) := by
    calc
      l2MeasurableRep r t = (Real.exp (t / 2) : ℂ) *
          ((Real.exp (-t / 2) : ℂ) * l2MeasurableRep r t) := by
        rw [← mul_assoc, hweight, one_mul]
      _ = _ := by rw [← hcoordR']
  rw [hrFromPhysical]
  rw [show suzukiCutoff (Real.log a) q t =
      (Icc (-Real.log a) (Real.log a)).indicator (fun s => q s) t by
        simpa only [Function.comp_apply] using hcut]
  by_cases htUpper : t ≤ Real.log a
  · have hexpUpper : Real.exp t ≤ a := by
      rw [← Real.exp_log (show 0 < a by linarith)]
      exact Real.exp_le_exp.mpr htUpper
    have hexpIcc : Real.exp t ∈ Icc (0 : ℝ) a :=
      ⟨(Real.exp_pos t).le, hexpUpper⟩
    have hv' : v (Real.exp t) = suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) :=
      hv (Real.exp_pos t)
    rw [hv', hres hexpIcc]
    by_cases htLower : -Real.log a ≤ t
    · rw [indicator_of_mem
        (show t ∈ Icc (-Real.log a) (Real.log a) from ⟨htLower, htUpper⟩), hqrep]
      calc
        (Real.exp (t / 2) : ℂ) * u (Real.exp t) =
            (Real.exp (t / 2) : ℂ) *
              ((Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t) := by rw [hcoordQ']
        _ = l2MeasurableRep q t := by rw [← mul_assoc, hweight, one_mul]
    · rw [indicator_of_notMem (fun h => htLower h.1)]
      have hnotLower : t ∉ Ici (-Real.log a) := htLower
      have hqZero : q t = 0 := by
        rw [← hlowerPoint]
        simpa [logLowerHalflineCutoff, hnotLower] using hlowerAe
      have hrepZero : l2MeasurableRep q t = 0 := by rw [← hqrep, hqZero]
      rw [hcoordQ', hrepZero, mul_zero, mul_zero]
  · have hexpAbove : a < Real.exp t := by
      rw [← Real.exp_log (show 0 < a by linarith)]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge htUpper)
    have hnotIcc : Real.exp t ∉ Icc (0 : ℝ) a := fun h => (not_le_of_gt hexpAbove) h.2
    have hv' : v (Real.exp t) = suzukiPhysicalIntervalZeroExtendFun f (Real.exp t) :=
      hv (Real.exp_pos t)
    rw [indicator_of_notMem (fun h => htUpper h.2), hv',
      suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hnotIcc, mul_zero]

end RHTower
