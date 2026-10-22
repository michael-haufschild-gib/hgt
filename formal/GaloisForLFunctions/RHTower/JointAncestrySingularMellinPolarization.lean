import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusPrimeNormalSuccessorBlowup
import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldGradedDet2ScalarDescentBoundary
import GaloisForLFunctions.RHTower.GammaSewnSynchronizedLcmContraction
import GaloisForLFunctions.RHTower.MassGaugeSuperluminalCompression
import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication

/-!
# Joint-ancestry singular Mellin polarization

Positive scalar source anomalies cannot act by nonunitary dilation on a fixed positive Hilbert
metric.  This module instead sends every positive gain `g` to logarithmic translation by
`-log g` on one zero-independent `L²(ℝ)` carrier.  Translation is unitary, reflection sends
`g` to `g⁻¹`, and multiplication by `exp(x)` is a densely defined closed self-adjoint
operator satisfying the exact source-shadow covariance

`M_exp T_t = exp(-t) T_t M_exp`.

The reflected closed operator is multiplication by `exp(-x)`; ordinary spatial reflection
interchanges the two maximal domains and the two operators exactly.  The construction is then
specialized to two corpus-native anomalies:

* every Gamma-sewn lcm insertion gain, including exact finite-face weight agreement and
  two-prime cocycle flatness;
* the BV--Wold graded determinant-two anomaly, whose insertion makes the curved transport
  triangle flat on the positive carrier.

This constructs a scalar (`ℂ`-linear) closed anomaly shadow.  It does **not** supply the
`C(PrimeTorus)`-source-linearity required by the prime-Poisson JAS gate: the corpus
superselection theorem rules such a nonzero closed sewing out away from `σ = 1/2`.  It also
does not identify the operator with the completed theta value/derivative current or prove an Xi
landing.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

set_option maxHeartbeats 800000

open GaloisForLFunctions.HTGeometry

/-- Exponentially weighted scalar source reporter on compactly supported test functions. -/
def jointAncestrySingularMellinShadow (f : ℝ → ℂ) : ℂ :=
  ∫ x, (Real.exp x : ℂ) * f x

theorem jointAncestry_integrable_singularMellinShadow
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x => (Real.exp x : ℂ) * f x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact hfc.mul_left

theorem jointAncestrySingularMellinShadow_translate (t : ℝ) (f : ℝ → ℂ) :
    jointAncestrySingularMellinShadow (fun x => f (x + t)) =
      (Real.exp (-t) : ℂ) * jointAncestrySingularMellinShadow f := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun y : ℝ => (Real.exp (y - t) : ℂ) * f y) t
  rw [jointAncestrySingularMellinShadow, jointAncestrySingularMellinShadow]
  calc
    ∫ x, (Real.exp x : ℂ) * f (x + t) =
        ∫ x, (Real.exp (x - t) : ℂ) * f x := by
          simpa only [add_sub_cancel_right] using h
    _ = ∫ x, (Real.exp (-t) : ℂ) *
          ((Real.exp x : ℂ) * f x) := by
      congr 1
      funext x
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring_nf
    _ = (Real.exp (-t) : ℂ) *
          ∫ x, (Real.exp x : ℂ) * f x := by
      rw [integral_const_mul]

theorem jointAncestrySingularMellinShadow_neg_log_translate
    {g : ℝ} (hg : 0 < g) (f : ℝ → ℂ) :
    jointAncestrySingularMellinShadow (fun x => f (x - Real.log g)) =
      (g : ℂ) * jointAncestrySingularMellinShadow f := by
  rw [show (fun x => f (x - Real.log g)) =
      fun x => f (x + (-Real.log g)) by
        funext x
        rw [sub_eq_add_neg]]
  rw [jointAncestrySingularMellinShadow_translate]
  simp [Real.exp_log hg]

/-- Positive gain `g` acts on one fixed `L²(ℝ)` carrier by unitary translation through
`-log g`. -/
def jointAncestryPositiveMellinLift (g : ℝ) :
    Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 :=
  MellinL2.additiveTranslationUnitary (-Real.log g)

/-- Closed operator-valued replacement for the nonclosable scalar shadow. -/
def jointAncestrySingularMellinOperator :
    Lp (α := ℝ) ℂ 2 →ₗ.[ℂ] Lp (α := ℝ) ℂ 2 :=
  maximalRealL2Mul (volume : Measure ℝ) Real.exp

theorem jointAncestrySingularMellinOperator_dense :
    Dense (jointAncestrySingularMellinOperator.domain : Set (Lp (α := ℝ) ℂ 2)) := by
  exact maximalRealL2Mul_dense (volume : Measure ℝ) Real.continuous_exp.measurable

theorem jointAncestrySingularMellinOperator_selfAdjoint :
    IsSelfAdjoint jointAncestrySingularMellinOperator := by
  exact maximalRealL2Mul_isSelfAdjoint (volume : Measure ℝ)
    Real.continuous_exp.measurable

theorem jointAncestrySingularMellinOperator_closed :
    jointAncestrySingularMellinOperator.IsClosed :=
  jointAncestrySingularMellinOperator_selfAdjoint.isClosed

theorem jointAncestrySingularMellinOperator_translation_mem
    (t : ℝ) (f : jointAncestrySingularMellinOperator.domain) :
    MellinL2.additiveTranslationUnitary t (f : Lp (α := ℝ) ℂ 2) ∈
      jointAncestrySingularMellinOperator.domain := by
  change MemLp (fun x : ℝ => (Real.exp x : ℂ) *
    (MellinL2.additiveTranslationUnitary t (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) x)
      2 volume
  have hcomp := f.property.comp_measurePreserving
    (MellinL2.realTranslation_measurePreserving t)
  have hscaled := hcomp.const_mul (Real.exp (-t) : ℂ)
  refine (memLp_congr_ae ?_).mpr hscaled
  filter_upwards [translation_coeFn_massGaugeSuperluminalCompression t (f : Lp (α := ℝ) ℂ 2)] with x hx
  rw [hx]
  change (Real.exp x : ℂ) * (f : Lp (α := ℝ) ℂ 2) (x + t) =
    (Real.exp (-t) : ℂ) *
      ((Real.exp (x + t) : ℂ) * (f : Lp (α := ℝ) ℂ 2) (x + t))
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring_nf

/-- Exact closed-shadow covariance `M_exp T_t = exp(-t) T_t M_exp` on the maximal domain. -/
theorem jointAncestrySingularMellinOperator_covariance
    (t : ℝ) (f Tf : jointAncestrySingularMellinOperator.domain)
    (htranslate : (Tf : Lp (α := ℝ) ℂ 2) =
      MellinL2.additiveTranslationUnitary t (f : Lp (α := ℝ) ℂ 2)) :
    jointAncestrySingularMellinOperator Tf =
      (Real.exp (-t) : ℂ) •
        MellinL2.additiveTranslationUnitary t
          (jointAncestrySingularMellinOperator f) := by
  apply Lp.ext
  have hApply : (jointAncestrySingularMellinOperator Tf : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp x : ℂ) * (Tf : Lp (α := ℝ) ℂ 2) x := by
    simpa only [jointAncestrySingularMellinOperator] using
      (maximalRealL2Mul_apply_ae (volume : Measure ℝ) Real.exp Tf)
  have hAfBase : (jointAncestrySingularMellinOperator f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp x : ℂ) * (f : Lp (α := ℝ) ℂ 2) x := by
    simpa only [jointAncestrySingularMellinOperator] using
      (maximalRealL2Mul_apply_ae (volume : Measure ℝ) Real.exp f)
  have hAf := hAfBase.comp_tendsto
    (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
  have hTfCoe : (Tf : ℝ → ℂ) =ᵐ[volume]
      (MellinL2.additiveTranslationUnitary t (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) := by
    rw [htranslate]
  filter_upwards [hApply, hTfCoe, translation_coeFn_massGaugeSuperluminalCompression t (f : Lp (α := ℝ) ℂ 2),
    Lp.coeFn_smul (Real.exp (-t) : ℂ)
      (MellinL2.additiveTranslationUnitary t (jointAncestrySingularMellinOperator f)),
    translation_coeFn_massGaugeSuperluminalCompression t (jointAncestrySingularMellinOperator f), hAf] with x hleft hTf' hf hs hr hA
  rw [hleft, hTf', hf, hs]
  change (Real.exp x : ℂ) * (f : Lp (α := ℝ) ℂ 2) (x + t) =
    (Real.exp (-t) : ℂ) *
      (MellinL2.additiveTranslationUnitary t
        (jointAncestrySingularMellinOperator f) : ℝ → ℂ) x
  rw [hr]
  change (jointAncestrySingularMellinOperator f : ℝ → ℂ) (x + t) =
    (Real.exp (x + t) : ℂ) * (f : Lp (α := ℝ) ℂ 2) (x + t) at hA
  rw [hA]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring_nf

/-- Every positive scalar gain is recovered by the closed operator shadow of its unitary Mellin
lift. -/
theorem jointAncestrySingularMellinOperator_mellinLiftCovariance
    {g : ℝ} (hg : 0 < g)
    (f Tf : jointAncestrySingularMellinOperator.domain)
    (htranslate : (Tf : Lp (α := ℝ) ℂ 2) = jointAncestryPositiveMellinLift g f) :
    jointAncestrySingularMellinOperator Tf =
      (g : ℂ) • jointAncestryPositiveMellinLift g (jointAncestrySingularMellinOperator f) := by
  let t : ℝ := -Real.log g
  have htranslate' : (Tf : Lp (α := ℝ) ℂ 2) =
      MellinL2.additiveTranslationUnitary t f := by
    exact htranslate
  have hcov := jointAncestrySingularMellinOperator_covariance t f Tf htranslate'
  simpa only [t, jointAncestryPositiveMellinLift, neg_neg, Real.exp_log hg] using hcov

/-- Reflected exponential multiplier. -/
def jointAncestrySingularMellinReflectedOperator :
    Lp (α := ℝ) ℂ 2 →ₗ.[ℂ] Lp (α := ℝ) ℂ 2 :=
  maximalRealL2Mul (volume : Measure ℝ) (fun x => Real.exp (-x))

theorem jointAncestrySingularMellinReflectedOperator_dense :
    Dense (jointAncestrySingularMellinReflectedOperator.domain :
      Set (Lp (α := ℝ) ℂ 2)) := by
  exact maximalRealL2Mul_dense (volume : Measure ℝ) (by fun_prop)

theorem jointAncestrySingularMellinReflectedOperator_selfAdjoint :
    IsSelfAdjoint jointAncestrySingularMellinReflectedOperator := by
  exact maximalRealL2Mul_isSelfAdjoint (volume : Measure ℝ) (by fun_prop)

theorem jointAncestrySingularMellinReflectedOperator_closed :
    jointAncestrySingularMellinReflectedOperator.IsClosed :=
  jointAncestrySingularMellinReflectedOperator_selfAdjoint.isClosed

theorem jointAncestry_l2Reflection_coeFn (f : Lp (α := ℝ) ℂ 2) :
    (l2Reflection f : ℝ → ℂ) =ᵐ[volume] fun x => (f : ℝ → ℂ) (-x) := by
  change (Lp.compMeasurePreserving (fun x : ℝ => -x)
    (Measure.measurePreserving_neg (volume : Measure ℝ)) f : ℝ → ℂ) =ᵐ[volume]
      fun x => (f : ℝ → ℂ) (-x)
  exact Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem jointAncestrySingularMellinOperator_reflection_mem
    (f : jointAncestrySingularMellinOperator.domain) :
    l2Reflection (f : Lp (α := ℝ) ℂ 2) ∈
      jointAncestrySingularMellinReflectedOperator.domain := by
  change MemLp (fun x : ℝ => (Real.exp (-x) : ℂ) *
    (l2Reflection (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) x) 2 volume
  have hcomp := f.property.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  refine (memLp_congr_ae ?_).mpr hcomp
  filter_upwards [jointAncestry_l2Reflection_coeFn (f : Lp (α := ℝ) ℂ 2)] with x hx
  rw [hx]
  rfl

/-- Spatial reflection exchanges the positive and negative closed Mellin shadows exactly. -/
theorem jointAncestrySingularMellinOperator_reflection_covariance
    (f : jointAncestrySingularMellinOperator.domain)
    (Rf : jointAncestrySingularMellinReflectedOperator.domain)
    (hRf : (Rf : Lp (α := ℝ) ℂ 2) = l2Reflection f) :
    jointAncestrySingularMellinReflectedOperator Rf =
      l2Reflection (jointAncestrySingularMellinOperator f) := by
  apply Lp.ext
  have hleft : (jointAncestrySingularMellinReflectedOperator Rf : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (-x) : ℂ) *
        (Rf : Lp (α := ℝ) ℂ 2) x := by
    simpa only [jointAncestrySingularMellinReflectedOperator] using
      (maximalRealL2Mul_apply_ae (volume : Measure ℝ)
        (fun x : ℝ => Real.exp (-x)) Rf)
  have hRfCoe : (Rf : ℝ → ℂ) =ᵐ[volume]
      (l2Reflection (f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) := by
    rw [hRf]
  have hAfBase : (jointAncestrySingularMellinOperator f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp x : ℂ) * (f : Lp (α := ℝ) ℂ 2) x := by
    simpa only [jointAncestrySingularMellinOperator] using
      (maximalRealL2Mul_apply_ae (volume : Measure ℝ) Real.exp f)
  have hAf := hAfBase.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hleft, hRfCoe,
    jointAncestry_l2Reflection_coeFn (f : Lp (α := ℝ) ℂ 2),
    jointAncestry_l2Reflection_coeFn (jointAncestrySingularMellinOperator f), hAf]
      with x hl hrc hrf hrA hA
  rw [hl, hrc, hrf, hrA]
  change (jointAncestrySingularMellinOperator f : ℝ → ℂ) (-x) =
    (Real.exp (-x) : ℂ) * (f : Lp (α := ℝ) ℂ 2) (-x) at hA
  exact hA.symm

/-- The positive cocycle lift preserves the fixed Hilbert polarization exactly. -/
theorem jointAncestryPositiveMellinLift_inner
    (g : ℝ) (f h : Lp (α := ℝ) ℂ 2) :
    inner ℂ (jointAncestryPositiveMellinLift g f) (jointAncestryPositiveMellinLift g h) =
      inner ℂ f h := by
  exact (jointAncestryPositiveMellinLift g).inner_map_map f h

theorem jointAncestryPositiveMellinLift_reflection
    (g : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    l2Reflection (jointAncestryPositiveMellinLift g f) =
      MellinL2.additiveTranslationUnitary (Real.log g)
        (l2Reflection f) := by
  simpa [jointAncestryPositiveMellinLift] using
    MellinL2.l2Reflection_additiveTranslation (-Real.log g) f

theorem jointAncestryPositiveMellinLift_mul
    {g h : ℝ} (hg : 0 < g) (hh : 0 < h)
    (f : MobiusThetaSourceL2) :
    jointAncestryPositiveMellinLift g (jointAncestryPositiveMellinLift h f) =
      jointAncestryPositiveMellinLift (g * h) f := by
  rw [jointAncestryPositiveMellinLift, jointAncestryPositiveMellinLift,
    jointAncestryPositiveMellinLift,
    additiveTranslationUnitary_add_apply]
  congr 1
  rw [Real.log_mul hg.ne' hh.ne']
  ring_nf

theorem jointAncestryPositiveMellinLift_flat
    {g₁ g₂ h₁ h₂ : ℝ}
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hflat : g₁ * g₂ = h₁ * h₂)
    (f : MobiusThetaSourceL2) :
    jointAncestryPositiveMellinLift g₁ (jointAncestryPositiveMellinLift g₂ f) =
      jointAncestryPositiveMellinLift h₁ (jointAncestryPositiveMellinLift h₂ f) := by
  rw [jointAncestryPositiveMellinLift_mul hg₁ hg₂,
    jointAncestryPositiveMellinLift_mul hh₁ hh₂, hflat]

theorem jointAncestryPositiveMellinLift_inv_reflection
    (g : ℝ) (f : MobiusThetaSourceL2) :
    l2Reflection (jointAncestryPositiveMellinLift g f) =
      jointAncestryPositiveMellinLift g⁻¹ (l2Reflection f) := by
  rw [jointAncestryPositiveMellinLift_reflection]
  simp only [jointAncestryPositiveMellinLift, Real.log_inv]
  congr 1
  ring_nf

theorem jointAncestryPositiveMellinLift_mul_three
    {g h k : ℝ} (hg : 0 < g) (hh : 0 < h) (hk : 0 < k)
    (f : MobiusThetaSourceL2) :
    jointAncestryPositiveMellinLift g
        (jointAncestryPositiveMellinLift h (jointAncestryPositiveMellinLift k f)) =
      jointAncestryPositiveMellinLift (g * h * k) f := by
  rw [jointAncestryPositiveMellinLift_mul hg hh,
    jointAncestryPositiveMellinLift_mul (mul_pos hg hh) hk]

theorem jointAncestry_primeDepthBVWoldAnomaly_shadow
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) (f : ℝ → ℂ) :
    jointAncestrySingularMellinShadow (fun x =>
        f (x + a * primeDepthBVWoldConsecutiveIncrementArea i j k)) =
      (primeDepthBVWoldGradedDet2Anomaly a i j k : ℂ) *
        jointAncestrySingularMellinShadow f := by
  rw [jointAncestrySingularMellinShadow_translate]
  simp only [primeDepthBVWoldGradedDet2Anomaly]
  congr 2
  ring_nf

theorem jointAncestry_primeDepthBVWoldAnomaly_mellinLift_eq_translation
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    jointAncestryPositiveMellinLift (primeDepthBVWoldGradedDet2Anomaly a i j k) =
      MellinL2.additiveTranslationUnitary
        (a * primeDepthBVWoldConsecutiveIncrementArea i j k) := by
  unfold jointAncestryPositiveMellinLift primeDepthBVWoldGradedDet2Anomaly
  rw [Real.log_exp]
  congr 1
  ring_nf

theorem jointAncestry_primeDepthBVWold_mellinLift_flat
    (a : ℝ) (i j k : PrimeDepthBVWoldCell)
    (f : MobiusThetaSourceL2) :
    jointAncestryPositiveMellinLift (primeDepthBVWoldTransport a i j)
        (jointAncestryPositiveMellinLift (primeDepthBVWoldTransport a j k)
          (jointAncestryPositiveMellinLift
            (primeDepthBVWoldGradedDet2Anomaly a i j k) f)) =
      jointAncestryPositiveMellinLift (primeDepthBVWoldTransport a i k) f := by
  rw [jointAncestryPositiveMellinLift_mul_three
    (primeDepthBVWoldTransport_pos a i j)
    (primeDepthBVWoldTransport_pos a j k)
    (primeDepthBVWoldGradedDet2Anomaly_pos a i j k),
    primeDepthBVWoldTransport_mul_gradedDet2Anomaly]

/-- Every Gamma-sewn synchronized lcm insertion gain is strictly positive, so logarithmic
unitary lifting is defined on every nonempty compound face. -/
theorem jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) {P : Finset Nat.Primes}
    (hP : P.Nonempty) :
    0 < gammaSewnSynchronizedLcmInsertionGain x p P := by
  have hnode := gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP
  exact div_pos
    (mul_pos
      (mul_pos
        (mul_pos
          (gammaSewnMobiusValuationContractionMultiplier_pos x p)
          (div_pos
            (xiTransversePrimeApertureDiskNode_pos 1 p)
            (by linarith [xiTransversePrimeApertureDiskNode_pos 1 p])))
        (sub_pos.mpr (xiMobiusContinuousApertureDiskNode_lt_one hx p)))
      (sub_pos.mpr hnode.2))
    (sub_pos.mpr (by
      have hp0 := xiMobiusContinuousApertureDiskNode_pos x p
      have hp1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
      nlinarith [hnode.1]))

theorem jointAncestry_gammaSewnMellinLift_closedShadow
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) {P : Finset Nat.Primes}
    (hP : P.Nonempty)
    (f Tf : jointAncestrySingularMellinOperator.domain)
    (htranslate : (Tf : Lp (α := ℝ) ℂ 2) =
      jointAncestryPositiveMellinLift (gammaSewnSynchronizedLcmInsertionGain x p P) f) :
    jointAncestrySingularMellinOperator Tf =
      (gammaSewnSynchronizedLcmInsertionGain x p P : ℂ) •
        jointAncestryPositiveMellinLift (gammaSewnSynchronizedLcmInsertionGain x p P)
          (jointAncestrySingularMellinOperator f) := by
  exact jointAncestrySingularMellinOperator_mellinLiftCovariance
    (jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos hx p hP) f Tf htranslate

theorem jointAncestry_gammaSewnMellinLift_closedShadow_weightInsert
    {x : ℝ} (hx : 0 < x) {p : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P)
    (f Tf : jointAncestrySingularMellinOperator.domain)
    (htranslate : (Tf : Lp (α := ℝ) ℂ 2) =
      jointAncestryPositiveMellinLift (gammaSewnSynchronizedLcmInsertionGain x p P) f) :
    (gammaSewnSynchronizedLcmWeight x P : ℂ) •
        jointAncestrySingularMellinOperator Tf =
      (gammaSewnSynchronizedLcmWeight x (insert p P) : ℂ) •
        jointAncestryPositiveMellinLift (gammaSewnSynchronizedLcmInsertionGain x p P)
          (jointAncestrySingularMellinOperator f) := by
  rw [jointAncestry_gammaSewnMellinLift_closedShadow hx p hP f Tf htranslate,
    gammaSewnSynchronizedLcmWeight_insert hx hP hp]
  simp only [Complex.ofReal_mul, smul_smul]
  congr 1
  ring_nf

/-- Two-prime Gamma-sewn insertion paths agree as actual unitary transports, not merely after
scalar evaluation. -/
theorem jointAncestry_gammaSewnMellinLift_cocycle
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) (hq : q ∉ P) (hpq : p ≠ q)
    (f : MobiusThetaSourceL2) :
    jointAncestryPositiveMellinLift (gammaSewnSynchronizedLcmInsertionGain x p P)
        (jointAncestryPositiveMellinLift
          (gammaSewnSynchronizedLcmInsertionGain x q (insert p P)) f) =
      jointAncestryPositiveMellinLift (gammaSewnSynchronizedLcmInsertionGain x q P)
        (jointAncestryPositiveMellinLift
          (gammaSewnSynchronizedLcmInsertionGain x p (insert q P)) f) := by
  apply jointAncestryPositiveMellinLift_flat
  · exact jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos hx p hP
  · exact jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos hx q
      (Finset.insert_nonempty p P)
  · exact jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos hx q hP
  · exact jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos hx p
      (Finset.insert_nonempty q P)
  · exact gammaSewnSynchronizedLcmInsertionGain_cocycle hx hP hp hq hpq

/-- The same closed operator shadow recovers the exact BV--Wold graded determinant-two anomaly. -/
theorem jointAncestry_primeDepthBVWoldAnomaly_mellinLift_closedShadow
    (a : ℝ) (i j k : PrimeDepthBVWoldCell)
    (f Tf : jointAncestrySingularMellinOperator.domain)
    (htranslate : (Tf : Lp (α := ℝ) ℂ 2) =
      jointAncestryPositiveMellinLift (primeDepthBVWoldGradedDet2Anomaly a i j k) f) :
    jointAncestrySingularMellinOperator Tf =
      (primeDepthBVWoldGradedDet2Anomaly a i j k : ℂ) •
        jointAncestryPositiveMellinLift (primeDepthBVWoldGradedDet2Anomaly a i j k)
          (jointAncestrySingularMellinOperator f) := by
  exact jointAncestrySingularMellinOperator_mellinLiftCovariance
    (primeDepthBVWoldGradedDet2Anomaly_pos a i j k) f Tf htranslate

end

end RHTower
