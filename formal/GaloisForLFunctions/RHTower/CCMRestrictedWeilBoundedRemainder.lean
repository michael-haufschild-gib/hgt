import GaloisForLFunctions.RHTower.CCMArchimedeanHilbertFormDomain
import GaloisForLFunctions.RHTower.SoninLogShellCocycle
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Exact bounded polar and finite-prime terms of the semilocal Weil form

On the logarithmic aperture `[-a,a]`, the two polar evaluations are Riesz pairings with
`exp(x/2)` and `exp(-x/2)`.  Every finite-prime term is the aperture compression of the two
unitary translations by `± log n`, with the literal coefficient `Λ(n) / sqrt(n)`.  Thus their
sum is a bounded self-adjoint operator.  Together with the exact scalar left over from the
archimedean form norm, this is precisely the bounded remainder in Connes--Consani's restricted
Weil quadratic form.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

noncomputable instance instCompleteSpaceSuzukiApertureHilbert
    (a : SuzukiPositiveAperture) : CompleteSpace (suzukiApertureHilbert a) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (show IsIdempotentElem (indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) from
      indicatorCutoff_idempotent (centralInterval a.1)
        (measurableSet_centralInterval a.1))).completeSpace_coe

/-! ## Translation adjoints and aperture compression -/

/-- Translation by `-h` is the Hilbert adjoint of translation by `h`. -/
theorem inner_logTranslationCLM (h : ℝ) (f g : SoninL2) :
    inner ℂ (logTranslationCLM h f) g =
      inner ℂ f (logTranslationCLM (-h) g) := by
  let U := MellinL2.additiveTranslationUnitary (-h)
  have hcancel : logTranslationCLM (-h) (logTranslationCLM h f) = f := by
    have happ := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f)
      (logTranslationCLM_neg_mul h)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using happ
  calc
    inner ℂ (logTranslationCLM h f) g =
        inner ℂ (U (logTranslationCLM h f)) (U g) :=
      (U.inner_map_map _ _).symm
    _ = inner ℂ f (logTranslationCLM (-h) g) := by
      change inner ℂ (logTranslationCLM (-h) (logTranslationCLM h f))
        (logTranslationCLM (-h) g) = _
      rw [hcancel]

/-- Symmetric sum of the two source translations at logarithmic displacement `h`. -/
def ccmSymmetricLogTranslation (h : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  logTranslationCLM h + logTranslationCLM (-h)

theorem ccmSymmetricLogTranslation_isSelfAdjoint (h : ℝ) :
    IsSelfAdjoint (ccmSymmetricLogTranslation h) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (logTranslationCLM h f + logTranslationCLM (-h) f) g =
    inner ℂ f (logTranslationCLM h g + logTranslationCLM (-h) g)
  rw [inner_add_left, inner_add_right]
  rw [inner_logTranslationCLM h, inner_logTranslationCLM (-h)]
  simp only [neg_neg]
  ac_rfl

/-- Orthogonal compression of a full-line operator to the logarithmic aperture. -/
def ccmApertureCompression (a : SuzukiPositiveAperture)
    (A : SoninL2 →L[ℂ] SoninL2) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  (suzukiApertureHilbert a).subtypeL.adjoint ∘L A ∘L
    (suzukiApertureHilbert a).subtypeL

theorem ccmApertureCompression_isSelfAdjoint
    (a : SuzukiPositiveAperture) {A : SoninL2 →L[ℂ] SoninL2}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (ccmApertureCompression a A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ ((suzukiApertureHilbert a).subtypeL.adjoint (A f.1)) g =
    inner ℂ f ((suzukiApertureHilbert a).subtypeL.adjoint (A g.1))
  rw [(suzukiApertureHilbert a).subtypeL.adjoint_inner_left,
    (suzukiApertureHilbert a).subtypeL.adjoint_inner_right]
  exact hA.isSymmetric f.1 g.1

theorem inner_ccmApertureCompression
    (a : SuzukiPositiveAperture) (A : SoninL2 →L[ℂ] SoninL2)
    (f g : suzukiApertureHilbert a) :
    inner ℂ (ccmApertureCompression a A f) g = inner ℂ (A f.1) g.1 := by
  exact (suzukiApertureHilbert a).subtypeL.adjoint_inner_left _ _

/-! ## The two polar Riesz vectors -/

def ccmPolarProfile (s x : ℝ) : ℂ := (Real.exp (s * x) : ℂ)

theorem ccmPolarProfile_memLp_aperture (a : SuzukiPositiveAperture) (s : ℝ) :
    MemLp ((centralInterval a.1).indicator (ccmPolarProfile s)) 2 volume := by
  apply (memLp_indicator_iff_restrict (measurableSet_centralInterval a.1)).2
  have hfinite : IsFiniteMeasure (volume.restrict (centralInterval a.1)) := by
    constructor
    simp [centralInterval]
  letI := hfinite
  refine MemLp.of_bound (p := (2 : ENNReal)) ?_
    (Real.exp (|s| * a.1)) ?_
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_centralInterval a.1)] with x hx
    have hxabs : |x| ≤ a.1 := abs_le.mpr hx
    have hsx : s * x ≤ |s| * a.1 := calc
      s * x ≤ |s * x| := le_abs_self _
      _ = |s| * |x| := abs_mul s x
      _ ≤ |s| * a.1 := mul_le_mul_of_nonneg_left hxabs (abs_nonneg s)
    rw [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hsx

def ccmPolarL2Vector (a : SuzukiPositiveAperture) (s : ℝ) : SoninL2 :=
  (ccmPolarProfile_memLp_aperture a s).toLp
    ((centralInterval a.1).indicator (ccmPolarProfile s))

theorem ccmPolarL2Vector_coeFn (a : SuzukiPositiveAperture) (s : ℝ) :
    (ccmPolarL2Vector a s : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (ccmPolarProfile s) :=
  (ccmPolarProfile_memLp_aperture a s).coeFn_toLp

theorem indicatorCutoff_ccmPolarL2Vector
    (a : SuzukiPositiveAperture) (s : ℝ) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (ccmPolarL2Vector a s) = ccmPolarL2Vector a s := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) (ccmPolarL2Vector a s),
    ccmPolarL2Vector_coeFn a s] with x hcut hvec
  rw [hcut]
  by_cases hx : x ∈ centralInterval a.1
  · simp [hx]
  · rw [Set.indicator_of_notMem hx, hvec, Set.indicator_of_notMem hx]

def ccmPolarApertureVector (a : SuzukiPositiveAperture) (s : ℝ) :
    suzukiApertureHilbert a := by
  refine ⟨ccmPolarL2Vector a s, ?_⟩
  rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
  exact ⟨ccmPolarL2Vector a s, indicatorCutoff_ccmPolarL2Vector a s⟩

/-- The source polar term `|h+⟩⟨h-| + |h-⟩⟨h+|`. -/
def ccmPolarOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (1 / 2))
      (ccmPolarApertureVector a (-1 / 2)) +
    InnerProductSpace.rankOne ℂ (ccmPolarApertureVector a (-1 / 2))
      (ccmPolarApertureVector a (1 / 2))

set_option maxHeartbeats 800000 in
theorem ccmPolarOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmPolarOperator a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmPolarOperator
  rw [ContinuousLinearMap.adjoint.map_add,
    InnerProductSpace.adjoint_rankOne, InnerProductSpace.adjoint_rankOne]
  exact add_comm _ _

theorem inner_ccmPolarOperator (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    inner ℂ (ccmPolarOperator a f) f =
      (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) f := by
  rw [ccmPolarOperator, add_apply,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    inner_add_left, inner_smul_left, inner_smul_left]

/-! ## Exact finite-prime operator -/

/-- Connes--Consani's bounded self-adjoint `T(n)` in logarithmic coordinates. -/
def ccmPrimeTransportOperator (a : SuzukiPositiveAperture) (n : ℕ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ((1 / Real.sqrt n : ℝ) : ℂ) •
    ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))

theorem ccmPrimeTransportOperator_isSelfAdjoint
    (a : SuzukiPositiveAperture) (n : ℕ) :
    IsSelfAdjoint (ccmPrimeTransportOperator a n) := by
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint]
  · exact ccmApertureCompression_isSelfAdjoint a
      (ccmSymmetricLogTranslation_isSelfAdjoint (Real.log n))

theorem inner_ccmPrimeTransportOperator
    (a : SuzukiPositiveAperture) (n : ℕ)
    (f g : suzukiApertureHilbert a) :
    inner ℂ (ccmPrimeTransportOperator a n f) g =
      ((1 / Real.sqrt n : ℝ) : ℂ) *
        (inner ℂ (logTranslationCLM (Real.log n) f.1) g.1 +
          inner ℂ (logTranslationCLM (-Real.log n) f.1) g.1) := by
  rw [ccmPrimeTransportOperator, smul_apply, inner_smul_left]
  rw [inner_ccmApertureCompression]
  simp only [ccmSymmetricLogTranslation, add_apply, inner_add_left]
  simp

def ccmFinitePrimeOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) •
      ccmPrimeTransportOperator a n

theorem ccmFinitePrimeOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmFinitePrimeOperator a) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmFinitePrimeOperator
  generalize Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      rw [ContinuousLinearMap.adjoint.map_add, ih]
      have hnself := ccmPrimeTransportOperator_isSelfAdjoint a n
      rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hnself
      rw [ContinuousLinearMap.adjoint.map_smulₛₗ, hnself]
      rw [show (starRingEnd ℂ) (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) =
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) by
          exact Complex.conj_ofReal _]

/-- Exact bounded remainder after the literal archimedean form norm is split off. -/
def ccmArchimedeanRemainderScalar : ℂ :=
  Complex.ofReal (2 * gammaHardyPhaseRate 0 - 1)

theorem star_ccmArchimedeanRemainderScalar :
    (starRingEnd ℂ) ccmArchimedeanRemainderScalar =
      ccmArchimedeanRemainderScalar := by
  unfold ccmArchimedeanRemainderScalar
  exact Complex.conj_ofReal _

def ccmRestrictedWeilBoundedRemainder (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmArchimedeanRemainderScalar • 1 +
    ccmPolarOperator a - ccmFinitePrimeOperator a

set_option maxHeartbeats 800000 in
theorem ccmRestrictedWeilBoundedRemainder_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmRestrictedWeilBoundedRemainder a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold ccmRestrictedWeilBoundedRemainder
  rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint.map_add]
  have hpolar := ccmPolarOperator_isSelfAdjoint a
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hpolar
  have hprime := ccmFinitePrimeOperator_isSelfAdjoint a
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hprime
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint_one, hpolar, hprime]
  rw [star_ccmArchimedeanRemainderScalar]

theorem inner_ccmRestrictedWeilBoundedRemainder
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f =
      ccmArchimedeanRemainderScalar * inner ℂ f f +
        inner ℂ (ccmPolarOperator a f) f -
          inner ℂ (ccmFinitePrimeOperator a f) f := by
  change inner ℂ
      (((ccmArchimedeanRemainderScalar •
          (1 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)) f +
        ccmPolarOperator a f) - ccmFinitePrimeOperator a f) f = _
  rw [inner_sub_left, inner_add_left, smul_apply, one_apply_eq_self,
    inner_smul_left]
  change (starRingEnd ℂ) ccmArchimedeanRemainderScalar * inner ℂ f f +
      inner ℂ (ccmPolarOperator a f) f - inner ℂ (ccmFinitePrimeOperator a f) f = _
  rw [star_ccmArchimedeanRemainderScalar]

theorem inner_ccmFinitePrimeOperator
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    inner ℂ (ccmFinitePrimeOperator a f) f =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          inner ℂ (ccmPrimeTransportOperator a n f) f := by
  classical
  unfold ccmFinitePrimeOperator
  simp

end RHTower
