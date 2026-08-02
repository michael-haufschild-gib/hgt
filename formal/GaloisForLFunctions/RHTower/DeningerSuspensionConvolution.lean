import GaloisForLFunctions.RHTower.DeningerSuspensionTranslation
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Convolution by a test function acts continuously on the suspension

Convolving a smooth periodic function with a compactly supported smooth function again gives a
smooth periodic function, and on Fourier coefficients the convolution is multiplication by the
value of the transform of the test function at the corresponding frequency.  That value is bounded
by the `L¹` norm of the test function, so convolution is bounded by that norm on every coefficient
seminorm and therefore acts continuously on the suspension tensor product.

The multiplier identity is Fubini's theorem: the double integral is supported in a compact box,
because the test function has compact support, and the integrand is continuous there.

* `deningerConvolve`, `deningerConvolveOp` : convolution by a test function.
* `deningerConvolve_coeff` : **the Fourier coefficients are multiplied by the transform.**
* `deningerSmoothSeminorm_convolve_le` : **convolution is bounded by the `L¹` norm.**
* `deningerSuspensionConvolve_bounded` : **convolution acts continuously on the suspension.**
-/

namespace RHTower

open Complex MeasureTheory

open scoped Convolution TensorProduct

section Convolve

/-- Convolution by a test function. -/
noncomputable def deningerConvolve (φ f : ℝ → ℂ) : ℝ → ℂ :=
  convolution φ f (ContinuousLinearMap.mul ℝ ℂ) volume

theorem deningerConvolve_apply (φ f : ℝ → ℂ) (x : ℝ) :
    deningerConvolve φ f x = ∫ s, φ s * f (x - s) := rfl

/-- The Fourier kernel is continuous. -/
theorem deningerFourierKernel_continuous (T : ℝ) (n : ℤ) :
    Continuous (deningerFourierKernel T n) :=
  continuous_iff_continuousAt.mpr fun x =>
    (deningerFourierKernel_hasDerivAt T n x).continuousAt

/-- **Convolution preserves periodicity.** -/
theorem deningerConvolve_periodic {T : ℝ} {φ f : ℝ → ℂ} (hf : Function.Periodic f T) :
    Function.Periodic (deningerConvolve φ f) T := by
  intro x
  show (∫ s, φ s * f (x + T - s)) = ∫ s, φ s * f (x - s)
  congr 1
  funext s
  have hrw : x + T - s = (x - s) + T := by ring
  rw [hrw, hf (x - s)]

/-- **Convolution by a smooth compactly supported function preserves smoothness.** -/
theorem deningerConvolve_contDiff {φ f : ℝ → ℂ} (hcφ : HasCompactSupport φ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hf : Continuous f) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerConvolve φ f) :=
  hcφ.contDiff_convolution_left _ hφ hf.locallyIntegrable

/-- **Convolution by a test function, as an operator on the smooth periodic test space.** -/
noncomputable def deningerConvolveOp {T : ℝ} {φ : ℝ → ℂ} (hcφ : HasCompactSupport φ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    DeningerSmoothPeriodic T →ₗ[ℂ] DeningerSmoothPeriodic T where
  toFun f := ⟨deningerConvolve φ (f : ℝ → ℂ),
    ⟨deningerConvolve_contDiff hcφ hφ (deningerSmoothPeriodic_contDiff f).continuous,
      deningerConvolve_periodic (deningerSmoothPeriodic_periodic f)⟩⟩
  map_add' f g := by
    refine Subtype.ext ?_
    have hex : ConvolutionExists φ (f : ℝ → ℂ) (ContinuousLinearMap.mul ℝ ℂ) volume :=
      hcφ.convolutionExists_left _ hφ.continuous
        (deningerSmoothPeriodic_contDiff f).continuous.locallyIntegrable
    have hex' : ConvolutionExists φ (g : ℝ → ℂ) (ContinuousLinearMap.mul ℝ ℂ) volume :=
      hcφ.convolutionExists_left _ hφ.continuous
        (deningerSmoothPeriodic_contDiff g).continuous.locallyIntegrable
    exact hex.distrib_add hex'
  map_smul' c f := by
    refine Subtype.ext (funext fun x => ?_)
    show (∫ s, φ s * (c * (f : ℝ → ℂ) (x - s))) = c * ∫ s, φ s * (f : ℝ → ℂ) (x - s)
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    ring

theorem deningerConvolveOp_apply {T : ℝ} {φ : ℝ → ℂ} (hcφ : HasCompactSupport φ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (f : DeningerSmoothPeriodic T) :
    ((deningerConvolveOp (T := T) hcφ hφ f : DeningerSmoothPeriodic T) : ℝ → ℂ)
      = deningerConvolve φ (f : ℝ → ℂ) := rfl

end Convolve

section Multiplier

/-- **The Fourier coefficients of a convolution.**  Convolving multiplies the `n`-th coefficient
by the integral of the test function against the `n`-th kernel: the double integral is supported
in a compact box, so Fubini applies, and the inner integral is the coefficient of a translate. -/
theorem deningerConvolve_coeff {T : ℝ} (hT : 0 < T) {φ f : ℝ → ℂ}
    (hcφ : HasCompactSupport φ) (hφ : Continuous φ) (hf : Continuous f)
    (hper : Function.Periodic f T) (n : ℤ) :
    deningerFourierCoeff T (deningerConvolve φ f) n
      = (∫ s, φ s * deningerFourierKernel T n s) * deningerFourierCoeff T f n := by
  classical
  set K : ℝ → ℂ := deningerFourierKernel T n with hKdef
  set F : ℝ → ℝ → ℂ := fun x s => K x * (φ s * f (x - s)) with hFdef
  have hTne : T ≠ 0 := hT.ne'
  have hcont : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun p : ℝ × ℝ => K p.1 :=
      (deningerFourierKernel_continuous T n).comp continuous_fst
    have h2 : Continuous fun p : ℝ × ℝ => φ p.2 := hφ.comp continuous_snd
    have h3 : Continuous fun p : ℝ × ℝ => f (p.1 - p.2) :=
      hf.comp (continuous_fst.sub continuous_snd)
    exact h1.mul (h2.mul h3)
  have hzero : ∀ p : ℝ × ℝ, p.2 ∉ tsupport φ → Function.uncurry F p = 0 := by
    intro p hp
    show K p.1 * (φ p.2 * f (p.1 - p.2)) = 0
    rw [image_eq_zero_of_notMem_tsupport hp, zero_mul, mul_zero]
  have hmeasA : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hmeasB : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ tsupport φ) :=
    measurableSet_Ioc.prod (isClosed_tsupport φ).measurableSet
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod (volume : Measure ℝ)) := by
    have hprod : (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (volume : Measure ℝ)
        = (volume.prod volume).restrict (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hbox : IsCompact (Set.Icc (0 : ℝ) T ×ˢ tsupport φ) := isCompact_Icc.prod hcφ
    have hbig : IntegrableOn (Function.uncurry F) (Set.Icc (0 : ℝ) T ×ˢ tsupport φ)
        (volume.prod volume) :=
      hcont.continuousOn.integrableOn_compact hbox
    have hsmall : IntegrableOn (Function.uncurry F) (Set.Ioc (0 : ℝ) T ×ˢ tsupport φ)
        (volume.prod volume) :=
      hbig.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self (subset_refl _))
    have hind : (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set ℝ)).indicator (Function.uncurry F)
        = (Set.Ioc (0 : ℝ) T ×ˢ tsupport φ).indicator (Function.uncurry F) := by
      funext p
      by_cases h2 : p.2 ∈ tsupport φ
      · simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, h2]
      · simp only [Set.indicator_apply, hzero p h2, ite_self]
    rw [hprod]
    refine (integrable_indicator_iff hmeasA).mp ?_
    rw [hind]
    exact (integrable_indicator_iff hmeasB).mpr hsmall
  have hswap : (∫ x in Set.Ioc (0 : ℝ) T, ∫ s, F x s)
      = ∫ s, ∫ x in Set.Ioc (0 : ℝ) T, F x s :=
    integral_integral_swap hint
  have houter : ∀ x, K x * deningerConvolve φ f x = ∫ s, F x s := by
    intro x
    rw [deningerConvolve_apply, ← MeasureTheory.integral_const_mul]
  have hinner : ∀ s, (∫ x in Set.Ioc (0 : ℝ) T, F x s)
      = φ s * (T * (deningerFourierKernel T n s * deningerFourierCoeff T f n)) := by
    intro s
    have hcomm : (∫ x in Set.Ioc (0 : ℝ) T, F x s)
        = ∫ x in Set.Ioc (0 : ℝ) T, φ s * (K x * f (x - s)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show K x * (φ s * f (x - s)) = φ s * (K x * f (x - s))
      ring
    have hpull : (∫ x in Set.Ioc (0 : ℝ) T, φ s * (K x * f (x - s)))
        = φ s * ∫ x in Set.Ioc (0 : ℝ) T, K x * f (x - s) :=
      MeasureTheory.integral_const_mul _ _
    have hIoc : (∫ x in Set.Ioc (0 : ℝ) T, K x * f (x - s))
        = ∫ x in (0 : ℝ)..T, K x * f (x - s) :=
      (intervalIntegral.integral_of_le hT.le).symm
    have hcoeff : deningerFourierCoeff T (fun t => f (t - s)) n
        = (1 / T) * ∫ x in (0 : ℝ)..T, K x * f (x - s) := rfl
    have htrans := deningerFourierCoeff_translate hTne hper s n
    rw [hcoeff] at htrans
    have hval : (∫ x in (0 : ℝ)..T, K x * f (x - s))
        = T * (deningerFourierKernel T n s * deningerFourierCoeff T f n) := by
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTne
      field_simp at htrans
      rw [htrans]
      ring
    rw [hcomm, hpull, hIoc, hval]
  have hfinal : (∫ s, φ s * (T * (deningerFourierKernel T n s * deningerFourierCoeff T f n)))
      = (T : ℂ) * deningerFourierCoeff T f n * ∫ s, φ s * deningerFourierKernel T n s := by
    have hrw : (fun s => φ s * (T * (deningerFourierKernel T n s * deningerFourierCoeff T f n)))
        = fun s => ((T : ℂ) * deningerFourierCoeff T f n)
            * (φ s * deningerFourierKernel T n s) := by
      funext s
      ring
    rw [hrw, MeasureTheory.integral_const_mul]
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTne
  show (1 / (T : ℂ)) * ∫ x in (0 : ℝ)..T, K x * deningerConvolve φ f x = _
  rw [intervalIntegral.integral_of_le hT.le]
  have hrw2 : (∫ x in Set.Ioc (0 : ℝ) T, K x * deningerConvolve φ f x)
      = ∫ x in Set.Ioc (0 : ℝ) T, ∫ s, F x s :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => houter x)
  rw [hrw2, hswap]
  have hrw3 : (∫ s, ∫ x in Set.Ioc (0 : ℝ) T, F x s)
      = ∫ s, φ s * (T * (deningerFourierKernel T n s * deningerFourierCoeff T f n)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun s => hinner s)
  rw [hrw3, hfinal]
  field_simp
  ring

/-- The modulus of the multiplier is at most the `L¹` norm of the test function. -/
theorem deningerConvolve_multiplier_norm_le {T : ℝ} {φ : ℝ → ℂ} (n : ℤ) :
    ‖∫ s, φ s * deningerFourierKernel T n s‖ ≤ ∫ s, ‖φ s‖ := by
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show ‖φ s * deningerFourierKernel T n s‖ = ‖φ s‖
  rw [norm_mul, deningerFourierKernel_norm, mul_one]

end Multiplier

section SeminormBound

variable {T : ℝ}

/-- **Convolution is bounded by the `L¹` norm of the test function**, on every coefficient
seminorm of the smooth periodic test space. -/
theorem deningerSmoothSeminorm_convolve_le (hT : 0 < T) (k : ℕ) {φ : ℝ → ℂ}
    (hcφ : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (f : DeningerSmoothPeriodic T) :
    deningerSmoothSeminorm hT k (deningerConvolveOp hcφ hφ f)
      ≤ (∫ s, ‖φ s‖) * deningerSmoothSeminorm hT k f := by
  have hC : (0 : ℝ) ≤ ∫ s, ‖φ s‖ :=
    integral_nonneg fun s => norm_nonneg _
  have hcoeff : ∀ n : ℤ,
      ‖deningerFourierCoeff T (deningerConvolve φ (f : ℝ → ℂ)) n‖
        ≤ (∫ s, ‖φ s‖) * ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖ := by
    intro n
    rw [deningerConvolve_coeff hT hcφ hφ.continuous
      (deningerSmoothPeriodic_contDiff f).continuous (deningerSmoothPeriodic_periodic f) n,
      norm_mul]
    exact mul_le_mul_of_nonneg_right (deningerConvolve_multiplier_norm_le n) (norm_nonneg _)
  rw [deningerSmoothSeminorm_apply, deningerSmoothSeminorm_apply, deningerKotheSeminorm_apply,
    deningerKotheSeminorm_apply]
  have hsummable₁ := deningerKothe_summable deningerFourierWeights
    (deningerSmoothCoeff hT (deningerConvolveOp hcφ hφ f)) k
  have hsummable₂ := deningerKothe_summable deningerFourierWeights
    (deningerSmoothCoeff hT f) k
  have hterm : ∀ n : ℤ,
      deningerFourierWeights.w k n
          * ‖((deningerSmoothCoeff hT (deningerConvolveOp hcφ hφ f) :
              DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n‖
        ≤ (∫ s, ‖φ s‖) * (deningerFourierWeights.w k n
            * ‖((deningerSmoothCoeff hT f :
              DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n‖) := by
    intro n
    have hw : (0 : ℝ) ≤ deningerFourierWeights.w k n := (deningerFourierWeights.pos k n).le
    calc deningerFourierWeights.w k n
          * ‖deningerFourierCoeff T (deningerConvolve φ (f : ℝ → ℂ)) n‖
        ≤ deningerFourierWeights.w k n
            * ((∫ s, ‖φ s‖) * ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖) :=
          mul_le_mul_of_nonneg_left (hcoeff n) hw
      _ = (∫ s, ‖φ s‖) * (deningerFourierWeights.w k n
            * ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖) := by ring
  calc ∑' n : ℤ, deningerFourierWeights.w k n
          * ‖((deningerSmoothCoeff hT (deningerConvolveOp hcφ hφ f) :
            DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n‖
      ≤ ∑' n : ℤ, (∫ s, ‖φ s‖) * (deningerFourierWeights.w k n
          * ‖((deningerSmoothCoeff hT f :
            DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n‖) :=
        Summable.tsum_le_tsum hterm hsummable₁ (hsummable₂.mul_left _)
    _ = (∫ s, ‖φ s‖) * ∑' n : ℤ, deningerFourierWeights.w k n
          * ‖((deningerSmoothCoeff hT f :
            DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n‖ := tsum_mul_left

end SeminormBound

section Suspension

variable {Y : Type*} [TopologicalSpace Y] {T : ℝ}

local instance deningerSuspensionConvolveAddCommGroup
    (F : Submodule ℂ (DeningerTestSpaceC Y)) :
    AddCommGroup (TensorProduct ℂ ↥F ↥(DeningerSmoothPeriodic T)) :=
  @TensorProduct.addCommGroup ℂ _ ↥F ↥(DeningerSmoothPeriodic T) _ _ _ _

/-- **Convolution by a compactly supported smooth test function acts continuously on the
suspension**, with norm at most the `L¹` norm of the test function. -/
theorem deningerSuspensionConvolve_bounded (hT : 0 < T)
    (F : Submodule ℂ (DeningerTestSpaceC Y)) (p : Seminorm ℂ (DeningerTestSpaceC Y)) (k : ℕ)
    {φ : ℝ → ℂ} (hcφ : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (u : TensorProduct ℂ ↥F ↥(DeningerSmoothPeriodic T)) :
    deningerTensorSeminorm (deningerRestrictSeminorm F p) (deningerSmoothSeminorm hT k)
        (TensorProduct.map LinearMap.id (deningerConvolveOp hcφ hφ) u)
      ≤ (∫ s, ‖φ s‖) * deningerTensorSeminorm (deningerRestrictSeminorm F p)
          (deningerSmoothSeminorm hT k) u := by
  have hC : (0 : ℝ) ≤ ∫ s, ‖φ s‖ := integral_nonneg fun s => norm_nonneg _
  have hbound := deningerTensorSeminorm_map_le (p := deningerRestrictSeminorm F p)
    (p' := deningerRestrictSeminorm F p) (q := deningerSmoothSeminorm hT k)
    (q' := deningerSmoothSeminorm hT k) (f := LinearMap.id)
    (g := deningerConvolveOp hcφ hφ) zero_le_one hC
    (fun x => by rw [one_mul]; exact le_rfl)
    (fun y => deningerSmoothSeminorm_convolve_le hT k hcφ hφ y) u
  rwa [one_mul] at hbound

end Suspension

end RHTower
