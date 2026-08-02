import GaloisForLFunctions.RHTower.DeningerMeyerCompleteSourceComparisonSingularity
import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Compactness.Lindelof

/-!
# Pointwise Xi nonerasure does not imply source fidelity

The complete Riemann source and the literal Meyer source admit a fixed,
uniformly first-order regular comparison whose Mellin transform is nonzero at
every actual Xi divisor point.  This does not contradict cofinal attenuation:
the comparison is rank one, factors through the source codiagonal, identifies
all source labels, and annihilates every canonical reflection displacement.
On normalized actual source vectors its Xi values are nonzero at each finite
stage but converge to zero cofinally.

The construction begins with one normalized smooth compactly supported bump.
Its Mellin transform is an entire nonzero function, so its zero set is
discrete and countable.  The actual Xi divisor support is also countable.
Complex exponential modulation translates the Mellin transform.  A single
modulation outside the countable union of bad translates therefore avoids
every actual Xi divisor point simultaneously.

This gives the sharp positive survivor of the complete-source singularity
wall.  Pointwise nonerasure alone is too weak to express arithmetic spectral
fidelity: it is already satisfied by a regular comparison which destroys all
transverse source geometry.  A viable last-mile comparison must impose
label/reflection fidelity in addition to pointwise Xi nonerasure.

All results are unconditional.  No RH, positivity, simplicity, trace formula,
inverse Mellin theorem, numerical computation, or divisor-selected family of
sources is used.
-/

open Complex Filter Function Set Topology MeasureTheory
open scoped Classical

namespace RHTower

noncomputable section

/-- A fixed smooth bump with support in the unit interval. -/
def deningerMeyerXiAvoidanceBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The normalized complex-valued profile of the fixed bump. -/
def deningerMeyerXiAvoidanceProfile (t : ℝ) : ℂ :=
  (deningerMeyerXiAvoidanceBump.normed volume t : ℂ)

theorem deningerMeyerXiAvoidanceProfile_smooth :
    ContDiff ℝ (⊤ : ℕ∞) deningerMeyerXiAvoidanceProfile := by
  exact
    Complex.ofRealCLM.contDiff.comp
      deningerMeyerXiAvoidanceBump.contDiff_normed

theorem deningerMeyerXiAvoidanceProfile_compact :
    HasCompactSupport deningerMeyerXiAvoidanceProfile := by
  exact
    deningerMeyerXiAvoidanceBump.hasCompactSupport_normed.comp_left rfl

/-- Fixed compactly supported literal Meyer source before modulation. -/
def deningerMeyerXiAvoidanceBaseSource :
    DeningerMeyerStrongLogTarget :=
  ⟨deningerMeyerXiAvoidanceProfile,
    deningerMeyerStrongLogDecay_of_hasCompactSupport
      deningerMeyerXiAvoidanceProfile_smooth
      deningerMeyerXiAvoidanceProfile_compact⟩

/-- Normalization makes the base Mellin transform equal to one at zero. -/
theorem deningerMeyerXiAvoidanceBaseSource_mellin_zero :
    deningerMeyerStrongLogMellin
        deningerMeyerXiAvoidanceBaseSource 0 = 1 := by
  rw [deningerMeyerStrongLogMellin]
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul,
    zero_mul, Complex.exp_zero, one_mul]
  simp only [deningerMeyerXiAvoidanceBaseSource,
    deningerMeyerXiAvoidanceProfile]
  change
    (∫ t : ℝ,
      (deningerMeyerXiAvoidanceBump.normed volume t : ℂ)) = 1
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (deningerMeyerXiAvoidanceBump.integral_normed (μ := volume))
  exact (integral_ofReal (𝕜 := ℂ)).trans h

/-- Complex exponential modulation of the fixed bump profile. -/
def deningerMeyerXiModulatedProfile
    (a : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (a * (t : ℂ)) *
    deningerMeyerXiAvoidanceProfile t

theorem deningerMeyerXiModulatedProfile_smooth (a : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (deningerMeyerXiModulatedProfile a) := by
  have hofReal :
      ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hexp :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun t : ℝ => Complex.exp (a * (t : ℂ))) :=
    (contDiff_const.mul hofReal).cexp
  exact hexp.mul deningerMeyerXiAvoidanceProfile_smooth

theorem deningerMeyerXiModulatedProfile_compact (a : ℂ) :
    HasCompactSupport (deningerMeyerXiModulatedProfile a) := by
  exact deningerMeyerXiAvoidanceProfile_compact.mul_left

/-- Modulated compactly supported literal Meyer source. -/
def deningerMeyerXiModulatedSource
    (a : ℂ) : DeningerMeyerStrongLogTarget :=
  ⟨deningerMeyerXiModulatedProfile a,
    deningerMeyerStrongLogDecay_of_hasCompactSupport
      (deningerMeyerXiModulatedProfile_smooth a)
      (deningerMeyerXiModulatedProfile_compact a)⟩

/-- Exponential modulation translates the entire Mellin transform. -/
theorem deningerMeyerXiModulatedSource_mellin
    (a s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerXiModulatedSource a) s =
      deningerMeyerStrongLogMellin
        deningerMeyerXiAvoidanceBaseSource (s + a) := by
  rw [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellin]
  apply integral_congr_ae
  filter_upwards with t
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul,
    deningerMeyerXiModulatedSource,
    deningerMeyerXiModulatedProfile,
    deningerMeyerXiAvoidanceBaseSource]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Zero set of the nonzero entire base Mellin transform. -/
def deningerMeyerXiAvoidanceZeroSet : Set ℂ :=
  {s |
    deningerMeyerStrongLogMellin
      deningerMeyerXiAvoidanceBaseSource s = 0}

/-- The base Mellin zero set is countable. -/
theorem deningerMeyerXiAvoidanceZeroSet_countable :
    deningerMeyerXiAvoidanceZeroSet.Countable := by
  have hnonzero :
      deningerMeyerStrongLogMellin
          deningerMeyerXiAvoidanceBaseSource 0 ≠ 0 := by
    rw [deningerMeyerXiAvoidanceBaseSource_mellin_zero]
    norm_num
  have hcodiscrete :=
    (analyticOnNhd_deningerMeyerStrongLogMellin
      deningerMeyerXiAvoidanceBaseSource.property)
      |>.preimage_zero_mem_codiscrete hnonzero
  have hcompl :
      deningerMeyerXiAvoidanceZeroSetᶜ ∈ codiscrete ℂ := by
    change
      (deningerMeyerStrongLogMellin
        deningerMeyerXiAvoidanceBaseSource ⁻¹' {0})ᶜ ∈
          codiscrete ℂ
    simpa only [preimage_compl] using hcodiscrete
  have hdiscrete : IsDiscrete deningerMeyerXiAvoidanceZeroSet :=
    (compl_mem_codiscrete_iff.mp hcompl).2
  exact
    (IsLindelof.of_coe (s := deningerMeyerXiAvoidanceZeroSet))
      |>.countable_of_isDiscrete hdiscrete

/-- Modulations at which at least one actual Xi trace vanishes. -/
def deningerMeyerXiBadModulations : Set ℂ :=
  ⋃ rho : XiDivisorSupport,
    (fun a : ℂ => (rho : ℂ) + a) ⁻¹'
      deningerMeyerXiAvoidanceZeroSet

theorem deningerMeyerXiBadModulations_countable :
    deningerMeyerXiBadModulations.Countable := by
  letI : Countable XiDivisorSupport :=
    xiDivisorSupport_countable
  apply Set.countable_iUnion
  intro rho
  exact
    deningerMeyerXiAvoidanceZeroSet_countable.preimage
      (fun _ _ h => add_left_cancel h)

/--
One modulation makes one fixed compact Meyer source nonzero at every actual
Xi divisor point simultaneously.
-/
theorem exists_deningerMeyerXiModulatedSource_nonzero_on_support :
    ∃ a : ℂ, ∀ rho : XiDivisorSupport,
      deningerMeyerStrongLogMellin
        (deningerMeyerXiModulatedSource a) (rho : ℂ) ≠ 0 := by
  have hexists :
      ∃ a : ℂ, a ∉ deningerMeyerXiBadModulations := by
    by_contra hnone
    push Not at hnone
    have huniv :
        deningerMeyerXiBadModulations = Set.univ :=
      Set.eq_univ_of_forall hnone
    have huncount :
        ¬ (Set.univ : Set ℂ).Countable :=
      Set.not_countable_univ
    apply huncount
    rw [← huniv]
    exact deningerMeyerXiBadModulations_countable
  obtain ⟨a, ha⟩ := hexists
  refine ⟨a, ?_⟩
  intro rho
  rw [deningerMeyerXiModulatedSource_mellin]
  intro hzero
  apply ha
  rw [deningerMeyerXiBadModulations, Set.mem_iUnion]
  exact ⟨rho, hzero⟩

/-- A fixed modulation avoiding every actual Xi divisor point. -/
noncomputable def deningerMeyerXiAvoidingModulation : ℂ :=
  Classical.choose
    exists_deningerMeyerXiModulatedSource_nonzero_on_support

/-- One fixed compactly supported source nonzero on all actual Xi support. -/
def deningerMeyerXiAvoidingSource :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerXiModulatedSource deningerMeyerXiAvoidingModulation

theorem deningerMeyerXiAvoidingSource_nonzero_on_support
    (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin
        deningerMeyerXiAvoidingSource (rho : ℂ) ≠ 0 := by
  exact
    (Classical.choose_spec
      exists_deningerMeyerXiModulatedSource_nonzero_on_support) rho

/--
Fixed rank-one comparison obtained by scalar fusion followed by the one
Xi-avoiding Meyer source.
-/
def deningerMeyerPointwiseXiComparison :
    DeningerMeyerCompleteSourceComparison :=
  sourceFusionCodiagonal.toLinearMap.smulRight
    deningerMeyerXiAvoidingSource

@[simp] theorem deningerMeyerPointwiseXiComparison_apply
    (x : CompleteResolutionSourceSpace) :
    deningerMeyerPointwiseXiComparison x =
      sourceFusionCodiagonal x •
        deningerMeyerXiAvoidingSource := by
  rfl

/-- Every actual complete source is sent to the same fixed Meyer source. -/
theorem deningerMeyerPointwiseXiComparison_completeSource
    (K : ℕ) (rho : XiDivisorSupport) :
    deningerMeyerPointwiseXiComparison
        (completeResolutionSourceVector K (rho : ℂ)
          (xi_divisor_support_re_mem_open_unit rho).1) =
      deningerMeyerXiAvoidingSource := by
  rw [deningerMeyerPointwiseXiComparison_apply,
    (completeResolution_banachHilbert_sourceFusion_dichotomy
      K (rho : ℂ)
      (xi_divisor_support_re_mem_open_unit rho).1).2.1,
    one_smul]

/--
The fixed comparison is pointwise nonerasing on every actual Xi divisor
point and every complete-resolution exponent.
-/
theorem deningerMeyerPointwiseXiComparison_nonzero_on_support
    (K : ℕ) (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin
        (deningerMeyerPointwiseXiComparison
          (completeResolutionSourceVector K (rho : ℂ)
            (xi_divisor_support_re_mem_open_unit rho).1))
        (rho : ℂ) ≠ 0 := by
  rw [deningerMeyerPointwiseXiComparison_completeSource]
  exact deningerMeyerXiAvoidingSource_nonzero_on_support rho

/-- The comparison annihilates every canonical reflection displacement. -/
theorem deningerMeyerPointwiseXiComparison_erases_reflection
    (K : ℕ) (s : CompleteResolutionOpenCriticalStrip) :
    deningerMeyerPointwiseXiComparison
        (completeResolutionReflectionSourceDisplacement K s) = 0 := by
  rw [deningerMeyerPointwiseXiComparison_apply,
    sourceFusionCodiagonal_completeResolutionReflectionSourceDisplacement,
    zero_smul]

/-- Vertical Sobolev cost is exactly homogeneous under complex scaling. -/
theorem deningerMeyerVerticalSobolevCost_smul
    (order : ℕ) (sigma : ℝ) (c : ℂ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerVerticalSobolevCost order sigma (c • g) =
      ‖c‖ * deningerMeyerVerticalSobolevCost order sigma g := by
  have hweighted :
      deningerMeyerWeightedLogProfile sigma
          (↑(c • g) : ℝ → ℂ) =
        c • deningerMeyerWeightedLogProfile sigma g := by
    funext t
    simp only [deningerMeyerWeightedLogProfile, Pi.smul_apply,
      smul_eq_mul]
    change
      (Real.exp (sigma * t) : ℂ) * (c * (g : ℝ → ℂ) t) =
        c * ((Real.exp (sigma * t) : ℂ) * (g : ℝ → ℂ) t)
    ring
  rw [deningerMeyerVerticalSobolevCost, hweighted]
  simp_rw [iteratedDeriv_const_smul_field, norm_smul]
  exact MeasureTheory.integral_const_mul _ _

/-- The rank-one pointwise-nonerasing comparison is uniformly regular. -/
theorem deningerMeyerPointwiseXiComparison_firstOrderRegular :
    DeningerMeyerCompleteSourceComparisonFirstOrderRegular
      deningerMeyerPointwiseXiComparison := by
  let C : ℝ :=
    ∫ t : ℝ,
      deningerMeyerVerticalMellinMajorant
        deningerMeyerXiAvoidingSource t
  have hC : 0 ≤ C := by
    apply integral_nonneg
    intro t
    exact
      mul_nonneg (Real.exp_pos _).le
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma0 hsigma1 x
  rw [deningerMeyerPointwiseXiComparison_apply,
    deningerMeyerVerticalSobolevCost_smul]
  have hcost :
      deningerMeyerVerticalSobolevCost 1 sigma
          deningerMeyerXiAvoidingSource ≤ C := by
    rw [deningerMeyerVerticalSobolevCost]
    apply integral_mono
    · simpa only [iteratedDeriv_one] using
        (integrable_deriv_deningerMeyerWeightedLogProfile
          deningerMeyerXiAvoidingSource.property sigma).norm
    · exact
        integrable_deningerMeyerVerticalMellinMajorant
          deningerMeyerXiAvoidingSource.property
    · intro t
      simpa only [iteratedDeriv_one] using
        norm_deriv_deningerMeyerWeightedLogProfile_le_majorant
          deningerMeyerXiAvoidingSource.property
          hsigma0 hsigma1 t
  calc
    ‖sourceFusionCodiagonal x‖ *
        deningerMeyerVerticalSobolevCost 1 sigma
          deningerMeyerXiAvoidingSource ≤
      ‖sourceFusionCodiagonal x‖ * C :=
        mul_le_mul_of_nonneg_left hcost (norm_nonneg _)
    _ ≤ ‖x‖ * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      simpa only [norm_sourceFusionCodiagonal_eq_one, one_mul] using
        sourceFusionCodiagonal.le_opNorm x
    _ = C * ‖x‖ := by ring

/-- The comparison treats all unit source labels identically. -/
theorem deningerMeyerPointwiseXiComparison_unitLabels_eq
    (i j : ℕ) :
    deningerMeyerPointwiseXiComparison
        (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) =
      deningerMeyerPointwiseXiComparison
        (lp.single (E := fun _ : ℕ => ℂ) 1 j 1) := by
  simp only [deningerMeyerPointwiseXiComparison_apply]
  rw [show
      sourceFusionCodiagonal
          (lp.single (E := fun _ : ℕ => ℂ) 1 i 1) = 1 by
        simp [sourceFusionCodiagonal, lp.tsumCLM_apply]]
  rw [show
      sourceFusionCodiagonal
          (lp.single (E := fun _ : ℕ => ℂ) 1 j 1) = 1 by
        simp [sourceFusionCodiagonal, lp.tsumCLM_apply]]

/--
On normalized actual sources the fixed comparison remains nonzero at every
finite Xi stage.
-/
theorem deningerMeyerPointwiseXiComparison_normalizedEscape_nonzero
    (K stage : ℕ) :
    deningerMeyerCompleteSourceXiEscapeTrace
        deningerMeyerPointwiseXiComparison K stage ≠ 0 := by
  let rho : XiDivisorSupport :=
    deningerMeyerXiVerticalEscape stage
  let x : CompleteResolutionSourceSpace :=
    completeResolutionSourceVector K (rho : ℂ)
      (xi_divisor_support_re_mem_open_unit rho).1
  have hx : x ≠ 0 :=
    completeResolutionSourceVector_ne_zero K
      (xi_divisor_support_re_mem_open_unit rho).1
  have hscalar : (((‖x‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hx)
  rw [deningerMeyerCompleteSourceXiEscapeTrace,
    completeResolutionXiEscapeUnitSource,
    complexUnitNormalization, map_smul]
  change
    deningerMeyerStrongLogMellin
        (((‖x‖⁻¹ : ℝ) : ℂ) •
          deningerMeyerPointwiseXiComparison x)
        (rho : ℂ) ≠ 0
  rw [deningerMeyerPointwiseXiComparison_completeSource]
  change
    (deningerMeyerStrongLogMellinLM (rho : ℂ))
        (((‖x‖⁻¹ : ℝ) : ℂ) •
          deningerMeyerXiAvoidingSource) ≠ 0
  rw [(deningerMeyerStrongLogMellinLM (rho : ℂ)).map_smul]
  exact
    smul_ne_zero hscalar
      (deningerMeyerXiAvoidingSource_nonzero_on_support rho)

/--
The same everywhere-nonzero normalized Xi trace converges to zero along the
actual escaping divisor sequence.
-/
theorem deningerMeyerPointwiseXiComparison_normalizedEscape_tendsto_zero
    (K : ℕ) :
    Tendsto
      (deningerMeyerCompleteSourceXiEscapeTrace
        deningerMeyerPointwiseXiComparison K)
      atTop (𝓝 0) :=
  deningerMeyerCompleteSourceXiEscapeTrace_tendsto_zero
    deningerMeyerPointwiseXiComparison
    deningerMeyerPointwiseXiComparison_firstOrderRegular K

end

end RHTower
