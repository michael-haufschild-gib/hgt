import GaloisForLFunctions.RHTower.JointAncestryHaarBilateralDilationSourceSuperselection

/-!
# JAS prime-Poisson Haar-vacuum power-dilation wall

An exact bilateral power dilation of commuting flat Boolean creators has product-Haar vacuum
moments: every nontrivial finite mixed Laurent word has vacuum coefficient zero.  The literal JAS
source, however, is the prime-Poisson multiplication representation.

This module proves the sharp classification.  A normalized vector in prime-Poisson `L²` has the
complete product-Haar Laurent law if and only if `1 / 2 < sigma`.  On and left of the critical
wall, the vector-state measure is dominated by prime-Poisson while Fourier tomography would force
it to equal Haar, contradicting corpus singularity.  To the right, the repaired Radon--Nikodym
half-density unitary explicitly transports the constant Haar vacuum into prime-Poisson `L²`.

Thus an unweighted Haar bilateral power dilation cannot be implemented inside the literal source
at the critical wall.  A surviving JAS completion must retain the prime-Poisson measure class or
replace exact power dilation by a genuinely different orientation mechanism.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Squared pointwise norm of an `L²` vector. -/
def l2VectorStateDensity {μ : Measure X} (v : Lp ℂ 2 μ) (x : X) : ℝ≥0 :=
  ‖(v : X → ℂ) x‖₊ ^ 2

/-- Spectral measure of an `L²` vector in the multiplication representation. -/
def l2VectorStateMeasure (μ : Measure X) (v : Lp ℂ 2 μ) : Measure X :=
  μ.withDensity (fun x => (l2VectorStateDensity v x : ℝ≥0∞))

theorem l2VectorStateMeasure_absolutelyContinuous (μ : Measure X) (v : Lp ℂ 2 μ) :
    l2VectorStateMeasure μ v ≪ μ :=
  withDensity_absolutelyContinuous μ _

theorem l2VectorStateMeasure_univ {μ : Measure X} (v : Lp ℂ 2 μ) (hv : ‖v‖ = 1) :
    l2VectorStateMeasure μ v Set.univ = 1 := by
  rw [l2VectorStateMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have heLp : eLpNorm ((v : Lp ℂ 2 μ) : X → ℂ) 2 μ = 1 := by
    exact (ENNReal.toReal_eq_one_iff _).mp (by simpa only [Lp.norm_def] using hv)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at heLp
  norm_num at heLp
  apply ENNReal.rpow_left_injective (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simpa only [l2VectorStateDensity, ENNReal.coe_pow, enorm_eq_nnnorm,
    ENNReal.one_rpow] using heLp

theorem isProbabilityMeasure_l2VectorStateMeasure {μ : Measure X}
    (v : Lp ℂ 2 μ) (hv : ‖v‖ = 1) :
    IsProbabilityMeasure (l2VectorStateMeasure μ v) :=
  ⟨l2VectorStateMeasure_univ v hv⟩

/-- Bundled vector-state probability measure. -/
def l2VectorStateProbabilityMeasure (μ : Measure X) (v : Lp ℂ 2 μ) (hv : ‖v‖ = 1) :
    ProbabilityMeasure X :=
  ⟨l2VectorStateMeasure μ v, isProbabilityMeasure_l2VectorStateMeasure v hv⟩

@[simp] theorem l2VectorStateProbabilityMeasure_toMeasure
    (μ : Measure X) (v : Lp ℂ 2 μ) (hv : ‖v‖ = 1) :
    (l2VectorStateProbabilityMeasure μ v hv : Measure X) = l2VectorStateMeasure μ v := rfl

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

/-- Integrating a continuous observable against a vector-state measure is its multiplication
operator vacuum matrix coefficient. -/
theorem integral_l2VectorStateMeasure_eq_inner (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) (v : Lp ℂ 2 μ) :
    (∫ x, f x ∂l2VectorStateMeasure μ v) =
      inner ℂ v (continuousL2Mul μ f v) := by
  rw [l2VectorStateMeasure]
  simp only [l2VectorStateDensity]
  rw [integral_withDensity_eq_integral_smul₀
      ((Lp.aestronglyMeasurable v).nnnorm.aemeasurable.pow_const 2) f,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousL2Mul_coeFn μ f v] with x hx
  rw [hx, RCLike.inner_apply]
  simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_pow, coe_nnnorm]
  rw [mul_comm, mul_assoc]
  congr 1
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm _

/-- A literal multiplication representation contains a normalized vector whose complete Laurent
spectral law is product Haar. -/
def HasHaarVacuumVector {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) : Prop :=
  ∃ v : Lp ℂ 2 μ, ‖v‖ = 1 ∧ ∀ n : I →₀ ℤ,
    (∫ x, infiniteTorusFourier n x ∂l2VectorStateMeasure μ v) =
      ∫ x, infiniteTorusFourier n x ∂torusHaar I

/-- Fourier tomography turns a Haar-vacuum vector into domination of Haar by the ambient
multiplication measure. -/
theorem torusHaar_absolutelyContinuous_of_hasHaarVacuumVector
    {I : Type*} [Countable I] (μ : Measure (I → UnitAddCircle))
    (h : HasHaarVacuumVector μ) :
    torusHaar I ≪ μ := by
  rcases h with ⟨v, hv, hmom⟩
  let ρ : ProbabilityMeasure (I → UnitAddCircle) :=
    l2VectorStateProbabilityMeasure μ v hv
  let m : ProbabilityMeasure (I → UnitAddCircle) :=
    ⟨torusHaar I, torusHaar_isProbabilityMeasure I⟩
  have hρm : ρ = m :=
    probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq ρ m (by
      intro n
      change (∫ x, infiniteTorusFourier n x ∂l2VectorStateMeasure μ v) =
        ∫ x, infiniteTorusFourier n x ∂torusHaar I
      exact hmom n)
  have hmeasure : l2VectorStateMeasure μ v = torusHaar I := by
    have := congrArg ProbabilityMeasure.toMeasure hρm
    change l2VectorStateMeasure μ v = torusHaar I at this
    exact this
  rw [← hmeasure]
  exact l2VectorStateMeasure_absolutelyContinuous μ v

/-- A measure singular to product Haar cannot carry a Haar-vacuum vector. -/
theorem not_hasHaarVacuumVector_of_mutuallySingular
    {I : Type*} [Countable I] (μ : Measure (I → UnitAddCircle))
    (hsing : μ ⟂ₘ torusHaar I) :
    ¬ HasHaarVacuumVector μ := by
  intro hvac
  have hac : torusHaar I ≪ μ :=
    torusHaar_absolutelyContinuous_of_hasHaarVacuumVector μ hvac
  rcases hsing with ⟨s, hs, hμs, hhaarComp⟩
  have hhaarS : torusHaar I s = 0 := hac hμs
  have hzero : torusHaar I Set.univ = 0 := by
    rw [← Set.union_compl_self s,
      measure_union disjoint_compl_right hs.compl, hhaarS, hhaarComp, zero_add]
  have hone : torusHaar I Set.univ = 1 := IsProbabilityMeasure.measure_univ
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- On and left of the critical wall, the literal prime-Poisson multiplication source has no
normalized vector with the complete Haar Laurent law. -/
theorem not_hasHaarVacuumVector_primePoisson_of_le_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hwall : sigma ≤ 1 / 2) :
    ¬ HasHaarVacuumVector (primePoissonMeasure sigma t hsigma) :=
  not_hasHaarVacuumVector_of_mutuallySingular _
    (primePoissonMeasure_mutuallySingular_torusHaar_of_le_half
      sigma t hsigma hwall)

/-- Constant unit vector in product-Haar `L²`. -/
def torusHaarVacuum (I : Type*) [Countable I] : Lp ℂ 2 (torusHaar I) :=
  ContinuousMap.toLp 2 (torusHaar I) ℂ (1 : C(I → UnitAddCircle, ℂ))

theorem norm_torusHaarVacuum (I : Type*) [Countable I] :
    ‖torusHaarVacuum I‖ = 1 := by
  have hsq : ‖torusHaarVacuum I‖ ^ 2 = 1 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hcoe : (((torusHaarVacuum I : Lp ℂ 2 (torusHaar I)) :
        (I → UnitAddCircle) → ℂ)) =ᵐ[torusHaar I] fun _ => (1 : ℂ) := by
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (torusHaar I)
        (1 : C(I → UnitAddCircle, ℂ))] with x hx
      simpa [torusHaarVacuum] using hx
    calc
      (∫ x, ‖((torusHaarVacuum I : Lp ℂ 2 (torusHaar I)) :
          (I → UnitAddCircle) → ℂ) x‖ ^ 2 ∂torusHaar I) =
          ∫ _x : I → UnitAddCircle, (1 : ℝ) ∂torusHaar I := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx]
        norm_num
      _ = 1 := by simp
  nlinarith [norm_nonneg (torusHaarVacuum I)]

theorem inner_torusHaarVacuum_continuousL2Mul
    {I : Type*} [Countable I] (f : C(I → UnitAddCircle, ℂ)) :
    inner ℂ (torusHaarVacuum I)
        (continuousL2Mul (torusHaar I) f (torusHaarVacuum I)) =
      ∫ x, f x ∂torusHaar I := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousL2Mul_coeFn (torusHaar I) f (torusHaarVacuum I),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (torusHaar I)
      (1 : C(I → UnitAddCircle, ℂ))] with x hmul hone
  rw [hmul]
  change inner ℂ (((torusHaarVacuum I : Lp ℂ 2 (torusHaar I)) :
      (I → UnitAddCircle) → ℂ) x) (f x *
        (((torusHaarVacuum I : Lp ℂ 2 (torusHaar I)) :
          (I → UnitAddCircle) → ℂ) x)) = f x
  rw [show (((torusHaarVacuum I : Lp ℂ 2 (torusHaar I)) :
      (I → UnitAddCircle) → ℂ) x) = 1 by simpa [torusHaarVacuum] using hone]
  simp

/-- An exact positive-density presentation of a measure over product Haar transports the Haar
vacuum into its `L²` multiplication representation. -/
theorem hasHaarVacuumVector_of_withDensity_eq
    {I : Type*} [Countable I]
    (w : (I → UnitAddCircle) → ℝ) (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (hmeasure : (torusHaar I).withDensity (realDensity w) = μ) :
    HasHaarVacuumVector μ := by
  subst μ
  let U := weightedDensityUnitary (μ := torusHaar I) w hw hpos
  let v : WeightedL2 (μ := torusHaar I) w := U.symm (torusHaarVacuum I)
  refine ⟨v, ?_, ?_⟩
  · change ‖U.symm (torusHaarVacuum I)‖ = 1
    rw [U.symm.norm_map, norm_torusHaarVacuum]
  · intro n
    rw [integral_l2VectorStateMeasure_eq_inner]
    rw [← U.inner_map_map]
    change inner ℂ (U v)
      (U (continuousL2Mul ((torusHaar I).withDensity (realDensity w))
        (infiniteTorusFourier n) v)) = _
    rw [weightedDensityUnitary_continuousL2Mul]
    have hUv : U v = torusHaarVacuum I := by simp [v]
    rw [hUv]
    change inner ℂ (torusHaarVacuum I)
      (continuousL2Mul (torusHaar I) (infiniteTorusFourier n)
        (torusHaarVacuum I)) = _
    exact inner_torusHaarVacuum_continuousL2Mul (infiniteTorusFourier n)

/-- Any finite measure equivalent to product Haar contains an exact Haar-vacuum vector, explicitly
transported by the repaired Radon--Nikodym half-density. -/
theorem hasHaarVacuumVector_of_mutuallyAbsolutelyContinuous_torusHaar
    {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (hμ : μ ≪ torusHaar I) (hhaar : torusHaar I ≪ μ) :
    HasHaarVacuumVector μ := by
  let w : (I → UnitAddCircle) → ℝ := repairedRnDensity μ (torusHaar I)
  have hw : Measurable w := measurable_repairedRnDensity μ (torusHaar I)
  have hpos : ∀ x, 0 < w x := repairedRnDensity_pos μ (torusHaar I)
  have hmeasure : (torusHaar I).withDensity (realDensity w) = μ :=
    withDensity_repairedRnDensity_eq μ (torusHaar I) hμ hhaar
  exact hasHaarVacuumVector_of_withDensity_eq w hw hpos μ hmeasure

/-- **Sharp prime-Poisson Haar-vacuum threshold.**  The literal prime-Poisson multiplication
source contains a normalized vector with every product-Haar Laurent moment exactly when the source
lies in the open right half-plane. -/
theorem primePoisson_hasHaarVacuumVector_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    HasHaarVacuumVector (primePoissonMeasure sigma t hsigma) ↔
      1 / 2 < sigma := by
  constructor
  · intro hvac
    by_contra hright
    exact (not_hasHaarVacuumVector_primePoisson_of_le_half
      sigma t hsigma (le_of_not_gt hright)) hvac
  · intro hright
    have hmac := (primePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
      sigma t hsigma).mpr hright
    exact hasHaarVacuumVector_of_mutuallyAbsolutelyContinuous_torusHaar
      (primePoissonMeasure sigma t hsigma) hmac.1 hmac.2

theorem integral_infiniteTorusFourier_torusHaar_eq_ite
    {I : Type*} [Countable I] [DecidableEq I] (n : I →₀ ℤ) :
    (∫ x, infiniteTorusFourier n x ∂torusHaar I) =
      if n = 0 then 1 else 0 := by
  classical
  have hchar : infiniteTorusFourier n = torusCharacter n := by
    ext x
    simp only [infiniteTorusFourier, torusCharacter_apply, ContinuousMap.coe_mk]
    rw [Finsupp.prod]
  rw [hchar, integral_torusCharacter]

/-- Operator-language exact bilateral vacuum law: every finite mixed Laurent word has the product
Haar vacuum coefficient.  This is the moment law forced by an exact power dilation of commuting
flat Boolean creators. -/
def HasExactHaarVacuumPowerLaw {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ] : Prop :=
  ∃ v : Lp ℂ 2 μ, ‖v‖ = 1 ∧ ∀ n : I →₀ ℤ,
    inner ℂ v (continuousL2Mul μ (infiniteTorusFourier n) v) =
      ∫ x, infiniteTorusFourier n x ∂torusHaar I

theorem hasExactHaarVacuumPowerLaw_iff_hasHaarVacuumVector
    {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ] :
    HasExactHaarVacuumPowerLaw μ ↔ HasHaarVacuumVector μ := by
  constructor
  · rintro ⟨v, hv, hpower⟩
    refine ⟨v, hv, ?_⟩
    intro n
    rw [integral_l2VectorStateMeasure_eq_inner]
    exact hpower n
  · rintro ⟨v, hv, hmom⟩
    refine ⟨v, hv, ?_⟩
    intro n
    rw [← integral_l2VectorStateMeasure_eq_inner]
    exact hmom n

/-- **Exact Boolean-bilateral vacuum power-dilation wall.**  The literal prime-Poisson source
supports the complete mixed Laurent vacuum law of a flat Boolean creator family exactly in the
open right half-plane, never at the critical wall. -/
theorem primePoisson_hasExactHaarVacuumPowerLaw_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    HasExactHaarVacuumPowerLaw (primePoissonMeasure sigma t hsigma) ↔
      1 / 2 < sigma := by
  rw [hasExactHaarVacuumPowerLaw_iff_hasHaarVacuumVector,
    primePoisson_hasHaarVacuumVector_iff]

end

end GaloisForLFunctions.HTGeometry
