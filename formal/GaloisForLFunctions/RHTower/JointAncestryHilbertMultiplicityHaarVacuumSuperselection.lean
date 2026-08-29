import GaloisForLFunctions.RHTower.JointAncestryPrimePoissonHaarVacuumPowerDilationWall
import GaloisForLFunctions.HTGeometry.LpBoundedSmulMultiplier

/-!
# JAS Hilbert-multiplicity Haar-vacuum superselection

Arbitrary Hilbert multiplicity does not evade the prime-Poisson/Haar vacuum wall.  A unit vector
in the Hilbert-valued diagonal multiplication representation defines the scalar state measure
`‖v(x)‖² dμ`.  Complete Laurent moments force this measure to be product Haar, so Haar must be
absolutely continuous with respect to the ambient source measure.  Prime-Poisson singularity
therefore excludes the law on and left of the critical wall, in every Hilbert multiplicity.

Conversely, any scalar Haar vacuum embeds along a supplied unit Hilbert vector.  The resulting
criterion is sharp: the complete Haar vacuum power law exists exactly when `1 / 2 < sigma`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal InnerProductSpace NNReal

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertL2VectorStateDensity {μ : Measure X} (v : Lp H 2 μ) (x : X) : ℝ≥0 :=
  ‖(v : X → H) x‖₊ ^ 2

def hilbertL2VectorStateMeasure (μ : Measure X) (v : Lp H 2 μ) : Measure X :=
  μ.withDensity (fun x => (hilbertL2VectorStateDensity v x : ℝ≥0∞))

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem hilbertL2VectorStateMeasure_absolutelyContinuous
    (μ : Measure X) (v : Lp H 2 μ) :
    hilbertL2VectorStateMeasure μ v ≪ μ :=
  withDensity_absolutelyContinuous μ _

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem hilbertL2VectorStateMeasure_univ {μ : Measure X}
    (v : Lp H 2 μ) (hv : ‖v‖ = 1) :
    hilbertL2VectorStateMeasure μ v Set.univ = 1 := by
  rw [hilbertL2VectorStateMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have heLp : eLpNorm ((v : Lp H 2 μ) : X → H) 2 μ = 1 := by
    exact (ENNReal.toReal_eq_one_iff _).mp (by simpa only [Lp.norm_def] using hv)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at heLp
  norm_num at heLp
  apply ENNReal.rpow_left_injective (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simpa only [hilbertL2VectorStateDensity, ENNReal.coe_pow, enorm_eq_nnnorm,
    ENNReal.one_rpow] using heLp

def continuousHilbertL2Smul [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    (μ : Measure X) (f : C(X, ℂ)) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  lpBoundedSmulCLM (p := 2) (μ := μ) (H := H) f.continuous.measurable
    (norm_nonneg f) (fun x => f.norm_coe_le_norm x)

omit [CompleteSpace H] in
theorem continuousHilbertL2Smul_coeFn
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    (μ : Measure X) (f : C(X, ℂ)) (v : Lp H 2 μ) :
    ((continuousHilbertL2Smul (H := H) μ f v : Lp H 2 μ) : X → H) =ᵐ[μ]
      fun x => f x • (v : X → H) x :=
  lpBoundedSmulCLM_coeFn _ _ _ v

omit [CompleteSpace H] in
theorem integral_hilbertL2VectorStateMeasure_eq_inner
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) (v : Lp H 2 μ) :
    (∫ x, f x ∂hilbertL2VectorStateMeasure μ v) =
      inner ℂ v (continuousHilbertL2Smul (H := H) μ f v) := by
  rw [hilbertL2VectorStateMeasure]
  simp only [hilbertL2VectorStateDensity]
  rw [integral_withDensity_eq_integral_smul₀
      ((Lp.aestronglyMeasurable v).nnnorm.aemeasurable.pow_const 2) f,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousHilbertL2Smul_coeFn (H := H) μ f v] with x hx
  rw [hx, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_pow, coe_nnnorm]
  push_cast
  exact mul_comm _ _

def scalarToUnitVectorIsometry (e : H) (he : ‖e‖ = 1) : ℂ →ₗᵢ[ℂ] H where
  toFun c := c • e
  map_add' a b := add_smul a b e
  map_smul' a b := by simp [smul_smul]
  norm_map' c := by
    change ‖c • e‖ = ‖c‖
    rw [norm_smul, he, mul_one]

def lpUnitVectorEmbedding (μ : Measure X) (e : H) (he : ‖e‖ = 1) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp H 2 μ where
  toLinearMap :=
    ((scalarToUnitVectorIsometry e he).toContinuousLinearMap.compLpL 2 μ).toLinearMap
  norm_map' v := by
    change ‖(scalarToUnitVectorIsometry e he).toContinuousLinearMap.compLp v‖ = ‖v‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [(scalarToUnitVectorIsometry e he).toContinuousLinearMap.coeFn_compLp v]
      with x hx
    rw [hx]
    change ‖(scalarToUnitVectorIsometry e he) ((v : X → ℂ) x)‖ = ‖(v : X → ℂ) x‖
    exact (scalarToUnitVectorIsometry e he).norm_map _

omit [CompleteSpace H] in
theorem lpUnitVectorEmbedding_continuousL2Mul
    [TopologicalSpace X] [CompactSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (e : H) (he : ‖e‖ = 1)
    (f : C(X, ℂ)) (v : Lp ℂ 2 μ) :
    lpUnitVectorEmbedding μ e he (continuousL2Mul μ f v) =
      continuousHilbertL2Smul (H := H) μ f (lpUnitVectorEmbedding μ e he v) := by
  change (scalarToUnitVectorIsometry e he).toContinuousLinearMap.compLp
      (continuousL2Mul μ f v) =
    continuousHilbertL2Smul (H := H) μ f
      ((scalarToUnitVectorIsometry e he).toContinuousLinearMap.compLp v)
  apply Lp.ext
  filter_upwards [
    (scalarToUnitVectorIsometry e he).toContinuousLinearMap.coeFn_compLp
      (continuousL2Mul μ f v),
    continuousL2Mul_coeFn μ f v,
    continuousHilbertL2Smul_coeFn (H := H) μ f
      ((scalarToUnitVectorIsometry e he).toContinuousLinearMap.compLp v),
    (scalarToUnitVectorIsometry e he).toContinuousLinearMap.coeFn_compLp v]
      with x hleft hmul hright hv
  rw [hleft, hmul, hright, hv]
  change (f x * (v : X → ℂ) x) • e = f x • ((v : X → ℂ) x • e)
  rw [mul_smul]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem isProbabilityMeasure_hilbertL2VectorStateMeasure {μ : Measure X}
    (v : Lp H 2 μ) (hv : ‖v‖ = 1) :
    IsProbabilityMeasure (hilbertL2VectorStateMeasure μ v) :=
  ⟨hilbertL2VectorStateMeasure_univ v hv⟩

def hilbertL2VectorStateProbabilityMeasure
    (μ : Measure X) (v : Lp H 2 μ) (hv : ‖v‖ = 1) : ProbabilityMeasure X :=
  ⟨hilbertL2VectorStateMeasure μ v,
    isProbabilityMeasure_hilbertL2VectorStateMeasure v hv⟩

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] theorem hilbertL2VectorStateProbabilityMeasure_toMeasure
    (μ : Measure X) (v : Lp H 2 μ) (hv : ‖v‖ = 1) :
    (hilbertL2VectorStateProbabilityMeasure μ v hv : Measure X) =
      hilbertL2VectorStateMeasure μ v := rfl

/-- Complete mixed Laurent vacuum law in an arbitrary Hilbert-multiplicity diagonal
multiplication representation. -/
def HasHilbertHaarVacuumPowerLaw
    {I : Type*} [Countable I]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ] : Prop :=
  ∃ v : Lp H 2 μ, ‖v‖ = 1 ∧ ∀ n : I →₀ ℤ,
    inner ℂ v
        (continuousHilbertL2Smul (H := H) μ (infiniteTorusFourier n) v) =
      ∫ x, infiniteTorusFourier n x ∂torusHaar I

/-- Arbitrary Hilbert multiplicity cannot hide measure class: a Haar-vacuum power vector forces
product Haar to be dominated by ambient multiplication measure. -/
theorem torusHaar_absolutelyContinuous_of_hasHilbertHaarVacuumPowerLaw
    {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (h : HasHilbertHaarVacuumPowerLaw H μ) :
    torusHaar I ≪ μ := by
  rcases h with ⟨v, hv, hpower⟩
  let ρ : ProbabilityMeasure (I → UnitAddCircle) :=
    hilbertL2VectorStateProbabilityMeasure μ v hv
  let m : ProbabilityMeasure (I → UnitAddCircle) :=
    ⟨torusHaar I, torusHaar_isProbabilityMeasure I⟩
  have hρm : ρ = m :=
    probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq ρ m (by
      intro n
      change (∫ x, infiniteTorusFourier n x ∂hilbertL2VectorStateMeasure μ v) =
        ∫ x, infiniteTorusFourier n x ∂torusHaar I
      rw [integral_hilbertL2VectorStateMeasure_eq_inner]
      exact hpower n)
  have hmeasure : hilbertL2VectorStateMeasure μ v = torusHaar I := by
    have := congrArg ProbabilityMeasure.toMeasure hρm
    change hilbertL2VectorStateMeasure μ v = torusHaar I at this
    exact this
  rw [← hmeasure]
  exact hilbertL2VectorStateMeasure_absolutelyContinuous μ v

theorem not_hasHilbertHaarVacuumPowerLaw_of_mutuallySingular
    {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (hsing : μ ⟂ₘ torusHaar I) :
    ¬ HasHilbertHaarVacuumPowerLaw H μ := by
  intro hvac
  have hac : torusHaar I ≪ μ :=
    torusHaar_absolutelyContinuous_of_hasHilbertHaarVacuumPowerLaw μ hvac
  rcases hsing with ⟨s, hs, hμs, hhaarComp⟩
  have hhaarS : torusHaar I s = 0 := hac hμs
  have hzero : torusHaar I Set.univ = 0 := by
    rw [← Set.union_compl_self s,
      measure_union disjoint_compl_right hs.compl, hhaarS, hhaarComp, zero_add]
  have hone : torusHaar I Set.univ = 1 := IsProbabilityMeasure.measure_univ
  rw [hone] at hzero
  exact one_ne_zero hzero

theorem not_hasHilbertHaarVacuumPowerLaw_primePoisson_of_le_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hwall : sigma ≤ 1 / 2) :
    ¬ HasHilbertHaarVacuumPowerLaw H (primePoissonMeasure sigma t hsigma) :=
  not_hasHilbertHaarVacuumPowerLaw_of_mutuallySingular _
    (primePoissonMeasure_mutuallySingular_torusHaar_of_le_half
      sigma t hsigma hwall)

/-- Embed any scalar Haar-vacuum power law along a unit vector into arbitrary Hilbert
multiplicity. -/
theorem hasHilbertHaarVacuumPowerLaw_of_hasExactHaarVacuumPowerLaw
    {I : Type*} [Countable I]
    (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (e : H) (he : ‖e‖ = 1) (h : HasExactHaarVacuumPowerLaw μ) :
    HasHilbertHaarVacuumPowerLaw H μ := by
  rcases h with ⟨v, hv, hpower⟩
  let E := lpUnitVectorEmbedding μ e he
  refine ⟨E v, ?_, ?_⟩
  · rw [E.norm_map, hv]
  · intro n
    rw [← lpUnitVectorEmbedding_continuousL2Mul μ e he]
    exact (E.inner_map_map v
      (continuousL2Mul μ (infiniteTorusFourier n) v)).trans (hpower n)

/-- **Arbitrary Hilbert-multiplicity JAS wall.**  For every complex Hilbert target carrying a unit
vector, no amount or cardinality of diagonal source-channel multiplicity moves the exact Haar
vacuum power law through the critical wall. -/
theorem primePoisson_hasHilbertHaarVacuumPowerLaw_iff
    (e : H) (he : ‖e‖ = 1) (sigma t : ℝ) (hsigma : 0 < sigma) :
    HasHilbertHaarVacuumPowerLaw H (primePoissonMeasure sigma t hsigma) ↔
      1 / 2 < sigma := by
  constructor
  · intro hvac
    by_contra hright
    exact (not_hasHilbertHaarVacuumPowerLaw_primePoisson_of_le_half
      (H := H) sigma t hsigma (le_of_not_gt hright)) hvac
  · intro hright
    exact hasHilbertHaarVacuumPowerLaw_of_hasExactHaarVacuumPowerLaw
      (primePoissonMeasure sigma t hsigma) e he
      ((primePoisson_hasExactHaarVacuumPowerLaw_iff sigma t hsigma).mpr hright)

end

end GaloisForLFunctions.HTGeometry
