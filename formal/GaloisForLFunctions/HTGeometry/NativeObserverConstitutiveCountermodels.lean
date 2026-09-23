import GaloisForLFunctions.HTGeometry.FramedTwoBoundaryPhaseFibreHistorySeparation
import GaloisForLFunctions.HTGeometry.RestrictedHistoryHurwitzRankCountermodels
import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionAnalyticLaw

/-!
# Five exact constitutive non-determination witnesses
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### 1. Same observer, different exact winding cost -/

/-- Strictly positive real parameters, carrying positivity as data rather than theorem premises. -/
private abbrev PositiveReal := {x : ℝ // 0 < x}

/-- Unit relative winding in the two-phase presentation of a circle fibre. -/
def nativeCircleUnitWinding : Fin 2 → ℤ := ![1, -1]

theorem nativeCircleUnitWinding_projectedNormSq :
    framedWindingProjectedNormSq nativeCircleUnitWinding = 2 := by
  norm_num [nativeCircleUnitWinding, framedWindingProjectedNormSq, framedPhaseNormSq,
    framedPhaseProjection, framedPhaseMean, Fin.sum_univ_two]

/-- Metric-scaled action spectrum of the same unit-winding fibre and same terminal observer. -/
def nativeCircleScaledActionValues (lam T : PositiveReal) : Set ℝ :=
  Set.range fun history : FramedCoverHistory 2 (T : ℝ)
      (framedWindingDisplacement nativeCircleUnitWinding) =>
    (lam : ℝ) ^ (2 : ℕ) * framedCoverAction 2 T history.path

/-- Exact same-observer unit-winding minimum `2π²λ²/T`. -/
theorem nativeCircleScaledAction_has_exactMinimum (lam T : PositiveReal) :
    IsLeast (nativeCircleScaledActionValues lam T)
      (2 * Real.pi ^ (2 : ℕ) * (lam : ℝ) ^ (2 : ℕ) / (T : ℝ)) := by
  have hbase := framedWindingAction_has_exactMinimum (by norm_num : 0 < 2) T.2
    nativeCircleUnitWinding
  have hformula : framedWindingMinimumAction (T : ℝ) nativeCircleUnitWinding =
      2 * Real.pi ^ (2 : ℕ) / (T : ℝ) := by
    rw [framedWindingMinimumAction, nativeCircleUnitWinding_projectedNormSq]
    norm_num
    ring
  rw [hformula] at hbase
  constructor
  · rcases hbase.1 with ⟨history, hhistory⟩
    refine ⟨history, ?_⟩
    change framedCoverAction 2 T history.path = 2 * Real.pi ^ (2 : ℕ) / (T : ℝ) at hhistory
    change (lam : ℝ) ^ (2 : ℕ) * framedCoverAction 2 T history.path =
      2 * Real.pi ^ (2 : ℕ) * (lam : ℝ) ^ (2 : ℕ) / (T : ℝ)
    rw [hhistory]
    ring
  · rintro y ⟨history, rfl⟩
    have hle := hbase.2 ⟨history, rfl⟩
    have hscale : 0 ≤ (lam : ℝ) ^ (2 : ℕ) := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hle hscale
    calc
      2 * Real.pi ^ (2 : ℕ) * (lam : ℝ) ^ (2 : ℕ) / (T : ℝ) =
          (lam : ℝ) ^ (2 : ℕ) * (2 * Real.pi ^ (2 : ℕ) / (T : ℝ)) := by ring
      _ ≤ (lam : ℝ) ^ (2 : ℕ) * framedCoverAction 2 T history.path := this

/-- Concrete scale-one and scale-two metrics have identical observer data but different minima. -/
theorem nativeCircle_sameObserver_differentCost :
    let one : PositiveReal := ⟨1, by norm_num⟩
    let two : PositiveReal := ⟨2, by norm_num⟩
    let T : PositiveReal := ⟨1, by norm_num⟩
    IsLeast (nativeCircleScaledActionValues one T) (2 * Real.pi ^ (2 : ℕ)) ∧
      IsLeast (nativeCircleScaledActionValues two T) (8 * Real.pi ^ (2 : ℕ)) ∧
      (2 * Real.pi ^ (2 : ℕ) : ℝ) ≠ 8 * Real.pi ^ (2 : ℕ) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · convert nativeCircleScaledAction_has_exactMinimum ⟨1, by norm_num⟩ ⟨1, by norm_num⟩ using 1
    all_goals norm_num
  · convert nativeCircleScaledAction_has_exactMinimum ⟨2, by norm_num⟩ ⟨1, by norm_num⟩ using 1
    all_goals ring
  · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    nlinarith [sq_pos_of_ne_zero hpi]

/-! ### 2. Same projection, three inertia phases -/

/-- Fixed one-port observer `q(x,y)=x`. -/
def nativeInertiaObserver : ℝ × ℝ → ℝ := Prod.fst

/-- Family `Q_σ(x,y)=y²+σx²`. -/
def nativeInertiaForm (σ : ℝ) (v : ℝ × ℝ) : ℝ := v.2 ^ (2 : ℕ) + σ * v.1 ^ (2 : ℕ)

theorem nativeInertiaForm_positiveOnKernel (σ : ℝ) (v : ℝ × ℝ)
    (hv : nativeInertiaObserver v = 0) (hne : v ≠ 0) :
    0 < nativeInertiaForm σ v := by
  have hx : v.1 = 0 := hv
  have hy : v.2 ≠ 0 := by
    intro hy
    apply hne
    exact Prod.ext hx hy
  simp [nativeInertiaForm, hx, sq_pos_of_ne_zero hy]

theorem nativeInertiaForm_one_posDef (v : ℝ × ℝ) (hne : v ≠ 0) :
    0 < nativeInertiaForm 1 v := by
  by_cases hx : v.1 = 0
  · have hy : v.2 ≠ 0 := by
      intro hy
      exact hne (Prod.ext hx hy)
    simp [nativeInertiaForm, hx, sq_pos_of_ne_zero hy]
  · have hxpos : 0 < v.1 ^ (2 : ℕ) := sq_pos_of_ne_zero hx
    have hy_nonneg : 0 ≤ v.2 ^ (2 : ℕ) := sq_nonneg _
    norm_num [nativeInertiaForm]
    linarith

theorem nativeInertiaForm_zero_iff (v : ℝ × ℝ) :
    nativeInertiaForm 0 v = 0 ↔ v.2 = 0 := by
  simp [nativeInertiaForm]

theorem nativeInertiaForm_negOne_lorentzian :
    nativeInertiaForm (-1) (0, 1) > 0 ∧ nativeInertiaForm (-1) (1, 0) < 0 := by
  norm_num [nativeInertiaForm]

/-- The fixed observer and vertical positivity coexist with positive-definite, corank-one, and
Lorentzian constitutive phases. -/
theorem nativeObserver_does_not_determine_inertia :
    (∀ v, v ≠ 0 → 0 < nativeInertiaForm 1 v) ∧
      (∀ v, nativeInertiaForm 0 v = 0 ↔ v.2 = 0) ∧
      (nativeInertiaForm (-1) (0, 1) > 0 ∧ nativeInertiaForm (-1) (1, 0) < 0) ∧
      (∀ σ v, nativeInertiaObserver v = 0 → v ≠ 0 → 0 < nativeInertiaForm σ v) := by
  exact ⟨nativeInertiaForm_one_posDef, nativeInertiaForm_zero_iff,
    nativeInertiaForm_negOne_lorentzian, nativeInertiaForm_positiveOnKernel⟩

/-! ### 3. Same scalar monodromy, DA versus Hurwitz hypertranscendence -/

/-- Exponent used by the corpus's explicit monodromy-two Hurwitz family. -/
def nativePowerExponent : ℂ := hurwitzTwoTwoExponents 0

/-- Differentially algebraic scalar power on the logarithmic cover. -/
def nativeScalarPowerHistory (z : ℂ) : ℂ := Complex.exp (-nativePowerExponent * z)

theorem nativeScalarPowerHistory_translation (z : ℂ) :
    nativeScalarPowerHistory (z + 2 * Real.pi * Complex.I) =
      2 * nativeScalarPowerHistory z := by
  calc
    nativeScalarPowerHistory (z + 2 * Real.pi * Complex.I) =
        Complex.exp (-nativePowerExponent * z) *
          Complex.exp (-(2 * Real.pi * Complex.I * nativePowerExponent)) := by
            rw [nativeScalarPowerHistory]
            have heq : -nativePowerExponent * (z + 2 * Real.pi * Complex.I) =
                -nativePowerExponent * z +
                  -(2 * Real.pi * Complex.I * nativePowerExponent) := by ring
            rw [heq, Complex.exp_add]
    _ = nativeScalarPowerHistory z * HurwitzOrbit.monoScalar nativePowerExponent := by
          rfl
    _ = 2 * nativeScalarPowerHistory z := by
          rw [nativePowerExponent, hurwitzTwoTwoExponents_monoScalar]
          ring

theorem hasDerivAt_nativeScalarPowerHistory (z : ℂ) :
    HasDerivAt nativeScalarPowerHistory
      (-nativePowerExponent * nativeScalarPowerHistory z) z := by
  unfold nativeScalarPowerHistory
  have hlin : HasDerivAt (fun x : ℂ => -nativePowerExponent * x)
      (-nativePowerExponent) z := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id z).const_mul (-nativePowerExponent)
  simpa only [mul_one, mul_comm] using hlin.cexp

theorem nativeScalarPowerHistory_linearODE (z : ℂ) :
    deriv nativeScalarPowerHistory z + nativePowerExponent * nativeScalarPowerHistory z = 0 := by
  rw [(hasDerivAt_nativeScalarPowerHistory z).deriv]
  ring

/-- The exact same scalar character `2` labels a first-order exponential and a differentially
independent Hurwitz function. -/
theorem nativeCharacterObserver_does_not_determine_DA :
    HurwitzOrbit.monoScalar nativePowerExponent = 2 ∧
      (∀ z, nativeScalarPowerHistory (z + 2 * Real.pi * Complex.I) =
        2 * nativeScalarPowerHistory z) ∧
      (∀ z, deriv nativeScalarPowerHistory z +
        nativePowerExponent * nativeScalarPowerHistory z = 0) ∧
      (letI := isDomain_upperEndAnalyticSubring
       letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
       letI := upperEndMeroFieldDifferential
       DifferentialIndependent (RatFunc ℂ)
        (fun _ : Fin 1 => HurwitzJointLadder.hzetaUpperEndMero
          (hurwitzTwoTwoExponents 0) (hurwitzTwoTwoExponents_gt_one 0))) := by
  exact ⟨hurwitzTwoTwoExponents_monoScalar 0, nativeScalarPowerHistory_translation,
    nativeScalarPowerHistory_linearODE,
    hurwitzTwoTwoExponents_each_differentialIndependent 0⟩

/-! ### 4. Forgetting topology loses effectivity -/

/-- A second copy of the reals carrying discrete topology. -/
def DiscreteReal := ℝ

instance : TopologicalSpace DiscreteReal := ⊥
instance : DiscreteTopology DiscreteReal := ⟨rfl⟩

/-- Identity on underlying sets, from discrete to usual topology. -/
def discreteRealToReal (x : DiscreteReal) : ℝ := x

theorem discreteRealToReal_continuous : Continuous discreteRealToReal :=
  continuous_of_discreteTopology

theorem discreteRealToReal_bijective : Function.Bijective discreteRealToReal := by
  constructor <;> intro x
  · exact fun y h => h
  · exact ⟨x, rfl⟩

theorem real_singleton_zero_not_open : ¬ IsOpen ({0} : Set ℝ) := by
  intro h
  rcases (Metric.isOpen_iff.mp h 0 (by simp)) with ⟨ε, hε, hball⟩
  have hhalf : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hz := hball hhalf
  simp only [Set.mem_singleton_iff] at hz
  linarith

theorem discreteRealToReal_not_isHomeomorph : ¬ IsHomeomorph discreteRealToReal := by
  intro h
  let zeroD : DiscreteReal := (0 : ℝ)
  have hopenDiscrete : IsOpen ({zeroD} : Set DiscreteReal) := isOpen_discrete _
  have hopenImage := h.isOpenMap _ hopenDiscrete
  have himage : discreteRealToReal '' {zeroD} = ({0} : Set ℝ) := by
    ext x
    simp [zeroD, discreteRealToReal]
  rw [himage] at hopenImage
  exact real_singleton_zero_not_open hopenImage

/-- Same underlying bijection and Set-level Cech relation, but usual-to-usual identity is a
homeomorphism while the discrete-to-usual lift is not. -/
theorem forgottenSetObserver_does_not_determine_topologicalEffectivity :
    Function.Bijective discreteRealToReal ∧ Continuous discreteRealToReal ∧
      ¬ IsHomeomorph discreteRealToReal ∧ IsHomeomorph (id : ℝ → ℝ) := by
  exact ⟨discreteRealToReal_bijective, discreteRealToReal_continuous,
    discreteRealToReal_not_isHomeomorph, (Homeomorph.refl ℝ).isHomeomorph⟩

/-! ### 5. Constant normalization preserves periods/depth but breaks reflection -/

/-- Constant rescaling of the actual normalized finite multiple-Gamma product. -/
def scaledFiniteMultipleGammaProduct (C : ℂ) (m : ℕ+) (z : ℂ) : ℂ :=
  C * multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z

theorem scaledFiniteMultipleGamma_periodRatio (C : ℂ) (hC : C ≠ 0)
    (m : ℕ+) (z τ : ℂ) :
    scaledFiniteMultipleGammaProduct C m (z + τ) /
        scaledFiniteMultipleGammaProduct C m z =
      multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) (z + τ) /
        multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z := by
  simp only [scaledFiniteMultipleGammaProduct]
  field_simp [hC]

theorem exists_scaledFiniteMultipleGamma_reflection_failure (m : ℕ+) :
    ∃ z : ℂ,
      multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m)
          (finiteMultipleGammaAnalyticReflectionCenter m - z) =
        (multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z)⁻¹ ∧
      scaledFiniteMultipleGammaProduct 2 m
          (finiteMultipleGammaAnalyticReflectionCenter m - z) ≠
        (scaledFiniteMultipleGammaProduct 2 m z)⁻¹ := by
  obtain ⟨z, hzF, hzB⟩ := exists_multipleEllipticGammaProducts_ne_zero
    (finiteMultipleGammaFunctionPeriods_im_pos m)
  refine ⟨z, finiteMultipleGammaProduct_reflection m z, ?_⟩
  have hcard : Even (Fintype.card (Fin 2)) := by norm_num
  have hprod : multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z ≠ 0 := by
    simp only [multipleEllipticGammaProduct, hcard, if_true]
    exact div_ne_zero hzF hzB
  intro hscaled
  rw [scaledFiniteMultipleGammaProduct, scaledFiniteMultipleGammaProduct,
    finiteMultipleGammaProduct_reflection] at hscaled
  field_simp [hprod] at hscaled
  norm_num at hscaled

/-- Actual Gamma normalization countermodel: period ratios and exact DA depth are unchanged by the
nonzero constant `2`, while reciprocal reflection fails somewhere. -/
theorem finiteMultipleGamma_normalization_not_determined (m : ℕ+) :
    (∀ z τ, scaledFiniteMultipleGammaProduct 2 m (z + τ) /
        scaledFiniteMultipleGammaProduct 2 m z =
      multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) (z + τ) /
        multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z) ∧
      multipleEllipticGammaTransverseDADepth
        (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) = 1 ∧
      ∃ z, scaledFiniteMultipleGammaProduct 2 m
          (finiteMultipleGammaAnalyticReflectionCenter m - z) ≠
        (scaledFiniteMultipleGammaProduct 2 m z)⁻¹ := by
  refine ⟨fun z τ => scaledFiniteMultipleGamma_periodRatio 2 (by norm_num) m z τ,
    finiteMultipleGammaTransverseDADepth m, ?_⟩
  obtain ⟨z, hbase, hscaled⟩ := exists_scaledFiniteMultipleGamma_reflection_failure m
  exact ⟨z, hscaled⟩

end

end GaloisForLFunctions.HTGeometry
