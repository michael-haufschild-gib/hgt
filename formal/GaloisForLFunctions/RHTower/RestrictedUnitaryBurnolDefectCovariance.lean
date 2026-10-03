import GaloisForLFunctions.RHTower.BurnolGraphActionFiltration
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicRelativeIndex
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# The Burnol defect covariance on primitive labels

Let `A_base : ℓ²(labels) → L²(0,∞)` be the complete primitive Burnol synthesis, with columns the
primitive features `f_α`, and `S_c` the forward damping semigroup, `S_c f_α = e^{-cλ_α} f_α`.  The
positive trace-class label Gram is `C_B = A_base† A_base`, `Tr C_B = B_base`, and its damped
conjugate is `D_c† C_B D_c = (S_c A_base)† (S_c A_base)`, with matrix entries
`e^{-cλ_α} e^{-cλ_β} ⟪f_α, f_β⟫`.  The defect covariance

`C_def(c) = C_B - D_c† C_B D_c = A_base† (1 - S_c† S_c) A_base ≥ 0`

is trace class, with `Tr C_def(c) = ∑_n (1 - n^{-2c}) Λ(n)/(4 n log³ n)`.  It is an operator identity
before any trace: on every finite packet of labels its compression is the sum of the
deleted-boundary and distributed-cocycle channel Grams, mixed prime entries included.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap Complex
open scoped NNReal InnerProductSpace ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

local instance rucriDefectFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance rucriDefectIndexMeasurableSpace : MeasurableSpace RoutePPrimitiveIndex := ⊤

/-- The positive trace-class label Gram `C_B = A_base† A_base`. -/
def burnolLabelGram :
    Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) →L[ℂ]
      Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) :=
  adjoint routePPrimitiveBurnolBaseSynthesis ∘L routePPrimitiveBurnolBaseSynthesis

/-- The damped conjugate `D_c† C_B D_c = (S_c A_base)† (S_c A_base)`. -/
def burnolDampedLabelGram (c : ℝ≥0) :
    Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) →L[ℂ]
      Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) :=
  adjoint (burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis) ∘L
    (burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis)

/-- **(RUCRI.13)** The defect covariance `C_def(c) = C_B - D_c† C_B D_c`. -/
def burnolDefectCovariance (c : ℝ≥0) :
    Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) →L[ℂ]
      Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) :=
  burnolLabelGram - burnolDampedLabelGram c

theorem burnolDefectCovariance_eq (c : ℝ≥0) :
    burnolDefectCovariance c =
      adjoint routePPrimitiveBurnolBaseSynthesis ∘L
        (1 - adjoint (burnolWeightedShift c) ∘L burnolWeightedShift c) ∘L
          routePPrimitiveBurnolBaseSynthesis := by
  rw [burnolDefectCovariance, burnolLabelGram, burnolDampedLabelGram, adjoint_comp]
  ext1 f
  simp only [sub_apply, comp_apply, one_apply_eq_self, map_sub]

/-- `C_def(c) ≥ 0`: the damping semigroup is a contraction. -/
theorem burnolDefectCovariance_isPositive (c : ℝ≥0) : (burnolDefectCovariance c).IsPositive := by
  rw [burnolDefectCovariance_eq, isPositive_iff]
  have hP := (isPositive_iff _).1 (isPositive_one_sub_adjoint_comp_self (norm_burnolWeightedShift_le c))
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · change inner ℂ (adjoint routePPrimitiveBurnolBaseSynthesis
        ((1 - adjoint (burnolWeightedShift c) ∘L burnolWeightedShift c)
          (routePPrimitiveBurnolBaseSynthesis x))) y =
      inner ℂ x (adjoint routePPrimitiveBurnolBaseSynthesis
        ((1 - adjoint (burnolWeightedShift c) ∘L burnolWeightedShift c)
          (routePPrimitiveBurnolBaseSynthesis y)))
    rw [adjoint_inner_left, adjoint_inner_right]
    exact hP.1 _ _
  · change 0 ≤ inner ℂ (adjoint routePPrimitiveBurnolBaseSynthesis
        ((1 - adjoint (burnolWeightedShift c) ∘L burnolWeightedShift c)
          (routePPrimitiveBurnolBaseSynthesis x))) x
    rw [adjoint_inner_left]
    exact hP.2 _

theorem burnolDampedSynthesis_isHilbertSchmidt (c : ℝ≥0) :
    (burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis).IsHilbertSchmidt :=
  routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt.comp_left _

theorem memSchattenClass_one_adjoint_comp_self {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (hT : T.IsHilbertSchmidt) : MemSchattenClass 1 (adjoint T ∘L T) :=
  (memRectSchattenClass_iff_memSchattenClass 1 _).1
    (memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hT hT.adjoint)

theorem burnolDefectCovariance_memSchattenClass_one (c : ℝ≥0) :
    MemSchattenClass 1 (burnolDefectCovariance c) :=
  (memSchattenClass_one_adjoint_comp_self routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt).one_sub
    (memSchattenClass_one_adjoint_comp_self (burnolDampedSynthesis_isHilbertSchmidt c))

/-- `Re Tr C_B = B_base`. -/
theorem re_opTrace_burnolLabelGram :
    (opTrace burnolLabelGram).re = routePPrimitiveBaseCauchyCubicTraceBudget := by
  rw [burnolLabelGram, ← RCLike.re_to_complex,
    re_opTrace_adjoint_comp_self routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt,
    hsNormSq_routePPrimitiveBurnolBaseSynthesis_eq_budget]

/-- **(RUCRI.14)** `Re Tr C_def(c)` is the total aperture defect mass. -/
theorem re_opTrace_burnolDefectCovariance (c : ℝ≥0) :
    (opTrace (burnolDefectCovariance c)).re = routePPrimitiveBurnolApertureTotalDefectMass c := by
  have h1 : MemSchattenClass 1 burnolLabelGram :=
    memSchattenClass_one_adjoint_comp_self routePPrimitiveBurnolBaseSynthesis_isHilbertSchmidt
  have h2 : MemSchattenClass 1 (burnolDampedLabelGram c) :=
    memSchattenClass_one_adjoint_comp_self (burnolDampedSynthesis_isHilbertSchmidt c)
  rw [burnolDefectCovariance, opTrace_sub_of_memSchattenClass_one h1 h2, sub_re, re_opTrace_burnolLabelGram, burnolDampedLabelGram, ← RCLike.re_to_complex,
    re_opTrace_adjoint_comp_self (burnolDampedSynthesis_isHilbertSchmidt c),
    hsNormSq_burnolDampedBase, routePPrimitiveBaseCauchyCubicTraceBudget,
    routePPrimitiveBurnolApertureTotalDefectMass]
  have hw := summable_routePPrimitiveBaseCauchyCubicWeight
  have hd : Summable fun pe : RoutePPrimitiveIndex =>
      Real.exp (-(2 * (c : ℝ) * xiGammaEulerPrimitiveLogFrequency pe)) *
        routePPrimitiveBaseCauchyCubicWeight pe := by
    refine hw.of_nonneg_of_le (fun pe => mul_nonneg (Real.exp_pos _).le
      (routePPrimitiveBaseCauchyCubicWeight_nonneg pe)) (fun pe => ?_)
    refine mul_le_of_le_one_left (routePPrimitiveBaseCauchyCubicWeight_nonneg pe) ?_
    rw [Real.exp_le_one_iff, neg_nonpos]
    have := xiGammaEulerPrimitiveLogFrequency_pos pe
    positivity
  rw [← hw.tsum_sub hd]
  refine tsum_congr fun pe => ?_
  rw [routePPrimitiveBurnolApertureDefectMass]
  ring_nf

/-- **(RUCRI.14)** natural-number form:
`Re Tr C_def(c) = ∑_n (1 - n^{-2c}) Λ(n) / (4 n log³ n)`. -/
theorem re_opTrace_burnolDefectCovariance_natural (c : ℝ≥0) :
    (opTrace (burnolDefectCovariance c)).re =
      ∑' n : ℕ, (1 - Real.exp (-2 * (c : ℝ) * Real.log n)) *
        finiteVonMangoldtRealWeight n / (4 * Real.log n ^ 3) := by
  rw [re_opTrace_burnolDefectCovariance, routePPrimitiveBurnolApertureTotalDefectMass_eq_natural]

/-! ## Matrix entries and the two defect channels -/

theorem eq_of_ae_count {β : Type*} {f g : RoutePPrimitiveIndex → β}
    (h : f =ᵐ[(Measure.count : Measure RoutePPrimitiveIndex)] g) (x : RoutePPrimitiveIndex) :
    f x = g x := by
  by_contra hne
  have hnull : (Measure.count : Measure RoutePPrimitiveIndex) {y | f y ≠ g y} = 0 := ae_iff.1 h
  have hx : (Measure.count : Measure RoutePPrimitiveIndex) {x} = 0 :=
    measure_mono_null (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hne) hnull
  rw [Measure.count_singleton] at hx
  exact one_ne_zero hx

/-- The label basis vector `e_α ∈ ℓ²(labels)`. -/
def burnolLabelBasisVec (α : RoutePPrimitiveIndex) :
    Lp ℂ 2 (Measure.count : Measure RoutePPrimitiveIndex) :=
  indicatorConstLp 2 (measurableSet_singleton α)
    (by rw [Measure.count_singleton]; exact ENNReal.one_ne_top) (1 : ℂ)

/-- The synthesis sends `e_α` to the primitive feature `f_α`. -/
theorem baseSynthesis_labelBasisVec (α : RoutePPrimitiveIndex) :
    routePPrimitiveBurnolBaseSynthesis (burnolLabelBasisVec α) = routePPrimitiveBurnolBaseField α := by
  rw [routePPrimitiveBurnolBaseSynthesis, l2Synthesis_apply]
  have hcoe : (burnolLabelBasisVec α : RoutePPrimitiveIndex → ℂ) =ᵐ[Measure.count]
      Set.indicator {α} fun _ => (1 : ℂ) := indicatorConstLp_coeFn
  rw [integral_congr_ae (hcoe.mono fun x hx => by rw [hx])]
  have hind : (fun x => Set.indicator {α} (fun _ => (1 : ℂ)) x •
      (routePPrimitiveBurnolBaseFieldLp : RoutePPrimitiveIndex → routePBurnolHalfLineL2) x) =
      Set.indicator {α} (fun x =>
        (routePPrimitiveBurnolBaseFieldLp : RoutePPrimitiveIndex → routePBurnolHalfLineL2) x) := by
    funext x
    by_cases hx : x ∈ ({α} : Set RoutePPrimitiveIndex) <;> simp [hx]
  rw [hind, integral_indicator (measurableSet_singleton α), integral_singleton, Measure.real,
    Measure.count_singleton, ENNReal.toReal_one]
  convert eq_of_ae_count memLp_two_routePPrimitiveBurnolBaseField.coeFn_toLp α using 1
  exact one_smul _ _

/-- `⟪e_α, C_B e_β⟫ = ⟪f_α, f_β⟫`. -/
theorem inner_labelBasis_burnolLabelGram (α β : RoutePPrimitiveIndex) :
    inner ℂ (burnolLabelBasisVec α) (burnolLabelGram (burnolLabelBasisVec β)) =
      inner ℂ (routePPrimitiveBurnolBaseField α) (routePPrimitiveBurnolBaseField β) := by
  rw [burnolLabelGram, comp_apply, adjoint_inner_right, baseSynthesis_labelBasisVec,
    baseSynthesis_labelBasisVec]

/-- The damped conjugate has the diagonal-semigroup matrix
`⟪e_α, D_c† C_B D_c e_β⟫ = e^{-cλ_α} e^{-cλ_β} ⟪f_α, f_β⟫`. -/
theorem inner_labelBasis_burnolDampedLabelGram (c : ℝ≥0) (α β : RoutePPrimitiveIndex) :
    inner ℂ (burnolLabelBasisVec α) (burnolDampedLabelGram c (burnolLabelBasisVec β)) =
      ((Real.exp (-((c : ℝ) * xiGammaEulerPrimitiveLogFrequency α)) *
          Real.exp (-((c : ℝ) * xiGammaEulerPrimitiveLogFrequency β)) : ℝ) : ℂ) *
        inner ℂ (routePPrimitiveBurnolBaseField α) (routePPrimitiveBurnolBaseField β) := by
  rw [burnolDampedLabelGram, comp_apply, adjoint_inner_right, comp_apply, comp_apply,
    baseSynthesis_labelBasisVec, baseSynthesis_labelBasisVec, burnolWeightedShift_baseField,
    burnolWeightedShift_baseField, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

/-- **(RUCRI.13), operator form.**  On every finite packet of labels the compression of
`C_def(c)` is the sum of the deleted-boundary and distributed-cocycle channel Grams. -/
theorem burnolDefectCovariance_packet (c : ℝ≥0) {N : ℕ} (pe : Fin N → RoutePPrimitiveIndex) :
    Matrix.of (fun i j => inner ℂ (burnolLabelBasisVec (pe i))
        (burnolDefectCovariance c (burnolLabelBasisVec (pe j)))) =
      routePPrimitiveBurnolApertureChannelGramMatrix c c.coe_nonneg 1 pe (fun _ => 0) +
        routePPrimitiveBurnolApertureChannelGramMatrix c c.coe_nonneg 2 pe (fun _ => 0) := by
  have hsum := routePPrimitiveBurnolWindowGramMatrix_eq_sum_channelGrams (c : ℝ) c.coe_nonneg pe
    (fun _ => 0)
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2] at hsum
  ext i j
  have hij := congrFun (congrFun hsum i) j
  simp only [Matrix.add_apply, Matrix.gram_apply] at hij
  have h0 : routePPrimitiveBurnolApertureChannelGramMatrix c c.coe_nonneg 0 pe (fun _ => 0) i j =
      inner ℂ (burnolWeightedShift c (routePPrimitiveBurnolBaseField (pe i)))
        (burnolWeightedShift c (routePPrimitiveBurnolBaseField (pe j))) := by
    rw [routePPrimitiveBurnolApertureChannelGramMatrix, Matrix.gram_apply, colligationVector_zero,
      colligationVector_zero]
    rfl
  rw [Matrix.of_apply, Matrix.add_apply, burnolDefectCovariance, sub_apply, inner_sub_right,
    inner_labelBasis_burnolLabelGram]
  change _ - inner ℂ (burnolLabelBasisVec (pe i))
    (adjoint (burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis)
      ((burnolWeightedShift c ∘L routePPrimitiveBurnolBaseSynthesis)
        (burnolLabelBasisVec (pe j)))) = _
  rw [adjoint_inner_right, comp_apply, comp_apply, baseSynthesis_labelBasisVec,
    baseSynthesis_labelBasisVec, ← h0]
  change inner ℂ (routePPrimitiveBurnolWindowFeatureLp (pe i) 0)
    (routePPrimitiveBurnolWindowFeatureLp (pe j) 0) - _ = _
  rw [hij]
  ring

/-- **(RUCRI.15) at the endpoint.**  The total defect opens with right derivative
`F(0) = ∑_n Λ(n) n^{-1} / (2 log² n)` at `c = 0`. -/
theorem tendsto_totalDefectMass_div_zero_natural :
    Tendsto (fun c : ℝ => routePPrimitiveBurnolApertureTotalDefectMass c / c) (nhdsWithin 0 (Ioi 0))
      (nhds (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + 2 * (0 : ℝ))) /
        (2 * Real.log n ^ 2))) := by
  rw [← restrictedUnitaryBurnolApertureTotalFlux_eq_natural, restrictedUnitaryBurnolApertureTotalFlux]
  have h : (fun pe : Nat.Primes × ℕ => restrictedUnitaryBurnolApertureFluxTerm 0 pe) =
      fun pe => routePPrimitiveBurnolApertureDefectFlux pe := by
    funext pe; simp [restrictedUnitaryBurnolApertureFluxTerm]
  rw [h]
  exact tendsto_routePPrimitiveBurnolApertureTotalDefectMass_div_zero

end

end RHTower
