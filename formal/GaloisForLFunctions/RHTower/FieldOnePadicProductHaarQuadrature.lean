import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFiniteLevel
import GaloisForLFunctions.RHTower.FieldOneFiniteQuotientHaarQuadrature
import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicProductFourierParseval

/-!
# Haar normalization on finite products of p-adic fields

This file proves the exact product Haar Jacobian for the simultaneous chart
`u ↦ (pᵢ⁻ⁿⁱ uᵢ)ᵢ`.  It is the measure-theoretic bridge from a compactly
supported locally constant function on a finite product of p-adic fields to
its finite additive quotient.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

/-- Product of the unit-ball-normalized Haar measures on the p-adic fields. -/
def fieldOnePadicProductUnitBallNormalizedHaar :
    Measure (FieldOnePadicProduct p) :=
  Measure.pi fun i => fieldOnePadicUnitBallNormalizedHaar (p i)

instance fieldOnePadicProductUnitBallNormalizedHaar_isAddHaar :
    (fieldOnePadicProductUnitBallNormalizedHaar p).IsAddHaarMeasure := by
  unfold fieldOnePadicProductUnitBallNormalizedHaar
  infer_instance

/-- Product of the probability Haar measures on the integral unit balls. -/
def fieldOnePadicIntProductNormalizedHaar :
    Measure (FieldOnePadicIntProduct p) :=
  Measure.pi fun i => fieldOnePadicIntNormalizedHaar (p i)

instance fieldOnePadicIntProductNormalizedHaar_isAddHaar :
    (fieldOnePadicIntProductNormalizedHaar p).IsAddHaarMeasure := by
  unfold fieldOnePadicIntProductNormalizedHaar
  infer_instance

omit [DecidableEq ι] in
@[simp] theorem fieldOnePadicIntProductNormalizedHaar_univ :
    fieldOnePadicIntProductNormalizedHaar p Set.univ = 1 := by
  rw [fieldOnePadicIntProductNormalizedHaar, Measure.pi_univ]
  simp

/-- Simultaneous additive chart `u ↦ (pᵢ⁻ⁿⁱ uᵢ)ᵢ`. -/
def fieldOnePadicProductInvPowIntCoeAddMonoidHom (n : ι → ℕ) :
    FieldOnePadicIntProduct p →+ FieldOnePadicProduct p where
  toFun u i := fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i) (u i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [DecidableEq ι] in
theorem fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
    (n : ι → ℕ) :
    Topology.IsOpenEmbedding
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n) := by
  change Topology.IsOpenEmbedding
    (Pi.map fun i => fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i))
  exact Topology.IsOpenEmbedding.piMap fun i =>
    fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding (p i) (n i)

omit [Fintype ι] [DecidableEq ι] in
theorem fieldOnePadicProductInvPowIntCoeAddMonoidHom_range (n : ι → ℕ) :
    Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n) =
      Set.univ.pi fun i =>
        (fieldOnePadicDenominatorStage (p i) (n i) : Set ℚ_[p i]) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    intro i _
    change fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i) (u i) ∈
      (fieldOnePadicDenominatorStage (p i) (n i) : Set ℚ_[p i])
    rw [← fieldOnePadicInvPowIntCoeAddMonoidHom_range (p i) (n i)]
    exact ⟨u i, rfl⟩
  · intro hx
    choose u hu using fun i =>
      (show x i ∈ Set.range
          (fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i)) by
        rw [fieldOnePadicInvPowIntCoeAddMonoidHom_range]
        exact hx i (Set.mem_univ i))
    refine ⟨u, ?_⟩
    funext i
    exact hu i

/-- Product pullback of ambient Haar measure along the simultaneous chart. -/
def fieldOnePadicProductScaledHaar (n : ι → ℕ) :
    Measure (FieldOnePadicIntProduct p) :=
  Measure.pi fun i => fieldOnePadicInvPowIntHaarComap (p i) (n i)

/-- The simultaneous chart sends its product pullback Haar measure to ambient
product Haar restricted to the coordinatewise denominator stage. -/
theorem fieldOnePadicProductScaledHaar_map (n : ι → ℕ) :
    Measure.map (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n)
        (fieldOnePadicProductScaledHaar p n) =
      (fieldOnePadicProductUnitBallNormalizedHaar p).restrict
        (Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n)) := by
  rw [fieldOnePadicProductScaledHaar,
    fieldOnePadicProductUnitBallNormalizedHaar]
  change Measure.map
      (fun u i => fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i) (u i))
      (Measure.pi fun i => fieldOnePadicInvPowIntHaarComap (p i) (n i)) = _
  rw [Measure.pi_map_pi]
  · rw [fieldOnePadicProductInvPowIntCoeAddMonoidHom_range]
    rw [Measure.restrict_pi_pi]
    congr 1
    funext i
    rw [show fieldOnePadicInvPowIntHaarComap (p i) (n i) =
        (fieldOnePadicUnitBallNormalizedHaar (p i)).comap
          (fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i)) by rfl]
    rw [(fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding
      (p i) (n i)).measurableEmbedding.map_comap]
    rw [fieldOnePadicInvPowIntCoeAddMonoidHom_range]
  · intro i
    exact (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding
      (p i) (n i)).measurableEmbedding.measurable.aemeasurable

omit [DecidableEq ι] in
/-- Product measures commute with finite families of finite scalar factors. -/
theorem fieldOneMeasurePi_nnreal_smul (c : ι → ℝ≥0)
    (μ : (i : ι) → Measure (ℤ_[p i])) [∀ i, SigmaFinite (μ i)] :
    Measure.pi (fun i => c i • μ i) =
      (∏ i, (c i : ℝ≥0∞)) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply]
  rw [Measure.pi_pi]
  simp_rw [Measure.smul_apply]
  change (∏ i, (c i : ℝ≥0∞)) * (∏ i, μ i (s i)) =
    ∏ i, (c i : ℝ≥0∞) * μ i (s i)
  exact Finset.prod_mul_distrib.symm

/-- Exact product Haar Jacobian of `u ↦ (pᵢ⁻ⁿⁱ uᵢ)ᵢ`. -/
theorem fieldOnePadicProductScaledHaar_eq_smul (n : ι → ℕ) :
    fieldOnePadicProductScaledHaar p n =
      (∏ i, (p i : ℝ≥0∞) ^ n i) •
        fieldOnePadicIntProductNormalizedHaar p := by
  rw [fieldOnePadicProductScaledHaar,
    fieldOnePadicIntProductNormalizedHaar]
  simp_rw [fieldOnePadicInvPowIntHaarComap_eq_smul]
  change Measure.pi
      (fun i => ((p i : ℝ≥0) ^ n i) • fieldOnePadicIntNormalizedHaar (p i)) =
    (∏ i, (((p i : ℝ≥0) ^ n i : ℝ≥0) : ℝ≥0∞)) •
      Measure.pi (fun i => fieldOnePadicIntNormalizedHaar (p i))
  exact fieldOneMeasurePi_nnreal_smul p (fun i => (p i : ℝ≥0) ^ n i)
    (fun i => fieldOnePadicIntNormalizedHaar (p i))

/-- Exact complex-valued change of variables from a coordinatewise
denominator stage to the product integral unit ball. -/
theorem fieldOnePadicProduct_setIntegral_invPowIntCoe (n : ι → ℕ)
    (h : FieldOnePadicProduct p → ℂ) :
    ∫ x in Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n), h x
        ∂fieldOnePadicProductUnitBallNormalizedHaar p =
      ((∏ i, (p i : ℝ) ^ n i : ℝ) : ℂ) *
        ∫ u, h (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n u)
          ∂fieldOnePadicIntProductNormalizedHaar p := by
  rw [← fieldOnePadicProductScaledHaar_map p n]
  rw [(fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
    p n).measurableEmbedding.integral_map]
  rw [fieldOnePadicProductScaledHaar_eq_smul, integral_smul_measure]
  simp only [ENNReal.toReal_prod, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, Complex.real_smul, Complex.ofReal_prod,
    Complex.ofReal_pow, Complex.ofReal_natCast]

/-- Real-valued form of product denominator-stage change of variables. -/
theorem fieldOnePadicProduct_setIntegral_invPowIntCoe_real (n : ι → ℕ)
    (h : FieldOnePadicProduct p → ℝ) :
    ∫ x in Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n), h x
        ∂fieldOnePadicProductUnitBallNormalizedHaar p =
      (∏ i, (p i : ℝ) ^ n i : ℝ) *
        ∫ u, h (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n u)
          ∂fieldOnePadicIntProductNormalizedHaar p := by
  rw [← fieldOnePadicProductScaledHaar_map p n]
  rw [(fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
    p n).measurableEmbedding.integral_map]
  rw [fieldOnePadicProductScaledHaar_eq_smul, integral_smul_measure]
  simp only [ENNReal.toReal_prod, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, smul_eq_mul]

end

end GaloisForLFunctions.RHTower
