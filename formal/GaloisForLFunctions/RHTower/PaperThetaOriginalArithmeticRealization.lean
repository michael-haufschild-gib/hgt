import GaloisForLFunctions.RHTower.PaperThetaNativeCohomology
import GaloisForLFunctions.RHTower.PaperThetaStripArithmeticSeries
import GaloisForLFunctions.RHTower.CHMDComplexWeilForm
import GaloisForLFunctions.RHTower.PaperThetaNativeArithmeticResolvent

/-! # Whole original Meyer cohomology in the literal native arithmetic graph

One fixed actual Gaussian regularization realizes every original class by a
continuous BV profile, faithfully, with both native tails and all arithmetic
edges. Its actual contour blocks converge in global BV and full graph norm,
and hence through the complete signed Weil expression.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph HedenmalmThetaSource
open Zeta23
open scoped DeningerMeyerNaturalTopology

/-- One fixed admitted schedule and one fixed genuine Gaussian regularization. -/
def nativeMeyerProfileMap : DeningerMeyerStrongLogCohomology →ₗ[ℂ] NativeContinuousSpace :=
  nativeGaussianClassMap deningerMeyerXiContourSchedule 1 zero_lt_one

def nativeMeyerArithmeticMap : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ComplexArithmeticGraph where
  toFun q := stripArithmeticLift (3/2) (nativeMeyerProfileMap q)
    (nativeGaussianClassMap_control deningerMeyerXiContourSchedule 1 zero_lt_one q).choose
    (nativeGaussianClassMap_control deningerMeyerXiContourSchedule 1 zero_lt_one q).choose_spec.2.2
  map_add' q r := by
    apply CHMDComplexJump.source_injective massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right
    change nativeMassCLM (nativeMeyerProfileMap (q+r)) =
      nativeMassCLM (nativeMeyerProfileMap q)+nativeMassCLM (nativeMeyerProfileMap r)
    rw [map_add, map_add]
  map_smul' c q := by
    apply CHMDComplexJump.source_injective massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right
    change nativeMassCLM (nativeMeyerProfileMap (c • q)) = c • nativeMassCLM (nativeMeyerProfileMap q)
    rw [map_smul, map_smul]

@[simp] theorem nativeMeyerArithmeticMap_source (q : DeningerMeyerStrongLogCohomology) :
    (nativeMeyerArithmeticMap q).val.fst = nativeMassCLM (nativeMeyerProfileMap q) := rfl

theorem nativeMeyerArithmeticMap_source_ae (q : DeningerMeyerStrongLogCohomology) :
    ((nativeMeyerArithmeticMap q).val.fst : ℝ → ℂ) =ᵐ[massMeasure] nativeMeyerProfileMap q :=
  (nativeMassMemLp (nativeMeyerProfileMap q)).coeFn_toLp

theorem nativeMeyerArithmeticMap_edge (q : DeningerMeyerStrongLogCohomology) :
    ((nativeMeyerArithmeticMap q).val.snd : ℝ × ℝ → ℂ) =ᵐ[edgeMeasure]
      (fun e => nativeMeyerProfileMap q (left e)-nativeMeyerProfileMap q (right e)) :=
  stripArithmeticLift_edge (3/2) (nativeMeyerProfileMap q)
    (nativeGaussianClassMap_control deningerMeyerXiContourSchedule 1 zero_lt_one q).choose
    (nativeGaussianClassMap_control deningerMeyerXiContourSchedule 1 zero_lt_one q).choose_spec.2.2

/-- Unconditional faithfulness on the entire original quotient. -/
theorem nativeMeyerArithmeticMap_injective : Function.Injective nativeMeyerArithmeticMap := by
  intro q r he
  apply nativeGaussianClassMap_injective deningerMeyerXiContourSchedule 1 zero_lt_one
  apply nativeMassCLM_injective
  exact congrArg (fun p : ComplexArithmeticGraph => p.val.fst) he

theorem nativeMeyerProfileMap_boundedVariation (q : DeningerMeyerStrongLogCohomology) :
    BoundedVariationOn (nativeMeyerProfileMap q) univ :=
  nativeGaussianClassMap_boundedVariation deningerMeyerXiContourSchedule 1 zero_lt_one q

def nativeMeyerBVProfile (q : DeningerMeyerStrongLogCohomology) : ThetaContinuousBV where
  toFun := nativeMeyerProfileMap q
  continuous := (nativeMeyerProfileMap q).continuous
  bv := nativeMeyerProfileMap_boundedVariation q

/-- Every original class now supplies actual whole-domain forcing, with a unique
native solution, compact AC transport and the complete arithmetic form. -/
theorem nativeMeyer_inhomogeneous_full_source (q : DeningerMeyerStrongLogCohomology) :
    ∃! f : ThetaNativeDomain,
      (∀ x, thetaSpatialAction f x-I*f x = nativeMeyerProfileMap q x) ∧
      AbsolutelyContinuousOnInterval (nativeClosedQuantile f) 0 1 ∧
      (∀ L : ℂ →L[ℝ] ℝ,
        (nativeWeilGraph f L).val.fst =ᵐ[massMeasure] (fun x => L (f x)) ∧
        sourceWeilEnergy (nativeWeilGraph f L) =
          ThetaQuantileArithmetic.weilEnergy (fun t => L (nativeClosedQuantile f t))) := by
  simpa [nativeMeyerBVProfile] using nativeThetaImaginaryEquation_existsUnique_full_source
    (1 : ℝˣ) (nativeMeyerBVProfile q)

theorem nativeMeyerProfileMap_theta_mean_zero (q : DeningerMeyerStrongLogCohomology) :
    boundedThetaMomentCLM 0 (nativeMeyerProfileMap q) = 0 := by
  obtain ⟨g, rfl⟩ := (Submodule.Quotient.mk_surjective (LinearMap.range deningerMeyerStrongLogSumLM)) q
  exact nativeGaussianSource_theta_mean_zero deningerMeyerXiContourSchedule g zero_lt_one

/-- Exact original-source readout, for every complex Mellin parameter. -/
theorem nativeMeyerProfileMap_transform (g : DeningerMeyerStrongLogTarget) (u : ℂ) :
    boundedThetaMomentCLM (thetaContourParameter u) (nativeMeyerProfileMap (Submodule.Quotient.mk g)) =
      (I*(u-1/2)/(thetaSource.mass : ℂ))*deningerMeyerStrongLogMellin
        (nativeGaussianOriginalSource deningerMeyerXiContourSchedule g 1 zero_lt_one) u :=
  nativeGaussianSource_transform deningerMeyerXiContourSchedule g zero_lt_one u

/-- Both scalar components retain every original prime, archimedean and polar term. -/
theorem nativeMeyerArithmeticMap_fullWeil (q : DeningerMeyerStrongLogCohomology) :
    complexWeilEnergy (nativeMeyerArithmeticMap q) =
      fullBVWeilExpression (fun x => (nativeMeyerProfileMap q x).re)+
      fullBVWeilExpression (fun x => (nativeMeyerProfileMap q x).im) :=
  complexWeilEnergy_eq_fullBV _ _ (nativeMeyerArithmeticMap_source_ae q)
    (Complex.reCLM.lipschitz.comp_boundedVariationOn (nativeMeyerProfileMap_boundedVariation q))
    (Complex.imCLM.lipschitz.comp_boundedVariationOn (nativeMeyerProfileMap_boundedVariation q))

def nativeMeyerBlock (g : DeningerMeyerStrongLogTarget) (n : ℕ) : NativeContinuousSpace :=
  nativeXiBlock deningerMeyerXiContourSchedule
    (deningerGaussianMellinRegularization 1 (deningerMeyerStrongLogMellin g))
    (deningerMeyerStrongLogMellin_gaussianRegular g zero_lt_one).differentiable n

/-- Actual contour approximants converge before and after arithmetic admission. -/
theorem nativeMeyerArithmeticMap_contour_approximation (g : DeningerMeyerStrongLogTarget) :
    ∃ (c : ℕ → ℝ) (_hc : Summable c)
      (hb : ∀ n, 0 ≤ c n ∧ ‖nativeMeyerBlock g n‖ ≤ c n ∧ ∀ x y,
        ‖nativeMeyerBlock g n y-nativeMeyerBlock g n x‖ ≤
          c n*|stripCutControl (3/2) y-stripCutControl (3/2) x|),
      HasSum (fun n => stripArithmeticLift (3/2) (nativeMeyerBlock g n) (c n) (hb n).2.2)
        (nativeMeyerArithmeticMap (Submodule.Quotient.mk g)) ∧
      Tendsto (fun N => globalBVSize (fun x =>
        (nativeMeyerProfileMap (Submodule.Quotient.mk g)-∑ n ∈ Finset.range N, nativeMeyerBlock g n) x))
        atTop (𝓝 0) ∧
      Tendsto (fun N => complexWeilEnergy
        (∑ n ∈ Finset.range N, stripArithmeticLift (3/2) (nativeMeyerBlock g n) (c n) (hb n).2.2))
        atTop (𝓝 (fullBVWeilExpression (fun x => (nativeMeyerProfileMap (Submodule.Quotient.mk g) x).re)+
          fullBVWeilExpression (fun x => (nativeMeyerProfileMap (Submodule.Quotient.mk g) x).im))) := by
  obtain ⟨c, hc, hb⟩ := gaussian_nativeXiBlock_control deningerMeyerXiContourSchedule g zero_lt_one
  have he : stripArithmeticLift (3/2) (∑' n, nativeMeyerBlock g n) (∑' n, c n)
      (stripSeries_increment hc (fun n => (hb n).2.1) (fun n => (hb n).2.2)) =
        nativeMeyerArithmeticMap (Submodule.Quotient.mk g) := by
    apply CHMDComplexJump.source_injective massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right
    rfl
  have hs : HasSum (fun n => stripArithmeticLift (3/2) (nativeMeyerBlock g n) (c n) (hb n).2.2)
      (stripArithmeticLift (3/2) (∑' n, nativeMeyerBlock g n) (∑' n, c n)
        (stripSeries_increment hc (fun n => (hb n).2.1) (fun n => (hb n).2.2))) :=
    stripArithmeticSeries (3/2) hc (fun n => (hb n).2.1) (fun n => (hb n).2.2)
  rw [he] at hs
  refine ⟨c, hc, hb, hs, stripSeries_globalBV hc (fun n => (hb n).2.1) (fun n => (hb n).2.2), ?_⟩
  have ht := (continuous_complexWeilEnergy.tendsto _).comp hs.tendsto_sum_nat
  rw [nativeMeyerArithmeticMap_fullWeil] at ht
  exact ht

/-- Closed structural capstone: every original class is faithfully realized in
the full arithmetic graph by a literal continuous BV theta profile. -/
theorem nativeMeyer_full_arithmetic_realization :
    Function.Injective nativeMeyerArithmeticMap ∧
      ∀ q : DeningerMeyerStrongLogCohomology,
        BoundedVariationOn (nativeMeyerProfileMap q) univ ∧
        ((nativeMeyerArithmeticMap q).val.fst : ℝ → ℂ) =ᵐ[massMeasure] nativeMeyerProfileMap q ∧
        ((nativeMeyerArithmeticMap q).val.snd : ℝ × ℝ → ℂ) =ᵐ[edgeMeasure]
          (fun e => nativeMeyerProfileMap q (left e)-nativeMeyerProfileMap q (right e)) ∧
        boundedThetaMomentCLM 0 (nativeMeyerProfileMap q) = 0 :=
  ⟨nativeMeyerArithmeticMap_injective, fun q => ⟨nativeMeyerProfileMap_boundedVariation q,
    nativeMeyerArithmeticMap_source_ae q, nativeMeyerArithmeticMap_edge q,
    nativeMeyerProfileMap_theta_mean_zero q⟩⟩

end RHTower.PaperThetaEndpoint
