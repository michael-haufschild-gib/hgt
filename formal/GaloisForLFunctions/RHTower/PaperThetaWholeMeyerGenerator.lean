import GaloisForLFunctions.RHTower.PaperThetaContourGenerator
import GaloisForLFunctions.RHTower.PaperThetaOriginalArithmeticRealization

/-! # Whole original Meyer cohomology in the native differential domain

The faithful source realization intertwines the original centered generator
with the literal theta differential expression on every original class.
The exact contour Green identity passes through both source-admitted series.
All scalar-shift words retain their full original-source solution equations.
-/

noncomputable section
open Complex Set Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

def nativeMeyerCenteredSource (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  (-I) • (deningerMeyerStrongLogGenerator g-(1/2 : ℂ) • g)

theorem nativeMeyerCenteredSource_mellin (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (nativeMeyerCenteredSource g) s =
      thetaContourParameter s*deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellinLM s
    ((-I) • (deningerMeyerStrongLogGenerator g-(1/2 : ℂ) • g)) = _
  rw [map_smul, map_sub, map_smul]
  change (-I)*(deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) s-
    (1/2 : ℂ)*deningerMeyerStrongLogMellin g s) = _
  rw [deningerMeyerStrongLogGenerator_mellin]
  dsimp [thetaContourParameter]
  ring

theorem nativeMeyerCenteredSource_mk (g : DeningerMeyerStrongLogTarget) :
    (Submodule.Quotient.mk (nativeMeyerCenteredSource g) : DeningerMeyerStrongLogCohomology) =
      deningerMeyerCenteredCohomologyGenerator (Submodule.Quotient.mk g) := by
  simp only [nativeMeyerCenteredSource, Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_sub, deningerMeyerCenteredCohomologyGenerator,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    deningerMeyerCohomologyGenerator_mk]

theorem nativeCompactResolvent_xiBlock_shift (S : DeningerMeyerXiContourSchedule)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n : ℕ) :
    nativeCompactResolvent
        (nativeXiBlock S (nativeContourShift F) (differentiable_nativeContourShift hF) n) =
      nativeXiBlock S F hF n := by
  cases n with
  | zero => exact nativeCompactResolvent_xiContour_shift hF S.central_nonzero
  | succ n =>
      change nativeCompactResolvent (_+_) = _+_
      rw [map_add, nativeCompactResolvent_xiContour_shift hF (S.upper_nonzero n),
        nativeCompactResolvent_xiContour_shift hF (S.lower_nonzero n)]

theorem nativeMeyerCenteredSource_gaussianMellin
    (g : DeningerMeyerStrongLogTarget) (ε : ℝ) :
    deningerGaussianMellinRegularization ε
      (deningerMeyerStrongLogMellin (nativeMeyerCenteredSource g-I • g)) =
        nativeContourShift
          (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)) := by
  funext s
  have hm : deningerMeyerStrongLogMellin
      (nativeMeyerCenteredSource g-I • g : DeningerMeyerStrongLogTarget) s =
      (thetaContourParameter s-I)*deningerMeyerStrongLogMellin g s := by
    change deningerMeyerStrongLogMellinLM s (nativeMeyerCenteredSource g-I • g) = _
    rw [map_sub, map_smul]
    change deningerMeyerStrongLogMellin (nativeMeyerCenteredSource g) s-
      I*deningerMeyerStrongLogMellin g s = _
    rw [nativeMeyerCenteredSource_mellin]
    ring
  change exp ((ε : ℂ)*s^2)*deningerMeyerStrongLogMellin
      (nativeMeyerCenteredSource g-I • g : DeningerMeyerStrongLogTarget) s =
    (thetaContourParameter s-I)*(exp ((ε : ℂ)*s^2)*deningerMeyerStrongLogMellin g s)
  rw [hm]
  ring

theorem nativeXiBlock_congr (S : DeningerMeyerXiContourSchedule)
    {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (h : F = G) :
    nativeXiBlock S F hF = nativeXiBlock S G hG := by
  subst G
  rfl

theorem nativeCompactResolvent_gaussian_source_shift (S : DeningerMeyerXiContourSchedule)
    (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    nativeCompactResolvent
        (nativeGaussianSource S (nativeMeyerCenteredSource g-I • g) ε hε) =
      nativeGaussianSource S g ε hε := by
  let F := deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)
  have hF : Differentiable ℂ F :=
    (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable
  have hb := nativeXiBlock_congr S
    (deningerMeyerStrongLogMellin_gaussianRegular
      (nativeMeyerCenteredSource g-I • g) hε).differentiable
    (differentiable_nativeContourShift hF) (nativeMeyerCenteredSource_gaussianMellin g ε)
  unfold nativeGaussianSource
  exact (nativeCompactResolvent.map_tsum
    (gaussian_nativeXiBlock_summable S (nativeMeyerCenteredSource g-I • g) hε)).trans
      (tsum_congr fun n =>
        (congrArg (fun H : ℕ → NativeContinuousSpace => nativeCompactResolvent (H n)) hb).trans
          (nativeCompactResolvent_xiBlock_shift S hF n))

/-- The actual compact inverse restricts to the entire original quotient. -/
theorem nativeGaussianClassMap_resolvent_shift (S : DeningerMeyerXiContourSchedule)
    (ε : ℝ) (hε : 0 < ε) (q : DeningerMeyerStrongLogCohomology) :
    nativeCompactResolvent (nativeGaussianClassMap S ε hε
      (deningerMeyerCenteredCohomologyGenerator q-I • q)) = nativeGaussianClassMap S ε hε q := by
  induction q using Submodule.Quotient.induction_on with
  | H g =>
      rw [← nativeMeyerCenteredSource_mk, ← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_sub, nativeGaussianClassMap_mk, nativeGaussianClassMap_mk]
      exact nativeCompactResolvent_gaussian_source_shift S g hε

/-- Whole-source generator compatibility for the literal spatial expression. -/
theorem nativeGaussianClassMap_generator (S : DeningerMeyerXiContourSchedule)
    (ε : ℝ) (hε : 0 < ε) (q : DeningerMeyerStrongLogCohomology) :
    thetaSpatialAction (nativeGaussianClassMap S ε hε q) =
      (nativeGaussianClassMap S ε hε (deningerMeyerCenteredCohomologyGenerator q) : ℝ → ℂ) := by
  funext x
  have he := boundedNativeResolvent_equation nativeCompactParameter
    (nativeGaussianClassMap S ε hε (deningerMeyerCenteredCohomologyGenerator q-I • q)) x
  change thetaSpatialAction (nativeCompactResolvent _) x-
    nativeCompactParameter.val*nativeCompactResolvent _ x = _ at he
  rw [nativeGaussianClassMap_resolvent_shift, nativeCompactParameter_val,
    map_sub, map_smul] at he
  simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul] at he
  linear_combination he

theorem nativeMeyerProfileMap_generator (q : DeningerMeyerStrongLogCohomology) :
    thetaSpatialAction (nativeMeyerProfileMap q) =
      (nativeMeyerProfileMap (deningerMeyerCenteredCohomologyGenerator q) : ℝ → ℂ) :=
  nativeGaussianClassMap_generator deningerMeyerXiContourSchedule 1 zero_lt_one q

theorem nativeMeyerProfileMap_resolvent_shift (q : DeningerMeyerStrongLogCohomology) :
    nativeCompactResolvent (nativeMeyerProfileMap
      (deningerMeyerCenteredCohomologyGenerator q-I • q)) = nativeMeyerProfileMap q :=
  nativeGaussianClassMap_resolvent_shift deningerMeyerXiContourSchedule 1 zero_lt_one q

/-- Every original forcing has its unique original solution under the same
literal compact Green operator used on the whole native uniform space. -/
theorem nativeMeyerCompactResolvent_source (f : DeningerMeyerStrongLogCohomology) :
    ∃! q : DeningerMeyerStrongLogCohomology,
      deningerMeyerCenteredCohomologyGenerator q-I • q = f ∧
        nativeCompactResolvent (nativeMeyerProfileMap f) = nativeMeyerProfileMap q := by
  obtain ⟨q, hq⟩ := deningerMeyerCohomologyShift_surjective_of_xi_ne_zero (-1/2)
    (xi_ne_zero_of_abs_im_le_four (by norm_num)) (I • f)
  have he : deningerMeyerCenteredCohomologyGenerator q-I • q = f := by
    have hs : deningerMeyerCenteredCohomologyGenerator q-I • q =
        (-I) • deningerMeyerCohomologyShift (-1/2) q := by
      simp only [deningerMeyerCenteredCohomologyGenerator, deningerMeyerCohomologyShift,
        LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]
      module
    rw [hs, hq, smul_smul]
    simp
  have hr := nativeMeyerProfileMap_resolvent_shift q
  rw [he] at hr
  refine ⟨q, ⟨he, hr⟩, fun v hv => ?_⟩
  apply nativeGaussianClassMap_injective deningerMeyerXiContourSchedule 1 zero_lt_one
  exact hv.2.symm.trans hr

/-- Every original class lies in the actual two-ended BV differential domain. -/
def nativeMeyerDifferentialRealization (q : DeningerMeyerStrongLogCohomology) :
    ThetaNativeDomain where
  toThetaContinuousBV := nativeMeyerBVProfile q
  differentiable := by
    rw [show (nativeMeyerBVProfile q : ℝ → ℂ) = nativeMeyerProfileMap q from rfl,
      ← nativeMeyerProfileMap_resolvent_shift q]
    exact fun x => (hasDerivAt_boundedNativeResolvent nativeCompactParameter _ x).differentiableAt
  leftTrace := by
    change Tendsto (nativeMeyerProfileMap q) atBot (𝓝 (thetaTailTrace (nativeMeyerProfileMap q)))
    rw [← nativeMeyerProfileMap_resolvent_shift q]
    rw [show thetaTailTrace (nativeCompactResolvent _) = boundedResolventTrace nativeCompactParameter _
      from boundedNativeResolvent_trace nativeCompactParameter _]
    exact boundedNativeResolvent_atBot nativeCompactParameter _

@[simp] theorem nativeMeyerDifferentialRealization_apply
    (q : DeningerMeyerStrongLogCohomology) (x : ℝ) :
    nativeMeyerDifferentialRealization q x = nativeMeyerProfileMap q x := rfl

/-- Every complete source word acts by the same literal differential word. -/
theorem nativeMeyerProfileMap_word (L : List ℂ) (q : DeningerMeyerStrongLogCohomology) :
    thetaSpatialWord L (nativeMeyerProfileMap q) =
      (nativeMeyerProfileMap
        (deningerMeyerGeneratorWord deningerMeyerCenteredCohomologyGenerator L q) : ℝ → ℂ) := by
  induction L with
  | nil => rfl
  | cons z L ih =>
      simp only [thetaSpatialWord, ih, nativeMeyerProfileMap_generator,
        deningerMeyerGeneratorWord, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
      rfl

/-- Exact source/spatial equation identity on the full original range. -/
theorem nativeMeyerProfileMap_word_equation (L : List ℂ)
    (q f : DeningerMeyerStrongLogCohomology) :
    thetaSpatialWord L (nativeMeyerProfileMap q) = (nativeMeyerProfileMap f : ℝ → ℂ) ↔
      deningerMeyerGeneratorWord deningerMeyerCenteredCohomologyGenerator L q = f := by
  rw [nativeMeyerProfileMap_word]
  constructor
  · intro h
    apply nativeGaussianClassMap_injective deningerMeyerXiContourSchedule 1 zero_lt_one
    exact BoundedContinuousFunction.ext (congrFun h)
  · rintro rfl
    rfl

theorem nativeMeyerProfileMap_word_boundedVariation (L : List ℂ)
    (q : DeningerMeyerStrongLogCohomology) :
    BoundedVariationOn (thetaSpatialWord L (nativeMeyerProfileMap q)) univ := by
  rw [nativeMeyerProfileMap_word]
  exact nativeMeyerProfileMap_boundedVariation _

/-- The complete signed arithmetic expression survives every source word. -/
theorem nativeMeyerProfileMap_word_fullWeil (L : List ℂ)
    (q : DeningerMeyerStrongLogCohomology) :
    CHMDDoobGraph.complexWeilEnergy
        (nativeMeyerArithmeticMap
          (deningerMeyerGeneratorWord deningerMeyerCenteredCohomologyGenerator L q)) =
      CHMDDoobGraph.fullBVWeilExpression (fun x => (thetaSpatialWord L (nativeMeyerProfileMap q) x).re)+
        CHMDDoobGraph.fullBVWeilExpression (fun x => (thetaSpatialWord L (nativeMeyerProfileMap q) x).im) := by
  rw [nativeMeyerProfileMap_word]
  exact nativeMeyerArithmeticMap_fullWeil _

/-- Faithful whole-source differential realization and exact native inversion,
with no spectral, positivity, or infinite-packet admission premise. -/
theorem nativeMeyer_whole_differential_realization :
    Function.Injective nativeMeyerProfileMap ∧
      (∀ q : DeningerMeyerStrongLogCohomology,
        thetaSpatialAction (nativeMeyerDifferentialRealization q) =
          (nativeMeyerProfileMap (deningerMeyerCenteredCohomologyGenerator q) : ℝ → ℂ)) ∧
      (∀ f : DeningerMeyerStrongLogCohomology,
        ∃! q : DeningerMeyerStrongLogCohomology,
          deningerMeyerCenteredCohomologyGenerator q-I • q = f ∧
            nativeCompactResolvent (nativeMeyerProfileMap f) = nativeMeyerProfileMap q) :=
  ⟨nativeGaussianClassMap_injective deningerMeyerXiContourSchedule 1 zero_lt_one,
    nativeMeyerProfileMap_generator, nativeMeyerCompactResolvent_source⟩

end RHTower.PaperThetaEndpoint
