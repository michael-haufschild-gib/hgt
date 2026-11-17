import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatEvenPotential
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralRoot
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralDifferential
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization
import GaloisForLFunctions.RHTower.CHMDJumpGraphContractions

/-!
# Flat nonlinear energy on the complete arithmetic jump graph

Integrate the even flat loss against the literal CHMD edge measure,
retaining the archimedean density and every prime-power line. The energy
is finite and C¹ on the complete source graph. Its critical states are
exactly constant profiles, despite vanishing curvature at zero jumps.
This concerns the positive nonlinear jump energy; the original signed
Weil energy retains its separate negative mass term.
-/

open MeasureTheory Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open _root_.RHTower.CHMDDoobGraph
noncomputable section

/-- Both jump orientations are charged by the actual flat potential. -/
def flatJumpEnergy (p : SourceGraph) : ℝ :=
  integralEnergy (edgeMap p) + integralEnergy (-edgeMap p)

/-- The actual first variation, including the negative jump orientation. -/
def flatJumpFirstVariation (p : SourceGraph) : SourceGraph →L[ℝ] ℝ :=
  (innerSL ℝ (gradientLp (edgeMap p))).comp edgeMap +
    (innerSL ℝ (gradientLp (-edgeMap p))).comp (-edgeMap)

theorem flatJumpEnergy_integral (p : SourceGraph) :
    flatJumpEnergy p = ∫ e, evenPotential (p.val.snd e) ∂edgeMeasure := by
  rw [flatJumpEnergy, integralEnergy, integralEnergy,
    ← integral_add (integrable_potential (edgeMap p)) (integrable_potential (-edgeMap p))]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg (edgeMap p)] with e he
  rw [he]
  rfl

private theorem integrable_even_edge (p : SourceGraph) :
    Integrable (fun e => evenPotential (p.val.snd e)) edgeMeasure := by
  apply ((integrable_potential (edgeMap p)).add (integrable_potential (-edgeMap p))).congr
  filter_upwards [Lp.coeFn_neg (edgeMap p)] with e he
  simp only [Pi.add_apply]
  rw [he]
  rfl

/-- The complete arithmetic edge measure needs no extra nonlinear integrability premise. -/
theorem flatJumpEnergy_bounds (p : SourceGraph) :
    0 ≤ flatJumpEnergy p ∧ flatJumpEnergy p ≤ ‖p.val.snd‖ ^ 2 / 2 := by
  refine ⟨add_nonneg (integral_energy_bounds (edgeMap p)).1
    (integral_energy_bounds (-edgeMap p)).1, ?_⟩
  rw [flatJumpEnergy_integral]
  have h := integral_mono (integrable_even_edge p) ((Lp.memLp p.val.snd).integrable_sq.div_const 2)
    (fun e => (evenPotential_bounds (p.val.snd e)).2)
  rw [integral_div] at h
  have hs : (∫ e, p.val.snd e ^ 2 ∂edgeMeasure) = ‖p.val.snd‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun e => by
      change p.val.snd e ^ 2 = p.val.snd e * p.val.snd e
      ring
  rwa [hs] at h

/-- The derivative acts on the actual complete graph, rather than a formal test space. -/
theorem flatJumpEnergy_hasFDerivAt (p : SourceGraph) :
    HasFDerivAt flatJumpEnergy (flatJumpFirstVariation p) p := by
  have hp : HasFDerivAt (fun q : SourceGraph => integralEnergy (edgeMap q))
      ((innerSL ℝ (gradientLp (edgeMap p))).comp edgeMap) p :=
    (integralEnergy_hasFDerivAt (edgeMap p)).comp p edgeMap.hasFDerivAt
  have hn : HasFDerivAt (integralEnergy ∘ ((-edgeMap) : SourceGraph → Lp ℝ 2 edgeMeasure))
      ((innerSL ℝ (gradientLp ((-edgeMap) p))).comp (-edgeMap)) p :=
    (integralEnergy_hasFDerivAt ((-edgeMap) p)).comp p (-edgeMap).hasFDerivAt
  exact hp.add hn

theorem flatJumpEnergy_contDiff_one : ContDiff ℝ 1 flatJumpEnergy :=
  (integralEnergy_contDiff_one.comp edgeMap.contDiff).add
    (integralEnergy_contDiff_one.comp (-edgeMap).contDiff)

private theorem integralEnergy_zero_profile :
    integralEnergy (0 : Lp ℝ 2 edgeMeasure) = 0 := by
  apply (integralEnergy_zero_iff _).mpr
  filter_upwards [Lp.coeFn_zero ℝ 2 edgeMeasure] with e he
  simp only [he, Pi.zero_apply, le_refl]

/-- The nonlinear loss detects precisely the same constant direction as the full jump form. -/
theorem flatJumpEnergy_zero_iff (p : SourceGraph) :
    flatJumpEnergy p = 0 ↔ ∃ c : ℝ, p = constantLift c := by
  rw [← edge_zero_iff_constant]
  constructor
  · intro h
    have hp : integralEnergy (edgeMap p) = 0 := by
      unfold flatJumpEnergy at h
      linarith only [h, (integral_energy_bounds (edgeMap p)).1,
        (integral_energy_bounds (-edgeMap p)).1]
    have hn : integralEnergy (-edgeMap p) = 0 := by
      unfold flatJumpEnergy at h
      linarith only [h, (integral_energy_bounds (edgeMap p)).1,
        (integral_energy_bounds (-edgeMap p)).1]
    apply Lp.ext
    filter_upwards [(integralEnergy_zero_iff _).mp hp,
      (integralEnergy_zero_iff _).mp hn, Lp.coeFn_neg (edgeMap p),
      Lp.coeFn_zero ℝ 2 edgeMeasure] with e hp' hn' he hz
    rw [he] at hn'
    change p.val.snd e ≤ 0 at hp'
    change -p.val.snd e ≤ 0 at hn'
    rw [hz]
    change p.val.snd e = 0
    linarith only [hp', hn']
  · intro hp
    change integralEnergy p.val.snd + integralEnergy (-p.val.snd) = 0
    rw [hp, neg_zero, integralEnergy_zero_profile, add_zero]

/-- Global tangent support identifies zero first variation with the constant ground direction. -/
theorem flatJumpFirstVariation_zero_iff (p : SourceGraph) :
    flatJumpFirstVariation p = 0 ↔ ∃ c : ℝ, p = constantLift c := by
  constructor
  · intro h
    apply (flatJumpEnergy_zero_iff p).mp
    have hp := integral_support (0 : Lp ℝ 2 edgeMeasure) (edgeMap p)
    have hn := integral_support (0 : Lp ℝ 2 edgeMeasure) (-edgeMap p)
    rw [integralEnergy_zero_profile, zero_sub, inner_neg_right] at hp hn
    have hv := congrArg (fun L : SourceGraph →L[ℝ] ℝ => L p) h
    change inner ℝ (gradientLp (edgeMap p)) (edgeMap p) +
      inner ℝ (gradientLp (-edgeMap p)) (-edgeMap p) = 0 at hv
    have he : flatJumpEnergy p ≤ 0 := by
      unfold flatJumpEnergy
      linarith only [hp, hn, hv]
    exact le_antisymm he (flatJumpEnergy_bounds p).1
  · rintro ⟨c, rfl⟩
    have he : edgeMap (constantLift c) = 0 := constantLift_edge c
    have hg : gradientLp (0 : Lp ℝ 2 edgeMeasure) = 0 :=
      gradient_contraction.compLp_zero gradient_zero
    simp only [flatJumpFirstVariation, he, neg_zero, hg, map_zero,
      ContinuousLinearMap.zero_comp, add_zero]

/-- Adding a constant profile leaves every nonlinear arithmetic jump unchanged. -/
theorem flatJumpEnergy_add_constant (p : SourceGraph) (c : ℝ) :
    flatJumpEnergy (p + constantLift c) = flatJumpEnergy p := by
  have he : edgeMap (constantLift c) = 0 := constantLift_edge c
  simp only [flatJumpEnergy, map_add, he, add_zero]

/-- Apply the flat gradient to the source while retaining its literal complete edge difference. -/
def flatGradientGraph (p : SourceGraph) : SourceGraph :=
  _root_.RHTower.CHMDClosedJump.contract massMeasure edgeMeasure left right
    nonsingular_left nonsingular_right p gradient_contraction gradient_zero

/-- The nonlinear flat jump energy contracts under its source-gradient transform. -/
theorem flatJumpEnergy_gradient_contraction (p : SourceGraph) :
    flatJumpEnergy (flatGradientGraph p) ≤ flatJumpEnergy p := by
  rw [flatJumpEnergy_integral, flatJumpEnergy_integral]
  apply integral_mono_ae (integrable_even_edge _) (integrable_even_edge p)
  have he := _root_.RHTower.CHMDClosedJump.contract_edge_ae massMeasure edgeMeasure left right
    nonsingular_left nonsingular_right p gradient_contraction gradient_zero
  filter_upwards [he, p.property] with e he hp
  change (flatGradientGraph p).val.snd e = _ at he
  rw [he, hp]
  apply evenPotential_le_of_abs_le
  simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    gradient_contraction.norm_sub_le (p.val.fst (left e)) (p.val.fst (right e))

#print axioms flatJumpEnergy_bounds
#print axioms flatJumpEnergy_hasFDerivAt
#print axioms flatJumpEnergy_contDiff_one
#print axioms flatJumpEnergy_zero_iff
#print axioms flatJumpFirstVariation_zero_iff
#print axioms flatJumpEnergy_add_constant
#print axioms flatJumpEnergy_gradient_contraction
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
