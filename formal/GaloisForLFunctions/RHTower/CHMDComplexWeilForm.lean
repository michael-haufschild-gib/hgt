import GaloisForLFunctions.RHTower.CHMDComplexJumpGraph
import GaloisForLFunctions.RHTower.ThetaBVWeilForm

/-! # The full signed Weil form on the complex arithmetic graph

Real and imaginary projections land in the original complete real graph.
Their two original Weil energies give the complex quadratic form, including
the full archimedean integral, every prime power, negative mass and both
polar moments. No sign assumption is introduced.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.CHMDDoobGraph

abbrev ComplexSourceGraph := CHMDComplexJump.graph massMeasure edgeMeasure left right
  nonsingular_left nonsingular_right

/-- A real linear scalar observation preserves the literal arithmetic differences. -/
def scalarGraphMap (L : ℂ →L[ℝ] ℝ) : ComplexSourceGraph →L[ℝ] SourceGraph where
  toFun p := ⟨WithLp.toLp 2
    (L.compLpL 2 massMeasure p.val.fst, L.compLpL 2 edgeMeasure p.val.snd), by
      filter_upwards [p.property, L.coeFn_compLpL p.val.snd,
        nonsingular_left.ae (L.coeFn_compLpL p.val.fst),
        nonsingular_right.ae (L.coeFn_compLpL p.val.fst)] with e he hd hl hr
      change L.compLpL 2 edgeMeasure p.val.snd e =
        L.compLpL 2 massMeasure p.val.fst (left e) -
          L.compLpL 2 massMeasure p.val.fst (right e)
      rw [hd, hl, hr, he, map_sub]⟩
  map_add' p q := by
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' c p := by
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  cont := by
    apply Continuous.subtype_mk
    exact (WithLp.prod_continuous_toLp 2 _ _).comp
      (((L.compLpL 2 massMeasure).continuous.comp
        ((WithLp.continuous_fst 2 _ _).comp continuous_subtype_val)).prodMk
      ((L.compLpL 2 edgeMeasure).continuous.comp
        ((WithLp.continuous_snd 2 _ _).comp continuous_subtype_val)))

theorem scalarGraphMap_source (L : ℂ →L[ℝ] ℝ) (p : ComplexSourceGraph) :
    ((scalarGraphMap L p).val.fst : ℝ → ℝ) =ᵐ[massMeasure] (fun x => L (p.val.fst x)) :=
  L.coeFn_compLpL p.val.fst

theorem scalarGraphMap_edge (L : ℂ →L[ℝ] ℝ) (p : ComplexSourceGraph) :
    ((scalarGraphMap L p).val.snd : ℝ × ℝ → ℝ) =ᵐ[edgeMeasure]
      (fun e => L (p.val.snd e)) := L.coeFn_compLpL p.val.snd

/-- The original full real form on both scalar components. -/
def complexWeilEnergy (p : ComplexSourceGraph) : ℝ :=
  sourceWeilEnergy (scalarGraphMap Complex.reCLM p) +
    sourceWeilEnergy (scalarGraphMap Complex.imCLM p)

theorem continuous_complexWeilEnergy : Continuous complexWeilEnergy :=
  (continuous_sourceWeilEnergy.comp (scalarGraphMap Complex.reCLM).continuous).add
    (continuous_sourceWeilEnergy.comp (scalarGraphMap Complex.imCLM).continuous)

/-- The complete arithmetic expression on a real BV profile. -/
def fullBVWeilExpression (v : ℝ → ℝ) : ℝ :=
  phiDoobArchJumpEnergy v + (∑' n, ∫ x, phiDoobPrimeJump v n x) -
    phiDoobCoshMass (fun x => v x^2) +
      2*phiDoobCoshMass v^2 - 2*phiDoobSinhMass v^2

theorem scalarGraphMap_eq_bvLift (L : ℂ →L[ℝ] ℝ) (p : ComplexSourceGraph)
    (v : ℝ → ℂ) (hp : (p.val.fst : ℝ → ℂ) =ᵐ[massMeasure] v)
    (hv : BoundedVariationOn (fun x => L (v x)) univ) :
    scalarGraphMap L p = bvLift (fun x => L (v x)) hv := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [scalarGraphMap_source L p, hp, bvLift_source (fun x => L (v x)) hv]
    with x hx hp' hb
  exact hx.trans ((congrArg L hp').trans hb.symm)

/-- Exact full expression: no jump, prime-power tail, mass or polar term is dropped. -/
theorem complexWeilEnergy_eq_fullBV (p : ComplexSourceGraph) (v : ℝ → ℂ)
    (hp : (p.val.fst : ℝ → ℂ) =ᵐ[massMeasure] v)
    (hr : BoundedVariationOn (fun x => (v x).re) univ)
    (hi : BoundedVariationOn (fun x => (v x).im) univ) :
    complexWeilEnergy p = fullBVWeilExpression (fun x => (v x).re) +
      fullBVWeilExpression (fun x => (v x).im) := by
  rw [complexWeilEnergy, scalarGraphMap_eq_bvLift Complex.reCLM p v hp hr,
    scalarGraphMap_eq_bvLift Complex.imCLM p v hp hi,
    sourceWeilEnergy_bvLift, sourceWeilEnergy_bvLift]
  rfl

end RHTower.CHMDDoobGraph
