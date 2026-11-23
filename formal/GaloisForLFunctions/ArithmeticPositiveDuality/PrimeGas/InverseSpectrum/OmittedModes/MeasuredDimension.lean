import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.RankReadings
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum

/-! # Omitted dimension is the algebraic rank of the observed square difference

The projected heat range is dense in the missing subspace. If either
has finite dimension they coincide. Left multiplication by heat is injective.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap Set

def exactRank (T : GasOp) (r : ℕ) : Prop :=
  FiniteDimensional ℂ T.toLinearMap.range ∧ Module.finrank ℂ T.toLinearMap.range = r

/-- The projection kernel and the difference of squares have exactly the same finite ranks. -/
theorem missingDimension_iff_squareRank (P : Projection) (r : ℕ) :
    MissingDimension P r ↔ exactRank (squareHeat.val-(projected P)^2) r := by
  let Q : GasOp := 1-P.val
  let Z := (Q*criticalOperator).toLinearMap.range
  let W := P.val.toLinearMap.ker
  have hZ : Z ≤ W := by
    rintro x ⟨u,rfl⟩
    change P.val (criticalOperator u-P.val (criticalOperator u)) = 0
    rw [map_sub,show P.val (P.val (criticalOperator u)) = P.val (criticalOperator u) from
      congrArg (fun T : GasOp => T (criticalOperator u)) P.property.isIdempotentElem.eq,sub_self]
  have hclosed [FiniteDimensional ℂ Z] : Z = W := by
    apply le_antisymm hZ
    intro x hx
    have hD := HTGeometry.denseRange_of_isSelfAdjoint_of_injective critical_isPositive.isSelfAdjoint critical_injective
    have him : Q '' Set.range criticalOperator ⊆ (Z : Set Gas) := by
      rintro _ ⟨_,⟨u,rfl⟩,rfl⟩
      exact ⟨u,rfl⟩
    have he := closure_mono him (mem_closure_image Q.continuous.continuousAt (hD x))
    rw [Z.closed_of_finiteDimensional.closure_eq] at he
    have hp : P.val x = 0 := hx
    have he' : Q x ∈ Z := he
    have hqx : Q x = x := by change x-P.val x = x; rw [hp,sub_zero]
    exact hqx ▸ he'
  let C := squareHeat.val-(projected P)^2
  have hval (u : Gas) : C u = criticalOperator (Q (criticalOperator u)) := by
    dsimp only [C]
    rw [projected_square]
    change criticalOperator (criticalOperator u)-criticalOperator (P.val (criticalOperator u)) =
      criticalOperator (criticalOperator u-P.val (criticalOperator u))
    exact (map_sub _ _ _).symm
  have hrange : C.toLinearMap.range = Z.map criticalOperator.toLinearMap := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨_,⟨u,rfl⟩,(hval u).symm⟩
    · rintro ⟨_,⟨u,rfl⟩,rfl⟩
      exact ⟨u,hval u⟩
  let e := Submodule.equivMapOfInjective criticalOperator.toLinearMap critical_injective Z
  change (FiniteDimensional ℂ W ∧ Module.finrank ℂ W = r) ↔
    FiniteDimensional ℂ C.toLinearMap.range ∧ Module.finrank ℂ C.toLinearMap.range = r
  rw [hrange]
  constructor
  · rintro ⟨hW,hd⟩
    letI : FiniteDimensional ℂ Z := FiniteDimensional.of_injective (Submodule.inclusion hZ)
      (Submodule.inclusion_injective hZ)
    exact ⟨FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective,
      e.finrank_eq.symm.trans ((congrArg (fun V : Submodule ℂ Gas => Module.finrank ℂ V) hclosed).trans hd)⟩
  · rintro ⟨hC,hd⟩
    letI : FiniteDimensional ℂ Z := FiniteDimensional.of_injective e.toLinearMap e.injective
    rw [← hclosed]
    exact ⟨inferInstance,e.finrank_eq.trans hd⟩

/-- Fourth-trace readings can be indexed directly by the squared propagator error. -/
theorem lossesAtRank_by_squares (r : ℕ) : lossesAtRank r =
    {y | ∃ G : Propagator, exactRank (squareHeat.val-G.val^2) r ∧ traceLoss G.val = y} := by
  ext y
  constructor
  · rintro ⟨P,hd,hc,he⟩
    exact ⟨⟨projected P,projected_positive P,hc⟩,(missingDimension_iff_squareRank P r).mp hd,he⟩
  · rintro ⟨G,hd,he⟩
    obtain ⟨P,⟨hi,hP⟩,_⟩ := (positive_propagators_iff G.val).mp G.property
    rw [hP] at hd he
    exact ⟨P,(missingDimension_iff_squareRank P r).mpr hd,(projected_conserves_iff P).mpr hi,he⟩

#print axioms lossesAtRank_by_squares
#print axioms missingDimension_iff_squareRank

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
