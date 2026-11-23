import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.RankReadings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.HeatSingularValues
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.Interlacing
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.StrictDeficit
import GaloisForLFunctions.RHTower.ConnesConsaniTraceClassReduction

/-! # Finite-dimensional ceiling for the fourth-trace deficit

The error in squared heat factors through the actual missing subspace.
Injectivity of a conserving propagator makes the interlacing bound strict.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

/-- Squared-heat error factors through the image under heat of the omitted directions. -/
theorem squareError_rank (P : Projection) {r : ℕ} (hd : MissingDimension P r) :
    _root_.RHTower.HasRankLE (squareHeat.val-(projected P)^2) r := by
  obtain ⟨hfd,he⟩ := hd
  let W := P.val.toLinearMap.ker
  letI : FiniteDimensional ℂ W := hfd
  refine ⟨W.map criticalOperator.toLinearMap,inferInstance,(Submodule.finrank_map_le _ W).trans he.le,?_⟩
  intro x
  let u := criticalOperator x
  have hu : u-P.val u ∈ W := by
    change P.val (u-P.val u) = 0
    rw [map_sub,show P.val (P.val u) = P.val u from congrArg (fun T : GasOp => T u) P.property.isIdempotentElem.eq,sub_self]
  refine ⟨_,hu,?_⟩
  rw [projected_square]
  change criticalOperator (u-P.val u) = criticalOperator u-criticalOperator (P.val u)
  exact map_sub _ _ _

private theorem projected_ne_of_rank {P : Projection} {r : ℕ} (hd : MissingDimension P r) (hr : 0 < r) :
    projected P ≠ criticalOperator := by
  intro he
  have hz := (missingDimension_zero_iff P).mpr ((projected_eq_critical_iff P).mp he)
  exact hr.ne (hz.2.symm.trans hd.2)

private theorem loss_eq_mass {T : GasOp} (hs : IsSelfAdjoint T) (hh : (T^2).IsHilbertSchmidt) :
    traceLoss T = hsNormSq squareHeat.val-hsNormSq (T^2) := by
  have ha := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq squareHeat.property.2 squareHeat.property.1.star_eq
  have hb := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hh (hs.pow 2).star_eq
  change opTrace ((criticalOperator^2)^2) = _ at ha
  rw [critical_fourth_trace] at ha
  rw [traceLoss,ha,show (4:ℕ) = 2*2 from rfl,pow_mul,hb,Complex.ofReal_re,Complex.ofReal_re]

/-- Fixing a positive finite missing dimension gives a strict ceiling at the sum of the
first squared occupation weights. -/
theorem lossesAtRank_subset (r : ℕ) (hr : 0 < r) : lossesAtRank r ⊆ Set.Ioo 0 (traceCeiling r) := by
  rintro y ⟨P,hd,hc,rfl⟩
  have hn := projected_ne_of_rank hd hr
  let G : Propagator := ⟨projected P,projected_positive P,hc⟩
  have hpos := (strict_trace_stability_iff G).mpr hn
  refine ⟨lt_of_le_of_lt (by positivity) hpos,?_⟩
  have hf := squareError_rank P hd
  have hh := squareHeat.property.2.sub (_root_.RHTower.isHilbertSchmidt_of_hasRankLE hf)
  rw [sub_sub_cancel] at hh
  have hsa := (projected_positive P).isSelfAdjoint
  have hi : Function.Injective ((projected P)^2 : GasOp) := by
    rw [projected_square]
    exact critical_injective.comp ((projected_conserves_iff P).mp hc)
  have hdiff : squareHeat.val ≠ (projected P)^2 := by
    intro he
    have h := congrArg (fun T : GasOp => positiveRoot T) he
    change positiveRoot (criticalOperator^2) = _ at h
    rw [positiveRoot_sq critical_isPositive,positiveRoot_sq (projected_positive P)] at h
    exact hn h.symm
  have hb := hs_loss_lt_head squareHeat.property.2 hh (hsa.pow 2) hi hdiff hf
  simpa only [loss_eq_mass hsa hh,traceCeiling,squareHeat_approxNumber] using hb

#print axioms squareError_rank
#print axioms lossesAtRank_subset

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
