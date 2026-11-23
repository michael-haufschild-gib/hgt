import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.FullSpace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Compression
import GaloisForLFunctions.HTGeometry.OperatorFredholmGerm
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.PositiveRoot

/-!
# The fourth trace measures the missing range

The trace of the squared input Gram operator is bounded by zeta at two.
Its exact deficit measures the part of the square heat missed by the range
isometry. Attainment recovers the positive critical Gibbs operator.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

def fourthMoment (G : GasOp) : ℂ := opTrace ((star G*G)^2)

private theorem critical_sa : IsSelfAdjoint criticalOperator := critical_isPositive.isSelfAdjoint

def squareHeat : HSObservable Gas := ⟨criticalOperator^2,critical_sa.pow 2,critical_square_hs⟩

private theorem squareHeat_injective : Function.Injective squareHeat.val :=
  critical_injective.comp critical_injective

private theorem zeta_two : (hsNormSq squareHeat.val:ℂ) = riemannZeta 2 :=
  (_root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq squareHeat.property.2 squareHeat.property.1.star_eq).symm.trans
    critical_fourth_trace

private theorem input_gram (U : Gas →ₗᵢ[ℂ] Gas) :
    star (criticalOperator*U.toContinuousLinearMap)*(criticalOperator*U.toContinuousLinearMap) =
      star U.toContinuousLinearMap*(squareHeat.val*U.toContinuousLinearMap) := by
  rw [star_mul,critical_sa.star_eq]
  change _ = star U.toContinuousLinearMap*(criticalOperator^2*U.toContinuousLinearMap)
  rw [pow_two,mul_assoc,mul_assoc]

private theorem fourth_factor (U : Gas →ₗᵢ[ℂ] Gas) :
    fourthMoment (criticalOperator*U.toContinuousLinearMap) =
      (hsNormSq (star U.toContinuousLinearMap*(squareHeat.val*U.toContinuousLinearMap)):ℂ) := by
  let V := U.toContinuousLinearMap
  have hs : (star V*(squareHeat.val*V)).IsHilbertSchmidt :=
    (squareHeat.property.2.comp_right V).comp_left (star V)
  rw [fourthMoment,input_gram]
  apply _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hs
  change star (star V*(squareHeat.val*V)) = _
  rw [star_mul,star_mul,star_star,squareHeat.property.1.star_eq,mul_assoc]

/-- Every omitted direction contributes a nonnegative term to the exact fourth-trace deficit. -/
theorem fourth_trace_defect (U : Gas →ₗᵢ[ℂ] Gas) :
    (riemannZeta 2).re-(fourthMoment (criticalOperator*U.toContinuousLinearMap)).re =
      hsNormSq (omitted U*squareHeat.val)+hsNormSq (omitted U*(squareHeat.val*U.toContinuousLinearMap)) := by
  rw [← zeta_two,fourth_factor,Complex.ofReal_re,Complex.ofReal_re]
  exact compression_loss U squareHeat

theorem omitted_zero_iff (U : Gas →ₗᵢ[ℂ] Gas) : omitted U = 0 ↔ Function.Surjective U := by
  let V := U.toContinuousLinearMap
  change 1-V*star V = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h x
    exact ⟨(star V) x,congrArg (fun B : GasOp => B x) h.symm⟩
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := h x
    have hi := congrArg (fun B : GasOp => B y) U.adjoint_comp_self
    change star V (V y) = y at hi
    change V y = V ((star V) (V y))
    rw [hi]

private theorem misses_square_iff (U : Gas →ₗᵢ[ℂ] Gas) :
    omitted U*squareHeat.val = 0 ↔ omitted U = 0 := by
  constructor
  · intro h
    have hs := congrArg star h
    rw [star_mul,squareHeat.property.1.star_eq,omitted_self,star_zero] at hs
    apply ContinuousLinearMap.ext
    intro f
    apply squareHeat_injective
    have hh := congrArg (fun A : GasOp => A f) hs
    change squareHeat.val ((omitted U) f) = 0 at hh
    change squareHeat.val ((omitted U) f) = squareHeat.val 0
    rwa [map_zero]
  · intro h
    rw [h,zero_mul]

/-- A single full-space fourth moment detects whether the range isometry is onto. -/
theorem fourth_trace_eq_iff (U : Gas →ₗᵢ[ℂ] Gas) :
    fourthMoment (criticalOperator*U.toContinuousLinearMap) = riemannZeta 2 ↔ Function.Surjective U := by
  rw [fourth_factor,← zeta_two,Complex.ofReal_inj,compression_eq_iff,misses_square_iff,omitted_zero_iff]

/-- The sharp upper bound holds for every bounded propagator conserving cyclic-order probability. -/
theorem fourth_trace_bound (G : {G : GasOp // Conserving G}) : (fourthMoment G.val).re ≤ (riemannZeta 2).re := by
  obtain ⟨U,hu,_⟩ := (full_isometry_iff G.val).mp G.property
  rw [hu]
  have h := fourth_trace_defect U
  linarith only [h,hsNormSq_nonneg (omitted U*squareHeat.val),
    hsNormSq_nonneg (omitted U*(squareHeat.val*U.toContinuousLinearMap))]

private theorem output_square {G : GasOp} {U : Gas →ₗᵢ[ℂ] Gas}
    (hg : G = criticalOperator*U.toContinuousLinearMap) (hr : Function.Surjective U) :
    G*star G = criticalOperator^2 := by
  have h := (omitted_zero_iff U).mpr hr
  change 1-U.toContinuousLinearMap*star U.toContinuousLinearMap = 0 at h
  rw [hg,star_mul,critical_sa.star_eq,mul_assoc,← mul_assoc U.toContinuousLinearMap,
    (sub_eq_zero.mp h).symm,one_mul,pow_two]

theorem moment_eq_iff_re (G : {G : GasOp // Conserving G}) :
    fourthMoment G.val = riemannZeta 2 ↔ (fourthMoment G.val).re = (riemannZeta 2).re := by
  obtain ⟨U,hu,_⟩ := (full_isometry_iff G.val).mp G.property
  rw [hu,fourth_factor,← zeta_two,Complex.ofReal_inj,Complex.ofReal_re,Complex.ofReal_re]

theorem fourthMoment_of_positive {G : GasOp} (hp : G.IsPositive) : fourthMoment G = opTrace (G^4) := by
  rw [fourthMoment,hp.isSelfAdjoint.star_eq,← pow_two,← pow_mul]

/-- Positive propagation, full isometry, and one trace recover all shell coordinates and amplitudes. -/
theorem positive_fourth_iff (G : GasOp) :
    G.IsPositive ∧ Conserving G ∧ opTrace (G^4) = riemannZeta 2 ↔ G = criticalOperator := by
  constructor
  · rintro ⟨hp,hi,ht⟩
    obtain ⟨U,hu,_⟩ := (full_isometry_iff G).mp hi
    have hz := (fourthMoment_of_positive hp).trans ht
    rw [hu] at hz
    have hs := output_square hu ((fourth_trace_eq_iff U).mp hz)
    rw [hp.isSelfAdjoint.star_eq,← pow_two] at hs
    exact (positiveRoot_sq hp).symm.trans
      ((congrArg (fun A : GasOp => positiveRoot A) hs).trans (positiveRoot_sq critical_isPositive))
  · rintro rfl
    refine ⟨critical_isPositive,?_,?_⟩
    · have h := conserves_factor (LinearIsometry.id : Gas →ₗᵢ[ℂ] Gas)
      change Conserving (criticalOperator*1) at h
      rwa [mul_one] at h
    · simpa only [← pow_mul] using critical_fourth_trace

#print axioms fourth_trace_defect
#print axioms fourth_trace_bound
#print axioms fourth_trace_eq_iff
#print axioms positive_fourth_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
