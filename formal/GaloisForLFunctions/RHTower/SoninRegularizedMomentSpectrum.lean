import GaloisForLFunctions.HTGeometry.OrderedPositiveMomentDetermination
import GaloisForLFunctions.RHTower.SoninRegularizedDiagonalPrefix
import GaloisForLFunctions.RHTower.SoninAllPrimeMomentApertureContinuity
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant
import GaloisForLFunctions.RHTower.CanonicalXiSeamLogEquivalence
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiOrderedPrimePartialTraceAsymptotics
import GaloisForLFunctions.RHTower.XiOrderedPrimeSchattenThreshold
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.HTGeometry.RectangularGramSpectrum
import GaloisForLFunctions.HTGeometry.LidskiiPowerTrace
import GaloisForLFunctions.HTGeometry.RegularizedResolventTraceOperator

/-!
# Exact regularized source and reciprocal-Xi spectral moments

The source identities have no RH premise. The reciprocal-Xi identification explicitly takes RH;
its callers must discharge that premise. Both reflection signs and all multiplicities remain.
-/

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

theorem opTrace_energyOp_pow_eq_approxNumber_moments
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →L[ℂ] H} (hA : A.IsHilbertSchmidt) (r : ℕ) :
    opTrace (energyOp A ^ (r + 1)) =
      ∑' n : ℕ, (((approxNumber A n ^ 2 : ℝ) : ℂ) ^ (r + 1)) := by
  have hpos : (energyOp A).IsPositive := isPositive_adjoint_comp_self A
  have hsplit : energyOp A ^ (r + 1) =
      A.adjoint ∘L (A ∘L energyOp A ^ r) := by
    rw [pow_succ']
    rfl
  rw [opTrace_pow_eq_tsum_sgVal_pow (energyOp_compact hA.isCompactOperator)
    hpos.isSymmetric (Nat.succ_pos r) hA.adjoint (hA.comp_right _) hsplit]
  apply tsum_congr
  intro n
  have hs : sgVal (energyOp A) n = approxNumber A n ^ 2 := by
    rw [approxNumber_sq_eq_approxNumber_energyOp hA.isCompactOperator,
      approxNumber_eq_singVal (energyOp_compact hA.isCompactOperator),
      ← abs_sgVal_eq_singVal (energyOp_compact hA.isCompactOperator) hpos.isSymmetric,
      abs_of_nonneg (sgVal_nonneg_of_isPositive hpos n)]
  rw [hs]

theorem soninAllPrimeEnergyMoment_eq_opTrace_energyOp_pow
    (a : ℝ) (ha : 0 < a) (r : ℕ) :
    soninAllPrimeEnergyMoment a r =
      opTrace (energyOp (soninAllPrimeResidualOperator a ha) ^ (r + 1)) := by
  classical
  let A := soninAllPrimeResidualOperator a ha
  have hA := soninAllPrimeResidualOperator_isHilbertSchmidt a ha
  have hU : HilbertSchmidt.toOperator (soninAllPrimeResidualEnergyKernel_isHS a ha) =
      energyOp A := by
    change HilbertSchmidt.toOperator (HilbertSchmidt.isHS_hsComp
      (HilbertSchmidt.isHS_hsAdjoint (soninAllPrimeResidualKernel_isHS a ha))
      (soninAllPrimeResidualKernel_isHS a ha)) = _
    rw [HilbertSchmidt.toOperator_hsComp (HilbertSchmidt.isHS_hsAdjoint
        (soninAllPrimeResidualKernel_isHS a ha)) (soninAllPrimeResidualKernel_isHS a ha),
      ← HilbertSchmidt.adjoint_toOperator]
    rfl
  have hp : HilbertSchmidt.toOperator (HilbertSchmidt.isHS_hsPow
      (soninAllPrimeResidualEnergyKernel_isHS a ha) r) = energyOp A ^ (r + 1) := by
    rw [HilbertSchmidt.toOperator_hsPow (soninAllPrimeResidualEnergyKernel_isHS a ha) r, hU]
  have hsplit : energyOp A ^ (r + 1) = A.adjoint ∘L (A ∘L energyOp A ^ r) := by
    rw [pow_succ']; rfl
  have hmatrix : HilbertSchmidt.matrixOf (A.adjoint ∘L (A ∘L energyOp A ^ r)) =
      HilbertSchmidt.hsPow (soninAllPrimeResidualEnergyKernel a) r := by
    rw [← hsplit, ← hp, HilbertSchmidt.matrixOf_toOperator]
  change _ = opTrace (energyOp A ^ (r + 1))
  rw [hsplit, HilbertSchmidt.opTrace_comp_eq_tsum_matrixOf hA.adjoint (hA.comp_right _),
    hmatrix]
  rfl

theorem soninAllPrimeEnergyMoment_eq_approxNumber_moments
    (a : ℝ) (ha : 0 < a) (r : ℕ) :
    soninAllPrimeEnergyMoment a r =
      ∑' n : ℕ, (((approxNumber (soninAllPrimeResidualOperator a ha) n ^ 2 : ℝ) : ℂ) ^
        (r + 1)) := by
  rw [soninAllPrimeEnergyMoment_eq_opTrace_energyOp_pow]
  exact opTrace_energyOp_pow_eq_approxNumber_moments
    (soninAllPrimeResidualOperator_isHilbertSchmidt a ha) r

theorem xiZeroCopyReciprocalSquare_orderedPrime_eq_norm_sq_of_rh
    (hRH : RiemannHypothesis) (i : RouteKSignedPrimeIndex) :
    xiZeroCopyReciprocalSquare (xiOrderedSignedPrimeZeroCopyEquiv i) =
      ((‖xiOrderedSignedPrimeMultiplier i‖ ^ 2 : ℝ) : ℂ) := by
  rw [xiZeroCopyReciprocalSquare,
    xiSpectralPoint_orderedSignedPrimeZeroCopyEquiv_eq_of_rh hRH, inv_inv]
  cases i <;> simp [xiOrderedSignedPrimeMultiplier, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

theorem normalizedPrimeArchMoment_eq_orderedXi_approxNumber_moments_of_rh
    (hRH : RiemannHypothesis) (r : ℕ) :
    (normalizedPrimeArchMoment r : ℂ) =
      ∑' n : ℕ, (((approxNumber xiOrderedSignedPrimeOperator n ^ 2 : ℝ) : ℂ) ^
        (r + 1)) := by
  let e := routeKSignedPrimeEquiv.trans xiOrderedSignedPrimeZeroCopyEquiv
  rw [normalizedPrimeArchMoment_coe_eq_xiCentralReciprocalMoment,
    ← tsum_xiZeroCopyReciprocalSquare_pow]
  rw [← e.tsum_eq (fun q => xiZeroCopyReciprocalSquare q ^ (r + 1))]
  apply tsum_congr
  intro n
  simp only [e, Equiv.trans_apply, xiZeroCopyReciprocalSquare_orderedPrime_eq_norm_sq_of_rh hRH,
    norm_xiOrderedSignedPrimeMultiplier, Equiv.symm_apply_apply,
    xiOrderedSignedPrimeOperator_approxNumber]

end
end RHTower
