import GaloisForLFunctions.RHTower.SoninTimeBandSchatten
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import GaloisForLFunctions.RHTower.SummableEulerCalkinInjectivity
import GaloisForLFunctions.RHTower.SoninCoupledPrimeResidual
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogFullWeakTraceNoGo
import GaloisForLFunctions.HTGeometry.TelescopingPowerTrace

/-!
# Prime-labelled regularized Sonin nuclear heads

Source coefficients and prime/depth labels are not changed. No Xi or RH premise is used.
This module does not assert a determinant weld or an RH conclusion.
-/

open ContinuousLinearMap
namespace RHTower
noncomputable section

theorem traceNorm_centralSoninDilationCornerResidual_le_source
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    traceNorm SoninL2 (centralSoninDilationCornerResidual a p hp) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) := by
  let J := centralSoninProjectionCorrection a
  let L := (1 - centralSoninProjection a) * dilationSum p hp
  let R := dilationSum p hp * centralSoninFormalComplement a
  have hJ : MemSchattenClass 1 J :=
    centralSoninProjectionCorrection_memSchattenClass_one a ha
  have hL : ‖L‖ ≤ 2 := by
    exact (norm_mul_le _ _).trans
      ((mul_le_mul (norm_one_sub_centralSoninProjection_le_one a)
        (norm_dilationSum_le_two p hp) (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hR : ‖R‖ ≤ 2 := by
    exact (norm_mul_le _ _).trans
      ((mul_le_mul (norm_dilationSum_le_two p hp)
        (norm_centralSoninFormalComplement_le_one a) (norm_nonneg _)
        (by norm_num)).trans_eq (by ring))
  have hLJ : MemSchattenClass 1 (L * J) := memSchattenClass_one_comp_left hJ L
  have hJR : MemSchattenClass 1 (J * R) := memSchattenClass_one_comp_right hJ R
  have hneg : MemSchattenClass 1 (-(J * R)) := by
    simpa using memSchattenClass_one_smul hJR (-1)
  have hleft : traceNorm SoninL2 (L * J) ≤ 2 * traceNorm SoninL2 J :=
    (traceNorm_comp_left_le (by simpa [MemSchattenClass] using hJ) L).trans
      (mul_le_mul_of_nonneg_right hL (traceNorm_nonneg J))
  have hright : traceNorm SoninL2 (J * R) ≤ 2 * traceNorm SoninL2 J := by
    exact (traceNorm_comp_right_le (by simpa [MemSchattenClass] using hJ) R).trans
      ((mul_le_mul_of_nonneg_left hR (traceNorm_nonneg J)).trans_eq (by ring))
  have hnormneg : traceNorm SoninL2 (-(J * R)) = traceNorm SoninL2 (J * R) := by
    simpa using traceNorm_smul (-1 : ℂ) (J * R)
  have heq : centralSoninDilationCornerResidual a p hp = L * J + -(J * R) := by
    rw [centralSoninDilationCornerResidual_eq_correction_factorization]
    dsimp [L, J, R]
    noncomm_ring
  rw [heq]
  calc
    _ ≤ traceNorm SoninL2 (L * J) + traceNorm SoninL2 (-(J * R)) :=
      traceNorm_add_le (hLJ.isCompactOperator one_pos) (hneg.isCompactOperator one_pos)
        (by simpa [MemSchattenClass] using hLJ) (by simpa [MemSchattenClass] using hneg)
    _ ≤ 4 * traceNorm SoninL2 J := by rw [hnormneg]; linarith

theorem traceNorm_centralSoninWeightedPrimePowerResidual_le_source
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    traceNorm SoninL2 (centralSoninWeightedPrimePowerResidual a pk) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        ‖soninLogPrimePowerCoefficient pk‖ := by
  rw [centralSoninWeightedPrimePowerResidual, traceNorm_smul]
  have h := traceNorm_centralSoninDilationCornerResidual_le_source a
    (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)

end
end RHTower

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

section FiniteNuclearSum
variable {H E F ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem traceNorm_finsetSum_le (s : Finset ι) (A : ι → H →L[ℂ] H)
    (hA : ∀ i ∈ s, MemSchattenClass 1 (A i)) :
    traceNorm H (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm H (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [traceNorm, approxNumber_zero_op]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, MemSchattenClass 1 (A j) :=
      fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hsum := GaloisForLFunctions.HTGeometry.memSchattenClass_one_sum s A hs
    have hAi := hA i (Finset.mem_insert_self i s)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (traceNorm_add_le (hAi.isCompactOperator one_pos)
      (hsum.isCompactOperator one_pos) (by simpa [MemSchattenClass] using hAi)
      (by simpa [MemSchattenClass] using hsum)).trans (add_le_add le_rfl (ih hs))

omit [CompleteSpace E] [CompleteSpace F] in
theorem rectangularLowerBlock_finsetSum (s : Finset ι) (A : ι → E →L[ℂ] F) :
    rectangularLowerBlock (∑ i ∈ s, A i) = ∑ i ∈ s, rectangularLowerBlock (A i) := by
  classical
  ext x
  simp [rectangularLowerBlock, map_sum]

theorem memRectSchattenClass_one_finsetSum (s : Finset ι) (A : ι → E →L[ℂ] F)
    (hA : ∀ i ∈ s, MemRectSchattenClass 1 (A i)) :
    MemRectSchattenClass 1 (∑ i ∈ s, A i) := by
  classical
  rw [memRectSchattenClass_iff_lowerBlock, rectangularLowerBlock_finsetSum]
  exact GaloisForLFunctions.HTGeometry.memSchattenClass_one_sum s _ fun i hi =>
    (memRectSchattenClass_iff_lowerBlock 1 (A i)).mp (hA i hi)

theorem rectTraceNorm_finsetSum_le (s : Finset ι) (A : ι → E →L[ℂ] F)
    (hA : ∀ i ∈ s, MemRectSchattenClass 1 (A i)) :
    rectTraceNorm E F (∑ i ∈ s, A i) ≤ ∑ i ∈ s, rectTraceNorm E F (A i) := by
  simp_rw [rectTraceNorm_eq_traceNorm_lowerBlock]
  rw [rectangularLowerBlock_finsetSum]
  exact traceNorm_finsetSum_le s _ fun i hi =>
    (memRectSchattenClass_iff_lowerBlock 1 (A i)).mp (hA i hi)
end FiniteNuclearSum

local instance : DecidableEq SoninHilbertIndex := Classical.decEq _
local instance : DecidableEq SoninAllPrimeIndex := Classical.decEq _

def soninPrimeRowInclusion (pk : Nat.Primes × ℕ) : SoninL2 →ₗᵢ[ℂ] SoninAllPrimeL2 :=
  (lpScalarInjection (fun i : SoninHilbertIndex => (pk, i))
    (fun _ _ h => (Prod.mk.inj h).2)).comp
      (ContinuousLinearMap.hsBasis ℂ SoninL2).repr.toLinearIsometry

theorem soninPrimeRowInclusion_apply (pk qk : Nat.Primes × ℕ)
    (x : SoninL2) (i : SoninHilbertIndex) :
    soninPrimeRowInclusion pk x (qk, i) =
      if qk = pk then inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i) x else 0 := by
  classical
  change lpScalarInjection (fun j : SoninHilbertIndex => (pk, j))
      (fun _ _ h => (Prod.mk.inj h).2)
      ((ContinuousLinearMap.hsBasis ℂ SoninL2).repr x) (qk, i) = _
  by_cases h : qk = pk
  · subst qk
    rw [lpScalarInjection_coordinate, HilbertBasis.repr_apply_apply, if_pos rfl]
  · rw [if_neg h]
    apply lpScalarInjection_coordinate_eq_zero_of_not_mem_range
    rintro ⟨j, hj⟩
    exact h (congrArg Prod.fst hj).symm

def soninAllPrimeColumnFiniteHead (a : ℝ) (s : Finset (Nat.Primes × ℕ)) :
    SoninL2 →L[ℂ] SoninAllPrimeL2 :=
  ∑ pk ∈ s, (soninPrimeRowInclusion pk).toContinuousLinearMap ∘L
    centralSoninWeightedPrimePowerResidual a pk

theorem soninAllPrimeColumnFiniteHead_apply (a : ℝ)
    (s : Finset (Nat.Primes × ℕ)) (x : SoninL2)
    (pk : Nat.Primes × ℕ) (i : SoninHilbertIndex) :
    soninAllPrimeColumnFiniteHead a s x (pk, i) =
      if pk ∈ s then inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 i)
        (centralSoninWeightedPrimePowerResidual a pk x) else 0 := by
  classical
  simp only [soninAllPrimeColumnFiniteHead, sum_apply, comp_apply,
    lp.coeFn_sum, Finset.sum_apply, LinearIsometry.coe_toContinuousLinearMap,
    soninPrimeRowInclusion_apply]
  exact Finset.sum_ite_eq s pk _

theorem soninPrimeColumn_memRectSchattenClass_one (a : ℝ) (ha : 0 < a)
    (pk : Nat.Primes × ℕ) :
    MemRectSchattenClass 1 ((soninPrimeRowInclusion pk).toContinuousLinearMap ∘L
      centralSoninWeightedPrimePowerResidual a pk) := by
  rw [memRectSchattenClass_one_iff]
  apply summable_rectApproxNumber_comp_left
  rw [← memRectSchattenClass_one_iff, memRectSchattenClass_iff_memSchattenClass]
  exact (centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal a ha pk).memSchattenClass_one

theorem rectTraceNorm_soninPrimeColumn_le_source (a : ℝ) (ha : 0 < a)
    (pk : Nat.Primes × ℕ) :
    rectTraceNorm SoninL2 SoninAllPrimeL2
      ((soninPrimeRowInclusion pk).toContinuousLinearMap ∘L
        centralSoninWeightedPrimePowerResidual a pk) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        ‖soninLogPrimePowerCoefficient pk‖ := by
  have hmem : MemSchattenClass 1 (centralSoninWeightedPrimePowerResidual a pk) :=
    (centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal a ha pk).memSchattenClass_one
  have hsum : Summable fun n => rectApproxNumber
      (centralSoninWeightedPrimePowerResidual a pk) n := by
    rw [← memRectSchattenClass_one_iff, memRectSchattenClass_iff_memSchattenClass]
    exact hmem
  have hnorm : ‖(soninPrimeRowInclusion pk).toContinuousLinearMap‖ ≤ 1 :=
    (soninPrimeRowInclusion pk).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖(soninPrimeRowInclusion pk).toContinuousLinearMap‖ *
        rectTraceNorm SoninL2 SoninL2 (centralSoninWeightedPrimePowerResidual a pk) :=
      rectTraceNorm_comp_left_le hsum _
    _ ≤ 1 * rectTraceNorm SoninL2 SoninL2
        (centralSoninWeightedPrimePowerResidual a pk) :=
      mul_le_mul_of_nonneg_right hnorm (rectTraceNorm_nonneg _)
    _ ≤ _ := by
      rw [one_mul, rectTraceNorm_eq_traceNorm]
      exact traceNorm_centralSoninWeightedPrimePowerResidual_le_source a ha pk

theorem soninAllPrimeColumnFiniteHead_memRectSchattenClass_one
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    MemRectSchattenClass 1 (soninAllPrimeColumnFiniteHead a s) :=
  memRectSchattenClass_one_finsetSum s _ fun pk _ =>
    soninPrimeColumn_memRectSchattenClass_one a ha pk

theorem rectTraceNorm_soninAllPrimeColumnFiniteHead_le_source
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    rectTraceNorm SoninL2 SoninAllPrimeL2 (soninAllPrimeColumnFiniteHead a s) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        ∑ pk ∈ s, ‖soninLogPrimePowerCoefficient pk‖ := by
  refine (rectTraceNorm_finsetSum_le s _
    (fun pk _ => soninPrimeColumn_memRectSchattenClass_one a ha pk)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun pk _ => rectTraceNorm_soninPrimeColumn_le_source a ha pk

end
end RHTower

