import GaloisForLFunctions.RHTower.SoninRegularizedSpectralPrefix

/-!
# Exact prime-labelled diagonal Sonin head and tail budgets

The original weighted blocks, including prime/depth labels, are retained. The discarded
Hilbert--Schmidt mass equals that of the common-input column without identifying the operators.
No Xi, moment-matching, or RH premise is used.
-/

open ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section
local instance : DecidableEq SoninAllPrimeIndex := Classical.decEq _

theorem soninPrimeRowInclusion_adjoint_single (pk qk : Nat.Primes × ℕ)
    (j : SoninHilbertIndex) :
    (soninPrimeRowInclusion pk).toContinuousLinearMap.adjoint
      (lp.single 2 (qk, j) (1 : ℂ)) =
        if qk = pk then hsBasis ℂ SoninL2 j else 0 := by
  classical
  apply ext_inner_left ℂ
  intro x
  rw [adjoint_inner_right, lp.inner_single_right]
  change inner ℂ (soninPrimeRowInclusion pk x (qk, j)) (1 : ℂ) = _
  rw [soninPrimeRowInclusion_apply]
  by_cases h : qk = pk
  · simp [h, RCLike.inner_apply, inner_conj_symm]
  · simp [h]

def soninPrimeDiagonalBlock (a : ℝ) (pk : Nat.Primes × ℕ) :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  ((soninPrimeRowInclusion pk).toContinuousLinearMap ∘L
    centralSoninWeightedPrimePowerResidual a pk) ∘L
      (soninPrimeRowInclusion pk).toContinuousLinearMap.adjoint

theorem soninPrimeDiagonalBlock_memSchattenClass_one
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    MemSchattenClass 1 (soninPrimeDiagonalBlock a pk) := by
  rw [← memRectSchattenClass_iff_memSchattenClass, memRectSchattenClass_one_iff]
  apply summable_rectApproxNumber_comp_right
  exact (memRectSchattenClass_one_iff _).mp (soninPrimeColumn_memRectSchattenClass_one a ha pk)

theorem traceNorm_soninPrimeDiagonalBlock_le_source
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    traceNorm SoninAllPrimeL2 (soninPrimeDiagonalBlock a pk) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        ‖soninLogPrimePowerCoefficient pk‖ := by
  rw [← rectTraceNorm_eq_traceNorm]
  have hs := (memRectSchattenClass_one_iff _).mp
    (soninPrimeColumn_memRectSchattenClass_one a ha pk)
  have hn : ‖(soninPrimeRowInclusion pk).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (soninPrimeRowInclusion pk).norm_toContinuousLinearMap_le
  exact (rectTraceNorm_comp_right_le hs _).trans
    ((mul_le_mul_of_nonneg_left hn (rectTraceNorm_nonneg _)).trans
      (by simpa using rectTraceNorm_soninPrimeColumn_le_source a ha pk))

def soninAllPrimeDiagonalFiniteHead (a : ℝ) (s : Finset (Nat.Primes × ℕ)) :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 := ∑ pk ∈ s, soninPrimeDiagonalBlock a pk

theorem soninAllPrimeDiagonalFiniteHead_memSchattenClass_one
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    MemSchattenClass 1 (soninAllPrimeDiagonalFiniteHead a s) :=
  GaloisForLFunctions.HTGeometry.memSchattenClass_one_sum s _
    (fun pk _ => soninPrimeDiagonalBlock_memSchattenClass_one a ha pk)

theorem traceNorm_soninAllPrimeDiagonalFiniteHead_le_source
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    traceNorm SoninAllPrimeL2 (soninAllPrimeDiagonalFiniteHead a s) ≤
      4 * traceNorm SoninL2 (centralSoninProjectionCorrection a) *
        ∑ pk ∈ s, ‖soninLogPrimePowerCoefficient pk‖ := by
  refine (traceNorm_finsetSum_le s _
    (fun pk _ => soninPrimeDiagonalBlock_memSchattenClass_one a ha pk)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun pk _ => traceNorm_soninPrimeDiagonalBlock_le_source a ha pk

theorem soninAllPrimeDiagonalFiniteHead_single (a : ℝ)
    (s : Finset (Nat.Primes × ℕ)) (pk qk : Nat.Primes × ℕ)
    (i j : SoninHilbertIndex) :
    soninAllPrimeDiagonalFiniteHead a s (lp.single 2 (qk, j) (1 : ℂ)) (pk, i) =
      if qk ∈ s then soninAllPrimeResidualKernel a ((pk, i), (qk, j)) else 0 := by
  classical
  simp only [soninAllPrimeDiagonalFiniteHead, sum_apply, soninPrimeDiagonalBlock,
    comp_apply, soninPrimeRowInclusion_adjoint_single,
    lp.coeFn_sum, Finset.sum_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, soninPrimeRowInclusion_apply]
  rw [Finset.sum_ite_eq]
  by_cases he : pk = qk
  · subst pk
    simp [soninAllPrimeResidualKernel]
  · simp [soninAllPrimeResidualKernel, he, Ne.symm he]

theorem soninAllPrimeDiagonalTail_eq_sourceProjection
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s =
      GaloisForLFunctions.HTGeometry.lpCoordinateProjection
        {z : SoninAllPrimeIndex | z.1 ∉ s} ∘L soninAllPrimeResidualOperator a ha := by
  classical
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis SoninAllPrimeIndex).dense_span) ?_
  rintro _ ⟨⟨qk, j⟩, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  apply lp.ext
  funext z
  rcases z with ⟨pk, i⟩
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
    soninAllPrimeDiagonalFiniteHead_single, comp_apply,
    GaloisForLFunctions.HTGeometry.lpCoordinateProjection_apply]
  simp only [soninAllPrimeResidualOperator, HilbertSchmidt.toOperator_single]
  by_cases he : pk = qk
  · subst pk
    by_cases h : qk ∈ s <;>
      simp [Set.indicator, h]
  · simp [soninAllPrimeResidualKernel, he, Set.indicator]

theorem soninAllPrimeDiagonalTail_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    IsHilbertSchmidt
      (soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s) := by
  rw [soninAllPrimeDiagonalTail_eq_sourceProjection]
  exact (soninAllPrimeResidualOperator_isHilbertSchmidt a ha).comp_left _

theorem soninAllPrimeDiagonalTail_single
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ))
    (pk : Nat.Primes × ℕ) (j : SoninHilbertIndex) :
    (soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s)
      (lp.single 2 (pk, j) (1 : ℂ)) =
      if pk ∈ s then 0 else soninPrimeRowInclusion pk
        (centralSoninWeightedPrimePowerResidual a pk (hsBasis ℂ SoninL2 j)) := by
  classical
  apply lp.ext
  funext z
  rcases z with ⟨qk, i⟩
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply,
    soninAllPrimeDiagonalFiniteHead_single, soninAllPrimeResidualOperator,
    HilbertSchmidt.toOperator_single]
  by_cases h : pk ∈ s
  · simp [h]
  · simp only [if_neg h, sub_zero, soninPrimeRowInclusion_apply]
    by_cases he : qk = pk
    · subst qk
      simp [soninAllPrimeResidualKernel]
    · simp [soninAllPrimeResidualKernel, he]

theorem hsNormSq_soninAllPrimeDiagonalTail_eq_blockTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    hsNormSq (soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s) =
      ∑' pk : Nat.Primes × ℕ, if pk ∈ s then 0 else
        hsNormSq (centralSoninWeightedPrimePowerResidual a pk) := by
  classical
  let T := soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s
  let b := HilbertSchmidt.lpBasis SoninAllPrimeIndex
  have hT := soninAllPrimeDiagonalTail_isHilbertSchmidt a ha s
  have hs : Summable (fun z : SoninAllPrimeIndex => ‖T (b z)‖ ^ 2) := hT.summable b
  rw [hsNormSq_eq hT b, hs.tsum_prod]
  apply tsum_congr
  intro pk
  by_cases h : pk ∈ s
  · simp only [T, b, HilbertSchmidt.lpBasis_apply, soninAllPrimeDiagonalTail_single,
      if_pos h, norm_zero, zero_pow (by decide : 2 ≠ 0), tsum_zero]
  · rw [if_neg h, hsNormSq_eq
      (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk)
      (hsBasis ℂ SoninL2)]
    apply tsum_congr
    intro j
    simp only [T, b, HilbertSchmidt.lpBasis_apply, soninAllPrimeDiagonalTail_single,
      if_neg h, LinearIsometry.norm_map]

theorem hsNormSq_soninAllPrimeDiagonalTail_eq_columnTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    hsNormSq (soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s) =
      hsNormSq (soninAllPrimeColumnOperator a ha - soninAllPrimeColumnFiniteHead a s) := by
  rw [hsNormSq_soninAllPrimeDiagonalTail_eq_blockTail,
    hsNormSq_soninAllPrimeColumnTail_eq_blockTail]

theorem hsNormSq_soninAllPrimeDiagonalTail_le_coefficientTail
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    hsNormSq (soninAllPrimeResidualOperator a ha - soninAllPrimeDiagonalFiniteHead a s) ≤
      (128 * a ^ 2) * ∑' pk : Nat.Primes × ℕ,
        if pk ∈ s then 0 else ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
  rw [hsNormSq_soninAllPrimeDiagonalTail_eq_columnTail]
  exact hsNormSq_soninAllPrimeColumnTail_le_coefficientTail a ha s

end
end RHTower
