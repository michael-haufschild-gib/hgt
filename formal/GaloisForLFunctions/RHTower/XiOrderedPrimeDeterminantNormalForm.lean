import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.XiCentralDiscBound
import GaloisForLFunctions.RHTower.HilbertBasisMultiplierOperator
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEntire

open Complex Set
open HilbertSchmidt

namespace RHTower

noncomputable section

def xiOrderedSignedPrimeDiagonalKernel :
    RouteKSignedPrimeIndex × RouteKSignedPrimeIndex → ℂ :=
  diagMul xiOrderedSignedPrimeMultiplier

theorem summable_norm_xiOrderedSignedPrimeMultiplier_sq_of_rh
    (hRH : RiemannHypothesis) :
    Summable (fun i : RouteKSignedPrimeIndex =>
      ‖xiOrderedSignedPrimeMultiplier i‖ ^ 2) := by
  have h := xiOrderedSignedPrimeZeroCopyEquiv.summable_iff.mpr
    summable_norm_xiSpectralPoint_inv_sq
  exact h.congr fun i => by
    rw [Function.comp_apply,
      xiSpectralPoint_orderedSignedPrimeZeroCopyEquiv_eq_of_rh hRH]
    simp

theorem fredholmDet_xiOrderedSignedPrimeDiagonalKernel_eq_xiCanonicalProduct_of_rh
    (hRH : RiemannHypothesis)
    (r : ℝ) (hr : r * hsNorm xiOrderedSignedPrimeDiagonalKernel < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet xiOrderedSignedPrimeDiagonalKernel z =
      xiCanonicalProduct z := by
  rw [xiOrderedSignedPrimeDiagonalKernel,
    fredholmDet_tprod_diagMul xiOrderedSignedPrimeMultiplier
      (summable_norm_xiOrderedSignedPrimeMultiplier_sq_of_rh hRH)
      r hr z hz]
  let f : RouteKSignedPrimeIndex → ℂ := fun i =>
    (1 - z * xiOrderedSignedPrimeMultiplier i) *
      Complex.exp (z * xiOrderedSignedPrimeMultiplier i)
  have hXi : HasProd
      (fun q : XiZeroCopy => weierstrassE1 (z / xiSpectralPoint q))
      (xiCanonicalProduct z) :=
    xiCanonicalProduct_hasProdLocallyUniformlyOn.hasProd (Set.mem_univ z)
  have hPrime : HasProd f (xiCanonicalProduct z) := by
    have hReindex :=
      xiOrderedSignedPrimeZeroCopyEquiv.hasProd_iff.mpr hXi
    have hfac :
        ((fun q : XiZeroCopy => weierstrassE1 (z / xiSpectralPoint q)) ∘
          xiOrderedSignedPrimeZeroCopyEquiv) = f := by
      funext i
      rw [Function.comp_apply,
        xiSpectralPoint_orderedSignedPrimeZeroCopyEquiv_eq_of_rh hRH]
      simp [f, weierstrassE1, div_eq_mul_inv]
    rw [hfac] at hReindex
    exact hReindex
  change (∏' i, f i) = xiCanonicalProduct z
  exact hPrime.tprod_eq

theorem XiC_zero_ne_zero : XiC 0 ≠ 0 := by
  intro hzero
  have hnorm : ‖XiC 0‖ = 0 := by simp [hzero]
  have hbound := norm_XiC_zero_ge
  rw [hnorm] at hbound
  norm_num at hbound

theorem xiCanonicalProduct_eq_XiC_div_zero (z : ℂ) :
    xiCanonicalProduct z = XiC z / XiC 0 := by
  apply (eq_div_iff XiC_zero_ne_zero).2
  have h := congrFun XiC_eq_constant_mul_canonicalProduct z
  simpa only [Pi.mul_apply, mul_comm] using h.symm

theorem fredholmDet_xiOrderedSignedPrimeDiagonalKernel_eq_XiC_normalized_of_rh
    (hRH : RiemannHypothesis)
    (r : ℝ) (hr : r * hsNorm xiOrderedSignedPrimeDiagonalKernel < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet xiOrderedSignedPrimeDiagonalKernel z =
      XiC z / XiC 0 := by
  rw [fredholmDet_xiOrderedSignedPrimeDiagonalKernel_eq_xiCanonicalProduct_of_rh
    hRH r hr z hz, xiCanonicalProduct_eq_XiC_div_zero]

theorem xiOrderedSignedPrimeDiagonalKernel_isRegularizedDet_XiC_normalized_of_rh
    (hRH : RiemannHypothesis) :
    GaloisForLFunctions.HTGeometry.IsRegularizedDet
      xiOrderedSignedPrimeDiagonalKernel (fun z => XiC z / XiC 0) := by
  refine ⟨?_, ?_⟩
  · have hXi : Differentiable ℂ XiC := by
      rw [← differentiableOn_univ]
      exact XiC_analytic.differentiableOn
    fun_prop
  · let r : ℝ := (hsNorm xiOrderedSignedPrimeDiagonalKernel + 1)⁻¹
    have hden : 0 < hsNorm xiOrderedSignedPrimeDiagonalKernel + 1 := by
      linarith [hsNorm_nonneg xiOrderedSignedPrimeDiagonalKernel]
    have hr : 0 < r := inv_pos.mpr hden
    have hrK : r * hsNorm xiOrderedSignedPrimeDiagonalKernel < 1 := by
      dsimp [r]
      rw [inv_mul_eq_div, div_lt_one hden]
      linarith
    exact ⟨r, hr, hrK, fun z hz =>
      (fredholmDet_xiOrderedSignedPrimeDiagonalKernel_eq_XiC_normalized_of_rh
        hRH r hrK z hz).symm⟩

section InvariantNormalForm

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def IsExactXiReciprocalEigenbasis
    (A : H →L[ℂ] H) (b : HilbertBasis RouteKSignedPrimeIndex ℂ H) : Prop :=
  ∀ i, A (b i) =
    (xiSpectralPoint (xiOrderedSignedPrimeZeroCopyEquiv i))⁻¹ • b i

def IsExactCompactSelfAdjointXiOperatorOnNonzeroSubspace
    (A : H →L[ℂ] H) : Prop :=
  IsCompactOperator A ∧ IsSelfAdjoint A ∧
    ∃ b : HilbertBasis RouteKSignedPrimeIndex ℂ H,
      IsExactXiReciprocalEigenbasis A b

omit [CompleteSpace H] in
theorem continuousLinearMap_eq_of_eq_on_hilbertBasis
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (S T : H →L[ℂ] K) (hST : ∀ i, S (b i) = T (b i)) :
    S = T := by
  have hspan :
      (Submodule.span ℂ (Set.range (b : ι → H))).topologicalClosure ≤
        (S - T).ker := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change S (b i) - T (b i) = 0
      rw [hST i, sub_self]
    · exact ContinuousLinearMap.isClosed_ker (S - T)
  apply ContinuousLinearMap.ext
  intro x
  have hx : x ∈
      (Submodule.span ℂ (Set.range (b : ι → H))).topologicalClosure := by
    rw [b.dense_span]
    trivial
  have hxker := hspan hx
  change S x - T x = 0 at hxker
  exact sub_eq_zero.mp hxker

omit [CompleteSpace H] in
theorem unitaryPush_eq_xiOrderedSignedPrimeOperator_of_exactEigenbasis
    (hRH : RiemannHypothesis) (A : H →L[ℂ] H)
    (b : HilbertBasis RouteKSignedPrimeIndex ℂ H)
    (hExact : IsExactXiReciprocalEigenbasis A b) :
    unitaryPush b.repr A = xiOrderedSignedPrimeOperator := by
  apply continuousLinearMap_eq_of_eq_on_hilbertBasis
    (HilbertSchmidt.lpBasis RouteKSignedPrimeIndex)
  intro i
  rw [unitaryPush_apply]
  have hsymm : b.repr.symm (HilbertSchmidt.lpBasis RouteKSignedPrimeIndex i) =
      b i := by
    apply b.repr.injective
    rw [b.repr.apply_symm_apply, b.repr_self,
      HilbertSchmidt.lpBasis_apply]
  rw [hsymm, hExact i,
    xiSpectralPoint_orderedSignedPrimeZeroCopyEquiv_eq_of_rh hRH,
    map_smul]
  simp only [inv_inv]
  rw [b.repr_self, HilbertSchmidt.lpBasis_apply]
  cases i with
  | inl p =>
      simpa [xiOrderedSignedPrimeMultiplier] using
        (xiOrderedSignedPrimeOperator_basis_inl p).symm
  | inr p =>
      simpa [xiOrderedSignedPrimeMultiplier] using
        (xiOrderedSignedPrimeOperator_basis_inr p).symm

theorem exactCompactSelfAdjointXiOperator_prime_normalForm_of_rh
    (hRH : RiemannHypothesis) (A : H →L[ℂ] H)
    (hA : IsExactCompactSelfAdjointXiOperatorOnNonzeroSubspace A) :
    ∃ V : H ≃ₗᵢ[ℂ] RouteKSignedPrimeHilbert,
      unitaryPush V A = xiOrderedSignedPrimeOperator ∧
      MemSchattenClass 1 (unitaryPush V A - routeKSignedPrimeRVMOperator) := by
  rcases hA.2.2 with ⟨b, hb⟩
  refine ⟨b.repr,
    unitaryPush_eq_xiOrderedSignedPrimeOperator_of_exactEigenbasis hRH A b hb,
    ?_⟩
  rw [unitaryPush_eq_xiOrderedSignedPrimeOperator_of_exactEigenbasis hRH A b hb]
  exact xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator_memSchattenClass_one

end InvariantNormalForm

end

end RHTower
