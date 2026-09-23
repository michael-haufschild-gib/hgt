import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalDeterminant
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteSectionMultiplicity

/-!
# Route P primitive Gamma--Julia Stokes cofinal child trace class

Every finite principal block of P-G105K's literal cofinal child kernel is an actual
aperture-conjugated P-G186 Gram, hence positive semidefinite.  Zero-padded finite-section
operators are therefore positive.  Their operator-norm limit is the full child operator, so the
cofinal operator is positive as well as self-adjoint.

A general positive-diagonal criterion then closes the missing nuclearity step: a positive bounded
operator whose diagonal is summable in one Hilbert basis has a Hilbert--Schmidt positive square
root, hence is Schatten-one.  Applying this to the canonical prime basis and the exact transported
Stokes diagonal proves that the full child operator is Schatten-one and that its ordinary operator
trace is exactly the oriented Stokes current.

This closes P-G105M without diagonalizing, deleting cross-prime incidence, or assuming trace class.
Lifting nuclearity through the finite Hellinger channel and constructing the ordinary physical
determinant remain.
-/

open Complex Matrix Filter Topology Set
open ContinuousLinearMap
open scoped Kronecker ComplexOrder BigOperators InnerProductSpace

namespace RHTower

noncomputable section

/-- Every finite principal block of the literal cofinal child kernel is positive semidefinite. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildBlockMatrix_posSemidef
    (d : ℝ) (s : Finset Nat.Primes) :
    (HilbertSchmidt.blockMatrix
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) s).PosSemidef := by
  let p : Fin s.card → Nat.Primes := fun i => (s.equivFin.symm i).1
  let M := routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
    d p (fun _ => 0)
  have hM : M.PosSemidef :=
    routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef
      d p (fun _ => 0)
  have hsub := hM.submatrix s.equivFin
  have heq : HilbertSchmidt.blockMatrix
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) s =
      M.submatrix s.equivFin s.equivFin := by
    ext i j
    rw [HilbertSchmidt.blockMatrix]
    change routePPrimitiveGammaJuliaStokesCofinalChildKernel d (i.1, j.1) =
      M (s.equivFin i) (s.equivFin j)
    have h := routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply
      d p (s.equivFin i) (s.equivFin j)
    simpa [p, M] using h
  rwa [heq]

/-- Quadratic form of a zero-padded finite section is its exact finite block matrix form. -/
theorem inner_routePPrimitiveGammaJuliaStokesCofinalChildTruncOperator
    {K : Nat.Primes × Nat.Primes → ℂ} (hK : HilbertSchmidt.IsHS K)
    (s : Finset Nat.Primes) (x : lp (fun _ : Nat.Primes => ℂ) 2) :
    inner ℂ x (HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_truncKernel hK s) x) =
      star (fun i : ↥s => x (i : Nat.Primes)) ⬝ᵥ
        (HilbertSchmidt.blockMatrix K s *ᵥ
          fun i : ↥s => x (i : Nat.Primes)) := by
  rw [GaloisForLFunctions.HTGeometry.toOperator_truncKernel_eq_liftBlock_mulVec_restrict
    hK s x]
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := s)]
  · rw [← Finset.sum_coe_sort s]
    simp [HilbertSchmidt.liftBlockLp_apply,
      HilbertSchmidt.liftBlock_apply_of_mem, dotProduct, RCLike.inner_apply,
      mul_comm]
  · intro i hi
    rw [HilbertSchmidt.liftBlockLp_apply,
      HilbertSchmidt.liftBlock_apply_of_notMem _ hi]
    simp

/-- Finite truncation preserves Hermitian symmetry of the cofinal child kernel. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildTruncKernel_hsAdjoint
    (d : ℝ) (s : Finset Nat.Primes) :
    HilbertSchmidt.hsAdjoint
      (HilbertSchmidt.truncKernel
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) s) =
      HilbertSchmidt.truncKernel
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) s := by
  funext pq
  rw [HilbertSchmidt.hsAdjoint]
  change star (if pq.2 ∈ s ∧ pq.1 ∈ s then
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.2, pq.1) else 0) =
    (if pq.1 ∈ s ∧ pq.2 ∈ s then
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq else 0)
  by_cases hmem : pq.1 ∈ s ∧ pq.2 ∈ s
  · have hmem' : pq.2 ∈ s ∧ pq.1 ∈ s := ⟨hmem.2, hmem.1⟩
    rw [if_pos hmem, if_pos hmem']
    have h := congrFun
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_hsAdjoint d) pq
    simpa [HilbertSchmidt.hsAdjoint] using h
  · have hmem' : ¬(pq.2 ∈ s ∧ pq.1 ∈ s) := by
      simpa [and_comm] using hmem
    rw [if_neg hmem, if_neg hmem']
    simp

/-- Every represented finite principal section is self-adjoint. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildTruncOperator_isSelfAdjoint
    {d : ℝ} (hd : 0 < d) (s : Finset Nat.Primes) :
    IsSelfAdjoint (HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_truncKernel
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) s)) := by
  rw [IsSelfAdjoint]
  change ContinuousLinearMap.adjoint
      (HilbertSchmidt.toOperator
        (HilbertSchmidt.isHS_truncKernel
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) s)) = _
  rw [HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    (routePPrimitiveGammaJuliaStokesCofinalChildTruncKernel_hsAdjoint d s)

/-- Every represented finite principal section is positive. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildTruncOperator_isPositive
    {d : ℝ} (hd : 0 < d) (s : Finset Nat.Primes) :
    (HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_truncKernel
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) s)).IsPositive := by
  let hK := routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  let T := HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel hK s)
  have hself : IsSelfAdjoint T :=
    routePPrimitiveGammaJuliaStokesCofinalChildTruncOperator_isSelfAdjoint hd s
  refine ⟨hself.isSymmetric, fun x => ?_⟩
  change 0 ≤ T.reApplyInnerSelf x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  calc
    0 ≤ RCLike.re (inner ℂ x (T x)) := by
      rw [inner_routePPrimitiveGammaJuliaStokesCofinalChildTruncOperator hK s x]
      exact
        (routePPrimitiveGammaJuliaStokesCofinalChildBlockMatrix_posSemidef d s).re_dotProduct_nonneg _
    _ = RCLike.re (inner ℂ (T x) x) :=
      congrArg RCLike.re (hself.isSymmetric x x).symm

/-- Positivity survives the cofinal operator-norm limit of finite principal sections. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildOperator_isPositive
    {d : ℝ} (hd : 0 < d) :
    (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)).IsPositive := by
  let hK := routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  let T := HilbertSchmidt.toOperator hK
  refine ⟨(routePPrimitiveGammaJuliaStokesCofinalChildOperator_isSelfAdjoint hd).isSymmetric,
    fun x => ?_⟩
  let Ts : Finset Nat.Primes →
      (lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2) :=
    fun s => HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel hK s)
  have hTend : Tendsto Ts atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact HilbertSchmidt.tendsto_norm_toOperator_truncKernel_sub hK
  have hcont : Continuous (fun A :
      (lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] lp (fun _ : Nat.Primes => ℂ) 2) =>
      A.reApplyInnerSelf x) := by
    exact RCLike.continuous_re.comp
      (continuous_inner.comp
        (((ContinuousLinearMap.apply ℂ _ x).continuous).prodMk continuous_const))
  have hquad : Tendsto (fun s => (Ts s).reApplyInnerSelf x) atTop
      (𝓝 (T.reApplyInnerSelf x)) := hcont.continuousAt.tendsto.comp hTend
  apply ge_of_tendsto hquad
  exact Filter.Eventually.of_forall fun s =>
    (routePPrimitiveGammaJuliaStokesCofinalChildTruncOperator_isPositive hd s).2 x

/-- Canonical prime-basis diagonal is the exact transported Stokes weight. -/
theorem inner_lpBasis_routePPrimitiveGammaJuliaStokesCofinalChildOperator
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    inner ℂ (HilbertSchmidt.lpBasis Nat.Primes p)
      (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)
        (HilbertSchmidt.lpBasis Nat.Primes p)) =
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p : ℂ) := by
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left,
    HilbertSchmidt.toOperator_single]
  simp [RCLike.inner_apply,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd]

/-- A positive bounded operator with a summable diagonal in one Hilbert basis is Schatten-one. -/
theorem memSchattenClass_one_of_isPositive_of_summable_diagonal
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hsum : Summable fun i => inner ℂ (b i) (T (b i))) :
    MemSchattenClass 1 T := by
  let R := traceClassRoot T
  have hT0 : (0 : H →L[ℂ] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive T).2 hT
  have hTstar : star T = T := hT.isSelfAdjoint.star_eq
  have habs : absOp T = T := by
    unfold absOp
    rw [hTstar]
    exact CFC.sqrt_mul_self T hT0
  have hR2 : R ∘L R = T := by
    rw [traceClassRoot_comp_self, habs]
  have hRself : IsSelfAdjoint R := isSelfAdjoint_traceClassRoot T
  have hR : R.IsHilbertSchmidt := by
    refine ContinuousLinearMap.isHilbertSchmidt_of_summable b ?_
    rw [← RCLike.summable_ofReal (𝕜 := ℂ)]
    refine hsum.congr fun i => ?_
    calc
      inner ℂ (b i) (T (b i)) = inner ℂ (b i) (R (R (b i))) := by
        rw [← ContinuousLinearMap.comp_apply, hR2]
      _ = inner ℂ (R (b i)) (R (b i)) :=
        (hRself.isSymmetric (b i) (R (b i))).symm
      _ = ((‖R (b i)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
  rw [← hR2]
  exact memSchattenClass_one_comp hR hR

/-- For a positive operator with summable basis diagonal, ordinary trace is that diagonal sum. -/
theorem opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hsum : Summable fun i => inner ℂ (b i) (T (b i))) :
    ContinuousLinearMap.opTrace T = ∑' i, inner ℂ (b i) (T (b i)) := by
  have hmem := memSchattenClass_one_of_isPositive_of_summable_diagonal b hT hsum
  obtain ⟨A, B, hA, hB, hfac⟩ := hmem.one_isTraceClass
  rw [hfac]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB b

/-- Literal cofinal Stokes child operator is Schatten-one; no incidence is discarded. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildOperator_memSchattenClass_one
    {d : ℝ} (hd : 0 < d) :
    MemSchattenClass 1 (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) := by
  let b := HilbertSchmidt.lpBasis Nat.Primes
  have hsum : Summable fun p => inner ℂ (b p)
      (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) (b p)) := by
    refine (Complex.summable_ofReal.mpr
      (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd)).congr
      fun p => ?_
    exact (inner_lpBasis_routePPrimitiveGammaJuliaStokesCofinalChildOperator hd p).symm
  exact memSchattenClass_one_of_isPositive_of_summable_diagonal b
    (routePPrimitiveGammaJuliaStokesCofinalChildOperator_isPositive hd) hsum

/-- Ordinary trace of the literal cofinal child operator is exactly the oriented Stokes current. -/
theorem opTrace_routePPrimitiveGammaJuliaStokesCofinalChildOperator
    {d : ℝ} (hd : 0 < d) :
    ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) =
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) := by
  let b := HilbertSchmidt.lpBasis Nat.Primes
  have hsum : Summable fun p => inner ℂ (b p)
      (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd) (b p)) := by
    refine (Complex.summable_ofReal.mpr
      (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd)).congr
      fun p => ?_
    exact (inner_lpBasis_routePPrimitiveGammaJuliaStokesCofinalChildOperator hd p).symm
  rw [opTrace_eq_tsum_basis_of_isPositive_of_summable_diagonal b
    (routePPrimitiveGammaJuliaStokesCofinalChildOperator_isPositive hd) hsum]
  rw [tsum_congr
      (fun p => inner_lpBasis_routePPrimitiveGammaJuliaStokesCofinalChildOperator hd p),
    ← Complex.ofReal_tsum,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]

/-- P-G105M: positive cofinal child, Schatten-one nuclearity, and exact ordinary Stokes trace. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildTraceClass
    {d : ℝ} (hd : 0 < d) :
    (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)).IsPositive ∧
      MemSchattenClass 1 (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) ∧
      ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) =
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) :=
  ⟨routePPrimitiveGammaJuliaStokesCofinalChildOperator_isPositive hd,
    routePPrimitiveGammaJuliaStokesCofinalChildOperator_memSchattenClass_one hd,
    opTrace_routePPrimitiveGammaJuliaStokesCofinalChildOperator hd⟩

end

end RHTower
