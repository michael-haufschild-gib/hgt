import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass

/-!
# Route P primitive Gamma--Julia physical Hellinger ordinary determinant

The indefinite physical channel is split exactly as

A_r = (diag(65,1) + v_r v_r*) - (64+r)I, with v_r=(sqrt(r),8 delta).

Both summands are positive semidefinite for r >= 0. Tensoring them with P-G105M's positive
cofinal child preserves positivity on every finite principal block, hence on operator-norm
cofinal limit. Summable diagonal then makes both product operators Schatten-one; subtraction gives
Schatten-one membership of full indefinite physical Hellinger operator without removing any
cross-prime incidence.

Its ordinary trace is exactly (1-r) times Stokes current. Reflecting corpus convention
entireDet2 K(z)=det2(I-zT) yields physical ordinary determinant
exp(u Tr T) entireDet2 K(-u). Every finite stage is literally det(I+uT_s), and these stages
converge pointwise to entire ordinary determinant. At forced polar ratio trace is completed
prime--Gamma current throughout a punctured wall neighborhood.

This closes P-G105N. Aperture-wall local-uniform convergence with nontrivial divisor retention and
Xi-divisor identification remain.
-/

open Complex Matrix Filter Topology Set
open ContinuousLinearMap
open scoped Kronecker ComplexOrder BigOperators InnerProductSpace Matrix

namespace RHTower

noncomputable section

def routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveChannelVector (r : ℝ) : Fin 2 → ℂ :=
  ![((Real.sqrt r : ℝ) : ℂ), ((8 * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ)]

def routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(65 : ℂ), (1 : ℂ)] +
    Matrix.vecMulVec (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveChannelVector r) (star (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveChannelVector r))

def routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun _ => (((64 + r : ℝ) : ℂ)))

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel_posSemidef (r : ℝ) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)
  · exact Matrix.posSemidef_vecMulVec_self_star _

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel_posSemidef {r : ℝ} (hr : 0 ≤ r) :
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r).PosSemidef := by
  exact Matrix.PosSemidef.diagonal (by
    intro i
    change (0 : ℂ) ≤ (((64 + r : ℝ) : ℂ))
    exact_mod_cast (show 0 ≤ 64 + r by positivity))

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_positiveShift_sub_counter {r : ℝ} (hr : 0 ≤ r) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r - routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r := by
  have hsqrt : Real.sqrt r ^ (2 : ℕ) = r := Real.sq_sqrt hr
  have hdefect : routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = (63 / 64 : ℝ) :=
    routeEPCubicFourthDepthJuliaDefect_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel, routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel, routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveChannelVector,
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel, Matrix.vecMulVec,
      Matrix.diagonal]
  · apply Complex.ext
    · simp
      nlinarith [hsqrt]
    · simp
  · apply Complex.ext
    · simp
      ring
    · simp
  · apply Complex.ext
    · simp
      ring
    · simp
  · apply Complex.ext
    · simp
      nlinarith [hdefect]
    · simp

def routePPrimitiveGammaJuliaStokesChannelTensorKernel (A : Matrix (Fin 2) (Fin 2) ℂ) (d : ℝ)
    (xy : (Fin 2 × Nat.Primes) × (Fin 2 × Nat.Primes)) : ℂ :=
  A xy.1.1 xy.2.1 *
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.1.2, xy.2.2)

theorem routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS (A : Matrix (Fin 2) (Fin 2) ℂ)
    {d : ℝ} (hd : 0 < d) : HilbertSchmidt.IsHS (routePPrimitiveGammaJuliaStokesChannelTensorKernel A d) := by
  let g : Fin 2 × Fin 2 → ℝ := fun ij => ‖A ij.1 ij.2‖ ^ (2 : ℕ)
  let h : Nat.Primes × Nat.Primes → ℝ := fun pq =>
    ‖routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq‖ ^ (2 : ℕ)
  have hg : Summable g := Summable.of_finite
  have hh : Summable h := routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  have hgh : Summable (fun x : (Fin 2 × Fin 2) ×
      (Nat.Primes × Nat.Primes) => g x.1 * h x.2) :=
    summable_mul_of_summable_norm hg.norm hh.norm
  rw [← routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv.summable_iff]
    at hgh
  simpa [HilbertSchmidt.IsHS, Function.comp_def,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerPairEquiv,
    routePPrimitiveGammaJuliaStokesChannelTensorKernel, g, h, norm_mul, mul_pow] using hgh

theorem routePPrimitiveGammaJuliaStokesChannelTensorKernel_hsAdjoint
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A) (d : ℝ) :
    HilbertSchmidt.hsAdjoint (routePPrimitiveGammaJuliaStokesChannelTensorKernel A d) = routePPrimitiveGammaJuliaStokesChannelTensorKernel A d := by
  funext xy
  rw [HilbertSchmidt.hsAdjoint]
  change star (A xy.2.1 xy.1.1 *
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.2.2, xy.1.2)) =
    A xy.1.1 xy.2.1 *
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.1.2, xy.2.2)
  rw [star_mul]
  have hAc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M xy.1.1 xy.2.1) hA
  have hK : star (routePPrimitiveGammaJuliaStokesCofinalChildKernel
      d (xy.2.2, xy.1.2)) =
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.1.2, xy.2.2) := by
    have h := congrFun
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_hsAdjoint d) (xy.1.2, xy.2.2)
    simpa [HilbertSchmidt.hsAdjoint] using h
  simp only [Matrix.conjTranspose_apply] at hAc
  rw [hAc, hK, mul_comm]

theorem routePPrimitiveGammaJuliaStokesChannelTensorOperator_isSelfAdjoint
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : Aᴴ = A) {d : ℝ} (hd : 0 < d) :
    IsSelfAdjoint (HilbertSchmidt.toOperator (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd)) := by
  rw [IsSelfAdjoint]
  change ContinuousLinearMap.adjoint
      (HilbertSchmidt.toOperator (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd)) = _
  rw [HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _ (routePPrimitiveGammaJuliaStokesChannelTensorKernel_hsAdjoint hA d)

theorem routePPrimitiveGammaJuliaStokesChannelTensorBlockMatrix_posSemidef
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef)
    (d : ℝ) (s : Finset (Fin 2 × Nat.Primes)) :
    (HilbertSchmidt.blockMatrix (routePPrimitiveGammaJuliaStokesChannelTensorKernel A d) s).PosSemidef := by
  classical
  let t : Finset Nat.Primes := s.image Prod.snd
  let e : s → Fin 2 × t := fun x =>
    (x.1.1, ⟨x.1.2, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩)
  have hprod : (A ⊗ₖ HilbertSchmidt.blockMatrix
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t).PosSemidef :=
    hA.kronecker
      (routePPrimitiveGammaJuliaStokesCofinalChildBlockMatrix_posSemidef d t)
  have hsub := hprod.submatrix e
  have heq : HilbertSchmidt.blockMatrix (routePPrimitiveGammaJuliaStokesChannelTensorKernel A d) s =
      (A ⊗ₖ HilbertSchmidt.blockMatrix
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t).submatrix e e := by
    ext x y
    simp [HilbertSchmidt.blockMatrix, routePPrimitiveGammaJuliaStokesChannelTensorKernel, Matrix.submatrix,
      e, t]
  rwa [heq]

theorem inner_toOperator_truncKernel_eq_blockMatrix
    {ι : Type*} [DecidableEq ι] {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K)
    (s : Finset ι) (x : lp (fun _ : ι => ℂ) 2) :
    inner ℂ x (HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_truncKernel hK s) x) =
      star (fun i : ↥s => x (i : ι)) ⬝ᵥ
        (HilbertSchmidt.blockMatrix K s *ᵥ fun i : ↥s => x (i : ι)) := by
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

theorem hsAdjoint_truncKernel_of_eq
    {ι : Type*} [DecidableEq ι] {K : ι × ι → ℂ}
    (hKstar : HilbertSchmidt.hsAdjoint K = K) (s : Finset ι) :
    HilbertSchmidt.hsAdjoint (HilbertSchmidt.truncKernel K s) =
      HilbertSchmidt.truncKernel K s := by
  funext ij
  rw [HilbertSchmidt.hsAdjoint]
  change star (if ij.2 ∈ s ∧ ij.1 ∈ s then K (ij.2, ij.1) else 0) =
    (if ij.1 ∈ s ∧ ij.2 ∈ s then K ij else 0)
  by_cases hmem : ij.1 ∈ s ∧ ij.2 ∈ s
  · have hmem' : ij.2 ∈ s ∧ ij.1 ∈ s := ⟨hmem.2, hmem.1⟩
    rw [if_pos hmem, if_pos hmem']
    have h := congrFun hKstar ij
    simpa [HilbertSchmidt.hsAdjoint] using h
  · have hmem' : ¬(ij.2 ∈ s ∧ ij.1 ∈ s) := by simpa [and_comm] using hmem
    rw [if_neg hmem, if_neg hmem']
    simp

theorem toOperator_truncKernel_isSelfAdjoint
    {ι : Type*} [DecidableEq ι] {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K)
    (hKstar : HilbertSchmidt.hsAdjoint K = K) (s : Finset ι) :
    IsSelfAdjoint (HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_truncKernel hK s)) := by
  rw [IsSelfAdjoint]
  change ContinuousLinearMap.adjoint
      (HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel hK s)) = _
  rw [HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _ (hsAdjoint_truncKernel_of_eq hKstar s)

theorem toOperator_truncKernel_isPositive
    {ι : Type*} [DecidableEq ι] {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K)
    (hKstar : HilbertSchmidt.hsAdjoint K = K)
    (hblock : ∀ s : Finset ι, (HilbertSchmidt.blockMatrix K s).PosSemidef)
    (s : Finset ι) :
    (HilbertSchmidt.toOperator
      (HilbertSchmidt.isHS_truncKernel hK s)).IsPositive := by
  let T := HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel hK s)
  have hself : IsSelfAdjoint T := toOperator_truncKernel_isSelfAdjoint hK hKstar s
  refine ⟨hself.isSymmetric, fun x => ?_⟩
  change 0 ≤ T.reApplyInnerSelf x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  calc
    0 ≤ RCLike.re (inner ℂ x (T x)) := by
      rw [inner_toOperator_truncKernel_eq_blockMatrix hK s x]
      exact (hblock s).re_dotProduct_nonneg _
    _ = RCLike.re (inner ℂ (T x) x) :=
      congrArg RCLike.re (hself.isSymmetric x x).symm

theorem toOperator_isPositive_of_blockMatrix_posSemidef
    {ι : Type*} [DecidableEq ι] {K : ι × ι → ℂ} (hK : HilbertSchmidt.IsHS K)
    (hKstar : HilbertSchmidt.hsAdjoint K = K)
    (hblock : ∀ s : Finset ι, (HilbertSchmidt.blockMatrix K s).PosSemidef) :
    (HilbertSchmidt.toOperator hK).IsPositive := by
  let T := HilbertSchmidt.toOperator hK
  have hself : IsSelfAdjoint T := by
    rw [IsSelfAdjoint]
    change ContinuousLinearMap.adjoint (HilbertSchmidt.toOperator hK) = _
    rw [HilbertSchmidt.adjoint_toOperator]
    exact HilbertSchmidt.toOperator_congr _ _ hKstar
  refine ⟨hself.isSymmetric, fun x => ?_⟩
  let Ts : Finset ι → (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :=
    fun s => HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel hK s)
  have hTend : Tendsto Ts atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact HilbertSchmidt.tendsto_norm_toOperator_truncKernel_sub hK
  have hcont : Continuous (fun A :
      (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) =>
      A.reApplyInnerSelf x) := by
    exact RCLike.continuous_re.comp
      (continuous_inner.comp
        (((ContinuousLinearMap.apply ℂ _ x).continuous).prodMk continuous_const))
  have hquad : Tendsto (fun s => (Ts s).reApplyInnerSelf x) atTop
      (𝓝 (T.reApplyInnerSelf x)) := hcont.continuousAt.tendsto.comp hTend
  apply ge_of_tendsto hquad
  exact Filter.Eventually.of_forall fun s =>
    (toOperator_truncKernel_isPositive hK hKstar hblock s).2 x

theorem routePPrimitiveGammaJuliaStokesChannelTensorOperator_isPositive
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef)
    {d : ℝ} (hd : 0 < d) :
    (HilbertSchmidt.toOperator (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd)).IsPositive :=
  toOperator_isPositive_of_blockMatrix_posSemidef (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd)
    (routePPrimitiveGammaJuliaStokesChannelTensorKernel_hsAdjoint hA.isHermitian d)
    (routePPrimitiveGammaJuliaStokesChannelTensorBlockMatrix_posSemidef hA d)

theorem summable_routePPrimitiveGammaJuliaStokesChannelTensorKernel_diagonal
    (A : Matrix (Fin 2) (Fin 2) ℂ) {d : ℝ} (hd : 0 < d) :
    Summable (fun ip : Fin 2 × Nat.Primes => routePPrimitiveGammaJuliaStokesChannelTensorKernel A d (ip, ip)) := by
  let f : Fin 2 × Nat.Primes → ℂ := fun ip =>
    A ip.1 ip.1 * routePPrimitiveGammaJuliaStokesCofinalChildKernel d (ip.2, ip.2)
  have hdiag := summable_routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd
  have hf : Summable f := by
    exact summable_mul_of_summable_norm
      (f := fun i : Fin 2 => A i i)
      (g := fun p : Nat.Primes =>
        routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p))
      Summable.of_finite hdiag.norm
  simpa [f, routePPrimitiveGammaJuliaStokesChannelTensorKernel] using hf

theorem routePPrimitiveGammaJuliaStokesChannelTensorOperator_memSchattenClass_one
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef)
    {d : ℝ} (hd : 0 < d) :
    MemSchattenClass 1 (HilbertSchmidt.toOperator (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd)) := by
  let b := HilbertSchmidt.lpBasis (Fin 2 × Nat.Primes)
  have hsum : Summable fun ip => inner ℂ (b ip)
      (HilbertSchmidt.toOperator (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd) (b ip)) :=
    (summable_routePPrimitiveGammaJuliaStokesChannelTensorKernel_diagonal A hd).congr fun ip =>
      (HilbertSchmidt.inner_lpBasis_toOperator (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS A hd) ip).symm
  exact memSchattenClass_one_of_isPositive_of_summable_diagonal b
    (routePPrimitiveGammaJuliaStokesChannelTensorOperator_isPositive hA hd) hsum

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_positiveShift_sub_counter
    {d r : ℝ} (hr : 0 ≤ r) :
    routePPrimitiveGammaJuliaStokesChannelTensorKernel (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r) d -
      routePPrimitiveGammaJuliaStokesChannelTensorKernel (routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r) d =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r := by
  funext xy
  rw [Pi.sub_apply]
  change routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r xy.1.1 xy.2.1 *
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.1.2, xy.2.2) -
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r xy.1.1 xy.2.1 *
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (xy.1.2, xy.2.2) = _
  rw [← sub_mul]
  have hentry :
      routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r xy.1.1 xy.2.1 -
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r xy.1.1 xy.2.1 =
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r xy.1.1 xy.2.1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M xy.1.1 xy.2.1)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel_positiveShift_sub_counter hr)
  rw [hentry]
  rfl

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_eq_positiveShift_sub_counter
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r) =
      HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r) hd) -
        HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS (routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r) hd) := by
  let hP := routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel r) hd
  let hC := routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS (routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r) hd
  calc
    HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r) =
      HilbertSchmidt.toOperator (HilbertSchmidt.isHS_sub hP hC) := by
        exact HilbertSchmidt.toOperator_congr _ _ (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_positiveShift_sub_counter hr).symm
    _ = HilbertSchmidt.toOperator hP - HilbertSchmidt.toOperator hC :=
      (HilbertSchmidt.toOperator_sub hP hC).symm

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_memSchattenClass_one
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    MemSchattenClass 1 (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)) := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_eq_positiveShift_sub_counter hd hr]
  let hP := routePPrimitiveGammaJuliaStokesChannelTensorOperator_memSchattenClass_one
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerPositiveShiftChannel_posSemidef r) hd
  let hC := routePPrimitiveGammaJuliaStokesChannelTensorOperator_memSchattenClass_one
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel_posSemidef hr) hd
  have hCn : MemSchattenClass 1
      (-HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesChannelTensorKernel_isHS
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCounterChannel r) hd)) := by
    simpa using memSchattenClass_one_smul hC (-1 : ℂ)
  rw [sub_eq_add_neg]
  exact memSchattenClass_one_add
    (hP.isCompactOperator one_pos) (hCn.isCompactOperator one_pos) hP hCn

private theorem opTrace_eq_tsum_basis_of_memSchattenClass_one
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) :
    ContinuousLinearMap.opTrace T = ∑' i, inner ℂ (b i) (T (b i)) := by
  obtain ⟨A, B, hA, hB, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB b

theorem opTrace_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)) =
      ((1 - r : ℝ) : ℂ) *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) := by
  let b := HilbertSchmidt.lpBasis (Fin 2 × Nat.Primes)
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one b
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_memSchattenClass_one hd hr)]
  rw [tsum_congr (fun ip => HilbertSchmidt.inner_lpBasis_toOperator
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r) ip),
    tsum_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal hd r]

def routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet (d r : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * (((1 - r : ℝ) : ℂ) *
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))) *
    routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r (-z)

theorem differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet {d r : ℝ} (hd : 0 < d) :
    Differentiable ℂ (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r) := by
  exact (Complex.differentiable_exp.comp
    (differentiable_id.mul_const ((((1 - r : ℝ) : ℂ) *
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))))).mul
      ((differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2
        hd r).comp differentiable_neg)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_zero_iff {d r : ℝ} {z : ℂ} :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r z = 0 ↔
      routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2 d r (-z) = 0 := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet, mul_eq_zero]
  exact or_iff_right (Complex.exp_ne_zero _)

def routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace (d r : ℝ) (s : Finset (Fin 2 × Nat.Primes)) : ℂ :=
  (HilbertSchmidt.blockMatrix
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s).trace

def routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet (d r : ℝ) (s : Finset (Fin 2 × Nat.Primes))
    (z : ℂ) : ℂ :=
  Complex.exp (z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s) *
    GaloisForLFunctions.HTGeometry.finiteDet2
      (-(HilbertSchmidt.blockMatrix
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s)) (-z)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet_eq_det
    (d r : ℝ) (s : Finset (Fin 2 × Nat.Primes)) (z : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z =
      (1 + z • HilbertSchmidt.blockMatrix
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s).det := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet, GaloisForLFunctions.HTGeometry.finiteDet2]
  simp only [routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace, neg_smul, smul_neg, neg_neg, Matrix.trace_neg]
  let M := HilbertSchmidt.blockMatrix
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s
  change Complex.exp (z * M.trace) *
      ((1 + z • M).det * Complex.exp (-(-z * -M.trace))) = (1 + z • M).det
  have harg : -(-z * -M.trace) = -(z * M.trace) := by ring
  rw [harg]
  calc
    _ = (1 + z • M).det *
        (Complex.exp (z * M.trace) * Complex.exp (-(z * M.trace))) := by ring
    _ = (1 + z • M).det * Complex.exp
        (z * M.trace + -(z * M.trace)) := by rw [Complex.exp_add]
    _ = _ := by simp

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace_eq_sum
    (d r : ℝ) (s : Finset (Fin 2 × Nat.Primes)) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s =
      ∑ ip ∈ s,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip) := by
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace, Matrix.trace, HilbertSchmidt.blockMatrix]
  exact Finset.sum_attach s
    (fun ip => routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip))

theorem tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) :
    Tendsto (routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r) atTop
      (nhds (ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)))) := by
  have hop : ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)) =
      ∑' ip : Fin 2 × Nat.Primes,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip) := by
    rw [opTrace_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator hd hr,
      tsum_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal hd r]
  rw [hop]
  rw [show routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r = fun s => ∑ ip ∈ s,
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r (ip, ip) by
    funext s
    exact routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace_eq_sum d r s]
  exact (summable_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_diagonal
    hd r).hasSum

theorem tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet
    {d r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (z : ℂ) :
    Tendsto (fun s : Finset (Fin 2 × Nat.Primes) =>
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z) atTop
      (nhds (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r z)) := by
  apply Tendsto.mul
  · have htrace := tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace hd hr
    have hmul : Tendsto (fun s : Finset (Fin 2 × Nat.Primes) =>
        z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s) atTop
        (nhds (z * ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)))) :=
      tendsto_const_nhds.mul htrace
    have hexp : Tendsto (fun s : Finset (Fin 2 × Nat.Primes) =>
        Complex.exp (z * routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteTrace d r s)) atTop
        (nhds (Complex.exp (z * ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r))))) :=
      Complex.continuous_exp.continuousAt.tendsto.comp hmul
    simpa [opTrace_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator hd hr] using hexp
  · exact GaloisForLFunctions.HTGeometry.tendsto_finiteDet2_entireDet2
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r) (-z)

theorem eventually_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_traceClass :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      ∃ hd : 0 < d,
        MemSchattenClass 1 (HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d))) ∧
        ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d))) =
          (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d : ℂ) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio_pos] with d hd hr
  exact ⟨hd, routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_memSchattenClass_one hd hr.le,
    (opTrace_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator hd hr.le).trans (by
      exact_mod_cast routePPrimitiveGammaJuliaPhysicalStokesLinearTrace_eq_completed hd)⟩

/-- **P-G105N capstone.** Full physical cofinal operator is nuclear, its ordinary trace is the
source-forced Stokes current, and its reflected ordinary determinant is the cofinal limit of the
literal finite physical determinants. -/
theorem routePPrimitive_GammaJulia_physicalStokesHellingerOrdinaryDeterminant
    (d : ℝ) (hd : 0 < d) (r : ℝ) (hr : 0 ≤ r) :
      MemSchattenClass 1 (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS
          (d := d) (r := r) hd)) ∧
      ContinuousLinearMap.opTrace (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS
          (d := d) (r := r) hd)) =
        ((1 - r : ℝ) : ℂ) *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) ∧
      Differentiable ℂ
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r) ∧
      (∀ z : ℂ,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r z = 0 →
          z.im = 0) ∧
      (∀ (s : Finset (Fin 2 × Nat.Primes)) (z : ℂ),
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z =
          (1 + z • HilbertSchmidt.blockMatrix
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d r) s).det) ∧
      (∀ z : ℂ,
        Tendsto (fun s : Finset (Fin 2 × Nat.Primes) =>
          routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d r s z)
          atTop
          (nhds (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d r z))) := by
  refine ⟨routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_memSchattenClass_one
      hd hr,
    opTrace_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator hd hr,
    differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet hd,
    ?_, routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet_eq_det d r,
    tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet hd hr⟩
  intro z hz
  have hdet2 :=
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_zero_iff.mp hz
  have him := routePPrimitiveGammaJuliaPhysicalStokesHellingerEntireDet2_zero_im hd r hdet2
  simpa using him

end

end RHTower
