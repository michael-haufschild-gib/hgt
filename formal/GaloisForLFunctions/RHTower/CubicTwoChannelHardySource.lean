import GaloisForLFunctions.RHTower.CubicBoundaryChargeTransport
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanRealTraceCocycle
import GaloisForLFunctions.HTGeometry.SourceLinearClosedRelationSplitting
import GaloisForLFunctions.HTGeometry.TraceClassQuantumCorner

/-!
# Two-channel realization of bounded source symbols and Hardy boundary currents

The literal multiplier representation preserves products and adjoints. Nuclear scalar
Hardy commutators lift through the orthogonal two-channel carrier, retaining the exact
trace of each diagonal corner. This is standard realization machinery for the explicit
cubic boundary loop, not an independent arithmetic law.
-/

open MeasureTheory ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower

abbrev CubicSymbols := BoundedContinuousFunction ℝ ℂ
def cubicSymbolMultiplier (f : CubicSymbols) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM f.continuous.measurable (norm_nonneg f) f.norm_coe_le_norm
theorem cubicSymbolMultiplier_ae (f : CubicSymbols) (x : SoninL2) :
    (cubicSymbolMultiplier f x : ℝ → ℂ) =ᵐ[volume] fun t => f t * x t :=
  lpBoundedMulCLM_coeFn _ _ _ _
theorem cubicSymbolMultiplier_mul (f g : CubicSymbols) :
    cubicSymbolMultiplier (f*g) = cubicSymbolMultiplier f * cubicSymbolMultiplier g := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [cubicSymbolMultiplier_ae (f*g) x,
    cubicSymbolMultiplier_ae f (cubicSymbolMultiplier g x),
    cubicSymbolMultiplier_ae g x] with t hfg hf hg
  change (cubicSymbolMultiplier (f*g) x : ℝ → ℂ) t =
    (cubicSymbolMultiplier f (cubicSymbolMultiplier g x) : ℝ → ℂ) t
  rw [hfg, hf, hg]
  change (f t * g t) * x t = f t * (g t * x t)
  ring
theorem cubicSymbolMultiplier_add (f g : CubicSymbols) :
    cubicSymbolMultiplier (f+g) = cubicSymbolMultiplier f + cubicSymbolMultiplier g := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [cubicSymbolMultiplier_ae (f+g) x,
    cubicSymbolMultiplier_ae f x, cubicSymbolMultiplier_ae g x,
    Lp.coeFn_add (cubicSymbolMultiplier f x) (cubicSymbolMultiplier g x)] with t hfg hf hg ha
  change (cubicSymbolMultiplier (f+g) x : ℝ → ℂ) t =
    (cubicSymbolMultiplier f x + cubicSymbolMultiplier g x : SoninL2) t
  rw [hfg, ha]
  simp only [Pi.add_apply, hf, hg]
  change (f t + g t) * x t = f t * x t + g t * x t
  ring
theorem cubicSymbolMultiplier_one : cubicSymbolMultiplier 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [cubicSymbolMultiplier_ae 1 x] with t ht
  simpa using ht
theorem cubicSymbolMultiplier_zero : cubicSymbolMultiplier 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [cubicSymbolMultiplier_ae 0 x, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht hz
  simpa [hz] using ht

def cubicSymbolMultiplierHom : CubicSymbols →+* (SoninL2 →L[ℂ] SoninL2) where
  toFun := cubicSymbolMultiplier
  map_one' := cubicSymbolMultiplier_one
  map_mul' := cubicSymbolMultiplier_mul
  map_zero' := cubicSymbolMultiplier_zero
  map_add' := cubicSymbolMultiplier_add

theorem cubicSymbolMultiplier_smul (z : ℂ) (f : CubicSymbols) :
    cubicSymbolMultiplier (z • f) = z • cubicSymbolMultiplier f := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [cubicSymbolMultiplier_ae (z • f) x,
    cubicSymbolMultiplier_ae f x, Lp.coeFn_smul z (cubicSymbolMultiplier f x)] with t hzf hf hz
  change (cubicSymbolMultiplier (z • f) x : ℝ → ℂ) t = (z • cubicSymbolMultiplier f x : SoninL2) t
  rw [hzf, hz]
  simp only [Pi.smul_apply, hf]
  change (z * f t) * x t = z * (f t * x t)
  ring

theorem cubicSymbolMultiplier_adjoint (f : CubicSymbols) :
    adjoint (cubicSymbolMultiplier f) = cubicSymbolMultiplier (star f) := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cubicSymbolMultiplier_ae (star f) x,
    cubicSymbolMultiplier_ae f y] with t hx hy
  rw [hx, hy, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  change starRingEnd ℂ (star (f t)) * starRingEnd ℂ (x t) * y t =
    starRingEnd ℂ (x t) * (f t * y t)
  simp only [starRingEnd_apply, star_star]
  ring

theorem cubicSymbolMultiplier_schwartz (f : SchwartzMap ℝ ℂ) :
    cubicSymbolMultiplier f.toBoundedContinuousFunction = ccmSchwartzMultiplier f := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [cubicSymbolMultiplier_ae f.toBoundedContinuousFunction x,
    ccmSchwartzMultiplier_coeFn f x] with t h h'
  exact h.trans h'.symm

section Blocks
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev CubicTwoChannel (H : Type*) := HilbertSum H H
def cubicBlock (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    CubicTwoChannel H →L[ℂ] CubicTwoChannel H :=
  hilbertSumInl ∘L (M 0 0 ∘L hilbertSumFst + M 0 1 ∘L hilbertSumSnd) +
    hilbertSumInr ∘L (M 1 0 ∘L hilbertSumFst + M 1 1 ∘L hilbertSumSnd)

@[simp] theorem cubicBlock_fst (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H))
    (x : CubicTwoChannel H) :
    hilbertSumFst (cubicBlock M x) = M 0 0 (hilbertSumFst x) + M 0 1 (hilbertSumSnd x) := by
  simp [cubicBlock, ContinuousLinearMap.comp_apply, map_add,
    -hilbertSumFst_apply, -hilbertSumSnd_apply]
@[simp] theorem cubicBlock_snd (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H))
    (x : CubicTwoChannel H) :
    hilbertSumSnd (cubicBlock M x) = M 1 0 (hilbertSumFst x) + M 1 1 (hilbertSumSnd x) := by
  simp [cubicBlock, ContinuousLinearMap.comp_apply, map_add,
    -hilbertSumFst_apply, -hilbertSumSnd_apply]

theorem cubicBlock_mul (M N : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    cubicBlock (M*N) = cubicBlock M * cubicBlock N := by
  apply ContinuousLinearMap.ext
  intro x
  apply hilbertSum_ext
  · simp only [mul_apply_eq_comp, cubicBlock_fst, cubicBlock_snd,
      Matrix.mul_apply, Fin.sum_univ_two, add_apply, map_add]
    abel
  · simp only [mul_apply_eq_comp, cubicBlock_fst, cubicBlock_snd,
      Matrix.mul_apply, Fin.sum_univ_two, add_apply, map_add]
    abel
theorem cubicBlock_add (M N : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    cubicBlock (M+N) = cubicBlock M + cubicBlock N := by
  apply ContinuousLinearMap.ext
  intro x
  apply hilbertSum_ext <;>
    simp only [add_apply, map_add, cubicBlock_fst, cubicBlock_snd,
      Matrix.add_apply] <;> abel
theorem cubicBlock_one : cubicBlock (1 : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply hilbertSum_ext <;> simp [-hilbertSumFst_apply, -hilbertSumSnd_apply]
theorem cubicBlock_zero : cubicBlock (0 : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply hilbertSum_ext <;> simp [-hilbertSumFst_apply, -hilbertSumSnd_apply]

def cubicBlockHom : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H) →+*
    (CubicTwoChannel H →L[ℂ] CubicTwoChannel H) where
  toFun := cubicBlock
  map_one' := cubicBlock_one
  map_zero' := cubicBlock_zero
  map_add' := cubicBlock_add
  map_mul' := cubicBlock_mul

theorem cubicBlock_smul (z : ℂ) (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    cubicBlock (z • M) = z • cubicBlock M := by
  apply ContinuousLinearMap.ext
  intro x
  apply hilbertSum_ext <;>
    simp [smul_add, -hilbertSumFst_apply, -hilbertSumSnd_apply]

variable [CompleteSpace H]

theorem cubicBlock_adjoint (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    adjoint (cubicBlock M) = cubicBlock M.conjTranspose := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change inner ℂ (hilbertSumFst (cubicBlock M.conjTranspose x)) (hilbertSumFst y) +
    inner ℂ (hilbertSumSnd (cubicBlock M.conjTranspose x)) (hilbertSumSnd y) =
    inner ℂ (hilbertSumFst x) (hilbertSumFst (cubicBlock M y)) +
    inner ℂ (hilbertSumSnd x) (hilbertSumSnd (cubicBlock M y))
  simp only [cubicBlock_fst, cubicBlock_snd, Matrix.conjTranspose_apply,
    ContinuousLinearMap.star_eq_adjoint, inner_add_left, inner_add_right, adjoint_inner_left]
  ring

theorem cubicBlock_diagonal (A B : H →L[ℂ] H) :
    cubicBlock !![A, 0; 0, B] = hilbertBlockDiagonal A B := by
  apply ContinuousLinearMap.ext
  intro x
  apply hilbertSum_ext <;> simp [-hilbertSumFst_apply, -hilbertSumSnd_apply]

private theorem cubicInl_adjoint :
    adjoint (hilbertSumInl : H →L[ℂ] CubicTwoChannel H) = hilbertSumFst := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  rw [WithLp.prod_inner_apply]
  change inner ℂ x.ofLp.1 y = inner ℂ x.ofLp.1 y + inner ℂ x.ofLp.2 0
  simp

private theorem cubicInr_adjoint :
    adjoint (hilbertSumInr : H →L[ℂ] CubicTwoChannel H) = hilbertSumSnd := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  rw [WithLp.prod_inner_apply]
  change inner ℂ x.ofLp.2 y = inner ℂ x.ofLp.1 0 + inner ℂ x.ofLp.2 y
  simp

theorem cubicBlock_diagonal_trace (A B : H →L[ℂ] H)
    (hA : MemSchattenClass 1 A) (hB : MemSchattenClass 1 B) :
    MemSchattenClass 1 (cubicBlock !![A, 0; 0, B]) ∧
      opTrace (cubicBlock !![A, 0; 0, B]) = opTrace A + opTrace B := by
  let J : H →L[ℂ] CubicTwoChannel H := hilbertSumInl
  let L : H →L[ℂ] CubicTwoChannel H := hilbertSumInr
  have hJ : adjoint J ∘L J = 1 := by
    change adjoint (hilbertSumInl : H →L[ℂ] CubicTwoChannel H) ∘L hilbertSumInl = 1
    rw [cubicInl_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have hL : adjoint L ∘L L = 1 := by
    change adjoint (hilbertSumInr : H →L[ℂ] CubicTwoChannel H) ∘L hilbertSumInr = 1
    rw [cubicInr_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    rfl
  have heq : cubicBlock !![A, 0; 0, B] = (J ∘L A) ∘L adjoint J + (L ∘L B) ∘L adjoint L := by
    dsimp [J, L]
    rw [cubicInl_adjoint, cubicInr_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    apply hilbertSum_ext <;> simp [ContinuousLinearMap.comp_apply, -hilbertSumFst_apply, -hilbertSumSnd_apply]
  have hJA := memSchattenClass_one_sandwich J hA
  have hLB := memSchattenClass_one_sandwich L hB
  rw [heq]
  refine ⟨hJA.one_add hLB, ?_⟩
  rw [opTrace_add_of_memSchattenClass_one hJA hLB, opTrace_sandwich J A hA,
    opTrace_sandwich L B hB, hJ, hL]
  rfl
omit [CompleteSpace H] in
 theorem cubicBlock_nuclear (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H))
    (hM : ∀ i j, MemSchattenClass 1 (M i j)) : MemSchattenClass 1 (cubicBlock M) := by
  have hcorner (A : H →L[ℂ] CubicTwoChannel H) (B : CubicTwoChannel H →L[ℂ] H)
      (T : H →L[ℂ] H) (hT : MemSchattenClass 1 T) : MemSchattenClass 1 (A ∘L T ∘L B) := by
    rw [← memRectSchattenClass_iff_memSchattenClass, memRectSchattenClass_one_iff]
    exact summable_rectApproxNumber_comp_left
      (summable_rectApproxNumber_comp_right ((memRectSchattenClass_one_iff T).mp hT) B) A
  have h00 := hcorner hilbertSumInl hilbertSumFst (M 0 0) (hM 0 0)
  have h01 := hcorner hilbertSumInl hilbertSumSnd (M 0 1) (hM 0 1)
  have h10 := hcorner hilbertSumInr hilbertSumFst (M 1 0) (hM 1 0)
  have h11 := hcorner hilbertSumInr hilbertSumSnd (M 1 1) (hM 1 1)
  simpa only [cubicBlock, ContinuousLinearMap.comp_add] using
    (h00.one_add h01).one_add (h10.one_add h11)
end Blocks

def cubicMatrixMultiplier : Matrix (Fin 2) (Fin 2) CubicSymbols →+*
    (CubicTwoChannel SoninL2 →L[ℂ] CubicTwoChannel SoninL2) :=
  cubicBlockHom.comp cubicSymbolMultiplierHom.mapMatrix

theorem cubicMatrixMultiplier_adjoint (M : Matrix (Fin 2) (Fin 2) CubicSymbols) :
    adjoint (cubicMatrixMultiplier M) = cubicMatrixMultiplier M.conjTranspose := by
  change adjoint (cubicBlock (M.map cubicSymbolMultiplier)) =
    cubicBlock (M.conjTranspose.map cubicSymbolMultiplier)
  rw [cubicBlock_adjoint]
  congr 1
  apply Matrix.ext
  intro i j
  exact cubicSymbolMultiplier_adjoint (M j i)

theorem cubicMatrixMultiplier_smul (z : ℂ) (M : Matrix (Fin 2) (Fin 2) CubicSymbols) :
    cubicMatrixMultiplier (z • M) = z • cubicMatrixMultiplier M := by
  change cubicBlock ((z • M).map cubicSymbolMultiplier) = z • cubicBlock (M.map cubicSymbolMultiplier)
  rw [← cubicBlock_smul]
  congr 1
  apply Matrix.ext
  intro i j
  exact cubicSymbolMultiplier_smul z (M i j)

def cubicHardyCutoff : CubicTwoChannel SoninL2 →L[ℂ] CubicTwoChannel SoninL2 :=
  cubicBlock !![ccmHardyProjection, 0; 0, ccmHardyProjection]

def cubicHardyBoundary (f : CubicSymbols) : SoninL2 →L[ℂ] SoninL2 :=
  ccmHardyProjection * cubicSymbolMultiplier f - cubicSymbolMultiplier f * ccmHardyProjection

theorem cubicMatrix_boundary (M : Matrix (Fin 2) (Fin 2) CubicSymbols) :
    cubicHardyCutoff * cubicMatrixMultiplier M - cubicMatrixMultiplier M * cubicHardyCutoff =
      cubicBlock (M.map cubicHardyBoundary) := by
  change cubicBlock _ * cubicBlock (M.map cubicSymbolMultiplier) -
    cubicBlock (M.map cubicSymbolMultiplier) * cubicBlock _ = _
  rw [← cubicBlock_mul, ← cubicBlock_mul]
  change cubicBlockHom _ - cubicBlockHom _ = cubicBlockHom _
  rw [← map_sub]
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two, cubicHardyBoundary] <;> rfl

theorem cubicHardyBoundary_schwartz (f : SchwartzMap ℝ ℂ) :
    cubicHardyBoundary f.toBoundedContinuousFunction = (1 / 2 : ℂ) • ccmQuantizedDifferential f := by
  rw [ccmQuantizedDifferential_eq_two_smul_projectionCommutator, smul_smul]
  simp only [div_mul_cancel₀ (1 : ℂ) (show (2 : ℂ) ≠ 0 by norm_num), one_smul,
    cubicHardyBoundary, cubicSymbolMultiplier_schwartz]

theorem cubicHardyBoundary_one : cubicHardyBoundary 1 = 0 := by
  simp [cubicHardyBoundary, cubicSymbolMultiplier_one]
theorem cubicHardyBoundary_add (f g : CubicSymbols) :
    cubicHardyBoundary (f+g) = cubicHardyBoundary f + cubicHardyBoundary g := by
  simp only [cubicHardyBoundary, cubicSymbolMultiplier_add, mul_add, add_mul]
  abel
theorem cubicHardyBoundary_smul (z : ℂ) (f : CubicSymbols) :
    cubicHardyBoundary (z • f) = z • cubicHardyBoundary f := by
  simp only [cubicHardyBoundary, cubicSymbolMultiplier_smul, mul_smul_comm, smul_mul_assoc,
    smul_sub]

theorem cubicHardyBoundary_schwartz_nuclear (f : SchwartzMap ℝ ℂ) :
    MemSchattenClass 1 (cubicHardyBoundary f.toBoundedContinuousFunction) := by
  rw [cubicHardyBoundary_schwartz]
  exact memSchattenClass_one_smul (ccmQuantizedDifferential_memSchattenClass_one f) _

theorem cubicHardyCutoff_idempotent : IsIdempotentElem cubicHardyCutoff := by
  unfold cubicHardyCutoff IsIdempotentElem
  rw [← cubicBlock_mul]
  congr 1
  apply Matrix.ext
  intro i j
  have h : ccmHardyProjection * ccmHardyProjection = ccmHardyProjection := ccmHardyProjection_idempotent
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem cubicHardyCutoff_selfAdjoint : IsSelfAdjoint cubicHardyCutoff := by
  have h : adjoint ccmHardyProjection = ccmHardyProjection :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ccmHardyProjection_symmetric)
  change adjoint (cubicBlock !![ccmHardyProjection, 0; 0, ccmHardyProjection]) =
    cubicBlock !![ccmHardyProjection, 0; 0, ccmHardyProjection]
  rw [cubicBlock_adjoint]
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint, h]

end RHTower
