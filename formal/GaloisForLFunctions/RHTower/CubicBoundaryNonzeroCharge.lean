import GaloisForLFunctions.RHTower.CubicTwoChannelHardySource
import GaloisForLFunctions.RHTower.CubicBoundaryLoopPulse

/-!
# A nonzero ordinary cubic trace from three orthogonal projections

The exact trace is `3 * sqrt 3 / (2 * pi)`. Only the combined cubic is nuclear.
The source is a smooth two-orientation matrix loop; its aggregate and cyclic current
commute before Hardy compression. Nuclear projection rounding retains its boundary pairing.

This refutes unrestricted combined-only cubic trace conservation. It does not contradict
commuting-source, mixed-product nuclear, or discrete-aggregate conservation, and does not
identify the constructed loop with a Xi divisor or primitive prime budget. Known parents
are the Hardy trace cocycle and trace-class spectral rounding; see the linked research card
`docs/drafts/pipeline/1-in-progress/cubic-aggregate-spectral-current.md` for novelty scope.
-/

open MeasureTheory ContinuousLinearMap Complex
open scoped ComplexConjugate
noncomputable section
namespace RHTower

def cubicBloch (a b c : CubicSymbols) : Matrix (Fin 2) (Fin 2) CubicSymbols :=
  !![(1 / 2 : ℂ) • (1 + a), (1 / 2 : ℂ) • b - (I / 2) • c;
    (1 / 2 : ℂ) • b + (I / 2) • c, (1 / 2 : ℂ) • (1 - a)]

theorem cubicBloch_idempotent (a b c : CubicSymbols)
    (h : ∀ t, a t ^ (2 : ℕ) + b t ^ (2 : ℕ) + c t ^ (2 : ℕ) = 1) :
    IsIdempotentElem (cubicBloch a b c) := by
  change cubicBloch a b c * cubicBloch a b c = cubicBloch a b c
  apply Matrix.ext
  intro i j
  apply BoundedContinuousFunction.ext
  intro t
  have hi := I_mul_I
  fin_cases i <;> fin_cases j <;>
    simp [cubicBloch, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  · linear_combination (1 / 4 : ℂ) * h t - c t ^ (2 : ℕ) / 4 * hi
  · ring
  · ring
  · linear_combination (1 / 4 : ℂ) * h t - c t ^ (2 : ℕ) / 4 * hi

theorem cubicBloch_selfAdjoint (a b c : CubicSymbols)
    (ha : ∀ t, star (a t) = a t) (hb : ∀ t, star (b t) = b t)
    (hc : ∀ t, star (c t) = c t) :
    (cubicBloch a b c).conjTranspose = cubicBloch a b c := by
  apply Matrix.ext
  intro i j
  apply BoundedContinuousFunction.ext
  intro t
  fin_cases i <;> fin_cases j <;>
    simp [cubicBloch, Matrix.conjTranspose_apply, smul_eq_mul,
      ha, hb, hc] <;> ring

def cubicSourceA : CubicSymbols := 1 + cubicLoopFSchwartz.toBoundedContinuousFunction
def cubicSourceB : CubicSymbols := cubicLoopBSchwartz.toBoundedContinuousFunction
def cubicSourceC : CubicSymbols := cubicLoopCSchwartz.toBoundedContinuousFunction
def cubicSourceG : CubicSymbols := cubicLoopGSchwartz.toBoundedContinuousFunction

@[simp] theorem cubicSourceA_apply (t : ℝ) : cubicSourceA t = (cubicLoopA t : ℂ) := by
  simp [cubicSourceA]
@[simp] theorem cubicSourceB_apply (t : ℝ) : cubicSourceB t = (cubicLoopB t : ℂ) := rfl
@[simp] theorem cubicSourceC_apply (t : ℝ) : cubicSourceC t = (cubicLoopC t : ℂ) := rfl
@[simp] theorem cubicSourceG_apply (t : ℝ) : cubicSourceG t = (cubicLoopFlux t : ℂ) := rfl

def cubicSourceP := cubicBloch cubicSourceA cubicSourceB 0
def cubicSourceQ := cubicBloch cubicSourceA ((-1 / 2 : ℂ) • cubicSourceB)
  ((-(Real.sqrt 3 : ℂ) / 2) • cubicSourceC)
def cubicSourceR := cubicBloch cubicSourceA ((-1 / 2 : ℂ) • cubicSourceB)
  (((Real.sqrt 3 : ℂ) / 2) • cubicSourceC)

theorem cubicSourceP_idempotent : IsIdempotentElem cubicSourceP := by
  apply cubicBloch_idempotent
  intro t
  simpa using congrArg Complex.ofReal (cubicLoop_circle t)

theorem cubicSourceQ_idempotent : IsIdempotentElem cubicSourceQ := by
  apply cubicBloch_idempotent
  intro t
  have h1 : (cubicLoopA t : ℂ) ^ (2 : ℕ) + (cubicLoopB t : ℂ) ^ (2 : ℕ) = 1 := by
    exact_mod_cast cubicLoop_circle t
  have h2 : (cubicLoopC t : ℂ) ^ (2 : ℕ) = (cubicLoopB t : ℂ) ^ (2 : ℕ) := by
    exact_mod_cast cubicLoopC_sq t
  have h3 : (Real.sqrt 3 : ℂ) ^ (2 : ℕ) = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [cubicSourceA_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul,
    cubicSourceB_apply, cubicSourceC_apply]
  linear_combination h1 + (3 / 4 : ℂ) * h2 + (cubicLoopC t : ℂ) ^ (2 : ℕ) / 4 * h3

theorem cubicSourceR_idempotent : IsIdempotentElem cubicSourceR := by
  apply cubicBloch_idempotent
  intro t
  have h1 : (cubicLoopA t : ℂ) ^ (2 : ℕ) + (cubicLoopB t : ℂ) ^ (2 : ℕ) = 1 := by
    exact_mod_cast cubicLoop_circle t
  have h2 : (cubicLoopC t : ℂ) ^ (2 : ℕ) = (cubicLoopB t : ℂ) ^ (2 : ℕ) := by
    exact_mod_cast cubicLoopC_sq t
  have h3 : (Real.sqrt 3 : ℂ) ^ (2 : ℕ) = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  simp only [cubicSourceA_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul,
    cubicSourceB_apply, cubicSourceC_apply]
  linear_combination h1 + (3 / 4 : ℂ) * h2 + (cubicLoopC t : ℂ) ^ (2 : ℕ) / 4 * h3

theorem cubicSourceP_selfAdjoint : cubicSourceP.conjTranspose = cubicSourceP := by
  apply cubicBloch_selfAdjoint <;> intro t <;> simp
theorem cubicSourceQ_selfAdjoint : cubicSourceQ.conjTranspose = cubicSourceQ := by
  apply cubicBloch_selfAdjoint <;> intro t <;> simp [smul_eq_mul]
theorem cubicSourceR_selfAdjoint : cubicSourceR.conjTranspose = cubicSourceR := by
  apply cubicBloch_selfAdjoint <;> intro t <;> simp [smul_eq_mul]

def cubicSourceSum : Matrix (Fin 2) (Fin 2) CubicSymbols :=
  cubicSourceP + cubicSourceQ + cubicSourceR
def cubicSourceCurrent : Matrix (Fin 2) (Fin 2) CubicSymbols :=
  (cubicSourceP*cubicSourceQ-cubicSourceQ*cubicSourceP) +
    (cubicSourceQ*cubicSourceR-cubicSourceR*cubicSourceQ) +
    (cubicSourceR*cubicSourceP-cubicSourceP*cubicSourceR)

theorem cubicSourceSum_diagonal : cubicSourceSum =
    !![(3 / 2 : ℂ) • (1 + cubicSourceA), 0; 0, (3 / 2 : ℂ) • (1 - cubicSourceA)] := by
  apply Matrix.ext
  intro i j
  apply BoundedContinuousFunction.ext
  intro t
  fin_cases i <;> fin_cases j <;>
    simp [cubicSourceSum, cubicSourceP, cubicSourceQ, cubicSourceR, cubicBloch, smul_eq_mul] <;> ring

theorem cubicSourceCurrent_diagonal : cubicSourceCurrent =
    !![(-I * 3 * (Real.sqrt 3 : ℂ) / 4) • cubicSourceG, 0;
      0, (I * 3 * (Real.sqrt 3 : ℂ) / 4) • cubicSourceG] := by
  apply Matrix.ext
  intro i j
  apply BoundedContinuousFunction.ext
  intro t
  fin_cases i <;> fin_cases j <;>
    simp [cubicSourceCurrent, cubicSourceP, cubicSourceQ, cubicSourceR, cubicBloch,
      smul_eq_mul, cubicLoopFlux, ofReal_mul] <;> ring

theorem cubicSource_flat : cubicSourceSum * cubicSourceCurrent = cubicSourceCurrent * cubicSourceSum := by
  rw [cubicSourceSum_diagonal, cubicSourceCurrent_diagonal]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def cubicAdmittedSymbols : Submodule ℂ CubicSymbols where
  carrier := {f | MemSchattenClass 1 (cubicHardyBoundary f)}
  zero_mem' := by
    have h : cubicHardyBoundary 0 = 0 := by
      simp [cubicHardyBoundary, cubicSymbolMultiplier_zero]
    rw [Set.mem_setOf_eq, h]
    have hn := ccmQuantizedDifferential_memSchattenClass_one cubicLoopFSchwartz
    simpa using hn.one_sub hn
  add_mem' := by
    intro f g hf hg
    change MemSchattenClass 1 (cubicHardyBoundary (f+g))
    rw [cubicHardyBoundary_add]
    exact hf.one_add hg
  smul_mem' := by
    intro z f hf
    change MemSchattenClass 1 (cubicHardyBoundary (z • f))
    rw [cubicHardyBoundary_smul]
    exact memSchattenClass_one_smul hf z

theorem cubicAdmittedSymbols_one : (1 : CubicSymbols) ∈ cubicAdmittedSymbols := by
  change MemSchattenClass 1 (cubicHardyBoundary 1)
  rw [cubicHardyBoundary_one]
  have hn := ccmQuantizedDifferential_memSchattenClass_one cubicLoopFSchwartz
  simpa using hn.one_sub hn

theorem cubicBloch_admitted (a b c : CubicSymbols)
    (ha : a ∈ cubicAdmittedSymbols) (hb : b ∈ cubicAdmittedSymbols) (hc : c ∈ cubicAdmittedSymbols) :
    ∀ i j, cubicBloch a b c i j ∈ cubicAdmittedSymbols := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact cubicAdmittedSymbols.smul_mem _ (cubicAdmittedSymbols.add_mem cubicAdmittedSymbols_one ha)
  · exact cubicAdmittedSymbols.sub_mem (cubicAdmittedSymbols.smul_mem _ hb)
      (cubicAdmittedSymbols.smul_mem _ hc)
  · exact cubicAdmittedSymbols.add_mem (cubicAdmittedSymbols.smul_mem _ hb)
      (cubicAdmittedSymbols.smul_mem _ hc)
  · exact cubicAdmittedSymbols.smul_mem _ (cubicAdmittedSymbols.sub_mem cubicAdmittedSymbols_one ha)

theorem cubicSourceA_admitted : cubicSourceA ∈ cubicAdmittedSymbols :=
  cubicAdmittedSymbols.add_mem cubicAdmittedSymbols_one
    (cubicHardyBoundary_schwartz_nuclear cubicLoopFSchwartz)
theorem cubicSourceB_admitted : cubicSourceB ∈ cubicAdmittedSymbols :=
  cubicHardyBoundary_schwartz_nuclear cubicLoopBSchwartz
theorem cubicSourceC_admitted : cubicSourceC ∈ cubicAdmittedSymbols :=
  cubicHardyBoundary_schwartz_nuclear cubicLoopCSchwartz

theorem cubicSourceP_admitted : ∀ i j, cubicSourceP i j ∈ cubicAdmittedSymbols :=
  cubicBloch_admitted _ _ _ cubicSourceA_admitted cubicSourceB_admitted cubicAdmittedSymbols.zero_mem
theorem cubicSourceQ_admitted : ∀ i j, cubicSourceQ i j ∈ cubicAdmittedSymbols :=
  cubicBloch_admitted _ _ _ cubicSourceA_admitted
    (cubicAdmittedSymbols.smul_mem _ cubicSourceB_admitted)
    (cubicAdmittedSymbols.smul_mem _ cubicSourceC_admitted)
theorem cubicSourceR_admitted : ∀ i j, cubicSourceR i j ∈ cubicAdmittedSymbols :=
  cubicBloch_admitted _ _ _ cubicSourceA_admitted
    (cubicAdmittedSymbols.smul_mem _ cubicSourceB_admitted)
    (cubicAdmittedSymbols.smul_mem _ cubicSourceC_admitted)

theorem cubicMatrix_boundary_nuclear (M : Matrix (Fin 2) (Fin 2) CubicSymbols)
    (h : ∀ i j, M i j ∈ cubicAdmittedSymbols) :
    MemSchattenClass 1 (cubicHardyCutoff * cubicMatrixMultiplier M -
      cubicMatrixMultiplier M * cubicHardyCutoff) := by
  rw [cubicMatrix_boundary]
  exact cubicBlock_nuclear _ h

theorem cubicHardyBoundary_zero : cubicHardyBoundary 0 = 0 := by
  simp [cubicHardyBoundary, cubicSymbolMultiplier_zero]

theorem cubicMatrixMultiplier_diagonal (f g : CubicSymbols) :
    cubicMatrixMultiplier !![f, 0; 0, g] =
      cubicBlock !![cubicSymbolMultiplier f, 0; 0, cubicSymbolMultiplier g] := by
  change cubicBlock _ = cubicBlock _
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cubicSymbolMultiplier_zero, cubicSymbolMultiplierHom]

theorem cubicHardyBoundary_neg (f : CubicSymbols) : cubicHardyBoundary (-f) = -cubicHardyBoundary f := by
  have h : cubicSymbolMultiplier (-f) = -cubicSymbolMultiplier f := cubicSymbolMultiplierHom.map_neg f
  simp [cubicHardyBoundary, h]
  abel

theorem cubicSourceG_boundary_trace : opTrace (cubicHardyBoundary cubicSourceG) = 0 := by
  rw [cubicSourceG, cubicHardyBoundary_schwartz, opTrace_smul,
    opTrace_ccmQuantizedDifferential_eq_zero, mul_zero]

theorem cubicSourceF_boundary_pairing :
    opTrace (ccmSchwartzMultiplier cubicLoopFSchwartz * cubicHardyBoundary cubicSourceG) =
      4 * I / (3 * (Real.pi : ℂ)) := by
  rw [cubicSourceG, cubicHardyBoundary_schwartz, mul_smul_comm, opTrace_smul,
    opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_local, integral_cubicLoop_Schwartz_pairing]
  ring

theorem cubicSourceA_boundary_pairing :
    opTrace (cubicSymbolMultiplier cubicSourceA * cubicHardyBoundary cubicSourceG) =
      4 * I / (3 * (Real.pi : ℂ)) := by
  have hD := cubicHardyBoundary_schwartz_nuclear cubicLoopGSchwartz
  change MemSchattenClass 1 (cubicHardyBoundary cubicSourceG) at hD
  have hFD := memSchattenClass_one_comp_left hD (ccmSchwartzMultiplier cubicLoopFSchwartz)
  change MemSchattenClass 1 (ccmSchwartzMultiplier cubicLoopFSchwartz * cubicHardyBoundary cubicSourceG) at hFD
  rw [cubicSourceA, cubicSymbolMultiplier_add, cubicSymbolMultiplier_one,
    cubicSymbolMultiplier_schwartz, add_mul, one_mul,
    opTrace_add_of_memSchattenClass_one hD hFD, cubicSourceG_boundary_trace,
    cubicSourceF_boundary_pairing, zero_add]

theorem cubicSource_boundary_charge :
    opTrace (cubicMatrixMultiplier cubicSourceSum *
      (cubicHardyCutoff*cubicMatrixMultiplier cubicSourceCurrent -
        cubicMatrixMultiplier cubicSourceCurrent*cubicHardyCutoff)) =
      3 * (Real.sqrt 3 : ℂ) / (Real.pi : ℂ) := by
  let A := cubicSymbolMultiplier cubicSourceA
  let D := cubicHardyBoundary cubicSourceG
  let z : ℂ := I * 3 * (Real.sqrt 3 : ℂ) / 4
  have hD : MemSchattenClass 1 D := cubicHardyBoundary_schwartz_nuclear cubicLoopGSchwartz
  have hAD := memSchattenClass_one_comp_left hD A
  change MemSchattenClass 1 (A*D) at hAD
  have htraceD : opTrace D = 0 := cubicSourceG_boundary_trace
  have htraceAD : opTrace (A*D) = 4*I/(3*(Real.pi : ℂ)) := cubicSourceA_boundary_pairing
  have hsub : cubicSymbolMultiplier (1-cubicSourceA) = 1-A := by
    change cubicSymbolMultiplierHom (1-cubicSourceA) = 1-cubicSymbolMultiplierHom cubicSourceA
    rw [map_sub, map_one]
  have hS : cubicMatrixMultiplier cubicSourceSum =
      cubicBlock !![(3/2 : ℂ) • (1+A), 0; 0, (3/2 : ℂ) • (1-A)] := by
    rw [cubicSourceSum_diagonal, cubicMatrixMultiplier_diagonal]
    congr 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicSymbolMultiplier_smul, cubicSymbolMultiplier_add, cubicSymbolMultiplier_one, hsub, A]
  have hK : cubicHardyCutoff*cubicMatrixMultiplier cubicSourceCurrent -
      cubicMatrixMultiplier cubicSourceCurrent*cubicHardyCutoff =
      cubicBlock !![(-z) • D, 0; 0, z • D] := by
    rw [cubicMatrix_boundary, cubicSourceCurrent_diagonal]
    congr 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, cubicHardyBoundary_smul, cubicHardyBoundary_zero,
        cubicHardyBoundary_neg, z, D, neg_mul, neg_div]
  rw [hS, hK, ← cubicBlock_mul]
  have heq : !![(3/2 : ℂ) • (1+A), 0; 0, (3/2 : ℂ) • (1-A)] *
      !![(-z) • D, 0; 0, z • D] =
      !![((-3/2 : ℂ)*z) • (D+A*D), 0; 0, ((3/2 : ℂ)*z) • (D-A*D)] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two,
        smul_smul, add_mul, sub_mul, smul_add, smul_sub] <;> module
  rw [heq]
  have hleft := memSchattenClass_one_smul (hD.one_add hAD) ((-3/2 : ℂ)*z)
  have hright := memSchattenClass_one_smul (hD.one_sub hAD) ((3/2 : ℂ)*z)
  rw [(cubicBlock_diagonal_trace _ _ hleft hright).2, opTrace_smul, opTrace_smul,
    opTrace_add_of_memSchattenClass_one hD hAD, opTrace_sub_of_memSchattenClass_one hD hAD,
    htraceD, htraceAD]
  dsimp [z]
  ring_nf
  simp [I_sq]

/-- Three genuine orthogonal projections with a nuclear combined cubic and nonzero charge.
No individual displacement, cube, or adjacent product is assumed nuclear. -/
theorem exists_projections_with_nonzero_cubic_trace :
    ∃ P Q R : CubicTwoChannel SoninL2 →L[ℂ] CubicTwoChannel SoninL2,
      IsSelfAdjoint P ∧ IsSelfAdjoint Q ∧ IsSelfAdjoint R ∧
      IsIdempotentElem P ∧ IsIdempotentElem Q ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      opTrace (formationAnchoredCubicAssociator R Q P) =
        3 * (Real.sqrt 3 : ℂ) / (2 * (Real.pi : ℂ)) := by
  let A := cubicMatrixMultiplier cubicSourceP
  let B := cubicMatrixMultiplier cubicSourceQ
  let C := cubicMatrixMultiplier cubicSourceR
  have hi (M : Matrix (Fin 2) (Fin 2) CubicSymbols) (h : IsIdempotentElem M) :
      IsIdempotentElem (cubicMatrixMultiplier M) := by
    change cubicMatrixMultiplier M * cubicMatrixMultiplier M = cubicMatrixMultiplier M
    rw [← map_mul, h]
  have hs (M : Matrix (Fin 2) (Fin 2) CubicSymbols) (h : M.conjTranspose = M) :
      IsSelfAdjoint (cubicMatrixMultiplier M) := by
    change adjoint (cubicMatrixMultiplier M) = cubicMatrixMultiplier M
    rw [cubicMatrixMultiplier_adjoint, h]
  have hS : cubicAggregate A B C = cubicMatrixMultiplier cubicSourceSum := by
    simp [cubicAggregate, A, B, C, cubicSourceSum, map_add]
  have hK : cubicCyclicCurrent A B C = cubicMatrixMultiplier cubicSourceCurrent := by
    simp [cubicCyclicCurrent, A, B, C, cubicSourceCurrent, map_add, map_sub, map_mul]
  have hflat : cubicAggregate A B C * cubicCyclicCurrent A B C =
      cubicCyclicCurrent A B C * cubicAggregate A B C := by
    rw [hS, hK, ← map_mul, ← map_mul, cubicSource_flat]
  obtain ⟨P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,_hPA,_hQB,_hRC,hCubic,htrace⟩ :=
    exists_rounded_cubic_with_boundary_trace cubicHardyCutoff A B C
      cubicHardyCutoff_idempotent cubicHardyCutoff_selfAdjoint
      (hi _ cubicSourceP_idempotent) (hi _ cubicSourceQ_idempotent) (hi _ cubicSourceR_idempotent)
      (hs _ cubicSourceP_selfAdjoint) (hs _ cubicSourceQ_selfAdjoint) (hs _ cubicSourceR_selfAdjoint)
      (cubicMatrix_boundary_nuclear _ cubicSourceP_admitted)
      (cubicMatrix_boundary_nuclear _ cubicSourceQ_admitted)
      (cubicMatrix_boundary_nuclear _ cubicSourceR_admitted) hflat
  refine ⟨P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,hCubic,?_⟩
  rw [hS, hK, cubicSource_boundary_charge] at htrace
  linear_combination (1/2 : ℂ) * htrace

/-- Combined cubic trace-class admission alone does not imply trace conservation. -/
theorem not_cubic_trace_conservation_of_combined_nuclearity :
    ¬ (∀ P Q R : CubicTwoChannel SoninL2 →L[ℂ] CubicTwoChannel SoninL2,
      IsSelfAdjoint P → IsSelfAdjoint Q → IsSelfAdjoint R →
      IsIdempotentElem P → IsIdempotentElem Q → IsIdempotentElem R →
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) →
      opTrace (formationAnchoredCubicAssociator R Q P) = 0) := by
  intro h
  obtain ⟨P,Q,R,hPs,hQs,hRs,hPi,hQi,hRi,hC,htrace⟩ := exists_projections_with_nonzero_cubic_trace
  have hz := h P Q R hPs hQs hRs hPi hQi hRi hC
  rw [htrace] at hz
  have hsqrt : (Real.sqrt 3 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)))
  exact (div_ne_zero (mul_ne_zero (by norm_num) hsqrt)
    (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))) hz

end RHTower
