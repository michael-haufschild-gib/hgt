import GaloisForLFunctions.HTGeometry.UnipotentParameterSubgroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Polynomial unipotent actions and invariant tensor menus

Apply the algebraic-versus-unitary representation distinction and tensor-menu reconstruction
from Gomes, arXiv:2607.24901, to the existing `unipotentUpper` action. The exact invariant
bilinear and sesquilinear forms expose the positive survivors of the metric obstruction.
Area with a marked fixed vector reconstructs the additive group; replacing that vector by
its quadratic tensor leaves a sign ambiguity.

https://arxiv.org/abs/2607.24901
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A single unit shear determines the invariant bilinear forms of the additive unipotent group. -/
theorem unipotentUpper_unit_bilinear_invariants {K : Type*} [Field K]
    (H : Matrix (Fin 2) (Fin 2) K) :
    (unipotentUpper (1 : K))ᵀ * H * unipotentUpper (1 : K) = H ↔
      H = !![0,H 0 1; -H 0 1,H 1 1] := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    have h11 := congrFun (congrFun h 1) 1
    simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two] at h01 h11
    have ha : H 0 0 = 0 := by linear_combination h01
    have hc : H 1 0 = -H 0 1 := by linear_combination h11-h01
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha,hc]
  · intro h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two]

/-- Exact invariant-form classification for the existing polynomial additive-group action. -/
theorem unipotentUpper_bilinear_invariants {K : Type*} [Field K]
    (H : Matrix (Fin 2) (Fin 2) K) :
    (∀ t : K, (unipotentUpper t)ᵀ * H * unipotentUpper t = H) ↔
      H = !![0,H 0 1; -H 0 1,H 1 1] := by
  constructor
  · intro h
    exact (unipotentUpper_unit_bilinear_invariants H).mp (h 1)
  · intro h t
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two]
    ring

/-- Upper and lower unit shears together retain exactly the alternating area forms. -/
theorem two_unipotent_shears_bilinear_invariants {K : Type*} [Field K]
    (H : Matrix (Fin 2) (Fin 2) K) :
    ((unipotentUpper (1 : K))ᵀ * H * unipotentUpper (1 : K) = H ∧
      unipotentUpper (1 : K) * H * (unipotentUpper (1 : K))ᵀ = H) ↔
      H = !![0,H 0 1; -H 0 1,0] := by
  constructor
  · rintro ⟨hu,hl⟩
    have hform := (unipotentUpper_unit_bilinear_invariants H).mp hu
    have he := congrFun (congrFun hl 1) 0
    simp [unipotentUpper,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] at he
    have hd : H 1 1 = 0 := by linear_combination he
    calc
      H = !![0,H 0 1; -H 0 1,H 1 1] := hform
      _ = !![0,H 0 1; -H 0 1,0] := by rw [hd]
  · intro h
    rw [h]
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two]

/-- A single shear's commutant is the two-dimensional algebra of scalar plus square-zero matrices. -/
theorem unipotentUpper_unit_commutant {K : Type*} [Field K]
    (C : Matrix (Fin 2) (Fin 2) K) :
    C * unipotentUpper (1 : K) = unipotentUpper (1 : K) * C ↔
      C = !![C 0 0,C 0 1; 0,C 0 0] := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01
    have hc : C 1 0 = 0 := h00
    have hd : C 1 1 = C 0 0 := by linear_combination -h01
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc,hd]
  · intro h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two]
    ring

/-- The upper and lower shear pair has only scalar commuting endomorphisms. -/
theorem two_unipotent_shears_commutant {K : Type*} [Field K]
    (C : Matrix (Fin 2) (Fin 2) K) :
    ((C * unipotentUpper (1 : K) = unipotentUpper (1 : K) * C) ∧
      C * (unipotentUpper (1 : K))ᵀ = (unipotentUpper (1 : K))ᵀ * C) ↔
      C = C 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · rintro ⟨hu,hl⟩
    have hf := (unipotentUpper_unit_commutant C).mp hu
    have he := congrFun (congrFun hl 0) 0
    simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two] at he
    have hb : C 0 1 = 0 := by linear_combination he
    calc
      C = !![C 0 0,C 0 1; 0,C 0 0] := hf
      _ = C 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb]
  · intro h
    rw [h]
    constructor <;> simp

/-- An upper-unipotent complex matrix is unitary exactly at the neutral parameter. -/
theorem unipotentUpper_unitary_iff (t : ℂ) :
    unipotentUpper t ∈ Matrix.unitaryGroup (Fin 2) ℂ ↔ t = 0 := by
  constructor
  · intro h
    have hu := Matrix.mem_unitaryGroup_iff'.mp h
    have he := congrFun (congrFun hu 0) 1
    simpa [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] using he
  · rintro rfl
    simp

/-- No positive-definite real bilinear metric can be invariant under the nontrivial unit shear. -/
theorem unipotentUpper_no_positive_metric :
    ¬ ∃ H : Matrix (Fin 2) (Fin 2) ℝ, H.PosDef ∧
      (unipotentUpper (1 : ℝ))ᵀ * H * unipotentUpper (1 : ℝ) = H := by
  rintro ⟨H,hpos,hinv⟩
  have hf := (unipotentUpper_unit_bilinear_invariants H).mp hinv
  have hz : H 0 0 = 0 := by
    have he := congrFun (congrFun hf 0) 0
    simpa using he
  have hp : (0 : ℝ) < H 0 0 := hpos.diag_pos
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- Allowing every complex shear parameter collapses sesquilinear invariants to a rank-one corner. -/
theorem complex_unipotent_sesquilinear_invariants (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ z : ℂ, (unipotentUpper z)ᴴ * H * unipotentUpper z = H) ↔
      H = !![0,0;0,H 1 1] := by
  constructor
  · intro h
    have h01 := congrFun (congrFun (h 1) 0) 1
    have h11 := congrFun (congrFun (h 1) 1) 1
    simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] at h01 h11
    have ha : H 0 0 = 0 := by linear_combination h01
    have hc : H 1 0 = -H 0 1 := by linear_combination h11-h01
    have hI := congrFun (congrFun (h Complex.I) 1) 1
    simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,ha,hc] at hI
    have hb : H 0 1 = 0 := by
      have hm : ((-2 : ℂ)*Complex.I) * H 0 1 = 0 := by linear_combination hI
      exact (mul_eq_zero.mp hm).resolve_left
        (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Complex.I_ne_zero)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha,hb,hc]
  · intro h z
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]

/-- The full complex additive action cannot preserve any positive-definite Hermitian metric. -/
theorem complex_unipotent_no_positive_metric :
    ¬ ∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.PosDef ∧
      ∀ z : ℂ, (unipotentUpper z)ᴴ * H * unipotentUpper z = H := by
  rintro ⟨H,hpos,hinv⟩
  have hf := (complex_unipotent_sesquilinear_invariants H).mp hinv
  have hz : H 0 0 = 0 := by
    have he := congrFun (congrFun hf 0) 0
    simpa using he
  have hp : (0 : ℂ) < H 0 0 := hpos.diag_pos
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- Real parameters preserve the larger two-parameter sesquilinear invariant family. -/
theorem real_unipotent_sesquilinear_invariants (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ t : ℝ, (unipotentUpper (t : ℂ))ᴴ * H * unipotentUpper (t : ℂ) = H) ↔
      H = !![0,H 0 1; -H 0 1,H 1 1] := by
  constructor
  · intro h
    apply (unipotentUpper_unit_bilinear_invariants H).mp
    have hs : (unipotentUpper (1 : ℂ))ᴴ = (unipotentUpper (1 : ℂ))ᵀ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipotentUpper]
    simpa only [Complex.ofReal_one,hs] using h 1
  · intro h t
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]
    ring

/-- The alternating area tensor on the two-dimensional source plane. -/
def gomesShearAreaMatrix (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0,1;-1,0]

/-- The rank-one quadratic tensor recording the transverse coordinate without choosing its sign. -/
def gomesShearRankOneMatrix (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0,0;0,1]

/-- Every linear map transports area by its determinant, including singular maps. -/
theorem gomesShearArea_transport {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    Aᵀ * gomesShearAreaMatrix K * A = A.det • gomesShearAreaMatrix K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesShearAreaMatrix,Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- Preserving area is exactly the determinant-one condition. -/
theorem gomesShearArea_preservation_iff {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    Aᵀ * gomesShearAreaMatrix K * A = gomesShearAreaMatrix K ↔ A.det = 1 := by
  rw [gomesShearArea_transport]
  constructor
  · intro h
    have he := congrFun (congrFun h 0) 1
    simpa [gomesShearAreaMatrix] using he
  · intro h
    rw [h,one_smul]

/-- Area plus a marked fixed vector reconstructs precisely the existing additive unipotent group. -/
theorem unipotentUpper_marked_vector_reconstruction {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    (Aᵀ * gomesShearAreaMatrix K * A = gomesShearAreaMatrix K ∧
      A *ᵥ ![1,0] = ![1,0]) ↔ A = unipotentUpper (A 0 1) := by
  constructor
  · rintro ⟨harea,hvec⟩
    have hdet := (gomesShearArea_preservation_iff A).mp harea
    have h0 := congrFun hvec 0
    have h1 := congrFun hvec 1
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at h0 h1
    have h11 : A 1 1 = 1 := by simpa [Matrix.det_fin_two,h0,h1] using hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentUpper,h0,h1,h11]
  · intro h
    rw [h]
    constructor
    · rw [gomesShearArea_preservation_iff,Matrix.det_fin_two]
      simp [unipotentUpper]
    · ext i
      fin_cases i <;> simp [unipotentUpper,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

/-- Replacing the marked vector by its rank-one quadratic tensor leaves exactly a global sign
ambiguity in reconstruction. -/
theorem unipotentUpper_quadratic_reconstruction {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    (Aᵀ * gomesShearAreaMatrix K * A = gomesShearAreaMatrix K ∧
      Aᵀ * gomesShearRankOneMatrix K * A = gomesShearRankOneMatrix K) ↔
      ∃ t : K, A = unipotentUpper t ∨ A = -unipotentUpper t := by
  constructor
  · rintro ⟨harea,hquad⟩
    have hdet := (gomesShearArea_preservation_iff A).mp harea
    have h00 := congrFun (congrFun hquad 0) 0
    have h11 := congrFun (congrFun hquad 1) 1
    simp [gomesShearRankOneMatrix,Matrix.mul_apply,Fin.sum_univ_two] at h00 h11
    have hc : A 1 0 = 0 := h00
    have hdpm : A 1 1 = 1 ∨ A 1 1 = -1 := by
      have hp : (A 1 1 - 1) * (A 1 1 + 1) = 0 := by linear_combination h11
      rcases mul_eq_zero.mp hp with hp | hp
      · left; linear_combination hp
      · right; linear_combination hp
    rcases hdpm with hd | hd
    · have ha : A 0 0 = 1 := by simpa [Matrix.det_fin_two,hc,hd] using hdet
      refine ⟨A 0 1,Or.inl ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipotentUpper,ha,hc,hd]
    · have ha : A 0 0 = -1 := by
        simp [Matrix.det_fin_two,hc,hd] at hdet
        linear_combination -hdet
      refine ⟨-A 0 1,Or.inr ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipotentUpper,ha,hc,hd]
  · rintro ⟨t,h | h⟩ <;> rw [h] <;> constructor <;> ext i j <;>
      fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper,gomesShearAreaMatrix,gomesShearRankOneMatrix,
        Matrix.mul_apply,Fin.sum_univ_two]


end GaloisForLFunctions.HTGeometry
