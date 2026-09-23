import GaloisForLFunctions.HTGeometry.GomesHiggsConjugate
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Reconstructing the weak group and its invariant contraction line

The geometry-first reconstruction in arXiv:2607.24901v1 and the weak-index
contraction mechanism of arXiv:2509.25276v7 act directly on the corpus's Higgs
spinors. Their Hermitian and alternating tensors recover exactly SU(2).
The invariant bilinear coefficient tensors form the volume-contraction line;
this is the weak-index statement, not a classification of full Standard Model
Yukawa couplings. The same tensors force compatibility with the existing causal
spin flip. The geometric U(2) stabilizer fixes one line and rotates its complement.
-/

open scoped Matrix ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The weak alternating contraction transforms by the determinant character. -/
theorem weakVolumeContraction_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (H K : Fin 2 → ℂ) :
    weakVolumeContraction (A.mulVec H) (A.mulVec K) = A.det * weakVolumeContraction H K := by
  simp [weakVolumeContraction, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Pulling both entries through a matrix inserts its Hermitian Gram operator. -/
theorem weakHermitianContraction_mulVec (A : Matrix (Fin 2) (Fin 2) ℂ) (H K : Fin 2 → ℂ) :
    weakHermitianContraction (A.mulVec H) (A.mulVec K) =
      weakHermitianContraction H ((Aᴴ * A).mulVec K) := by
  simp [weakHermitianContraction, Matrix.mulVec, Matrix.mul_apply, dotProduct,
    Fin.sum_univ_two]
  ring

/-- Preserving the weak volume tensor is precisely the determinant-one restriction. -/
theorem weakVolume_preservation_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ H K, weakVolumeContraction (A.mulVec H) (A.mulVec K) = weakVolumeContraction H K) ↔
      A.det = 1 := by
  constructor
  · intro h
    have hh := h ![1,0] ![0,1]
    simpa [weakVolumeContraction_mulVec, weakVolumeContraction, Matrix.det_fin_two, mul_comm] using hh
  · intro h H K
    rw [weakVolumeContraction_mulVec, h, one_mul]

/-- Preserving the weak Hermitian tensor is precisely unitarity. -/
theorem weakHermitian_preservation_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ H K, weakHermitianContraction (A.mulVec H) (A.mulVec K) = weakHermitianContraction H K) ↔
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  constructor
  · intro h
    have h00 := h ![1,0] ![1,0]
    have h01 := h ![1,0] ![0,1]
    have h10 := h ![0,1] ![1,0]
    have h11 := h ![0,1] ![0,1]
    simp [weakHermitianContraction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h10
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
  · intro h H K
    change Aᴴ * A = 1 at h
    rw [weakHermitianContraction_mulVec, h, Matrix.one_mulVec]

/-- The two existing weak contractions recover exactly the special-unitary gauge group. -/
theorem weakTensorMenu_reconstructs_specialUnitary (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ((∀ H K, weakHermitianContraction (A.mulVec H) (A.mulVec K) = weakHermitianContraction H K) ∧
      ∀ H K, weakVolumeContraction (A.mulVec H) (A.mulVec K) = weakVolumeContraction H K) ↔
        A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [weakHermitian_preservation_iff, weakVolume_preservation_iff,
    Matrix.mem_specialUnitaryGroup_iff]

/-- The alternating contraction separates all weak spinors. -/
theorem weakVolumeContraction_left_separates (H K : Fin 2 → ℂ) :
    (∀ L, weakVolumeContraction H L = weakVolumeContraction K L) ↔ H = K := by
  constructor
  · intro h
    have h0 := h ![0,1]
    have h1 := h ![1,0]
    simp [weakVolumeContraction] at h0 h1
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · rintro rfl L
    rfl

/-- A special unitary treats the conjugate Higgs identically to the original doublet. -/
theorem causalSpinFlip_specialUnitary (A : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (H : Fin 2 → ℂ) :
    causalSpinFlip ((A : Matrix (Fin 2) (Fin 2) ℂ).mulVec H) =
      (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec (causalSpinFlip H) := by
  have ht := (weakTensorMenu_reconstructs_specialUnitary A).mpr A.property
  have hsur : Function.Surjective (A : Matrix (Fin 2) (Fin 2) ℂ).mulVec := by
    intro K
    refine ⟨(star (A : Matrix (Fin 2) (Fin 2) ℂ)).mulVec K, ?_⟩
    rw [Matrix.mulVec_mulVec, (Matrix.mem_unitaryGroup_iff.mp A.property.1), Matrix.one_mulVec]
  apply (weakVolumeContraction_left_separates _ _).mp
  intro K
  obtain ⟨L, rfl⟩ := hsur K
  rw [weakVolumeContraction_spinFlip, ht.1 H L, ht.2 (causalSpinFlip H) L,
    weakVolumeContraction_spinFlip]

/-- The real quaternionic matrix form is forced by preservation of the two weak tensors. -/
theorem specialUnitary_quaternionic_matrix_form (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ a b : ℂ, (A : Matrix (Fin 2) (Fin 2) ℂ) = spinFlipQuaternionMatrix a b := by
  exact (causalSpinFlip_matrix_commutant A).mp (causalSpinFlip_specialUnitary A)

/-- Bilinear weak contractions represented by their coefficient tensor. -/
def weakBilinearContraction (B : Matrix (Fin 2) (Fin 2) ℂ) (H K : Fin 2 → ℂ) : ℂ :=
  H 0 * (B 0 0 * K 0 + B 0 1 * K 1) + H 1 * (B 1 0 * K 0 + B 1 1 * K 1)

/-- Every alternating coefficient tensor is a multiple of the existing volume contraction. -/
theorem weakBilinear_alternating (c : ℂ) (H K : Fin 2 → ℂ) :
    weakBilinearContraction !![0,c;-c,0] H K = c * weakVolumeContraction H K := by
  simp [weakBilinearContraction, weakVolumeContraction]
  ring

/-- The invariant bilinear weak tensors form exactly the volume-contraction line. -/
theorem weakBilinear_invariant_classification (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ U : Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ H K,
      weakBilinearContraction B ((U : Matrix (Fin 2) (Fin 2) ℂ).mulVec H)
        ((U : Matrix (Fin 2) (Fin 2) ℂ).mulVec K) = weakBilinearContraction B H K) ↔
      ∃ c : ℂ, B = !![0,c;-c,0] := by
  constructor
  · intro h
    let D : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I,0;0,-Complex.I]
    let J : Matrix (Fin 2) (Fin 2) ℂ := !![0,-1;1,0]
    have hD : D ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [D, Matrix.det_fin_two]
    have hJ : J ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
      constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [J, Matrix.det_fin_two]
    have h00 := h ⟨D,hD⟩ ![1,0] ![1,0]
    have h11 := h ⟨D,hD⟩ ![0,1] ![0,1]
    have h01 := h ⟨J,hJ⟩ ![1,0] ![0,1]
    simp [D, J, weakBilinearContraction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h00 h11 h01
    have hb00 : B 0 0 = 0 := by
      linear_combination (-1/2 : ℂ) * h00 + (B 0 0 / 2) * Complex.I_sq
    have hb11 : B 1 1 = 0 := by
      linear_combination (-1/2 : ℂ) * h11 + (B 1 1 / 2) * Complex.I_sq
    refine ⟨B 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb00, hb11, ← h01]
  · rintro ⟨c,rfl⟩ U H K
    have hdet : (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := U.property.2
    rw [weakBilinear_alternating, weakBilinear_alternating, weakVolumeContraction_mulVec,
      hdet, one_mul]

/-- The geometric rank-two unitary stabilizer consists of a phase on the perpendicular line. -/
theorem weak_unitary_stabilizer_north (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![1,0] = ![1,0] ↔
      ∃ z : Circle, (U : Matrix (Fin 2) (Fin 2) ℂ) = !![1,0;0,(z:ℂ)] := by
  constructor
  · intro h
    have h00 := congrFun h 0
    have h10 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h00 h10
    have hu := Matrix.mem_unitaryGroup_iff'.mp U.property
    have h01 := congrFun (congrFun hu 0) 1
    have h11 := congrFun (congrFun hu 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h10] at h01
    simp [Matrix.mul_apply, Fin.sum_univ_two, h01] at h11
    have hn : ‖U 1 1‖ = 1 := by
      have hs : ‖U 1 1‖ ^ (2 : ℕ) = 1 := by
        rw [← Complex.normSq_eq_norm_sq]
        apply Complex.ofReal_injective
        simpa only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one] using h11
      have hp := norm_nonneg (U 1 1)
      nlinarith
    refine ⟨⟨U 1 1, mem_sphere_zero_iff_norm.mpr hn⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h01]
  · rintro ⟨z,hz⟩
    rw [hz]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end GaloisForLFunctions.HTGeometry
