import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.Option
import GaloisForLFunctions.HTGeometry.SquareMatrixCorankOne

/-!
# Exact nonsingularity criterion for a symmetric border

For a symmetric matrix with a specified nonzero kernel vector `κ`, adjoining
a row and column `w` produces a nonsingular matrix exactly when the original
kernel is the line through `κ` and `w` pairs nontrivially with that line.
The criterion works over every field, including characteristic two.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix

variable {F ι : Type*} [Field F] [Fintype ι]

/-- Add one symmetric row and column, with zero at the new corner. -/
def symmetricBorder (M : Matrix ι ι F) (w : ι → F) : Matrix (Option ι) (Option ι) F
  | some i, some j => M i j
  | some i, none => w i
  | none, some j => w j
  | none, none => 0

@[simp] theorem symmetricBorder_mulVec_some (M : Matrix ι ι F) (w : ι → F)
    (z : Option ι → F) (i : ι) :
    (symmetricBorder M w *ᵥ z) (some i) =
      (M *ᵥ fun j => z (some j)) i + w i * z none := by
  simp only [mulVec, dotProduct, Fintype.sum_option, symmetricBorder, add_comm]

@[simp] theorem symmetricBorder_mulVec_none (M : Matrix ι ι F) (w : ι → F)
    (z : Option ι → F) :
    (symmetricBorder M w *ᵥ z) none = w ⬝ᵥ (fun j => z (some j)) := by
  simp only [mulVec, dotProduct, Fintype.sum_option, symmetricBorder, zero_mul, zero_add]

theorem symmetricBorder_kernel_iff (M : Matrix ι ι F) (w : ι → F) (z : Option ι → F) :
    symmetricBorder M w *ᵥ z = 0 ↔
      M *ᵥ (fun j => z (some j)) + z none • w = 0 ∧
        w ⬝ᵥ (fun j => z (some j)) = 0 := by
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · funext i
      have h := congrFun hz (some i)
      simpa only [symmetricBorder_mulVec_some, Pi.zero_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm] using h
    · simpa only [symmetricBorder_mulVec_none, Pi.zero_apply] using congrFun hz none
  · rintro ⟨htop, hbottom⟩
    funext o
    cases o with
    | none => simpa only [symmetricBorder_mulVec_none, Pi.zero_apply] using hbottom
    | some i =>
      simpa only [symmetricBorder_mulVec_some, Pi.zero_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun htop i

/-- A symmetric matrix can be moved across the scalar pairing. -/
theorem dot_mulVec_symmetric {M : Matrix ι ι F} (hM : M.IsSymm) (u v : ι → F) :
    u ⬝ᵥ (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM]

variable [DecidableEq ι]

private theorem border_nonsingular_of_kernel_line {M : Matrix ι ι F} (hM : M.IsSymm)
    {κ w : ι → F} (hκ : M *ᵥ κ = 0)
    (hline : ∀ v, M *ᵥ v = 0 → ∃ a : F, v = a • κ) (hw : w ⬝ᵥ κ ≠ 0) :
    (symmetricBorder M w).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hzne, hz⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨htop, hbottom⟩ := (symmetricBorder_kernel_iff M w z).mp hz
  have hpair : κ ⬝ᵥ (M *ᵥ (fun j => z (some j))) = 0 := by
    rw [dot_mulVec_symmetric hM, hκ, zero_dotProduct]
  have ht := congrArg (fun v => κ ⬝ᵥ v) htop
  rw [dotProduct_add, dotProduct_smul, hpair, zero_add, dotProduct_zero,
    smul_eq_mul, dotProduct_comm κ w] at ht
  have ht0 : z none = 0 := (mul_eq_zero.mp ht).resolve_right hw
  have hv : M *ᵥ (fun j => z (some j)) = 0 := by simpa only [ht0, zero_smul, add_zero] using htop
  obtain ⟨a, ha⟩ := hline _ hv
  rw [ha, dotProduct_smul, smul_eq_mul] at hbottom
  have ha0 : a = 0 := (mul_eq_zero.mp hbottom).resolve_right hw
  have hv0 : (fun j => z (some j)) = 0 := by rw [ha, ha0, zero_smul]
  apply hzne
  funext o
  cases o with
  | none => exact ht0
  | some i => exact congrFun hv0 i

/-- Nonsingularity of one symmetric border is equivalent to a one-dimensional
kernel and a nonzero pairing with its generator. -/
theorem symmetricBorder_det_ne_zero_iff {M : Matrix ι ι F} (hM : M.IsSymm)
    {κ : ι → F} (hκne : κ ≠ 0) (hκ : M *ᵥ κ = 0) (w : ι → F) :
    (symmetricBorder M w).det ≠ 0 ↔
      (∀ v, M *ᵥ v = 0 → ∃ a : F, v = a • κ) ∧ w ⬝ᵥ κ ≠ 0 := by
  constructor
  · intro hdet
    have hker : ∀ z, symmetricBorder M w *ᵥ z = 0 → z = 0 := by
      intro z hz
      by_contra hzne
      exact hdet (exists_mulVec_eq_zero_iff.mp ⟨z, hzne, hz⟩)
    have horth : ∀ v, M *ᵥ v = 0 → w ⬝ᵥ v = 0 → v = 0 := by
      intro v hv hpair
      let z : Option ι → F := fun o => o.elim 0 v
      have hz : symmetricBorder M w *ᵥ z = 0 := by
        apply (symmetricBorder_kernel_iff M w z).mpr
        simpa only [z, Option.elim_none, Option.elim_some, zero_smul, add_zero] using
          And.intro hv hpair
      have hz0 := hker z hz
      funext i
      exact congrFun hz0 (some i)
    have hw : w ⬝ᵥ κ ≠ 0 := fun h => hκne (horth κ hκ h)
    refine ⟨?_, hw⟩
    intro v hv
    let a : F := (w ⬝ᵥ v) / (w ⬝ᵥ κ)
    have hu : M *ᵥ (v - a • κ) = 0 := by
      rw [mulVec_sub, mulVec_smul, hv, hκ, smul_zero, sub_zero]
    have hpair : w ⬝ᵥ (v - a • κ) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      dsimp only [a]
      rw [div_mul_cancel₀ _ hw, sub_self]
    exact ⟨a, sub_eq_zero.mp (horth _ hu hpair)⟩
  · rintro ⟨hline, hw⟩
    exact border_nonsingular_of_kernel_line hM hκ hline hw

/-- Every symmetric matrix with kernel a line admits a nonsingular
symmetric border. A coordinate detecting the kernel supplies it. -/
theorem exists_nonsingular_symmetricBorder {M : Matrix ι ι F} (hM : M.IsSymm)
    {κ : ι → F} (hκne : κ ≠ 0) (hκ : M *ᵥ κ = 0)
    (hline : ∀ v, M *ᵥ v = 0 → ∃ a : F, v = a • κ) :
    ∃ w : ι → F, (symmetricBorder M w).det ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, κ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hκne (funext h)
  refine ⟨Pi.single i 1, (symmetricBorder_det_ne_zero_iff hM hκne hκ _).mpr ⟨hline, ?_⟩⟩
  simpa [dotProduct, Pi.single_apply] using hi

/-- A surviving cofactor of a singular symmetric matrix supplies an
invertible symmetric extension by one row and one column. -/
theorem exists_nonsingular_symmetricBorder_of_cofactor {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) F) (hM : M.IsSymm)
    (hdet : M.det = 0) {r c : Fin N → Fin (N + 1)}
    (hcofactor : (M.submatrix r c).det ≠ 0) :
    ∃ w : Fin (N + 1) → F, (symmetricBorder M w).det ≠ 0 := by
  obtain ⟨κ, hκne, hκ⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  apply exists_nonsingular_symmetricBorder hM hκne hκ
  have hdim := finrank_ker_mulVecLin_eq_one_of_det_eq_zero M hdet hcofactor
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim
    (show κ ∈ LinearMap.ker M.mulVecLin from hκ) hκne
  intro v hv
  have hmem : v ∈ Submodule.span F {κ} := by
    rw [← hspan]
    exact hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨a, ha.symm⟩

#print axioms symmetricBorder_det_ne_zero_iff
#print axioms exists_nonsingular_symmetricBorder
#print axioms exists_nonsingular_symmetricBorder_of_cofactor

end GaloisForLFunctions.HTGeometry.LinearAlgebra
