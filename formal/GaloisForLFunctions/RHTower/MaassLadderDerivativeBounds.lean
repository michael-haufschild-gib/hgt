import GaloisForLFunctions.RHTower.MaassCircleDerivativeBounds
import GaloisForLFunctions.RHTower.MaassDifferentialLadder

/-!
# Global derivative bounds for both Maass ladders

The space of smooth functions with all Euler words bounded is stable under
raising and lowering at every weight. Compact circle kernels put the original
positive-eigenvalue congruence Maass form in this space.
-/

open UpperHalfPlane
namespace GaloisForLFunctions.RHTower.MaassCircle
open MaassSmooth
noncomputable section

theorem eulerWord_append (v w : List Bool) : eulerWord (v ++ w) = eulerWord v * eulerWord w := by
  induction v with
  | nil => simp only [List.nil_append, eulerWord, one_mul]
  | cons d v ih => simp only [List.cons_append, eulerWord, ih, mul_assoc]

/-- Smooth functions whose every finite Euler word is bounded. -/
def boundedEulerSpace : Submodule ℂ FunctionSpace where
  carrier := {f | ∀ w : List Bool, ∃ C : ℝ, ∀ z : ℍ, ‖eulerWord w f z‖ ≤ C}
  zero_mem' := by
    intro w
    refine ⟨0, fun z => ?_⟩
    simp only [map_zero]
    change ‖(0 : ℂ)‖ ≤ 0
    exact norm_zero.le
  add_mem' := by
    intro f g hf hg w
    obtain ⟨C,hC⟩ := hf w
    obtain ⟨D,hD⟩ := hg w
    refine ⟨C+D, fun z => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hC z) (hD z))
  smul_mem' := by
    intro c f hf w
    obtain ⟨C,hC⟩ := hf w
    refine ⟨‖c‖*C, fun z => ?_⟩
    rw [map_smul]
    change ‖c * eulerWord w f z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC z) (norm_nonneg c)

theorem boundedEulerSpace_euler (d : Bool) {f : FunctionSpace} (hf : f ∈ boundedEulerSpace) :
    euler d f ∈ boundedEulerSpace := by
  intro w
  obtain ⟨C,hC⟩ := hf (w ++ [d])
  refine ⟨C, fun z => ?_⟩
  simpa only [eulerWord_append, eulerWord, mul_one, Module.End.mul_apply] using hC z

theorem boundedEulerSpace_raise (m : ℤ) {f : FunctionSpace} (hf : f ∈ boundedEulerSpace) :
    raise m f ∈ boundedEulerSpace := by
  have hx : X f ∈ boundedEulerSpace :=
    boundedEulerSpace.smul_mem Complex.I (boundedEulerSpace_euler false hf)
  have hy : Y f ∈ boundedEulerSpace := boundedEulerSpace_euler true hf
  rw [raise_apply]
  exact boundedEulerSpace.sub_mem (boundedEulerSpace.sub_mem hx hy)
    (boundedEulerSpace.smul_mem (m : ℂ) hf)

theorem boundedEulerSpace_lower (m : ℤ) {f : FunctionSpace} (hf : f ∈ boundedEulerSpace) :
    lower m f ∈ boundedEulerSpace := by
  have hx : X f ∈ boundedEulerSpace :=
    boundedEulerSpace.smul_mem Complex.I (boundedEulerSpace_euler false hf)
  have hy : Y f ∈ boundedEulerSpace := boundedEulerSpace_euler true hf
  rw [lower_apply]
  exact boundedEulerSpace.add_mem (boundedEulerSpace.sub_mem (boundedEulerSpace.neg_mem hx) hy)
    (boundedEulerSpace.smul_mem (m : ℂ) hf)

/-- All Euler derivatives of every actual changing-weight raised or lowered source are bounded. -/
theorem ladders_all_euler_words_bounded (N : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam) (n : ℕ) :
    raised (ofMaass f) n ∈ boundedEulerSpace ∧ lowered (ofMaass f) n ∈ boundedEulerSpace := by
  induction n with
  | zero => exact ⟨all_euler_words_bounded N hlam f, all_euler_words_bounded N hlam f⟩
  | succ n ih => exact ⟨boundedEulerSpace_raise (n : ℤ) ih.1,
      boundedEulerSpace_lower (-(n : ℤ)) ih.2⟩

end
end GaloisForLFunctions.RHTower.MaassCircle
