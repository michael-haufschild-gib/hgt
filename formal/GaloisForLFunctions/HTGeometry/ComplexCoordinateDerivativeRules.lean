import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
noncomputable section
variable {d : ℕ}

/-- Coordinate differentiation of a sum of complex fields on real coordinates. -/
theorem coordDeriv_add {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    coordDeriv k (fun y => f y + g y) x = coordDeriv k f x + coordDeriv k g x := by
  simp only [coordDeriv, fderiv_fun_add hf hg, add_apply]

/-- Coordinate differentiation of a difference of complex fields. -/
theorem coordDeriv_sub {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    coordDeriv k (fun y => f y - g y) x = coordDeriv k f x - coordDeriv k g x := by
  simp only [coordDeriv, fderiv_fun_sub hf hg, sub_apply]

/-- Full coordinate product rule, retaining both differentiated factors. -/
theorem coordDeriv_mul {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    coordDeriv k (fun y => f y * g y) x = coordDeriv k f x * g x + f x * coordDeriv k g x := by
  simp only [coordDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Coordinate differentiation commutes with a finite sum of differentiable entries. -/
theorem coordDeriv_sum {ι : Type*} {s : Finset ι} {F : ι → (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) x) (k : Fin d) :
    coordDeriv k (fun y => ∑ a ∈ s, F a y) x = ∑ a ∈ s, coordDeriv k (F a) x := by
  simp [coordDeriv, fderiv_fun_sum hF]

/-- A coordinate derivative retains every available lower smoothness order. -/
theorem coordDeriv_contDiffAt {m n : ℕ∞ω} {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ n f x) (hm : m + 1 ≤ n) (j : Fin d) :
    ContDiffAt ℝ m (coordDeriv j f) x :=
  (hf.fderiv_right hm).clm_apply contDiffAt_const

/-- Actual derivative of a coordinate derivative is a slot of the second Frechet derivative. -/
theorem coordDeriv_hasFDerivAt {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j : Fin d) :
    HasFDerivAt (coordDeriv j f) ((fderiv ℝ (fderiv ℝ f) x).flip (Pi.single j 1)) x := by
  have h := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  simpa [coordDeriv] using h.clm_apply (hasFDerivAt_const (Pi.single j 1) x)

/-- C2 complex fields have commuting ordered real coordinate derivatives. -/
theorem coordDeriv_comm {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (i j : Fin d) :
    coordDeriv i (coordDeriv j f) x = coordDeriv j (coordDeriv i f) x := by
  change fderiv ℝ (coordDeriv j f) x (Pi.single i 1) =
    fderiv ℝ (coordDeriv i f) x (Pi.single j 1)
  rw [(coordDeriv_hasFDerivAt hf j).fderiv, (coordDeriv_hasFDerivAt hf i).fderiv]
  exact (hf.isSymmSndFDerivAt (by norm_num)) (Pi.single i 1) (Pi.single j 1)

end
end GaloisForLFunctions.HTGeometry.ScalarTwoJet
