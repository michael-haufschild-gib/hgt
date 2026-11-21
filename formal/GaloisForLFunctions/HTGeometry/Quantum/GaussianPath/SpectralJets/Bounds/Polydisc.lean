import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BranchEvaluation
import GaloisForLFunctions.HTGeometry.CauchyFirstOrderStep

/-! # Cauchy estimates for polynomial partial derivatives on coupling boxes -/
open MvPolynomial Metric
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Uniform modulus bound on a closed coordinate polydisc. -/
def BoxBound (p : MvPolynomial ι ℂ) (R M : ℝ) : Prop :=
  ∀ x : ι → ℂ, (∀ i, ‖x i‖ ≤ R) → ‖eval x p‖ ≤ M

omit [Fintype ι] [DecidableEq ι] in
theorem BoxBound.shrink {p : MvPolynomial ι ℂ} {r R M : ℝ}
    (h : BoxBound p R M) (hr : r ≤ R) : BoxBound p r M :=
  fun x hx => h x (fun i => (hx i).trans hr)

/-- Taking one polynomial partial derivative costs one unit of polydisc radius. -/
theorem BoxBound.partial {p : MvPolynomial ι ℂ} {R M : ℝ} (h : BoxBound p (R+1) M) (i : ι) :
    BoxBound (pderiv i p) R M := by
  intro x hx
  let d (j : ι) : ℂ := if j = i then 1 else 0
  let f (t : ℂ) := eval (coordLine x i t) p
  have hline (t : ℂ) : HasDerivAt (coordLine x i) d t := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hj : j=i
    · simpa [coordLine,d,hj] using (hasDerivAt_id t).const_add (x i)
    · simpa [coordLine,d,hj] using hasDerivAt_const t (x j)
  have hf (t : ℂ) := hasDerivAt_mvPolynomial_eval_comp p (hline t)
  have hd : Differentiable ℂ f := fun t => (hf t).differentiableAt
  have h₀ : deriv f 0 = eval x (pderiv i p) := by
    simpa [f,coordLine_zero,d,mul_ite] using (hf 0).deriv
  rw [← h₀]
  apply (le_of_le_of_eq (_root_.HTGeometry.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := f) (R := 1) (M := M) zero_lt_one hd.diffContOnCl ?_) (div_one M))
  intro t ht
  have ht' : ‖t‖ = 1 := by simpa using ht
  apply h
  intro j
  by_cases hj : j=i
  · simpa [coordLine,hj] using (norm_add_le (x i) t).trans (add_le_add (hx i) ht'.le)
  · simpa [coordLine,hj] using (hx j).trans (le_add_of_nonneg_right zero_le_one)

end
end GaloisForLFunctions.HTGeometry.SpectralJets
