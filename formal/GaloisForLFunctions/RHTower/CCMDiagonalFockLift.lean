import GaloisForLFunctions.RHTower.CCMHalfUnitCauchySeam
import Mathlib.Analysis.Matrix.Order

/-!
# The half-unit covariance is a diagonal Fock lift

At any finite family of nodes beyond the half-unit seam the three kernels of the seam card become
three Gram matrices, and the card's equations `(3)`, `(4)`, `(10)`–`(12)` become exact matrix
identities:

```text
D = A ∘ C   (Schur product),        J_RH = A - D,
alpha* A alpha - alpha* D alpha = alpha* J_RH alpha .
```

The Cauchy factor `C (x, y) = 1/(x+y)` is proved positive semidefinite *by its Gram realization*
`1/(x+y) = int_0^infinity e^{-xt} e^{-yt} dt`, so the diagonal Fock feature `k_x -> k_x tensor c_x`
really is a feature map and not an abstract choice.  Consequently the defect form `I - T_0^* T_0` on
the kernel core is literally the `J_RH` form, so contractivity of the lift and positivity of the RH
kernel are the same statement, and their negative indices coincide.
-/

open Matrix MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The Cauchy kernel `(2)`. -/
def cauchyKernel (x y : ℝ) : ℝ := 1 / (x + y)

/-- The Gram matrix of a kernel at a finite family of nodes. -/
def kernelMatrix {n : ℕ} (K : ℝ → ℝ → ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => K (x i) (x j)

theorem kernelMatrix_apply {n : ℕ} (K : ℝ → ℝ → ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    kernelMatrix K x i j = K (x i) (x j) := rfl

/-! ## The Cauchy factor is a genuine Gram matrix -/

theorem integrableOn_expPair {a b : ℝ} (h : 0 < a + b) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a * t)) * Real.exp (-(b * t))) (Ioi (0 : ℝ)) volume := by
  have hcongr : ∀ t : ℝ, Real.exp (-(a * t)) * Real.exp (-(b * t)) = Real.exp (-(a + b) * t) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    ring
  refine MeasureTheory.IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi (0 : ℝ) h) ?_
    measurableSet_Ioi
  intro t _
  exact (hcongr t).symm

/-- **Equation (5), quadratic form.**  The Cauchy quadratic form is the `L²` energy of the
exponential feature. -/
theorem cauchy_quadratic_form {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (α : Fin n → ℝ) :
    ∑ i, ∑ j, α i * α j * cauchyKernel (x i) (x j)
      = ∫ t in Ioi (0 : ℝ), (∑ i, α i * Real.exp (-(x i * t))) ^ 2 := by
  have hexpand : ∀ t : ℝ, (∑ i, α i * Real.exp (-(x i * t))) ^ 2
      = ∑ i, ∑ j, α i * α j * (Real.exp (-(x i * t)) * Real.exp (-(x j * t))) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j : Fin n,
      IntegrableOn (fun t : ℝ => α i * α j * (Real.exp (-(x i * t)) * Real.exp (-(x j * t))))
        (Ioi (0 : ℝ)) volume :=
    fun i j => (integrableOn_expPair (by have := hx i; have := hx j; linarith)).const_mul _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => hexpand t]
  rw [MeasureTheory.integral_finsetSum _ fun i _ =>
    (MeasureTheory.integrable_finsetSum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul,
    integral_exp_ray (by have := hx i; have := hx j; linarith)]
  rfl

theorem isHermitian_kernelMatrix {n : ℕ} {K : ℝ → ℝ → ℝ} (hK : ∀ a b, K a b = K b a)
    (x : Fin n → ℝ) : (kernelMatrix K x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, kernelMatrix_apply, star_trivial]
  exact hK (x j) (x i)

/-- **The Cauchy kernel is positive semidefinite**, by its exponential Gram realization. -/
theorem posSemidef_cauchyMatrix {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (kernelMatrix cauchyKernel x).PosSemidef := by
  refine ⟨isHermitian_kernelMatrix (fun a b => by unfold cauchyKernel; rw [add_comm]) x,
    fun α => ?_⟩
  have hcoe : (α.sum fun i xi => α.sum fun j xj => star xi * kernelMatrix cauchyKernel x i j * xj)
      = ∑ i, ∑ j, α i * α j * cauchyKernel (x i) (x j) := by
    rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [kernelMatrix_apply, star_trivial]
    ring
  rw [hcoe, cauchy_quadratic_form hx (fun i => α i)]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun t _ => ?_
  positivity

/-! ## The three Gram matrices -/

/-- **Equation (3).**  The Fock covariance is the Schur product of the safe kernel and the Cauchy
kernel. -/
theorem fockMatrix_eq_hadamard {n : ℕ} (Q : ℝ → ℝ) (x : Fin n → ℝ) :
    kernelMatrix (fockKernel Q) x
      = (kernelMatrix (safeKernel Q) x) ⊙ (kernelMatrix cauchyKernel x) := by
  ext i j
  simp only [Matrix.hadamard_apply, kernelMatrix_apply, fockKernel, cauchyKernel]
  rw [div_eq_mul_inv, one_div]

/-- **Positivity of the Fock covariance.**  Schur product of two positive semidefinite kernels. -/
theorem posSemidef_fockMatrix {n : ℕ} {Q : ℝ → ℝ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i)
    (hA : (kernelMatrix (safeKernel Q) x).PosSemidef) :
    (kernelMatrix (fockKernel Q) x).PosSemidef := by
  rw [fockMatrix_eq_hadamard]
  exact hA.hadamard (posSemidef_cauchyMatrix hx)

/-- **Equation (4).**  The RH Gram matrix is the safe Gram matrix minus the Fock covariance. -/
theorem rhMatrix_eq_sub {n : ℕ} (Q : ℝ → ℝ) {x : Fin n → ℝ}
    (h1 : ∀ i j, x i + x j - 1 ≠ 0) (h2 : ∀ i j, x i + x j ≠ 0) :
    kernelMatrix (rhKernel Q) x
      = kernelMatrix (safeKernel Q) x - kernelMatrix (fockKernel Q) x := by
  ext i j
  simp only [Matrix.sub_apply, kernelMatrix_apply]
  exact rhKernel_eq_safe_sub_fock Q (h1 i j) (h2 i j)

/-! ## The defect form -/

/-- **Equations (10)–(12).**  The defect of the diagonal Fock lift on the kernel core is exactly
the RH quadratic form. -/
theorem defect_form_eq {n : ℕ} (Q : ℝ → ℝ) {x : Fin n → ℝ}
    (h1 : ∀ i j, x i + x j - 1 ≠ 0) (h2 : ∀ i j, x i + x j ≠ 0) (α : Fin n → ℝ) :
    (∑ i, ∑ j, α i * α j * safeKernel Q (x i) (x j))
        - ∑ i, ∑ j, α i * α j * fockKernel Q (x i) (x j)
      = ∑ i, ∑ j, α i * α j * rhKernel Q (x i) (x j) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rhKernel_eq_safe_sub_fock Q (h1 i j) (h2 i j)]
  ring

/-- **Equation (7), form level.**  The diagonal Fock lift is contractive on every finite kernel
core exactly when the RH quadratic form is nonnegative there. -/
theorem contractive_iff_rhForm_nonneg {n : ℕ} (Q : ℝ → ℝ) {x : Fin n → ℝ}
    (h1 : ∀ i j, x i + x j - 1 ≠ 0) (h2 : ∀ i j, x i + x j ≠ 0) :
    (∀ α : Fin n → ℝ, (∑ i, ∑ j, α i * α j * fockKernel Q (x i) (x j))
        ≤ ∑ i, ∑ j, α i * α j * safeKernel Q (x i) (x j))
      ↔ ∀ α : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, α i * α j * rhKernel Q (x i) (x j) := by
  constructor
  · intro h α
    have := h α
    rw [← defect_form_eq Q h1 h2 α]
    linarith
  · intro h α
    have hval := h α
    rw [← defect_form_eq Q h1 h2 α] at hval
    linarith

end GaloisForLFunctions.RHTower

end
