import GaloisForLFunctions.HTGeometry.EulerQGammaLanding
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthDilation

/-!
# The divisor of the dilation organ

The depth-`j` factor of the grand response is `ζ(j(σ+u)+v)`, an affine pullback of `ζ` in the
dilation variable `u` with slope `j`.  Its order at `u` is therefore the order of `ζ` at the pulled
back point, and the order of any depth-truncated product is the finite sum of those orders: this is
(GAS.9).  The same affine identity says that the depth-`j` factor is singular exactly on the line
`j·u + v = w − j·σ`, which is (GAS.10) with depth as slope.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The depth-`j` factor of the grand response, in the dilation variable. -/
def depthFactor (σ : ℝ) (v : ℂ) (j : ℕ) (u : ℂ) : ℂ :=
  riemannZeta ((j : ℂ) * ((σ : ℝ) + u) + v)

/-- **(GAS.10).**  The depth-`j` factor meets a prescribed zeta argument `w` exactly on an affine
line of slope `j`. -/
theorem depthFactor_arg_eq_iff (σ : ℝ) (j : ℕ) (u v w : ℂ) :
    (j : ℂ) * ((σ : ℝ) + u) + v = w ↔ (j : ℂ) * u + v = w - (j : ℂ) * (σ : ℝ) := by
  constructor <;> intro h <;> linear_combination h

theorem depthFactor_eq_affine (σ : ℝ) (v : ℂ) (j : ℕ) :
    depthFactor σ v j = fun u : ℂ => riemannZeta ((j : ℂ) * u + ((j : ℂ) * (σ : ℝ) + v)) := by
  funext u
  rw [depthFactor]
  congr 1
  ring

theorem meromorphicAt_depthFactor (σ : ℝ) (v : ℂ) {j : ℕ} (hj : 1 ≤ j) (u : ℂ) :
    MeromorphicAt (depthFactor σ v j) u := by
  have hj0 : ((j : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [depthFactor_eq_affine]
  exact meromorphicAt_comp_affine hj0 (meromorphicAt_riemannZeta _)

/-- **(GAS.9), one depth.**  The order of the depth-`j` factor is the order of `ζ` at the pulled
back point. -/
theorem meromorphicOrderAt_depthFactor (σ : ℝ) (v : ℂ) {j : ℕ} (hj : 1 ≤ j) (u : ℂ) :
    meromorphicOrderAt (depthFactor σ v j) u
      = meromorphicOrderAt riemannZeta ((j : ℂ) * ((σ : ℝ) + u) + v) := by
  have hj0 : ((j : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [depthFactor_eq_affine]
  rw [meromorphicOrderAt_comp_affine hj0 u (meromorphicAt_riemannZeta _)]
  congr 1
  ring

/-- The depth-truncated grand response in the dilation variable. -/
def depthProduct (σ : ℝ) (v : ℂ) (J : ℕ) (u : ℂ) : ℂ :=
  ∏ j ∈ Finset.range J, depthFactor σ v (j + 1) u

/-- **(GAS.9).**  The order of the depth-truncated grand response is the finite sum of the pulled
back zeta orders. -/
theorem meromorphicOrderAt_depthProduct (σ : ℝ) (v : ℂ) (J : ℕ) (u : ℂ) :
    meromorphicOrderAt (depthProduct σ v J) u
      = ∑ j ∈ Finset.range J,
        meromorphicOrderAt riemannZeta (((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + u) + v) := by
  induction J with
  | zero =>
      have hone : depthProduct σ v 0 = fun _ : ℂ => (1 : ℂ) := by
        funext w
        show (∏ j ∈ Finset.range 0, depthFactor σ v (j + 1) w) = 1
        rw [Finset.range_zero, Finset.prod_empty]
      rw [hone, Finset.range_zero, Finset.sum_empty]
      exact meromorphicOrderAt_eq_zero_of_analytic analyticAt_const one_ne_zero
  | succ J ih =>
      have hfun : depthProduct σ v (J + 1)
          = depthProduct σ v J * depthFactor σ v (J + 1) := by
        funext w
        show (∏ j ∈ Finset.range (J + 1), depthFactor σ v (j + 1) w)
            = (∏ j ∈ Finset.range J, depthFactor σ v (j + 1) w) * depthFactor σ v (J + 1) w
        rw [Finset.prod_range_succ]
      have hmerA : MeromorphicAt (depthProduct σ v J) u := by
        show MeromorphicAt (fun w : ℂ => ∏ j ∈ Finset.range J, depthFactor σ v (j + 1) w) u
        exact MeromorphicAt.fun_prod fun j _ =>
          meromorphicAt_depthFactor σ v (Nat.succ_le_succ (Nat.zero_le j)) u
      have hmerB : MeromorphicAt (depthFactor σ v (J + 1)) u :=
        meromorphicAt_depthFactor σ v (Nat.succ_le_succ (Nat.zero_le J)) u
      rw [hfun, meromorphicOrderAt_mul hmerA hmerB, ih,
        meromorphicOrderAt_depthFactor σ v (Nat.succ_le_succ (Nat.zero_le J)) u,
        Finset.sum_range_succ]

end

end GaloisForLFunctions.HTGeometry
