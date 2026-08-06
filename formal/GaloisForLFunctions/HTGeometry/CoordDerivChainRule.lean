import GaloisForLFunctions.HTGeometry.TorusDerivationLeibniz

/-!
# The coordinate chain rule and the gradient of a phase observable

The coordinate derivatives obey the same chain rule as the torus derivation: a
polynomial expression in holomorphic functions is differentiated through the
partial derivatives of the polynomial.

Assembling the coordinate derivatives into a gradient vector turns a polynomial
relation among holomorphic functions into a linear relation among their
gradients, with the partial derivatives of the relation as coefficients.  This
is the linear-algebraic form of a differential relation.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The coordinate chain rule -/

/-- **The chain rule for a coordinate derivative.** -/
theorem coordDeriv_eval_mvPolynomial {σ : Type} [Fintype σ] [DecidableEq σ]
    {U : Set (d → ℂ)} {g : σ → (d → ℂ) → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) (Q : MvPolynomial σ ℂ) (j : d)
    {z : d → ℂ} (hz : z ∈ U) :
    coordDeriv (fun w => MvPolynomial.eval (fun i => g i w) Q) j z
      = ∑ i : σ, MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i Q)
          * coordDeriv (g i) j z := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun w : d → ℂ =>
          MvPolynomial.eval (fun i => g i w) (MvPolynomial.C a)) = fun _ => a := by
        funext w
        rw [MvPolynomial.eval_C]
      rw [hfun, coordDeriv_const]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [MvPolynomial.pderiv_C, map_zero, zero_mul]
  | add p q hp hq =>
      have hfun : (fun w : d → ℂ =>
            MvPolynomial.eval (fun i => g i w) (p + q)) =
          fun w => MvPolynomial.eval (fun i => g i w) p +
            MvPolynomial.eval (fun i => g i w) q := by
        funext w
        rw [map_add]
      rw [hfun, coordDeriv_add (analyticOnNhd_mvPolynomialEval hg p)
        (analyticOnNhd_mvPolynomialEval hg q) j hz, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, map_add]
      ring
  | mul_X p k hp =>
      have hfun : (fun w : d → ℂ =>
            MvPolynomial.eval (fun i => g i w) (p * MvPolynomial.X k)) =
          fun w => MvPolynomial.eval (fun i => g i w) p * g k w := by
        funext w
        rw [map_mul, MvPolynomial.eval_X]
      have hpd : ∀ i : σ,
          MvPolynomial.eval (fun i => g i z)
              (MvPolynomial.pderiv i (p * MvPolynomial.X k))
            = MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i p) * g k z
              + MvPolynomial.eval (fun i => g i z) p * (if k = i then 1 else 0) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul,
          map_mul, MvPolynomial.pderiv_X, MvPolynomial.eval_X, Pi.single_apply]
        by_cases hik : k = i
        · simp only [if_pos hik, map_one]
          ring
        · simp only [if_neg hik, map_zero]
          ring
      have hterm : ∀ i : σ, MvPolynomial.eval (fun i => g i z)
            (MvPolynomial.pderiv i (p * MvPolynomial.X k)) * coordDeriv (g i) j z
          = g k z * (MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i p)
              * coordDeriv (g i) j z)
            + (if k = i then MvPolynomial.eval (fun i => g i z) p
                * coordDeriv (g i) j z else 0) := by
        intro i
        rw [hpd i]
        by_cases hik : k = i
        · rw [if_pos hik, if_pos hik]
          ring
        · rw [if_neg hik, if_neg hik]
          ring
      rw [hfun, coordDeriv_mul (analyticOnNhd_mvPolynomialEval hg p) (hg k) j hz, hp]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        ← Finset.mul_sum,
        Finset.sum_ite_eq Finset.univ k (fun i => MvPolynomial.eval (fun i => g i z) p
          * coordDeriv (g i) j z), if_pos (Finset.mem_univ k)]
      ring

/-! ### Gradients -/

/-- The gradient vector of a holomorphic function. -/
def gradientVec (F : (d → ℂ) → ℂ) (z : d → ℂ) : d → ℂ :=
  fun j => coordDeriv F j z

omit [Fintype d] in
@[simp] theorem gradientVec_apply (F : (d → ℂ) → ℂ) (z : d → ℂ) (j : d) :
    gradientVec F z j = coordDeriv F j z := rfl

/-- **A polynomial relation differentiates to a linear relation among the
gradients.** -/
theorem gradientVec_eval_mvPolynomial {σ : Type} [Fintype σ] [DecidableEq σ]
    {U : Set (d → ℂ)} {g : σ → (d → ℂ) → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) (Q : MvPolynomial σ ℂ)
    {z : d → ℂ} (hz : z ∈ U) :
    gradientVec (fun w => MvPolynomial.eval (fun i => g i w) Q) z
      = ∑ i : σ, MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i Q)
          • gradientVec (g i) z := by
  funext j
  rw [gradientVec, coordDeriv_eval_mvPolynomial hg Q j hz]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, gradientVec]

/-- **A vanishing polynomial relation gives a vanishing linear combination of
the gradients.** -/
theorem sum_smul_gradientVec_eq_zero {σ : Type} [Fintype σ] [DecidableEq σ]
    {U : Set (d → ℂ)} (hU : IsOpen U) {g : σ → (d → ℂ) → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) (Q : MvPolynomial σ ℂ)
    (hQ : ∀ w ∈ U, MvPolynomial.eval (fun i => g i w) Q = 0)
    {z : d → ℂ} (hz : z ∈ U) :
    ∑ i : σ, MvPolynomial.eval (fun i => g i z) (MvPolynomial.pderiv i Q)
        • gradientVec (g i) z = 0 := by
  rw [← gradientVec_eval_mvPolynomial hg Q hz]
  funext j
  rw [gradientVec, coordDeriv]
  have hev : (fun w => MvPolynomial.eval (fun i => g i w) Q) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hQ w hw
  rw [hev.fderiv_eq]
  simp

end

end GaloisForLFunctions.HTGeometry
