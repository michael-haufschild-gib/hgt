import GaloisForLFunctions.RHTower.ZetaWeightedSeam
import Zeta23.PrimeSideA.EndsCore
import Zeta23.PrimeSideB.Concrete

/-!
# The weighted prime-side Gram matrix as an integral

For grid weights `W_k` put `K_W(τ,τ') = Σ_{k<d} W_k φ̂(τ − τ_k) φ̂(τ' − τ_k)` (`KfunW`).  The prime-side Gram entries
`G_kl = ∫ φ̂(τ − τ_k) φ̂(τ − τ_l) ν(τ) dτ` then satisfy (absolute convergence as in Zeta23's [eq:trG2int])

* `Σ_k W_k G_kk = ∫ K_W(τ,τ) ν(τ) dτ` (`eq_trG1intW`),
* `Σ_{k,l} W_k W_l G_kl² = ∬ K_W(τ,τ')² ν(τ) ν(τ') dτ dτ'` (`eq_trG2intW`).

For the bandwidth-`λ` Gram matrix of `ζ` and real weights `w_k`, the weighted matrix `Ĝ_w = (w_k w_l Ĝ_kl)` of the
weighted seam has `tr Ĝ_w = (aL²)⁻¹ Σ_k w_k² G_kk` and `‖Ĝ_w‖² = (aL²)⁻² Σ_{k,l} w_k² w_l² G_kl²`
(`rtrace_hat_wmat_Gp`, `frobSq_hat_wmat_Gp`), i.e. the two integrals above with `W_k = w_k²`.
-/

open Matrix Finset MeasureTheory Real Zeta23 Zeta23.PrimeSide RHLinalg

noncomputable section

namespace RHTower

section Abstract

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- The weighted kernel `K_W(τ,τ') = Σ_{k<d} W_k φ̂(τ − τ_k) φ̂(τ' − τ_k)`. -/
def KfunW (p : Setting) (F : LocalFun) (W : Fin p.d → ℝ) (τ τ' : ℝ) : ℝ :=
  ∑ k : Fin p.d, W k * (F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))

/-- The integrand `K_W(τ,τ')² ν(τ) ν(τ')`. -/
def trG2integrandW (p : Setting) (F : LocalFun) (ν : ℝ → ℝ) (W : Fin p.d → ℝ) (q : ℝ × ℝ) : ℝ :=
  KfunW p F W q.1 q.2 ^ 2 * ν q.1 * ν q.2

theorem sum_W_gkl_mul_gkl (W : Fin p.d → ℝ) (q : ℝ × ℝ) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, W k * W l * (gkl p F ν k l q.1 * gkl p F ν k l q.2)
      = trG2integrandW p F ν W q := by
  unfold trG2integrandW KfunW gkl
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The weighted Frobenius sum as a double integral.** -/
theorem eq_trG2intW (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) (W : Fin p.d → ℝ) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, W k * W l * GentryNu ν p F k l ^ 2
      = ∫ q, trG2integrandW p F ν W q := by
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hI : ∀ k l : Fin p.d, Integrable (fun q : ℝ × ℝ => gkl p F ν k l q.1 * gkl p F ν k l q.2) :=
    fun k l => (gkl_integrable hνc hF hν hT1 hB k l).mul_prod (gkl_integrable hνc hF hν hT1 hB k l)
  have hsq : ∀ k l : Fin p.d, W k * W l * GentryNu ν p F k l ^ 2
      = ∫ q : ℝ × ℝ, W k * W l * (gkl p F ν k l q.1 * gkl p F ν k l q.2) := by
    intro k l
    rw [integral_const_mul, sq, GentryNu_eq, ← integral_prod_mul]
    rfl
  have hinner : ∀ k : Fin p.d, ∑ l : Fin p.d, W k * W l * GentryNu ν p F k l ^ 2
      = ∫ q : ℝ × ℝ, ∑ l : Fin p.d, W k * W l * (gkl p F ν k l q.1 * gkl p F ν k l q.2) := by
    intro k
    rw [integral_finsetSum _ (fun l _ => (hI k l).const_mul _)]
    exact Finset.sum_congr rfl fun l _ => hsq k l
  rw [Finset.sum_congr rfl fun k _ => hinner k,
    ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => (hI k l).const_mul _)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q => sum_W_gkl_mul_gkl W q)

/-- **The weighted trace as an integral.** -/
theorem eq_trG1intW (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) (W : Fin p.d → ℝ) :
    ∑ k : Fin p.d, W k * GentryNu ν p F k k = ∫ τ, KfunW p F W τ τ * ν τ := by
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hI : ∀ k : Fin p.d, Integrable (gkl p F ν k k) :=
    fun k => gkl_integrable hνc hF hν hT1 hB k k
  have h1 : ∀ k : Fin p.d, W k * GentryNu ν p F k k = ∫ τ, W k * gkl p F ν k k τ := by
    intro k
    rw [integral_const_mul, GentryNu_eq]
  rw [Finset.sum_congr rfl fun k _ => h1 k,
    ← integral_finsetSum _ (fun k _ => (hI k).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [KfunW, gkl, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Abstract

section Concrete

variable {P : Params} {T : ℝ}

/-- `tr Ĝ_w = (aL²)⁻¹ Σ_k w_k² G_kk`. -/
theorem rtrace_hat_wmat_Gp (w : Fin (P.d T) → ℝ) :
    rtrace (P.hat T (wmat w (P.Gp T)))
      = (P.a T * P.L T ^ 2)⁻¹ * ∑ k : Fin (P.d T), w k ^ 2 * P.Gentry T k k := by
  rw [ZeroSide.hat_eq, Assembly.rtrace_smul_ofReal]
  congr 1
  simp only [rtrace, Matrix.trace, Matrix.diag, wmat, Params.Gp, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  ring

/-- `‖Ĝ_w‖² = (aL²)⁻² Σ_{k,l} w_k² w_l² G_kl²`. -/
theorem frobSq_hat_wmat_Gp (w : Fin (P.d T) → ℝ) :
    frobSq (P.hat T (wmat w (P.Gp T)))
      = ((P.a T * P.L T ^ 2)⁻¹) ^ 2
        * ∑ k : Fin (P.d T), ∑ l : Fin (P.d T), w k ^ 2 * w l ^ 2 * P.Gentry T k l ^ 2 := by
  rw [ZeroSide.hat_eq, Assembly.frobSq_smul_ofReal, Assembly.frobSq_eq_sum_norm_sq]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [wmat, Params.Gp]
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end Concrete

end RHTower
