import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorArithmeticBridge
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionLinear
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue

/-!
# Critical detector mollified cutoff error

The Gaussian cutoff error in the direct critical detector head remains an exact Dirichlet
convolution after multiplication by the linear Levinson mollifier.  Its `ell^(1 : ℕ)` norm is controlled
by the one-head cutoff error and the explicit `2 * sqrt M` mollifier mass.
-/

noncomputable section

namespace RHTower

open Complex

/-- Finite unsmoothed critical detector convolved with the literal linear mollifier. -/
def levinsonCriticalDetectorMollifiedFinCoeff
    (lam : ℝ) (L M : ℕ) : Fin (L * M) → ℂ :=
  Sieve.dirConv L M
    (fun n : Fin L =>
      Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1))
    (levinsonLinearMollifierFinCoeff M)

/-- Coefficient error caused by the Gaussian cutoff in the direct mollified head. -/
def smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff
    (lam x : ℝ) (L M : ℕ) (r : Fin (L * M)) : ℂ :=
  smoothAFEZetaDisplacedDirectMollifiedCoeff lam 0 x L M r -
    levinsonCriticalDetectorMollifiedFinCoeff lam L M r

/-- The mollified cutoff error is exactly the convolution of the one-head cutoff error
with the literal linear mollifier. -/
theorem smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff_eq_dirConv
    (lam x : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff lam x L M r =
      Sieve.dirConv L M
        ((fun n : Fin L => smoothAFEZetaDisplacedDirectDetectorCoeff lam 0 x n) -
          (fun n : Fin L =>
            Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)))
        (levinsonLinearMollifierFinCoeff M) r := by
  rw [smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff,
    smoothAFEZetaDisplacedDirectMollifiedCoeff,
    levinsonCriticalDetectorMollifiedFinCoeff]
  exact (Sieve.dirConv_sub_left L M _ _ _ r).symm

/-- The zero-based finite mollifier has the same `ell^(1 : ℕ)` mass as its positive-natural form. -/
theorem sum_norm_levinsonLinearMollifierFinCoeff_le
    {M : ℕ} (hM : 1 < M) :
    ∑ m : Fin M, ‖levinsonLinearMollifierFinCoeff M m‖ ≤
      2 * Real.sqrt M := by
  change (∑ m : Fin M,
      ‖Sieve.levinsonLinearMollifierCoeff M ((m : ℕ) + 1)‖) ≤ _
  calc
    _ = ∑ k ∈ Finset.Icc 1 M,
        ‖Sieve.levinsonLinearMollifierCoeff M k‖ :=
      Sieve.sum_fin_eq_sum_Icc M
        (fun k => ‖Sieve.levinsonLinearMollifierCoeff M k‖)
    _ ≤ _ := Sieve.sum_norm_levinsonLinearMollifierCoeff_le hM

/-- Multiplication by the linear mollifier amplifies the direct-head cutoff error by at most
its explicit `ell^(1 : ℕ)` mass. -/
theorem sum_norm_smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff_le
    (lam x : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) :
    ∑ r : Fin (L * M),
        ‖smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff lam x L M r‖ ≤
      (∑ n : Fin L,
          ‖smoothAFEZetaDisplacedDirectDetectorCoeff lam 0 x n -
            Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)‖) *
        (2 * Real.sqrt M) := by
  rw [show (∑ r : Fin (L * M),
        ‖smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff lam x L M r‖) =
      ∑ r : Fin (L * M),
        ‖Sieve.dirConv L M
          ((fun n : Fin L => smoothAFEZetaDisplacedDirectDetectorCoeff lam 0 x n) -
            (fun n : Fin L =>
              Sieve.levinsonCriticalDetectorHeadCoeff lam ((n : ℕ) + 1)))
          (levinsonLinearMollifierFinCoeff M) r‖ by
      apply Finset.sum_congr rfl
      intro r hr
      rw [smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff_eq_dirConv]]
  refine (Sieve.sum_norm_dirConv_le L M _ _).trans ?_
  exact mul_le_mul_of_nonneg_left
    (sum_norm_levinsonLinearMollifierFinCoeff_le hM)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Uniform power-rate removal of the Gaussian cutoff after multiplication by the linear
Levinson mollifier. -/
theorem exists_sum_norm_smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam x : ℝ) (L : ℕ) {M : ℕ},
      0 < x → 1 < M →
      ∑ r : Fin (L * M),
          ‖smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff lam x L M r‖ ≤
        (∑ n : Fin L,
            K * ((((n : ℕ) + 1 : ℕ) : ℝ) / x) ^ delta *
              (((1 : ℝ) / Real.sqrt ((((n : ℕ) + 1 : ℕ) : ℝ))) *
                |1 - lam * Real.log ((((n : ℕ) + 1 : ℕ) : ℝ))|)) *
          (2 * Real.sqrt M) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_smoothAFEZetaDirectDetectorPositiveCoeff_zero_sub_le hdelta
  refine ⟨K, hK, ?_⟩
  intro lam x L M hx hM
  refine (sum_norm_smoothAFEZetaCriticalDirectMollifiedCutoffErrorCoeff_le
    lam x L hM).trans ?_
  refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun n _ => ?_) (by positivity)
  simpa only [smoothAFEZetaDisplacedDirectDetectorPositiveCoeff_succ] using
    hbound lam x hx (by omega : 0 < (n : ℕ) + 1)

end RHTower
