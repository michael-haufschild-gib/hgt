import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFiniteDetectorDirichlet
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTNegativeWindow
import GaloisForLFunctions.RHTower.EntireDirichletPolynomial
import GaloisForLFunctions.RHTower.HighBlockTruncatedAFE

/-!
# High-block law, brick B4: the direct×direct mean value for a general mollifier

`D_L(s)·Ψ(s)` with `D_L = Σ_{n<L} (n+1)^{−s} V((n+1)/x)` and `Ψ = Σ_{m ≤ N} b_m m^{−s}` on
`s = ½ − d + iτ` is one Dirichlet polynomial of length `LN` in the frequency `−τ`; its
coefficients are the Dirichlet convolution of the displaced direct coefficients with the displaced
mollifier coefficients. The corpus's mean-value theorem then gives

`|∫_{T₁}^{T₂} ‖D_LΨ‖² − (T₂−T₁)·E| ≤ 8 LN (1 + log LN) E`,  `E = Σ_r |c_r|²`,

which is `E·((T₂−T₁) + O(LN log LN))`: proportional to the coefficient energy, so the error is
`o(a)` on a block `[a, 2a]` as soon as `LN = o(a/log a)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Displaced mollifier coefficients in the `n+1` indexing: `b(m+1)·(m+1)^{−(½−d)}`. -/
def highBlockMollifierCoeffNat (d : ℝ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  b (m + 1) * (m + 1 : ℂ) ^ (-displacedLinePt d 0)

/-- The entire Dirichlet polynomial on the displaced line is a `dirPoly` at frequency `−τ`. -/
theorem edPoly_Icc_eq_dirPoly (d τ : ℝ) (b : ℕ → ℂ) (N : ℕ) :
    edPoly b (Finset.Icc 1 N) (displacedLinePt d τ) =
      Sieve.dirPoly N (fun m => highBlockMollifierCoeffNat d b m) (-τ) := by
  rw [sieveDirPoly_nat_eq_sum_range, edPoly, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rw [show N + 1 - 1 = N from Nat.add_sub_cancel N 1]
  apply Finset.sum_congr rfl
  intro k _
  rw [highBlockMollifierCoeffNat, add_comm 1 k]
  have hcast : (((k + 1 : ℕ) : ℝ) : ℂ) = (k + 1 : ℂ) := by push_cast; ring
  rw [hcast, natSucc_cpow_neg_displacedLinePt_eq_phase d τ k]
  ring

/-- The truncated direct head at `λ = 0` is a `dirPoly`. -/
theorem sum_smoothAFEZetaDisplacedDirectTerm_eq_dirPoly (d x τ : ℝ) (L : ℕ) :
    (∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) =
      Sieve.dirPoly L (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n) (-τ) := by
  have h := sum_smoothAFEZetaDisplacedDirect_detector_eq_dirPoly 0 d x τ L
  rw [show ((0 : ℝ) : ℂ) * (-I) *
      (∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n) = 0 by
        simp, add_zero] at h
  exact h

/-- The mollified direct head is one Dirichlet polynomial of length `L·N`. -/
theorem highBlockDirectHead_mul_edPoly_eq_dirPoly (d x τ : ℝ) (b : ℕ → ℂ) (L N : ℕ) :
    (∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) *
        edPoly b (Finset.Icc 1 N) (displacedLinePt d τ) =
      Sieve.dirPoly (L * N)
        (Sieve.dirConv L N (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n)
          (fun m => highBlockMollifierCoeffNat d b m)) (-τ) := by
  rw [edPoly_Icc_eq_dirPoly, sum_smoothAFEZetaDisplacedDirectTerm_eq_dirPoly,
    Sieve.dirPoly_mul_eq_dirPoly]

/-- The direct mollified coefficient energy `Σ_r |c_r|²`. -/
def highBlockDirectEnergy (d x : ℝ) (b : ℕ → ℂ) (L N : ℕ) : ℝ :=
  ∑ r : Fin (L * N),
    ‖Sieve.dirConv L N (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n)
      (fun m => highBlockMollifierCoeffNat d b m) r‖ ^ 2

/-- **B4.** Mean value of the mollified direct head on any window. -/
theorem abs_integral_normSq_highBlockDirect_sub_le (d x : ℝ) (b : ℕ → ℂ) (L N : ℕ)
    (T₁ T₂ : ℝ) :
    |(∫ τ in T₁..T₂, ‖(∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) *
          edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) -
        (T₂ - T₁) * highBlockDirectEnergy d x b L N| ≤
      8 * ((L * N : ℕ) : ℝ) * (1 + Real.log ((L * N : ℕ) : ℝ)) *
        highBlockDirectEnergy d x b L N := by
  have hpoint : ∀ τ : ℝ,
      ‖(∑ n ∈ Finset.range L, smoothAFEZetaDisplacedDirectTerm d x τ n) *
          edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2 =
        ‖Sieve.dirPoly (L * N)
          (Sieve.dirConv L N (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff 0 d x n)
            (fun m => highBlockMollifierCoeffNat d b m)) (-τ)‖ ^ 2 := by
    intro τ
    rw [highBlockDirectHead_mul_edPoly_eq_dirPoly]
  rw [intervalIntegral.integral_congr (fun τ _ => hpoint τ)]
  exact Sieve.dirichlet_meanValue_window_neg (L * N) _ T₁ T₂

end

end RHTower
