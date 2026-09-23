import GaloisForLFunctions.RHTower.Sieve.ConvolutionBlockTypeI
import GaloisForLFunctions.RHTower.Sieve.TypeILogWeight

/-!
# A `ζ`-convolution over a block is a type-I sum

`(ζ ∗ c)(n) = Σ_{d ∣ n} c(d)`, so summing it against `e(F(n))` over a block gives, for each `d`,
the near-diagonal sum at the scaled offset `r/d` over the fibre interval.  This is the first of the
three Vaughan pieces.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The near-diagonal phase evaluated at a natural number. -/
def ndPhaseExp (T r : ℝ) (n : ℕ) : ℂ := phaseExp (nearDiagonalPhase T r (n : ℝ))

theorem ndPhaseExp_mul (T r : ℝ) (a b : ℕ) :
    ndPhaseExp T r (a * b) = ndExp T r a b := by
  rw [ndPhaseExp, ndExp]
  congr 2
  push_cast
  ring

/-- The fibre block bound at the divisor `b`. -/
def fibreBound (T r : ℝ) (A B b : ℕ) : ℝ :=
  2500 * Real.sqrt (T * (r / b) / (36 * Real.pi * (((A - 1) / b + 1 : ℕ) : ℝ)))
    + 22 * Real.sqrt (36 * Real.pi / (T * (r / b)))
        * Real.sqrt (((((B - 1) / b + 1 : ℕ) : ℝ)) ^ (3 : ℕ))

/-- **The `ζ`-convolution type-I estimate.** -/
theorem norm_sum_zeta_conv_ndPhaseExp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {A B L : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L) (g : ℕ → ℂ)
    (hcond : ∀ b ∈ Finset.Icc 1 L,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B,
        (∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * g p.2) * ndPhaseExp T r n‖
      ≤ ∑ b ∈ Finset.Icc 1 L, ‖g b‖ * fibreBound T r A B b := by
  rw [sum_conv_mul_Ico_eq hA hB hBL (fun _ => (1 : ℂ)) g (ndPhaseExp T r)]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_Icc] at hb
  obtain ⟨hrA, hlam⟩ := hcond b (Finset.mem_Icc.2 hb)
  have hb1 : 1 ≤ b := hb.1
  have hinner : (∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1),
      (1 : ℂ) * ndPhaseExp T r (a * b))
      = ∑ a ∈ Finset.Ico ((A - 1) / b + 1) ((B - 1) / b + 1), ndExp T r a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [one_mul, ndPhaseExp_mul]
  rw [norm_mul, hinner]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact norm_sum_ndExp_le hT hr hb1 _ _ (Nat.le_add_left 1 _) hrA hlam

end

end RHTower.Sieve
