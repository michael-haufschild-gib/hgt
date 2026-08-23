import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIICoefficients
import GaloisForLFunctions.RHTower.Sieve.TypeIICorrelationRegimes

/-!
# The type-II piece of Vaughan's identity, in bilinear form

Rearranged, masked, and Cauchy--Schwarzed, the type-II piece becomes a coefficient energy times a
sum of correlations, each of which runs over an interval.  Nothing quantitative is used here: this
is the structural identity the optimisation consumes.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- The type-II short-side coefficients. -/
def typeIIShort (V : ℕ) : ArithmeticFunction ℝ :=
  (1 : ArithmeticFunction ℝ) - (zeta : ArithmeticFunction ℝ)
    * truncAF (moebius : ArithmeticFunction ℝ) V

/-- The type-II long-side coefficients. -/
def typeIILong (U : ℕ) : ArithmeticFunction ℝ := vonMangoldt - truncAF vonMangoldt U

/-- **The type-II piece as a masked bilinear form.** -/
theorem sum_typeII_piece_eq {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (T r : ℝ) (U V : ℕ) :
    (∑ n ∈ Finset.Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n)
      = ∑ d ∈ Finset.Icc 1 L, ((typeIILong U d : ℝ) : ℂ)
          * ∑ m ∈ Finset.Icc 1 L, ((typeIIShort V m : ℝ) : ℂ) * maskedNdExp T r A B d m := by
  have hI : ∀ n ∈ Finset.Ico A B, 1 ≤ n ∧ n ≤ L := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact ⟨by omega, by omega⟩
  have hterm : ∀ n ∈ Finset.Ico A B,
      (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n
        = (∑ p ∈ n.divisorsAntidiagonal,
            ((typeIILong U p.1 : ℝ) : ℂ) * ((typeIIShort V p.2 : ℝ) : ℂ)) * ndPhaseExp T r n :=
    fun n _ => by rw [coe_mul_apply]
  rw [Finset.sum_congr rfl hterm,
    sum_conv_mul_eq hI (fun d => ((typeIILong U d : ℝ) : ℂ))
      (fun m => ((typeIIShort V m : ℝ) : ℂ)) (ndPhaseExp T r),
    sum_typeII_masked_eq hA hB T r (fun d => ((typeIILong U d : ℝ) : ℂ))
      (fun m => ((typeIIShort V m : ℝ) : ℂ))]

/-- **The type-II energy bound for the Vaughan piece.** -/
theorem norm_typeII_piece_sq_le {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (T r : ℝ) (U V : ℕ) :
    ‖∑ n ∈ Finset.Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖ ^ 2
      ≤ (∑ d ∈ Finset.Ico 1 (L + 1), ‖((typeIILong U d : ℝ) : ℂ)‖ ^ 2)
        * ∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
            ‖((typeIIShort V m₁ : ℝ) : ℂ)‖ * ‖((typeIIShort V m₂ : ℝ) : ℂ)‖
              * ‖∑ d ∈ Finset.Ico 1 (L + 1),
                  maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ := by
  rw [sum_typeII_piece_eq hA hB hBL T r U V, ← Finset.Ico_add_one_right_eq_Icc 1 L]
  exact norm_typeII_masked_sq_le T r A B 1 (L + 1) (Finset.Icc 1 L)
    (fun d => ((typeIILong U d : ℝ) : ℂ)) (fun m => ((typeIIShort V m : ℝ) : ℂ))

end

end RHTower.Sieve
