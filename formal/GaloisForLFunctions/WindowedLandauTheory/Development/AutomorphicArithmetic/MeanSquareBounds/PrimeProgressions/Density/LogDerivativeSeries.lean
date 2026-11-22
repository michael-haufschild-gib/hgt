import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RepulsionPositivity

/-! The Euler series for normalized derivatives on the right of one. -/

open ArithmeticFunction Complex LSeries WindowedLandauTheory.ZeroFreeDirichlet
open scoped LSeries.notation

noncomputable section

namespace QH.PrimeProgressions

def derSeries (c : ℕ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (n : ℂ) ^ (-s)

theorem derSeries_eq_log_derivative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    derSeries (fun n => χ (n : ZMod q)) k s =
      (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ) s := by
  have h := (dhDom_hasSum χ k hs).mul_left ((k.factorial : ℂ)⁻¹)
  have he (n : ℕ) :
      (k.factorial : ℂ)⁻¹ * term (logMul^[k] (↗χ * ↗Λ)) s n =
        ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (n : ℂ) ^ (-s) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Complex.natCast_log]
    change (k.factorial : ℂ)⁻¹ *
        (Complex.log (n : ℂ) ^ k * (χ (n : ZMod q) * ((Λ n : ℝ) : ℂ)) / (n : ℂ) ^ s) = _
    rw [cpow_neg, div_eq_mul_inv, div_eq_mul_inv]
    ring
  unfold derSeries
  simp_rw [← he]
  rw [h.tsum_eq]
  ring

end QH.PrimeProgressions
