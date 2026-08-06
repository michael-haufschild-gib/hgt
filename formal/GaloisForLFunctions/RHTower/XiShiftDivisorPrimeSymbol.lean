import GaloisForLFunctions.HTGeometry.ShiftDivisorLSeries
import GaloisForLFunctions.RHTower.XiShiftDivisorValueReflection

/-!
# The prime symbol of a completed-Xi shift divisor

On the half-plane of absolute convergence the completed logarithmic derivative with its archimedean
part removed is exactly minus the von Mangoldt Dirichlet series.  Applying a finite shift divisor
therefore turns the corrected completed-Xi value into a single L-series: the von Mangoldt stream
twisted by the divisor's Dirichlet symbol `n ↦ ∑ a w a * n ^ (-a)`.

This identifies the arithmetic content of an arbitrary weighted family of completed-Xi translates
with one Dirichlet symbol, and the divisor reflection about `(1 - σ) / 2` with the symbol inversion
`n ^ (-a) ↦ n ^ a` twisted by `n ^ (σ - 1)`.  The single-shift prime exposure is the two-point
divisor `δ_a - δ_0`, whose symbol is `n ^ (-a) - 1`.
-/

namespace RHTower

open Complex

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Completed prime source.** Removing the archimedean logarithmic derivative from the completed
one leaves exactly minus the von Mangoldt Dirichlet series on the Euler half-plane. -/
theorem logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s - logDeriv archFactor s =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have h := seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs
  rw [seamFluxCochain, infinitePrimeFlux_eq_vonMangoldtLSeries hs] at h
  linear_combination -h

/-- **Divisor prime-symbol law.** For a shift divisor with nonnegative real shifts, the corrected
completed-Xi value on the Euler half-plane is minus the von Mangoldt L-series twisted by the
divisor's Dirichlet symbol. -/
theorem xiShiftDivisorPrimeValue_eq_lSeries (w : ℂ →₀ ℂ)
    (hw : ∀ a ∈ w.support, 0 ≤ a.re) {s : ℂ} (hs : 1 < s.re) :
    xiShiftDivisorPrimeValue w s =
      -LSeries (shiftDivisorStream w fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hre : ∀ a ∈ w.support, 1 < (s + a).re := by
    intro a ha
    have := hw a ha
    rw [Complex.add_re]
    linarith
  have hsum : ∀ a ∈ w.support,
      LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + a) := fun a ha =>
    ArithmeticFunction.LSeriesSummable_vonMangoldt (hre a ha)
  rw [LSeries_shiftDivisorStream _ _ _ hsum, xiShiftDivisorPrimeValue,
    xiShiftDivisorLogDeriv, xiShiftDivisorArchimedeanCorrection,
    ← shiftDivisorValue_fun_sub, ← shiftDivisorValue_fun_neg]
  exact shiftDivisorValue_congr w fun a ha =>
    logDeriv_xi_sub_archFactor_eq_neg_vonMangoldtLSeries (hre a ha)

/-- **Symbol reflection dictionary for completed Xi.** The divisor reflection attached to the
coordinate reflection about `σ / 2` acts on Dirichlet symbols as the inversion `n ^ (-a) ↦ n ^ a`
twisted by `n ^ (σ - 1)`. -/
theorem shiftDivisorSymbol_xiReflection (w : ℂ →₀ ℂ) (σ : ℂ) {n : ℕ} (hn : n ≠ 0) :
    shiftDivisorSymbol (reflectShiftDivisor (1 - σ) w) n =
      (n : ℂ) ^ (σ - 1) * w.sum fun a m => m * (n : ℂ) ^ a := by
  rw [shiftDivisorSymbol_reflectShiftDivisor (1 - σ) w hn,
    show -((1 : ℂ) - σ) = σ - 1 by ring]

/-- A completed-Xi reflection eigen-divisor is exactly a Dirichlet symbol obeying the inversion
functional equation with the same eigenvalue. -/
theorem shiftDivisorSymbol_of_xiReflection_eigen {w : ℂ →₀ ℂ} {σ η : ℂ}
    (hw : reflectShiftDivisor (1 - σ) w = η • w) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ (σ - 1) * (w.sum fun a m => m * (n : ℂ) ^ a) =
      η * shiftDivisorSymbol w n := by
  rw [show (σ : ℂ) - 1 = -(1 - σ) by ring]
  exact shiftDivisorSymbol_of_reflect_eq_smul hw hn

/-! ## The one-shift instance -/

/-- The symbol of the two-point divisor `δ_a - δ_0` is `n ^ (-a) - 1`; twisting the von Mangoldt
stream by it is minus the transverse shift source. -/
theorem shiftDivisorStream_pairShiftDivisor_vonMangoldt (a : ℕ) (n : ℕ) :
    shiftDivisorStream (pairShiftDivisor (a : ℂ) 0)
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) n =
      -(xiTransverseShiftArithmetic a n) := by
  rw [shiftDivisorStream, pairShiftDivisor, shiftDivisorSymbol_sub,
    shiftDivisorSymbol_single, shiftDivisorSymbol_single,
    xiTransverseShiftArithmetic_apply, cpowWeight]
  simp
  ring

end

end RHTower
