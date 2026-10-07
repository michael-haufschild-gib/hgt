import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorStripDecay
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Mellin transform of the actual degree-two quotient

Möbius convolution supplies the coefficients of `G/ζ` with absolute convergence
on the original half-plane. Its actual K₀ theta function has Mellin transform
one quarter of the pole-cleared completion on the right contour line.
-/

noncomputable section

open Complex Set
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace RHTower.WeilHigherDenominator

/-- The actual coefficients of division by one copy of zeta. -/
def degreeTwoQuotientCoeff (g : ℕ → ℂ) : ℕ → ℂ :=
  LSeries.convolution g (fun n => (ArithmeticFunction.moebius n : ℂ))

/-- Dividing by zeta preserves the first coefficient. -/
theorem degreeTwoQuotientCoeff_one (g : ℕ → ℂ) : degreeTwoQuotientCoeff g 1 = g 1 := by
  simp [degreeTwoQuotientCoeff, LSeries.convolution_def]

/-- The quotient's absolute convergence follows from the original convergence assumption. -/
theorem degreeTwoQuotientCoeff_summable {g : ℕ → ℂ} {s : ℂ}
    (hg : LSeriesSummable g s) (hs : 1 < s.re) :
    LSeriesSummable (degreeTwoQuotientCoeff g) s :=
  hg.convolution (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)

/-- The convolution represents the actual quotient, without an Euler product for g. -/
theorem LSeries_degreeTwoQuotientCoeff {g : ℕ → ℂ} {s : ℂ}
    (hg : LSeriesSummable g s) (hs : 1 < s.re) :
    LSeries (degreeTwoQuotientCoeff g) s = LSeries g s / riemannZeta s := by
  have hi := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hi
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  rw [degreeTwoQuotientCoeff, LSeries_convolution' hg
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)]
  apply (eq_div_iff hz).mpr
  calc
    LSeries g s * LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s * riemannZeta s =
        LSeries g s * (riemannZeta s * LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s) := by ring
    _ = LSeries g s := by rw [hi, mul_one]

/-- The real weighted summability needed by the Bessel theta transform is produced. -/
theorem degreeTwoQuotientCoeff_weighted_summable {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖degreeTwoQuotientCoeff g n‖ * (n : ℝ) ^ (-σ) :=
  MaassZetaSquaredConverse.summable_of_LSeriesSummable hσ
    (degreeTwoQuotientCoeff_summable (hD.summable σ (by simpa using hσ)) (by simpa using hσ))

/-- Mellin identity on the full half-plane of absolute convergence. -/
theorem hasMellin_degreeTwoQuotient {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g)) s
      ((1 / 4 : ℂ) * (Complex.Gammaℝ s ^ 2 * LSeries g s / riemannZeta s)) := by
  have h := MaassThetaMellin.hasMellin_kTheta
    (fun _ hσ => degreeTwoQuotientCoeff_weighted_summable hD hσ) hs
  rw [LSeries_degreeTwoQuotientCoeff (hD.summable s hs) hs] at h
  convert h using 1; ring

/-- On the actual contour line the transform is the pole-cleared continuation divided by four. -/
theorem hasMellin_poleClearedDegreeTwoCompletion {g : ℕ → ℂ} {E H : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {s : ℂ} (hs : 2 ≤ s.re) :
    HasMellin (MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g)) s
      ((1 / 4 : ℂ) * poleClearedDegreeTwoCompletion P H s) := by
  rw [poleClearedDegreeTwoCompletion_eq_right hD P hfac hord hs]
  exact hasMellin_degreeTwoQuotient hD (by linarith)

end RHTower.WeilHigherDenominator
