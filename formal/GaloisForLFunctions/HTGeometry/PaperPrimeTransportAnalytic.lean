import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeLSeries
import GaloisForLFunctions.HTGeometry.PaperPrimeExponentialRange
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic units from the actual Möbius prime transport

The quotient factor agrees with the reciprocal transported Dirichlet series
on its convergence half-plane. The exact Euler range theorem pays its
nonvanishing on the stated parameter domain. Multiplication then preserves
every meromorphic order, including at zeros and poles of the original source.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped NNReal

noncomputable section

/-- The exactly classified parameter set for an open Euler half-plane. -/
def paperPrimeTransportParameters (p : Nat.Primes) (σ : ℝ) : Set ℂ :=
  {t | t = 1 ∨ (p : ℝ) ^ (-σ) ≤ ‖1 - t‖}

/-- The reciprocal Euler factor obtained from the literal source transport. -/
def paperPrimeTransportFactor (p : Nat.Primes) (t s : ℂ) : ℂ :=
  (1 - ((p : ℕ) : ℂ) ^ (-s)) / (1 - t - ((p : ℕ) : ℂ) ^ (-s))

/-- The continuation formula for the reciprocal of the transported Möbius series. -/
def paperPrimeTransportZeta (p : Nat.Primes) (t s : ℂ) : ℂ :=
  paperPrimeTransportFactor p t s * riemannZeta s

/-- The continuation is identified with the actual source series on the Euler half-plane. -/
theorem paperPrimeTransportZeta_eq_inv_LSeries (p : Nat.Primes) (t : ℂ)
    (s : {s : ℂ // 1 < s.re}) :
    paperPrimeTransportZeta p t s = (LSeries (⇑(paperMoebiusPrimeTransport p t)) s)⁻¹ := by
  rw [paperMoebiusPrimeTransport_LSeries_inv]
  dsimp only [paperPrimeTransportZeta, paperPrimeTransportFactor]
  ring

/-- The exceptional arithmetic nonunit time has an entire explicit Euler multiplier. -/
theorem paperPrimeTransportFactor_time_one (p : Nat.Primes) (s : ℂ) :
    paperPrimeTransportFactor p 1 s = 1 - ((p : ℕ) : ℂ) ^ s := by
  have hp := RHTower.primeCpow_neg_ne_zero s p
  simp only [paperPrimeTransportFactor, sub_self, zero_sub, Complex.cpow_neg]
  field_simp [hp]
  ring

/-- The exceptional-time reciprocal source retains the exact original zeta factor. -/
theorem paperPrimeTransportZeta_time_one (p : Nat.Primes) (s : ℂ) :
    paperPrimeTransportZeta p 1 s = (1 - ((p : ℕ) : ℂ) ^ s) * riemannZeta s := by
  rw [paperPrimeTransportZeta, paperPrimeTransportFactor_time_one]

/-- Analyticity of the multiplier is paid at every point of the classified half-plane. -/
theorem paperPrimeTransportFactor_analyticAt (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    AnalyticAt ℂ (paperPrimeTransportFactor p t) s := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hr : AnalyticAt ℂ (fun z : ℂ => ((p : ℕ) : ℂ) ^ (-z)) (s : ℂ) := by
    have he : (fun z : ℂ => ((p : ℕ) : ℂ) ^ (-z)) =
        (fun z : ℂ => Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-z))) := by
      funext z
      exact Complex.cpow_def_of_ne_zero hp (-z)
    rw [he]
    fun_prop
  have hden := (paperPrimeTransport_openHalfPlane_nonvanishing_iff p σ t).mpr
    t.property (s : ℂ) s.property
  change AnalyticAt ℂ (fun z : ℂ =>
    (1 - ((p : ℕ) : ℂ) ^ (-z)) / (1 - (t : ℂ) - ((p : ℕ) : ℂ) ^ (-z))) (s : ℂ)
  exact (analyticAt_const.sub hr).div (analyticAt_const.sub hr) hden

/-- The same multiplier is nonzero throughout that half-plane. -/
theorem paperPrimeTransportFactor_ne_zero (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    paperPrimeTransportFactor p t s ≠ 0 := by
  have hnum := RHTower.one_sub_primeCpow_neg_ne_zero
    (lt_of_le_of_lt σ.property s.property) p
  have hden := (paperPrimeTransport_openHalfPlane_nonvanishing_iff p σ t).mpr
    t.property (s : ℂ) s.property
  exact div_ne_zero hnum hden

/-- The paid analytic unit preserves the order of every original source, without a source premise. -/
theorem paperPrimeTransportFactor_meromorphicOrder (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re})
    (f : ℂ → ℂ) :
    meromorphicOrderAt (fun z => paperPrimeTransportFactor p t z * f z) s =
      meromorphicOrderAt f s :=
  meromorphicOrderAt_mul_of_ne_zero (paperPrimeTransportFactor_analyticAt p σ t s)
    (paperPrimeTransportFactor_ne_zero p σ t s)

/-- The faithful reciprocal Möbius transport preserves the original zeta divisor orders. -/
theorem paperPrimeTransportZeta_meromorphicOrder (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    meromorphicOrderAt (paperPrimeTransportZeta p t) s = meromorphicOrderAt riemannZeta s :=
  paperPrimeTransportFactor_meromorphicOrder p σ t s riemannZeta

/-- Pointwise source zeros are unchanged on the same fully paid parameter domain. -/
theorem paperPrimeTransportZeta_zero_iff (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    paperPrimeTransportZeta p t s = 0 ↔ riemannZeta s = 0 := by
  change paperPrimeTransportFactor p t s * riemannZeta s = 0 ↔ riemannZeta s = 0
  exact mul_eq_zero.trans (or_iff_right (paperPrimeTransportFactor_ne_zero p σ t s))

/-- Despite the ambient arithmetic unit obstruction, time one preserves all right-half-plane orders. -/
theorem paperPrimeTransportZeta_time_one_meromorphicOrder (p : Nat.Primes)
    (s : {s : ℂ // 0 < s.re}) :
    meromorphicOrderAt (paperPrimeTransportZeta p 1) s = meromorphicOrderAt riemannZeta s :=
  paperPrimeTransportZeta_meromorphicOrder p 0 ⟨1, Or.inl rfl⟩ s

end

end GaloisForLFunctions.HTGeometry
