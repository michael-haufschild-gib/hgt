import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The safe-half-plane arithmetic ratio wall is an automatic zeta square

The leading full-source theta wall has ordered-pair ratio atoms. On the absolute-convergence
half-plane, the complex character of their log-ratio measure is the double Dirichlet series below.
It factors as `ζ(z) * conj (ζ(z))`, so its spectral sign is automatic. This is a source-specific
no-go for trying to derive RH from positivity of that scalar wall alone; it says nothing about
the signed completed current or its boundary continuation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Ordered-pair character of the arithmetic ratio wall. For `z = σ + it`, this is
`(nm)^(-σ) exp (it (log m - log n))` at positive integers `n,m`. -/
def thetaWallOrderedPairSpectralTerm (z : ℂ) (nm : ℕ × ℕ) : ℂ :=
  (1 / ((nm.1 + 1 : ℕ) : ℂ) ^ z) *
    (1 / ((nm.2 + 1 : ℕ) : ℂ) ^ (star z))

/-- Exact source-level Fourier factorization wherever the double ratio sum converges absolutely. -/
theorem thetaWallOrderedPairSpectrum_eq_zeta_square {z : ℂ} (hz : 1 < z.re) :
    (∑' nm : ℕ × ℕ, thetaWallOrderedPairSpectralTerm z nm) =
      riemannZeta z * star (riemannZeta z) := by
  let f : ℕ → ℂ := fun n => 1 / ((n + 1 : ℕ) : ℂ) ^ z
  let g : ℕ → ℂ := fun n => 1 / ((n + 1 : ℕ) : ℂ) ^ star z
  have hz' : 1 < (star z).re := by simpa using hz
  have hf : Summable f := by
    have h : Summable (fun n : ℕ => 1 / (n : ℂ) ^ z) :=
      Complex.summable_one_div_nat_cpow.mpr hz
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ z) 1).mpr h)
  have hg : Summable g := by
    have h : Summable (fun n : ℕ => 1 / (n : ℂ) ^ star z) :=
      Complex.summable_one_div_nat_cpow.mpr hz'
    simpa only [g, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ star z) 1).mpr h)
  have hprod := tsum_mul_tsum_of_summable_norm
    (f := f) (g := g) hf.norm hg.norm
  change (∑' nm : ℕ × ℕ, f nm.1 * g nm.2) = _
  rw [← hprod]
  have hfz : (∑' n, f n) = riemannZeta z := by
    simpa [f] using (zeta_eq_tsum_one_div_nat_add_one_cpow hz).symm
  have hgz : (∑' n, g n) = star (riemannZeta z) := by
    have h0 : (∑' n, g n) = riemannZeta (star z) := by
      simpa [g] using (zeta_eq_tsum_one_div_nat_add_one_cpow hz').symm
    exact h0.trans (riemannZeta_conj z)
  simpa only [thetaWallOrderedPairSpectralTerm, f, g] using congrArg₂ (· * ·) hfz hgz

theorem thetaWallOrderedPairSpectrum_eq_normSq {z : ℂ} (hz : 1 < z.re) :
    (∑' nm : ℕ × ℕ, thetaWallOrderedPairSpectralTerm z nm) =
      (Complex.normSq (riemannZeta z) : ℂ) := by
  rw [thetaWallOrderedPairSpectrum_eq_zeta_square hz]
  exact Complex.mul_conj _

/-- Safe-chamber wall spectral positivity is tautological and cannot orient Xi zeros. -/
theorem thetaWallOrderedPairSpectrum_re_nonneg {z : ℂ} (hz : 1 < z.re) :
    0 ≤ (∑' nm : ℕ × ℕ, thetaWallOrderedPairSpectralTerm z nm).re := by
  rw [thetaWallOrderedPairSpectrum_eq_normSq hz]
  exact Complex.normSq_nonneg _

end

end RHTower
