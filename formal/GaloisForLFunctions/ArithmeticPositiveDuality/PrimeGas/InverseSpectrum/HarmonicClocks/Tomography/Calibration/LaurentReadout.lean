import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.ContinuedTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.ReturnSlope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdjacentShellTrace
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-! # Composition amplitudes in leading Laurent coefficients of clock returns -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open HTGeometry ZeroForcingCalculus

/-- In the right half-plane only the zeta germ can contribute a nonzero order. -/
theorem continuedClockReturn_coefficient (p : Nat.Primes) (D : ℕ+) {s : ℂ} (hs : 0 < s.re) :
    meromorphicTrailingCoeffAt (continuedClockReturn p D) s =
      ((1-heat s (primeRayLabel p D.val)) * meromorphicTrailingCoeffAt riemannZeta s)⁻¹ := by
  rw [continuedClockReturn,meromorphicTrailingCoeffAt_inv]
  change (meromorphicTrailingCoeffAt ((fun w => 1-heat w (primeRayLabel p D.val)) * riemannZeta) s)⁻¹ = _
  have ha := clockFactor_analytic (primeRayLabel p D.val) s
  rw [ha.meromorphicAt.meromorphicTrailingCoeffAt_mul (ZeroForcingCalculus.meromorphicAt_riemannZeta s),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (clockFactor_ne_zero p D hs)]

/-- Comparing the leading coefficients of two returns recovers the entire complex heat
amplitude at regular points and at common poles of every multiplicity. -/
theorem returnCoefficient_excess (p : Nat.Primes) (D : ℕ+) {s : ℂ} (hs : 0 < s.re) :
    meromorphicTrailingCoeffAt (continuedClockReturn p D) s /
      meromorphicTrailingCoeffAt (continuedClockReturn p (D+D)) s - 1 = heat s (primeRayLabel p D.val) := by
  have hd : heat s (primeRayLabel p (D+D).val) = heat s (primeRayLabel p D.val) * heat s (primeRayLabel p D.val) := by
    simp only [primeRayLabel,PNat.add_coe,pow_add,heat_mul]
  have hc := (ZeroForcingCalculus.meromorphicAt_riemannZeta s).meromorphicTrailingCoeffAt_ne_zero
    (meromorphicOrderAt_riemannZeta_ne_top s)
  have h₁ := clockFactor_ne_zero p D hs
  have h₂ := clockFactor_ne_zero p (D+D) hs
  rw [hd] at h₂
  rw [continuedClockReturn_coefficient p D hs,continuedClockReturn_coefficient p (D+D) hs,hd]
  field_simp [h₁,h₂,hc]
  ring

theorem continuedClockReturn_pole_iff (p : Nat.Primes) (D : ℕ+) (s : OpenStrip) :
    meromorphicOrderAt (continuedClockReturn p D) s.val < 0 ↔ riemannZeta s.val = 0 := by
  rw [continuedClockReturn_order p D s.property.1]
  have h1 : s.val ≠ 1 := fun he => s.property.2.ne (by rw [he]; rfl)
  have ha := HTGeometry.analyticAt_riemannZeta h1
  constructor
  · intro ho
    by_contra hn
    rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero ha hn,neg_zero] at ho
    exact ho.false
  · intro hz
    have hp := meromorphicOrderAt_pos_of_analyticAt_eq_zero ha hz
    lift meromorphicOrderAt riemannZeta s.val to ℤ using meromorphicOrderAt_riemannZeta_ne_top s.val with n
    have hn : (0:ℤ) < n := by exact_mod_cast hp
    exact_mod_cast neg_neg_of_pos hn

/-- The Born normalization of the Laurent-coefficient excess is equivalent to norm
conservation on the entire two-copy space. -/
theorem returnCoefficient_iff_isometry (p : Nat.Primes) (D : ℕ+) {s : ℂ} (hs : 0 < s.re) :
    ‖meromorphicTrailingCoeffAt (continuedClockReturn p D) s /
      meromorphicTrailingCoeffAt (continuedClockReturn p (D+D)) s - 1‖^2 = ((primeRayLabel p D.val).val:ℝ)⁻¹ ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  let χ := fun _ : ℕ+ => (1:Circle)
  have h := singleReturn_pole_blockSize χ p D
  rw [returnCoefficient_excess p D hs,← singleReturn_iff_split_isometry χ p D s]
  exact ⟨fun e => e.symm ▸ h,fun ht => tendsto_nhds_unique ht h⟩

/-- RH is exactly the Born magnitude condition on the first Laurent coefficients at all
open-strip poles of a single block and its double. -/
theorem rh_iff_pole_coefficient_born (p : Nat.Primes) (D : ℕ+) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, meromorphicOrderAt (continuedClockReturn p D) s.val < 0 →
      ‖meromorphicTrailingCoeffAt (continuedClockReturn p D) s.val /
        meromorphicTrailingCoeffAt (continuedClockReturn p (D+D)) s.val - 1‖^2 = ((primeRayLabel p D.val).val:ℝ)⁻¹ := by
  rw [rh_iff_trace_zero_forces_isometry]
  constructor
  · intro h s hp
    exact (returnCoefficient_iff_isometry p D s.property.1).mpr
      (h s ((adjacentTrace_zero_iff s).mpr ((continuedClockReturn_pole_iff p D s).mp hp)))
  · intro h s hz
    exact (returnCoefficient_iff_isometry p D s.property.1).mp
      (h s ((continuedClockReturn_pole_iff p D s).mpr ((adjacentTrace_zero_iff s).mp hz)))

#print axioms continuedClockReturn_coefficient
#print axioms returnCoefficient_excess
#print axioms continuedClockReturn_pole_iff
#print axioms returnCoefficient_iff_isometry
#print axioms rh_iff_pole_coefficient_born

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
