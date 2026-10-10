import GaloisForLFunctions.HTGeometry.PaperPrimeTransportAnalytic
import GaloisForLFunctions.RHTower.RiemannTower
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Completed source of the literal prime transport

The multiplier acts on the original completed Xi. Its identification with
the reciprocal transported Möbius series uses the original completion
quotient on the convergence half-plane. Analyticity, multiplicities and
the first differential at every original zero are then proved explicitly.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped NNReal

noncomputable section

/-- Original completion applied to the reciprocal transported source. -/
def paperPrimeTransportXi (p : Nat.Primes) (t s : ℂ) : ℂ :=
  paperPrimeTransportFactor p t s * RHTower.xi s

/-- Faithful completion of the actual Dirichlet series on its convergence domain. -/
theorem paperPrimeTransportXi_eq_completed_inv_LSeries (p : Nat.Primes) (t : ℂ)
    (s : {s : ℂ // 1 < s.re}) :
    paperPrimeTransportXi p t s = (RHTower.xi s / riemannZeta s) *
      (LSeries (⇑(paperMoebiusPrimeTransport p t)) s)⁻¹ := by
  rw [← paperPrimeTransportZeta_eq_inv_LSeries]
  dsimp only [paperPrimeTransportXi, paperPrimeTransportZeta]
  have hz := riemannZeta_ne_zero_of_one_lt_re s.property
  field_simp

/-- The transported completion is analytic on the fully paid parameter domain. -/
theorem paperPrimeTransportXi_analyticAt (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    AnalyticAt ℂ (paperPrimeTransportXi p t) s :=
  (paperPrimeTransportFactor_analyticAt p σ t s).mul
    (RHTower.xi_analyticOnNhd_univ s (Set.mem_univ _))

/-- All original completed-source multiplicities are retained. -/
theorem paperPrimeTransportXi_meromorphicOrder (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    meromorphicOrderAt (paperPrimeTransportXi p t) s = meromorphicOrderAt RHTower.xi s :=
  paperPrimeTransportFactor_meromorphicOrder p σ t s RHTower.xi

/-- Original completed-source zeros are preserved and reflected. -/
theorem paperPrimeTransportXi_zero_iff (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ) (s : {s : ℂ // (σ : ℝ) < s.re}) :
    paperPrimeTransportXi p t s = 0 ↔ RHTower.xi s = 0 := by
  change paperPrimeTransportFactor p t s * RHTower.xi s = 0 ↔ RHTower.xi s = 0
  exact mul_eq_zero.trans (or_iff_right (paperPrimeTransportFactor_ne_zero p σ t s))

/-- The first differential at an actual Xi zero is multiplied by the same nonzero unit. -/
theorem paperPrimeTransportXi_deriv_at_zero (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ)
    (s : {s : ℂ // (σ : ℝ) < s.re ∧ RHTower.xi s = 0}) :
    deriv (paperPrimeTransportXi p t) s =
      paperPrimeTransportFactor p t s * deriv RHTower.xi s := by
  have hu : DifferentiableAt ℂ (paperPrimeTransportFactor p t) (s : ℂ) :=
    (paperPrimeTransportFactor_analyticAt p σ t ⟨s, s.property.1⟩).differentiableAt
  change deriv (paperPrimeTransportFactor p t * RHTower.xi) (s : ℂ) = _
  rw [deriv_mul hu (RHTower.xi_differentiable s), s.property.2, mul_zero, zero_add]

/-- Simplicity, expressed by the first differential, is preserved at every original zero. -/
theorem paperPrimeTransportXi_deriv_zero_iff (p : Nat.Primes) (σ : ℝ≥0)
    (t : paperPrimeTransportParameters p σ)
    (s : {s : ℂ // (σ : ℝ) < s.re ∧ RHTower.xi s = 0}) :
    deriv (paperPrimeTransportXi p t) s = 0 ↔ deriv RHTower.xi s = 0 := by
  rw [paperPrimeTransportXi_deriv_at_zero]
  exact mul_eq_zero.trans
    (or_iff_right (paperPrimeTransportFactor_ne_zero p σ t ⟨s, s.property.1⟩))

end

end GaloisForLFunctions.HTGeometry
