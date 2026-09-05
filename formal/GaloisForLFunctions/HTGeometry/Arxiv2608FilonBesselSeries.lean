import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelBessel
import GaloisForLFunctions.HTGeometry.PoincareSeriesBesselCoefficient

/-!
# Exact Bessel series used by arXiv:2608.18589 Filon moments

The paper evaluates local Bessel moments through the `J_0` Taylor series.  This module specializes
the corpus's independently proved all-order Bessel expansion to the scaled Filon kernel and its
monomial-weighted integrand.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Exact all-order series for the scaled Filon kernel. -/
theorem filonBesselKernel_series (b u : ℝ) :
    ((GaloisForLFunctions.RHTower.besselJ0 (b * u) : ℝ) : ℂ) =
      ∑' k : ℕ, (-1 : ℂ) ^ k * ((b * u : ℝ) : ℂ) ^ (2 * k) /
        ((4 : ℂ) ^ k * ((k.factorial : ℂ) ^ 2)) :=
  RHTower.ofReal_besselJ0_eq_secondFactorial_series (b * u)

/-- Pointwise integrand expansion underlying equation (19): multiplying by a local monomial shifts
every Bessel-series power from `2k` to `r + 2k`. -/
theorem filonBesselMomentIntegrand_series (b u : ℝ) (r : ℕ) :
    (((u ^ r * GaloisForLFunctions.RHTower.besselJ0 (b * u) : ℝ)) : ℂ) =
      ∑' k : ℕ, (-1 : ℂ) ^ k * (b : ℂ) ^ (2 * k) * (u : ℂ) ^ (r + 2 * k) /
        ((4 : ℂ) ^ k * ((k.factorial : ℂ) ^ 2)) := by
  have hcast : (((u ^ r * GaloisForLFunctions.RHTower.besselJ0 (b * u) : ℝ)) : ℂ) =
      (u : ℂ) ^ r *
        ((GaloisForLFunctions.RHTower.besselJ0 (b * u) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, filonBesselKernel_series]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  push_cast
  rw [mul_pow, pow_add]
  ring

/-! ## Arbitrary integer-order kernels -/

/-- The corpus Poincare-series Bessel function supplies the paper's Filon kernel at every
nonnegative integer angular order, not only at order zero. -/
theorem filonIntegerOrderBesselKernel_series (m : ℕ) (b u : ℝ) :
    besselJ m (b * u) =
      ∑' j : ℕ, (-1 : ℝ) ^ j * (b * u / 2) ^ (2 * j + m) /
        ((j.factorial : ℝ) * ((j + m).factorial : ℝ)) := by
  rfl

/-- Monomial-weighted arbitrary-order Filon integrand.  This is the exact series that supplies
moments for every cylindrical Fourier mode `m`. -/
theorem filonIntegerOrderBesselMomentIntegrand_series
    (m : ℕ) (b u : ℝ) (r : ℕ) :
    u ^ r * besselJ m (b * u) =
      ∑' j : ℕ, (-1 : ℝ) ^ j * (b / 2) ^ (2 * j + m) *
        u ^ (r + 2 * j + m) /
          ((j.factorial : ℝ) * ((j + m).factorial : ℝ)) := by
  rw [besselJ, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [show b * u / 2 = (b / 2) * u by ring, mul_pow]
  rw [show r + 2 * j + m = r + (2 * j + m) by omega, pow_add]
  ring

/-- Every positive integer-order Filon kernel vanishes on the cylindrical axis. -/
@[simp] theorem filonIntegerOrderBesselKernel_zero_succ (m : ℕ) :
    besselJ (m + 1) 0 = 0 := by
  simp [besselJ]

/-- The order-zero power-series carrier and the corpus integral carrier are the same function. -/
theorem poincareBesselJ_zero_eq_corpusBesselJ0 (x : ℝ) :
    besselJ 0 x = GaloisForLFunctions.RHTower.besselJ0 x := by
  apply Complex.ofReal_injective
  rw [besselJ, Complex.ofReal_tsum,
    RHTower.ofReal_besselJ0_eq_secondFactorial_series]
  apply tsum_congr
  intro j
  push_cast
  simp only [Nat.add_zero]
  rw [div_pow]
  have htwo : (2 : ℂ) ^ (2 * j) = (4 : ℂ) ^ j := by
    rw [pow_mul]
    norm_num
  rw [htwo]
  ring

end GaloisForLFunctions.HTGeometry
