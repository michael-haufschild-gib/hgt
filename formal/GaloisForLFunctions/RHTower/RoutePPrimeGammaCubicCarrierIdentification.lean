import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum
import GaloisForLFunctions.RHTower.VonMangoldtGammaJetBoundaryConvergence
import GaloisForLFunctions.RHTower.SummablePurePointPhaseRecurrence

/-!
# Route P / prime--Gamma cubic carrier identification

The primitive collision kernel of Route P is not an auxiliary prime-indexed construction.  This
module identifies its complete non-diagonal Gram with a natural-number von Mangoldt carrier.  The
pullback along prime-power valuation is literal, its diagonal is the inverse-cubic-log von Mangoldt
mass, and its global trace budget is exactly the sum of that source mass.

This joins the Route P collision geometry to the coefficient-faithful prime--Gamma source used by
the Gamma-jet and hard-edge routes.  It does not assert the remaining source-to-Xi incidence map.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Cubic collision mass on the native natural-number von Mangoldt carrier. -/
def routePPrimeGammaCubicWeight (n : ℕ) : ℝ :=
  (115 / 864 : ℝ) * vonMangoldtInverseLogPowerWeight 0 n

/-- Prime-power valuation carries the natural-number cubic mass to the existing primitive Euler
weight with every coefficient and divisor multiplicity unchanged. -/
theorem routePPrimeGammaCubicWeight_valuation
    (pe : Nat.Primes × ℕ) :
    routePPrimeGammaCubicWeight (xiGammaEulerValuationNat pe) =
      xiGammaEulerPrimitiveCubicLogMomentWeight pe := by
  apply Complex.ofReal_injective
  have hn : xiGammaEulerValuationNat pe ≠ 0 := by
    exact pow_ne_zero _ pe.1.property.ne_zero
  calc
    ((routePPrimeGammaCubicWeight (xiGammaEulerValuationNat pe) : ℝ) : ℂ) =
        xiGammaEulerPrimitiveCubicLogMomentDiagonal 0 pe := by
      rw [xiGammaEulerPrimitiveCubicLogMomentDiagonal,
        cubicLogMomentHellingerHorizontalKernel_self
          (xiGammaEulerPrimitiveLogFrequency_pos pe),
        xiGammaEulerPrimitiveBalancedReflectionCoeff_eq,
        finiteVonMangoldtWeight_eq_ofReal hn]
      rw [routePPrimeGammaCubicWeight, vonMangoldtInverseLogPowerWeight,
        finiteVonMangoldtRealWeight, xiGammaEulerPrimitiveLogFrequency]
      norm_cast
      ring
    _ = (xiGammaEulerPrimitiveCubicLogMomentWeight pe : ℂ) :=
      xiGammaEulerPrimitiveCubicLogMomentDiagonal_eq_weight 0 pe

/-- Diagonal von Mangoldt amplitude on an arbitrary finite natural-number packet. -/
def routePPrimeGammaCubicScalingMatrix {N : ℕ}
    (n : Fin N → ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => finiteVonMangoldtDepthOneAmplitude (n i)

/-- Complete Route P collision Gram on the natural-number prime--Gamma carrier. -/
def routePPrimeGammaCubicKernelMatrix {N : ℕ}
    (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  routePPrimeGammaCubicScalingMatrix n *
    routePCollisionCubicKernelMatrix R
      (fun i => Real.log (n i : ℝ)) kappa *
    (routePPrimeGammaCubicScalingMatrix n)ᴴ

/-- The full non-diagonal primitive matrix is the literal pullback of the natural-number
prime--Gamma matrix along prime-power valuation. -/
theorem routePPrimitiveCollisionCubicKernelMatrix_eq_primeGamma_pullback
    {N : ℕ} (R : ℝ) (pe : Fin N → Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) :
    routePPrimitiveCollisionCubicKernelMatrix R pe kappa =
      routePPrimeGammaCubicKernelMatrix R
        (fun i => xiGammaEulerValuationNat (pe i)) kappa := by
  rfl

/-- Positivity holds on arbitrary finite natural-number packets, not only on a chosen list of
primitive Euler cells. -/
theorem routePPrimeGammaCubicKernelMatrix_posSemidef
    {N : ℕ} {R : ℝ} {n : Fin N → ℕ} {kappa : Fin N → ℝ}
    (hR : 0 < R) (hn : ∀ i, 1 < n i) :
    (routePPrimeGammaCubicKernelMatrix R n kappa).PosSemidef := by
  exact (routePCollisionCubicKernelMatrix_posSemidef hR
    (fun i => Real.log_pos (by exact_mod_cast hn i))).mul_mul_conjTranspose_same
      (routePPrimeGammaCubicScalingMatrix n)

/-- Entrywise form of the natural-number collision congruence. -/
theorem routePPrimeGammaCubicKernelMatrix_apply
    {N : ℕ} (R : ℝ) (n : Fin N → ℕ) (kappa : Fin N → ℝ)
    (i j : Fin N) :
    routePPrimeGammaCubicKernelMatrix R n kappa i j =
      finiteVonMangoldtDepthOneAmplitude (n i) *
        routePCollisionCubicKernel R
          (Real.log (n i : ℝ)) (Real.log (n j : ℝ))
          (kappa j - kappa i) *
        star (finiteVonMangoldtDepthOneAmplitude (n j)) := by
  simp [routePPrimeGammaCubicKernelMatrix,
    routePPrimeGammaCubicScalingMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, routePCollisionCubicKernelMatrix]

/-- The diagonal is exactly the cubic von Mangoldt mass, independently of collision ordinate. -/
theorem routePPrimeGammaCubicKernelMatrix_diagonal
    {N : ℕ} {R : ℝ} (hR : 0 < R) (n : Fin N → ℕ)
    (hn : ∀ i, 1 < n i) (kappa : Fin N → ℝ) (i : Fin N) :
    routePPrimeGammaCubicKernelMatrix R n kappa i i =
      (routePPrimeGammaCubicWeight (n i) : ℂ) := by
  rw [routePPrimeGammaCubicKernelMatrix_apply, sub_self,
    routePCollisionCubicKernel_diagonal hR
      (Real.log_pos (by exact_mod_cast hn i))]
  have hni : n i ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one (hn i))
  have hampStar : star (finiteVonMangoldtDepthOneAmplitude (n i)) =
      finiteVonMangoldtDepthOneAmplitude (n i) := by
    simp [finiteVonMangoldtDepthOneAmplitude]
  rw [hampStar, show
    finiteVonMangoldtDepthOneAmplitude (n i) *
          (((115 : ℝ) / (864 * Real.log (n i : ℝ) ^ (3 : ℕ)) : ℝ) : ℂ) *
        finiteVonMangoldtDepthOneAmplitude (n i) =
      finiteVonMangoldtDepthOneAmplitude (n i) ^ (2 : ℕ) *
        (((115 : ℝ) / (864 * Real.log (n i : ℝ) ^ (3 : ℕ)) : ℝ) : ℂ) by ring,
    finiteVonMangoldtDepthOneAmplitude_sq hni,
    finiteVonMangoldtWeight_eq_ofReal hni]
  rw [routePPrimeGammaCubicWeight, vonMangoldtInverseLogPowerWeight,
    finiteVonMangoldtRealWeight]
  norm_cast
  ring

theorem summable_routePPrimeGammaCubicWeight :
    Summable routePPrimeGammaCubicWeight := by
  exact (summable_vonMangoldtInverseLogPowerWeight 0).mul_left (115 / 864 : ℝ)

theorem routePPrimeGammaCubicWeight_nonneg (n : ℕ) :
    0 ≤ routePPrimeGammaCubicWeight n := by
  exact mul_nonneg (by norm_num)
    (vonMangoldtInverseLogPowerWeight_nonneg 0 n)

/-- Reversible source-clock displacement of the fixed coefficient-faithful
prime--Gamma cubic packet.  This definition contains no Xi divisor data. -/
def routePPrimeGammaCubicPhaseEnergy (t : ℕ) : ℝ :=
  summablePhaseEnergy routePPrimeGammaCubicWeight
    (fun n => Real.log (n : ℝ)) t

/-- The complete fixed cubic prime--Gamma packet returns arbitrarily close
to its initial source state after every prescribed integer horizon.  This
closes the countable source-recurrence obligation; it does not identify a
source return with an Xi collision or supply irreversible action. -/
theorem exists_arbitrarilyLate_routePPrimeGammaCubicPhaseEnergy_lt
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ t : ℕ, N ≤ t ∧ routePPrimeGammaCubicPhaseEnergy t < ε := by
  simpa only [routePPrimeGammaCubicPhaseEnergy] using
    exists_arbitrarilyLate_summablePhaseEnergy_recurrence
      routePPrimeGammaCubicWeight (fun n => Real.log (n : ℝ))
      routePPrimeGammaCubicWeight_nonneg
      summable_routePPrimeGammaCubicWeight hε N

/-- The P-G175 budget is exactly the cubic moment of the full natural-number von Mangoldt
prime--Gamma carrier. -/
theorem routePPrimitiveCollisionCubicTraceBudget_eq_primeGamma :
    routePPrimitiveCollisionCubicTraceBudget =
      ∑' n : ℕ, routePPrimeGammaCubicWeight n := by
  have hsupp : Function.support routePPrimeGammaCubicWeight ⊆
      {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hpow
    have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
    exact hn (by simp [routePPrimeGammaCubicWeight,
      vonMangoldtInverseLogPowerWeight, finiteVonMangoldtRealWeight, hzero])
  have hreindex := tsum_eq_tsum_primes_of_support_subset_prime_powers
    summable_routePPrimeGammaCubicWeight hsupp
  have hcomp : Summable (fun pe : Nat.Primes × ℕ =>
      routePPrimeGammaCubicWeight (xiGammaEulerValuationNat pe)) :=
    summable_routePPrimeGammaCubicWeight.comp_injective
      xiGammaEulerValuationNat_injective_commonTest
  rw [routePPrimitiveCollisionCubicTraceBudget]
  calc
    (∑' pe : Nat.Primes × ℕ,
        xiGammaEulerPrimitiveCubicLogMomentWeight pe) =
        ∑' pe : Nat.Primes × ℕ,
          routePPrimeGammaCubicWeight (xiGammaEulerValuationNat pe) := by
      apply tsum_congr
      intro pe
      exact (routePPrimeGammaCubicWeight_valuation pe).symm
    _ = ∑' p : Nat.Primes, ∑' e : ℕ,
        routePPrimeGammaCubicWeight (p.1 ^ (e + 1)) := by
      simpa [xiGammaEulerValuationNat] using hcomp.tsum_prod
    _ = ∑' n : ℕ, routePPrimeGammaCubicWeight n := hreindex.symm

end

end RHTower
