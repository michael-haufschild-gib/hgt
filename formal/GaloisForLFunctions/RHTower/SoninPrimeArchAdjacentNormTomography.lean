import GaloisForLFunctions.RHTower.SoninPrimeArchCofinalMomentSection

/-!
# Adjacent Sonin norm tomography for the prime--Gamma moment weld

The all-moment Sonin/prime--Gamma coupling can be tested on only two explicit families of
finite source probes.  The monomial norm `Q_a(X^n)` reads the even moment `m_a(2n)`.  The adjacent
binomial norm `Q_a(X^n + X^(n+1))`, together with the neighboring monomial norms, reads the odd
moment `m_a(2n+1)` by polarization.  Hence these two norm families reconstruct the whole moment
germ.

This is a source-to-source reduction.  Its premise contains neither Xi divisor locations nor any
RH-equivalent sign or limiting measure.  The remaining analytic problem is to prove convergence of
these concrete Hilbert--Schmidt norm values from the explicit Sonin kernel to the normalized
prime--Gamma targets.
-/

open Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A monomial Sonin trace-Hankel value is the even member of the intrinsic energy-moment
sequence. -/
theorem soninAllPrimeTraceHankel_monomial_eq_energyMoment
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    soninAllPrimeTraceHankel a (X ^ n) =
      soninAllPrimeEnergyMoment a (2 * n) := by
  rw [soninAllPrimeTraceHankel_eq_energyMoment_sum a ha]
  rw [support_X_pow]
  simp [two_mul]

/-- The adjacent-binomial norm contains exactly the two neighboring even moments and twice the
intervening odd moment. -/
theorem soninAllPrimeTraceHankel_adjacent_eq_energyMoments
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    soninAllPrimeTraceHankel a (X ^ n + X ^ (n + 1)) =
      soninAllPrimeEnergyMoment a (2 * n) +
        2 * soninAllPrimeEnergyMoment a (2 * n + 1) +
        soninAllPrimeEnergyMoment a (2 * n + 2) := by
  rw [soninAllPrimeTraceHankel_eq_energyMoment_sum a ha]
  have hsupp : (X ^ n + X ^ (n + 1) : Polynomial ℝ).support = {n, n + 1} := by
    ext k
    by_cases hkn : k = n
    · subst k
      simp
    · by_cases hks : k = n + 1
      · subst k
        simp
      · simp [hkn, hks]
  rw [hsupp]
  simp
  ring_nf

/-- One positive aperture sequence matches the prime--Gamma targets on only the monomial norms
and the adjacent-binomial norms.  Each premise is a scalar value relation for an explicit finite
Sonin probe. -/
def SoninPrimeArchAdjacentNormCoupling (aperture : ℕ → ℝ) : Prop :=
  (∀ j, 0 < aperture j) ∧
    (∀ n,
      Tendsto
        (fun j => soninAllPrimeTraceHankel (aperture j) (X ^ n))
        atTop
        (nhds ((normalizedPrimeArchMoment (2 * n) : ℝ) : ℂ))) ∧
    ∀ n,
      Tendsto
        (fun j => soninAllPrimeTraceHankel (aperture j)
          (X ^ n + X ^ (n + 1)))
        atTop
        (nhds
          (((normalizedPrimeArchMoment (2 * n) : ℝ) : ℂ) +
            2 * ((normalizedPrimeArchMoment (2 * n + 1) : ℝ) : ℂ) +
            ((normalizedPrimeArchMoment (2 * n + 2) : ℝ) : ℂ)))

/-- Adjacent norm tomography reconstructs convergence of every Sonin moment.  Even moments are
monomial norms; odd moments are obtained by subtracting the two neighboring monomial norms from
the adjacent-binomial norm and dividing by two. -/
theorem soninPrimeArchSingleMomentCoupling_of_adjacentNormCoupling
    {aperture : ℕ → ℝ}
    (h : SoninPrimeArchAdjacentNormCoupling aperture) :
    SoninPrimeArchSingleMomentCoupling aperture := by
  refine ⟨h.1, fun r => ?_⟩
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨n, rfl⟩ := hr
    simpa [soninAllPrimeTraceHankel_monomial_eq_energyMoment, h.1, two_mul] using
      h.2.1 n
  · obtain ⟨n, rfl⟩ := hr
    have hcomb := ((h.2.2 n).sub (h.2.1 n)).sub (h.2.1 (n + 1))
    have hhalf := hcomb.const_mul ((2 : ℂ)⁻¹)
    convert hhalf using 1
    · funext j
      rw [soninAllPrimeTraceHankel_adjacent_eq_energyMoments
          (aperture j) (h.1 j),
        soninAllPrimeTraceHankel_monomial_eq_energyMoment
          (aperture j) (h.1 j),
        soninAllPrimeTraceHankel_monomial_eq_energyMoment
          (aperture j) (h.1 j)]
      ring_nf
    · ring_nf

/-- Conversely, all-moment convergence implies convergence of the two norm families. -/
theorem soninPrimeArchAdjacentNormCoupling_of_singleMomentCoupling
    {aperture : ℕ → ℝ}
    (h : SoninPrimeArchSingleMomentCoupling aperture) :
    SoninPrimeArchAdjacentNormCoupling aperture := by
  refine ⟨h.1, ?_, ?_⟩
  · intro n
    convert h.2 (2 * n) using 1
    funext j
    exact soninAllPrimeTraceHankel_monomial_eq_energyMoment
      (aperture j) (h.1 j) n
  · intro n
    have hsum :=
      ((h.2 (2 * n)).add ((h.2 (2 * n + 1)).const_mul (2 : ℂ))).add
        (h.2 (2 * n + 2))
    convert hsum using 1
    funext j
    rw [soninAllPrimeTraceHankel_adjacent_eq_energyMoments
      (aperture j) (h.1 j)]

/-- Exact tomography theorem: the two explicit norm families carry precisely the same convergence
data as the full Sonin/prime--Gamma moment germ. -/
theorem soninPrimeArchAdjacentNormCoupling_iff_singleMomentCoupling
    {aperture : ℕ → ℝ} :
    SoninPrimeArchAdjacentNormCoupling aperture ↔
      SoninPrimeArchSingleMomentCoupling aperture :=
  ⟨soninPrimeArchSingleMomentCoupling_of_adjacentNormCoupling,
    soninPrimeArchAdjacentNormCoupling_of_singleMomentCoupling⟩

/-- **Adjacent-norm source chain to RH.**  Convergence of the two explicit Sonin norm families to
their normalized prime--Gamma values implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_soninPrimeArchAdjacentNormCoupling
    {aperture : ℕ → ℝ}
    (h : SoninPrimeArchAdjacentNormCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninPrimeArchSingleMomentCoupling
    (soninPrimeArchSingleMomentCoupling_of_adjacentNormCoupling h)

end

end RHTower
