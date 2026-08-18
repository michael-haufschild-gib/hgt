import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic
import GaloisForLFunctions.HTGeometry.HorizonTruncationCancel

/-!
# The reciprocal tangent at the fold: nonzero constant term, and coprimality

Two steps of §3 of the projective-horizon card.  §3's conclusion — two states of one critical fibre
with the same **coprime** vertical tangent pair are equal — is already
`CriticalFibreSharedTangentRigidity.criticalFibre_eq_of_shared_coprime_tangent`, and `U(0) ≠ 0` is
already `CriticalSchurKernelLeadingCoefficient.criticalSchurGeneric_ker_coord_zero_ne_zero`.  What
was missing is the coprimality itself.

* `criticalReciprocalInfinitesimal_coeff_zero_ne_zero` — step `3b`, `V(0) ≠ 0`.  Since
  `dY = -(Y² dX)`, this is one application of `Polynomial.mul_coeff_zero`.

* `isCoprime_of_low_tangent_unique` — step `3c`.  A common factor `g` of the pair has `g(0) ≠ 0`,
  so `HorizonTruncationCancel.tangent_relation_of_common_factor` divides the truncated relation by
  it and the quotient pair is again low; uniqueness of the low pair up to scale then forces `g` to
  be a unit.  The uniqueness hypothesis is supplied by generic corank one
  (`CriticalSchurGenericCorank.finrank_ker_criticalSchurGenericMatrix_eq_one`).
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1000000

/-- The constant term of the first-order reciprocal response. -/
theorem criticalReciprocalInfinitesimal_coeff_zero {K : Type*} [CommRing K] (Y dX : K[X]) :
    (criticalReciprocalInfinitesimal Y dX).coeff 0
      = -(Y.coeff 0 * Y.coeff 0 * dX.coeff 0) := by
  simp [criticalReciprocalInfinitesimal, Polynomial.mul_coeff_zero]

/-- **The reciprocal tangent has nonzero constant term.**  On the chart the reciprocal jet has a
nonzero constant term, so a low tangent with `U(0) ≠ 0` produces `V(0) ≠ 0`. -/
theorem criticalReciprocalInfinitesimal_coeff_zero_ne_zero {K : Type*} [CommRing K]
    [NoZeroDivisors K] {Y dX : K[X]} (hY : Y.coeff 0 ≠ 0) (hdX : dX.coeff 0 ≠ 0) :
    (criticalReciprocalInfinitesimal Y dX).coeff 0 ≠ 0 := by
  rw [criticalReciprocalInfinitesimal_coeff_zero, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hY hY) hdX

/-- **Uniqueness of the low tangent pair forces it to be coprime.**  If the two components have
nonzero constant term and every low pair satisfying the same truncated relation is a scalar
multiple of this one, then a common factor is a unit. -/
theorem isCoprime_of_low_tangent_unique {K : Type*} [Field K] {U V A B : K[X]} {L : ℕ}
    (hU0 : U.coeff 0 ≠ 0) (hV0 : V.coeff 0 ≠ 0)
    (hrel : (X : K[X]) ^ L ∣ U * B + A * V)
    (huniq : ∀ U' V' : K[X], U'.degree ≤ U.degree → V'.degree ≤ V.degree →
      (X : K[X]) ^ L ∣ U' * B + A * V' → ∃ c : K, U' = Polynomial.C c * U) :
    IsCoprime U V := by
  classical
  have hUne : U ≠ 0 := fun h => hU0 (by rw [h]; simp)
  have hVne : V ≠ 0 := fun h => hV0 (by rw [h]; simp)
  obtain ⟨U', hU'⟩ := EuclideanDomain.gcd_dvd_left U V
  obtain ⟨V', hV'⟩ := EuclideanDomain.gcd_dvd_right U V
  set g := EuclideanDomain.gcd U V with hg
  have hg0 : g.coeff 0 ≠ 0 := by
    intro h0
    apply hU0
    rw [hU', Polynomial.mul_coeff_zero, h0, zero_mul]
  have hrel' : (X : K[X]) ^ L ∣ U' * B + A * V' :=
    tangent_relation_of_common_factor hg0 hU' hV' hrel
  have hU'deg : U'.degree ≤ U.degree :=
    Polynomial.degree_le_of_dvd ⟨g, by rw [hU']; ring⟩ hUne
  have hV'deg : V'.degree ≤ V.degree :=
    Polynomial.degree_le_of_dvd ⟨g, by rw [hV']; ring⟩ hVne
  obtain ⟨c, hc⟩ := huniq U' V' hU'deg hV'deg hrel'
  have hUU : U = (g * Polynomial.C c) * U := by
    conv_lhs => rw [hU', hc]
    ring
  have hone : g * Polynomial.C c = 1 := by
    have h1 : (g * Polynomial.C c) * U = 1 * U := by rw [one_mul, ← hUU]
    exact mul_right_cancel₀ hUne h1
  exact EuclideanDomain.gcd_isUnit_iff.mp (isUnit_iff_exists_inv.mpr ⟨_, hone⟩)

end GaloisForLFunctions.HTGeometry
