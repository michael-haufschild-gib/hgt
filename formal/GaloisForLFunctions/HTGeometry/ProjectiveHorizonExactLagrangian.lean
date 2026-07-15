import GaloisForLFunctions.HTGeometry.ProjectiveHorizonLandauGinzburgDuality

/-!
# The reciprocal horizon graph is an exact Lagrangian constraint

The coefficient-residue pairing on two copies of a truncated scalar jet space is the canonical
symplectic pairing.  The tangent graph of inversion is isotropic because
`dY = -Y^2 dX` and scalar multiplication is commutative.  Dimension counting and the logarithmic
primitive are retained at paper level; this file certifies the exact algebraic isotropy identity.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The coefficient pairing of a raw jet with its reversed reciprocal momentum packet. -/
noncomputable def criticalHorizonLegendrePairing
    {K : Type*} [CommSemiring K] (N : ℕ) (Xj Y : K[X]) : K :=
  (Xj * Y).coeff N

/-- The coefficient-residue pairing is exactly the canonical dot product of a raw jet packet
with the coefficient-reversed reciprocal momentum packet. -/
theorem criticalHorizonLegendrePairing_eq_reversedDotProduct
    {K : Type*} [CommSemiring K] (N : ℕ) (Xj Y : K[X]) :
    criticalHorizonLegendrePairing N Xj Y =
      ∑ i ∈ Finset.range (N + 1), Xj.coeff i * Y.coeff (N - i) := by
  rw [criticalHorizonLegendrePairing, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Every positive source--momentum pairing below the inverse truncation vanishes. -/
theorem criticalHorizonLegendrePairing_eq_zero_of_inverse
    {K : Type*} [Field K] {Xj Y : K[X]} {L N : ℕ}
    (hN : 0 < N) (hNL : N < L) (hInv : X ^ L ∣ Xj * Y - 1) :
    criticalHorizonLegendrePairing N Xj Y = 0 := by
  have hcoeff : (Xj * Y - 1).coeff N = 0 :=
    (X_pow_dvd_iff.mp hInv) N hNL
  simpa [criticalHorizonLegendrePairing, coeff_sub, coeff_one, hN.ne'] using hcoeff

/-- The top-coefficient symplectic pairing on two tangent pairs of raw and reciprocal jets. -/
noncomputable def criticalHorizonSymplecticPairing
    {K : Type*} [CommRing K] (L : ℕ)
    (dX₁ dY₁ dX₂ dY₂ : K[X]) : K :=
  (dX₁ * dY₂ - dX₂ * dY₁).coeff (L - 1)

/-- In coefficient coordinates, the residue form is the canonical cotangent symplectic sum after
reversing the reciprocal packet. -/
theorem criticalHorizonSymplecticPairing_eq_reversedCotangentSum
    {K : Type*} [CommRing K] (L : ℕ) (hL : 0 < L)
    (dX₁ dY₁ dX₂ dY₂ : K[X]) :
    criticalHorizonSymplecticPairing L dX₁ dY₁ dX₂ dY₂ =
      ∑ i ∈ Finset.range L,
        (dX₁.coeff i * dY₂.coeff (L - 1 - i) -
          dX₂.coeff i * dY₁.coeff (L - 1 - i)) := by
  simp only [criticalHorizonSymplecticPairing, coeff_sub, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_sub_distrib]
  have hsucc : (L - 1).succ = L := by omega
  simp only [hsucc]

/-- The tangent graph of reciprocal inversion is isotropic at every truncation depth. -/
theorem criticalReciprocalGraph_isotropic
    {K : Type*} [CommRing K] (Y dX₁ dX₂ : K[X]) (L : ℕ) :
    criticalHorizonSymplecticPairing L
        dX₁ (criticalReciprocalInfinitesimal Y dX₁)
        dX₂ (criticalReciprocalInfinitesimal Y dX₂) = 0 := by
  simp only [criticalHorizonSymplecticPairing, criticalReciprocalInfinitesimal]
  rw [show dX₁ * -(Y * Y * dX₂) - dX₂ * -(Y * Y * dX₁) = 0 by ring]
  simp

/-- Swapping the two tangent pairs negates the coefficient-residue pairing. -/
theorem criticalHorizonSymplecticPairing_swap
    {K : Type*} [CommRing K] (L : ℕ)
    (dX₁ dY₁ dX₂ dY₂ : K[X]) :
    criticalHorizonSymplecticPairing L dX₂ dY₂ dX₁ dY₁ =
      -criticalHorizonSymplecticPairing L dX₁ dY₁ dX₂ dY₂ := by
  simp only [criticalHorizonSymplecticPairing]
  rw [show dX₂ * dY₁ - dX₁ * dY₂ = -(dX₁ * dY₂ - dX₂ * dY₁) by ring]
  exact coeff_neg _ _

end GaloisForLFunctions.HTGeometry
