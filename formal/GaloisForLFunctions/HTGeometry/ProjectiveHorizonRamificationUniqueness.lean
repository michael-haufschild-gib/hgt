import GaloisForLFunctions.HTGeometry.ProjectiveHorizonExactLagrangian

/-!
# Uniqueness of a ramified state from its conormal displacement

At a critical raw/reciprocal horizon, the residue symplectic form identifies the branch conormal
with a low tangent pair `(U,V)`.  If two inverse states with the same marked reciprocal tail had
the same conormal, their difference is a syzygy multiple `(C*U,-C*V)` after removing the common
factor of the two tangent components.

This file proves the decisive algebraic rigidity step: such a nonzero displacement is impossible.
The two inverse identities and the common tangent identity would make
`(C*U) * (Y + Y')` vanish through order `m+n-1`, while its two factors have a surviving coefficient
strictly below that order.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Residue pairing of a low tangent pair with a raw/reciprocal tail variation.  On the Lagrangian
inversion graph this is the branch conormal. -/
noncomputable def criticalHorizonConormalPairing {K : Type*} [CommRing K]
    (N : ℕ) (U V dP dQ : K[X]) : K :=
  (U * dQ - dP * V).coeff N

/-- The branch conormal is literally the ambient coefficient-residue symplectic pairing between
the vertical kernel tangent and a tail variation. -/
theorem criticalHorizonConormalPairing_eq_symplecticPairing
    {K : Type*} [CommRing K] (N : ℕ) (U V dP dQ : K[X]) :
    criticalHorizonConormalPairing N U V dP dQ =
      criticalHorizonSymplecticPairing (N + 1) U V dP dQ := by
  simp [criticalHorizonConormalPairing, criticalHorizonSymplecticPairing]

/-- A reciprocal-tail monomial reads one raw tangent coefficient exactly. -/
theorem criticalHorizonConormalPairing_reciprocalBasis
    {K : Type*} [CommRing K] (N i : ℕ) (hi : i ≤ N) (U V : K[X]) :
    criticalHorizonConormalPairing N U V 0 (X ^ (N - i)) = U.coeff i := by
  simp only [criticalHorizonConormalPairing, zero_mul, sub_zero, coeff_mul_X_pow']
  rw [if_pos (Nat.sub_le N i)]
  congr 1
  omega

/-- A raw-tail monomial reads the negative of one reciprocal tangent coefficient exactly. -/
theorem criticalHorizonConormalPairing_rawBasis
    {K : Type*} [CommRing K] (N j : ℕ) (hj : j ≤ N) (U V : K[X]) :
    criticalHorizonConormalPairing N U V (X ^ (N - j)) 0 = -V.coeff j := by
  simp only [criticalHorizonConormalPairing, mul_zero, zero_sub, coeff_neg, coeff_X_pow_mul']
  rw [if_pos (Nat.sub_le N j)]
  congr 2
  omega

/-- Two compatible inverse states with the same nonzero first reciprocal-tail coefficient cannot
differ by opposite multiples of one common tangent pair.  This is the algebraic core of generic
injectivity from the ramification divisor to the branch divisor. -/
theorem criticalHorizon_sharedConormal_displacement_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {m n : ℕ} {Xj Y U V C : K[X]}
    (hU : U ≠ 0) (hCUdeg : (C * U).natDegree < m)
    (hYn : Y.coeff n ≠ 0)
    (hSameTail : (Y - C * V).coeff n = Y.coeff n)
    (hInv : X ^ (m + n) ∣ Xj * Y - 1)
    (hInv' : X ^ (m + n) ∣ (Xj + C * U) * (Y - C * V) - 1)
    (hTang : X ^ (m + n) ∣ U * Y + Xj * V) :
    C = 0 := by
  by_contra hC
  have hCU : C * U ≠ 0 := mul_ne_zero hC hU
  have hYsumCoeff : (Y + (Y - C * V)).coeff n ≠ 0 := by
    rw [coeff_add, hSameTail]
    simpa [two_mul] using mul_ne_zero (show (2 : K) ≠ 0 by norm_num) hYn
  have hYsum : Y + (Y - C * V) ≠ 0 := by
    intro hzero
    rw [hzero, coeff_zero] at hYsumCoeff
    exact hYsumCoeff rfl
  have hDiff : X ^ (m + n) ∣
      ((Xj + C * U) * (Y - C * V) - 1) - (Xj * Y - 1) :=
    dvd_sub hInv' hInv
  have hCTang : X ^ (m + n) ∣ C * (U * Y + Xj * V) := by
    obtain ⟨q, hq⟩ := hTang
    refine ⟨C * q, ?_⟩
    rw [hq]
    ring
  have hProduct : X ^ (m + n) ∣ (C * U) * (Y + (Y - C * V)) := by
    rw [show (C * U) * (Y + (Y - C * V)) =
        (((Xj + C * U) * (Y - C * V) - 1) - (Xj * Y - 1)) +
          C * (U * Y + Xj * V) by ring]
    exact dvd_add hDiff hCTang
  apply not_all_low_mul_coeff_zero hCU hYsum hCUdeg hYsumCoeff
  intro k hk
  exact (X_pow_dvd_iff.mp hProduct) k hk

end GaloisForLFunctions.HTGeometry
