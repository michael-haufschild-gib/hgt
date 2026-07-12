import GaloisForLFunctions.RHTower.PrimeDyadicWeyl
import GaloisForLFunctions.RHTower.CutoffCochain

/-!
# The cutoff boundary of a Weyl relation

For an idempotent cutoff `e`, compression is not multiplicative.  Applying the existing
Toeplitz--Hankel semicommutator identity to a global Weyl pair `UV = ζ VU` gives the exact finite
descent defect:

`(eUe)(eVe) - ζ(eVe)(eUe)`

is the difference of the two products of opposite cutoff corners.  Therefore the compressed pair
retains the Weyl relation exactly when those boundary products balance.

This is the positive successor to the pinned-centre no-go in `PrimeDyadicWeyl`: a nonzero spectral
translation cannot act on one pinned germ, but its compression carries a precise boundary inflow
whose cancellation is the remaining source theorem.
-/

namespace RHTower

open Matrix

/-- **Cutoff Weyl boundary identity.**  The failure of a global Weyl relation to survive
compression is exactly the imbalance of its two opposite corner products. -/
theorem compression_weylBoundary {n : Type*} [Fintype n] [DecidableEq n]
    (e U V : Matrix n n ℂ) (he : IsIdempotentElem e) (ζ : ℂ)
    (hweyl : U * V = ζ • (V * U)) :
    compression e U * compression e V - ζ • (compression e V * compression e U) =
      ζ • (upperBoundary e V * crossBoundary e U) -
        upperBoundary e U * crossBoundary e V := by
  have hcomp : compression e (U * V) = ζ • compression e (V * U) := by
    rw [hweyl]
    simp [compression]
  rw [compression_mul he U V, compression_mul he V U] at hcomp
  rw [smul_add] at hcomp
  rw [sub_eq_sub_iff_add_eq_add]
  simpa [add_comm] using hcomp

/-- **Boundary-balance descent criterion.**  If the opposite corner products balance with the
global Weyl phase, the compressed pair obeys the same Weyl relation exactly. -/
theorem compression_weylRelation_of_boundaryBalance
    {n : Type*} [Fintype n] [DecidableEq n]
    (e U V : Matrix n n ℂ) (he : IsIdempotentElem e) (ζ : ℂ)
    (hweyl : U * V = ζ • (V * U))
    (hbalance : ζ • (upperBoundary e V * crossBoundary e U) =
      upperBoundary e U * crossBoundary e V) :
    compression e U * compression e V = ζ • (compression e V * compression e U) := by
  have h := compression_weylBoundary e U V he ζ hweyl
  rw [hbalance, sub_self] at h
  exact sub_eq_zero.mp h

/-- If one member of the Weyl pair commutes with the cutoff, both of its directed corners vanish,
so the compressed pair retains the Weyl relation automatically.  For the physical aperture cutoff,
this applies to the Euler multiplication operator; the remaining obstruction is invertibility of
the compressed translation, not the projective relation. -/
theorem compression_weylRelation_of_left_commutes_cutoff
    {n : Type*} [Fintype n] [DecidableEq n]
    (e U V : Matrix n n ℂ) (he : IsIdempotentElem e) (ζ : ℂ)
    (hweyl : U * V = ζ • (V * U)) (hcomm : U * e = e * U) :
    compression e U * compression e V = ζ • (compression e V * compression e U) := by
  apply compression_weylRelation_of_boundaryBalance e U V he ζ hweyl
  rw [crossBoundary_eq_zero_of_commute he hcomm,
    upperBoundary_eq_zero_of_commute he hcomm, Matrix.mul_zero, Matrix.zero_mul, smul_zero]

/-- Equivalently, a nonzero compressed Weyl defect certifies failure of the boundary-balance law. -/
theorem not_boundaryBalance_of_compression_weylDefect_ne_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (e U V : Matrix n n ℂ) (he : IsIdempotentElem e) (ζ : ℂ)
    (hweyl : U * V = ζ • (V * U))
    (hdefect : compression e U * compression e V -
      ζ • (compression e V * compression e U) ≠ 0) :
    ζ • (upperBoundary e V * crossBoundary e U) ≠
      upperBoundary e U * crossBoundary e V := by
  intro hbalance
  exact hdefect (sub_eq_zero.mpr
    (compression_weylRelation_of_boundaryBalance e U V he ζ hweyl hbalance))

end RHTower
