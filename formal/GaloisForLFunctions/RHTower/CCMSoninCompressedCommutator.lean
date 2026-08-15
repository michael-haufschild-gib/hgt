import Mathlib

/-!
# The projection-compressed degree-one commutator identity

The Sonin three-grade carrier needs the exact split of a compressed commutator into an internal
commutator plus the polarized leakage cross.  For a projection `Q`, a self-adjoint `X` and a
skew-adjoint `Z`, with the leakages

```text
L_X = (1−Q) X Q ,      L_Z = (1−Q) Z Q ,
```

one has exactly

```text
Q [X, Z] Q = [QXQ, QZQ] + L_X^* L_Z + L_Z^* L_X ,
```

which is equation `(9c)` of the card.  The proof is purely algebraic: inserting `Q + (1−Q)` in the
middle of each product splits it into the internal term and the leakage term, and the adjoint of
each leakage is computed from the symmetry of `Q`, `X` and `Z`.

Everything here is stated in an arbitrary `*`-ring, so it applies verbatim to bounded operators on
the Sonin carrier.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {R : Type*} [Ring R] [StarRing R]

omit [StarRing R] in
/-- A projection idempotent has an idempotent complement. -/
theorem one_sub_mul_one_sub {Q : R} (hQ : Q * Q = Q) : (1 - Q) * (1 - Q) = 1 - Q := by
  have hexp : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
  rw [hexp, hQ]
  noncomm_ring

omit [StarRing R] in
/-- **Equation (9b)–(9c), splitting step.**  Inserting the resolution of the identity splits a
compressed product into its internal part and its leakage part. -/
theorem compress_split {Q : R} (hQ : Q * Q = Q) (X Z : R) :
    Q * X * Z * Q = (Q * X * Q) * (Q * Z * Q) + (Q * X * (1 - Q)) * ((1 - Q) * Z * Q) := by
  have h1 : (Q * X * Q) * (Q * Z * Q) = Q * X * (Q * Q) * Z * Q := by noncomm_ring
  have h2 : (Q * X * (1 - Q)) * ((1 - Q) * Z * Q) = Q * X * ((1 - Q) * (1 - Q)) * Z * Q := by
    noncomm_ring
  rw [h1, h2, hQ, one_sub_mul_one_sub hQ]
  noncomm_ring

/-- The adjoint of the self-adjoint leakage. -/
theorem star_leakage_selfAdjoint {Q X : R} (hQs : star Q = Q) (hX : star X = X) :
    star ((1 - Q) * X * Q) = Q * X * (1 - Q) := by
  rw [star_mul, star_mul, hQs, hX, star_sub, star_one, hQs]
  noncomm_ring

/-- The adjoint of the skew-adjoint leakage. -/
theorem star_leakage_skewAdjoint {Q Z : R} (hQs : star Q = Q) (hZ : star Z = -Z) :
    star ((1 - Q) * Z * Q) = -(Q * Z * (1 - Q)) := by
  rw [star_mul, star_mul, hQs, hZ, star_sub, star_one, hQs]
  noncomm_ring

/-- **Equation (9c).**  The compressed degree-one commutator splits into the internal commutator
plus the polarized leakage cross. -/
theorem compressed_commutator_split {Q X Z : R} (hQ : Q * Q = Q) (hQs : star Q = Q)
    (hX : star X = X) (hZ : star Z = -Z) :
    Q * (X * Z - Z * X) * Q
      = ((Q * X * Q) * (Q * Z * Q) - (Q * Z * Q) * (Q * X * Q))
        + (star ((1 - Q) * X * Q) * ((1 - Q) * Z * Q)
          + star ((1 - Q) * Z * Q) * ((1 - Q) * X * Q)) := by
  have hXZ := compress_split hQ X Z
  have hZX := compress_split hQ Z X
  rw [star_leakage_selfAdjoint hQs hX, star_leakage_skewAdjoint hQs hZ]
  have hsplit : Q * (X * Z - Z * X) * Q = Q * X * Z * Q - Q * Z * X * Q := by noncomm_ring
  rw [hsplit, hXZ, hZX]
  noncomm_ring

/-- **Equation (9d).**  With a trace `τ` the degree-one term splits into the internal trace defect
and the leakage pairing. -/
theorem degree_one_trace_split {Q X Z : R} (tau : R → ℂ)
    (htau : ∀ u v : R, tau (u + v) = tau u + tau v)
    (hQ : Q * Q = Q) (hQs : star Q = Q) (hX : star X = X) (hZ : star Z = -Z) :
    tau (Q * (X * Z - Z * X) * Q)
      = tau ((Q * X * Q) * (Q * Z * Q) - (Q * Z * Q) * (Q * X * Q))
        + tau (star ((1 - Q) * X * Q) * ((1 - Q) * Z * Q)
          + star ((1 - Q) * Z * Q) * ((1 - Q) * X * Q)) := by
  rw [compressed_commutator_split hQ hQs hX hZ, htau]

end GaloisForLFunctions.RHTower

end
