# Fractional-ideal theta inversion with arithmetic normalization

- **ID:** hecke-fractional-ideal-theta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke L-functions HL7; actual arithmetic Gaussian theta series
- **Statement:** For every nonzero fractional ideal `I` and positive real `t`, the sum
  `θ_I(t) = Σ_(a∈I) exp(-πt ‖S(ι(a))‖²)` is summable and satisfies
  `θ_I(t) = (absNorm(I) sqrt(abs(discr K)))⁻¹ t^(-[K:ℚ]/2) θ_(dual I)(1/t)`.

## Source and dependency audit

Corpus search finds arbitrary-lattice theta inversion and the newly formalized arithmetic
dual/covolume modules, but no existing theorem summing over actual fractional-ideal
elements. Reuse `NumberFieldIdealTraceDuality`, `NumberFieldIdealCovolume`, and the
[intrinsic-lattice theta bridge](gaussian-poisson-sums-over-intrinsic-dual-lattices.md).

## Proof

The weighted mixed embedding is injective and identifies the ideal subtype with its
actual coordinate lattice. The arithmetic dual-membership theorem similarly identifies
the trace-dual ideal subtype with the intrinsic integer dual, using conjugated embeddings.
Conjugation preserves the weighted Euclidean norm: apply the weighted trace-pairing
identity to `(z, conjugate z)` and `(conjugate z, z)`, then commute the product.

Reindex the ideal's actual real basis to the mixed coordinate index and apply intrinsic
lattice theta inversion. The exact covolume theorem supplies the norm/discriminant
factor. Mathlib `mixedEmbedding.finrank` identifies mixed-space real dimension with
the field degree; transport it through weighted coordinates. Transport both Gaussian summability and the theta sums through
the actual embedding equivalences. No analytic continuation or Hecke-character input
is assumed.

## Lean declarations and validation

In [NumberFieldIdealTheta.lean](../../../../formal/GaloisForLFunctions/HTGeometry/NumberFieldIdealTheta.lean),
namespace `GaloisForLFunctions.HTGeometry`:

- `numberFieldIdealLatticeEquiv`, `numberFieldDualIdealLatticeEquiv`
- `norm_sq_traceCoordinates_conjugation`, `numberFieldTraceCoordinates_finrank`
- `numberFieldIdealTheta`, `numberFieldIdealTheta_eq_intrinsic`
- `intrinsicLatticeTheta_dual_eq_idealTheta`
- `summable_numberFieldIdealTheta`, `numberFieldIdealTheta_inversion`

The complete scratch and final direct `lake --old env lean` source audit pass without
warnings. Summability and the final arithmetic theta inversion audit to only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into `HTGeometry.lean`;
no umbrella was compiled. No limit overrides or analytic premises were added.
Its olean is built for the written archimedean-theta consumer.

- [x] Exact target and corpus audit.
- [x] Lean implementation, direct source audit, transitive axiom audit.

Next is the [archimedean place-parameter family](ideal-theta-under-archimedean-place-scaling.md).
This completed result is the unweighted ideal theta identity. Finite characters,
real parity factors, unit integration, and the Hecke Mellin transform remain open.
