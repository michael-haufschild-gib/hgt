# Signed reciprocal tails and scale contraction

- **ID:** vaughan-tail-scale-contraction
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** q-i-selective-square-root-band.md
- **Statement:** Test whether ordinary-integer incidence supplies a scale-composition inequality for the actual signed reciprocal-tail envelope, strong enough to upgrade its proved vanishing to a power rate.

## Existing foothold

For fixed `0<ε<1/2`, let `F(N)=ρ-A_N` and
`r(N)=sup_(n≥N)|n^ε F(n)|`, with `N≥1`. The scaled signed-tail theorem on the
product-horizon card gives a finite, nonnegative, decreasing envelope with `r(N)→0`.
A power rate for this envelope is equivalent to the fixed-strip target by the
dependency-closed Abel inversion on the centered-empty-leg card.

## Concrete conjecture to audit

Does some source-defined composition law imply

`r(MN) ≤ C r(M) r(N)` for all sufficiently large `M,N`,

with a fixed finite `C`? Such a law would supply the missing power rate: choose a fixed
`q` with `C r(q)<1`, iterate at `q^k`, and use monotonicity between powers of `q`.
The existing little-o estimate alone does not imply this inequality.

No composition law is currently proved. Möbius multiplicativity applies to coprime
factors, whereas the envelope ranges over additive cutoffs. The missing step is exact
control of the overlap and remainder terms in a composition. A finite-dimensional
leading Gram limit is not a closed transport law and must not be treated as one.

## Further moving-cutoff question

The product-horizon theorem now only requires `UV→∞`, with positive cutoffs.
It holds uniformly over every factorization, including a fixed smaller cutoff.
The complete Lean proof is recorded in
`../3-formalized/uniform-product-horizon-vaughan-second-scale.md`:
the truncated Möbius patterns have a common mean-zero partial-sum modulus, and the
existing quantitative prefix proof is uniform in that modulus. The scale-composition
conjecture remains open; the uniform little-o theorem supplies no power rate by itself.

## Status

Initial corpus search found window/receiver equivalences, but no applicable
submultiplicative source estimate. Search the exact cofactor-transport and composition
obstructions before committing to this route. No mathematical input is assumed, no
negative result is claimed, and no Lean theorem is drafted for the conjectured law.

A frontier refresh found no producer for a fixed strip. The apparent uniform-strip
theorem `exists_zeta_uniform_strip_zero_free` has width `log(K)^(-2)` up to height
`K`; the detector zero-count truncation uses the same shrinking width.
`mobiusSchurTransfer` is contractive only on its stated absolutely convergent shifted
half-plane, while `mobiusSquarefreeShiftContraction` supplies a non-expansive norm bound.
The distinct divisor-resolved channel in `MobiusChannelCriticalMassEscape` does have
the strict norm factor `ζ(2σ)^(-1/2)`, but maps into a channel space whose mass escapes
every fixed finite window. None of these read source statements supplies an iterable
self-map of the actual signed reciprocal-tail envelope. The missing transport or
synthesis estimate must be proved before a channel contraction can be used here.

The exact fresh-prime identity
`mobiusDivisorOrientedFibre_insert_mul_prime_renormalization` reads the processed
coordinate at `pN` as its unprocessed background minus `sqrt(p)` times the old
coordinate at `N`. Its squared identity retains the complete cross-scale product;
it provides no upper bound for that product. The source theorem
`exists_powerMesh_dilationTailAbsoluteMass_lower` also shows that deleting a
sublinear dilation head preserves the absolute tail mass scale `M sqrt(M)`.
These statements identify the missing signed estimate but do not give the proposed
composition law for `r`.

The read `ComplementarySectorPropagationAndAffineContraction` gives a strict
factor `2^(1-4β)` for square-cutoff transport when `1/4<β<ε`. Its controlled
quantity is the difference between cutoff approximants on their common head.
The full-stage recurrence remains an explicit premise; the source proves it
equivalent to receiver admission in `complementarySector_propagation_tfae`.
Its produced compensated-head recurrence assumes `ε>1/2` and
`ε>Θ-1/2`. The introductory `1/4` threshold was inaccurate and is corrected
to the actual theorem's `1/2`. Thus this contraction does not yet produce an
iterable bound for the signed tail or receiver below half damping.
