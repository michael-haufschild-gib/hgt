# Signed atomic Euler correction cannot repair Gaussian surgery

- **ID:** euler-fe-signed-atomic-gaussian-repair.
- **Stage:** 3-formalized.
- **Type:** INFINITE SIGNED SOURCE RIGIDITY.
- **Source:** Full causal Gaussian reconstruction and the signed Euler/Möbius class.

## Exact statement

Let `A,B` be positive causal measures on a common countable carrier, and `K,H`
positive absolutely continuous causal measures. All four have finite mass
against `w(t)=exp(t/2−exp(2t)+1)`. Normalize `A{0}=B{0}+1`. Put

    μ=A+A*K+B*H,   ν=B+A*H+B*K.

For `ψ(x)=exp(x/2−πexp(2x))` and `L=∂x−(1/2−2πexp(2x))`, equality of
`L T_μψ` and `L T_νψ` on any interval `(a,b)` with `πexp(2a)>1` forces

    A=B+δ₀,   K=H.

Thus the normalized signed atomic operator `A−B` is the identity and the
continuous surgery `K−H` vanishes. Positive and negative sources may have
infinitely many atoms and infinite undamped mass.

## Proof and positive survivor

Full local reconstruction and source separation give
`A|(0,∞)=B|(0,∞)` and `A*K+B*H=A*H+B*K`. Decompose each causal atomic source
into its positive-ray restriction and its zero atom. Normalization yields
`A=B+δ₀`. Distributing convolution leaves `B*K+B*H` as a common summand.

For any common measure `C` with `∫w dC<∞`, multiplication by `w` turns
`C+K=C+H` into an equality with finite common measure `wC`. Cancel there,
then remove `w` using its measurable positive inverse. This proves `K=H`
without assuming finite undamped mass. Convolution admission is supplied by
`w(t+u)≤w(t)w(u)`.

The positive survivor is faithful local reconstruction of the full source,
its convolution domain, and weighted cancellation. These are proved laws,
not additional analytic premises of the repair exclusion.

## Lean and scope

Module: `EulerFETransportTheory/SignedEulerCorrectionCannotRepairGaussianSurgery.lean`.
Namespace: `GaloisForLFunctions.EulerFETransportTheory`.

- `cancel_gaussianWeighted_common_measure`.
- `signed_atomic_convolution_repair_is_trivial`.

Direct `lake --old env lean` check passes. Both transitive audits use only
`propext`, `Classical.choice` and `Quot.sound`.

The corpus's `ThetaChronologicalSingularDeconvolution.lean` gives global
convolution injectivity for a fixed cutoff kernel and finite signed measures.
The present result uses local Gaussian differential data, permits infinite
undamped mass and separates the atomic operator from continuous surgery.
It does not prove height replication, `LinAt C`, or AAL for the original ζ.
