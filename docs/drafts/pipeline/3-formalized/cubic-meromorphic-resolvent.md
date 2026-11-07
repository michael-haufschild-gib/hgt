# Meromorphic cubic resolvent

- **ID:** cubic-meromorphic-resolvent
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](../1-in-progress/cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** The actual quotient Laplacian has an operator-valued meromorphic resolvent near `z=8/9`; composition with `z=s(2−s)` is meromorphic at `s=4/3`.

Let `T(z)=Id−(z+1)M*M`, and let `P` project onto `ker T(8/9)`.
The [Fredholm theorem](cubic-spectral-pencil-fredholm.md)
makes this kernel finite-dimensional and identifies the range with its
orthogonal complement. On the kernel, `M*M=9/17`, so
`T(z)=(8/9−z)9/17`. The Gram operator preserves the complement, where
`T(8/9)` is bijective. Its inverse is analytic near `8/9`.

Consequently the energy inverse is
`(17/9)/(8/9−z) P + T(z)|_(ker P)⁻¹(1−P)`.
Sandwiching by `M` and `M*` gives the actual `L²` resolvent, with singular
part `(17/9)/(8/9−z) MPM*`. The variational equation proves both inverse
identities on the actual Laplacian domain. Self-adjointness gives
invertibility for nonreal `z`. The polynomial `s(2−s)` takes `4/3` to
`8/9`; its other preimage, `2/3`, is excluded from a small neighborhood.

Lean: `MetaplecticMobiusDescent/TheCubicMeromorphicResolvent.lean`,
namespace `CubicEisenstein`: `kernelSpectralResolvent_meromorphicAt`,
`kernelSpectralResolvent_graph`, `kernelEisensteinResolvent_meromorphicAt`,
and `kernelEisensteinPencil_eventually_isUnit`.

Direct source and transitive audits use only `propext`, `Classical.choice`,
and `Quot.sound`.

This constructs a possible finite-rank pole; it does not prove `P≠0`
or match the original Eisenstein series. Adapted from OpenAI's
`Eisenstein/MeromorphicResolvent.lean` using the locally checked quotient,
energy graph, Fredholm estimate, and Laplacian.
