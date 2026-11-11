# Exterior coercivity on the cubic quotient

- **ID:** cubic-quotient-exterior-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [cubic theta residue](cubic-theta-residue-and-gauss-coefficients.md)
- **Statement:** There are a compact quotient set `K` and `C≥0` such that every actual completed energy vector satisfies `‖Mu‖₂²≤‖Gu‖₂²+C‖1_KMu‖₂²`. The restriction map `u↦1_KMu` is compact.

`M` is the actual mass embedding and `G` the completed hyperbolic gradient.

The [invariant barrier](cubic-invariant-cusp-barrier.md) satisfies `φ≥1`
and `Δφ=Vφ`, with continuous `V≥1−C1_K` for a compact `K`.
For a compact smooth test `f`, choose a compact smooth cutoff `χ=1`
near its support and test the equation for `χφ` against `|f|²/φ`.
The test has support inside that of `f`. The support-local
[Green identity](cubic-quotient-green-identity.md) therefore gives
`∫V|f|²=Re E(χφ,|f|²/φ)`.

The pointwise identity
`|df|²−dφ·d(|f|²/φ)=|df−f·dφ/φ|²≥0`
bounds the pairing by `E(f)`. Integration yields `∫V|f|²≤E(f)`.
The potential lower bound gives the stated mass estimate on compact
smooth tests. Both sides are continuous on the completed energy graph,
so density extends it to every energy vector. The actual
[compact restriction theorem](cubic-kernel-local-sobolev-compactness.md)
supplies compactness of the error map.

Lean: `MetaplecticMobiusDescent/TheCubicExteriorCoercivity.lean`,
namespace `CubicEisenstein`:

- `kernel_actual_barrier_ground_state`.
- `kernel_global_exterior_coercivity`.

Both endpoints discharge the barrier equation and ground-state input;
no analytic hypothesis remains. Direct source and transitive audits use only `propext`,
`Classical.choice`, and `Quot.sound`.
Spectral continuation, nonzero theta residue, and arithmetic descent
remain on the parent cards.

Adapted from OpenAI `CubicSieve/CutoffOrders.lean`, using locally checked
barrier geometry, coordinate calculus, Green identities, and compact
restriction.
