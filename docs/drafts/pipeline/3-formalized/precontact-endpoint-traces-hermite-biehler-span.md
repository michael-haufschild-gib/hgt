# The endpoint traces lie in the Hermite–Biehler span

- **ID:** precontact-endpoint-traces-hermite-biehler-span
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ35; Σ75.
- **Statement:** Each actual normalized endpoint trace is an explicit linear combination of the two anchored Hermite–Biehler coordinates, at every complex parameter.

## Exact identity

For either actual trace `τ`, put `q=K_a(i,i)=‖E_i‖²`. Then

`2i q τ(z)=E_a(conj z)τ(−i)−conj(E_a(z))τ(i)`.

Both anchor traces `τ_L(i), τ_R(i)` are real. Reflection exchanges their
values at `−i`.

## Proof

The canonical continuous physical Riesz source `S_z` has Fourier transform
`K_a(z,·)`. Form `P_κ,z=q_κ S_z−K_a(z,κ)S_κ`. The unitary zero-moving
identity for projected evaluation vectors gives the Fourier relation
between `conj(z−conj κ)P_κ,z` and `conj(z−κ)P_conj κ,z`.

Compact Fourier uniqueness identifies the second source with the explicit
zero flip of the first. Their difference is a compact primitive correction,
differentiable and zero at both endpoints. Its normalized trace vanishes
because `t sqrt(log(1/t))→0`. Taking either actual trace and setting `κ=i`
gives the displayed identity, including both anchors. Reflection and
conjugation make the anchor values real.

## Formal results

Module `CanonicalSystemOfTheWindowTower/TheEndpointTracesLieInTheHermiteBiehlerSpan`,
namespace `WeilHilbertBeforeContact`, wired into the programme umbrella:

- `paperFT_evalVectorContinuousRepresentative`
- `evalVectorLeftTrace_hermiteBiehler_span`
- `evalVectorRightTrace_hermiteBiehler_span`
- `evalVectorLeftTrace_I_im`
- `evalVectorRightTrace_I_im`

Final `lake --old env lean` source audit passed. All five transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The canonical differential equation and contact-uniform arithmetic control
are separate obligations.
