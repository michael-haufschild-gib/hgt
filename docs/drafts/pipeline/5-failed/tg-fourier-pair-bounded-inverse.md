# TG Fourier pairing: bounded inverse and neutral descent fail

- **ID:** TG-C8-BOUNDED-INVERSE
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Scope:** the literal even-source/Fourier pair and its ordinary Hilbert completion only.

## Killing theorem

`RHTower.primeBurnolFourierCoordinateCore_inverse_escape` proves that no
finite physical-channel inverse bound holds on any single-prime finite-depth coordinate core.
The core is dense; completed joint synthesis `S(x,y)=x+Jy` has the exact nonzero kernel
`x=-Jy`. The original neutral coordinate projection does not preserve this kernel.
Canonical section compression instead equals half the identity and has idempotence defect
minus one quarter of the identity.

## Strongest positive survivor

`PrimeBurnolFourierPair` proves actual source/Fourier independence for every finite injective
prime-depth packet and nonsingularity of its full mixed Gram. The actual Fourier transforms
have distinct rational poles, whose isolation proves the result without deleting cross terms.
`PrimeBurnolFourierCompletion` proves bounded full synthesis, exact kernel classification,
explicit section, and the full kernel/diagonal splitting of its completion.

## New insight and status

An actual noncentral Fourier channel removes the finite opposite-clock collision. The loss
reappears through the dense completed kernel, where the neutral projector fails to descend.
The next construction must retain additional source information before quotienting; merely
inverting every finite Gram or choosing the canonical section cannot provide a Hardy pair.

Both positive-survivor production leaves pass direct `lake --old env lean` audits without
warnings. All 27 public theorem axiom audits show only the standard three Lean foundations.
Paper proofs, exact scope and shared lint limitation appear on the two P3 cards. No RH result,
general Gamma-completion exclusion, or classification of every possible signed construction
is claimed. TG-C9 remains active: add the literal radial-jet output and prove its maximal-domain
kernel theorem.
