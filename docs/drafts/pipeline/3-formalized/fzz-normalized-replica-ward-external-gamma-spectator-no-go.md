# FZZ normalized replica-Ward external-Gamma spectator no-go

- **ID:** FZZ-NW1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` FZZ-P remaining source-dynamical Ward edge (map read-only)
- **Statement:** A normalized replica derivative of a factorized correlator cancels every replica-independent external Gamma factor; admissible reciprocal-Schwarz cubic rephasing leaves that Ward datum unchanged while flipping off-wall vacuum-delay saturation.

## Goal

Kill direct chain `HJ replica-area Ward derivative → external-leg Gamma momentum delay → FZZ divisor passivity → RH`. Exact survivor must introduce mixed replica–momentum coupling and a source-fixed phase frame.

## Gates

- [x] 0 → 1 in-progress: corpus and primary-source factorization audited; exact route class frozen
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `fzzHJNormalizedReplicaWardExternalGammaSpectatorRouteKilled`; targeted build `13154/13154`; standard axioms only
- [ ] 3 → 4 publication-ready: standalone paper

## Approach

For `A(δ,P)=G(P)C(δ,P)`, prove `(∂δA)/A=(∂δC)/C`. Define an entire nonzero normalization `H_c(s)=exp(-c(s-1/2)^3)`: Schwarz-compatible, reciprocal under `s↦1-s`, centered, and unit-modulus on `Re s=1/2`. On `s=1/2+iP` it adds `cP^3` to phase and `3cP^2` to delay. At every `P≠0`, one `c` forces vacuum-delay saturation while `c=0` does not. Therefore no predicate of normalized replica-Ward data characterizes saturation uniformly over the allowed normalization orbit.

## Proof

**[PROVED HERE]** Let `W_G(P)=(G(P)D(P))/(G(P)C(P))`, where `D(P)=∂δC(0,P)`. If `G(P)C(P)≠0`, field cancellation gives `W_G(P)=D(P)/C(P)`; hence the full profile `W_G` is unchanged by any nonzero external rephasing.

For real `c`, `H_c` is entire and nonzero. Real coefficients give `conj(H_c(s))=H_c(conj(s))`; oddness of the centered cube gives `H_c(1-s)H_c(s)=1`; `H_c(1/2)=1`; and `H_c(1/2+iP)=exp(icP^3)`, so its critical-line norm is one. Thus these gauges preserve Schwarz structure, reciprocal reflection, center normalization, and continuum modulus.

Writing the canonical physical phase as `Φ(P)` and delay as `DΓ(P)=Φ′(P)`, the gauged phase is `Φ_c(P)=Φ(P)+cP^3`, so `DΓ,c(P)=DΓ(P)+3cP²` and `DΓ,c(0)=DΓ(0)`. Corpus strict delay rigidity gives `DΓ(P)>DΓ(0)` for `P≠0`. But

`c_P=(DΓ(0)-DΓ(P))/(3P²)`

makes `DΓ,c_P(P)=DΓ,c_P(0)`. Therefore canonical and `c_P` frames have identical complete normalized replica-Ward profiles but opposite saturation truth values at `P`. No predicate of that profile can characterize saturation uniformly over this admissible normalization orbit. QED.

Primary-source scope: Halder--Jafferis (arXiv:2402.00932v3), (3.33), differentiates only the replica-deformed winding operators, while (4.1)--(4.2) place the Gamma factors on external vertices in a factorized correlator. Jafferis--Schneider (arXiv:2004.05223), (1.1), (3.18)--(3.20), explicitly states the scattering-operator normalization is noncanonical and the reflection coefficient normalizes the two-point function.

## No-go closure

- **Exact killing theorem/mechanism:** normalized replica differentiation cancels replica-independent external factors; admissible cubic phase gauge flips delay saturation.
- **Strongest positive survivor:** mixed `∂P∂δ` correlator or asymptotically framed relative phase.
- **New insight:** source Ward data must break spectator factorization or fix an asymptotic phase frame before external-Gamma delay can carry RH information.
- **Status:** Lean formalized in `FZZCigarParityExternalBRSTNormalizedReplicaWardSpectatorNoGo.lean`; direct check and targeted build pass; `propext`, `Classical.choice`, `Quot.sound` only; umbrella wired.

## Log

- 2026-09-02 — created directly in 1-in-progress after corpus/literature audit.
- 2026-09-02 — paper proof closed; conjecture FZZ-NW1 proved.
- 2026-09-02 — Lean formalization and targeted audit complete; promoted to `3-formalized`.
