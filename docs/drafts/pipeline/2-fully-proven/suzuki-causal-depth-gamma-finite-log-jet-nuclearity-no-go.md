# Suzuki causal-depth Gamma finite-log-jet nuclearity no-go

- **ID:** CCM-FU-C29
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `irregular-stokes-robin-gamma-holonomy-coercivity.md` C1--C28
- **Statement:** Every fixed logarithmic Wigner--Smith/Robin jet of the actual causal-depth Gamma feature is nuclear and cannot yield a lower-semibounded rectangular Ward defect through a uniformly bounded response.

## Goal

Kill the literal finite-order unbounded-generator escape left by C28. This is upstream of RH: it
uses only source weights, the exact prime-power Weyl charge, and trace duality.

## Gates

- [x] 0 → 1: exact source-pure claim and RH chain fixed
- [x] 1 → 2: dependency-closed paper proof and hostile audit
- [x] 2 → 3: exact Lean theorem and targeted audit
- [ ] 3 → 4: publication-ready

## Exact claim and proof

For `q_(p,e)=p^(e+1)` and fixed `k≥0`, scale the `(p,e)` source column of the actual feature `F`
by `(log q_(p,e))^k`; call the resulting operator `F_k`.

The corpus gives

`weight(p,e)=A_p r_p^e`, `A_p ≤ C(1+log p)p^(-5/4)`, and `0<r_p≤r<1`.

Moreover `log q_(p,e)=(e+1)log p`. Hence

`(log q_(p,e))^k weight(p,e)`

is dominated by the product of

`C (log p)^k(1+log p)p^(-5/4)` and `(e+1)^k r^e`.

The prime factor is summable because every fixed logarithmic power is absorbed by exponent
`5/4>1`; the depth factor is a polynomial times a geometric series. Tonelli gives joint `ℓ¹`.
The unscaled feature-column norm is at most `weight(p,e)`, so the scaled column norms are jointly
summable. Their canonical rank-one expansion is therefore nuclear, proving `F_k∈S¹`.

For any response family `R_N` with one operator-norm ceiling,

`|Re Tr(F_k R_N†)| ≤ ‖F_k‖₁ sup_N ‖R_N‖ = O(1)`.

Thus this correction is `o(N)`. The corpus theorem
`no_sublinear_transitionCore_rectangularWardProducer` excludes eventual lower semiboundedness of
the rectangular Ward defect.

## Source fidelity and hostile audit

The multiplier is the exact source charge: the corpus Weyl relation gives Wigner--Smith value
`log(p^(e+1))`. C28 alone does not imply the theorem because trace ideals are not stable under an
arbitrary unbounded multiplier; the new input is the all-log-moment source decay above.

Fixed `k` is essential. The argument does not cover cutoff-growing jet order, super-polynomial or
singular functional calculus, norm-growing response, or a non-nuclear moving source. Suzuki's 2026
screw-function operator framework and the standard Wigner--Smith literature do not state this
source-specific nuclearity/no-go. Abstract polynomial-geometric summability and trace duality are
classical; novelty claim is only the exact CCM-FU producer-class kill.

## RH-chain consequence

`finite-order source Weyl/Robin jet → F_k∈S¹ → bounded response correction O(1) → sublinear →`
`no_sublinear_transitionCore_rectangularWardProducer`.

Survivor: cutoff-growing order, genuinely singular functional calculus, norm/graph-weak blow-up,
or a moving source that loses `S¹` after source weighting.

## Lean realization

Module `GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaFiniteLogJetRobinTraceNoGo` proves exact
source-column scaling, fixed-log-moment `ℓ¹` summability, `F_k∈S¹`, bounded-response sublinearity,
and `no_suzukiCausalDepthGammaFixedLogJetWardProducer`.
