# No Finite Boundary Audit Under Amplification

- **ID:** no-finite-boundary-audit-under-amplification
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/consolidated/gpt/proof-route.md, source-built `kappa_-` boundary-extension layer
- **Statement:** A finite-scale boundary audit cannot certify `kappa_-=0` for a scale-dependent boundary extension unless a source theorem supplies a uniform amplification bound or a scale-independent PSD boundary Weyl inequality.

## Goal

Strengthen the finite-rank boundary Schur reduction. The static reduction says boundary data determine inertia at a fixed scale. This card records the scale-dependent obstruction: a boundary channel can be harmless at every checked scale and still cross the negative-inertia threshold later.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let `B=I` on a Hilbert space and let `v` be a unit vector. Consider the one-channel boundary family

```text
H(t) = I - alpha(t) v v^*
```

with

```text
alpha(t)=epsilon exp(kappa t),   epsilon>0, kappa>0.
```

On `v^perp`, `H(t)` is the identity. On `span(v)`, its eigenvalue is

```text
1 - epsilon exp(kappa t).
```

Therefore

```text
neg H(t) = 0  iff  epsilon exp(kappa t) <= 1,
neg H(t) = 1  iff  epsilon exp(kappa t) > 1.
```

The crossing time is

```text
t_* = (log(1/epsilon))/kappa.
```

Given any finite audit scale `T`, choose for example

```text
epsilon = exp(-kappa (T+1)).
```

Then `neg H(t)=0` for every `0<=t<=T`, but `neg H(T+1+delta)=1` for every `delta>0`.

Thus no finite checked scale can certify that the boundary family stays nonnegative. A valid source-built `kappa_-` theorem must prove a uniform-in-scale boundary inequality, a bounded amplification law, or a scale-independent completed boundary extension. Sampling finitely many scales is not a proof obligation substitute.

## Computation

Validated in:

- `computations/2026-06-21-penrose-proof-r15-boundary-amplification-no-finite-audit.py`
- `computations/2026-06-21-penrose-proof-r15-boundary-amplification-no-finite-audit.txt`

## Log

- 2026-06-21 -- created in 2-fully-proven from the black-hole inner-horizon mass-inflation NODE, method 9 small cases.

## 2026-06-24 static Schur reduction separated from uniform proof

`finite-rank-boundary-schur-index.md` records the static finite-rank boundary Schur reduction: at a fixed scale, `kappa_-(B+VCV*)` is determined by the finite boundary Schur matrix. This card remains the scale warning: static Schur reduction at checked degrees does not prove the uniform all-degree/channel statement.

A valid source-built index proof needs both ingredients: the correct Schur matrix at each scale and a source theorem preventing later amplification or hidden-channel crossings.

## 2026-06-24 finite prolate channels are a height-graded shadow

`finite-prolate-channel-boundary-rh-strength.md` gives the all-order fixed-channel version of this warning. At any fixed finite set of exterior prolate channels, the boundary repair vanishes on a finite ideal whose positivity remains RH-strength. Finite channel checks can therefore calibrate the semilocal carrier, but they cannot replace a source-uniform all-channel theorem.

## 2026-06-24 summable all-channel measure is still not enough

`summable-exterior-boundary-measure-rh-strength.md` separates two issues. Finite checks cannot certify a scale-dependent boundary family; moreover, even the full exterior channel set does not soften the all-order target if it enters only as a finite-total-variation measure. Source-uniform control must therefore come from a stronger semilocal operator theorem, not merely from including more summable exterior channels.
