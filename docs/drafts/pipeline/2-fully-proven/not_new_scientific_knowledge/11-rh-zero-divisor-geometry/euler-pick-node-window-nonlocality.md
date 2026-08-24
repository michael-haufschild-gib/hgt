# Euler Pick node windows do not localize the divisor

- **ID:** `euler-pick-node-window-nonlocality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE-D NO-GO (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Input:** `euler-pick-inertia-offline-zero-count.md`

## Statement

Let `K(z,w)` be a Hermitian kernel, meromorphic-holomorphic in `z` and
meromorphic-antiholomorphic in `w`, on a connected domain `Omega`, and suppose its negative-square
index is `kappa` (finite or infinite).  For every nonempty open subset `V` of `Omega`,

```text
ind_-(K restricted to V x V)=kappa.                         (1)
```

Applied to the Euler-region shifted-Xi Pick kernel `S_omega`, equation (1) says that restricting
Euler sample nodes to any nonempty open band, box, or purported height window does **not** count only
zeros in the corresponding ordinate range.  It retains the complete off-line count in
`Re(rho)>1/2+omega`.

Consequently a Route D height window cannot be created by:

1. restricting the Pick kernel to a smaller open sampling region;
2. choosing a dense node sequence inside such a region; or
3. multiplying by an analytic cutoff that is one on the desired region and zero on another open
   region.

Exact height localization requires a different operation: a source-defined Riesz projection of a
closed model operator, a modified meromorphic symbol with an independently controlled divisor, or
another genuinely excisive closed construction.

## Proof of locality

The inequality

```text
ind_-(K|V)<=ind_-(K)=kappa
```

is immediate because every Gram matrix formed from points of `V` is also a Gram matrix formed from
points of `Omega`.

For the reverse inequality, first suppose `kappa` is finite.  In the reproducing-kernel Pontryagin
realization of `K`, the kernel sections `K(.,w)` with `w in V` have dense span.  Indeed, a vector
orthogonal to all these sections represents a meromorphic function vanishing on the nonempty open
set `V`; the identity theorem makes it zero on the connected domain.  Choose a basis of a
`kappa`-dimensional negative subspace.  Approximate that finite basis by vectors in the span of the
sections with nodes in `V`.  Strict negative definiteness is open under sufficiently small
perturbation of a finite Gram matrix, so `K|V` has a negative subspace of dimension `kappa`.

If `kappa` is infinite, apply the same argument to a negative subspace of every prescribed finite
dimension.  This proves (1).

For the shifted-Xi kernel, the earlier Euler Pick theorem identifies `kappa` with the complete
multiplicity of zeros satisfying

```text
Re(rho)>1/2+omega.
```

Therefore every nonempty open uniqueness region sees that same complete count.  A node band can
change numerical conditioning and the speed at which finite sections reveal negative directions,
but not the exact limiting index or its divisor support.

Finally, an analytic scalar cutoff on a connected domain which vanishes on one nonempty open set is
identically zero.  It cannot also equal one on the desired window.  A nonanalytic cutoff destroys
the analytic-kernel hypothesis supporting the Pick/Pontryagin divisor identity.  Thus neither form
of pointwise cutoff gives an exact analytic window.

## Exact route boundary

- `[CLOSED]` Node restriction does not turn the global transverse Pick count into a height-local
  count.
- `[CLOSED]` Dense finite sections inside a node window converge to the global negative index.
- `[CLOSED]` There is no nontrivial exact analytic pointwise cutoff on the connected source domain.
- `[OPEN CORE]` A height-excisive source theorem must construct a closed model operator and a Riesz
  projection, or an equivalent modified symbol, and then prove its contour resolvent is controlled
  from Euler--Gamma data without evaluating the unknown window divisor.

## Novelty audit

Locality of negative squares on analytic uniqueness regions, density of kernel sections, and the
identity theorem are standard.  The application removes a Route D shortcut but is not new
scientific knowledge.

## Lean status update (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/AnalyticOpenCutoffNoGo.lean` now proves the exact analytic
pointwise-cutoff obstruction: on every preconnected complex domain, an analytic scalar that
vanishes on one nonempty open subregion vanishes globally, and therefore cannot equal one on any
other nonempty subregion. The leaf is wired into `HTGeometry.lean`, checked with `lake env lean`,
target-built as `GaloisForLFunctions.HTGeometry.AnalyticOpenCutoffNoGo`, and both declarations
audit to only `propext`, `Classical.choice`, and `Quot.sound`.

This formalizes the third exclusion in the statement. It does not yet formalize the
Pontryagin-space kernel-section density argument or the shifted-Xi negative-index/divisor
identification, so the card remains at stage 2.

## Lean status update (2026-08-24)

`formal/GaloisForLFunctions/RHTower/AnalyticKernelUniquenessRegion.lean` now formalizes the complete
abstract locality-of-negative-squares argument. It proves analytic uniqueness for kernel-section
spans on every nonempty open subregion and every node set with an interior accumulation point,
proves openness and density stability of arbitrary finite negative dimensions, and identifies those
dimensions with literal finitely supported double kernel-Gram sums. Thus both finite and unbounded
negative-index profiles are preserved without a finite-index assumption.

The leaf is wired into `RHTower.lean`; exact source check and targeted leaf build pass. Every new
public declaration audits to only `propext`, `Classical.choice`, and `Quot.sound`. Remaining card
dependency is now exact: construct the analytic Pontryagin realization of the actual
`xiShiftPick` kernel and prove its global index/divisor identification. Until that arithmetic
realization is closed, the shifted-Xi application is not promoted.
