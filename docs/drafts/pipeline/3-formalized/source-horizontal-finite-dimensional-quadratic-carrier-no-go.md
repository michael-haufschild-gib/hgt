# Source-horizontal finite-dimensional quadratic-carrier no-go

- **ID:** SH-FDQC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SourceHorizontalFinitePortStokesCapacity.lean`
- **Statement:** No fixed finite-dimensional real quadratic carriers, with arbitrary quadratic forms and linear landing maps, receive both orientations of every off-wall source-horizontal reflected packet.

## Goal

Kill finite-dimensional source carriers before the shared HB/FZZ-P/PW-B/RBH Ward receiver. Chain: source carrier landing → reflected Ward orientation → shared receiver extinction → RH.

## Gates

- [x] 0 → 1: corpus-derived exact packet/inertia data; source-pure dimension attack
- [x] 1 → 2: dependency-closed proof; `[PROVED HERE]`
- [x] 2 → 3: Lean theorem, target build, axiom audit, umbrella wire
- [ ] 3 → 4: publication-ready

## Theorem and proof

Let `S = Q ∘ f` be a real quadratic-form pullback through finite-dimensional `M`. A maximal negative-definite subspace `W` of `S` maps injectively under `f`: a nonzero `x ∈ W` in `ker f` would give both `S x < 0` and `S x = Q 0 = 0`. Hence `sigNeg S ≤ dim M`.

For a right-half source-horizontal packet of size `m`, corpus theorem gives `sigNeg S = m - 1`. Off wall, either packet or line-conjugate reflection is right-half. Given target dimensions `k₁,k₂`, choose an injectively prime-labelled packet of size `max k₁ k₂ + 2`; then both dimensions are `< m - 1`, so simultaneous exact landings are impossible.

## Novelty audit

`[NEW]` relative to corpus search and literature through 2026-08. Corpus finite-port theorem assumes sums of one-port forms; this removes all positivity, decomposition, Stokes, and bounded-coefficient assumptions. General Pontryagin realization theory treats kernels with finitely many negative squares, but no audited source proves this Xi source-packet exhaustion law: [Alpay–Pinhas–Vinnikov](https://arxiv.org/abs/1806.10704). Recent Xi/Krein proposal supplies an interpretive indefinite spectral ansatz, not this obstruction: [Takook 2026](https://arxiv.org/abs/2606.13932). Connes–Consani's semilocal analysis instead stresses missing global prime normalization: [Scaling Hamiltonian](https://arxiv.org/abs/1910.14368).

## No-go closure

- **Exact killing mechanism:** negative index of right packet grows as `m - 1`; pullback through dimension `k` has negative index at most `k`.
- **Strongest positive survivor:** any exact landing of a right packet of size `m` requires target dimension at least `m - 1`.
- **New insight:** shared source producer needs unbounded-dimensional negative capacity, or must abandon linear quadratic landing via nonlinear/singular dynamics.
- **Status:** `sourceHorizontalFiniteDimensionalQuadraticCarrierRouteKilled` in `SourceHorizontalFiniteDimensionalQuadraticCarrierNoGo.lean`; direct Lean and target build pass; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired.
