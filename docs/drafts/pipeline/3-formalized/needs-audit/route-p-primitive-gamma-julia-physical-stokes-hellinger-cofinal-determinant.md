# Route P primitive Gamma--Julia physical Stokes Hellinger cofinal determinant

- **ID:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-cofinal-determinant`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105L]`
- **Parent:** `route-p-primitive-gamma-julia-stokes-cofinal-child-kernel.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalDeterminant.lean`

## Goal

Convert P-G105J's forced row-weighted Julia--polar generator into a source-equivalent symmetric
channel, tensor it with P-G105K's literal cofinal child kernel, and prove cofinal determinant
stability without deleting cross-prime incidence or fitting Xi.

## Conjecturing loop

### Conjecture 1 — physical nonnormality is intrinsic to signed polar completion

**Falsified.** Write `delta` for the fourth-depth Julia defect and `r` for forced polar ratio.
P-G105J channel generator is

```text
C_r = [[1, 64 delta], [r delta, -r]].
```

For `r >= 0`, its canonical Hellinger representative is

```text
A_r = [[1, 8 sqrt(r) delta], [8 sqrt(r) delta, -r]].
```

This is real symmetric. It has trace `1-r` and determinant `-64r`, using exact law
`delta^2=63/64`.

### Conjecture 2 — symmetrization may alter actual finite physical determinants

**Falsified exactly.** On every nonnegative source eigenvalue `lambda`,

```text
det(I + lambda u A_r)
  = 1 + lambda(1-r)u - 64 r lambda^2 u^2
  = F_lambda(64u, ru),
```

where right side is P-G105G signed bivariate factor. Hermitian diagonalization of arbitrary finite
source matrix then proves equality of full determinants. Specializing source to actual
aperture-conjugated P-G186 Gram proves entry-source-level P-G105J determinant retention for every
finite packet, not merely equality of traces or asymptotic factors.

### Conjecture 3 — full channel tensor may lose cofinal compactness

**Falsified.** Kernel on `(Fin 2 x primes)^2` is literal tensor `A_r(i,j) K_d(p,q)`. Finite channel
norm square is summable and P-G105K prime-pair norm square is summable, so separated product is
Hilbert--Schmidt after exact reindexing. Hermitian laws of both factors make represented operator
self-adjoint.

### Conjecture 4 — finite upper-half-plane stability may still fail in cofinal limit

**Falsified at det2 level.** Regularized determinant exists and finite principal det2 functions
converge uniformly on every closed disc. Any nonzero cofinal zero gives reciprocal eigenvalue of
represented Hilbert--Schmidt operator. Self-adjointness forces this eigenvalue, hence determinant
zero, to be real. Therefore cofinal det2 has no nonreal zeros. No Hurwitz zero-count argument is
needed.

### Conjecture 5 — symmetric channel may lose completed first current

**Falsified.** Cofinal diagonal sum is `tr(A_r)` times P-G105K Stokes trace, namely
`(1-r) firstTraceCurrent`. At forced `r(d)=-polar/firstTrace`, this is exactly completed
prime--Gamma current.

## Paper proof

Hellinger congruence is square-root splitting of positive channel weights:
`sqrt(diag(64,r)) B sqrt(diag(64,r))`, where `B` is Julia--Krein block. Exact defect identity gives
trace, determinant, and physical characteristic factor. Finite Hermitian source diagonalization
reduces both Hellinger and row-weighted pencils to identical product of these factors.

Tensor-product square summability follows after reindexing channel pairs away from prime pairs.
Both kernels are Hermitian, hence tensor is Hermitian; Hilbert--Schmidt kernel-to-operator bridge
makes operator self-adjoint. General corpus det2 theorem supplies an entire function and uniform
finite-section convergence on discs. General reciprocal-eigenvalue theorem plus self-adjoint
spectral reality forces every zero real. Diagonal Fubini and exact trace identity give completed
current. `QED`

## Novelty and anti-theatre audit

This closes live determinant obstruction rather than adding generic infrastructure:

- explains why finite stable but nonnormal P-G105J geometry admits cofinal spectral control;
- proves exact determinant equality for every actual finite P-G186 packet;
- retains all channel coupling and cross-prime cubic Cauchy incidence;
- constructs actual cofinal entire det2 with local-uniform finite-section convergence;
- proves cofinal zero locus is real;
- recovers completed arithmetic first current exactly.

Result is not RH. It does not prove child/physical operator trace class, construct ordinary
trace-restored determinant, control `d -> 0` determinant limit, or identify its divisor with Xi.
Claiming more would be theatre.

## Formal status

Lean proves unconditionally:

- Hellinger channel Hermitian, exact trace, determinant, and characteristic factor;
- full finite Hermitian-source product factorization;
- exact actual finite P-G186 physical determinant equality;
- full cofinal physical kernel Hilbert--Schmidt and Hermitian;
- represented operator self-adjoint;
- summable diagonal and exact completed current at forced ratio;
- entire det2 and uniform finite-section convergence on every closed disc;
- every cofinal det2 zero has zero imaginary part;
- premise-free P-G105L capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Module is umbrella-wired; no umbrella build was run.

## Refined open core

Prove P-G105K positive child operator is Schatten-one from positive finite pullbacks and summable
diagonal, lift trace class through finite Hellinger channel, and identify operator trace with
completed current. Then define ordinary trace-restored determinant, prove finite ordinary
determinants equal P-G105J physical pencils, and establish locally uniform `d -> 0+` convergence
with nontrivial divisor retention. Final arithmetic gate remains equality of resulting divisor
with Xi without target fitting.

## Higher universal principle

Signed stability is self-adjoint after changing density, not after changing operator. Positive
channel coordinates define canonical Hellinger metric; row-weighted Julia--polar generator and
symmetric representative are same colligation viewed in counting versus Hellinger density. Earlier
nonnormality obstruction was shadow of using wrong Hilbert metric. This suggests broader rule:
source-positive multichannel Euler completions should be symmetrized by square-root Radon--Nikodym
weights before cofinalization; determinant invariants survive, while spectral reality becomes
visible.

## Log

- 2026-08-16 — Exact Hellinger channel, finite determinant retention, full cofinal self-adjoint
  Hilbert--Schmidt det2, local-uniform finite-section convergence, real-zero law, and completed
  first trace paper-proved and formalized.
