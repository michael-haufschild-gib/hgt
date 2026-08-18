# G-CE marked clock--Sonin producer

- **ID:** `g-ce-marked-clock-sonin-producer`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / source producer
- **Source:** G-CE singular graph wall; CCM one-corner incidence; signed Möbius source
- **Statement:** Keep the two source orders `P_N D_{sigma,u}` and `D_{sigma,u} P_N` as orthogonal
  marks before scalarization. Their normalized two-port block is contractive, and its odd port is
  exactly half the source clock--Sonin commutator which produces the scalar seam.

## Goal

Construct the producer demanded by the G-CE debt dichotomy on the actual marked divisor source,
before any scalar inner product or signed-channel synthesis. The producer must retain the
reflection-odd order coordinate, be source-defined, and have an unconditional source norm bound.
It must not install `-I` on the scalar Ward value or select a Xi divisor.

## Gates

- [x] 0 -> 1 in-progress: source-pure object, exact formulas, hostile tests fixed
- [ ] 1 -> 2 fully-proven: dependency-closed paper proof and novelty audit
- [ ] 2 -> 3 formalized: unconditional Lean theorem, targeted check/build/axiom audit
- [ ] 3 -> 4 publication-ready: standalone theorem/proof/Lean certificate/priority audit

## Frozen corpus frontier

Let `H` be the complete squarefree Möbius source, `D_{sigma,u}` its bounded arithmetic-clock
damping, and `P_N=A_N^*A_N` the positive source pullback of the finite-depth contractive Sonin
corner. Corpus already proves

```text
||D_{sigma,u}|| <= 1,
||P_N x|| <= ||x||,
P_N x -> x,
[P_N,D_{sigma,u}]x -> 0                              (fixed sigma,u).
```

It also proves that scalarizing against the Fisher tangent gives

```text
transportedScore_N - reporterScore_N
  = <chi_sigma,[P_N,D_{sigma,u}] psi_sigma>.           (1)
```

Existing four-unit saturation and connection-escape theorems exclude every scalar connection or
Hilbert-vector correction after this scalarization. Existing pointed-Fisher rank-one and doubled
parity modules already exclude presenting a generic rank-one/two-port lift as new work.

## Conjecture / failure / pivot loop

### C1 -- Julia lift of the signed coisometry `[REJECTED: CORPUS DUPLICATE]`

The canonical coisometry colligation splits a marked source into its signed source-line projection
and orthogonal complement. This is standard Julia-operator algebra and does not change the
RH-bearing angle. It only records scalarization loss.

### C2 -- source-adaptive rotation into the synthesis kernel `[REJECTED: ERASURE]`

A unitary depending on the actual input can rotate it into the kernel of signed synthesis whenever
the orthogonal component is nonzero. This kills every chosen source by construction, has no
Gamma/Sonin covariance, and transfers rather than eliminates its energy. It is not a linear
source law.

### C3 -- scalar moving connection `[REJECTED: IMPOSSIBLE CATEGORY]`

At a strict-right Xi zero, the Hardy father diagonal, Ward codiagonal, and four-unit detail budget
violate Cauchy--Schwarz even for singular/cofinal lifts. A connection added after scalarization
cannot remove exact debt.

### C4 -- marked two-order producer `[ACTIVE SURVIVOR]`

Define the normalized producer

```text
M_{N,sigma,u}(x)
  =2^(-1/2) (P_N D_{sigma,u}x, D_{sigma,u}P_Nx) in H direct_sum H.  (2)
```

Let normalized Hadamard ports be

```text
H_+(y,z)=2^(-1/2)(y+z),
H_-(y,z)=2^(-1/2)(y-z).                                 (3)
```

Then

```text
H_+ M(x)=(P_ND+DP_N)x/2,
H_- M(x)=[P_N,D]x/2.                                    (4)
```

Both source orders therefore survive until the final choice of port. The exact Hilbert identity

```text
||H_+M(x)||^2+||H_-M(x)||^2=||M(x)||^2                 (5)
```

and contractivity of both `P_N` and `D` give

```text
||M(x)|| <= ||x||.                                       (6)
```

For the normalized Möbius source `psi_sigma`, `||M(psi_sigma)||<=1`. Combining `(1)` and `(4)`
gives the exact pre-scalar seam

```text
transportedScore_N-reporterScore_N
  =2 <chi_sigma,H_-M_{N,sigma,u}(psi_sigma)>.            (7)
```

Thus the discrepancy is not an unexplained scalar connection. It is scalarization of one explicit
reflection-odd vector port of a contractive higher-dimensional source producer.

## Paper proof

Equations `(4)` follow by linearity. Equation `(5)` is the parallelogram identity applied to the
two marked order vectors. For `(6)`, the product norm gives

```text
||M(x)||^2
 =1/2 (||P_N D x||^2+||D P_N x||^2)
 <=1/2 (||D x||^2+||P_N x||^2)
 <=||x||^2.
```

Nonnegativity of norms then yields `(6)`. Equation `(7)` is `(1)` with
`[P_N,D]psi_sigma=2 H_-M(psi_sigma)` from `(4)`. No Xi zero, RH assumption, target norm, or
post-scalar controller occurs.

## Novelty and frontier effect

Primary-source audit: Suzuki's 2026 screw-function paper constructs finite self-adjoint nonlocal
realizations but leaves their limiting operator conjectural. Connes--Consani--Moscovici's 2025
zeta spectral triples construct finite rank-one perturbations but leave spectral/determinant
convergence as the RH-bearing step. Neither retains the two source orders in `(2)` nor identifies
their odd Hadamard port with the Möbius clock--Sonin seam.

Generic Hadamard/parallelogram algebra is classical and is not claimed new. Candidate new content
is the source-specific placement `(2)`--`(7)`: exact G-CE discrepancy is generated before
scalarization by a contractive marked divisor-source block.

This does not prove RH. It sharpens exact remaining theorem. Since `H_-M(psi_sigma)->0` at fixed
`sigma`, nonzero G-CE debt can only arise after division by the collapsing Gamma graph scale.
Required RH-bearing estimate is vector-level scaled admission

```text
||H_-M_{N(sigma),sigma,u}(psi_sigma)||
  =o((sigma-1) squarefreeBoundaryOverlap(sigma,sigma-1,u))          (8)
```

on one source-defined cofinal schedule, together with boundary transport. Mere strong convergence,
scalar commutator cancellation, or a controller installed after `(7)` is insufficient.

## No-go closure

- **Exact killing mechanism:** C1 duplicates canonical coisometry splitting; C2 is nonlinear
  source erasure; C3 violates the already formalized cofinal four-unit Gram obstruction.
- **Strongest positive survivor:** contractive marked two-order producer `(2)` with exact odd-port
  seam `(7)`.
- **New insight:** exact debt is singular amplification of a vanishing reflection-odd source port;
  it is not excess norm of the pre-scalar source.
- **Status:** paper proof complete; Lean formalization pending.

## Log

- 2026-08-18 -- corpus-first and primary-literature audits; three candidates rejected; C4 frozen.
