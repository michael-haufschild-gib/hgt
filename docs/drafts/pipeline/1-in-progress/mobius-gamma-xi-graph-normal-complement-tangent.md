# Möbius Gamma/Xi graph-normal complement tangent

- **ID:** P-G161
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); Lean module written, audit pending
- **Source:** Route P, P-G159 complex Hermitian graph normal + P-G160 sharp saturation
- **Lean:** `RHTower/MobiusGammaXiGraphNormalComplementTangent.lean`
- **Statement:** graph-normal source minus explicit Wiener--Hopf complement has a rank-one critical
  tangent `(1+u)⁻¹ r_Xi(1/2)`; its scalar coefficient vanishes exactly under RH.

## Goal

Replace failed independent source/complement energy split with exact coherent graph-normal
incidence.  Determine full node dependence of first nonzero complement tangent and reduce Route P
to one source-pure positivity producer.

## Gates

- [x] 0 → 1 in-progress: exact source-pure definitions, proof, and Door passport
- [x] 1 → 2 fully-proven on paper: algebraic factorization, analytic limit, fixed-node RH detector
- [ ] 2 → 3 formalized: direct check, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external novelty audit and final positivity producer

## Conjecture loop

### P-G161a — first graph-normal complement tangent has general Hardy node dependence

Let `A_sigma(u)` be actual Gamma/Xi affine source, `A_sigma^0(u)` its zero-vector affine base,
`L(w)=logDeriv P_nonright(iw)`, `b` boundary self-symbol, and

```text
E_sigma(u) = (sigma-1) O_sigma(u),
w_sigma(u) = sigma + u(sigma-1) - 1/2.
```

Define explicit complementary graph-normal channel

```text
C_sigma(u) = E_sigma(u) [2i A_sigma^0(u) + 2i L(w_sigma(u)) - b].
```

Existing raw Ward decomposition and graph normalizer `N_sigma=-2i E_sigma` give, by exact algebra,

```text
g_sigma(u) - C_sigma(u)
  = E_sigma(u) r_Xi(w_sigma(u)).                         (P-G161.1)
```

**FALSIFIED.** After division only by `sigma-1`, critical node dependence is forced to be
rank-one:

```text
(g_sigma(u)-C_sigma(u))/(sigma-1)
  → (1+u)⁻¹ r_Xi(1/2).                                  (P-G161.2)
```

Proof: arithmetic overlap tends to `(1+u)⁻¹`; `w_sigma(u)→1/2`; strict-right canonical product is
nonzero at `iw` for `Re w>0`; analyticity makes its logarithmic derivative, relative trace, and
continued Ward response continuous at `1/2`.

The old complementary notation is a totalized quotient and is globally analytic iff RH, so using
it as graph infrastructure would be circular.  The proof therefore also establishes local
neighborhood equality with the unconditional entire divisor complement
`xiRightComplementCanonicalProduct` at every safe `iw`, equality of logarithmic derivatives, and
restates `(P-G161.1)`--`(P-G161.2)` with that genuine complement.  The rank-one tangent is not an
artifact of totalized division.

### P-G161b — fixed base node may miss off-critical zeros

Every strict-right Schwarz-pair Ward response has strictly positive real part on every right
half-plane node.  If RH fails, upper strict-right divisor is nonempty, so absolute summability and
one selected positive term imply

```text
Re r_Xi(1/2) > 0.
```

Under RH the strict-right divisor is empty and `r_Xi(w)=0`.  Therefore

```text
r_Xi(1/2)=0  iff  RH.                                   (P-G161.3)
```

**FALSIFIED.** No moving zero-adapted node is required for detection after graph-normal tangent
collapse.

## Higher principle

Critical graph normalization is a tangent-cone operation.  Zeroth-order source and complement
coincide; first nontrivial defect cannot retain arbitrary node geometry because the arithmetic
overlap kernel contracts it onto source feature at node zero.  Stalling of independent-energy and
first-order contraction routes was shadow of this rank-one tangent collapse.

P-G160c then makes collapse rigid: a fixed-four boundary tangent Gram with cross coefficient
`d=r_Xi(1/2)` is PSD on all canonical two-node packets only if `d=0`, hence only if RH.  This is a
receiver theorem.  P-G159 does not itself construct that tangent Gram.

## Hostile audit

- `(1+u)⁻¹` as escaped-mass transform is prior internal knowledge in
  `MobiusCriticalFisherSteinContact.lean`; not claimed novel.
- Raw Ward decomposition, graph normal factorization, overlap limit, and pair positivity are prior
  internal theorems.
- Corpus-new synthesis is exact adjusted true-complement law `(P-G161.1)`, rank-one tangent law
  `(P-G161.2)`, fixed-node completeness `(P-G161.3)`, safe-node replacement of totalized quotient
  by genuine entire complement, and reduction to P-G160c two-node rigidity.
- This is not RH proof: positivity of actual adjusted finite-sigma/source-incidence block remains
  unproved.  Claiming completion before that producer would be theatre.

## Exact next producer

Construct actual second-order unitary-curvature identity on source-selected Gamma/Sonin graph.
For first-order complement coefficient `epsilon*r_Xi(1/2)`, P-G160.5 proves any positive tangent
extension needs diagonal surplus `epsilon^2|r_Xi(1/2)|^2`.  Prove boundary unitarity supplies total
curvature at most source Fisher curvature, so this surplus is zero after causal energy is retained.
Equivalently, identify anti-causal derivative with rank-one defect `(P-G161.2)` on completed graph
core and close graph domain.  Merely postulating same-diagonal PSD is RH rewritten and receives no
credit.  If exact curvature contains positive surplus, compute it and pivot; do not call it RH.

## Log

- 2026-08-14 — exact complement algebra and rank-one critical profile proved on paper; Lean module
  written.
- 2026-08-14 — fixed node `1/2` proved complete for RH using strict pair positivity.
- 2026-08-14 — route reduced to finite-sigma adjusted-block positivity; RH not yet proved.
