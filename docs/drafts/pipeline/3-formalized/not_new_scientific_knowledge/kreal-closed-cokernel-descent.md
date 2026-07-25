# Closed-cokernel descent in Deninger's \(K_{\mathbb R}\)

- **ID:** `kreal-closed-cokernel-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `kreal-kernel-cokernel-descent` · CCM topological quotient
- **Statement:** a continuous \(K_{\mathbb R}\)-structure preserving a subspace also preserves
  its closure, so quotient by the closed image inherits the same parity square.

## Goal

Discharge the topological quotient step in CCM's definition
\[
  \operatorname{coker}_{\overline{\operatorname{im}}}\rho^\natural
\]
without assuming the arithmetic quaternionic lift itself.

## Theorem

`[LITERATURE / PROVED HERE]` Let \(W\) be a complex topological vector space, let
\(\sigma:W\to W\) be continuous and conjugate-linear, and suppose
\[
  \sigma^2=(-1)^p,\qquad p\in\{0,1\}.
\]
If a complex subspace \(S\subseteq W\) satisfies \(\sigma(S)\subseteq S\), then:

1. \(\sigma(\overline S)\subseteq\overline S\);
2. \(\overline S\) is a closed complex subspace;
3. \([w]\mapsto[\sigma w]\) is a well-defined conjugate-linear map on
   \(W/\overline S\);
4. its square is \((-1)^p\).

In particular, if \(f:V\to W\) is a continuous \(K_{\mathbb R}\)-morphism, the closed-image
cokernel
\[
  W/\overline{\operatorname{im}f}
\]
inherits the target \(K_{\mathbb R}\)-parity.

## Proof

Continuity gives the general inclusion
\[
  \sigma(\overline S)\subseteq\overline{\sigma(S)}.
\]
Since \(\sigma(S)\subseteq S\),
\[
  \overline{\sigma(S)}\subseteq\overline S,
\]
proving item 1.  Closure of a complex subspace is a complex subspace because addition and scalar
multiplication are continuous, proving item 2.  Items 3 and 4 are then the algebraic quotient
argument:
\[
  \overline\sigma^2([w])=[\sigma^2w]=[(-1)^pw]=(-1)^p[w].
\]

## Exact CCM consequence and boundary

Once a continuous quaternionic lift of the CCM restriction arrow is constructed, no additional
closure hypothesis is needed: equivariance makes the image stable, this theorem makes its closure
stable, and the closed CCM cokernel automatically has \(\sigma^2=-1\).

The remaining arithmetic problem is therefore not quotient well-definedness.  It is construction
of a continuous source-defined \(\sigma\) on the enhanced restriction correspondence and proof
that forgetting the enhancement is the single CCM realization.

## Novelty audit

This is standard topology of continuous maps and quotient modules and is not claimed as new
scientific knowledge.  It is isolated because CCM explicitly use closure of the range, whereas
the preceding algebraic descent theorem only treats the raw image.

Lean module:
`GaloisForLFunctions.RHTower.KRealClosedCokernel`.

Formal capstones:

- `KRealStructure.topologicalClosure_stable`;
- `KRealStructure.closedQuotient`;
- `KRealStructure.closedCokernel`;
- `KRealStructure.closedCokernel_sigma_mkQ`.

## Gates

- [x] 0 → 1 in-progress: exact closed-image statement and CCM role identified
- [x] 1 → 2 fully-proven: complete proof above; no open dependency
- [x] 2 → 3 formalized: leaf build green; axiom audit contains only Lean foundational axioms;
  formal lint passes
- [ ] 3 → 4 publication-ready: not intended as a standalone new result

## Log

- 2026-07-25 — proved immediately after algebraic kernel/cokernel descent.  No numerical
  evidence and no RH assumption used.
- 2026-07-25 — formalized in `KRealClosedCokernel.lean`; minimal
  `lake env lean GaloisForLFunctions/RHTower/KRealClosedCokernel.lean` passed; final
  `lake build GaloisForLFunctions.RHTower.KRealClosedCokernel` passed; formal lint passed.
