# Route E Deninger analytic log-pull and finite-dilation fracture

- **ID:** `ROUTE-E-DENINGER-ANALYTIC-LOG-PULL-FINITE-DILATION-FRACTURE-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT DOMAIN CLASSIFICATION / NO-GO SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../2-fully-proven/new_scientific_knowledge/route-e-deninger-vacuum-finite-dilation-fracture.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Statement:** A strict Deninger-source representative of an analytic logarithmic pull forces
  infinite analytic order at the origin; an entire pull is zero, and a finite mask of distinct
  positive vacuum dilates belongs to the source exactly when every coefficient vanishes.

## Goal and non-theatre standard

Finite prime-dilation defects were proposed as a way to move Route E's vacuum into the strict
Deninger--Meyer source. Merely observing that one vacuum profile is outside that source would not
close the mechanism. The exact task is to classify every finite distinct-dilation mask and expose
the strongest source-domain rigidity behind it.

The result below does this without an RH premise, an arithmetic cancellation hypothesis, or a
finite-dimensional proxy for source membership. It uses the actual all-weight
`DeningerExpSchwartz` definition. It does not estimate the surviving compact vacuum collar and
therefore does not claim an RH proof.

## Theorem A — analytic log-pull fracture

Let `G : C -> C` be analytic at zero. Suppose `f` is a real Schwartz function with values in `C`,
`f` belongs to `DeningerExpSchwartz`, and

```text
f(t) = G(exp(t))                                                     (A.1)
```

for every real `t`. Then

```text
analyticOrderAt G 0 = top.                                          (A.2)
```

If `G` is entire, then `G=0` on `C`.

### Dependency-closed proof

Assume the analytic order is the finite integer `n`. Analytic factorization gives a germ `g`,
analytic near zero, with

```text
G(z) = z^n g(z),       g(0) != 0.                                   (A.3)
```

Use the order-zero Deninger source estimate with exponential weight `n+1`. On the left tail,
`|t|=-t`; inserting (A.1)--(A.3) into that estimate cancels the `n` powers of `exp(t)` and yields

```text
norm(g(exp(t))) <= C exp(t).                                        (A.4)
```

The right side tends to zero as `t -> -infinity`. Continuity of `g` at zero simultaneously sends
the left side to `norm(g(0))`, contradicting `g(0) != 0`. Thus (A.2) holds. For an entire `G`, the
analytic identity theorem in analytic-order form says infinite order at one point is equivalent to
`G=0`.

## Theorem B — exact finite-dilation classification

Define

```text
V(t) = exp(-exp(t)).
```

For pairwise distinct positive real rates `a_j` and complex coefficients `c_j`,

```text
exists f : DeningerExpSchwartz,
  f(t) = sum_j c_j V(t + log(a_j)) for every t
iff
c_j = 0 for every j.                                                (B.1)
```

### Dependency-closed proof

The exact identity

```text
V(t + log(a_j)) = exp(-a_j exp(t))
```

writes the mask as `G(exp(t))` for the entire function

```text
G(z) = sum_j c_j exp(-a_j z).                                       (B.2)
```

Theorem A forces infinite analytic order at zero, hence its first `r` derivatives vanish:

```text
sum_j c_j (-a_j)^k = 0,        0 <= k < r.                           (B.3)
```

Distinct rates make the Vandermonde matrix invertible, so every `c_j=0`. Conversely the zero mask
is represented by the zero element of `DeningerExpSchwartz`.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.RouteEDeningerVacuumFiniteDilationFracture
```

Principal declarations:

```text
deningerExpSchwartz_logPull_analyticOrderAt_eq_top
deningerExpSchwartz_logPull_entire_eq_zero
routeEDeningerFiniteVacuumDilation_eq_shifted_vacuum
routeEDeningerFiniteVacuumDilation_coeff_eq_zero
exists_deningerExpSchwartz_finiteVacuumDilation_iff
exists_deningerExpSchwartz_shiftedVacuum_iff
```

The module is imported by `GaloisForLFunctions.RHTower`. The proof reuses the corpus's analytic
exponential-amplitude derivative formula and mathlib's finite Vandermonde rigidity theorem. No
axiom, `sorry`, `admit`, `opaque`, `unsafe`, numerical computation, or route premise is introduced.

## Exact positive survivor and remaining boundary

The no-go's positive survivor is the analytic source-domain classification in Theorem A. It is
strictly stronger than the finite vacuum statement: every analytic germ pulled back through
`exp(t)` is excluded unless it is flat to infinite analytic order, and every entire such pull is
zero.

This closes finite dilation, finite difference, and finite recurrence masks as strict-source
escape mechanisms. The parent's smooth cutoff decomposition is now formalized independently in
`route-e-deninger-vacuum-meyer-tail-hard-collar-decomposition.md`: the tail kernel is a literal
strict source and the compact collar is an exact finite Möbius sum. Estimating that finite collar
is still `OPEN-SOURCE-001`; this card makes no such arithmetic claim.

## Novelty status

Per current research directive, no external literature search was performed. The result is new to
the internal Route E corpus at this level of generality and is classified conservatively as
`[BRIDGE] [NOVELTY UNVERIFIED]`, not as an external priority claim.

## Log

- 2026-08-11 — exact analytic-order fracture and finite shifted-vacuum iff proved in Lean;
  umbrella import added; promoted as claim-complete Stage 3 child while parent cutoff claim remains
  Stage 2.
