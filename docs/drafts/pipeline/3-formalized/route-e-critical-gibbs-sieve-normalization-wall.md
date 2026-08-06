# Route E critical Gibbs/sieve normalization wall

- **ID:** `route-e-critical-gibbs-sieve-normalization-wall`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / `[NORMALIZATION WALL]` / `[NOT RH]`
- **Scientific status:** `[STANDARD FINITE EULER IDENTITY]`
  `[NEW ROUTE-E CROSS-CORPUS CONSEQUENCE]` `[EXTERNAL NOVELTY NOT CLAIMED]`
- **Parent:** `../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Lean:** `RHTower/GibbsCriticalSieveNormalizationWall.lean`

## Statement

For a finite prime set (P), put

\[
 a_P=\prod_{p\in P}(1-p^{-1}),\qquad
 B_1(P)=\prod_{p\in P}(1+p^{-1}),\qquad
 C_2(P)=\prod_{p\in P}(1-p^{-2}).
\]

Here (a_P) is the coprime-sieve density and (B_1(P)) is the Euler inflation factor in the
surviving Route E Mellin-energy channel (r=1).  Then

\[
 \boxed{a_PB_1(P)=C_2(P).}                                      \tag{1}
\]

If

\[
 T_2(P)=\sum_{(n,\prod_{p\in P}p)=1}n^{-2},
\]

the prime-sieve trace law gives

\[
 T_2(P)=T_2(\varnothing)C_2(P),\qquad
 T_2(P_N)\longrightarrow1                                     \tag{2}
\]

along every prime exhaustion (P_N).  Consequently

\[
 a_{P_N}B_1(P_N)\longrightarrow T_2(\varnothing)^{-1}>0,       \tag{3}
\]

and, at every finite stage,

\[
 \boxed{B_1(P)=\frac{T_2(P)}{T_2(\varnothing)a_P}.}             \tag{4}
\]

Thus critical Gibbs Euler growth is exactly reciprocal sieve-density growth times a regular
Hilbert--Schmidt factor with a finite nonzero cofinal limit.

## Proof

For each prime,

\[
 (1-p^{-1})(1+p^{-1})=1-p^{-2},
\]

and multiplication over (P) proves `(1)`.  The existing finite sieve-trace Euler product proves
the first identity in `(2)`; its cofinal vacuum theorem proves the limit.  Substitution yields
`(3)`.  Positivity of (T_2(\varnothing)) and (a_P) permits division and gives `(4)`.

## Route E consequence

This closes the **regular** part of the surviving (r=1) energy normalization.  The
(p^{-2}) layer is already the second sieved trace/Hilbert--Schmidt vacuum defect.  Within this
normalization comparison, the remaining Route E burden lies in the **normalized first-order**
(p^{-1}) source layer.

Multiplying a Route E energy estimate by (a_P) can remove the Euler inflation, but it also sends
the source mass to zero.  Dividing back by (a_P) restores all of (B_1(P)).  This is the same
normalization amplification already proved for conditioned prime-valuation states:
the summable unnormalized edge (a_P/p) becomes the nonsummable normalized edge (1/p).
Therefore none of the following implies the Route E current bound:

- cofinal Hilbert--Schmidt convergence of the sieve operator;
- convergence of the regular determinant character;
- telescoping total variation of the unnormalized sieve density;
- an abstract graph-seminorm completion built from those convergent channels.

Each controls the (p^{-2}) regular layer or the vanishing unnormalized source.  Route E asks for
the normalized signed (p^{-1}) layer.

## Sharpened survivor

The only new avenue exposed by this bridge is a **signed first-trace/Bockstein cancellation before
positive norm**.  A viable theorem must construct, from the literal parity--energy covariance
integrals, a source-defined countertransport which cancels the normalized (1/p) principal
transition across alternating finite volumes and leaves an absolutely summable (p^{-2}) (or
smaller) remainder.  It must remain uniform at the moving antiscale frequency
(t_P\asymp1/\log\max P).

The regular remainder is now closed by `(1)`--`(3)`.  Construction and estimation of the signed
first-trace countertransport is not proved and remains another formulation of
`WEIGHTED-PRIME-DILATION-INCREMENT-CANCELLATION` until an explicit non-circular formula is given.

For the Hall alternative, the sieve edges (a_{P_{j-1}}/p_j) are canonical nonnegative scalar
weights and telescope to one.  They still lack a uniform moving-window lift to the fixed physical
relation (R_X^{\rm gr}), collision-quotiented interval Hall, and cross-anchor incoming-load
control.  Treating scalar sieve weights as physical seam weights without that lift is invalid.

## Lean declarations

`RHTower/GibbsCriticalSieveNormalizationWall.lean` proves unconditionally:

- `gibbsCriticalEulerBaseline`;
- `sieveDensity_mul_gibbsCriticalEulerBaseline` — `(1)`;
- `sieveTrace_empty_two_mul_criticalNormalization` — finite trace form of `(2)`;
- `tendsto_criticalSieveNormalization` — `(3)` for every prime enumeration;
- `gibbsCriticalEulerBaseline_eq_sieveTrace_div` — `(4)`.

No zero hypothesis, RH hypothesis, computation, or new axiom is used.

## Hostile audit

1. `(1)` is elementary and carries no external novelty claim.
2. The new content is its exact cross-corpus localization of Route E's surviving (r=1) burden.
3. The theorem does not estimate (J_P/Z_P), the covariance increments, or their signed
   accumulation.
4. Source-normalization amplification prevents promotion of unnormalized sieve convergence to a
   normalized current estimate.
5. `OPEN-SOURCE-001` and RH remain open.
