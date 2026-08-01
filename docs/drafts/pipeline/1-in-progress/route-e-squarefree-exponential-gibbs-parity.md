# Route E squarefree exponential-Gibbs parity source

- **ID:** `ROUTE-E-GIBBS-PARITY-001`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HOSTILE SOURCE AUDIT
- **Source:** `mobius-additive-frontier-research-ledger.md` · `OPEN-SOURCE-001`
- **Statement:** Möbius--Laplace cancellation is the parity Fourier coefficient of a positive
  squarefree exponential-Gibbs law; every conditional two-prime table is strictly Rayleigh, but
  three primes already destroy real stability, so any successful parity estimate must use the
  multiplicative cutoff boundary rather than generic negative-dependence machinery.

## Goal

For `x>0`, put

```text
Z(x)   = sum_(n>=1) mu(n)^2 exp(-nx),
nu_x(n)= mu(n)^2 exp(-nx)/Z(x),
eta(n) = mu(n) on the squarefree support.
```

Then

```text
Phi(x)=sum_(n>=1) mu(n) exp(-nx)=Z(x) E_(nu_x)[eta].       (G1)
```

Since `Z(x)` has order `x^(-1)`, the exact Route E source can be written as the all-prime parity
mixing law

```text
for every epsilon>0,
  |E_(nu_x)[eta]| <= C_epsilon x^(1/2-epsilon),  0<x<=1.  (G2)
```

Equation `(G2)` implies every strict-half Möbius--Laplace decay estimate and hence RH through the
existing unconditional consumer. The claim is not admitted as proved. Its purpose is to force a
producer to act on a genuine positive source law while retaining the signed parity observable.

## Gates

- [x] 0 → 1  in-progress: source-pure probability law, exact RH-bearing parity target, and first
  hostile mechanism fixed
- [ ] 1 → 2  fully-proven: prove `(G2)` without RH, zero locations, or an equivalent Mertens bound
- [ ] 2 → 3  formalized: only after dependency-closed paper proof
- [ ] 3 → 4  publication-ready: only after external priority audit and complete Lean certificate

## Exact positive source representation

For a finite prime set `P`, define the multiaffine partition polynomial

```text
F_(P,x)(z)=sum_(S subset P) exp(-x product(S)) product_(p in S) z_p,  (G3)
```

with `product(empty)=1`. All coefficients are positive. Evaluation at the all-minus prime
orientation is the finite Möbius partition sum:

```text
F_(P,x)(-1,...,-1)
  =sum_(S subset P) (-1)^#S exp(-x product(S)).            (G4)
```

Cofinal prime exhaustion converges absolutely to `Phi(x)`. Thus `(G3)` is an honest positive
carrier for the exact signed observable, not an analytic continuation or zero-selected model.

## Theorem A — conditional two-prime Rayleigh law `[PROVED HERE]`

Fix a squarefree spectator product `a>=1` and distinct primes `p,q`. The four conditional weights
are

```text
w00=exp(-ax),   w10=exp(-apx),
w01=exp(-aqx), w11=exp(-apqx).
```

For every `x>0`,

```text
w10 w01-w00 w11
 =exp(-a(p+q)x)-exp(-a(1+pq)x)>0,                         (G5)
```

because `1+pq-(p+q)=(p-1)(q-1)>0`. Hence every two-coordinate conditional table of `(G3)` is
strictly log-submodular/Rayleigh. This recovers the useful sign behind the renewal anti-TP2 law in
a genuinely positive probability table.

## Theorem B — three-prime real-stability obstruction `[PAPER-PROVED HERE]`

Let `1<p<q<r`. The three-variable polynomial `F_({p,q,r},x)` is not real stable for all
sufficiently large `x`.

For a real multiaffine polynomial, real stability implies nonnegativity of every Rayleigh
difference on every real specialization. Specializing `z_r=t`, the `(p,q)` Rayleigh difference is

```text
Delta_(p,q)(t)=A_x+B_x t+C_x t^2,                         (G6)

A_x=exp(-(p+q)x)-exp(-(1+pq)x)>0,
C_x=exp(-r(p+q)x)-exp(-r(1+pq)x)>0,
B_x=exp(-(p+qr)x)+exp(-(q+pr)x)
      -exp(-(1+pqr)x)-exp(-(r+pq)x).
```

Put `D=r+pq`. Since

```text
D < p+qr,  D < q+pr,  D < 1+pqr,
```

one has `exp(Dx) B_x -> -1`. Also

```text
exp((p+q)x) A_x -> 1,
exp(r(p+q)x) C_x -> 1.                                   (G7)
```

Finally,

```text
(p+q)(r+1)-2(r+pq)>0.                                    (G8)
```

Indeed the left side is increasing in `r`, and at `r=q` it is
`(q-p)(q-1)>0`. Equations `(G7)`--`(G8)` give

```text
B_x^2/(A_x C_x) -> +infinity.                             (G9)
```

For all sufficiently large `x`, therefore, `B_x<0` and `B_x^2>4A_xC_x`. The quadratic `(G6)`
has two positive real roots and is negative between them. This violates the Rayleigh-difference
criterion, proving the claim.

No numerical test enters this proof. The obstruction is uniform for every ordered triple
`1<p<q<r`.

## Hostile audit

1. **Strongly-Rayleigh concentration is unavailable.** `(G5)` is only the two-coordinate shadow.
   Theorem B gives an exact three-coordinate failure of the real-stability hypothesis needed by
   strongly-Rayleigh and stability-preserving concentration theorems.
2. **Pairwise negative dependence cannot yield a power by itself.** Independent small-prime
   divisibility heuristics produce parity decay of logarithmic size; the missing square-root law is
   created at the moving multiplicative cutoff, where prime occupations cease to be independent.
3. **Fixed safe Dirichlet Gibbs law is not enough.** At weight `mu(n)^2/n^2`, prime occupations
   factor independently, but the critical observable localizes in the rare tail `n` of order
   `sqrt(k)`; absolute tail mass gives only the known Báez--Duarte `k^(-1/2)` floor.
4. **No probability-language substitution.** `(G2)` is exactly the Möbius--Laplace source after
   multiplication by `Z(x)`; proving it is RH-strength. The positive carrier prevents sign
   smuggling but does not weaken the theorem.
5. **Finite/local stability is not closure.** Theorem B kills one proposed producer only. It does
   not close Route E and cannot be cited as permission to retire `OPEN-SOURCE-001`.

## Strengthened surviving conjecture

`[CONJECTURE: GIBBS-BOUNDARY-MIXING]` Prove `(G2)` from a boundary-sensitive multiscale inequality
for `(G3)` which:

1. retains the all-minus parity observable before taking norms;
2. couples prime blocks whose products straddle the physical scale `1/x`;
3. gains one square root from the moving cutoff, not merely logarithmic small-prime decorrelation;
4. is stable under cofinal prime exhaustion; and
5. fails for phase-twisted or Beurling fake sources with known off-line zeros.

Generic strong-Rayleigh theory, pairwise covariance, fixed-prime induction, positive diagonal
energy, and independent-prime approximation are excluded by the hostile audit. A proof must use a
genuinely integer-specific boundary interaction.

## No-go status of the stability submechanism

- **Exact killing theorem/mechanism:** Theorem B; a three-prime Rayleigh difference has a negative
  interval for every sufficiently large physical scale.
- **Strongest positive survivor:** Theorem A; every conditional two-prime table is strictly
  Rayleigh, uniformly in the spectator product and scale.
- **New insight:** local negative dependence is real but stops at order two. Required source lives
  in scale-dependent higher-prime boundary interaction, not a global stable polynomial.
- **Status:** dependency-closed paper proof; Lean formalization deferred while the card remains an
  active Stage-1 source attack. Route E remains open.

## Log

- 2026-08-01 — created after exact `OPEN-SOURCE-001` re-audit; derived positive Gibbs parity form,
  proved conditional two-prime Rayleigh law, and paper-proved uniform three-prime real-stability
  obstruction without computation.
