# Möbius additive-triangle source for half-polylog Laplace decay

- **ID:** `mobius-additive-triangle-half-polylog-source`
- **Stage:** 1-in-progress
- **Type:** `[CANDIDATE THEOREM] [CONJECTURAL SOURCE ESTIMATE]`
- **Scientific status:** `[PAPER-PROVED BRIDGE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN UNCONDITIONAL RH PROOF]`
- **Source:** Möbius--Laplace frontier; additive Cauchy square of the distinguished source
- **Statement:** Linear-polylog upper control of the triangular additive Möbius self-convolution
  implies fixed-half-polylog Laplace decay, RH, and a critical-zero multiplicity cap.

## Goal

Replace direct pointwise control of

```text
Phi(x) = sum_(n>=1) mu(n) exp(-n x)
```

by a two-dimensional arithmetic cancellation problem.  Put

```text
c(k) = sum_(m+n=k) mu(m) mu(n),
T(N) = sum_(k<=N) c(k)
     = sum_(m+n<=N) mu(m) mu(n).                       (AT1)
```

The source conjecture is that for some fixed `q : Nat` and `C>0`,

```text
T(N) <= C (N+1) log(N+2)^(2q)                         (AT2)
```

for every `N`.  Absolute-value control is sufficient but not required.  Proving `(AT2)`
unconditionally would imply `MobiusDiscreteLaplaceHalfPolylogDecay q`, hence RH.  This route is
source-pure: `(AT2)` concerns only finite Möbius sums and does not mention zeta zeros.

## Dependency-closed bridge theorem

Let `r=exp(-x)`, so `0<r<1`.  Absolute convergence permits the Cauchy product

```text
Phi(x)^2 = sum_(k>=0) c(k) r^k.                        (AT3)
```

Since `c(k)=T(k)-T(k-1)` with `T(-1)=0`, Abel summation gives the exact identity

```text
Phi(x)^2 = (1-r) sum_(N>=0) T(N) r^N.                 (AT4)
```

The left side is real and nonnegative.  Thus the one-sided estimate `(AT2)` and positive weights
in `(AT4)` give

```text
|Phi(x)|^2
  <= C (1-exp(-x))
       sum_(N>=0) (N+1) log(N+2)^(2q) exp(-N x).       (AT5)
```

For `0<x<=1/2`, `1-exp(-x)<=x`.  Split the last sum at `N<=1/x`.  On the first part,
`log(N+2)=O(|log x|)` and the arithmetic sum of `N+1` is `O(x^-2)`.  On the tail, write
`u=Nx`; fixed powers of `log(N+2)` are absorbed into a fixed polynomial in
`|log x|+u`, while `exp(-u)` has every polynomial moment.  Therefore

```text
sum_(N>=0) (N+1) log(N+2)^(2q) exp(-N x)
  = O_q(x^-2 |log x|^(2q)).                            (AT6)
```

Combining `(AT5)` and `(AT6)` and taking the nonnegative square root yields

```text
|Phi(x)| = O_q(x^-1/2 |log x|^q).                     (AT7)
```

The formalized half-polylog consumer then gives

```text
RiemannHypothesis,
order_rho(zeta) <= q+1 for every critical-line zero rho. (AT8)
```

This proves the bridge `(AT2) -> (AT7) -> (AT8)` on paper.  Only `(AT2)` remains open.

## Why this is not a renamed first-moment target

`T(N)` is a genuinely two-dimensional triangular sum.  The elementary identity

```text
T(N) = sum_(m<N) mu(m) M(N-m)
```

shows why the prime number theorem is insufficient: inserting only `M(y)=o(y)` gives at best
`o(N^2)`, far above the linear scale required in `(AT2)`.  Conversely, `(AT2)` controls a positive
Laplace square after Abel smoothing and need not provide a pointwise Mertens bound.  It is a new
arithmetic interface, though still an RH-strength source conjecture.

## Attack plan

1. Treat `T(N)` as a bilinear Möbius form over the convex lattice triangle `m+n<=N`.
2. Apply a two-variable Möbius/Heath--Brown decomposition before absolute values.
3. Separate balanced boxes `m,n asymp N` from boundary boxes.  Boundary boxes reduce to known
   first-moment cancellation; balanced boxes require a dispersion or large-sieve estimate that
   preserves the additive inequality.
4. Seek a one-sided upper bound only.  Large negative excursions help `(AT4)` and should not be
   discarded by an absolute-value reduction.

## Hostile audit

1. **Cauchy-square circularity.** `(AT3)` alone is an identity and gives no estimate.  Scientific
   content is exactly the finite arithmetic bound `(AT2)`.
2. **Fixed-shift Chowla does not close it.** Rewriting by `h=m-n` produces shifts up to size `N`
   with nonrectangular endpoints.  Known fixed-shift or logarithmically averaged Chowla results do
   not give the uniform linear total required here.
3. **PNT does not close it.** Summation against `M(N-m)` loses one full power of `N` without new
   bilinear cancellation.
4. **Absolute values likely destroy the route.** The trivial absolute triangle has order `N^2`.
   Any proof must retain Möbius signs through the balanced bilinear stage.
5. **One-sided legitimacy.** Although individual `T(N)` may be negative, `(AT4)` equals
   `Phi(x)^2>=0`; an upper bound on each `T(N)` is sufficient because all Abel weights are positive.
6. **No unconditional RH claim.** No proof of `(AT2)` is known here.

## Corpus and literature audit

- Exact searches of `formal/`, stages 2--5, and the support log found no additive-triangle
  Möbius source or identity `(AT4)` specialized to the discrete Möbius--Laplace transform.
- Liflandsky's 2026 paper studies `Phi`, its explicit formula, and the direct half-power criterion;
  it does not state `(AT1)`--`(AT8)`.
- Standard Chowla literature studies products at fixed or averaged shifts, not this cofinally
  growing triangular family with a linear one-sided total.
- Targeted searches for `sum_(m+n<=N) mu(m)mu(n)`, additive Möbius self-convolution, and triangular
  Möbius sums found no matching theorem or criterion.

Classification remains `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` pending specialist priority review.
The elementary general Cauchy-product/Abel mechanism is classical; candidate delta is its exact
Möbius--Laplace source interface plus the one-sided linear-polylog sufficient condition.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, hostile audit
- [x] paper-prove `(AT2) -> (AT7) -> (AT8)`
- [ ] formalize `c`, `T`, exact identities `(AT3)`--`(AT4)`, and bridge to half-polylog decay
- [ ] prove unconditional source estimate `(AT2)`
- [ ] move dependency-closed bridge theorem to stage 2 after Lean verification
- [ ] RH from unconditional source estimate

## No-go closure

- **Exact killing theorem/mechanism:** not killed; open balanced-bilinear estimate `(AT2)`.
- **Strongest positive survivor:** dependency-closed additive-triangle-to-RH bridge
  `(AT2)`--`(AT8)`.
- **New insight:** direct half-decay is the positive Abel transform of a one-sided finite
  two-dimensional Möbius cancellation law; negative triangle excursions are harmless.
- **Status:** paper-proved bridge, Lean pending, arithmetic source open.

## Log

- 2026-07-22 — Created after corpus and primary-literature searches found no matching additive
  triangle criterion; bridge and hostile audit completed on paper.

## Lean milestone: one-sided linear source theorem

Formal module:
`formal/GaloisForLFunctions/RHTower/MobiusLaplaceAdditiveTriangle.lean`.

Verified declarations now include:

- `mobiusDiscreteLaplaceTransform_sq_eq_tsum_additiveConvolution`: exact Cauchy square `(AT3)`;
- `mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_mul_tsum_additiveTriangle`: unconditional
  Abel identity `(AT4)`, including absolute convergence from a quadratic elementary majorant;
- `MobiusAdditiveTriangleLinearUpperBound`: the `q=0` one-sided source condition
  `T(N) <= C(N+1)`;
- `mobiusAdditiveTriangleLinearUpperBound_implies_halfDecay`: one-sided linear control implies
  exact `O(x^-1/2)` Möbius--Laplace decay;
- `mobiusAdditiveTriangleLinearUpperBound_implies_riemannHypothesis_and_simpleZeros`: source
  condition implies RH and simplicity of every critical-line zeta zero.

The proof never assumes a lower or absolute bound on `T(N)`.  It takes real parts of `(AT4)`, uses
that the left side is `|Phi(x)|^2`, and compares positive Abel weights against
`sum (N+1)r^N=(1-r)^-2`.  This formally certifies the strongest clean special case of the candidate
new interface.

General fixed `q` still needs Lean formalization of the elementary numerical estimate `(AT6)`.
Arithmetic endpoint `T(N) <= C(N+1)` remains unproved; therefore this is not an unconditional RH
proof.

### Gate update

- [x] formalize `c`, `T`, `(AT3)`, `(AT4)`, convergence, and the complete `q=0` bridge
- [x] prove in Lean that one-sided—not absolute—linear control implies RH and simple zeros
- [ ] formalize general logarithmic Abel estimate `(AT6)`
- [ ] prove unconditional one-sided linear or linear-polylog source estimate

- 2026-07-22 — Lean-verified exact Abel bridge and complete one-sided `q=0` source theorem.

## Lean milestone: full fixed-polylog source theorem

Formal modules:

- `formal/GaloisForLFunctions/RHTower/MobiusLaplaceAdditiveTrianglePolylog.lean`;
- `formal/GaloisForLFunctions/RHTower/MobiusAdditiveTrianglePolylogUniversalityLaw.lean`.

The general estimate `(AT6)` is now Lean-verified.  Core declarations:

- `tsum_natSucc_mul_logPow_exp_le`: explicit
  `sum (N+1) log(N+2)^p exp(-Nx) = O_p(x^-2(1+|log x|)^p)` bound;
- `norm_sq_mobiusDiscreteLaplaceTransform_le_one_sub_exp_mul_tsum_of_triangleUpper`: generic
  one-sided triangle-majorant comparison for the real Laplace square;
- `mobiusAdditiveTriangleLinearPolylogUpperBound_implies_halfPolylogDecay`: `(AT2) -> (AT7)` for
  every fixed `q`;
- `MobiusAdditiveTrianglePolylogSourceUniversalCertificate`: one retained source witness packages
  RH, all reciprocal-square source charts, multiplicity at most `q+1`, and the sharp local
  coefficient cap `C q!` at maximal multiplicity;
- `mobiusAdditiveTriangleLinearPolylogUpperBound_implies_sourceUniversalCertificate`: `(AT2)`
  supplies that complete certificate.

Proof retains exact logarithmic exponent.  It uses
`log(N+2) <= 1+|log x|+Nx`, absorbs `(Nx)^p` by halving exponential decay, and sums the resulting
first geometric moment.  No epsilon power loss occurs.

Literature refresh found Misra--Saha--Sharma, *On additive convolution sum of arithmetic functions
and related questions*, arXiv:2502.08305v2 (2026).  Its general additive-convolution theorem assumes
absolutely convergent Ramanujan expansions; no application to the Möbius self-convolution or the
cumulative one-sided triangle `(AT2)` is stated.  This is a relevant neighboring source, not a
priority collision.

### Superseding gate update

- [x] formalize general logarithmic Abel estimate `(AT6)`
- [x] formalize complete fixed-`q` bridge `(AT2) -> (AT7) -> (AT8)`
- [x] connect the retained source constant to reciprocal-square universality and the sharp
  maximal-order local zeta coefficient
- [ ] prove unconditional one-sided linear-polylog source estimate `(AT2)`

- 2026-07-22 — Full fixed-polylog bridge and strongest current downstream universal certificate
  Lean-verified; only finite arithmetic source remains.
