# Defect-neutral positive-power Abel tomography

- **ID:** `defect-neutral-positive-power-abel-tomography`
- **Stage:** 1-in-progress
- **Type:** MASTER THEOREM GENERALIZATION / SHARP SCALE / POWER-SPECTRUM UNIVERSALITY
- **Scientific status:** `[PAPER-PROVED] [LEAN IN PROGRESS] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`

## Exact strengthened theorem

Let `(c_i,z_i)` be a bounded absolutely summable atomic presentation with real pointed moments,
nonnegative orientation on occupied real nodes, and cofinally vanishing transverse defect

```text
transverseDefect(z_i) = |z_i| - Re(z_i) -> 0.
```

Repeated nodes and cancelling fibres are allowed. Pass canonically to the nonzero aggregate
support. Then every clause of intrinsic scale-covariant Bernstein--Abel tomography holds, and at
every scale `R>M` containing a transverse occupied node,

```text
E_(p,N)(R)^(1/N) -> B(R)^p
```

for every real `p>0`. Thus one sharp threshold `R>M` controls the quadratic half-order, the Abel
boundary, every positive power spectrum, the exact radical, and the quantitative recession.

## Paper proof

### 1. Transverse neutrality implies confocal neutrality

Put

```text
deltaInf(z) = |z| - Re(z),
delta_R(z) = |z| + |R-z| - R.
```

Write `z=x+iy`, `r=|z|`, and assume `r<=M<R`. Rationalization gives

```text
delta_R(z)-deltaInf(z)
  = sqrt((R-x)^2+y^2)-(R-x)
  = y^2/(sqrt((R-x)^2+y^2)+(R-x)).
```

The denominator is at least `2(R-M)`. Moreover

```text
y^2 = (r-x)(r+x) = deltaInf(z)(r+x)
    <= 2M deltaInf(z).
```

Therefore

```text
0 <= delta_R(z)
   <= deltaInf(z) + M/(R-M) deltaInf(z)
   = R/(R-M) deltaInf(z).
```

The affine Bernstein amplitude after inverse scaling is exactly

```text
1 + delta_R(z)/R.
```

Multiplication by the fixed positive constants in the preceding bound proves cofinite convergence
of every normalized amplitude to one. This is precisely the compactness input used to extract a
finite superunit maximal packet. No convergence of the nodes to the origin is needed.

### 2. Aggregate descent

Choose one raw representative of every nonzero aggregate fibre. Distinct aggregate fibres have
distinct representatives, so the representative map preserves the cofinite filter. The raw
transverse-defect limit therefore descends to the aggregate source by composition. Absolute
summability, moments, boundedness, and real orientation descend by the already proved fibrewise
regrouping theorem.

### 3. Sharp quadratic selection

For `R>M`, every normalized aggregate node lies in the open unit disk. A real nonnegative node in
that disk has amplitude one, so every maximal superunit node is nonreal. Cofinal amplitude
neutrality makes the superunit maximum finite and source-attained. The complete reflected-fibre
classification gives a strict quadratic cross gap for every pair of distinct maximal nodes.
Consequently

```text
E_(2,N)(R) ~ L(R) B(R)^(2N)/sqrt(N),  L(R)>0,
```

and Abelian transfer gives the square-root boundary.

### 4. Every positive power has the same sharp spectral radius

Let `a_(N,k)` be the selected coefficient vector, `d_N=N+1`,

```text
E_(p,N) = sum_k |a_(N,k)|^p,
Q_N = E_(2,N),
L1_N = sum_k |a_(N,k)|.
```

For every `p>0`, each coefficient is bounded by `L1_N`, so

```text
E_(p,N) <= d_N L1_N^p.
```

The atomic binomial theorem gives `L1_N <= C B^N`, with
`C=sum_u |cHat(u)|`. Hence the upper exponential rate is at most `B^p`.

For the lower rate put `q=p/2`. If `0<q<=1`, concavity gives

```text
Q_N^q <= E_(p,N).
```

If `q>=1`, the finite power-mean inequality gives

```text
Q_N^q <= d_N^(q-1) E_(p,N).
```

The quadratic half-order law implies, eventually,

```text
Q_N >= (L(R)/2) B^(2N)/sqrt(N).
```

Thus `E_(p,N)` is bounded below by a positive multiple of `B^(pN)` divided by a fixed real power
of `N+1`. Polynomial losses disappear after taking the `N`th root. Squeezing proves

```text
E_(p,N)^(1/N) -> B^p
```

for every `p>0` at the same sharp scale `R>M`.

### 5. Remaining clauses

The global moment chart, exact atomic realization, radical, finite-scale Abel transport, explicit
recession error, and both first recessions use only boundedness, summability, and nonemptiness.
They are unchanged. Combining Steps 1--4 with those clauses proves the strengthened master
theorem.

## Hostile audit

- The positive-power transfer is a standard finite-dimensional power-mean mechanism; by itself it
  is a `[BRIDGE]`, not a novelty claim.
- The scientific strengthening is the conjunction: the source class expands from nodes converging
  to one point to sources becoming cofinally transverse-neutral along the full positive segment,
  while the sharp selector simultaneously becomes independent of every positive power exponent.
- The theorem does not estimate the Xi radical to zero and does not imply RH.
- The threshold remains sharp uniformly: at `R<M`, an allowed positive real endpoint can itself
  have superunit amplitude.

## Lean obligations

- [ ] pointwise linear confocal/transverse defect bound
- [ ] cofinite amplitude-neutrality transport
- [ ] neutral-amplitude maximal-packet selector
- [ ] aggregate descent of transverse-defect neutrality
- [ ] abstract positive-power transfer from quadratic half-order plus `l1` envelope
- [ ] sharp inverse-scale `p>0` spectrum theorem
- [ ] strengthened single master theorem
- [ ] direct leaf checks and ordinary-axiom audit

## Open RH core

```text
Delta_Xi = 0.
```
