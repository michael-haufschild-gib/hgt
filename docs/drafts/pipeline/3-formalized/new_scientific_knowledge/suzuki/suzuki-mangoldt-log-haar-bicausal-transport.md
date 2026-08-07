# Suzuki Mangoldt log-Haar bi-causal transport

- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-mangoldt-log-haar-bicausal-transport-formalized.md`
- **Type:** positive transport / frontier localization
- **Status:** `[PROVED HERE] [SOURCE-SPECIFIC] [NOVELTY NOT EXTERNALLY CERTIFIED]`
- **Computation used:** no
- **RH used:** no
- **Lean:** `SuzukiMangoldtLogHaarTransport.lean`

## Frontier attacked

S66 writes Suzuki's complete prime wall as atoms

```text
w_n delta_(tau_n),   w_n = 2 Lambda(n)/n,   tau_n = 2 log n,
```

sampling the positive archimedean channel `A_a`.  The missing step is a source-derived positive
transport from these atoms to Lebesgue lag mass.  Universal sampling is impossible; arbitrary
fitted cells would merely rename RH.

## Literature audit

Ramaré--Zuniga Alterman, *Möbius function and primes: an identity factory with applications*,
arXiv:2312.05138v3 (2026), prove

```text
sum_(d<=X) Lambda(d)/d <= log X,   X>=1.                 (C)
```

Therefore `(C)` is not claimed as new.  Corpus contained only the weaker absolute-constant
Mertens bound.  New result below is the transport geometry obtained by combining `(C)` with an
endpoint-retaining factorial lower law and the actual Suzuki lag normalization.

## Exact theorem

Let

```text
F_n = 2 sum_(d<=n) Lambda(d)/d,
tau_n = 2 log n.
```

First, without `(C)`, divisor swapping and the exact endpoint form

```text
n log n - n + 1 <= sum_(m<=n) log m
```

give

```text
tau_n - 2 + 2/n <= F_n.                                  (1)
```

The logarithmic step inequality

```text
log n - log(n-1) <= 1/(n-1)
```

then cancels the endpoint `2/(n-1)` in `(1)` and gives

```text
tau_n - 2 <= F_(n-1).                                    (2)
```

Under known capacity theorem `(C)`, `F_n<=tau_n`.  Hence two canonical cells

```text
P_n = (F_(n-1), F_n],
Q_n = (F_(n-1)+2, F_n+2]
```

satisfy

```text
length(P_n)=length(Q_n)=w_n,
P_n subset (tau_n-2,tau_n],
Q_n subset (tau_n,tau_n+2].                              (3)
```

Both families are pairwise disjoint because they are consecutive intervals in cumulative-mass
coordinates.  Thus they use Lebesgue capacity with multiplicity at most one.

For every continuous profile `f`:

```text
f decreasing on [tau_n-2,tau_n]
  => w_n f(tau_n) <= integral_(P_n) f,

f increasing on [tau_n,tau_n+2]
  => w_n f(tau_n) <= integral_(Q_n) f.                    (4)
```

For Suzuki's actual channel, the left side is exactly

```text
2 Lambda(n)/sqrt(n) R_(L,a)(log n),                       (5)
```

not a surrogate atomic source.

## Fully unconditional in-tree fallback

Until `(C)` itself is formalized, existing formal Mertens theorem yields the same construction
with radius

```text
R = 2(log 4+4),   W = 2+2R.
```

Shifted cells

```text
(F_(n-1)-R,F_n-R],
(F_(n-1)+R+2,F_n+R+2]
```

are still exact-mass, pairwise-disjoint, and lie respectively in
`(tau_n-W,tau_n]` and `(tau_n,tau_n+W]`.  This part is fully unconditional in Lean.

## New frontier localization

For a unimodal lag profile with turning point `c`, every atom whose future cell stays left of `c`
or whose past cell stays right of `c` is discharged by `(4)`.  Therefore all nontrivial transport
debt is confined to the bounded turning layer

```text
|tau_n-c| < 2                                             (sharp paper theorem)
```

or `|tau_n-c|<W` in the currently assumption-free Lean realization.

This is a genuine reduction of the frontier: monotone bulk atoms are no longer part of the RH
problem.  Remaining problem is a finite-width, aperture-moving seam splice.  Its atom count grows,
so "finite width" does not make it elementary; it identifies exact local source where RH-bearing
prime irregularity survives.

## Scientific verdict

- `[KNOWN]` log-Haar capacity `(C)`.
- `[PROVED HERE]` endpoint-corrected lower law `(1)` and predecessor law `(2)`.
- `[PROVED HERE]` bi-causal exact-mass cells `(3)`.
- `[PROVED HERE]` monotone branch discharge `(4)` and exact Suzuki weld `(5)`.
- `[OPEN]` splice left/future and right/past partitions through moving turning layer without
  double use of Lebesgue capacity, while retaining completed Gamma boundary charge.

