# Deninger failure-nerve singular Cartier metric

- **ID:** `deninger-failure-nerve-singular-cartier-metric`
- **Status:** formalized finite/source-local core in Lean 4; unconditional; Route L remains open
- **Paper proof:**
  `new_scientific_knowledge/deninger/deninger-failure-nerve-singular-cartier-metric.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerFailureNerveSingularCartierMetric`

## Formal result

For the actual local Euler gauge

```text
G_(p,m)(s) = (1-p^(-s))/(1-p^(-(m+1)s)),
Q_(p,m)(s) = G_(p,m)(s)/sqrt(G_(p,m)(1)),
```

the module proves throughout `Re(s)>0` that `G` and `Q` are nonzero and that
the norm-based positive normalizer is exactly the real paper normalization.
It also identifies

```text
lambda_(p^m)(s) = p^(-m(s-1/2)),
Rhat_(p,m)(s) = lambda_(p^m)(s) Q_(p,m)(s).
```

For every finite prime face `F`, it constructs

```text
Q_(F,m)(s) = product_(p in F) Q_(p,m)(s),
h_(F,m)(s) = |Q_(F,m)(s)|^(-2)
```

and proves exact edge purification

```text
h_(F union {p},m) |Rhat_(p,m)|^2
  = h_(F,m) |lambda_(p^m)|^2.
```

The empty-face normalization and these edge equations uniquely determine
`h` on every finite face.  Lean exposes a strengthening of the paper theorem:
positivity of a competing real weight is unnecessary for uniqueness.

The induced squared incidence gain is exactly `|lambda_(p^m)|^2`; hence its
source-inverse/analytic-dagger mate curvature is unconditionally

```text
K_(p^m)(s)
  = |lambda_(p^m)(s)|^(-2) - |lambda_(p^m)(s)|^2.
```

This connects actual finite failure-nerve geometry to the independently
formalized Deninger tensor-square curvature, rather than only matching scalar
formulas.

## Singular Cartier landing

The same module proves generic analytic infrastructure needed by the cofinal
Xi limit.  If

```text
f(u) = (u-rho)^d g(u),   g(u) -> c != 0,
```

then the inverse-square metric satisfies

```text
|u-rho|^(2d) weight |f(u)|^(-2)
  -> weight |c|^(-2),
```

with strictly positive limit for positive `weight`.  Thus pole order is
exactly twice analytic multiplicity and top-conormal renormalization is
finite and nonannihilating.

## Boundary of formal claim

Actual Mertens/Euler cofinal convergence and Xi normal-cone convergence are
not reconstructed or assumed in this module.  Their paper-level composition
with the finite theorem yields the Xi Cartier metric, but formalizing those
analytic limits remains separate infrastructure.  No antipode--dagger
identification, source Bianchi law, Xi-zero location, or RH theorem follows.

## Verification

- scratch proofs using repository toolchain: passed;
- direct `lake env lean` on module: passed;
- umbrella import: `GaloisForLFunctions.RHTower`;
- targeted module build: passed;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- repository formal lint: passed.
