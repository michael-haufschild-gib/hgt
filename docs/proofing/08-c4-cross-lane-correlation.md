# C4 Proof Attempt: Divergent Cross-Lane Correlation Length

Source: `docs/consolidated/08-conjectures-required.md` §1.

Claim status: `[CONJECTURE]`.

## Target Claim

The true carrier has a cross-sigma correlation length `xi_sigma(sigma,t)` that
is large or divergent in the critical strip and `O(1)` for `sigma > 1`, because
Cauchy-Riemann coupling links neighboring sigma-lanes while finite Euler lanes
factorize per lane.

## Proof Attempt

Let `F(s)` be a holomorphic nonvanishing weld field on a zero-free strip
rectangle, and write

```text
u(sigma,t) = log |F(sigma + i t)|,
v(sigma,t) = arg F(sigma + i t).
```

Then `u` and `v` are harmonic conjugates:

```text
partial_sigma u = partial_t v,
partial_t u = -partial_sigma v.                            (1)
```

Equation `(1)` proves local lane coupling. A perturbation in one sigma-lane
cannot be varied independently of nearby lanes if it is the boundary trace of a
single holomorphic field. Cauchy estimates give, for a smaller rectangle
`R' compactly contained R`,

```text
sup_R' |nabla u| + |nabla v| <= C_R sup_R |u + i v|.
```

Thus local cross-lane coherence is forced by analyticity wherever the chosen
log branch exists.

## Weakened Theorem Proved Here

**Theorem C4-W.** On a zero-free rectangle admitting a holomorphic logarithm of
`F`, sigma-lane and t-lane variations are not independent; they satisfy the
Cauchy-Riemann coupling `(1)`, with local derivative bounds by Cauchy estimates.

## Why This Does Not Prove C4

Local analytic coupling is far weaker than a divergent correlation length. It
does not distinguish true `xi` from any holomorphic surrogate with the same zero
set or comparable boundary data. It also does not produce the q70-style spectral
gap for the indicator kernel

```text
K_q(sigma,sigma') =
  Corr(1_{Delta(sigma+it)>q}, 1_{Delta(sigma'+it)>q}).
```

The conjecture needs a lower bound on a global correlation length or on the
leading spectrum of such a kernel. Cauchy-Riemann only gives local compatibility.

## Attack As False

If a correct-zero FE-exact fake has the same local zero geometry, then its
`log |F|` will satisfy the same harmonic coupling near those zeros. In that
case the observed `xi_sigma` could be zero-spacing content rather than native
transport content. This is exactly the corpus kill criterion.

## Missing Input

1. A precise definition of `xi_sigma`.
2. A theorem converting holomorphic coupling plus the Gamma/prime split into a
   diverging correlation-length lower bound.
3. A surrogate-separation theorem showing zero-spacing alone cannot reproduce
   the same kernel spectrum.
