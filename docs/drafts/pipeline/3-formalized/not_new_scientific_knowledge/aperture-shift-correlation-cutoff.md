# Exact logarithmic-aperture shift cutoff

- **ID:** `aperture-shift-correlation-cutoff`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** A function supported in `[-a,a]` has identically zero correlation with every
  translate by `t>2a`. In particular, support in `[-log lambda,log lambda]` makes the dilation
  correlation at `log q` exactly zero for `q>lambda^2`.

## Formal statement

The module `GaloisForLFunctions.RHTower.ApertureShiftCutoff` proves:

```text
intervalShiftProduct_eq_zero
intervalShiftCorrelation_eq_zero
intervalNegativeShiftProduct_eq_zero
intervalNegativeShiftCorrelation_eq_zero
logApertureDilationCorrelation_eq_zero
logApertureReverseDilationCorrelation_eq_zero
```

The last theorem has the source-pure hypotheses

```text
1 < lambda,
lambda^2 < q,
support f subset [-log lambda, log lambda],
```

and concludes, for both choices of shift,

```text
integral conj(f(x))*f(x+log q) dx = 0.
integral conj(f(x))*f(x-log q) dx = 0.
```

No integrability assumption is needed because the integrand is proved pointwise zero first.

## Route consequence

The CCM finite-aperture prime form has no terms with `q>lambda^2`. Since
`c=2*pi*lambda^2`, each visible prime shift satisfies `q=O(c)`. In the radial Poisson expansion,
however, a shifted component has index `k=q*n` with `n` unbounded. Thus this theorem does not
truncate the radial first row at `k<=lambda^2`.

For the low subseries `k<=lambda^2`, a Dunster remainder bounded by `C*d_1/(c*k)` accumulates as

```text
d_1/c * sum_(q<=lambda^2) log(q)/q
  = O(d_1*log(c)^2/c)
  = o(d_1/lambda).
```

This proves low-index summability only. The high truncated-divisor weighted radial tail remains the
gate isolated in
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-prime-shift-radial-index-separation-law.md`.
The formal theorem itself is
unchanged: it is exactly a shift cutoff, not a radial-harmonic cutoff.

## Verification

- The producing module builds with the repository toolchain.
- All six declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The umbrella `GaloisForLFunctions.RHTower` imports the module.

## Gates

- [x] support-disjointness statement proved on paper
- [x] translation correlation theorem formalized
- [x] logarithmic dilation specialization formalized
- [x] reverse logarithmic dilation specialization formalized for the even Weil form
- [x] exact target build and axiom audit passed
- [x] prime-shift and radial-harmonic cutoff scopes separated
- [ ] connect the finite cutoff to the exact CCM form once that operator is represented in Lean
