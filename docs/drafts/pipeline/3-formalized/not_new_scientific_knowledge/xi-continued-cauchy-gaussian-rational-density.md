# Xi continued-Cauchy Gaussian-rational density

- **ID:** `xi-continued-cauchy-gaussian-rational-density`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE-CORE COUNTABILIZATION
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiContinuedCauchyGaussianRatDensity.lean`
- **Statement:** Regular Gaussian-rational poles in the centered open strip generate exactly the
  same Xi-divisor Hilbert closure as all poles in the analytically continued prime--Gamma Cauchy
  source domain.

## Goal

Replace the uncountable continued-Cauchy source family by a concrete countable family without
changing any closure-based RH consumer.

The two-sided continued source domain first simplifies exactly to

\[
\operatorname{CCMDomain}(z)
\iff
-\frac12<\operatorname{Im}z<\frac12
\quad\text{and}\quad
\Xi_C(z)\ne0.
\]

For every point in this open set and every shrinking radius, Gaussian-rational density supplies a
rational point in the same regular source domain.  The existing norm-continuity theorem for
`xiWeilCauchyLp` then gives a sequence of rational-pole Cauchy vectors converging in the exact
multiplicity-weighted Xi `ell^2` carrier.

Consequently

\[
\overline{\operatorname{span}}
  \{k_q:q\in(\mathbb Q+i\mathbb Q)\cap U\}
=
\overline{\operatorname{span}}
  \{k_z:z\in U\},
\]

where `U` is the regular centered strip.

## Proof chain

```text
CCM two-sided domain
  = regular XiC locus in |Im z| < 1/2
  -> this domain is open
  -> every shrinking ball contains a regular Gaussian-rational pole
  -> Cauchy evaluation vectors converge in ell^2
  -> every full generator lies in the countable-source closure
  -> both closed source spans are equal.
```

No RH assumption, zero enumeration, sign condition, divisor selection, or limiting spectral
measure is used.

## Literature calibration

Kernel spans and their Hilbert closures belong to classical reproducing-kernel theory; see
[Aronszajn, Theory of Reproducing Kernels, Trans. AMS 68
(1950)](https://doi.org/10.1090/S0002-9947-1950-0051437-7).  The project contribution is the exact
compatibility with the Xi continued prime--Gamma domain and its multiplicity-exact Cauchy map.  No
scientific-novelty claim is made.

## Lean certificate

The public declarations are:

```text
ccmContinuedCauchyDomain_iff_regular_mem_centeredStrip
XiGaussianRatContinuedCauchyPoint
xiGaussianRatContinuedCauchyPoint
xiWeilGaussianRatContinuedCauchyLp
xiWeilGaussianRatContinuedCauchyAlgebraicSubspace
isOpen_xiRegularCenteredStrip
exists_gaussianRatContinuedCauchyLp_tendsto
xiWeilContinuedCauchyLp_mem_gaussianRatClosure
gaussianRatContinuedCauchy_topologicalClosure_eq
```

The module is imported by `GaloisForLFunctions.RHTower`.

## Gates

- [x] 0 → 1 in-progress: countable source-core reduction isolated
- [x] 1 → 2 fully-proven: open-domain density and norm-limit proof complete
- [x] 2 → 3 formalized: Lean module is placeholder-free and umbrella-wired
- [ ] 3 → 4 publication-ready: not proposed; this is source infrastructure
