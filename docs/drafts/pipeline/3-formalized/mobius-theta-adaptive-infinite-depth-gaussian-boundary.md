# Adaptive prime-normal infinite-depth Gaussian boundary

- **ID:** `mobius-theta-adaptive-infinite-depth-gaussian-boundary`
- **Stage:** 3-formalized
- **Type:** RANGE COMPATIBILITY / SOURCE BOUNDARY COMPLETION
- **Status:** `[LOCAL-RESEARCH] [PAPER PROVED] [LEAN PROVED] [UNCONDITIONAL]`
- **Parents:**
  `deninger-meyer-reflected-gaussian-prime-gamma-cauchy-landing.md`,
  `mobius-theta-adaptive-prime-normal-horizon-intertwiner.md`
- **Intended Lean module:**
  `../../../../formal/GaloisForLFunctions/RHTower/MobiusThetaAdaptiveInfiniteDepthGaussianBoundary.lean`

## 1. Exact source object

Fix one ordinary prime label `p`.  For divisor copy `q`, let `N(q)` be the already constructed
honest adaptive depth, and put

```text
N_K(q) = (K+1) N(q),
m_K(p,q) = 8 p N_K(q).
```

The inequality `1/2 <= N(q) Re(s_q)` implies the same inequality at `N_K(q)`, so every finite
`K` remains inside the literal prime-normal convergence chamber.  Let

```text
A_K(p,q) = -1 + sum_{j>=0} c_{p,m_K(p,q),q}(j)
H_K(p)(q) = A_K(p,q) h_ref(q),
```

where `c` is the exact strict Möbius--theta spectral tail.  Thus `H_K(p)` is coefficient
augmentation of an honest adaptive prime-normal codiagonal column, graded by the fixed source
Gaussian; it is not an arbitrary divisor multiplier.

## 2. Frozen conjecture

In the complete multiplicity-aware Xi Hilbert carrier,

```text
H_K(p) -> -h_ref as K -> infinity.                       (1)
```

Combining `(1)` with the two-sided prime--Gamma Cauchy landing gives

```text
integral_R B_tau(x) dx = h_ref = -lim_K H_K(p).          (2)
```

Equation `(2)` is the required common-range boundary identification between the literal
prime--Gamma source completion and the adaptive prime-normal source: both land on the same fixed
Gaussian vector, while the adaptive construction retains the unchanged prime label `p` at every
finite depth.

## 3. Dependency-closed paper proof

For fixed `p,q,j`, the exact coefficient modulus is

```text
|c_{p,m,q}(j)|
 = |mu(p+j+1)| (p/(p+j+1))^(m Re(s_q)).
```

Here `0 < p/(p+j+1) < 1`, `Re(s_q)>0`, and `m_K(p,q)->infinity`; hence every coefficient tends to
zero.  The corpus already proves the full strict tail tends to zero by a summable
exponent-independent `3/2`-power majorant.  Therefore `A_K(p,q)->mu(p)=-1` for every divisor copy.

Every finite-depth reader has modulus at most `5/4`.  Consequently

```text
|H_K(p)(q) - (-h_ref(q))|^2 <= (9/4)^2 |h_ref(q)|^2,
```

and the right side is summable.  Tannery/dominated convergence over the complete Xi divisor proves
`(1)` in `ell^2`.

## 4. Lean theorem inventory

Module:
`formal/GaloisForLFunctions/RHTower/MobiusThetaAdaptiveInfiniteDepthGaussianBoundary.lean`

- `xiAdaptivePrimeNormalScaleAtDepth_spec`: every cofinal depth stays in the literal convergence
  chamber.
- `adaptivePrimeNormalDivisorReaderAtDepth_single_eq_asymptoticMultiplier`: every finite reader is
  exactly the augmented adaptive codiagonal source column.
- `tendsto_adaptivePrimeNormalDivisorReaderAtDepth_single`: retained prime-labelled reader tends to
  its Möbius head `-1`.
- `tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn`: unconditional strong Xi-Hilbert limit
  `H_K(p) -> -h_ref`.
- `tendsto_neg_adaptivePrimeNormalInfiniteDepthHorizonColumn_eq_cauchyBoundary`: exact common
  boundary with the two-sided prime--Gamma Cauchy source integral.

Direct verification:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusThetaAdaptiveInfiniteDepthGaussianBoundary.lean
```

passes with no errors.

## 5. Anti-theatre audit

- Prime label is fixed; no unproved prime-limit or Möbius stabilization is used.
- Completion variable is actual valuation depth, already proved independent of Wold breadth.
- Every finite stage is an honest source codiagonal in its convergence domain.
- Dominating sequence is the independently source-derived Gaussian grade, not a target-selected
  interpolation weight.
- Result is a boundary-range theorem, not RH.  Remaining hard edge is transport of retained
  infinite-depth provenance through the resolved Green antidiagonal, then four-unit Gram sign.
