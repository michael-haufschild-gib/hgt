# FE Orbit Quotient Half-Trace Moments

- **ID:** fe-orbit-quotient-half-trace-moments
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`, RNG-selected orbit `[w] = {w, -w}`
- **Statement:** Passing from the even completed function `Xi(w)` to the quotient function
  `Phi(z)=Xi(sqrt(z))` removes the FE sign duplication. The quotient divisor has multiplicity `m` on
  each orbit `[w]`, while the bridge reciprocal moments use the doubled trace weight `2m`. If
  `ell_k=[z^k] log Phi(z)`, then

```text
T_k = -2 k (-1)^k ell_k.
```

## Goal

Prevent a second folding error. The existing card `fe-reciprocal-folding-doubles-y-multiplicity.md`
records that the original zero sum counts both `w` and `-w`. But there is a natural even quotient
function in the variable `z=w^2`; that quotient legitimately has only one zero per orbit. A route using
the quotient function must convert back to the doubled bridge trace.

## Gates

- [x] 0 -> 1 in-progress: bridge-theorem orbit selected by RNG and checked against folding prior work
- [x] 1 -> 2 fully-proven: algebraic proof complete
- [x] 2 -> 3 formalized (2026-08-18):
  `formal/GaloisForLFunctions/RHTower/FEOrbitQuotientMoments.lean` —
  `analyticOrderAt_xiSquaredSeamEntireQuotient` (the quotient carries `m`, not `2m`),
  `analyticOrderAt_XiC_neg` (the orbit total is `2m`), `hasSum_orbitLog` (the `ℓ_k` formula) and
  `traceMoment_eq` (the dictionary `T_k = −2k(−1)^k ℓ_k`).  `lake build` green, axiom audit clean.
- [ ] 3 -> 4 publication-ready: fold into reciprocal-coordinate exposition

## Proof

[PROVED HERE]

Since `Xi(w)` is even, its Taylor expansion contains only even powers:

```text
Xi(w) = sum_{n>=0} a_n w^(2n).
```

Hence there is a unique entire quotient function

```text
Phi(z) = sum_{n>=0} a_n z^n
```

such that

```text
Phi(w^2) = Xi(w).
```

Let `w0 != 0` be a zero of `Xi` of multiplicity `m`. By evenness, `-w0` is also a zero of multiplicity
`m`. Locally,

```text
Xi(w) = (w-w0)^m (w+w0)^m h(w)
      = (w^2-w0^2)^m h(w),
```

with `h(w0) != 0` and `h(-w0) != 0`. Therefore `Phi(z)` has a zero at

```text
z0 = w0^2
```

of multiplicity `m`, not `2m`. This is the quotient divisor on the FE orbit `[w0]={w0,-w0}`.

For the nonzero quotient zeros, write the finite-order product locally/formally as

```text
Phi(z) = Phi(0) prod_[w] (1 - z/w_[w]^2)^(m_[w])
```

with the usual Hadamard interpretation for the completed infinite product. Expanding the logarithm at
`z=0` gives

```text
log Phi(z)
  = log Phi(0) - sum_{k>=1} z^k/k * sum_[w] m_[w] w_[w]^(-2k).
```

Thus

```text
ell_k := [z^k] log Phi(z)
       = -(1/k) sum_[w] m_[w] w_[w]^(-2k).
```

The bridge reciprocal moments, however, are defined by summing over the original completed divisor, or
equivalently by giving each FE orbit the trace weight `2m_[w]`:

```text
T_k = sum_[w] 2m_[w] (-w_[w]^(-2))^k
    = 2 (-1)^k sum_[w] m_[w] w_[w]^(-2k).
```

Combining the two formulas gives the dictionary

```text
T_k = -2 k (-1)^k ell_k.
```

This proves that the quotient `Phi` is the correct algebraic carrier for the orbit set, but its divisor
moments are half-trace moments until multiplied by the FE trace factor `2`.

## Computation

A finite even-product check with rational `w^2` values is archived at:

- `computations/2026-06-21-conway-fe-orbit-quotient-moments.py`
- `computations/2026-06-21-conway-fe-orbit-quotient-moments.txt`

It verifies exactly that

```text
T_k = -2 k (-1)^k [z^k] log Phi(z)
```

for `k=1,...,6`.

## Route Consequence

There are two legitimate but different objects:

```text
quotient divisor of Phi(z)=Xi(sqrt(z)): one zero per FE orbit, multiplicity m;
bridge reciprocal trace measure:          one y-atom per FE orbit, weight 2m.
```

Mixing them silently loses a factor of two in every reciprocal moment and therefore in every shifted
square-test matrix. Any proof route through `Xi(sqrt(z))`, secular coefficients, or quotient logarithmic
derivatives must apply the conversion above before comparing with `Q_0` and `Q_1`.

## Log

- 2026-06-21 -- Conway: created from bridge-theorem RNG draw `28/78`, `[w] = {w, -w}`.


## Lean formalization (stage 3)

Unconditional and axiom-clean (`propext, Classical.choice, Quot.sound` only), wired into the
`RHTower` umbrella and built:
`formal/GaloisForLFunctions/RHTower/FEOrbitQuotientMoments.lean`.

### The quotient function

The entire square-root quotient already exists in the corpus:
`RHTower.xiSquaredSeamEntireQuotient` with `xiSquaredSeamEntireQuotient_sq : Q (z²) = XiC z` and
`differentiable_xiSquaredSeamEntireQuotient` (`RHTower/XiSquaredSeamCassiniSource.lean`).  It is
reused verbatim; nothing about the existence of `Φ` is rebuilt.

### The divisor count — `m`, not `2m`

```text
analyticOrderAt_sq_sub (hw : w₀ ≠ 0) : analyticOrderAt (fun w => w² − w₀²) w₀ = 1

analyticOrderAt_xiSquaredSeamEntireQuotient (hw : w₀ ≠ 0) :
  analyticOrderAt xiSquaredSeamEntireQuotient (w₀²) = analyticOrderAt XiC w₀

analyticOrderAt_XiC_neg (w₀ : ℂ) : analyticOrderAt XiC (−w₀) = analyticOrderAt XiC w₀
```

The first two run through `AnalyticAt.analyticOrderAt_comp`: squaring is a local isomorphism away
from the origin, so the composition order is the quotient order times one.  The third is the card's
evenness step, so the orbit `{w₀, −w₀}` carries total `2m` while the quotient carries `m`.

### The log coefficients and the dictionary

```text
orbitProduct m zr s z = ∏ j ∈ s, (1 − z/z_j)^{m_j}
orbitLog     m zr s z = ∑ j ∈ s, m_j · log (1 − z/z_j)
exp_orbitLog          : exp (orbitLog …) = orbitProduct …          (so it *is* a logarithm)
orbitLog_zero         : orbitLog … 0 = 0

ell        m zr s k = −(1/k) · ∑ j ∈ s, m_j · z_j^{−k}
traceMoment m zr s k = ∑ j ∈ s, 2·m_j · (−z_j^{−1})^k

hasSum_orbitLog (hz : ∀ j ∈ s, ‖z/z_j‖ < 1) :
  HasSum (fun k => ell m zr s k · z^k) (orbitLog m zr s z)

traceMoment_eq (hk : k ≠ 0) :
  traceMoment m zr s k = −2·k·(−1)^k · ell m zr s k
```

`hasSum_orbitLog` is the card's expansion `log Φ(z) = log Φ(0) − Σ_k z^k/k · Σ_[w] m_[w] w^{−2k}`,
obtained from `Complex.hasSum_taylorSeries_log` factor by factor.  Defining the logarithm as the sum
of the branch logarithms — and *proving* it exponentiates to the product — removes the branch-cut
question entirely; `orbitLog_zero` fixes the normalization the card uses.

`traceMoment_eq` is the dictionary: the bridge weight is `2m` per orbit, the quotient log
coefficient is the half-trace, and the conversion factor is `−2k(−1)^k`.  This is exactly the
conversion the route consequence demands before any comparison with `Q₀`, `Q₁`.

**Stage:** 3-formalized.
