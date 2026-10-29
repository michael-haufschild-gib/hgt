# Fixed polynomial ideals preserve integrality precision

- **ID:** asrp-fixed-polynomial-ideal-preserves-integrality-precision
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ASRP open topic 1, constructive integrality and forced rational zeros.
- **Statement:** For each nonzero `Q ∈ ℤ[X]`, the least positive Nair integral among multiples of `Q` of degree at most `N-1` lies between `1/d_N` and `C_Q/d_N` for all sufficiently large `N`, with `C_Q` independent of `N`.

## Goal

Give the exact precision of the integrality floor after imposing any fixed polynomial vanishing pattern. If proved, fixed rational zeros and fixed multiplicities cost only a bounded additive logarithmic error; their presence alone does not change the integrality exponent or its square-root criterion.

## Gates

- [x] Source and attack identified; corpus search found the unrestricted lattice only.
- [ ] Dependency-closed proof, including lattice generation and prime-adic bounds.
- [ ] Exact theorem formalized and audited.

## Approach

Let `m=deg Q`, `c=leadingCoeff Q`, and let `g_N` be the gcd of the integer moments `d_N ∫ x^j Q`, `0≤j≤N-m-1`. Bézout gives the constrained floor `g_N/d_N`.

For a prime `p`, write `a=v_p(d_N)` and `b=v_p(d_m)`. If `a>v_p(c)+b`, the moment with `j=p^a-m-1` has a unique dominant denominator `p^a`: its top coefficient contributes valuation `v_p(c)-a`; every lower denominator has valuation at most `b`. Thus `v_p(g_N)≤v_p(c)`.

Otherwise use one fixed positive moment, `∫Q²=K/d_(2m+1)`, to obtain `v_p(g_N)≤a+v_p(K)≤v_p(c)+b+v_p(K)`. These bounds suggest `g_N` divides `|c| d_m |K|`, uniformly once `N≥2m+1`.

## Audit obligations

Verify zero-degree and small-prime cases; show the selected moment is within the degree horizon; prove all moment valuations and the gcd attainment without hiding any input. The fixed moment is a linear combination of the allowed `Q X^j`, not an additional assumption. Hermite interpolation alone does not establish this result: rational evaluations can introduce exponentially growing denominators.

## Novelty boundary

The unrestricted lattice and the sup-norm forced-root theorem already exist. This conjecture concerns the whole ideal `Q ℤ[X]` with a uniform loss independent of the horizon, not sharper constants for an existing auxiliary.
