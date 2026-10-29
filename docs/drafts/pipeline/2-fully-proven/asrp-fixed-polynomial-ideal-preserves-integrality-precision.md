# Fixed polynomial ideals preserve integrality precision

- **ID:** asrp-fixed-polynomial-ideal-preserves-integrality-precision
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ASRP open topic 1, constructive integrality and forced rational zeros.
- **Statement:** For each nonzero `Q ∈ ℤ[X]`, a fixed positive integer `C_Q` satisfies: for every `N≥2 deg(Q)+1`, some multiple of `Q` of degree at most `N-1` has Nair integral exactly `C_Q/d_N`. The least positive integral consequently lies between `1/d_N` and `C_Q/d_N`.

## Goal

Give the exact precision of the integrality floor after imposing any fixed polynomial vanishing pattern. If proved, fixed rational zeros and fixed multiplicities cost only a bounded additive logarithmic error; their presence alone does not change the integrality exponent or its square-root criterion.

## Gates

- [x] Source and attack identified; corpus search found the unrestricted lattice only.
- [x] Dependency-closed constructive paper proof.
- [ ] Exact theorem formalized and audited.

## Proof [PROVED HERE]

Write `Q=Σ_(i=0)^m a_i X^i` with `a_m≠0`. Put `H=d_(2m+1) Q²` and `K=∫H`. Integrality gives `K∈ℤ`; the square of a nonzero real polynomial has positive integral on `(0,1)`, so `K>0`. Also `Q∣H` and `deg H≤2m`.

For `j≥0`, let `d=j+m+1` and `D_j=∏_(i<m)(j+i+1)`. Then

`D_j ∫ X^j Q = Z_j + A/d`, with `Z_j∈ℤ` and the fixed nonzero integer `A=a_m ∏_(i<m)(i-m)=a_m(-1)^m m!`.

Indeed, the lower denominators divide `D_j`, and `D_j≡∏_(i<m)(i-m) mod d`. Therefore

`P_j = K D_j Q X^j - Z_j H`

is divisible by `Q`, has degree at most `max(m+j,2m)`, and has integral `K A/d`.

Set `C_Q=K |A| d_m>0`. At a horizon `N≥2m+1`, every `1≤k≤N` has a degree-`≤N-1` multiple of `Q` with integral `C_Q/k`: for `k>m`, use `sign(A)d_m P_(k-m-1)`; for `k≤m`, use `(|A|d_m/k)H`, whose coefficient is an integer because `k∣d_m`.

The existing reciprocal Bézout theorem gives integers `b_k` with `Σ_(k=1)^N b_k/k=1/d_N`. Sum the constructed multiples with these coefficients. Their sum remains divisible by `Q`, remains within the degree horizon, and has integral `C_Q/d_N`. The lower floor `1/d_N` is the existing integrality theorem. The zero-degree case uses empty products and `d_0=1`, so the construction still applies.

## Precision consequence

The constrained log-floor differs from `psi(N)` by a bounded amount. Thus each constrained Siegel/Liouville half at an admissible scale is equivalent to its unrestricted half. In particular both square-root criteria remain RH-equivalent. The construction preserves signed integrals; it does not supply a height, sup-norm, or absolute-integral ceiling.

## Novelty boundary

The unrestricted lattice and the sup-norm forced-root theorem already exist. This conjecture concerns the whole ideal `Q ℤ[X]` with a uniform loss independent of the horizon, not sharper constants for an existing auxiliary.
