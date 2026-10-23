# Product residue profiles and the exact smoothing cost

- **ID:** goldbach-product-residue-profile
- **Stage:** 3-formalized
- **Type:** BRIDGE; finite arithmetic, no scientific novelty claim
- **Source:** [failed smoothing candidate](../../5-failed/goldbach-balanced-product-smoothing.md)
- **Lean:** [ProductResidueProfile.lean](../../../../../formal/GaloisForLFunctions/goldbach/ProductResidueProfile.lean)

## Exact statements

For a positive modulus q, let ν_q(r) count pairs `(a,b) mod q` with
ab=r, and let ψ_q be the canonical additive character. Then

    Σ_r ν_q(r) ψ_q(hr) = q gcd(q,h),
    ν_q(r) = Σ_h gcd(q,h) ψ_q(−hr),
    E_q := Σ_r(ν_q(r)−q)² = q Σ_h gcd(q,h)² − q³.

Moreover `E_q=0` exactly when q=1. For the actual interval `(qk,2qk]`,
the number of ordered products in residue r is exactly `k²ν_q(r)`.
A positive number of complete q-step averaging periods replaces ν_q by
its constant mean q.

For positive q,L,h, put X=qk and H=qh. Encode an integer n by
`(n mod q, floor(n/q) mod L)`. Let D_c(r,t) count the actual ordered
products in `(X,2X]²` after shifting their product by c, with this label.
Define the real row

    F(r,t) = D_H(r,t) − H⁻¹Σ_(0≤j<H)D_(H−j)(r,t).

There are no assumptions on its masses: counting proves

    Σ_t F(r,t) = k²(ν_q(r)−q).

Writing m_r(u)=L⁻¹Σ_t u(r,t), the exact energy and signed pairing are

    Σ_(r,t)F(r,t)²
      = (k⁴/L)E_q + Σ_(r,t)(F(r,t)−m_r(F))²,

    Σ_(r,t)F(r,t)g(r,t)
      = k²Σ_r(ν_q(r)−q)m_r(g)
        + Σ_(r,t)(F(r,t)−m_r(F))(g(r,t)−m_r(g)).

The second identity holds for every real row g. It isolates its periodic
mean and the exact compensated covariance; it does not estimate either.

The choice `L=4qk²+h+1` contains every shifted product before reducing
the quotient modulo L: each label has integer representative below qL.
For q=2, k=2j², h=j, j≥1, one has X=4j² and H=2j=√X, and

    Σ_(r,t)F(r,t)² ≥ (E_2/34)X²,       E_2>0.

Thus ordinary product smoothing cannot have squared error o(X²), even
at the square-root window. This is a theorem about the finite count row
itself. The equivalent infinite integer ℓ² formulation and its asymptotic
contradiction are paper corollaries; no Lean limit theorem for that
infinite-space notation is claimed.

## Dependency-closed paper proof

For fixed a, orthogonality gives `Σ_b ψ_q(hab)=q` when ha=0 and zero
otherwise. The kernel of multiplication by h on the cyclic group of
order q has gcd(q,h) elements. This proves the Fourier formula. Finite
Fourier inversion gives the reconstruction, and Parseval gives
`Σ_rν_q(r)²=qΣ_h gcd(q,h)²`. Since `Σ_rν_q(r)=q²`, subtracting the
constant mode yields the energy formula.

If E_q=0, every ν_q(r) equals q. For q>1 its Fourier coefficient at
frequency 1 would then be zero, contradicting the coefficient q from
the gcd formula. For q=1 there is a single fibre, of size one. This
proves the exact vanishing classification.

Every complete q-block contains each residue once. Two intervals of
length qk therefore give k² copies of the full residue square. A
complete-period averaging window visits each residue equally often,
so its average is q. The quotient label assigns each product to one
column independently of its residue. Consequently
`Σ_tD_c(r,t)=k²ν_q(r−c)`, and the displayed mass identity for F follows.

For any two real L-entry rows u,v, expanding their centered product gives

    Σ_tu_tv_t = L m(u)m(v) + Σ_t(u_t−m(u))(v_t−m(v)).

Summing this identity over r and substituting the proved mass of F gives
both exact decompositions. The residual squared norm is nonnegative,
yielding the lower bound. Every shifted product is at most
`4X²+H<q(4qk²+h+1)`, proving absence of wraparound at the specified width.

For q=2,k=2j²,h=j, the width is `32j⁴+j+1≤34j⁴`. Hence
`k⁴/L≥16j⁸/(34j⁴)=X²/34`. Multiplication by E_2>0 gives the stated
square-root-window obstruction. Only finite sums, cyclic-group counting,
character orthogonality and real algebra enter the proof.

## Lean declarations

Namespace `GaloisForLFunctions.Goldbach`:

- `productZeroMultiplicity_eq_gcd`
- `productResidueCount_fourier`
- `productResidueCount_eq_gcdFourier`
- `productResidueCenteredEnergy_eq_gcd`
- `productResidueCenteredEnergy_eq_zero_iff`
- `productResidueCenteredEnergy_pos_iff`
- `balancedProduct_periodic_pairing`
- `balancedProductResidueCount_eq`
- `productResidueBlockAverage`
- `balancedProductSmoothing_energy`
- `balancedProductSmoothing_energy_ge`
- `balancedProductSmoothing_pairing`
- `balancedProductSmoothing_noWrap`
- `balancedProductSmoothing_squareRoot_obstruction`

All parameters are actual finite data or positive lengths. No analytic
premise, assumed residue profile, conjecture-valued interface or proof hole
occurs in these statements.

## Audit status

`lake --old env lean GaloisForLFunctions/goldbach/ProductResidueProfile.lean`
passed from `formal/`, exit 0, without warnings. Eleven closures were
audited: kernel multiplicity, forward and inverse Fourier formulas,
centered energy, strict positivity classification, actual balanced counts,
complete-period average, smoothing energy, signed pairing, absence of
wraparound and the square-root-window obstruction. They use only
`propext`, `Classical.choice`, and `Quot.sound` (the no-wrap bound does
not use `Classical.choice`). No added axiom or analytic premise occurs.
Temporary audit directives were removed without changing proof bodies.
The module is imported by `goldbach/Main.lean`; the umbrella was not built.

Audit log: `/tmp/hgt-goldbach-product-residue-audit.log`.
Declaration index regeneration passed. Source checks found no proof holes,
added axioms, unsafe shortcuts or raised proof budgets; changed-file whitespace
checks and the new pipeline-card links passed. Owned search scratch files
were removed; the audit log was retained.

This is elementary positive salvage of a failed transfer mechanism, not a
new prime-distribution estimate. Neither RH nor Goldbach follows. The
actual signed residual covariance remains open.
