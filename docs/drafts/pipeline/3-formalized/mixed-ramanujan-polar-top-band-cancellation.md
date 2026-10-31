# Mixed Ramanujan–polar top-band cancellation

- **ID:** SSH-MIXED-POLAR-TOP-BAND
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q1/O1.
- **Statement:** Fix a `C²` atom profile supported in `[0,1]` with positive
  quadratic mass. The joint coefficient with base `c_m(n)/√φ(m)` and constant
  top-band perturbation is at most `Kφ m(U_m+V_m)G(1+log N)` in absolute
  value, uniformly for `m≥2`, `N≥8`, and `1≤c≤N/4`; `U_m,V_m` are defined below.

## Mechanism

The exact divisor convolution is
`Σ_(d|ℓ)Λ(d)c_m(ℓ/d)=c_m(ℓ)log ℓ−J_m(ℓ)`.
The periodic divisor jet has mean `Λ(m)`. The harmonic base moment tends to
`−Λ(m)/√φ(m)`, with a periodic-tail error of order `1/N`.
Thus the constant jet and the first polar cross term have opposite signs
and equal continuum mass. Abel summation pays the two mean-zero periodic
remainders. The second polar cross term and removed ratio diagonal retain
their exact finite sums.

## Exact decomposition and bounds

Write `a=c_m/√φ(m)`, `H=Λ(m)/√φ(m)`,
`j=(J_m−Λ(m))/√φ(m)`, `U=√φ(m)`, and
`V=(Σ_(d|m)|μ(m/d)d log d|+Λ(m))/√φ(m)`.
Both `a` and `j` have period `m` and mean zero; their amplitudes are at
most `U,V`. Put `P=(∫g e^(-u/2))(∫g e^(u/2))` and
`K(ℓ,n)=β(log ℓ−log n)/√(ℓn)`, where `g(u)=φ(u/w)`, `w=c/N`,
`G=∫g²`, and `T={1≤n≤N:Ne^w<2n}`.

For `ℓ≤ceil(N exp w)≤2N`, the finite base horizon omits only zero
Mangoldt terms, so `H_a(ℓ)=a(ℓ)log ℓ−j(ℓ)−H` exactly.
Let `A_n=Σ_ℓ K(ℓ,n)a(ℓ)log ℓ`, `B_n=Σ_ℓ K(ℓ,n)j(ℓ)`,
and `E_n=Σ_ℓ K(ℓ,n)−P`. The exact joint coefficient is

`P[(Σ_(k≤N)a(k)/k+H)|T|+(Σ_(k≤N)a(k))Σ_T 1/n]`
`−Σ_T A_n+Σ_T B_n+HΣ_T E_n+GΣ_T H_a(n)/n`.

Take `r=1/4+A₁/∫φ²` and `C₀=2+28r`, where `A₁` bounds the
profile-autocorrelation derivative. The shell window has at most `7wn`
cells, lies in `[n/2,2n]`, and contains the entire kernel support.
Abel summation and first-order lattice quadrature give

- `|A_n|≤2C₀mUG(1+log(2n))/n`;
- `|B_n|≤2C₀mVG/n`;
- `|E_n|≤C₀G/n`.

The exact harmonic remainder is at most `2mU/(N+1)`; the ordinary
partial sum is at most `2mU`. Since `Σ_T1/n≤2`, `|P|≤G`, and
`|H_a(n)|≤U log N`, the two pole terms cost `6mUG`, the removed
diagonal costs `2UG log N`, and the three shell sums cost
`8C₀mUG(1+log N)+4C₀mVG+2C₀HG`.
Using `H≤V` gives the explicit bound

`|J(a,1)|≤(24+224r)m(U+V)G(1+log N)`.

Together with the periodic-partner theorem, this bounds every entry except
the constant–constant coefficient without an explicit overlap factor.

## Lean verification

All modules lie in `SuccessorShellArithmetic/TopBand`:

- `RamanujanDivisorMoments`: `periodMean_ramanujanLogDivisorJet`,
  `horizonDivisorCoefficient_ramanujan_eq`, and
  `abs_normalizedRamanujan_harmonic_add_vonMangoldt_le`.
- `FullShellRows`: exact support reindexing, pole-mass integral,
  `abs_full_periodic_shellPartnerKernel_sum_le`,
  `abs_full_shellPartnerKernel_sum_sub_integral_le`, and
  `abs_full_periodic_rowIntegrand_sum_le`.
- `MixedPolarCancellation`: `jointTopCoefficient_ramanujan_const_eq` and
  `exists_abs_ramanujan_polar_jointTopCoefficient_le`.

Each production leaf passed its final `lake --old env lean` check without
diagnostics. Every audited capstone has exactly `propext`, `Classical.choice`,
`Quot.sound` as transitive axioms. Umbrella imports and programme README
are updated.

The [two-conductor packet theorem](two-conductor-top-band-polar-channel.md)
combines this orientation with periodic-partner cancellation. The full
agreement-shell sum-of-squares identity remains open.
