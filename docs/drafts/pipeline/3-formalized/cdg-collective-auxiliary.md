# Collective integral auxiliaries with explicit parameters

- **ID:** CDG-AUX
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** The integer auxiliary construction, not a simultaneous logarithm bound.

## Statement

Let `p_1,…,p_k` be distinct primes, and let `M` be an integer `r×k`
matrix of rank `r≥1`. Put `d=k−r`, `W=ceil(Σ log p_j)+1`, and
`h=floor(d/r)+1`.

Choose a largest absolute `r×r` column minor `B`, with determinant `D≠0`,
pivot selector `s`, and complementary selector `t`. For `l∈[0,q)^k`, set

`Γ_j(l)=D l_j−Σ_i l_(s_i) cramer(B,M_col(j))_i`.

Then `Γ_(s_i)=0`, `|Γ_j/D|≤(r+1)q`, and

`Σ_j (Γ_j/D)log p_j = Σ_j l_j log p_j−u B⁻¹(M log p)`,

where `u_i=l_(s_i)`.

Define

`L=2+h(k+1)(floor(log₂(1000Wk))+1)`,
`J=h(k+1)+k`, `b=floor(log₂(L+J+1))+1`, `R=L+2Jb`,
`E=1000Wk(R+1)`, `q=E^h(R+1)`, `M₀=1000Wkq`,
`S=RM₀+1`, `c=16k²(R+1)q`, `a=2cE^h`.

For every integer `n≥1`, let `N=an`, `X=cn`, `U=(N+1)q^k`.
There is a nonzero integer coefficient vector `C_(v,l)`, `0≤v≤N`, such that
all true companion jets

`Φ_(σ,τ)(z)=Σ_(v,l) C_(v,l) g_v^[σ](z) Π_j(Γ_(t_j)(l)/D)^τ_j exp(z Σ_i l_i log p_i)`

vanish at every integer `0≤x<X`, for `σ<S` and `τ∈[0,S)^d`.
Here `g_v` and its divided derivatives are the corpus's Fel'dman polynomials.
Some integer `x<U` nevertheless has `Φ_(0,0)(x)≠0`.

Writing `F=feldmanDivisor(N+1,S)` and `W₀=Σ log p_j`, the coefficients obey

`|C_(v,l)|≤U max(1,V)`,

`V=2^N(X+N+1)^N/F · ((r+1)q|D|)^(dS) · exp(XqW₀)`.

## Proof

**Normalization.** Replacing one pivot column by any column of `M` produces
another minor. Maximality gives `|cramer(B,M_col(j))_i|≤|D|`.
Cramer's rule kills the pivot coordinates exactly. The triangle inequality
gives the projection bound; expanding the finite sums gives the frequency
defect identity.

**Parameters.** Since `d+1≤hr`,
`(Eq)^(d+1)≤E^h q^k`. Therefore `2cS^(d+1)≤aq^k`.
The binary-logarithmic choice of `R` gives
`4(1000Wk)^(h(k+1))(R+1)^(h(k+1)+k)≤2^R`, hence
`2aq^k≤2^R c` and `floor(log₂ S)≤R`.
The same parameters satisfy the numerical growth inequality used by
Fel'dman's interpolation argument. This arithmetic inequality does not
assert the missing analytic estimate for the collective family.

**Integer kernel and height.** Clear `D^|τ|` from each jet and divide its
polynomial jet by `F`. Fel'dman's common-divisor theorem makes the resulting
matrix integral. It has `XS^(d+1)≤U/2` rows. The projection bound and the
polynomial-jet bound give entry height at most `V`. Integer Siegel gives
a nonzero kernel vector of height at most
`(U max(1,V))^(rows/(U−rows))≤U max(1,V)`.
The exact arithmetic identity then gives the asserted vanishing jets.

**Nonvanishing.** At jet order zero, the companion is the original
prime-frequency exponential polynomial. Unique factorization makes its
`q^k` integer bases distinct. Confluent interpolation at the first
`(N+1)q^k` integers, followed by independence of the Fel'dman polynomial
basis, would force `C=0` if all these values vanished.

## Contribution and boundary

The construction separates prime-frequency dimension `k` from jet dimension
`d+1`. At `r≥d`, `h≤2`, so the parameter polynomial has degree at most
`3k+2`, instead of the quadratic degree at rank one. All dimensions and
coefficient-height scales are unrestricted.

Analytic extrapolation for these collective jets remains open. This result
neither imports Gaudron's theorem nor proves a breadth law or an RH producer.

## Lean

`CollectiveDiophantineGeometry/CollectiveAuxiliaryConstruction.lean`.
The capstone `exists_collective_auxiliary` exports the explicit parameters,
the chosen pivot bounds, exact vanishing, coefficient height, and nonvanishing.
The numerical closure is `exists_collectiveFeldmanParams`; the frequency
identity is `collectiveFrequency_defect`.

Direct `lake --old env lean` verification passed. Axiom audits of these
three declarations, `exists_bounded_collective_projection`, and
`collectiveStepD_of_half_rank` use only `propext`, `Classical.choice`,
and `Quot.sound`.
