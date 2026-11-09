# Collective rank and depth of prime-logarithm forms

- **ID:** CDG-RANK
- **Stage:** 2-fully-proven
- **Type:** COLLECTIVE APPROXIMATION TOOL

## Statement

Let `p₁,…,p_k≤y` be distinct primes and `1≤r≤k`. Put `d=k−r` and
let `B_{d+1}(y)=bakerExponent d ceil((d+1)log y)` be the explicit corpus
exponent for `d+1` logarithms. For `H≥1`, define

`Δ(r,d,y,H)=exp(−B_{d+1}(y)(log((d+1)r!H^r)+2))/(r!H^(r−1))`.

At full rank `d=0`, use the stronger elementary floor
`Δ(r,0,y,H)=log 2/(r!H^(r−1))`.

Every family of `r` rationally independent integer coefficient vectors
`ν₁,…,ν_r`, with `|ν_ij|≤H`, satisfies

`max_i |Σ_j ν_ij log p_j| ≥ Δ(r,k−r,y,H)>0`.

Thus the approximation body `|ν_j|≤H`, `|ν·log p|<Δ` contains no `r`
independent integer points. This is a bound on the rank of the whole family,
not repeated use of a scalar `k`-logarithm estimate.

## Paper proof

Choose a nonzero maximal minor of the coefficient matrix; it exists by row
independence. Permuting columns gives `[A|B]`, where `A` is an invertible
`r×r` integer matrix and `B` has `d` columns. Write the corresponding prime
logarithms as vectors `x,z`, so the vector of forms is `v=Ax+Bz`.

Fix a pivot column `i`. The adjugate identity gives

`det(A)x_i + Σ_j det(A[i←B_j])z_j = Σ_h adj(A)_ih v_h`.

The coefficients on the left are integers, and the first is nonzero.
The logarithms involved are those of `d+1` distinct primes at most `y`.
The determinant expansion bounds every coefficient by `F=r!H^r`, so their
sum of absolute values is at most `(d+1)F`. The proved scalar Baker theorem
therefore bounds the absolute value of the left side below by

`exp(−B_{d+1}(y)(log((d+1)F)+2))`.

Each adjugate entry is a signed `(r−1)×(r−1)` determinant, of absolute
value at most `(r−1)!H^(r−1)`. Hence the right side has absolute value
at most `r!H^(r−1) max_h |v_h|`. Division proves the stated bound.
The denominator and exponential are positive. Selecting a maximal minor
and its complementary columns changes neither coefficient bounds nor the
values of the forms.

At full rank there are no complementary columns. The left side is
`det(A) log p_i`, whose absolute value is at least `log 2`: the determinant
is a nonzero integer and `p_i≥2`. The same adjugate bound therefore gives
the stronger full-rank floor without a transcendence estimate.

## Counting near relations

For integer `H≥1` and `ε≤Δ(r,k−r,y,H)`, let
`S={ν∈ℤ^k: |ν_j|≤H, |ν·log p|<ε}`. Then

`dim_Q span_Q S ≤ r−1`, and `#S ≤ (2H+1)^(r−1)`.

Choose a basis from the finite set `S`. If its size were at least `r`,
selecting `r` basis vectors would contradict the collective depth floor.
A rational subspace of dimension `s` admits an injective projection onto
`s` coordinate axes: select a nonzero maximal minor of a basis matrix.
Each selected integer coordinate has `2H+1` possibilities, so
`#S≤(2H+1)^s≤(2H+1)^(r−1)`. The coordinate-projection and integer-box
counting lemmas already exist in the corpus.

## Mathematical consequence

For the penultimate rank `r=k−1`, the transcendence exponent is the
**two-logarithm** exponent, regardless of `k`. Dimension enters through
`r!H^r` and the adjugate factor. More generally, the relevant number of
logarithms is codimension plus one. The result is uniform in growing rank,
coefficient height, and prime cutoff.

The mechanism is elementary Cramer transference of the existing Baker bound;
no new transcendence estimate is claimed. It supplies a collective
approximation tool. It does not bound the first minimum beyond the existing
scalar estimate or prove the missing return-count or breadth law.

## Lean status

Paper proof dependency-closed. Formalization in progress.
