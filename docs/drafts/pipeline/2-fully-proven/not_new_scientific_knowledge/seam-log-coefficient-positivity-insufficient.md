# Seam-Log Coefficient Positivity Is Insufficient

- **ID:** seam-log-coefficient-positivity-insufficient
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / analytic shortcut guardrail
- **Source:** `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** Nonnegativity of all Taylor coefficients of the seam-log Markov
  candidate is not enough to imply Markov/Stieltjes positivity. The all-order Hankel
  square-test condition is strictly stronger.

## Setup

The seam-log Markov target is

`G_src(x)=sum_{n>=0} T_{n+1}^src x^n`.

If RH holds, then `G_src` is a Markov transform of a positive measure on `R_+`, so
every coefficient `T_{n+1}^src` is nonnegative. A tempting weaker target is therefore:

`T_k^src >= 0 for every k>=1`.

This condition is not enough.

## Theorem

There is a power series

`G(x)=sum_{n>=0} a_n x^n`

with every `a_n>0` and positive radius of convergence, but whose coefficient sequence
is not the moment sequence of any positive measure on `R_+`. Equivalently, coefficient
positivity does not imply the shifted Hankel positivity required by the seam-log
Markov target.

## Proof

Take

`a_0=1`, `a_1=3`, and `a_n=1` for every `n>=2`.

Then every coefficient is positive and

`G(x)=1+3x+x^2/(1-x)`

has radius of convergence `1`.

However, the first Hankel matrix is

```text
[a_0 a_1]
[a_1 a_2]
```

so

`det [[1,3],[3,1]] = 1-9 = -8`.

Hence the quadratic form is negative on the vector `(1,-1)`:

`a_0 - 2a_1 + a_2 = 1 - 6 + 1 = -4`.

If `(a_n)` were moments of a positive measure on `R_+`, then every Hankel matrix
`[a_{i+j}]` would be positive semidefinite, since

`sum_{i,j} c_i c_j a_{i+j} = int (sum_i c_i y^i)^2 dnu(y) >= 0`.

The negative determinant contradicts this. Therefore coefficient positivity is
strictly weaker than Markov/Stieltjes positivity.

## Consequence for the RH Route

A proof that only establishes

`T_k^src >= 0 for all k`

does not prove RH. It gives positive Taylor coefficients for `G_src`, but it does not
give a positive representing measure and does not control the cross-moment Hankel
minors.

The required target remains the full square-test condition:

`sum_{i,j} c_i c_j T_{i+j+1}^src >= 0`

for every real polynomial `p(y)=sum_i c_i y^i`, equivalently the Markov/Pick
representation by a positive measure on `R_+`.

## Source Boundary

This is an elementary moment-theory guardrail. It is not an RH result. It prevents a
weaker analytic positivity shadow from being substituted for the Markov/Stieltjes
property.

## Gates

- [x] 0 -> 1 in-progress: coefficient-positivity shortcut isolated.
- [x] 1 -> 2 fully-proven: explicit positive-coefficient non-moment sequence.
- [ ] 2 -> 3 formalized: finite determinant calculation.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal after the seam-log
  Markov/Pick target was isolated. This records that coefficient positivity of the
  source transform is not enough; the square-test cone is essential.

## 2026-06-24 axis-mode reading

`axis-positivity-does-not-imply-hankel-positivity.md` gives the source-route reading of this example. Coefficient positivity is an axis-mode condition; Hankel positivity is a combination-mode square-test condition. The Euler-product transfer must prove the latter from the former through the completed source object, not merely cite positive coefficients.
