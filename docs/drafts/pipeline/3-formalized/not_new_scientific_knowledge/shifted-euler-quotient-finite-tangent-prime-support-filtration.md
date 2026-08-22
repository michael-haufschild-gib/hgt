# Shifted Euler quotient finite tangents equal the distinct-prime-support filtration

- **ID:** `shifted-euler-quotient-finite-tangent-prime-support-filtration`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** Every finite transverse tangent of the shifted Euler quotient is a bounded
  distinct-prime-support layer.  The coefficient at an integer `n` first appears at order equal to
  the number of distinct prime divisors of `n`, with an explicit leading derivative.  Equivalently,
  the entire finite tangent germ is a Bell-polynomial reorganization of the odd logarithmic
  derivatives of the original completed source and introduces no independent arithmetic datum.

## Setup

On an Euler half-plane put

```text
R_omega(s)=zeta(s-omega)/zeta(s+omega)
           =sum_(n>=1) c_omega(n)n^(-s),
```

where

```text
c_omega(n)
 =n^omega sum_(d|n) mu(d)d^(-2omega)
 =n^omega product_(p|n)(1-p^(-2omega)).                  (1)
```

Write `nu(n)` for the number of distinct prime divisors of `n`, with `nu(1)=0`.

## Theorem A: exact prime-support order

For `n>1`, `c_omega(n)` has a zero at `omega=0` of exact order `nu(n)`.  More precisely, if
`r=nu(n)`, then

```text
partial_omega^k c_omega(n)|_(omega=0)=0       for k<r,

partial_omega^r c_omega(n)|_(omega=0)
 =2^r r! product_(p|n) log p.                            (2)
```

Consequently, the `k`th transverse derivative of `R_omega` is supported on integers with at most
`k` distinct prime divisors; cancellations may remove individual coefficients inside that layer.

### Proof

For every prime divisor `p` of `n`,

```text
1-p^(-2omega)=2omega log p+O(omega^2).                   (3)
```

The factor `n^omega` is nonzero at zero.  Multiplying `(3)` over the `r` distinct prime divisors
gives

```text
c_omega(n)
 =(2omega)^r product_(p|n)log p+O(omega^(r+1)).          (4)
```

Equation `(2)` follows.  Absolute convergence of the Euler quotient for `Re s>1+|omega|` permits
termwise differentiation on every smaller common half-plane, proving the support statement.

For `k=1`, equation `(2)` and the prime-power exponents give

```text
partial_omega c_omega(n)|_0=2Lambda(n).
```

For `k=2`, direct convolution or quotient differentiation gives

```text
partial_omega^2 c_omega(n)|_0=4(Lambda*Lambda)(n).
```

These are the one-prime and two-prime layers used by the infinitesimal leakage Schur curvature.

## Theorem B: the completed finite germ is logarithmically triangular

Let `F` be nonzero and holomorphic near `s`.  Then

```text
log(F(s-omega)/F(s+omega))
 =-2 sum_(j>=0)
    omega^(2j+1)/(2j+1)!
    partial_s^(2j+1) log F(s).                           (5)
```

Hence every derivative

```text
partial_omega^k (F(s-omega)/F(s+omega))|_(omega=0)       (6)
```

is a universal complete Bell polynomial in the odd derivatives

```text
partial_s log F(s), partial_s^3 log F(s), ...,
partial_s^(2 floor((k-1)/2)+1) log F(s).                 (7)
```

In particular, the leading monomial in `(6)` is

```text
(-2 partial_s log F(s))^k.                               (8)
```

### Proof

Taylor-expand `log F(s-omega)` and `log F(s+omega)`.  Their even powers cancel and their odd powers
subtract, proving `(5)`.  Exponentiating `(5)` and applying the ordinary derivative formula for an
exponential gives the Bell-polynomial statement.  Choosing the linear term from `(5)` in all `k`
factors gives `(8)`.

For the completed Xi source, the gamma and pole-clearing factors contribute explicit holomorphic
terms to the same triangular germ, while the Euler quotient has the support filtration of Theorem
A.

## Route C consequence

Passing from first to any fixed higher transverse derivative does not create a new all-prime
constraint.  It only adds the next bounded distinct-prime-support interaction layer and repackages
odd logarithmic derivatives of the same completed function.  In particular:

1. the second-order Toeplitz Schur curvature is the two-prime completion of the first-order
   von-Mangoldt tangent;
2. every fixed order remains a finite interaction-grade object, although it ranges over infinitely
   many primes; and
3. no finite tangent identity supplies the missing absolute corner bound by formal differentiation
   alone.

This closes “take more `omega` derivatives” as an independent source of arithmetic rigidity.  A
surviving Route C theorem must use a genuinely nonperturbative constraint in the full `omega` germ,
an infinite interaction-grade completion with a proved boundary law, or a direct Euler--Gamma
estimate on the already constructed second-order corner.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The exact support filtration is an elementary Taylor expansion of
finite Euler factors, and the completed germ is the standard exponential Bell-polynomial formula.
The Route C interpretation is useful, but the theorem fails the parent-theory and anti-theatre
gates.

## Gates

- [x] 0 -> 1: finite-tangent escape and its prime-support falsifier isolated.
- [x] 1 -> 2: exact vanishing order, leading derivative, Dirichlet support, and Bell triangularity
  proved on paper.
- [x] 2 -> 3: formalized unconditionally in Lean 4 (see **Lean formalization** below).
- [ ] 3 -> 4: no scientific-novelty claim.

## Lean formalization

Modules (unconditional, no hypotheses standing for analytic inputs, no added axioms; every capstone
audited at `[propext, Classical.choice, Quot.sound]`):

- `formal/GaloisForLFunctions/HTGeometry/ShiftedEulerTangentFiltration.lean`
- `formal/GaloisForLFunctions/HTGeometry/VonMangoldtSelfConvolution.lean`

| Card statement | Lean declaration |
|---|---|
| `(1)`: `c_omega(n) = n^omega prod_{p|n}(1 - p^{-2omega})` | `shiftedEulerCoeff` |
| Exact flat factor `omega^{nu(n)}` with leading value `2^{nu(n)} prod log p` | `exists_flatFactor_shiftedEulerCoeff` |
| Theorem A, vanishing half (`k < nu(n)`) and the Dirichlet support statement | `iteratedDeriv_shiftedEulerCoeff_eq_zero` |
| Theorem A, equation `(2)`: `2^r r! prod_{p|n} log p` | `iteratedDeriv_shiftedEulerCoeff_card` |
| `partial_omega c_omega(n)|_0 = 2 Lambda(n)` | `iteratedDeriv_one_shiftedEulerCoeff` |
| `partial_omega^2 c_omega(n)|_0 = 4 (Lambda * Lambda)(n)` | `iteratedDeriv_two_shiftedEulerCoeff` |
| prime-power second layer `4(a-1)(log p)^2` | `iteratedDeriv_two_shiftedEulerCoeff_primePow` |
| Theorem B, equation `(5)` in jet form | `iteratedDeriv_reflectedLog` |
| Theorem B triangularity (the `k`-jet of the quotient sees only the `k`-jet of the logarithm) | `iteratedDeriv_exp_congr_of_flat` |
| Theorem B, equation `(8)`: leading monomial `(-2 partial_s log F)^k` | `iteratedDeriv_reflectedQuotient_affine` |

The `Lambda * Lambda` layer is new corpus infrastructure (mathlib has no self-convolution of the
von Mangoldt function):

| Statement | Lean declaration |
|---|---|
| `(Lambda * Lambda)(n) = 0` once `n` has three distinct prime divisors | `vonMangoldt_mul_self_eq_zero_of_three_le` |
| `(Lambda * Lambda)(p^a) = (a - 1)(log p)^2` | `vonMangoldt_mul_self_prime_pow` |
| `(Lambda * Lambda)(n) = 2 prod_{p | n} log p` when `nu(n) = 2` | `vonMangoldt_mul_self_of_card_eq_two` |
