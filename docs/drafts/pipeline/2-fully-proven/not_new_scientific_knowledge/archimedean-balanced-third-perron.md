# Archimedean-balanced third-order Perron charge and scalar decompletion obstruction

- **ID:** archimedean-balanced-third-perron
- **Stage:** 2-fully-proven
- **Type:** THEOREM / OBSTRUCTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Lean:** `formal/GaloisForLFunctions/RHTower/ArchimedeanBalancedPerron.lean`

## Theorem A `[PROVED]`: the balanced Mellin kernel

Define

`b(u)=max(1-u,0)(3u-1)/2`.

For `Re(s)>0`,

`M[b](s)=(s-1)/(s(s+1)(s+2))`.                              (1)

Moreover the inverse-Mellin vertical integral is absolutely convergent on every positive
abscissa.

### Proof

On `(0,1)`,

`b(u)=-1/2+2u-3u^2/2`.

Termwise integration gives

`M[b](s)=-1/(2s)+2/(s+1)-3/(2(s+2))=(s-1)/(s(s+1)(s+2))`.

The last expression is the ordinary second-order Perron kernel multiplied by `(s-1)/(s+2)`.
On `Re(s)=c>0` that multiplier is uniformly bounded, while `1/(s(s+1))` is `L1`.  This proves
absolute vertical integrability and Mellin inversion.

The extra denominator is necessary for the present absolute-integral interface: multiplying the
old second-order kernel by `s-1` would leave only `O(|t|^-1)`.

## Theorem B `[PROVED]`: balanced Perron summation

For an absolutely convergent Dirichlet series

`L(s)=sum_(m>=1) a_m m^(-s)`

on `Re(s)=c>0`, and `x>0`, let

`W_x(m)=x^2 b(m/x)`.

Then

`sum_(m>=1) a_m W_x(m)`

` = (1/(2pi)) integral_R L(c+it) x^(c+it+2)
      (c+it-1)/((c+it)(c+it+1)(c+it+2)) dt`.                 (2)

### Proof

Absolute convergence of the Dirichlet series and Theorem A give an integrable product majorant,
so sum and integral may be interchanged.  Mellin inversion at `y=x/m` evaluates each term as
`a_m x^2 b(m/x)`.

## Theorem C `[PROVED]`: the four-knot charge

Fix an integer `n>=1` and `0<delta<2/3`.  Set

`x0=n-3delta/2`, `x1=n-delta/2`, `x2=n+delta/2`, `x3=n+3delta/2`,

and

`N3(s)=x0^(s+2)-3x1^(s+2)+3x2^(s+2)-x3^(s+2)`.

Then `N3(0)=N3(-1)=N3(-2)=0`, so

`E3(s)=N3(s)/(s(s+1)(s+2))`                              (3)

has an entire continuation.  Its balanced version `(s-1)E3(s)` is entire, absolutely integrable
on the Perron right edge after multiplication by `L`, and

`(1/(2pi)) integral_R L(c+it)(c+it-1)E3(c+it)dt
   = (3delta^2/4)a_n`.                                      (4)

### Proof

In the active region `m<x`,

`W_x(m)=-x^2/2+2mx-3m^2/2`,                              (5)

a quadratic polynomial in `x`.

For `m<n`, all four knots lie in the active region, and the signed third difference

`W_x0(m)-3W_x1(m)+3W_x2(m)-W_x3(m)`

vanishes.  For `m>n`, the largest knot is strictly below `n+1<=m`, so all four weights vanish.
For `m=n`, the first two weights vanish and direct substitution in (5) gives

`3W_x2(n)-W_x3(n)=3delta^2/4`.

Apply (2) at the four knots and combine the absolutely convergent integrals.  The numerator is
`N3`, giving (4).

## Theorem D `[PROVED]`: entire boundary decompletion

Let

`D_infty(s)=2 dslope((Gamma_R)^(-1),0)(s)`.                 (6)

The reciprocal Gamma factor is entire and vanishes at `s=0`; hence `D_infty` is entire.  Away from
`s=0`,

`D_infty(s)=2/(s Gamma_R(s))`,

and wherever `Gamma_R(s)` is nonzero,

`archFactor(s)D_infty(s)=s-1`.                              (7)

Consequently, every completed Dirichlet carrier `F=archFactor*L` on the right edge satisfies

`(1/(2pi)) integral_R F(c+it)D_infty(c+it)E3(c+it)dt
  =(3delta^2/4)a_n`.                                        (8)

In particular, for the completed zeta carrier `xi`, every `a_n=1`, so the charge is
`3delta^2/4`.

## Theorem E `[PROVED]`: scalar decompletion obstruction

At every point where `archFactor` is nonzero, a scalar function `K` satisfying

`archFactor(s)K(s)=s-1`

must satisfy

`K(s)=D_infty(s)`.                                          (9)

For zeta this forces

`xi(s)D_infty(s)=(s-1)zeta(s)`.                             (10)

### Proof

Equation (9) follows by cancellation from (7).  Equation (10) follows from
`xi=archFactor*zeta` and (7).

Thus exact pointwise scalar coefficient extraction does not transport the Gamma decay: it cancels
the Gamma factor and returns the entire pole-cancelled raw carrier.  The third denominator repairs
polynomial vertical integrability, but it cannot preserve the completed carrier's exponential
flank advantage.

## Attack and status

- `[FAILED]` Full reciprocal `1/archFactor`: meromorphic at the boundary point `s=1`.
- `[FAILED]` Boundary-balanced decompletion with the old second-order kernel: only `O(|t|^-1)`.
- `[PROVED]` Third-order smoothing is the minimal repair within the current absolute-integral
  scalar Perron family.
- `[PROVED OBSTRUCTION]` Exact pointwise scalar decompletion is unique and spends the Gamma factor.
- `[OPEN CORE]` A completed RH-facing extractor must be non-diagonal in the archimedean and
  finite-prime variables, or obtain raw-carrier flank mass by another mechanism.  Adding further
  scalar polynomial smoothing does not evade (9)-(10).

## Novelty and significance gates

- **NOVEL:** the minimal-order and scalar-uniqueness obstruction locate the exact failure of the
  project-native completed/raw Perron weld; this is not the classical higher Riesz mean by itself.
- **SIGNIFICANT:** the completed coefficient charge is unconditional and formalized, while the
  surviving obstruction rules out the entire pointwise scalar family as a way to preserve Gamma
  decay.  The next search space is therefore sharply reduced to non-diagonal pairings.

## Gates

- [x] 0 -> 1: candidates generated and attacked.
- [x] 1 -> 2: Mellin, summation, four-knot, decompletion, completed charge, and no-go proofs complete.
- [x] 2 -> 3: formalized in `ArchimedeanBalancedPerron.lean`.
- [ ] 3 -> 4: requires the non-diagonal completed extractor or a target mass theorem.
