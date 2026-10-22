# Suzuki's completed tail is exactly the shifted-Euler summatory error transform

- **ID:** `suzuki-tail-is-exact-summatory-error-transform`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `suzuki-euler-pole-archimedean-moment-annihilation.md`
- **Statement:** After subtracting the positive main term dictated by the leading shifted-Euler
  pole, Suzuki's completed primitive is unchanged.  It is exactly a Stieltjes transform of the
  generalized Jordan-totient summatory error.  Thus the positive coefficient mass contributes no
  residual main term; every sign-bearing contribution lies in the arithmetic error term.

## Setup

Fix `omega>0`.  Let

```text
c_omega(n)=n^omega product_(p|n)(1-p^(-2omega)),
A_omega(X)=sum_(n<=X)c_omega(n),                          (1)
```

and put

```text
r_omega=1/zeta(1+2omega),
M_omega(X)=r_omega X^(1+omega)/(1+omega),
E_omega(X)=A_omega(X)-M_omega(X).                        (2)
```

Regard `A_omega`, `M_omega`, and `E_omega` as locally bounded-variation functions on
`[0,infinity)`, with `A_omega(X)=0` for `0<=X<1`.

Suzuki's integrated causal source is

```text
h_omega^(1)(x)
 =x^(-1) sum_(n<=x)c_omega(n)g_omega^(1)(n/x),           (3)
```

where

```text
integral_0^1 g_omega^(1)(u)u^omega du=0.                (4)
```

## Theorem: exact error-transform identity

For every `x>1`,

```text
h_omega^(1)(x)
 =x^(-1) integral_((0,x]) g_omega^(1)(t/x)dE_omega(t).   (5)
```

### Proof

The Stieltjes measure of `A_omega` is the atomic measure

```text
dA_omega=sum_n c_omega(n)delta_n.
```

Therefore `(3)` is

```text
h_omega^(1)(x)
 =x^(-1) integral_((0,x])g_omega^(1)(t/x)dA_omega(t).    (6)
```

The smooth main term has

```text
dM_omega(t)=r_omega t^omega dt.
```

Its contribution to `(6)` is

```text
x^(-1)r_omega integral_0^x g_omega^(1)(t/x)t^omega dt
 =r_omega x^omega integral_0^1 g_omega^(1)(u)u^omega du
 =0                                                     (7)
```

by `(4)`.  Since `dA_omega=dM_omega+dE_omega`, subtracting `(7)` from `(6)` proves `(5)`.

The integral at zero is legitimate in the RH-relevant range `0<omega<1/2`: the endpoint theorem
gives `g_omega^(1)(u)=O(u^(omega-1))`, so the main-term integrand is `O(u^(2omega-1))`, which is
integrable.  For other positive `omega`, Suzuki's Mellin identity supplies the same vanishing by
analytic continuation wherever the displayed Stieltjes integral is classically convergent.

## Mellin singularity boundary

The Mellin--Stieltjes transform of the atomic measure is

```text
integral_((0,infinity)) t^(-s)dA_omega(t)
 =zeta(s-omega)/zeta(s+omega)                            (8)
```

on `Re s>1+omega`.  On `[1,infinity)`, the Mellin transform of the main density is

```text
r_omega integral_1^infinity t^(omega-s)dt
 =r_omega/(s-1-omega).                                   (9)
```

Inserting a fixed cutoff that is zero near zero and one on `[1,infinity)` changes only a compactly
supported Mellin term and not the pole `(9)`.  Thus the large-`X` part of `E_omega` is the
physical-side carrier of the shifted-Euler quotient after its leading pole is subtracted.  After
completion, its next possible meromorphic singularities are the shifted nontrivial-zero poles,
subject to exceptional common-factor cancellation.

## Route C consequence

Equation `(5)` closes every argument that tries to dominate the completed tail by the positive
average size of `c_omega(n)`.  That average has been projected out exactly.  The remaining source
problem is now

```text
control the sign or boundary curvature of a signed transform of E_omega,
```

where `E_omega` is the all-prime summatory discrepancy after the leading pole is removed.

A bound obtained from a zero-free region or from the next Mellin pole is divisor-fed.  A genuinely
new Route C theorem would need an arithmetic constraint on `E_omega` strong enough to control the
transform `(5)` without first locating those poles.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The theorem is Stieltjes summation plus an exact vanishing moment.
It gives the correct surviving arithmetic object but is a routine parent-theory reduction.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTailSummatoryErrorTransform.lean`
(with the complex-valued countable Dirac integration lemmas added to
`formal/GaloisForLFunctions/HTGeometry/CountableWeightedDirac.lean`).

| Card statement | Lean declaration |
|---|---|
| `(1)`-`(2)` coefficients, summatory, main term, error | `suzukiShiftedCoefficient`, `RHTower.suzukiShiftedSummatoryReal`, `RHTower.suzukiMainTermReal`, `RHTower.suzukiCoupledErrorReal` |
| `dA_ω = ∑ₙ c_ω(n) δₙ` is the Stieltjes measure of `A_ω` | `RHTower.suzukiShiftedAtomicMeasure`, `RHTower.suzukiShiftedAtomicMeasure_Ioc` |
| `dM_ω = r_ω t^ω dt` is the Stieltjes measure of `M_ω` | `RHTower.integral_suzukiMainTermDensity_Ioc` |
| `(6)` atomic integral is the truncated sum | `RHTower.integral_suzukiShiftedAtomicMeasure_Ioc` |
| `(4)`/`(7)` vanishing main-term contribution | `RHTower.integral_rpow_mul_suzukiSourceGOne_eq_zero`, `RHTower.integral_suzukiMainTermDensity_mul_suzukiSourceGOne_eq_zero` |
| `(5)` exact error-transform identity | `RHTower.suzukiSourceHOneFinite_eq_coupledErrorStieltjes`, `RHTower.suzukiSourceHOne_eq_coupledErrorStieltjes` |
| `(8)` Mellin--Stieltjes transform of `dA_ω` | `RHTower.integral_suzukiShiftedAtomicMeasure_cpow` |
| `(9)` Mellin pole of the main density | `RHTower.integral_Ioi_one_suzukiMainTermDensity_cpow` |

The causal source is the corpus's literal `suzukiSourceHOne`/`suzukiSourceHOneFinite`, and the signed
Stieltjes integral against `dE_ω` is `RHTower.suzukiCoupledErrorStieltjes`, defined as the difference
of the two Stieltjes integrals whose measures are identified above.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for every declaration above.

## Gates

- [x] 0 -> 1: canceled main term and summatory-error carrier isolated.
- [x] 1 -> 2: exact Stieltjes identity and Mellin pole subtraction proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the open theorem is a new bound for `E_omega`.
- [ ] 3 -> 4: no scientific-novelty claim.
