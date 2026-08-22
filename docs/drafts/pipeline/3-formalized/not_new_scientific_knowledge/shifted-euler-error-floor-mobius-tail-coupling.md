# Shifted-Euler error is a coupled floor discrepancy and Möbius tail

- **ID:** `shifted-euler-error-floor-mobius-tail-coupling`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `suzuki-tail-is-exact-summatory-error-transform.md`
- **Statement:** The pole-subtracted shifted-Euler summatory error splits exactly into a weighted
  power-sum floor discrepancy and the tail of the Möbius Dirichlet series.  In the RH-relevant
  range each piece has only the elementary scale `X^(1-omega)` under absolute values.  Any
  critical-scale improvement must use cancellation between the two coupled pieces; separate bounds
  cannot supply it.

## Setup

Fix `0<omega<1/2`.  Put

```text
S_omega(Y)=sum_(m<=Y)m^omega,
R_omega(Y)=S_omega(Y)-Y^(1+omega)/(1+omega),             (1)
```

and retain

```text
A_omega(X)=sum_(n<=X)c_omega(n),
r_omega=1/zeta(1+2omega),
E_omega(X)=A_omega(X)-r_omega X^(1+omega)/(1+omega).     (2)
```

## Theorem A: exact two-piece decomposition

For every `X>=1`,

```text
E_omega(X)
 =sum_(d<=X) mu(d)d^(-omega)R_omega(X/d)
  -X^(1+omega)/(1+omega)
    sum_(d>X)mu(d)d^(-1-2omega).                         (3)
```

### Proof

The coefficient identity

```text
c_omega(n)=sum_(dm=n)mu(d)d^(-omega)m^omega             (4)
```

gives

```text
A_omega(X)
 =sum_(d<=X)mu(d)d^(-omega)S_omega(X/d).                 (5)
```

Insert `(1)` into `(5)`.  The main part becomes

```text
X^(1+omega)/(1+omega)
 sum_(d<=X)mu(d)d^(-1-2omega).                           (6)
```

Since the absolutely convergent full series is

```text
sum_(d>=1)mu(d)d^(-1-2omega)=r_omega,                    (7)
```

subtracting the main term in `(2)` changes `(6)` into the tail term of `(3)`.  The remaining term
is the floor discrepancy in `(3)`.

## Theorem B: absolute-value ceiling

Each term on the right side of `(3)` is

```text
O_omega(X^(1-omega)).                                    (8)
```

Consequently the decomposition gives only

```text
E_omega(X)=O_omega(X^(1-omega))                          (9)
```

without cancellation.

### Proof

Integral comparison for the increasing function `t^omega` gives

```text
R_omega(Y)=O_omega(Y^omega+1).                           (10)
```

Hence the absolute value of the first term in `(3)` is at most a constant times

```text
X^omega sum_(d<=X)d^(-2omega)+sum_(d<=X)d^(-omega)
 =O_omega(X^(1-omega)),                                  (11)
```

because `2omega<1`.  For the second term, absolute convergence and integral comparison give

```text
sum_(d>X)d^(-1-2omega)=O_omega(X^(-2omega)).             (12)
```

Multiplication by `X^(1+omega)` proves the same bound.  This yields `(8)`--`(9)`.

## Route C consequence

The exact source carrier is not a single positive remainder.  It is the coupled expression `(3)`:

1. a signed Möbius weighting of the power-sum floor discrepancy; and
2. the compensating tail needed to complete `1/zeta(1+2omega)`.

Taking absolute values destroys their interaction and stops at exponent `1-omega`.  The shifted
critical-line pole frontier would correspond formally to exponent `1/2-omega`, but a sharp
summatory function may also contain larger floor fluctuations not represented by a new Mellin
pole.  Therefore a pointwise `X^(1/2-omega+epsilon)` bound would be sufficient but is not asserted
here to be necessary.  What Route C actually needs is enough cancellation after applying Suzuki's
signed Stieltjes transform.

This does not prove that no other arithmetic method can obtain the transformed gain.  It closes
separate floor-error estimates, separate Möbius-tail estimates, and triangle-inequality
combinations as a Route C proof mechanism.

`[SEARCH]` Kaczorowski's work on generalized Euler totient functions proves that large square-mean
summatory errors are native even for Selberg-class Euler products and that zeta is extremal inside
that parent family.  That theory confirms that raw summatory size and the signed completed transform
must not be conflated; it does not supply the Route C corner bound.

- Jerzy Kaczorowski, *On a generalization of the Euler totient function*, Monatsh. Math. 170
  (2013), 27--48, DOI `10.1007/s00605-012-0417-6`.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The decomposition is the standard Möbius divisor switch followed
by power-sum main-term subtraction.  The bound is elementary.  Its role is to expose the exact
remaining cancellation, not to claim new summatory-function theory.

## Gates

- [x] 0 -> 1: summatory-error carrier and triangle-inequality falsifier isolated.
- [x] 1 -> 2: exact decomposition and absolute-value ceiling proved on paper.
- [x] 2 -> 3: Theorem A `(3)` and Theorem B `(8)`--`(9)` formalized unconditionally in Lean 4.
- [ ] 3 -> 4: no scientific-novelty claim.
- [ ] open theorem: the coupled half-power gain (cancellation between the two pieces).

## Lean status (2026-08-22)

`formal/GaloisForLFunctions/RHTower/ShiftedEulerFloorMobiusTailCoupling.lean`, wired into
`GaloisForLFunctions.RHTower`, `lake build`-green, axiom audit
`[propext, Classical.choice, Quot.sound]`:

- `suzukiShiftedSummatory_eq` — the Möbius divisor switch, equation `(5)`, obtained from the
  corpus convolution swap `RHTower.Sieve.sum_Icc_convolution_apply` and the coefficient identity
  `shiftedEulerCoefficient ω n = ∑_{dm=n} μ(d) d^{-ω} m^ω`.
- `suzukiEulerDensityConstant_eq_tsum`, `tsum_moebius_split`, `mobiusShiftTail` — the exact
  splitting of `r_ω = 1/ζ(1+2ω)` into its prefix and tail, equation `(7)`.
- `suzukiCoupledError_eq` — **Theorem A, equation `(3)`**.
- `abs_suzukiCoupledError_le` — **Theorem B, equations `(8)`--`(9)`**: an explicit absolute
  constant `C(ω) = 2 + 2/(1-2ω) + 1/((1+ω)2ω)` with `|E_ω(X)| ≤ C(ω) X^{1-ω}` for every `X ≥ 1`.

Reused corpus assets (no duplication): `RHTower.powerSumRemainder` and
`RHTower.abs_powerSumRemainder_le` (`|R_ω(Y)| ≤ (Y+1)^ω`), `RHTower.sum_rpow_neg_head_le`
(head of a `p`-series below the abscissa), `RHTower.tsum_add_rpow_neg_le` (tail above it),
`RHTower.shiftedEulerCoefficient_eq_prod`, `RHTower.ofReal_tsum_moebius_rpow`,
`RHTower.suzukiMainTermReal_natCast`.
