# One-prime fractional polynomial carrier

- **ID:** `suzuki-one-prime-fractional-carrier`
- **Stage:** 3-formalized (paper proof; Lean certificate `../../3-formalized/not_new_scientific_knowledge/suzuki-one-prime-fractional-carrier-formalized.md`)
- **Type:** operator infrastructure / weighted valuation representation
- **Scientific status:** `[MATHEMATICALLY STANDARD] [CORPUS-GAP CLOSED] [NOT RH]`
- **Route:** O, completed Suzuki/Evans branch

## Frontier correction

The surviving rank-one Gamma window uses the nonintegral exponent

```text
kappa = 2/3.
```

Earlier corpus infrastructure proved polynomial valuation-shift bounds only for natural-number
exponents. It therefore did not construct the fractional carrier invoked by the rank-one
rough-primitive Hardy proof. This card closes that exact gap.

## Weight and cocycle

For a valuation vector `nu in Z^d`, write `|nu|_1` for its orbit length and define

```text
w_kappa(nu) = (1 + |nu|_1)^(-kappa),
r_kappa(s,nu) = w_kappa(nu) / w_kappa(nu+s).
```

The triangle inequality gives

```text
1 + |nu+s|_1 <= (1+|nu|_1)(1+|s|_1).
```

For every `kappa >= 0`, monotonicity and multiplicativity of real powers therefore give

```text
|r_kappa(s,nu)| <= (1+|s|_1)^kappa.                    (1)
```

Moreover the ratios telescope exactly:

```text
r_kappa(s,nu) r_kappa(t,nu+s) = r_kappa(s+t,nu).       (2)
```

Thus the weighted shifts

```text
(S_s Z)(nu) = r_kappa(s,nu) Z(nu+s)
```

form an exact representation:

```text
S_s S_t = S_(s+t).                                     (3)
```

Polynomial growth is a norm effect caused by the changed metric, not a defect in the valuation
action.

## Rank-one `2/3` carrier

For `d=1`, `kappa=2/3`,

```text
sum_(n in Z) w_(2/3)(n)^2
 = sum_(n in Z) (1+|n|)^(-4/3) < infinity.             (4)
```

Applying the standard weighted-shift energy inequality to `(1)` gives

```text
sum_n |(S_s Z)(n)|^2
 <= (1+|s|)^(4/3) sum_n |Z(n)|^2.                      (5)
```

Equivalently, the operator norm grows at most as `(1+|s|)^(2/3)`. Equations `(2)`--`(5)` construct
the literal rank-one fractional polynomial group used by the low-rank Gamma argument.

## Scope and novelty boundary

Weighted shifts and submultiplicative polynomial weights are standard. No external novelty is
claimed. Route-level advance is precise: fractional carrier construction and its group law are now
closed; remaining low-rank analytic gate is the Gamma-resolvent one-block estimate and its
vector-valued Fourier/Bochner assembly.

## Gates

- [x] fractional weight defined
- [x] exact cocycle proved
- [x] exact group law proved
- [x] rank-one `2/3` square summability proved
- [x] polynomial lattice-energy estimate proved
- [ ] Gamma-resolvent one-block estimate
- [ ] full vector-valued completed-source assembly


## Stage-3 note

Every checked gate above is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeFractionalCarrier.lean`
(`fractionalPolynomialOrbitWeight`, `…_pos`, `fractionalPolynomialOrbitShiftRatio`,
`…_cocycle`, `fractionalPolynomialOrbitShift`, `…_add`,
`abs_fractionalPolynomialOrbitShiftRatio_le`,
`summable_fractionalPolynomialOrbitWeight_twoThirds_sq`,
`tsum_sq_fractionalPolynomialOrbitWeightedShift_le`), axiom audit clean.
The two unchecked boxes are forward route targets of the Gamma-resolvent lane, not debt of a
proven theorem on this card.
