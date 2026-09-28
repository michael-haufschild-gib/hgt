# Route E coprime square-root Möbius sign density

- **ID:** `ROUTE-E-COPRIME-SQRT-MOBIUS-SIGN-DENSITY-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ALL-INTERVAL ARITHMETIC CAPSTONE
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../route e/route-e-coprime-square-root-mobius-product-sign-law.md`
- **RH used:** no
- **Computation used:** no

## Exact theorem package

Let `balancedPairs x h` be ordered integer pairs `(n₁,n₂)` satisfying

```text
x ≤ n₁ n₂ ≤ x + h sqrt(x),    sqrt(x) ≤ n₁ ≤ 2 sqrt(x),
```

and let `coprimeSignClass x h s` retain the coprime pairs with
`μ(n₁) μ(n₂) = s`, for `s = ±1`. Define

```text
D = squarefreeDensity = 6/pi²,
A = coprimeSharedPrimeDensity = sum_p (p+1)^(-2).
```

Lean proves the elementary growth law

```text
sqrt(x) / log(log(3x)) → infinity.
```

It then instantiates the corpus's unconditional Mertens-rate pair theorem at `h(x)=sqrt(x)` and
proves, for every `ε>0` and either sign `s`, eventually

```text
D²/2 - D² A - ε
  ≤ #coprimeSignClass(x,sqrt(x),s) / (x log 2).
```

The already-formalized Euler estimate `A ≤ 13/36 < 1/2` makes the limiting margin strictly
positive. Hence, for each `s=±1`, every sufficiently large balanced product window `[x,2x]`
contains a coprime squarefree pair with Möbius product sign `s`.

No Matomäki--Radziwiłł premise, rate hypothesis, auxiliary axiom, or finite verification remains in
this square-root-window statement.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.Sieve.SqrtWindowLaw
```

Principal declarations:

```text
RHTower.Sieve.tendsto_sqrt_div_logLog_atTop
RHTower.Sieve.route_e_sign_density_sqrt_window
RHTower.Sieve.route_e_signClass_nonempty_sqrt_window
```

The module is umbrella-reachable through `GaloisForLFunctions.RHTower`. Direct
`lake env lean GaloisForLFunctions/RHTower/Sieve/SqrtWindowLaw.lean` passes. Axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact boundary

This closes coprime opposite-sign supply at the largest admissible window `h=sqrt(x)`. It does not
control multiplicity after pushing pairs through the product map, provide the physical prime-anchor
projection, or estimate the signed physical covariance. Those remain Route E's non-circular
transport obstruction.

## Log

- 2026-08-12 — source rechecked, axiom boundary audited, exact unconditional capstone promoted.
