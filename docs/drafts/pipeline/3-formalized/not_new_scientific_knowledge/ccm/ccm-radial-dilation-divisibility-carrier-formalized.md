# Radial dilation divisibility carrier — formalized closure

- **ID:** `ccm-radial-dilation-divisibility-carrier-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-radial-dilation-divisibility-carrier.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCM.CCMRadialDivisibilityCarrier`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)` | `radialComponent` | `radialComponent q λ n s = √(λ e^s) · q(n·(λ e^s))` |
| `(4)` | `radialComponent_add_log` | the dilation identity `H n (s + log m) = √m · H (m n) s`. It needs only `0 < m`; the hypothesis `0 ≤ λ` is unnecessary, since `√(mx) = √m √x` follows from positivity of `m` alone |
| `(5)` | `sum_radialComponent_add_log` | translation by `log m` selects exactly the radial indices divisible by `m` |
| `(6)`–`(7)` | `divisibleTail`, `sum_divisors_moebius`, `moebius_recovery` | the finite Möbius recovery. `∑_{d ∣ k} μ d = [k = 1]` is derived from `moebius_mul_coe_zeta` and holds for every `k` including `k = 0`, so the card's nonvanishing side condition is unnecessary. The reindexing is the bijection `(d,r) ↦ (dr, d)` |
| `(8)`–`(11)` | `eq_zero_of_powerSums_tendsto` | the algebraic core of the exact finite radial dimension. The card proves independence by a generalized Vandermonde determinant and Schur-polynomial positivity at positive nodes; the Lean proof uses an elementary dominant-term limit — dividing `∑_{n ≤ K} a n n^{r i} = 0` by `K^{r i}` sends every lower node to zero because `n/K < 1`, forcing `a K = 0`, and descending induction finishes. Needs only that the exponents tend to infinity |

## Axioms

`#print axioms` on every theorem returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

Genuinely analytic, and not proved by the card's algebraic core: Poisson summation `(3)`; entirety of
`q_λ` with the identity-theorem step reducing `(8)` to the power-sum relations `(11)`; the diagonal
mass `(14)`, an improper-integral change of variables; and the Gram/autocorrelation estimates behind
`(13)` and `(18)`.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
