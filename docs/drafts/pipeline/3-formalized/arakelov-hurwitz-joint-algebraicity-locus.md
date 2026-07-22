# Exact Arakelov–Hurwitz joint-algebraicity locus

## Status

Stage 3 — formalized in Lean 4.

## Claim

`[PAPER-PROVED]` For every `rho : ℂ`,

`IsAlgebraic ℚ (arakelovW rho) ∧ IsAlgebraic ℚ (monoScalar rho)`

holds if and only if `rho` is the complex image of a rational number.

## Scientific delta

The corpus contains the hard forward ingredient only: joint algebraicity forces `-2*rho` to be
rational. It does not state the exact global locus or prove the converse. The exact classification
is the strongest positive theorem exposed by failure of the Xi source predicate.

`[LITERATURE]` Gelfond–Schneider gives the irrational-algebraic exponent obstruction, while
classical roots-of-unity theory makes rational exponents algebraic. The audit found no source
stating this exact Arakelov-coordinate/continued-Hurwitz-monodromy locus. Expected label if closed:
`[NEW TO CORPUS] [NOT FOUND IN LITERATURE AUDIT] [ELEMENTARY SYNTHESIS]`, not a claim of a new
transcendence method.

## Proof obligations

1. Forward: use the existing Gelfond–Schneider collision, then solve `-2*rho = r` for `rho`.
2. Reverse Arakelov coordinate: rational casts are algebraic and algebraicity is closed under the
   field operations in `arakelovW rho = 1 - rho⁻¹`.
3. Reverse monodromy coordinate: rewrite `monoScalar (r : ℂ)` as
   `exp(2*pi*I*(-r))`; this is a root of unity, hence integral and algebraic.
4. Include `r=0`; Lean's total inverse makes the Arakelov formula well-defined there.

## Hostile tests

- Principal-branch ambiguity: avoided by the exponential definition of `monoScalar` in the reverse
  direction and by the already audited principal-power theorem in the forward direction.
- Nonzero denominator: no division by `rho` occurs in the logical recovery of rationality.
- Overclaim: classification does not locate Xi zeros and does not prove RH.

## Dependency-closed proof

### Forward direction

Assume both coordinates are algebraic. The existing Gelfond–Schneider collision supplies
`r : ℚ` with `-2*rho = r`. Multiplication by `-1/2` gives `rho = -r/2`, hence `rho` is rational.

### Reverse direction

Write `rho = r` with `r : ℚ`. Rational casts are algebraic over `ℚ`; closure under inverse and
subtraction makes `arakelovW(r) = 1-r⁻¹` algebraic. Also

`monoScalar(r) = exp(-2*pi*I*r) = exp(2*pi*I*(-r))`.

The last value is a root of unity of order `den(-r)`, hence integral over `ℤ` and algebraic over
`ℚ`. This includes `r=0` because `den(0)>0` and Lean's field inverse is total.

## Classification

`[NEW TO CORPUS] [NOT FOUND IN LITERATURE AUDIT] [ELEMENTARY SYNTHESIS]`. Exact positive survivor;
not a source theorem for RH.

## Lean formalization

- `arakelovW_monoScalar_jointly_algebraic_iff_exists_rat`
- Targeted verification:
  `lake env lean GaloisForLFunctions/RHTower/XiArakelovHurwitzAlgebraicityCollision.lean`
