# PCS reflection-odd co-shift singular class

## Result

All-prime co-shift row → singular `H¹ = (ℕ₊→ℂ)/ℓ²` → reflection-odd class
`[n⁻ˢ-n⁻⁽¹⁻s̄⁾]`.

- Class is zero iff `Re s=1/2`.
- Reflection negates class.
- Every finite coordinate truncation is zero in `H¹`; obstruction is genuinely cofinal/singular.
- Any linear boundary operator from any source module with square-summable range contains the reflected profile iff `Re s=1/2`.
- Global Xi-divisor class vanishing is iff RH; failure of RH produces a nonzero class at an Xi zero.

Formal module: `PrimeCoShiftReflectionOddSingularCohomology`.

## Consequence

Discharges PCS frontier's missing singular secondary-class construction and kills every regular `ℓ²`-valued boundary operator, independent of source domain or presentation. Remaining PCS survivor must have genuinely non-`ℓ²` image and prove source null-homology/admission; global null-homology is exactly RH, not proved here.

## Novelty audit

Corpus search found no reflected co-shift quotient class. August-2026 literature search found Hilbert spaces of Dirichlet series and multiplicative-shift work, but no matching class or finite-exact/global-singular theorem. Elementary `ℓ²` abscissa ingredients are classical; novelty claim is route-specific class and exact PCS closure.

## Audit

`lake env lean` and targeted `lake build GaloisForLFunctions.RHTower.PrimeCoShiftReflectionOddSingularCohomology` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Global lint remains red only on unrelated pre-existing unwired modules.
