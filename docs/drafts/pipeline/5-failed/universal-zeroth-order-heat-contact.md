# Universal zeroth-order heat contact

- **ID:** universal-zeroth-order-heat-contact
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED EXACT POSITIVE SURVIVOR
- **Source:** Arithmetic Local Divisor Geometry; model calibration of Ward threshold rigidity
- **Claim under audit:** Evenness, monicity, real-axis nonnegativity, exact paired roots and arbitrary central multiplicity force first coefficient-cone contact at order zero under forward heat.

## Obstruction

For `P_m=X^(2m)(X²−a)²`, `a>0`, the full heat threshold is positive. At that threshold the constant coefficient is strictly positive; exactly one even coefficient through the degree vanishes, at degree `m+2+(m mod 2)`. Taking `m=2n` realizes every positive even contact degree `2n+2`. Thus none of the listed polynomial properties forces a zeroth-order contact. This does not refute the source-specific Ward rigidity question.

## Exact positive survivor

The family has an unconditional complete classification. Put `B=(2m+2)(2m+1)`, `C=(2m+4)(2m+3)`, `h=floor(m/2)` and

`τ_m=[B(h+1)+sqrt(B(h+1)(B−(C−B)h))]/(BC)`.

For every real `a,s`,

`(s≥0 and every coefficient of E_s[X^(2m)(X²−a)²] is nonnegative)`

if and only if `s≥max(a,0)τ_m`. The dimensionless thresholds decrease strictly with `m`, satisfy `1/(8m+10)≤τ_m≤1/(8m+5)`, and obey `(8m)τ_m→1`. For `a>0`, the contact degree above is exact and unique among even coefficients up to the degree, and the constant coefficient stays positive. The Gaussian moment normalization is `λ=2s`, with the positive per-order factor `λ^j(2j)!`.

Paper proofs: `../3-formalized/central-multiplicity-full-heat-cone.md` and
`../3-formalized/masked-pair-middle-order-contact.md`. Lean sources: `MaskedHeatIndex`,
`MaskedHeatContactIndex`, `MaskedPairHeatCone`, `MaskedPairHeatThreshold` and
`MaskedPairHermite`, all in the programme folder. Final plain module checks passed.
The complete classification, radical, contact and Hermite-conversion audits use only
`propext`, `Classical.choice` and `Quot.sound`.

## Closure gates

- [x] Negative claim tested against the entire growing-multiplicity family.
- [x] Strongest identified positive survivor given a dependency-closed paper proof.
- [x] Exact survivor formalized and transitive dependencies audited.
- [x] Final plain module checks and umbrella wiring.

The universal polynomial forcing principle is retired. Its strongest identified positive
survivor is the exact all-real classification and unique middle-order contact law above.
The arithmetic source rigidity endpoint remains open.
