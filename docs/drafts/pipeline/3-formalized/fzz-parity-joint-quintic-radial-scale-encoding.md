# FZZ parity joint quintic-radial scale encoding

- **ID:** HC27
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** FZZ-P
- **Date:** 2026-08-28
- **Statement:** The literal negative-real Fermi coordinate is a strict positive-scale clock; paired with fixed-quintic phase, it is simultaneously phase-complete and scale-injective.

## Goal

Realize HC26's strongest positive survivor with an observable already present in the literal FZZ
source. Resolve every fixed-monomial phase collision without a target-fitted branch label.

## Result

Write

`g(a) = (a^2+1)^2 / ((a+1)(a^4+1))`.

For `a >= 1`, its derivative has the exact form

`g'(a) = (a^2+1)(-a^6-5a^4-4a^3+3a^2+4a-1) / ((a+1)(a^4+1))^2`,

and the polynomial numerator is strictly negative. Therefore:

1. `g` is strictly decreasing on `a>1`;
2. `beta ↦ (-Re y(beta))^2` and `beta ↦ -Re y(beta)` are strictly decreasing on `beta>0`;
3. the literal balanced source eigenline is injective on positive physical scales;
4. every radial value `c` in `(0,1)` determines one unique positive scale;
5. the joint report `beta ↦ (-Re y(beta), y(beta)^5)` has a unit-circle-surjective phase projection and is injective on `beta>0`.

This exactly repairs HC26's phase-only loss of scale using source-native Fermi data.

## Proof certificate

The numerator inequality follows from `1 <= a`, hence `1 <= a^2`, `a^2 <= a^4`,
`a^4 <= a^6`, and `a <= a^3`. The quotient-rule derivative is checked symbolically in Lean.
Strict negativity of the derivative gives strict antitonicity of `g`; composition with
`a=exp(beta)` transfers it to the squared radial coordinate. Positivity of `-Re y(beta)` turns the
squared comparison into an unsquared comparison. Existing radial surjectivity on `(0,1)` plus
strict antitonicity gives uniqueness. HC25 supplies quintic phase completeness, while equality of
joint reports forces equality of radial coordinates and hence equality of scales.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityJointQuinticRadialScaleEncoding.lean`.

Main declarations:

- `fzzCigarParityKreinEigenlineAlgebraicRadialSqDerivativeNumerator_neg`
- `hasDerivAt_fzzCigarParityKreinEigenlineAlgebraicRadialSq`
- `strictAntiOn_fzzCigarParityKreinEigenlineAlgebraicRadialSq`
- `strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re`
- `existsUnique_pos_fzzCigarParityKreinEigenline_neg_re_eq`
- `fzzCigarParityJointQuinticRadialEncoding_phaseComplete`
- `fzzCigarParityJointQuinticRadialEncoding_injOn_pos`
- `fzzCigarParityJointQuinticRadialEncoding_complete_and_injective`

Verification: direct `lake env lean` passed; target-only `lake build
GaloisForLFunctions.RHTower.FZZCigarParityJointQuinticRadialScaleEncoding` passed (9764 jobs); six
audited endpoints report only `[propext, Classical.choice, Quot.sound]`.

## Literature and corpus novelty audit

Mandatory corpus searches covered the exact FZZ Fermi ratio, strict radial monotonicity,
source-scale injectivity, and joint amplitude-phase encodings. The corpus contained generic joint
defect injectivity machinery, but no coefficient-faithful theorem for this Fermi profile and no
joint quintic-radial FZZ source result.

Primary-source searches checked Ikhlef--Jacobsen--Saleur, *An integrable spin chain for the
SL(2,R)/U(1) black hole sigma model* (arXiv:1109.1119); Jafferis--Schneider, *Stringy ER = EPR*
(arXiv:2004.05223); Jatkar, *The Spectrum of SL(2,R)/U(1) Black Hole Conformal Field Theory*
(arXiv:hep-th/9203063); and Israel--Pakman--Troost, *D-branes in N=2 Liouville theory and its
mirror* (arXiv:hep-th/0405259). They study cigar spectra, reflection data, densities, and mirror
descriptions; searches found no exact monotonicity theorem for this coefficient-faithful Fermi
ratio or this joint source encoding. Novelty claim is bounded to corpus plus these searches as of
2026-08-28.

## Gates

- [x] 0 -> 1: source-pure monotonicity attack and explicit joint reporter
- [x] 1 -> 2: dependency-closed paper proof
- [x] 2 -> 3: unconditional Lean theorem, target build, axiom audit
- [ ] 3 -> 4: standalone publication draft

## Positive survivor

- **Exact new insight:** phase completeness and source-scale determinism coexist once the literal
  monotone Fermi radial coordinate is retained.
- **Sharp boundary:** phase alone is terminal by HC26; one source-native radial coordinate suffices
  to separate every collision.
- **Status:** dependency-closed and formalized.

## Remaining burden

Derive the phase and radial reports jointly from actual FZZ/GFZZ parity-delay dynamics on divisor
modes. HC27 proves source capacity and deterministic parametrization, not a divisor landing law.

## Log

- 2026-08-28 — conjectured from HC26's positive survivor and HC23's exact Fermi ratio
- 2026-08-28 — exact derivative and strict radial monotonicity proved
- 2026-08-28 — joint encoding formalized, wired, target-built, and axiom-audited
