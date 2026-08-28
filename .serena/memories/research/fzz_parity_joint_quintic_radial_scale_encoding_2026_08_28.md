# HC27: FZZ parity joint quintic-radial scale encoding (2026-08-28)

Route: FZZ-P. Status: formalized positive survivor.

Module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityJointQuinticRadialScaleEncoding.lean`.

For the exact Fermi profile
`g(a)=(a^2+1)^2/((a+1)(a^4+1))`, Lean proves the derivative numerator
`-a^6-5a^4-4a^3+3a^2+4a-1` is negative for `a>=1`. Thus `g` is strictly decreasing on `a>1`,
and the literal source coordinate `beta ↦ -Re y(beta)` is strictly decreasing on `beta>0`.
Every `c` in `(0,1)` determines a unique positive scale.

The joint report `beta ↦ (-Re y(beta), y(beta)^5)` is unit-circle phase-complete in its second
coordinate and injective on positive scales. This is HC26's exact positive survivor: retaining one
literal radial Fermi coordinate resolves every phase-only collision without a target-fitted tag.

Strong endpoints:

- `strictAntiOn_fzzCigarParityDilatedKreinEigenline_neg_re`
- `existsUnique_pos_fzzCigarParityKreinEigenline_neg_re_eq`
- `fzzCigarParityJointQuinticRadialEncoding_complete_and_injective`

Remaining burden: actual FZZ/GFZZ dynamics must jointly produce radial and phase reports on divisor
modes. Audit: direct Lean and target-only build passed; six audited endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Frontier map was not edited.
