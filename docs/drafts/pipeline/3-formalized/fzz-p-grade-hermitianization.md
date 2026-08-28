# FZZ-P grade Hermitianization

- **ID:** FZZ-P-HC2
- **Stage:** 3-formalized
- **Type:** THEOREM / exact source-mechanism identification
- **Source:** FZZ-P-HC1 chiral survivor + literal all-scale FZZ grade crossing
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityGradeHermitianization`
- **Statement:** On every two-coordinate state, the imaginary part of the literal FZZ Krein grade
  crossing is exactly the unit imaginary off-diagonal Hermitian reporter multiplied by the positive
  source normalization `-Q(beta)/2`.

## Main law

For every real scale `beta` and every `u : ℂ × ℂ`,

`2 Im(C_beta(u)) = -Q(beta) Re(H_chiral(u))`,

where

- `C_beta(u)=B_beta(u,D u)` is the literal dilated FZZ source-grade crossing;
- `H_chiral=H(0,0,1,0)` is the Hermitian block `[[0,i],[-i,0]]`.

At `beta>0`, `Q(beta)>0`, and hence:

1. `Im(C_beta(u))>0 ↔ Re(H_chiral(u))<0`;
2. `Im(C_beta(u))<0 ↔ Re(H_chiral(u))>0`;
3. `H_chiral(u)=0 ↔ Im(C_beta(u))=0`.

For an arbitrary Hermitian reporter `H(a,b,c,d)`, its antiunitary-odd part is exactly

`H(u)-H(conj u)=2c H_chiral(u)`.

Combining both identities gives the complete all-state blindness classification

`H(u)=H(conj u) ↔ c=0 or Im(C_beta(u))=0`

at every positive scale.

## Paper proof

Let `z=conj(u₁)u₂`.  Expanding the literal grade projection gives

`C_beta(u)=Q(beta) z + R(beta) conj(u₂)u₂`.

The second summand is real, so `Im(C_beta(u))=Q(beta) Im(z)`.  Direct expansion of the unit chiral
Hermitian form gives

`H_chiral(u)=i z - i conj(z)=-2 Im(z)`.

This proves the main law.  The full Hermitian reporter is affine in `c`; conjugation reverses `c`
and fixes `a,b,d`, so subtraction gives `2c H_chiral(u)`.  Since `Q(beta)>0` for `beta>0`, the sign
and zero-wall equivalences follow.  No premise or unproved dependency remains.

## New route knowledge

FZZ-P-HC1 reduced Hermitian orientation to one chiral coefficient but appeared to leave a new
finite-block producer to construct.  FZZ-P-HC2 removes that burden: the already literal,
coefficient-faithful source grade is precisely the required Hermitian chiral reporter after taking
its imaginary part and dividing by the positive source coefficient.

Consequences:

- grade-crossing orientation and Hermitian chiral orientation are not independent mechanisms;
- their chambers and zero walls agree on the entire two-coordinate state space;
- no separate finite-block Hermitian interaction is needed to orient the source pair;
- remaining RH-strength FZZ-P core is the full interacting FZZ/GFZZ divisor incidence/landing law,
  not finite-block source orientation.

## Corpus audit

Mandatory searches:

- `scripts/formal_tools.py research "FZZ grade crossing Hermitian imaginary off diagonal sigma y source native interaction"`
- `scripts/formal_tools.py research "FZZ Krein grade crossing quadratic observable eigenvector imaginary orientation"`
- `scripts/formal_tools.py research "FZZ source chiral coupling Xi divisor eigenline landing"`

The corpus contained both exact ingredients but no identification theorem or all-state blindness
classification.

## Literature boundary

Checked primary neighbors:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Ashok--Troost, cigar continuum spectral asymmetry, arXiv:1101.1059:
  https://arxiv.org/abs/1101.1059
- Kapitula--Kevrekidis--Yan, Krein matrix and signature theory, arXiv:1212.2951:
  https://arxiv.org/abs/1212.2951
- Kollár--Miller, graphical Krein signatures and Evans--Krein functions, arXiv:1209.3185:
  https://arxiv.org/abs/1209.3185
- Chernyavsky--Kevrekidis--Pelinovsky, real Krein quantities in Hamiltonian and PT-symmetric
  systems, arXiv:1711.02191: https://arxiv.org/abs/1711.02191

Exact-object searches found no paper identifying the literal FZZ parity grade with the unique
Hermitian chiral reporter or proving the all-state disjunction above.  Status is “no collision
located,” not an absolute priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityHermitianQuadraticObservable_sub_realSymmetric`
- `fzzCigarParityHermitianQuadraticObservable_antiunitaryOddPart`
- `fzzCigarParityDilatedTwoScaleGradeCrossing_im_eq_chiral`
- `fzzCigarParityHermitianUnitChiral_eq_normalizedGradeCrossing`
- `fzzCigarParityDilatedTwoScaleGradeCrossing_im_pos_iff_chiral_neg`
- `fzzCigarParityDilatedTwoScaleGradeCrossing_im_neg_iff_chiral_pos`
- `fzzCigarParityHermitianUnitChiral_eq_zero_iff_gradeCrossing_im_eq_zero`
- `fzzCigarParityHermitianQuadraticObservable_antiunitaryBlind_iff`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 → 1 in-progress: corpus-led conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 → 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured after FZZ-P-HC1 isolated the chiral coefficient.
- 2026-08-28 — Universal identity, sign/zero-wall equivalences, and all-state blindness
  classification proved and formalized.
