# FZZ-P real-symmetric Hermitian orientation no-go

- **ID:** FZZ-P-HC1-NG
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Route:** FZZ-P dynamical orientation by fixed real-symmetric quadratic reporter
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityHermitianChiralOrientationClassification`

## Failed proposal

Distinguish the literal positive- and negative-imaginary FZZ parity Krein eigenlines using a fixed
real-symmetric quadratic interaction, including arbitrary diagonal weights and arbitrary real
off-diagonal mixing.

## Exact obstruction

Every such reporter has Hermitian coordinates `(a,b,0,d)`.  The formal theorem

`fzzCigarParityRealSymmetricQuadraticObservable_conjugatePair_eq`

proves, for every real scale `beta` without any positivity hypothesis,

`Q_(a,b,0,d)(v₊(beta)) = Q_(a,b,0,d)(v₋(beta))`.

This is not merely diagonal blindness.  The entire real-symmetric block is fixed by conjugation and
cannot read the orientation of a conjugate eigenpair.

## Strongest positive survivor

The full Hermitian classification proves that the imaginary off-diagonal coefficient `c` is the
unique surviving coordinate.  For `beta>0`, nonzero `c` is necessary and sufficient to distinguish
the pair, and its sign determines the strict order.  The unit chiral reporter `(a,b,c,d)=(0,0,1,0)`
is strictly oriented at every positive scale.

Paper proof and formal status:

- dependency-closed paper proof: complete;
- Lean status: complete and unconditional;
- survivor card: `../3-formalized/fzz-p-hermitian-chiral-orientation-classification.md`.

## Route consequence

Any FZZ/GFZZ proof using only real transfer matrices, diagonal occupations, real symmetric mixing,
or their fixed quadratic compressions cannot orient this source pair.  A viable source-native
dynamics must generate an anti-real Hermitian component, equivalently an `i sigma_y`-type chiral
coupling, and must connect that component to Xi divisor landing.

## Audit

Corpus searches found no existing FZZ-specific classification.  Checked FZZ duality, scattering,
spectral-asymmetry, and general Krein literature did not state this exact source theorem.  See the
survivor card for queries and primary references.  Novelty status is “no collision located,” not an
absolute priority claim.

## Log

- 2026-08-28 — Route retired after exact all-scale Lean obstruction; positive chiral survivor
  extracted and formalized before retirement.
