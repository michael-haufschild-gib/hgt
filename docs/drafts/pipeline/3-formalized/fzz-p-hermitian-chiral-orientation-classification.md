# FZZ-P Hermitian chiral orientation classification

- **ID:** FZZ-P-HC1
- **Stage:** 3-formalized
- **Type:** THEOREM / source-side classification
- **Source:** `rh-current-frontier-map.md` · FZZ-P dynamical orientation
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityHermitianChiralOrientationClassification`
- **Statement:** On the literal all-scale FZZ parity Krein conjugate pair, the full
  four-real-parameter Hermitian quadratic family distinguishes the two orientations exactly through
  its imaginary off-diagonal coefficient.  Equality, inequality, and both strict orderings are
  classified at every positive scale.

## Result

Write

`A(a,b,c,d) = [[a, b + i c], [b - i c, d]]`

and let `v₊(beta)` and `v₋(beta)` be the literal positive- and negative-imaginary FZZ parity Krein
eigenvectors.  For every real scale `beta`,

`Q_A(v₊) - Q_A(v₋) = -4 Q(beta) c sqrt(Delta(beta))`.

For `beta > 0`, both `Q(beta)` and `Delta(beta)` are strictly positive.  Therefore:

1. `Q_A(v₊) = Q_A(v₋) ↔ c = 0`;
2. `Q_A(v₊) ≠ Q_A(v₋) ↔ c ≠ 0`;
3. `Re(Q_A(v₊)-Q_A(v₋)) < 0 ↔ 0 < c`;
4. `0 < Re(Q_A(v₊)-Q_A(v₋)) ↔ c < 0`.

The exact antiunitary law is also formalized: coordinatewise complex conjugation sends the reporter
coefficient `c` to `-c` and fixes `a,b,d`.  Every reporter value is real.

## Paper proof

Put `Q=Q(beta)`, `P=P(beta)`, and `S=sqrt(Delta(beta))`.  The source eigenvectors are

`v₊=(Q,-P+iS)` and `v₋=(Q,-P-iS)`.

All four quantities are real.  Expanding the Hermitian form on `v₊` gives

`aQ² + d(P²+S²) - 2bQP - 2cQS`.

On `v₋`, the diagonal terms and real-symmetric cross term are unchanged, while the chiral term is
`+2cQS`.  Subtraction proves the displayed identity.  Positive-scale source theorems give `Q>0`
and `S>0`; cancellation, noncancellation, and sign equivalences follow.  No hypothesis remains open.

## New route knowledge

The previous FZZ-P burden asked vaguely for an interacting or off-diagonal dynamical reporter.  This
classification is sharper:

- diagonal and real-symmetric off-diagonal interactions are exactly blind;
- nonzero imaginary off-diagonal coefficient is necessary and sufficient;
- its sign fixes orientation with no scale exception on the positive ray;
- unit `i sigma_y`-type coupling is an explicit strict source-side survivor.

Thus the surviving FZZ/GFZZ dynamical burden is no longer “find a Hermitian interaction.”  It is:
construct a source-native physical interaction whose compression has nonzero chiral coefficient,
then prove Xi divisor landing into the classified eigenlines.

## Corpus audit

Mandatory searches:

- `scripts/formal_tools.py research "FZZ antiunitary invariant projective observable conjugate Krein pair orientation blindness"`
- `scripts/formal_tools.py research "FZZ conjugate pair Hermitian quadratic observable imaginary off diagonal chiral orientation classification"`
- `scripts/formal_tools.py research "two by two Hermitian quadratic form conjugate vectors difference imaginary offdiagonal"`

The corpus contained the all-scale FZZ pair and related CCM chiral operators, but no FZZ-specific
Hermitian iff-classification.  An earlier conjecture that antiunitary-invariant projective data would
identify the two eigenlines failed: the canonical antiunitary fixes each line projectively.  The
failed conjecture forced the stronger coefficient-level classification proved here.

## Literature boundary

Closest checked primary sources:

- Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*, arXiv:0805.3931, proves cigar / sine-
  Liouville duality and correlation-function matching:
  https://arxiv.org/abs/0805.3931
- Pakman, *FZZ Scattering*, arXiv:hep-th/0606067, studies exact reflection coefficients:
  https://arxiv.org/abs/hep-th/0606067
- Ashok--Troost, *A Twisted Non-compact Elliptic Genus*, arXiv:1101.1059, derives cigar continuum
  spectral asymmetry from reflection amplitudes: https://arxiv.org/abs/1101.1059
- Kapitula--Kevrekidis--Yan, *The Krein Matrix*, arXiv:1212.2951, develops general Krein collision
  theory: https://arxiv.org/abs/1212.2951

Targeted exact-object and mechanism searches located no theorem joining the literal dilated FZZ
source eigenpair to the four-parameter Hermitian coefficient classification above.  This supports
“no collision located,” not an absolute global priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityHermitianQuadraticObservable_star_self`
- `fzzCigarParityHermitianQuadraticObservable_conjugate_eq_neg_chiral`
- `fzzCigarParityDilatedTwoScaleConjugateKreinEigenvector_eq_star`
- `fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub`
- `fzzCigarParityHermitianQuadraticObservable_conjugatePair_eq_iff`
- `fzzCigarParityHermitianQuadraticObservable_conjugatePair_ne_iff`
- `fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub_re_neg_iff`
- `fzzCigarParityHermitianQuadraticObservable_conjugatePair_sub_re_pos_iff`
- `fzzCigarParityRealSymmetricQuadraticObservable_conjugatePair_eq`
- `fzzCigarParityUnitChiralQuadraticObservable_conjugatePair_sub_re_neg`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- no frontier-map edit.

## Gates

- [x] 0 → 1 in-progress: exact source conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: unconditional Lean theorem package, targeted build and axiom audit green
- [ ] 3 → 4 publication-ready: independent specialist priority and physics audit

## Log

- 2026-08-28 — Created after antiunitary-invariance conjecture failed.
- 2026-08-28 — Exact gap, iff/non-iff, sign, antiunitary, and real-symmetric no-go package proved in
  Lean and promoted to Stage 3.
