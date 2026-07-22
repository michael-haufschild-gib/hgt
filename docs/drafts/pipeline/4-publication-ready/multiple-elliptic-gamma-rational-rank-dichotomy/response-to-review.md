# Response to major-revision review

Source review: `docs/htzeta.md`

## Outcome

Manuscript has been upgraded from a rational-rank classification note to a two-theorem paper:

1. exact nome-rank classification of every finite Nishizawa period tuple;
2. exact translation-coset differential matroid of elliptic-gamma defects and quotients.

The second theorem states, for both the paired elliptic compositum and `C(z)`, that differential
transcendence degree of any finite shift packet is number of distinct nonzero classes modulo
`Z + Z sigma + Z tau`. It also strengthens source hypertranscendence to the paired elliptic base.

## Mathematical revisions

- Added differential-algebra preliminaries: field closure, transitivity, logarithmic-derivative
  equivalence, differentially algebraic base change, generated-field notation, and semilinear
  translation behavior.
- Expanded joint Ostrowski proof with induced semilinear action on Kahler differentials, support
  lowering, universal-derivation kernel, stability of finite algebraic extension, and semilinear
  trace compatibility.
- Replaced full-period-lattice argument by direct nondiscrete-period rigidity.
- Added named lemmas for nondiscrete periods, elliptic product field and base comparison,
  generic-fiber specialization, one-orbit boundary obstruction, and highest-pole persistence.
- Applied finite-family criterion to all shifts, proving private-orbit independence, zero-class
  loops, same-class parallelism, exact rank count, and logarithmic transfer to quotients.
- Added nome-rank identity
  `d_Q(tau) - 1 = rank_Z(<q_i>/torsion)` and its classification corollary.
- Added precise constructive rank-two reduction. An unconditional algorithm for arbitrary complex
  `omega` is not well-posed without an effective representation of coefficients and an effective
  Kato input; manuscript now states this boundary rather than suggesting nonexistent bounds.

## Positioning and references

- Central novelty is restricted to two complete classifications.
- Finite-family Ostrowski theorem is described as a common-trace formulation of known
  one-operator mechanism.
- Multiplication and orbital pole obstruction are explicitly described as known mechanisms in a
  new synthesis.
- Added Hardouin--Singer Proposition 3.1, Dreyfus--Hardouin--Roques--Singer Appendix B,
  Arreche--Babbitt Theorems 1.1 and 2.6, Felder--Varchenko multiplication formulas, and Kato's
  multiple-sine hypertranscendence paper.
- Added explicit comparison with elliptic isogeny and elliptic hypergeometric literature.

## Editorial revisions

- Renamed rank-three period group from `H` to `P`.
- Separated universal differential notation from extension degree notation.
- Replaced vague pair-extraction language by exact distinct-label statement.
- Reduced noncommuting-automorphism emphasis in abstract.
- Added proof-flow diagram.
- Updated title, abstract, cover letter, highlights, keywords, and conclusion.

## Lean status

Existing unconditional modules already prove exact natural-base defect and quotient matroids,
arbitrary-family rank count, exact resonance spectrum, and source hypertranscendence over paired
elliptic compositum. New capstone module
`GaloisForLFunctions.HTGeometry.EllipticGammaTranslationCosetRankLaw` packages those results into
paper-facing theorems and adds quotient-matroid transfer and quotient independence over genuine
rational-coordinate base. No analytic assumption, `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` declaration is introduced.

Full pointed rational-base upper structure additionally uses classical differential algebraicity
of elliptic function fields. Manuscript proves that standard step. Lean currently verifies
rational-base free nonzero classes and natural-base exact pointed structure; it does not encode
classical generation of every elliptic function field by Weierstrass functions as a new axiom.
