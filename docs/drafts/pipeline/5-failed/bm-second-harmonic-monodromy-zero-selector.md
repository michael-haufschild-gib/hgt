# BM second-harmonic monodromy-zero selector

- **Route:** force critical-line incidence from vanishing nonresonant `++` horizon monodromy
- **Status:** `FAILED / RETIRED`
- **Date:** 2026-08-27
- **Parent:** `bm-third-order-peierls-polarized-causal-cut.md`

## Frozen claim

The complementary `++` Frobenius branch has a lateral monodromy jump whose Xi-fibre zero locus is
the critical line, so causal consistency could force RH by forcing that jump to vanish.

## Killing mechanism

Exact BM substitution gives complementary exponent

\[
\lambda_{++}=1-c(\omega_{++})=4n+3+2i\chi.
\]

Its counterclockwise and clockwise multipliers are

\[
M_+=e^{2\pi i\lambda_{++}}=e^{-4\pi\chi},\qquad
M_-=e^{-2\pi i\lambda_{++}}=e^{4\pi\chi}.
\]

Thus `M_+ - M_- = 0` implies equality of norms. Injectivity of the real exponential then forces
`Re chi = 0`. Corpus Xi angular momentum instead satisfies `Re chi != 0` on every divisor fibre.
The jump is therefore nonzero everywhere in the relevant Xi family, not zero exactly off or on the
critical line.

## Strongest positive survivor

For the positive-real radial branch `h(z)=exp(lambda_++ log z)`, the exact BM integrating factor
obeys

\[
p_{++}(z)h'(z)=\lambda_{++}\sqrt{1-z}\longrightarrow\lambda_{++}.
\]

This gives a canonical nonresonant horizon Wronskian normalization. Its explicit nonzero lateral
jump distinguishes augmented causal branches even though the same-projective outer AdS determinant
vanishes.

## Audits

- **Paper proof:** dependency-closed exponent, Wronskian, exponential, and norm calculation
- **Lean:** `[LEAN-PROVED]`
  `ThetaCuspHawkingBMSecondHarmonicHorizonWronskianMonodromy.lean`; direct Lean and targeted build
  pass; axioms only `propext`, `Classical.choice`, `Quot.sound`
- **Literature:** exact hypergeometric BM radial solutions are external input; audited sources do not
  identify this nonresonant second-harmonic jump as an RH selector or augmented cubic Peierls block

## No-go closure

- **Exact killing theorem/mechanism:**
  `d4BMXiPlusPlusFrobeniusMonodromyJump_ne_zero`
- **Strongest positive survivor:** exact horizon Wronskian limit and explicit lateral jump
- **New insight:** `++` horizon branch data are universally nontrivial on Xi fibres and must enter
  causal branch normalization; they cannot provide the final critical-line zero locus
- **Status:** survivor fully proved on paper and formalized in Lean
- **Next hard problem:** construct augmented retarded/advanced affine response maps whose difference
  incorporates this normalized horizon jump, then prove full horizon-plus-AdS Green reciprocity

## Survivor continuation

`ThetaCuspHawkingBMSecondHarmonicComplementaryHypergeometric.lean` now constructs the genuine
complementary `₂F₁` factor with radius one on every Xi fibre. Its coefficient recurrence, formal
Gauss Euler equation, and first two analytic derivatives are Lean-proved in the subsequent formal
ODE and analytic-derivative modules. Remaining gap is analytic residual identification followed by
the exact full-branch radial equation and endpoint reciprocity.
