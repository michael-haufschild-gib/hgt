# Separate the density intake from the external zero-exclusion argument

- **ID:** review-2910-w10-distinguish-density-and-zero-exclusion
- **Stage:** 1-in-progress
- **Type:** SOURCE AUDIT / formalization programme
- **Source:** W10 of the obstacles summary.

## Source correction

W10 and §2.4 conflate two different papers. The local `ChenGuptaLi*` modules trace to
[Chen–Gupta–Li, arXiv:2507.08296v2](https://arxiv.org/html/2507.08296v2),
*Large Value Estimates for Dirichlet Polynomials with Characters and Zero Density of
Dirichlet L-Functions*. Theorem 1.2 is a density estimate. Its q=1 specialization already
has exponent 30/13; the uniform all-moduli simplification has exponent 7/3.
Neither is a fixed zero-free half-plane. The paper's applications explicitly retain a
separate zero-free-region input. Local provenance is also recorded in
`guth-maynard-large-values-lean-programme.md`, including the actual Lemma 6.2 contour intake.

The linked [OpenAI preprint](https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
has a different argument: cubic-theta reflection, compensated character sums and continuation
of reciprocals over the Eisenstein field. It is not authored by Chen–Gupta–Li.
Source pinned at commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
Its published Lean solution entry is
`OAI.NumberTheory.DirichletL.Nonvanishing`, through
`Detector.FinalAssemblyUnconditional`, `Energy.CertifiedExistence`,
`Detector.FinalAssemblyCertifiedBands`, and `Moments.DetectorPlainSlotProfile`.
Read the actual solution modules: `ComparatorChallenges` contains statement stubs and must
not be mistaken for the proof. No external theorem has been accepted or imported locally.

## Corrected work, retaining the intended endpoint

1. Finish and audit the actual CGL contour/density intake on its own statements.
2. Audit the separate OpenAI continuation argument and its dependency closure before attempting
   a local zero-exclusion capstone. Read source mathematics; do not accept advertised validation.
3. Derive any exponent/modulus threshold from that argument's actual inputs. A substitution of
   30/13 or DH into an unspecified CGL-to-exclusion implication has no mathematical meaning.
4. Record the positive density survivor and its exact q=1 calibration in Lean.

## Current evidence

- [x] Primary CGL introduction and Theorems 1.1–1.2 read; local provenance checked.
- [x] OpenAI introduction, solution entry and final assembly source read.
- [ ] External continuation argument and transitive proof audit.
- [ ] CGL remaining leaf audits and density capstone.
- [ ] Symbolic exponent calibration and proof that the density envelope alone permits a singleton.
- [ ] Local zero-exclusion theorem, if the separate source argument survives audit.

This correction does not finish W10 and does not refute either paper.

## Exact modulus calibration: paper proof

Put δ=1−σ>0 and q,T>0. The logarithm of the ratio of CGL's first source power
to its second is `δ(log q−12 log T)/39`. Consequently the first dominates precisely
when `q≥T^12`, with equality exactly at that boundary. This locates the genuine
modulus crossover in the source estimate; it is not a zero-free abscissa.
For q=1 and T≥1 the sum lies between `T^(30δ/13)` and twice that power.
At σ=7/8, the exponents are 15/52 for q=1, 7/24 in the uniform all-moduli
envelope, and 1/4 for a density-hypothesis envelope. All are positive, so these
upper envelopes permit a singleton zero count at every sufficiently large height.
The existing `DensityEnvelopeNoGo` supplies the latter obstruction for arbitrary
nonnegative density exponent and logarithmic loss. Formalization in progress.
