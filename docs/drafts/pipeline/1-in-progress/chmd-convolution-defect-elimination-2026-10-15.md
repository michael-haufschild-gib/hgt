# CHMD convolution and off-line defect elimination

Status: IN PROGRESS. Target remains an unconditional Lean proof of RH through CHMD.

## Scope and gates

- Corpus-only research; no external literature, numerical experiments, new premises, or axioms.
- A new bound, RH equivalence, or conditional receiver does not meet the requested contribution.
- Read current Lean source; preserve pre-existing work in Stage 22 and Meyer modules.
- Compile only required leaves, one foreground Lean process at a time; final audit with
  `lake env lean <module>`. Wire any finished new leaf into RHTower; run formal lint.

## Current evidence

- `CHMDForcedSpectralMeasureAndOffLineDefectWave` constructs a finite positive measure
  unconditionally, but its equality with the causal wave remains equivalent to RH.
- `CHMDStage16ZeroSideSymmetriesAndXiConvolutionAnnihilation` proves exact global
  convolution annihilation by the lifted Xi multiplier.
- `CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion` isolates a nonnegative
  hyperbolic defect. Its vanishing is not established.

## Work plan

1. Audit corpus mechanisms connecting convolution annihilation to positivity or spectral rigidity.
2. State and attack a concrete structural conjecture; record failed mechanisms precisely.
3. Close a dependency-complete paper proof before formalization.
4. Formalize the exact survivor, verify axioms and leaf compilation, update progress.

`update_plan` is unavailable in this session. This card tracks the work.
Serena symbol lookup rejects the Lean path as ignored; source inspection uses `rg` and bounded reads.

## Open core

Extract a sign-forcing mechanism from the actual arithmetic source, without assuming any
property already equivalent to RH. Xi annihilation alone does not yet supply this mechanism.

## Conjecture cycle: synchronized polar detector

The proposed implication from Xi annihilation alone to positivity fails as a proof mechanism:
the multiplier vanishes at every zero, including every possible off-line zero. No independent
sign has been obtained. The corpus already has general indefinite Hilbert decompositions and
multi-orbit negative-index results; reproducing those is not the missing advance.

Exact next statement: each actual zero admits an explicit four-point packet that annihilates
the polar frequency and has a nonpositive selected summand, strictly negative off-line.
This resolves the simultaneous phase and polar constraints for an individual mode, not the
sign of the full arithmetic sum. No RH equivalence is proposed.

### Dependency-closed paper proof

For a nontrivial zero write `w = kgFreq rho = u + iv`, `a = sqrt(7/4)`,
`b = kgWeight rho`, `h = 2*pi/u`, and `c = cos(h*a)`. Corpus theorems give
`u > 1` and `Re b > 0`. Use times `(0,h,2h,3h)` and real coefficients
`(1,-(1+2c),1+2c,-1)`.

With `q = exp(i*h*w)`, the packet polynomial is
`P(q) = (1-q)(1-2c*q+q^2)`. Its opposite-exponential product is exactly

`P(q)P(1/q) = 8(1-cos(h*w))(cos(h*w)-c)^2`.

At the real polar frequency `a`, the second factor is zero. At the selected frequency,
`h*u = 2*pi`, hence `cos(h*w) = cosh(h*v)` is real. The weighted real summand is therefore

`-8 (cosh(h*v)-1) (cosh(h*v)-cos(h*a))^2 Re b`.

All three unsigned factors are nonnegative. If `v != 0`, then `h > 0` and
`cosh(h*v) > 1 >= cos(h*a)`, so the expression is strictly negative. If `v = 0`, it is zero.
These are exact identities; no estimate or unproved analytic input is used.

Positive survivor: an explicit pole-free detector and exact hyperbolic factorization at every
actual zero. Paper proof complete. Lean verification pending. This does not yet meet the user's
requested significant advance toward an unconditional RH proof: other zero summands remain.

### Next conjecture after the detector

Seek an arithmetic source identity for the full four-point detector family that controls the
sum of the remaining modes. Mere cancellation by Xi multiples, termwise real-weight positivity,
and a positive real-axis shadow are insufficient. `[OPEN CORE]`: actual prime/archimedean
comparison for this family without importing the desired sign.
