# CCM convolution prime-face/composite-apex separation universality law

- **ID:** LAW450
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus theorem-posting closure
- **Statement:** Every infinite Dirichlet-convolution observation on the first-clock irreducible-prime face is invariant under an arbitrary spike at composite `4`, while that excluded coordinate is a positive unit-amplitude atom that obstructs full apex majorization.

## Goal

Close the tempting but invalid lift from convolution/tilt rigidity on irreducible primes to
superlevel dominance on the full prime-power source. Identify the exact lost coordinate rather
than merely restating failure of majorization.

## Gates

- [x] 0 → 1  in-progress: literal common first-clock source and support cut identified
- [x] 1 → 2  fully-proven: dependency-closed source-observation separation proof below
- [x] 2 → 3  formalized: Lean theorem
  `ccmConvolutionPrimeFace_compositeApexSeparationUniversality`; exact-file check green
- [ ] 3 → 4  publication-ready: standalone paper pending

## Approach

For a prime `p`, `dirichletConvolutionSeries c f p` depends only on `f 1` and `f p`, by the
corpus prime-face differential theorem. Therefore two arithmetic sources agreeing at `1` and on
the filtered first-clock primes have identical aligned/counter observations after every
coefficientwise infinite convolution functional. A source spike supported only at `4` satisfies
those agreements because `4` is not prime, so it is invisible for every coefficient sequence,
background source, aperture, and spike amplitude.

At the negative-apex aperture, the same coordinate `4` lies in the full cutoff, has positive
critical Mellin weight, and has counter amplitude exactly `1`. Consequently the bad apex measure
has positive mass on the closed apex set while the continuous-plus-aligned measure has zero mass
there, refuting full apex majorization. Thus prime-face convolution rigidity factors through a
quotient that erases the precise composite coordinate carrying the obstruction.

## No-go closure

- **Exact killing theorem/mechanism:** the prime filter erases composite `4`; infinite
  convolution prime coefficients use only unit and prime source coordinates.
- **Strongest positive survivor:** universal extensionality of first-clock convolution
  observations plus invariance under an arbitrary composite-four spike.
- **New insight:** failure to lift is an information-loss theorem, not a missing inequality.
- **Status:** paper proof dependency-closed; exact Lean theorem and source-observation certificate
  formalized.

## Log

- 2026-07-23 — generated from
  `CCMConvolutionTiltOddsRigidityUniversalityLaw`,
  `CCMInfiniteConvolutionPrimeFaceRigidity`, and
  `CCMFirstClockApexSuperlevelMajorization`
- 2026-07-23 — corpus research found prime-face rigidity and the apex no-go separately, but no
  composite-spike extensionality/separation master theorem
- 2026-07-23 — exact Lean check passed; wired into `GaloisForLFunctions.RHTower`
- 2026-07-23 — post-proof arXiv mechanism search found general Dirichlet-convolution literature,
  but no first-clock prime-observation/composite-apex separation or arbitrary four-spike
  invariance theorem
