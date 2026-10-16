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
`b = kgWeight rho`, `m = zetaZeroConfig.mult rho`, `h = 2*pi/u`, and
`c = cos(h*a)`. Corpus theorems give `u > 1`, `m > 0`, and `Re b > 0`.
Use times `(0,h,2h,3h)` and real coefficients
`(1,-(1+2c),1+2c,-1)`.

With `q = exp(i*h*w)`, the packet polynomial is
`P(q) = (1-q)(1-2c*q+q^2)`. Its opposite-exponential product is exactly

`P(q)P(1/q) = 8(1-cos(h*w))(cos(h*w)-c)^2`.

At the real polar frequency `a`, the second factor is zero. At the selected frequency,
`h*u = 2*pi`, hence `cos(h*w) = cosh(h*v)` is real. The weighted real summand is therefore

`-8 m (cosh(h*v)-1) (cosh(h*v)-cos(h*a))^2 Re b`.

All unsigned factors are nonnegative. If `v != 0`, then `h > 0` and
`cosh(h*v) > 1 >= cos(h*a)`, so the expression is strictly negative. If `v = 0`, it is zero.
These are exact identities; no estimate or unproved analytic input is used.

Positive survivor: an explicit pole-free detector and exact hyperbolic factorization at every
actual zero. Paper proof and Lean verification complete. This does not yet meet the user's
requested significant advance toward an unconditional RH proof: other zero summands remain.

### Formalized detector and audit

Leaf: `formal/GaloisForLFunctions/RHTower/CHMDResonantPolarPackets.lean`, namespace
`RHTower.CHMDPolarDetector`; imported by `RHTower.lean`.

- `fourPoint_weight`: exact exponential-polynomial factorization.
- `detector_pole_zero`: exact polar cancellation.
- `selectedEnergy_eq`, `selectedEnergy_nonpos`: exact selected-zero formula and sign.
- `selectedEnergy_neg_iff_offLine`: strict negativity exactly off the critical line.
- `selectedEnergy_eq_zero_iff_criticalLine`: exact vanishing classification.
- `detectorEnergy_zero_side`, `detectorEnergy_prime_arch`: full zero sum and pole-free
  prime–archimedean identity. Neither theorem asserts a sign for the full sum.

Validation completed:

- `lake --old build GaloisForLFunctions.RHTower.CHMDResonantPolarPackets`: exit 0.
- `lake env lean GaloisForLFunctions/RHTower/CHMDResonantPolarPackets.lean`: exit 0,
  no diagnostics.
- `/tmp` axiom audit of all eight results above: only `propext`, `Classical.choice`,
  `Quot.sound`; no additional axiom or unproved premise.
- `scripts/formal_tools.py index`: exit 0; API, gap, and overview artifacts regenerated.
- `scripts/formal_tools.py lint`: exit 1 because concurrent modules
  `DeningerMeyerCausalReflectionCovariance`, `EvenSectorDetunedPackets`, and
  `EvenSectorDetunedReflection` were unreachable from the umbrella at audit time.
  No diagnostic named the CHMD leaf. Unrelated work was preserved.

The unconditional RH objective remains open. A local negative summand is not a negative
full zero sum, and a new formal lemma is not by itself a significant scientific advance.

### Next conjecture after the detector

Seek an arithmetic source identity for the full four-point detector family that controls the
sum of the remaining modes. Mere cancellation by Xi multiples, termwise real-weight positivity,
and a positive real-axis shadow are insufficient. `[OPEN CORE]`: actual prime/archimedean
comparison for this family without importing the desired sign.

### Follow-up source audit

Corpus searches for causal support, conserved energy, and negative-index mechanisms
completed without reported partial results. Compiler metadata still had many pending or
stale entries, so retrieval was treated as a source locator, never as proof verification.

- `kgFieldEnergy_conserved` in `KleinGordonExactConservation.lean` assumes an appropriate
  self-adjoint operator. No identification of its wave with the actual CHMD wave was obtained.
- `PaperPrimeArchCurrentOperator` constructs an actual self-adjoint multiplication
  operator, but its positivity theorem explicitly retains the missing arithmetic sign.
  Its `forall_operator_positive_iff_rh` is not a positivity producer.
- `XiWeilSpectralFoldIndexConservation` already gives exact finite negative-index
  classification for separated source packets. Repackaging that result would not remove
  the CHMD sign obstruction.

No further Lean receiver or bound was added. This is an unresolved proof mechanism,
not a proof that CHMD cannot work. The four-point detector remains the exact positive
survivor of this cycle; the original RH objective remains active.

## Current cycle: exact removal of the other-zero contributions

Previous turn classification: progress (detector build, direct audit, axioms, wiring,
and index completed), but no significant RH breakthrough. Current objective unchanged.

Local origin maximality does not establish positivity for general local packets. A source
search for an all-packet positivity producer returned conditional positivity machinery,
not such a producer. Do not formalize another local-to-global positivity receiver.

Exact next conjecture: every actual zero has an admissible even CHMD test, vanishing at
the two poles and at every zero outside its symmetry orbit, whose full zero-side energy
is nonpositive and strictly negative exactly off the critical line. This removes masking
by other zeros, including when the selected zero has arbitrary multiplicity.

Corpus attack: `XiWeilPolarization` already isolates simple zeros with removable divided
quotients; `XiThetaEigenGramLaw` computes their Gram law. `XiHedenmalmMultiplicityChain`
already supplies the full-order quotient with nonzero center value. The missing proposed
bridge is its admissible, pole-free, even CHMD realization and exact full-source sign.
No claim of external novelty; no new RH equivalence or bound is the intended result.

### Paper proof for the exact selector

At a centered Xi zero `a` of analytic multiplicity `m`, let `Q` be the terminal divided
quotient, so `XiC(z) = (z-a)^m Q(z)` and `Q(a) != 0`. Normalize `Q/Q(a)`; at every Xi
zero this is exactly the indicator of `a`, without a simplicity assumption. On any fixed
horizontal strip it retains Xi's exponential decay: outside a compact box `|z-a| >= 1`,
and inside that box continuity supplies the finite constant.

Multiply by `r(z)/r(a)`, where `r(z) = (z^2+1/4)/(z^2+9)`. This is holomorphic and
bounded on `|Im z| <= 9/4`, vanishes at `+i/2` and `-i/2`, and is nonzero at every
actual Xi zero. Call the resulting normalized cardinal function `B`.

Set `F(z) = i (B(z)+B(-z)-conj(B(conj z))-conj(B(-conj z)))`.
Then `F` is even and Schwarz-real, has the same strip decay, and vanishes at both poles.
At any Xi zero it equals `i` times a real signed orbit indicator. Hence `specSq F`
is a nonpositive real number at every zero, and is zero outside the selected orbit.
At `a`, it equals `-1` when `Re a != 0` and `Im a != 0`; actual Xi zeros have `Re a != 0`.
If `a` is real, every orbit indicator cancels. Absolute summability then proves the
full energy is nonpositive, strictly negative precisely off-line. Multiplicity contributes
a positive factor, never an extra premise.

Choose Xi strip decay rate `3/4`. The bounded filter preserves it, and
`sechWeight F = specSq F * cosh(z/2)^2` has positive decay rate `1/2` on the wider strip.
The existing unconditional sech representation therefore realizes the exact selector as
an integral against the original CHMD causal wave. Pole cancellation gives its exact
prime–archimedean expression. No sign for that source expression is assumed or established.

Paper proof and formalization complete. The remaining RH obstruction after this
construction is an independent arithmetic sign for these selected source expressions.

### Exact-selector formalization and audit (2026-10-16)

Leaf: `formal/GaloisForLFunctions/RHTower/CHMDExactDivisorPackets.lean`, namespace
`RHTower.CHMDExactPackets`; imported once by `RHTower.lean`.

- `zeroSelector_evenStrip`, `zeroSelector_multiplier`, `zeroSelector_pole_zero`:
  the constructed function is an admissible CHMD test with exact polar cancellation.
- `zeroSelector_zero_values`, `zeroSelector_eq_zero_outside_orbit`: exact divisor
  interpolation, including arbitrary analytic multiplicity.
- `zeroSelectorEnergy_eq`: full arithmetic energy equals the negative
  multiplicity-weighted squared orbit indicator; no remaining-zero tail.
- `zeroSelectorEnergy_nonpos`, `zeroSelectorEnergy_neg_iff_offLine`,
  `zeroSelectorEnergy_eq_zero_iff_criticalLine`: complete sign classification.
- `zeroSelectorEnergy_convolution`, `zeroSelectorEnergy_prime_arch`: identification
  with the original CHMD wave and the actual pole-free arithmetic source.

Validation completed:

- Complete `/tmp` proof: direct Lean exit 0, no diagnostics.
- `lake --old build GaloisForLFunctions.RHTower.CHMDExactDivisorPackets`: exit 0.
- `lake env lean GaloisForLFunctions/RHTower/CHMDExactDivisorPackets.lean`: exit 0,
  no diagnostics.
- `/tmp` axiom audit of all eleven results listed above: only `propext`,
  `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: exit 0, `formal lint passed`. This supersedes
  the earlier concurrent-unwired-module failure recorded above.
- `scripts/formal_tools.py index`: exit 0; API, gap, and overview artifacts regenerated.
- Scoped `git diff --check`: exit 0. No umbrella build, heartbeat increase, or new
  unproved declaration. Owned Lean commands ran sequentially and reached terminal exit.
- All fourteen owned temporary proof, axiom, search, and log files removed after
  recording the results; cleanup exit 0. No owned Lean process remains.

Assessment: verified structural progress from one selected summand to an exactly isolated
full CHMD energy, without a simplicity hypothesis. The underlying divided-quotient and
divisor sign-test ideas already exist in the Lean corpus. The new bridge is their
admissible, pole-free CHMD realization. This is not an unconditional RH proof and does
not by itself establish the requested significant scientific breakthrough.

### Next attack: Xi-null corrections and arithmetic source signs

An admissible correction `F -> F + XiC * G` preserves every divisor value and therefore
the full Weil energy. It can change the separate prime and archimedean expressions but
cannot change their difference. Thus a correction is useful only if it exposes an
independently provable source sign; cancellation alone supplies no sign.

Corpus-only deep retrieval completed with `partial = false` and full file inventory,
but many compiler records remain pending or stale. Its broad gauge query mostly returned
unrelated gauge and positivity-receiver declarations; the automatic sufficiency assessment
was not accepted as mathematical evidence.

Directly inspected `WeilWorkDeficitRestrictedXiDensity.dense_span_deficitXiShiftLp`:
Xi profiles with shifts in any nonempty interval span a dense subspace of real-axis
complex `L2`. Its statement supplies neither coefficient cost nor control of the prime
sum or the analytic strip topology. Consequently it cannot justify removing the prime
contribution in an admissible limit. Finite positive packet repairs likewise do not
provide a cost-free, all-prime Xi-null correction. No such limit or sign was formalized.

Next conjecture to attack: an exact nonnegative arithmetic decomposition for the selected
source family, using the Xi-null identities with a justified topology. Do not replace
this producer by a positivity assumption or another RH equivalence. The RH goal remains
active; this route has not been retired.

## Current cycle: isolate the complete arithmetic evolution (2026-10-16)

Previous goal turn: progress. Exact-selector build, direct audit, axiom audit, wiring,
index, lint, and scratch cleanup completed. RH remains open.

The attempted direct Hilbert sign argument does not close: the actual theta convolution
operator has dense range, and its reduced ordinary-L2 cokernel loses the divisor
(`XiThetaConvolutionDefectTrilemma`). The positive singular theta metric instead retains
a nonzero rank-two Green boundary term (`HedenmalmThetaMetricCommutator` and
`HedenmalmThetaSourceDifferentialGreen`). Polar cancellation in a CHMD test cannot be
identified with cancellation of that source boundary without a new proof. Existing
Hedenmalm--Weil eigenfunction polarization still retains the missing sign, and its
first-quotient realization degenerates at multiple zeros. No positivity receiver added.

Next exact conjecture: the selector isolates a complete arithmetic wave, not just its
value at time zero. Write `E = zeroSelectorEnergy rho`, `w = kgFreq rho`, and
`W(y) = cosineShiftFn Lambda (zeroSelector rho) y`. Then, unconditionally,

`W(y) = E Re cos(y w)`.

Paper proof: every other divisor orbit vanishes under the selector. Reflection leaves
`rhoC` unchanged, and conjugation conjugates it, so the real part of the cosine is one
common value on the selected orbit. Factor that value out of the absolutely convergent
zero sum. For the source realization, the multiplier `zeroSelector rho * cosh(z/2)`
retains positive strip decay and cancels the reference `sechHalf`; the existing shifted
cosine-kernel identity then isolates this same wave directly from the original CHMD wave.

The isolated arithmetic evolution exposes an exact positive square, without a sign
assumption on `E`. Its cosine-addition defect is

`2 W(s) W(t) - E (W(s+t)+W(s-t))
   = 2 E^2 Im(cos(s w)) Im(cos(t w))`.

Thus every finite quadratic combination of that defect is one real square. This is an
exact channel of rank at most one for the failure of real-frequency cosine dynamics.
It does not establish that the channel vanishes. Paper proof and formalization complete.

### Exact-evolution formalization and audit

Leaf: `formal/GaloisForLFunctions/RHTower/CHMDExactOrbitEvolution.lean`, namespace
`RHTower.CHMDOrbitEvolution`; imported once by `RHTower.lean`.

- `specSq_zeroSelector_complex`: exact complex selector-square values, with no imaginary
  remainder hidden by taking real parts.
- `orbitWave_eq`, `orbitWave_eq_cos_mul_cosh`: the whole actual arithmetic evolution is
  `E Re cos(t w) = E cos(t Re w) cosh(t Im w)`.
- `multiplier_selectorCosh`, `orbitWave_convolution`: an explicit admissible kernel extracts
  that evolution from the original CHMD causal wave at every real shift.
- `orbitWave_prime_arch`: the isolated arithmetic evolution has no polar term.
- `orbitAdditionDefect_eq`, `orbitAdditionDefect_quadratic`, `orbitAdditionDefect_nonneg`:
  exact factorization through one real channel and its unconditional finite-square law.

Proof audit: the zero-side formula is unconditional; the terminal quotient handles full
analytic multiplicity; real cosine values agree on the entire reflection/conjugation
orbit; every other zero contributes exactly zero. The convolution proof uses positive
strip decay of the literal selector-times-cosh multiplier. The final square identity is
the complex cosine addition law applied to this verified arithmetic evolution. No RH,
simplicity, source positivity, or unproved limiting premise enters these statements.

Validation completed:

- Complete `/tmp` proof: direct Lean exit 0, no diagnostics.
- `lake --old build GaloisForLFunctions.RHTower.CHMDExactOrbitEvolution`: exit 0.
- `lake env lean GaloisForLFunctions/RHTower/CHMDExactOrbitEvolution.lean`: exit 0,
  no diagnostics.
- `/tmp` axiom audit of all nine results listed above: only `propext`,
  `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py index`: exit 0; API, gap, and overview artifacts regenerated.
- `scripts/formal_tools.py lint`: exit 1, solely for concurrent unwired modules
  `OddWeilGramLimit`, `OddWeilResolventApproximation`, `OddWeilResolventArithmetic`, and
  `OddWeilResolventIntegral`. No diagnostic named the CHMD leaf. Their work was preserved.
- Tracked-file whitespace check: exit 0. New-file `git diff --no-index --check` emitted
  no whitespace diagnostic (its exit 1 reports the new-file difference).
- Audited leaf SHA-256: `20adbc5a4969ecbf6cca8819f20b3902178e8e7863cabf1d0134da8faf6f9d60`.
  No heartbeat increase, full/umbrella build, or concurrent owned Lean process.
- All nine owned temporary proof, name-probe, axiom, search, and log files removed;
  cleanup exit 0. No owned running process remains.

All three corpus searches completed with `partial = false`, full inventories, and no
reported retrieval error. Compiler metadata remained largely pending or stale, so each
used mathematical ingredient was checked in source and then in the actual Lean proof.

Assessment: the exact scalar detector now has an exact dynamical realization and an
explicit nonnegative defect form with one channel. This removes cancellation between
other modes throughout the evolution. It is structural progress, but does not supply
the requested decisive arithmetic exclusion or an unconditional RH proof. No external
novelty claim is made.

Next conjecture: evaluate this same addition defect through the actual prime--archimedean
source and obtain a source identity forcing its square to vanish. Do not assume the
desired reverse sign. Xi-multiple annihilation alone cannot provide it: every selected
mode remains at an Xi zero and satisfies those homogeneous annihilation identities.
The full RH objective remains active.

## Current cycle: exact arithmetic radical (2026-10-16)

The direct arithmetic-vanishing conjecture remains open. Inspection of the new
odd-resolvent Gram/continuation modules found an explicit odd-positivity premise;
the source identities inspected elsewhere retain a boundary or sign obstruction.
No unconditional reverse sign for the isolated addition defect was found.

Next conjecture: the radical of the actual CHMD arithmetic polarization on
admissible even Schwarz multipliers is exactly the ideal of functions vanishing
at every actual Xi divisor point. In particular this radical is power-saturated:
the arithmetic quotient contains no nonzero nilpotent multiplier classes, even
when Xi zeros have higher analytic multiplicity. This is a nullspace
classification, not a positivity claim or a new RH equivalence.

Paper mechanism: polarize the actual prime--archimedean energy. Its mixed form is
the absolutely convergent sum of multiplicity times Re(F(gamma)G(gamma)). For a
selected zero a, symmetrize the full-multiplicity cardinal quotient with scalar
conj(F(a)). The resulting admissible, pole-free test G has divisor values
conj(F(z)) times the nonnegative four-point orbit incidence count. Thus every
mixed summand is a nonnegative multiple of normSq(F(z)), and the summand at a
is strictly positive whenever F(a) is nonzero. A radical element must therefore
vanish at every divisor point. The reverse implication follows termwise; powers
then detect exactly the same vanishing set. No simplicity, source positivity,
growth conjecture, or new axiom is used.

Current status: paper argument and Lean formalization complete. This classifies
all invisible directions on the admissible multiplier class, but does not
eliminate the surviving off-line modes or prove RH.

### Formal implementation and scope

New leaf: `formal/GaloisForLFunctions/RHTower/CHMDArithmeticRadical.lean`.
For the existing `Multiplier` class, define the actual arithmetic energy E and
its real polarization B(F,G) = (E(F+G)-E(F)-E(G))/2. The leaf proves that B is
literally `evenWeilDensity vonMangoldt (F*G)` and equals its absolutely convergent
mixed divisor sum.

The pole-free evaluation dual T(a,F) satisfies, at every actual divisor point z,

    T(a,F)(z) = conj(F(z)) N(a,z),

where N counts z=a, -z=a, conj(z)=a, and -conj(z)=a, including collisions. Hence

    B(F,T(a,F)) = sum_z multiplicity(z) normSq(F(z)) N(a,z) >= 0,

with equality exactly when F(a)=0. No cancellation, simplicity premise, or
positivity assumption enters this construction. Both polar terms vanish in
the mixed density, so the same readout is an exact archimedean-minus-prime value.

Main consequences proved in the leaf:

- `sourceRadical_iff_divisor_zero`: full arithmetic radical equals divisor
  vanishing on this admissible class.
- `sourceResponses_eq_iff`: equality of all arithmetic responses is exactly
  equality of all divisor values.
- `sourceRadical_pow_iff`: a positive power is invisible exactly when its base
  is invisible. The arithmetic radical is power-saturated.

The admissible arithmetic quotient therefore forgets no divisor values and has
no hidden nilpotent multiplier classes. Analytic multiplicity remains a positive
weight; the proof does not assert simplicity or identify this radical with the
unsaturated principal ideal generated by Xi.

Limit: these are mixed evaluation-dual pairings. They do not give nonnegativity
of B(F,F). An off-line selector can retain its negative diagonal value while
having a positive pairing with its evaluation dual. The requested RH exclusion
is still absent; no replacement goal or completion claim is made.

Additional source check: `WeilPhiDoobArchimedeanJumpAndHalfLineFolding` already
has the exact positive archimedean and prime jump terms, but subtracts the cosh
mass. `WeilMarkovOddSectorTrivialZeroSquares` retains the half-line energy and
only signs the product-prime term for nonnegative input. Neither supplies the
missing diagonal sign. A future attack must retain and resolve that subtraction;
positive jump terms alone cannot be treated as a proof.

### Completed verification

- Scratch Lean check: exit 0. A nonfatal ring diagnostic was subsequently removed
  by a direct symmetry simplification; the built leaf has no new diagnostics.
- `lake --old build GaloisForLFunctions.RHTower.CHMDArithmeticRadical`: exit 0;
  leaf built in 37 seconds. No full or umbrella build.
- Required final `lake env lean GaloisForLFunctions/RHTower/CHMDArithmeticRadical.lean`:
  exit 0, no diagnostics.
- Ten `#print axioms` checks: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py index`: exit 0; refreshed API, gaps, overview and
  search index, with eight changed source files across concurrent work.
- `scripts/formal_tools.py lint`: exit 1 solely for the unrelated concurrently
  unwired `GaloisForLFunctions.RHTower.DeningerMeyerStrictCoupledSolvability`.
  No diagnostic concerns this CHMD leaf. Other sessions' files preserved.
- Umbrella imports the new leaf exactly once. Scoped tracked whitespace check:
  exit 0. New-file `git diff --no-index --check`: no diagnostics (exit 1 denotes
  the ordinary nonempty difference).
- Leaf SHA-256: `2b064a92f25c782210dbc6e691446997a80d65b78b23661196817eda6efb7f3e`.
- All eight owned temporary proof, name-probe, axiom, search, and log files removed;
  cleanup verified. No owned process remains running.

Both corpus searches reported `partial = false`, complete inventories and no
retrieval errors. Compiler metadata was largely pending/stale; used ingredients
were checked in source and in Lean. No numerical experiments or external sources.

The next conjecture remains a direct arithmetic production step: factor the
actual pole-free diagonal source form into positive terms while retaining the
Doob cosh subtraction. The new radical theorem prevents hiding that obstruction
inside an invisible correction. It does not resolve it. The unconditional RH
goal remains active.

## Current cycle: positive arithmetic divisor cuts (2026-10-16)

Direct diagonal positivity remains open. The exact Doob identity has two positive
jump forms minus `phiDoobCoshMass(v^2)`. The existing complete divisor expansion
in `WeilPhiDoobDivisorEnergy` retains arithmetic indexing but has a signed theta
fiber outside its central logarithmic interval; termwise positivity is unavailable.

New conjecture: fold the origin-crossing prime jumps before reindexing. Their
complete source is an absolutely convergent sum of finite divisor-cut energies
with nonnegative fibers, with no signed tails. For an edge m -> k=md inside
N=mdn, retain only log(m) < u < log(k). This forces 0 < u < log(N), where both
theta factors are positive. The exact change of variable u=x+log(m) identifies
the edge with the theta-expanded prime collar on 0<x<log(d). For odd v the
collar sum v(x)+v(log(d)-x) equals v(x)-v(x-log(d)).

Paper argument: restrict the existing absolutely integrable triple edge series
to each edge interval, translate to the common collar, sum both theta indices,
then group triples by N. Absolute convergence follows by domination by the
already proved full edge norm series. Finite divisor antidiagonal regrouping
gives the cut graph. Positivity is now termwise, because every active edge lies
inside the positive theta chamber. Combining with the existing half-line folding
retains the entire prime energy as twice the same-side energy plus this positive
arithmetic cut sum. Substitution into the actual Doob identity retains the exact
cosh subtraction; it does not assert diagonal positivity or RH.

Work plan: expose only needed existing reindex/integrability lemmas; formalize
the complete cut identity and positivity; wire, build leaf, direct Lean and axiom
audits, index/lint, clean owned scratch. No numerical experiments, improved-bound
deliverable, positivity premise, or new RH receiver.

### Positive-cut nullspace attack (2026-10-16, paper complete; Lean pending)

Conjecture: the complete origin-crossing divisor-cut sum has zero radical on continuous compactly supported real tests. This is a statement about the retained positive source component, not positivity of the full source.

Dependency-closed proof: nonnegative summable prime-crossing integrals sum to the cut sum. If the latter vanishes, every prime-crossing integral vanishes. For any prime power d, continuity and positivity of its coefficient and both original theta factors imply v(x-log d)=v(x) throughout the closed collar [0,log d]; endpoints follow by continuity. Compact support gives a radius R outside which v vanishes. For any fixed x, choose d=2^(k+1) with log d>|x|+|R|+1. If x>=0, its collar partner x-log d is outside support; if x<0, use the collar point x+log d, again outside support. Thus v(x)=0, including x=0. Conversely the zero test has zero cuts. This uses genuine unbounded prime powers and no numerical computation or prime-distribution premise.

The result rules out a hidden compact source mode annihilated by every positive crossing cut. It supplies no comparison with the negative cosh mass; that exact obstruction remains.

### Positive divisor-cut result — kernel audit complete (2026-10-16)

Classification: **PROGRESS**, not RH and not elimination of the original CHMD defect.

New leaf: `formal/GaloisForLFunctions/RHTower/CHMDPrimeDivisorCuts.lean` (445 lines), namespace `RHTower.CHMDPrimeCuts`.

- `cutDensity_nonneg`: every finite arithmetic product fiber is nonnegative after retaining only divisor edges crossing the logarithmic cut. `divisorCutEnergy_zero_outside` and `fiber_pos_on_central` supply the exact support/sign mechanism.
- `primeCrossing_hasSum_cuts` / `compact_primeCrossing_hasSum_cuts`: complete absolutely convergent crossing-prime source equals the divisor-cut sum. Both theta indices and all genuine prime powers remain; no finite truncation or changed arithmetic weights.
- `primeJump_eq_sameSide_add_cuts`: full prime source equals the two same-side pieces plus the cut sum for every continuous compactly supported real test, without a parity hypothesis.
- `doob_source_eq_positive_cuts_sub_cosh` (line 341): the original Doob/Markov source equals the archimedean jump energy, both same-side prime energies and the cut sum, minus the unchanged cosh mass.
- `collar_eq_of_primeCrossing_zero`, `exists_positive_primeJump_after`, `crossing_cuts_eq_zero_iff` (line 396), `crossing_cuts_pos`: the crossing-cut sum has exactly the zero null vector on continuous compactly supported tests. The proof uses closed-collar continuity and unbounded powers of two, not a numerical calculation or a prime-distribution assumption.

The earlier positive-cut paper conjecture and its nullspace extension are now formalized exactly. Exported four already-proved helpers from `WeilPhiDoobDivisorEnergy.lean` (`integrable_edge`, `hasSum_chains`, `tsum_shifted_edge_eq`, `primeFirstEquiv`); their proofs are unchanged. New leaf wired once into `formal/GaloisForLFunctions/RHTower.lean`.

Validation: bounded-continuous scratch and final compact-support extension checked; mathlib names verified in a separate `/tmp` scratch. Leaf builds `lake --old build GaloisForLFunctions.RHTower.WeilPhiDoobDivisorEnergy` and `lake --old build GaloisForLFunctions.RHTower.CHMDPrimeDivisorCuts` exited 0. Final plain `lake env lean` audits of both changed tree leaves exited 0 with empty output. All 39 new or newly exported declarations audited via `#print axioms` in `/tmp`; only `propext`, `Classical.choice`, `Quot.sound` appeared. `scripts/formal_tools.py index` exited 0 (7 changed sources, including concurrent work); `scripts/formal_tools.py lint` exited 0 (`formal lint passed`; existing size warnings). Scoped `git diff --check` passed. No heartbeat override, full build, web lookup, numerical experiment, subagent, commit, or push.

SHA-256 at final direct audit:
- `CHMDPrimeDivisorCuts.lean`: `8fe2821d5b96e5acc48d8cb0887141dac3e61ba667f938d6e012ea45e2d57601`
- `WeilPhiDoobDivisorEnergy.lean`: `4eb812f7613902780be197c58167fe205ff9d687d9ba3084b67f2786e1c79209`

Remaining obstruction and next attack: strict positivity of a source component gives no uniform domination of the negative cosh mass. Work must now attack that actual subtraction jointly with the original archimedean and same-side terms under the original CHMD/polar conditions. Do not infer full source positivity, extend compact-support rigidity to arbitrary strip multipliers, replace the arithmetic source, or assume defect vanishing. The unconditional premise-free RH goal remains ACTIVE.

Cleanup complete: all 15 owned `/tmp` search/proof/name/audit/log files removed; absence verified. Both audited source hashes rechecked unchanged. All owned process handles terminal. Final scoped whitespace check passed.

### Reflected source-kernel conjecture (2026-10-16, paper resolved; Lean pending)

Attack: could odd half-line folding turn the original source into a positive jump kernel plus a diagonal killing potential, allowing the cosh subtraction to be handled locally?

The literal reflected-kernel positivity conjecture fails. Set L=log 2 and B={(x,L-x):0<x<L/2}. The positive same-side prime jumps lie on y=x+log n. None intersects B for any active n>=2, since L=2x+log n>log n>=L. The reflected prime jumps lie on x+y=log n and occur with a negative sign when a reflected sum-square is rewritten as a difference-square plus its exact diagonal term. Only n=2 meets B. Its restriction is precisely the pushforward of the strictly positive finite density (Lambda(2)/sqrt 2)*Theta(x)*Theta(L-x) dx on (0,L/2). The archimedean reflected kernel is absolutely continuous in (x,y), while B is a graph of planar measure zero. Every diagonal measure also vanishes on B because x<y there. Thus neither the full archimedean density nor any diagonal killing correction can remove this singular negative source component.

Positive survivor to formalize: exact restriction/classification of the complete source's negative reflected-prime component on B, with positive finite mass and zero contribution from every same-side prime and every other reflected prime. This is an invariant singular part of the actual folded source, not an arbitrary signed toy model. Also formalize the per-prime original-energy identity linking the negative reflected difference-square to its retained positive killing density. Do not conclude the Weil quadratic form is negative, or exclude nonlocal Hilbert/Hodge factorizations. This rejects only the local positive-jump absorption mechanism; CHMD remains active.

Corpus checks: source/cosh deep search partial due reranking deadline; source-index search complete; odd-derivative search complete; reflected-Markov search partial due malformed local filter output. Used available Lean hits and direct exhaustive source searches. Existing exact collar identities and positive reflected archimedean weight are in WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal.lean. No existing literal reflected-prime singular-component theorem located. No web or old research markdown read.

Stronger survivor exposed by the measure proof: the entire negative reflected-prime measure is supported on the countable union S of ordered lines x+y=log n, 0<x<y. Every forward prime line meets each reflected line in at most one point, hence its weighted Lebesgue pushforward gives S zero mass. The archimedean density also gives S zero mass. Therefore the positive and negative jump measures are mutually singular globally, not merely separable at prime 2. This exact sign decomposition is preserved by every strictly positive scalar reweighting; no absolutely continuous or diagonal correction cancels the first-prime negative mass. The original collar diagonal nevertheless compensates the negative difference-square exactly: for odd tests, collar killing minus twice reflected difference energy equals the positive prime-crossing energy, whose complete divisor-cut sum is already proved. Formalize this full singular/compensated decomposition, not only the negative witness.

### Reflected singular-part audit complete (2026-10-16)

Classification: **PROGRESS through a disproved local conjecture and exact positive survivor**. The complete paper proof, negative result, survivor and verification are recorded in `docs/drafts/pipeline/5-failed/chmd-reflected-local-jump-2026-10-16.md`; only that local absorption mechanism is retired.

New wired leaf `formal/GaloisForLFunctions/RHTower/CHMDReflectedPrimeSingularPart.lean` (415 lines), namespace `RHTower.CHMDReflectedPrime`. The complete positive jump measure and negative reflected-prime measure are mutually singular (`positive_negative_mutuallySingular`, line 382). The first-prime slice has exactly the reflected prime-2 measure, with finite strictly positive mass; every positive contribution vanishes there. `negative_component_survives_positive_gauge` (line 209) shows that positive reweighting, absolutely continuous additions and diagonal measures cannot absorb it. `reflectedDifference_as_measure` and `integral_primeJump_eq_reflected_difference` tie these literal measures to the actual prime source.

The strongest positive survivor is retained: `compensated_source_hasSum_cuts` (line 308) and `compensated_source_pos` (line 388) identify the full original collar-diagonal compensation minus the reflected difference energy with the already-proved positive finite-divisor cut expansion, strictly positive on nonzero compact odd tests. `doob_source_eq_reflected_compensation` (line 397) identifies this component inside the full original Doob source, retaining the negative cosh mass explicitly. No negative Weil-form value is claimed, and no nonlocal positive factorization is excluded.

Scratch and name probes passed. Leaf --old build and final plain direct Lean audit exited 0; direct output empty. All 50 declarations audited, only standard propext/Classical.choice/Quot.sound. SHA-256 `e397128936fcad6ccc9c3c89584a80355aab740404d86f973851c23539c3fef8`. Index exited 0 (7 changed sources with concurrent work). Lint exited 1 solely on unrelated unwired DeningerMeyerInvisibleTorsionFree and DeningerMeyerSourceShiftTopology. No changes to those modules. Scoped diff whitespace passed.

Next mathematical target: preserve the reflection sum-square interactions and their exact diagonal compensation in a global source factorization. Local positive-jump or positive scalar-gauge arguments cannot discard this singular sector. The actual cosh subtraction, and hence original CHMD defect elimination, remains unresolved. Unconditional premise-free RH goal remains ACTIVE.

Cleanup: all 12 owned scratch/search/log files removed and absence verified. Audited leaf hash unchanged. All owned processes terminal. Final scoped and new-artifact whitespace checks passed.

### Prime-chain variance factorization (2026-10-16, paper proof; Lean pending)

Current attack: factor the complete positive crossing source into arithmetic conditional variances, retaining the original cosh subtraction. The corpus already contains sharp theta-translation admission and derivative-history closure; no new claim is made from those. The scalar reflected-jump obstruction also remains in force.

For each product N, prime p dividing N, and p-free divisor b, partition the p-chain of divisors m with ordCompl[p] m=b at the logarithmic cut u into L={m: log m<u} and R={m: u<log m}. Every active Mangoldt edge crossing the cut belongs to exactly one such chain. Indeed, its ratio k/m is a positive power of the unique prime p; conversely two distinct ordered divisors in one p-chain have prime-power ratio and weight log p. Thus the entire divisor-cut energy is the sum, over p and b, of log p times the complete bipartite energy between L and R. This retains every divisor, prime and prime power.

For finite nonempty L,R, writing their cardinalities l,r, means A,B, and centered sums of squares V_L,V_R, the exact identity is
E(L,R)=r V_L+l V_R+lr(A-B)^2.
Empty sides contribute zero throughout. Proof: expand each square, use the zero sums of centered values, and sum; no inequality is used. Consequently the original crossing source admits an exact nonlocal square factorization into within-chain fluctuations and between-side mean differences. Multiply by the unchanged theta product fibre and use the previously proved absolute convergence to integrate and sum all product indices. The fibre is positive wherever a crossing chain is active and all chains vanish outside the central interval.

Work plan: formalize the arithmetic edge/chain classification; finite variance identity and complete divisor reindexing; transfer the exact factorization to the original source and retain cosh explicitly; leaf build, direct Lean and complete axiom audit, index/lint, owned scratch cleanup. No claimed domination of cosh, RH equivalence, positivity premise, numerical experiment or novelty claim. The missing global cancellation is still the target; this factorization must be assessed by the actual identity proved, not by a claim that it settles that cancellation.

Analytic closure of the paper proof: every individual chain vanishes outside 0<u<log N, so its original theta fibre is positive wherever it contributes. Each chain density is measurable by its finite indicator expansion and is bounded by the already-integrable complete cut density. Hence each is integrable. Reindex the nonnegative integrated family by the dependent countable index (N,p,b), with p in N.primeFactors and b in N.divisors. Its finite N-fibre sum is exactly the old cut integral. The old HasSum theorem therefore proves summability of the entire chain family, including the integrals of its absolute values. Fubini gives the integral of the full pointwise chain sum. The reflected-compensation identity then identifies the same sum with the original collar diagonal minus twice the negative reflected difference energy, without discarding either.

Implementation checkpoint: CHMDPrimeChainVariance.lean (350 lines, 30 declarations) and CHMDPrimeChainSourceFactorization.lean (220 lines, 21 declarations) are written and wired once each. Arithmetic and full-source scratch proofs pass; mathlib names and the finite-subtype reindexing probe pass. Both --old leaf builds exit 0. Final plain direct Lean audit of the arithmetic leaf exits 0 with empty output. Direct source audit is running; all 51 declaration axiom checks, index/lint and cleanup remain. Source leaf build replays existing dependency warnings, with no errors or new-leaf warnings. No change to the original cosh subtraction and no RH proof.

### Complete prime-chain variance factorization — final audit (2026-10-16)

Classification: **PROGRESS on the exact arithmetic factorization**, not elimination of the original CHMD defect or proof of RH. The full dependency-closed paper proof, precise limitations and audit are in `docs/drafts/pipeline/3-formalized/chmd-prime-chain-variance-2026-10-16.md`.

Every original Mangoldt divisor-cut edge belongs to one prime chain. The chain is a complete bipartite graph at the cut, and its energy equals the two internal variances plus the squared difference of its two means. All product indices, prime powers and chain bases are retained. Every individual theta-weighted chain density is nonnegative and integrable. The complete countable family has summable integral norms and sums exactly to the original crossing source. The same sum is the retained original reflected-prime compensation. The full Doob identity keeps the negative cosh mass unchanged. No new RH equivalence or positivity premise was introduced.

Both --old leaf builds and final plain direct Lean audits exit 0; both direct outputs empty. All 51 declarations audited in /tmp, with only propext/Classical.choice/Quot.sound. Arithmetic hash `c2646ccc128aae1a8f0ba0e6198798709155f4e4147dda94cfcc4cd6fc96dbb2`; source hash `a0f96631b1c0ce47f9f17ace59b16a9cfdac54823dc5a175cf20a711d4c1577e`. Both imports occur once. Index exit 0, five changed sources including concurrent work. Global lint exit 1 solely on unrelated unwired DeningerMeyerGaussianStripRegularization, DeningerMeyerMellinReconstruction and DeningerMeyerMellinStripControl; these untracked modules were not touched. Own leaves have no lint errors. Scoped and new-artifact whitespace checks pass.

All 18 owned temporary files removed and absence verified. All owned processes terminal. Audited source hashes unchanged. No full/umbrella build, heartbeat increase, numerical experiment, external lookup, subagent, commit or push.

Next: attack the original cosh subtraction jointly with archimedean and same-side terms using the explicit arithmetic mean/variance sectors. Do not count another positivity or faithfulness statement for the retained crossing component as elimination of that obstacle. The unconditional premise-free RH goal remains ACTIVE.


### Complete Doob source form closure (2026-10-16, new conjecture and paper plan)

Corpus audit: zero-division sources and their theta-relative realization already exist; do not re-prove them. A generic selfadjoint construction does not establish the missing spectral gap. The concrete domain obstacle is that the complete arithmetic/archimedean jump energy must be represented on the same source carrier as the negative cosh mass, with no invisible edge vectors introduced by completion.

Conjecture: the literal full difference graph is closed in L2(mu) x L2(kappa), where mu(dx)=Theta(x) cosh(x/2) dx and kappa consists of the positive archimedean edge density and every original prime line measure. The signed form is norm(Dv)^2-norm(v)^2, so its mass term is exactly the original cosh subtraction. This is a realization theorem, not an RH equivalence or a claimed proof of its primitive positivity.

Dependency-closed paper argument: both endpoint pushforwards of kappa are absolutely continuous with respect to mu. For the archimedean part this follows from product Lebesgue measure and translation invariance; for every prime line it follows from translation invariance and the strictly positive mu density. If (v_n,Dv_n) converges in both L2 factors, choose a subsequence converging mu-a.e., lift convergence to both kappa endpoints, then a further edge-a.e. subsequence. Uniqueness of scalar limits identifies the edge limit with v(x)-v(y). Thus the graph is closed, its source projection is injective, and its induced graph norm is complete. The signed form plus twice the mass norm is the graph norm squared. Compact C2 source tests must be placed in this graph and the edge norm identified with the complete existing Doob identity, retaining all primes and the original cosh term. Do not identify the maximal graph with the minimal compact-test closure without proving the core theorem; distinguish these explicitly.

Work plan: prove the endpoint-null-set and closed-graph lemmas; instantiate the literal full source measures; prove exact source-energy identification and complete graph realization; build only changed leaves, run plain direct audits and all-declaration axiom checks, index/lint, clean owned scratch. The primitive sign and unconditional RH remain unresolved and the goal remains active.


Closure checkpoint: the generic closed difference graph, complete Hilbert structure, injective source projection, exact shifted norm identity, and actual-function lift have passed a scratch Lean check. CHMDClosedJumpGraph.lean is written and its --old leaf build passed. The actual full-source measure and energy identification is under verification in /tmp/chmd_doob_graph_20261016.lean; no claim that this leaf has passed yet. All earlier arithmetic leaves remain unchanged.

Further exact structure exposed by this construction: the maximal graph contains the constant profile 1 with mass norm squared 1/2 and signed energy -1/2. Its bottom-energy eigendirection is unique. Proof of uniqueness: a zero edge vector gives equality f(x)=f(x+t) for almost every positive archimedean shift, since its density is strictly positive. A measure-preserving shear converts this to equality for almost every ordered pair x<y; swapping coordinates yields all pairs, and Fubini forces f to be constant almost everywhere. Consequently equality in sourceEnergy >= -mass occurs precisely in the one-dimensional constant-profile direction. This is a classification of the actual complete form, not the missing spectral gap at zero. Keep the compact-test closure as a separately defined closed subspace; do not assert it equals the maximal graph.


Second closure checkpoint: actual-source scratch now contains the complete endpoint nonsingularity proof; exact mass, archimedean and all-prime integral identifications; compact C2 admission and equality with original markovEnergy; constant-profile mass/energy; the archimedean pair-rigidity argument and exact ground-direction classification; and a separate complete compact-test core with injective source projection. The first full pass identified five implementation errors (function eta form, pointwise addition normalization, MemLp.zero namespace, Lp.stronglyMeasurable namespace, and an opaque typeclass target); these were corrected without changing the mathematics or heartbeat limits. A fresh full scratch check is running. Neither the maximal/minimal core equality nor primitive nonnegativity is claimed. Generic graph leaf is built; actual-source tree leaf, umbrella wiring, final audits and cleanup remain.


Closure implementation complete: CHMDClosedJumpGraph.lean (11 declarations) and CHMDDoobSourceGraph.lean (60 declarations) are wired once each. Full scratch check and mathlib-name probe pass. The --old source leaf build, including the renamed core instance, exits 0 with no new-leaf warnings. Core final plain direct audit exits 0; source final plain direct audit is running. The all-71 declaration axiom audit, index/lint and cleanup remain. Hash snapshot: {"CHMDClosedJumpGraph": "9371c79bfdb7a126750efce316d981696daa5a6336efbe84b8df71604d5c6bc9", "CHMDDoobSourceGraph": "f2e0fdd3f3d63167706f81e4fc46b04e5d767fe7fc45f9cd6af1625ba57c542c"}. No RH or primitive-gap claim.


### Complete signed Doob source closure — final audit (2026-10-16)

Classification: **PROGRESS on the actual source domain and ground-direction classification**, not primitive positivity or RH. Full paper proof and limits: docs/drafts/pipeline/3-formalized/chmd-complete-doob-source-closure-2026-10-16.md.

CHMDClosedJumpGraph.lean (124 lines, 11 declarations) proves literal difference-graph closure, complete Hilbert structure, injective source projection, exact shifted norm identity and function-level energy realization. CHMDDoobSourceGraph.lean (415 lines, 60 declarations) instantiates every original archimedean and prime edge with the theta-cosh mass; admits all compact C2 profiles; identifies the signed graph energy exactly with original markovEnergy; proves constants have mass c^2/2 and energy -c^2/2; and classifies these as exactly the zero-jump / bottom-energy directions. The separate compact-test completion is complete and retains an injective source projection. No maximal/minimal domain equality or selfadjoint-operator theorem is asserted.

Both --old leaf builds and final plain direct audits exit 0; direct outputs empty. All 71 declarations audited, only propext/Classical.choice/Quot.sound. Mathlib-name probe passes. Index and global lint both exit 0 (formal lint passed; existing file-size warnings). Both imports occur once; whitespace checks pass. Audited hashes: {"CHMDClosedJumpGraph": "9371c79bfdb7a126750efce316d981696daa5a6336efbe84b8df71604d5c6bc9", "CHMDDoobSourceGraph": "f2e0fdd3f3d63167706f81e4fc46b04e5d767fe7fc45f9cd6af1625ba57c542c"}.

The original negative cosh mass remains exact, and the sign on the mass-orthogonal primitive sector remains open. The unique negative ground direction does not imply the missing gap. Next work must use the actual arithmetic interactions to resolve that primitive sign, not add a generic spectral-gap receiver. Unconditional premise-free RH goal remains ACTIVE.

Cleanup complete: all 19 owned temporary files removed and absence verified; audited source hashes unchanged; all owned process handles terminal. Final whitespace checks passed.


### Order-preserving full-source conjecture and prime-threshold survivor (2026-10-16)

Attack: can the actual positive jump generator preserve spatial order, so a one-dimensional first-mode argument controls the primitive sign? The corpus proves theta log-concavity but already refutes shape-only positivity mechanisms. We must inspect the literal complete arithmetic rates.

Paper conclusion: order preservation fails at each active prime-power threshold in the far positive cusp. The positive survivor is an exact countable arithmetic tail-selection law, retaining the archimedean tail and every active prime, not a sharper bound or an RH receiver.

Let a_n be the existing vonMangoldtAtom and Theta the actual Riemann kernel. For x<b define the complete upward rate
R(x,b) = [integral_{t>b-x} omega(t) Theta(x+t) dt + sum_n 1_{b<=x+log n} a_n Theta(x+log n)] / cosh(x/2).
This is the literal forward-edge density divided by the theta-cosh mass density from the closed Doob source graph; backward edges cannot reach b when x<b. At an integer threshold m>=2,
cosh(x/2) R(x,x+log m)/Theta(x+log m) tends to a_m.
For a fixed 0<h<log m-log(m-1), the SAME upward threshold is reached by exactly the same n>=m from state x+h, yet
cosh(x/2) R(x+h,x+log m)/Theta(x+log m) tends to 0.
If a_m>0, eventually R(x+h,x+log m)<R(x,x+log m). Thus the full upward rates fail the necessary upper-set monotonicity for an order-preserving jump mechanism. This does not prove the quadratic source negative or disprove RH.

Dependency-closed paper proof: the existing complete-theta shift ratio tends to zero for every strictly larger shift. Its existing first-atom envelope bounds give, uniformly for n>=m and x sufficiently large, Theta(x+log n)/Theta(x+log m)<=C(m/n)^2. The original coefficients obey a summable majorant C m^2 Lambda(n)/n^2, so dominated convergence passes through the COMPLETE countable prime tail and selects precisely n=m. For the advanced state, factor its prime tail through Theta(x+h+log m), whose ratio to Theta(x+log m) tends to zero. The archimedean density is bounded on every t>=s>0; the existing theta-tail integral divided by Theta at its lower endpoint tends to zero. This disposes of the entire archimedean contribution at both states. The cosh quotient is positive and eventually at most one. Integer cutoff equivalence follows from log(m-1)<log m-h<=log m; zero coefficients at n=0,1 are retained under the original convention. At m=2 the selected coefficient is strictly positive unconditionally. All asymptotics concern the original complete measures.

Plan: verify exact infinite prime-tail selection; prove full upward-rate identification and both-state tail limits; extract the explicit nonmonotonicity witness, retaining the positive selection theorem as the survivor; leaf builds/direct audits/all-declaration axiom checks/index/lint/cleanup. Do not claim a semigroup theorem without constructing its generator, and do not retire CHMD: only the order-preserving source mechanism is being tested.

#### Full-source arithmetic tail selection: implementation (2026-10-16)

Both new leaves build successfully: `CHMDPrimeTailSelection.lean` (19 declarations)
and `CHMDJumpTailOrderObstruction.lean` (21 declarations). The full countable
prime tail selects its first atom, the full archimedean tail vanishes in the
same normalization, and the literal original graph rates violate upper-set
monotonicity at n = 2. Both integrability and summability are proved on the
positive cusp; a separate identity checks the closed archimedean endpoint.

Positive survivor: exact recovery of all original arithmetic coefficients
from normalized complete source tails. Dependency-closed paper proof:
`../3-formalized/chmd-full-jump-tail-selection-2026-10-16.md`. Failed route and
second-pass salvage:
`../5-failed/chmd-spatial-order-preservation-2026-10-16.md`. No semigroup,
negative quadratic energy, primitive gap or RH theorem has been claimed.

Both leaves are wired once into `RHTower.lean`; no umbrella build was run.
Final plain Lean audits, all-declaration axiom audit, mathlib name check,
index/lint and cleanup are in progress.

#### Full-source tail audit results (2026-10-16)

- Both new leaf builds (`lake --old build <leaf>`) exited 0.
- Both final plain `lake env lean <leaf>` audits exited 0 with empty output.
- Separate `/tmp` probe checked 34 source/mathlib names with `have := @Name`
  lines; exit 0.
- All 40 new declarations audited in `/tmp`; only `propext`, `Classical.choice`,
  and `Quot.sound`. Exit 0.
- Both new imports occur exactly once. Scoped whitespace checks passed.
- `scripts/formal_tools.py index`: exit 0.
- `scripts/formal_tools.py lint`: exit 1 solely for unrelated concurrent
  `GaloisForLFunctions.RHTower.PaperThetaCutMeyerCurrent`, unreachable from its
  theorem-area umbrella. No owned CHMD lint error; unrelated work preserved.
- `CHMDPrimeTailSelection.lean`: 230 lines, 19 declarations, SHA256
  `8599c3afeec8bd27f47ca1a49db40f235ee69859bf2735a23671d15e678f920c`.
- `CHMDJumpTailOrderObstruction.lean`: 238 lines, 21 declarations, SHA256
  `08e2e5f7d946287a0c88e86ac1702be83b2eee10fc04032e668c275f0c10bc31`.

No computations, web lookup, novelty audit, subagents, heartbeat overrides,
full/umbrella builds, commit or push. Scratch cleanup is the remaining owned
audit task. RH remains unproved; primitive-sector cosh domination remains open.

Cleanup complete: all 13 owned scratch files removed; absence verified. All
owned search, Lean, index and lint sessions reached terminal exit. No owned
work remains for this contribution; the global lint exception above belongs
to concurrent work. The unconditional RH goal remains active.

### Primitive cusp escape and noncompact source projection (2026-10-16)

Constructed an unconditional sequence in the actual compact-core primitive
hyperplane: source norms one, graph norms at most two, pairwise orthogonal
source coordinates, signed energies tending to zero, full jump energies
tending to one, and graph norms squared tending to two. Consequently no
source-coordinate subsequence is Cauchy, the primitive graph ball has a
noncompact source image, and no strictly positive uniform signed margin
can hold in this source norm. No sign of Markov energy was assumed.

The mechanism is exact translation invariance of the complete Markov energy
together with diverging inverse-Doob theta-cosh mass. The explicit compact
profile has both half-moments zero, so every translate remains primitive.
No prime truncation, replacement source, maximal/core-domain identification,
selfadjoint operator or spectral Weyl residual is used. RH remains open.

Artifacts: `CHMDTranslatedPrimitiveSource.lean` (216 lines, 25 declarations)
and `CHMDPrimitiveCuspEscape.lean` (254 lines, 34 declarations). Both leaf
builds and final plain Lean source audits passed; all 59 declarations use
only propext/Classical.choice/Quot.sound. A separate 25-name probe, exact-once
imports, whitespace and index checks passed. Global lint exited 1 for six
other unwired Deninger modules; no owned CHMD error. Full proof, hashes and
audit record: `../3-formalized/chmd-primitive-cusp-escape-2026-10-16.md`.
Failed route and positive salvage:
`../5-failed/chmd-primitive-compact-projection-2026-10-16.md`.

No web lookup, numerical experiment, novelty audit, subagents, heartbeat
increase, umbrella/full build, commit or push. Owned scratch cleanup pending.

Primitive cusp escape cleanup complete: all 12 owned scratch files removed;
absence verified. All owned processes terminal. The topic card was moved to
`3-formalized`; no owned work remains for this contribution. The unconditional
RH goal remains active; global lint exceptions above belong to other work.


## 2026-10-16: full jump core density

Proved unconditional `CHMDDoobGraph.compactCore_eq_top` and `dense_compactTests`: actual compact C2 tests exhaust the maximal complete theta-cosh/archimedean/all-prime jump graph. Constant ground states belong to that core. Proof: normal contraction and bounded truncation, full-measure cutoffs, compact transfer to stationary Levy energy, normalized convolution, and weak closedness. Primitive positivity and RH remain unproved.

Card: [full jump core density](../3-formalized/chmd-full-jump-core-density-2026-10-16.md). Eight wired leaf builds and all eight final plain Lean audits passed. All 96 declarations use only standard axioms; 51 mathlib name probes passed. Index passed. Global lint failed solely on 12 other unwired modules (listed on card); concurrent work preserved. All 36 owned scratch files removed and absence verified.
