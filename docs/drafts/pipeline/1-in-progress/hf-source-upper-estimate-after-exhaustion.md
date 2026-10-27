# HF: arithmetic sign after source-work exhaustion

- **ID:** hf-source-upper-estimate-after-exhaustion
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / direct source-sign investigation
- **Parent goal:** unconditional Lean closure of HF, unchanged.
- **Statement:** Obtain an actual arithmetic upper bound on the completed source
  work below the off-line quantum, or prove the corresponding full-source sign.

## Current evidence

The preceding card `hf-global-selberg-work-exhaustion` is formalized: compact
Laurent-residue works converge to nonnegative damped work, then to the full
multiplicity-copy transverse energy in `[0,∞]`. This supplies no upper estimate.
The current frontier still marks full Weil positivity, Hecke-defect annihilation,
and the arithmetic field/work bound open.

No new RH criterion, multiplicity comparison, zero-side lower bound, or improved
constant is the target of this cycle. A successful subtheorem must prove an
actual signed arithmetic estimate with every prime, Gamma and polar contribution
accounted for.

## Corpus audit and rejected shortcuts

- `TheTowerFormOfAPrime`: positive Kac–Murdock–Szegő form, but the prime form
  subtracts its diagonal. Local positivity does not supply full source positivity.
- `TheHeckeMomentProblem`: Hankel positivity is for the collided depth measure;
  its first moment remains an unbounded, nonnegative Hecke defect.
- `WeilPhiDoobGroundStateCancellationAndShortSupportNoGo`: the theta ground-state
  cancellation and full Doob decomposition are already proved. Reproving them
  would not move the sign frontier.
- ACT's two-moment law excludes a positive decaying folded supersolution.
  Its exact light-cone identity leaves the signed prime anti-diagonal contribution.
  No Perron–Frobenius conclusion on the odd sector is available.

## Direct attacks

1. **Global source work.** Seek a nonpositive arithmetic upper estimate for
   `xiDampedSourceWork R`, `R≥4`, using the actual source rather than its zero-side
   representation. `[OPEN CORE]`: signed prime–Gamma cancellation at the zeros;
   coefficient positivity on `Re s>1` does not control Laurent residues inside.
2. **Source compensation.** Investigate the actual shifted-theta variation form
   `2 S_a(u) - D_a(u) + V_a(u)`. The full target is payment of prime anti-diagonals
   by same-side primes plus the exact light-cone continuum term. `[OPEN CORE]`:
   no independent all-profile payment estimate.
3. **Structured profiles.** Audit ACT's open monotone-profile question as a possible
   substantive all-scale source inequality. This is not permission to replace
   the parent goal or to report a restated criterion as progress. Establish the
   exact statement and test it against existing fold/variance obstructions before
   attempting a proof.

## Proof status

No new source sign or upper estimate is proved. No paper theorem is being
claimed, and no assumption interface has been added in Lean. Every dependency-
closed paper theorem will be followed directly by formalization.

## Direct-source investigation checkpoint

The following checks did **not** discharge the upper estimate. They are research
notes, not new impossibility theorems or reasons to retire HF.

1. **Monotone shifted-theta profiles.** Read
   `ShiftedGroundStateMonotoneFoldDomination`,
   `ShiftedGroundStateFoldExcessThresholdAndOddProfileDomination`, and
   `ShiftedGroundStateCollarDeficitAndHalfCollarPeak` in ACT. Their unconditional
   estimate retains the positive fold-excess weight. The support-localized
   positivity result explicitly assumes the weight bound; neither dual-threshold
   annihilation nor discarded collar mass supplies it. The ACT README already
   records failure of the global weight criterion at large shifts. An argument
   must retain additional same-side energy, not reuse that criterion.
2. **Complete light-cone formula.**
   `LightConeAntisymmetricVariationLaw.zeroForm_shiftedGroundState_eq_antisymmetric_weilJumpDensity_add_prime`
   includes the polar contribution in the continuum kernel. Its continuum term
   is nonnegative; its remaining prime term is signed. No all-profile payment
   estimate was found or proved. Rewriting the formula is not progress on its sign.
3. **Exterior prime field.** Read the newly available
   `ArithmeticElectrostatics/TheExternalFieldIsAPrimeSum`. Its prime upper bound
   holds at `Re s > 1` and follows from a *lower* bound on the zero field there.
   It does not upper-bound the regular source field at an interior zero or the
   damped source work. The finite-energy escape corollary still assumes transverse
   equilibrium.
4. **Discrete Gibbs bound.** Read the proof in
   `RHTower/CriticalGibbsPerronPolarization`. Its actual diagonal bound is
   `log k + mertensPartial (N / k)`, subsequently bounded by `log N + C`.
   The proof does not identify this diagonal with the completed Gamma--polar
   contribution or give a bound on the polar complement. The finite divisor
   estimate cannot be substituted for full Weil positivity.
5. **Selberg source cancellation.** Corpus contains `SelbergSymmetryFormula`,
   `SelbergSymmetryCore`, and the asymptotic for the summatory `Lambda * Lambda`
   in `CCMFUSuzukiSecondGradeAsymptotic`. These statements concern integer
   summatory functions. No theorem transferring their bounds to the required
   signed interior Laurent residues was found. Such a transfer remains an
   analytic obligation, not an inferred consequence of coefficient positivity.
6. **Ground-state localization.**
   `CCMFullGroundZeroSideEigen.riemannHypothesis_of_localizedFullGrounds`
   retains an exponential-moment localization premise. The corpus supplies
   real-rooted ground states and their eigen-equation, but that theorem does not
   discharge the localization bound. No substitution of this criterion for the
   requested producer was made.

**Batch verdict:** no new mathematical result; no Lean file changed or compiled.
The earlier source-work exhaustion remains the last completed bridge. HF and
this card remain in progress. External search, novelty checks, numerical
experiments and new assumption interfaces were not used.

**Continuation obligation:** attack the literal signed arithmetic estimate.
Choose an explicit prime--Gamma--polar cancellation or source inequality before
further implementation; check its first unproved sign on paper. Do not count
another equivalent criterion, a positive collided form, an exterior field
identity, or a smaller constant as discharging the open core.

## Composite-node and continuation checks

The next batch again did not prove a closing estimate or discharge a significant
premise. The previous goal turn is classified as **no mathematical progress**.

- Read the current `ThePrimeKernelIsASumOfTransverseTowers`: its tensor
  decomposition retains `K_p - 1`. Summing the local upper bounds diverges;
  transversality of prime ladders supplies no completed diagonal cancellation.
- Investigated the open whole-tower problem in
  `BiScaleUncertainty/PrimeTowerDeletionCompositeCharge`. Its full-grid cone is
  blind at integer products `p^i q^j`, not at rational ratios `p^i/q^j`.
  Therefore an additive decomposition of the joint spectral measure into
  independent prime marginals cannot be inferred from the stated constraints.
  Such a decomposition was not asserted or formalized. Pairwise moment
  inequalities were considered, but no proof linking them to the required
  aperture-uniform prime--Gamma--polar bound was obtained. Merely sharpening
  a finite tower price would not meet the user's requested progress.
- Read `TheHeckeDefectIsTheMomentOfInertia`: its upper comparison is with the
  actual nonnegative depth second moment, whose vanishing remains unproved.
  It cannot be used as an independent upper estimate for the defect.
- Read `CCMSharpPrimeWindowCancellation`: multiplying by pole-filled zeta
  produces a holomorphic source and lowers the zero order. This is analytic
  cancellation, not a sign for the completed source.
- Rechecked the naive/convex-height and ACCE transport frontiers. The former
  retain the bounded-error height construction; the latter retain a
  horizon-independent signed budget. The exact derivative and shell-flux
  identities do not prove either budget.
- A stress-tensor formulation of the squared logarithmic derivative was
  considered as a possible direct source attack. No signed integral bound was
  proved. A divergence identity alone would be another representation of the
  same work and must not be reported as a closing estimate.

No Lean changes or compilations were made in this batch. No paper theorem or
new no-go is claimed. HF remains active, with the original objective unchanged.

## Laguerre, cut-profile and radical-span checks

This continuation also produced **no mathematical progress**: no source upper
bound, new theorem, or discharged premise. The following distinctions prevent
the next continuation from repeating these searches as attempted proofs.

- **First Laguerre sign.** The corpus has
  `XiLaguerreWindowPositivity.laguerre_Xi_pos_of_abs_le_four`, positive-measure
  height results, the exact inverse-square zero sum, and central domination in
  `XiSliceHeatHeightPositiveDefinite`. None proves the first Laguerre inequality
  at every real height. `xi-laguerre-identity-and-kernel-no-go-lean` already
  excludes inferring that sign from positive, even, log-concave theta kernels.
  Bochner positivity of the coefficient as a function of height is not its
  pointwise nonnegativity.
- **Retaining the same-side energy.** Read the exact light-cone identity and
  the monotone fold-domination proof. For a fixed shift, writing a decreasing
  profile as a positive superposition of half-line cuts suggests estimating
  mixed cut energies. That is only a proposed attack: no sign of the mixed
  energies or positive-semidefinite cut kernel was established. The existing
  weight criterion still assumes the unpaid fold-excess bound. In particular,
  positive continuum conductance does not order the signed prime atoms.
- **Monotonicity is not a producer by itself.** The corpus card
  `weil-profile-monotone-cone` gives an RH receiver even for a specific
  non-polar monotone cone, through Fejer triangles and Landau. Its test profile
  differs from ACT's multiplicative profile; no equivalence between these
  cones was inferred. This does rule out treating the word “monotone” as
  sufficient reason that a full arithmetic sign should follow.
- **Truncated theta derivatives.**
  `RiemannKernelTruncationWeilPositive.eventually_re_W_truncKernel_pos` already
  proves the scalar truncation positive. Its paper card leaves positivity on
  finite derivative spans open because signed coefficients can cancel the
  leading edge profile. A finite-rank extension was considered, but fixed-rank
  positivity approaching the theta radical supplies no upper bound on HF's
  nonzero defect. No rank-uniform estimate or transfer was proved, so this
  extension was not substituted for the requested source estimate.
- **Finite prime matrices.** Rechecked the actual Gibbs Schur diagonal
  `log k + mertensPartial (N / k)` and AIT's local tower subtraction. No
  identification with the complete Gamma--polar compensation was found.
  Changing the constant in the finite matrix bound would leave this missing
  identification and the signed inequality unresolved.

No mathematical impossibility or new no-go is claimed by these checks. The
next task remains an actual signed arithmetic estimate, with all prime, Gamma
and polar terms retained. Do not repeat a restricted-height sign, a radical
identity, a finite-rank positive cone, or a finite-matrix norm bound as closure.
No Lean file was changed or compiled; no new hypotheses were introduced.

## Terminal regular-part upper estimate

The following continuation is again **no mathematical progress**. It investigated
an explicit analytic route to the missing upper field estimate, rather than
reusing the terminal lower bound as though it were an upper bound.

For a zero `rho` of multiplicity `m`, locally write
`xi(z) = (z-rho)^m G(z)` with `G(rho) != 0`. The completed regular field is
`Re(G'(rho)/G(rho))`. The corpus's
`Sieve.BorelCaratheodoryLogDeriv.norm_deriv_div_le_of_norm_le` bounds this
logarithmic derivative by `8 log M / R` on a quarter-disc, provided `G` is
zero-free on the whole disc and `|G(z)| <= M |G(rho)|` there.

`XiTerminalRegularField` provides the analytic regular part, and
`XiTerminalOutwardLogDeriv` provides the outward zero-free ray and a lower
field reserve. Neither supplies the required normalized modulus estimate or
a radius with a controlled quotient `log M / R`. A bound for `|xi|` alone
does not provide the lower control of the deflated value needed in that
normalization. No separation estimate or derivative lower bound was assumed.
The proposed upper estimate therefore has an unproved analytic input and was
not formalized as a theorem with that input hidden in a hypothesis.

Also checked the current working sources
`ArithmeticElectrostatics/TheWeilPrimeFormOnAtomsIsLogarithmic` and
`ArithmeticIntersectionTheory/TheFiniteIntersectionIsGaugeBlind`. The former
gives a finite atomic prime-form bound; it does not pay that bound with the
actual Gamma and polar terms. The latter identifies precisely why a prime-form
bound alone cannot distinguish the sign twins. These are other work, not new
results of this continuation. No changes were made to those files.

HF remains open. No paper proof, new criterion, new no-go, or Lean assumption
interface was produced. Future attacks must prove the normalized interior
estimate from the arithmetic source or obtain a different actual signed
upper estimate; local analyticity by itself is not the missing estimate.

## Log

- 2026-10-27 — revalidated the previous source exhaustion theorem and current HF
  frontier; researched actual upper estimates, tower forms, depth moments and
  the complete theta ground-state decomposition. External search, novelty audits
  and numerical experiments remain excluded by the user.
