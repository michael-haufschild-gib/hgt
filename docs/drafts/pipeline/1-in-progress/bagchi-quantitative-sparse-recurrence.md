# Quantitative sparse Bagchi recurrence

- **ID:** `bagchi-quantitative-sparse-recurrence`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-alternatives-search-2026-09-12/assessment.md` · `rh-three-alternatives-working-log.md`
- **Working log:** `bagchi-quantitative-sparse-recurrence-working-log.md`
- **Statement:** Replace RH-equivalent positive-density zeta self-recurrence by a coefficient-faithful return count that quantitatively exceeds the strict-right-strip zero count.

## Goal

Close the chain

```text
actual zeta coefficients
  -> boundary self-return around a hypothetical off-line zero
  -> distinct translated zeros
  -> more right-strip zeros than the zero-density bound allows
  -> RH.
```

The return theorem may be sparse. It must give enough shifts below height `T` to exceed the
available bound for `N(sigma,T)` at every fixed `sigma>1/2`; positive lower density is sufficient
but not necessary.

## Gates

- [x] 0 -> 1 in-progress: exact chain, source-purity condition, and first falsifiable mechanisms
- [ ] 1 -> 2 fully-proven: unconditional quantitative return theorem for the actual zeta germ
- [ ] 2 -> 3 formalized: coefficient-faithful Lean producer, zero transfer, and counting contradiction
- [ ] 3 -> 4 publication-ready: standalone proof and axiom audit

## Existing receivers

- `RecurrenceZeroDensity.lean` contains the abstract scalar contradiction and zero-transfer wrappers;
  it assumes the return and count inequalities.
- `InfiniteTorusEquidistribution.lean`, `PrimeTorusKroneckerDensity.lean`, and
  `IntegerTorusReturnVolume.lean` provide finite phase-flow equidistribution and target volume.
- `CCMPrimePoleFiniteCoherence.lean` gives deterministic finite-dimensional return delay
  `(Q+1)^d` and error `2*pi/(Q+1)`.
- `InghamUniformDetectorZeroDensityLinearExponent.lean` currently supplies the unconditional Lean
  zero-density input only in the deep band beginning at `sigma=7/10`.

None of these constructs critical-strip zeta self-return.

## Conjecture loop

### C1 — finite Euler recurrence plus a uniformly small tail

`[FALSIFIED]` Every finite Euler product is nonzero. Uniform approximation on a circle enclosing a
zeta zero below the boundary minimum would preserve nonzero winding and force an interior zero.
More generally,
`PrimeAFXichargeNoNucleation.exists_xiBoundaryLoop_not_uniformLimit_of_zeroWindingLoops` proves
unconditionally that one actual Xi boundary loop of nonzero winding cannot be a uniform limit of
periodic zero-winding loops. The stronger theorem
`PrimeAFXichargeNoNucleation.exists_xiBoundaryLoop_zeroWinding_uniformGap` supplies one fixed
`m>0` such that every continuous periodic zero-winding loop has sup-distance at least `m` from that
Xi loop. Thus the decisive infinite tail cannot be appended as a uniformly vanishing error to
zero-free finite Euler carriers, even along a sparse subsequence.

**Positive survivor:** finite phase recurrence remains usable only when the finite carrier itself
can carry the required winding, or when a weaker convergence topology is paired with a genuinely
new zero-stability theorem.

### C2 — ordinary universality on a circle with a shrinking slit

`[FAILED AS CURRENT MECHANISM]` Removing an arc makes the complement connected and admits the
nonvanishing target on the remaining compact. The missing arc still carries the entire winding
defect. Bounding its phase by `zeta'/zeta` requires a zero-free exterior buffer, not merely absence
of a zero in the shifted disk. The slit width must also shrink with height, while ordinary
universality supplies no lower-density estimate uniform in that shrinking compact. Generic
close-loop winding stability is already formalized in `ConnectedSymmetryBarrier.lean`.

**Positive survivor:** any slit argument must simultaneously prove a quantitative shrinking-compact
universality bound and a source-derived exterior-zero buffer. A generic winding wrapper is not the
missing theorem.

### C3 — growing finite-prime target

`[OPEN; RATE BLOCKED]` In presenting dimension `d`, Haar return volume has exact order `epsilon^d`.
The deterministic return delay is exponential in `d`. This does not itself disprove a slowly growing
support schedule, but no theorem couples such a schedule to uniform control of the actual critical-
strip zeta tail. Compact linear boundary reporters cannot restore a uniform lower bound in infinite
dimension (`PrimeFormationCompactNonproper.lean`), although that linear-Hilbert obstruction is not a
no-go for nonlinear zeta recurrence.

### C4 — additive smooth-AFE carrier

`[LIVE ONLY AFTER RATE REPAIR]` Additive finite Dirichlet carriers can have zeros and avoid C1's
topological obstruction. The corpus gives an exact height-uniform displaced AFE. At fixed smoothing
scale its deep reflected tail is currently bounded by

```text
C L^(-1) + D (1+|tau|)^N L^(-7/2),
```

and the classical-head replacement adds

```text
E |tau|^(-eta) (1 + L^(1/2+eta)),  0 < eta <= 1/4.
```

The existing sharp line theorem gives `N=4`. A power schedule `L=T^a` would therefore need
`a>8/7` from the deep tail and `a<eta/(1/2+eta)<=1/3` from conductor localization. These bounds
cannot close at fixed smoothing scale.

**Positive survivor:** make the exponent-four deep tail explicit in the AFE theorem. A successor
must use a height-coupled smoothing scale, mean-square tail control on the return set, or recurrent
control of the full deep coefficients rather than their classical replacement.

### C5 — nonzero-dilation recurrence followed by `d -> 0`

`[FAILED AS CURRENT HANDOFF]` Generalized strong recurrence gives positive lower density for each
fixed `d != 0`, but its onset and density may depend on `d`. To keep the second shift inside an
isolating zero disk requires a good return with `|d*tau|<r`; counting requires many such returns.
No corpus theorem gives uniform onset or count on intervals of length `O(1/|d|)`.

**Positive survivor:** a quantitative dilation theorem with explicit uniformity in `d`, interval
length, compact geometry, and error would be sufficient input. Fixed-parameter asymptotics are not.

### C6 — whole-interval mean-square tail plus finite phase returns

`[FALSIFIED IN SMALL-TAIL FORM]` The corpus contains the sharp Montgomery--Vaughan mean-value
error `104 sum n|a_n|^2`, exact twisted finite-polynomial mean values, and the displaced-AFE
Dirichlet bridge. A whole-interval tail-good set and a finite-phase return set need not intersect.
Weighting by a trigonometric approximation to the return cell reduces the desired conditional
second moment to twisted mean values, but if its conclusion makes the infinite remainder uniformly
small behind a zero-free finite Euler carrier, the uniform-gap theorem gives a contradiction.

**Positive survivor:** estimate recurrence of the infinite remainder to its actual base remainder,
not annihilation of that remainder. It must retain the boundary winding before the uniform limit.

### C7 — recent shrinking-target and discrepancy transfers

`[FAILED IN CURRENT LITERATURE PASS]` Broad newest-first arXiv probes found randomized Haar-thinning
for quasi-Monte Carlo and metastability for piecewise expanding maps. The former assumes iid samples;
the latter uses mixing absent from the deterministic irrational prime flow. Neither controls a
growing-dimensional shrinking target along one height orbit, and neither couples it to a zeta tail.

### C8 — logarithmically growing phase support

`[OPEN ONLY WITH WINDING-BEARING TAIL RECURRENCE]` Taking support dimension of order
`log log T / log log log T` would make a fixed-tolerance torus-cell volume `T^(-o(1))`, leaving
`T^(1-o(1))` candidate shifts and therefore enough room to beat any fixed sublinear zero-density
exponent. This rate observation does not solve self-recurrence: the uniform-gap theorem forces the
uncontrolled infinite component to carry the divisor charge. Required estimate is a conditional
return law for that component inside the phase cell, with uniform boundary control and an explicit
exceptional-set count.

### C9 — right-half-plane convergence plus Vitali propagation

`[FAILED WITH AVAILABLE MOMENTS]` Finite prime returns give convergence on `Re s>1`. Extending that
convergence across the critical strip by Vitali requires a locally bounded family along the same
return sequence. Selecting bounded shifts from a whole-interval second or fourth moment loses the
inverse mass of the return cell. For a cutoff carrying all primes below `N`, that mass decays
exponentially in `pi(N)`, while the right-half-plane truncation improves only polynomially in `N`.
The available moments cannot supply normality on the selected phase cells.

**Positive survivor:** a phase-conditioned high-moment estimate whose order grows with the phase
dimension, or a direct normal-family bound on the return set, would revive this route. Such an
estimate is already of Lindelof/RH strength and is absent from the corpus.

### C10 — right-strip AFE with phase-conditioned dual cancellation

`[NAIVE DECORRELATION FALSIFIED; CLUSTER BOUND OPEN]` The corpus has an exact Gaussian AFE at every
point of `0<Re s<1`. On a fixed strict-right strip, shifting the normalized dual contour left by
`-eta` should localize each dual weight with error of order `(Y/T)^eta`; the remaining dual main
sum has moving length about `T/x`. Its prefactor decays like `T^(-d)`, but its absolute mass is of
square-root size, so termwise decay does not control it.

Conditioning on a finite prime-return cell does not turn that block into an ordinary diagonal mean
square. The closed theorem
`PrimePhaseConditionedSmoothResonance.bohrMean_expChar_neg_log_nat_mul_primeMultiFejerKernel`
computes the conditioned Bohr mean of every supported integer frequency exactly. Its multiplier is
strictly positive and satisfies

```text
product_p (N_p+1)^(-1)
  <= product_p (1-v_p(n)/(N_p+1)).
```

Thus every ratio supported on conditioned primes survives as an exact smooth resonance. A full-
interval Montgomery--Vaughan bound cannot be transferred to a phase cell by multiplying by cell
mass; one must bound the aggregate smooth-ratio clusters. `SmoothCount.lean` controls bounded-
exponent smooth counts, but no theorem yet offsets the simultaneous Fejer multiplier loss and the
AFE block length.

**Positive survivor:** split the dual block by its prime-free kernel and prove an explicit weighted
cluster inequality using bounded-exponent smooth counts. Failure of that inequality pivots to a
sparse winding-bearing carrier with fewer synchronized prime directions.

### C11 — exact fixed-scale dual-target reduction

`[LEAN-PROVED REDUCTION]` At any fixed smoothing scale `x>0`, subtracting the two exact general
Gaussian AFEs gives

```text
M(t) - (M(s)+R(s)) = (D(t)-D(s)) - (zeta(t)-zeta(s)) - R(t),
```

where `D` is the direct edge, `M` the dual edge, and `R` the shifted-pole residue. Therefore, once
`D(t)->D(s)` and `R(t)->0`, zeta self-recurrence is equivalent to the moving dual edge synthesizing
the nonzero target `M(s)+R(s)`. The converse estimate and arbitrary-filter limit are formalized in
`SmoothAFEZetaGeneralSelfRecurrenceDualNecessity.lean`; targeted build and axiom audit pass.

**Positive survivor:** fixed `x` makes the direct edge a fixed, rapidly truncated Dirichlet series.
The only moving arithmetic producer is now the explicit dual-target event. Boundary-uniform
recurrence still requires simultaneous values on a finite mesh plus derivative control.

### C12 — terminal scale is forced

`[OPEN; PAPER SCALE AUDIT]` For a fixed strict-right abscissa `1/2+d`, the fixed-`x` dual edge has
effective length `N` comparable to height `T/x`. Its chi factor has size `T^{-d}`, while the
coefficient square mass through `N` is of order `N^{2d}`; the complete normalized dual block thus
has order-one variance. A mesoscopic head `n<=T^alpha`, `alpha<1`, has variance of order
`T^{-2d(1-alpha)}` and cannot supply a fixed nonzero target. The synthesis must use the terminal
scale.

The isolated prime shell `p in (N/2,N]` has total radius about `sqrt(T)/log T` but variance only
about `1/log T`; hitting an order-one target through primes alone is a moderate-deviation event.
`RVPlanarLDP.lean` supplies lower mass for fixed normalized targets, not the moving normalized
centre and radius needed here.

### C13 — full-strip zero-density gate

`[OPEN BELOW 7/10]` The actual Lean zero-count chain remains restricted to `sigma>=7/10` and has
exponent at most `(16/5)(1-sigma)`. The file named
`InghamUniformDetectorZeroDensityUniformPolylog.lean` also quantifies only over `sigma>=7/10`;
"full Gabriel strip" does not mean the full critical strip. The Huxley modules prove unconditional
two-term large-values bounds for abstract dyadic Dirichlet polynomials, with amplitude parameter
up to `7/32`, but no downstream theorem converts them into a zeta-zero count for every
`sigma>1/2`.

**Required successor:** either wire a Huxley/zero-detecting polynomial argument to obtain a
sublinear count throughout `sigma>1/2`, or prove recurrence numerous enough to contradict the
weaker available count after an independent mechanism moves every hypothetical zero into the
covered band. No such mechanism is present.

### C14 — coordinatewise terminal-phase targeting

`[FAILED QUANTITATIVELY]` Independent terminal prime phases have enough total radius to synthesize
a bounded complex correction, and finite-dimensional Kronecker density can approximate any fixed
phase assignment. But the number of terminal coordinates grows polynomially in `T`; coordinatewise
return volume and delay become superpolynomial, while restricting to logarithmically many terminal
primes gives vanishing total amplitude. This cannot produce enough shifts below the same height
that sets the AFE cutoff.

**Pivot:** transfer an aggregate complex-value event, not a coordinate cylinder.

### C15 — largest-prime conditional synthesis

`[OPEN; ARITHMETIC DECOMPOSITION LEAN-PROVED]` The full terminal block, unlike the prime-only shell,
has order-one variance.
Conditioning on phases for primes at most `sqrt(T)` decomposes terms with largest prime factor above
`sqrt(T)` as a sum over independent large-prime phases, with random cofactor coefficients. A
conditional planar local law could therefore give fixed or polynomial lower mass for a prescribed
dual target without synchronizing every phase.

The exact arithmetic/dependency half is now closed in Lean for arbitrary complex weights. If
`X < Y^2`, `steinhausCarrier_eq_smooth_add_largePrimeChannels` proves
`sum_{n<=X} a_n X_n = B_Y + sum_{Y<p<=X} X_p C_p`, where
`C_p = sum_{m<=X/p} a_{pm} X_m`; every such `m` is strictly below `Y`, both `B_Y` and every `C_p`
read only prime phases at most `Y`, and each channel phase `p` lies outside that conditioning set.
This retains the composite mass lost by the failed prime-only shell. Module:
`RHTower.SteinhausLargestPrimeDecomposition`; targeted build passes; axiom audit is only `propext`,
`Classical.choice`, `Quot.sound`.

The complex-coefficient Parseval identity is also closed in
`RHTower.SteinhausComplexSecondMoment`. Consequently
`steinhausCoefficientMass_eq_smooth_add_largePrimeChannelEnergy` identifies the sum of expected
channel energies exactly with the square mass of the non-smooth coefficient sector. Thus the
variance question is now an arithmetic lower bound for the actual terminal AFE weights, followed
by concentration of that conditional energy; it is not an unverified independence calculation.

The corresponding lower bound is now closed for the ideal right-line power profile. For
`0<d<1/2`, normalized coefficient-square weight `N^(-2d)n^(-(1-2d))`, and every prime `p` with
`2p<=N`, the complete dyadic cofactor block `N/(2p)<m<=N/p` has mass at least
`((1/2)/2^(2d))/p` (`normalized_power_channel_lower_recip`). The reciprocal-prime mass between
the half- and two-thirds-power cuts tends to `log(4/3)>0`; therefore
`eventually_normalized_power_terminal_channels_lower` gives a uniform positive aggregate floor.
Module: `RHTower.SteinhausLargestPrimePowerMass`; targeted build passes; axiom audit is only
`propext`, `Classical.choice`, `Quot.sound`. This proves that variable
composite cofactors repair the fixed-cofactor loss.

The direct right-line analytic gate is now closed in Lean. For `0<d`, `d+eta<1/2`, the exact
right-line dual weight obeys
`|W_R(d,tau,Y)-1| <= C*Y^eta/(max 1 |tau|)^eta`
(`exists_norm_smoothAFEZetaRightDualWeight_sub_one_le_conductor`), and
`exists_norm_smoothAFEZetaDualCoefficientGeneral_right_add_main_le` connects this estimate to the
actual general-AFE coefficient. The exact direct two-series AFE and the reflected AFE with an
ordinary primal terminal cutoff are also proved. Targeted builds pass; axiom audits use only
`propext`, `Classical.choice`, `Quot.sound`. This closes sub-conductor transfer, but not terminal-edge
mass: when `Y` is proportional to `|tau|`, the direct bound is only `O(1)`. The reflected-primal
identity is the surviving exact route for transferring a fixed inner terminal fraction.

That reflected terminal transfer is now closed in Lean. Reflection gives a uniform lower bound
`|chi(1/2+d+i*tau)| >= c*N^(-d)` for `tau in [N,2N]`, while the ordinary cutoff is bounded below on
one fixed inner interval. The exact coefficient-square identity then transfers the ideal dyadic
channel estimate to the literal reflected-primal AFE coefficients, and
`exists_eventually_reflected_actual_terminal_channels_lower` proves an eventual uniform positive
aggregate terminal channel mass. Module: `RHTower.SmoothAFEZetaRightReflectedPrimalMass`; targeted
build passes; axiom audit is only `propext`, `Classical.choice`, `Quot.sound`.

The conditional-energy gate is now closed with an arbitrary-small-power probability loss.
Squaring a complex Steinhaus carrier produces its finite Dirichlet convolution, so complex Parseval
and the divisor-fibre estimate give fourth moment at most
`C_epsilon*(M^2)^epsilon*variance^2`. Weighted Cauchy aggregates all channels without a factor for
their number; zero-variance channels vanish exactly. Paley--Zygmund and the literal terminal mass
therefore prove `exists_eventually_measure_reflectedPrimalChannelEnergy_gt_ge_rpow`: uniformly for
`tau in [N,2N]`, the literal reflected-primal conditional energy exceeds half a fixed positive
constant on a set of small-prime phases of measure at least
`1/(4*C_epsilon*(N^2)^epsilon)`. Modules:
`RHTower.SteinhausComplexFourthMomentBound` and
`RHTower.SmoothAFEZetaRightReflectedPrimalEnergyEvent`; targeted builds pass; axiom audit is only
`propext`, `Classical.choice`, `Quot.sound`.

The joint-covariance reduction is also closed exactly. For every finite node family and complex
Rayleigh direction, linear combination commutes with largest-prime channel formation. Conditional
large-prime Parseval gives the frozen covariance energy, and small-prime Parseval identifies its
mean with an explicit prime--cofactor coefficient Gram form. Complex Cauchy--Binet then writes the
Gram determinant as a sum of squared maximal coefficient minors; any selected terminal sample
minor lower-bounds that determinant. Module: `RHTower.SteinhausFiniteNodeCovariance`; targeted build
passes; axiom audit is only `propext`, `Classical.choice`, `Quot.sound`. The next arithmetic gate is
a uniform lower bound for the sum of literal reflected-AFE terminal minors, followed by
concentration of the full covariance form rather than only its trace. The analytic rank part of
that lower bound is now closed: distinct normalized node powers remain independent on the real
terminal log interval, yield a nonsingular real evaluation packet, and retain a fixed positive
determinant floor on coordinatewise neighborhoods. Module:
`RHTower.SteinhausFiniteNodePowerMinor`; targeted build passes; axiom audit is only `propext`,
`Classical.choice`, `Quot.sound`. A single literal minor still scales like `N^(-J)` after squaring,
so it cannot give a uniform floor. The required multiplicity is now closed: every fixed normalized
interval contains at least `cN` terminal prime--cofactor samples eventually; summing the per-prime
floor estimate loses only the sublinear cardinality of the terminal prime window. Module:
`RHTower.SteinhausTerminalSampleCounting`; targeted build passes; axiom audit is only `propext`,
`Classical.choice`, `Quot.sound`. The many-minor combinatorics are now closed too. Strictly ordered
color blocks inject all transversals into distinct canonical Pluecker coordinates; product-first
ordering of actual terminal feature indices makes separated normalized intervals satisfy this
hypothesis; and the product of their cardinalities is `Ω(N^J)`. Modules:
`HTGeometry.ComplexGramColoredMinors` and `RHTower.SteinhausTerminalColoredMinors`; targeted builds
pass; axiom audit is only `propext`, `Classical.choice`, `Quot.sound`. Remaining arithmetic task is
to transfer the stable normalized power-determinant floor to every literal reflected-AFE
coefficient minor with its exact `N^(-J/2)` scale.

Two analytic sublemmas remain: a two-dimensional local lower bound uniform
in the random centre and simultaneously in finitely many boundary nodes; and deterministic vertical-orbit
transfer for the resulting triangular family. Corpus deep/method-enriched searches found conditional probability
infrastructure but no theorem closing these gates. Recent random-multiplicative evidence also
warns that a standard complex-Gaussian CLT on dense support is the wrong target
([Escaping Chaos in Random Multiplicative Functions](https://arxiv.org/abs/2605.21737)); a Gaussian
mixture or direct full-support law remains possible.

## No-go closure

- **Exact killing theorem/mechanism:** C1 and the small-tail form of C6 are killed quantitatively by
  `exists_xiBoundaryLoop_zeroWinding_uniformGap`; naive phase-cell decorrelation in C10 is killed by
  the exact positive Fejer multiplier for every smooth integer frequency. C14 is killed as a
  same-height quantitative mechanism. C2, C4 fixed-scale, C5, C7, and C9 with available moments
  are failed proof mechanisms, not universal impossibility theorems.
- **Strongest positive survivor:** exact fixed-scale dual-target equivalence plus C15's exact
  largest-prime conditional-channel decomposition. C15's local law and C13 remain independent
  analytic gates.
- **New insight:** positive lower density is stronger than the contradiction needs, but weakening it
  transfers the entire problem into a quantitative return-count versus zero-density race. Uniform
  finite-Euler tails cannot enter that race because they erase winding. Fixed-scale AFE recurrence
  instead asks the terminal dual block to synthesize one explicit nonzero target.
- **Status:** fixed uniform winding gap, sharp exponent-four AFE transfer, exact survival of
  prime-conditioned smooth resonances, the necessary-and-sufficient dual-target reduction, and
  C15's arbitrary-weight largest-prime decomposition/locality interface and exact expected
  channel-energy partition are Lean-proved, targeted-build verified, and axiom-audited. Open
  theorems are C15 aggregate target recurrence and C13 full-strip strict-right zero density. No RH
  claim.

## Log

- 2026-09-12 — created after deep statement/proof-body searches and five conjecture/failure pivots.
- 2026-09-12 — C6--C8: mean-square/phase-cell and recent-paper pivots; proved fixed uniform winding
  gap; exposed fourth-power AFE coefficient, tail, deep-value, and classical-value bounds.
- 2026-09-12 — C9--C10: normal-family rate failure; proved exact positive Fejer survival and lower
  bound for every prime-supported integer resonance; isolated weighted smooth-cluster estimate.
- 2026-09-12 — C11--C15: proved exact dual-target necessity and sufficiency; terminal-scale audit;
  falsified coordinatewise targeting; isolated largest-prime conditional local law and full-strip
  zero density as separate remaining gates.
- 2026-09-12 — C15.1: proved arbitrary-complex-weight largest-prime channel decomposition, smooth
  background/channel low-phase locality, cofactor cutoff, and large/small phase disjointness; reduced
  remaining route to channel energy, conditional planar local law, and triangular orbit transfer.
- 2026-09-12 — C15.2: proved complex-coefficient Steinhaus Parseval and exact expected
  largest-prime-channel energy partition; isolated non-smooth terminal AFE coefficient mass and
  conditional energy concentration as next quantitative gate.
- 2026-09-12 — C15.3: proved each variable-cofactor ideal power channel contributes a reciprocal-
  prime floor and the half-to-two-thirds prime-power window has a uniform positive aggregate mass;
  isolated transfer to actual right-line smooth AFE weights as the remaining coefficient gate.
- 2026-09-12 — C15.4: proved direct right-line chi-ratio decay, signed residue contour, infinite
  contour localization, exact actual-coefficient error, direct two-series AFE, and reflected-primal
  AFE; isolated fixed-inner-fraction cutoff mass as the remaining coefficient transfer.
- 2026-09-12 — C15.5: proved a right-line chi lower bound uniform on dyadic height windows, a fixed
  inner cutoff lower bound, the exact literal reflected-primal coefficient-square identity, and an
  eventual positive aggregate terminal channel mass; isolated conditional energy concentration as
  the remaining coefficient/probability interface.
- 2026-09-12 — C15.6: proved exact complex fourth moment via finite Dirichlet convolution, its
  arbitrary-small-power divisor-fibre bound, channel-count-free weighted aggregation, exact removal
  of zero-variance channels, and a Paley--Zygmund event of measure `N^(-o(1))` for literal
  reflected-primal terminal energy; isolated simultaneous planar local probability as next gate.
- 2026-09-12 — C15.7: proved exact finite-node channel linearity, frozen conditional covariance,
  literal reflected-AFE mean arithmetic Gram identity, complex Cauchy--Binet determinant formula,
  and selected-minor determinant lower interface; isolated uniform terminal-minor positivity and
  covariance concentration as the next joint-law gates.
- 2026-09-12 — C15.8: proved exponential independence survives restriction to every nonempty real
  log interval, extracted pairwise distinct terminal samples with nonzero power determinant, and
  proved a uniform positive determinant floor on coordinatewise neighborhoods; ruled out one-minor
  scaling and isolated colored sample counting plus many-minor summation as the arithmetic gate.
- 2026-09-12 — C15.9: proved every fixed normalized interval contains linearly many terminal
  prime--cofactor samples: reciprocal-prime mass supplies the linear main term and the one-unit
  floor loss per prime sums to `o(N)`; isolated colored-choice injection and literal-minor scaling.
- 2026-09-12 — C15.10: proved colored transversals inject into distinct Pluecker minors without
  factorial loss, ordered actual feature indices by represented product, lifted cofactor counts to
  `Ω(N)` actual block cardinalities, and combined finitely many blocks into `Ω(N^J)` minors;
  isolated literal reflected-AFE determinant scaling as the remaining arithmetic gate.

### C15.11 — literal determinant scale and independent recurrence producer

2026-09-30 continuation. User restricts work to constructing and formalizing the independent
recurrence producer. Receiver extensions and unrelated obstruction formalizations are out of scope.

Plan (the requested `update_plan` tool is unavailable in this session):
1. Verify current literal coefficient definitions and search producer ingredients.
2. Prove exact common-height factorization of finite-node reflected-primal minors; use the
   height-independent normalized power matrix, positive inner cutoff, and chi lower envelope.
3. Combine stable sample neighborhoods with the existing colored terminal count to obtain a
   uniform literal arithmetic Gram determinant floor.
4. Attack joint conditional target probability and deterministic vertical-orbit transfer.
5. Compile each completed producer module individually, inspect axioms in `/tmp`, wire imports,
   and run formal lint. Keep the RH goal active until independent recurrence is proved.

The first deep search completed with `partial=false`, complete source inventory, but most compiler
metadata pending or stale. Its top reflection matches concern unrelated sources and do not close
any BAG gate. Existing source definitions remain authoritative; targeted lexical search follows.

Paper mechanism under audit: for fixed node offsets `s_j`, common moving height `tau`,
`n=N*u`, the literal coefficient factors as
`chi(s_j+i*tau) * N^(s_j+i*tau-1) * u^(i*tau) * W(r*u) * u^(s_j-1)`.
The common-height column phase has norm one. Row norms scale as `N^(-1/2)`, hence a
`J`-minor has norm bounded below by `c*N^(-J/2)` on fixed sample neighborhoods. The existing
`Omega(N^J)` distinct squared minors should give a fixed Gram determinant floor. This alone is
not recurrence: conditional covariance, target probability, and orbit transfer remain to prove.

**C15.11 result — [LEAN-PROVED].**
`RHTower.exists_eventually_reflectedPrimalFiniteNode_gram_det_lower_height_window` in
`SmoothAFEZetaReflectedFiniteNodeGram.lean`: for every fixed distinct node family
`1/2+d_j+i*b_j`, `0<d_j<1/2`, there exist fixed `r,c>0` such that, eventually in `N`,
for every `tau` in `[5N/4,7N/4]`, the determinant of the literal reflected-primal
arithmetic mean covariance matrix over `terminalPrimePowerWindow N` is at least `c`.
There is no assumed source determinant floor, recurrence, zero exclusion, or RH premise.

Proof: exponential independence supplies a nonzero real-log evaluation packet. Sorting the
packet changes the determinant by a unit; continuity yields strictly ordered normalized-product
intervals and a common shape floor. The exact coefficient identity factors each minor into:
(1) chi and conductor row factors, (2) common-height column phases, (3) ordinary cutoffs, and
(4) the fixed power evaluation determinant. Column phases have norm one, cutoffs have norm at
least `1/2` after fixing `r`, and each row norm is at least `k_j*N^(-1/2)` by reflection.
Thus every colored minor has norm at least `c0*N^(-J/2)`. Existing literal sample counts give
at least `C*N^J` distinct colored minors. Complex Cauchy–Binet sums their squares, canceling
`N^J` exactly. Fixed offsets fit the dyadic chi window throughout `[5N/4,7N/4]` for large `N`.

Validation: final leaf compiled with `lake --old env lean -o ...` (exit 0, no warnings);
six exported theorems checked via `/tmp/BagLiteralGramAudit.lean`, all depending only on
`propext`, `Classical.choice`, `Quot.sound`. New module wired into `RHTower.lean`; generated
index refreshed. Global `scripts/formal_tools.py lint` exited 1 on unrelated unreachable modules
already being added elsewhere (including the ZetaNotch series); it did not flag the new module.
No full or umbrella build run. Independent recurrence and RH remain unproved.

### C16 — determinant event before the joint target law

`[OPEN]` Next producer conjecture: the literal *conditional* channel covariance has a positive
smallest-eigenvalue floor, together with a bounded background/target centre and small maximal
channel, on a small-prime phase event of measure `N^(-o(1))`. The event must intersect the fixed
base direct-edge phase-return constraints. A joint conditional local law would then target all
boundary nodes; deterministic vertical-orbit transfer remains a separate required producer step.

Do not infer this event from C15.11: its determinant is `det(E G)`, not `E(det G)`. A scalar
Paley–Zygmund bound only controls trace, and separate directional events cannot be intersected
without proof. The current deep search (complete inventory; stale compiler/semantic-coverage
warnings) returned the existing Gram and fourth-moment modules, no conditional determinant or
joint target theorem.

Attack candidate C16a: expand each channel determinant by its cofactor product frequency before
Parseval. Terms with the same product must be added *before* taking the squared norm. The exact
common-height factor from C15.11 is constant on each such frequency fibre, so it can be removed
without losing cancellations. Seek a noncancelling positive fraction of those fibres, then apply
fourth-moment control to the full conditional determinant. This is an analytic conjecture, not a
claimed consequence of the mean Gram floor. No numerical experiments used.

**C16a — [LEAN-PROVED: exact source identity, quantitative floor open].**
`SmoothAFEZetaConditionalGramFibres.lean` expands the actual channel determinant, groups all
cofactor tuples with equal product, and applies Parseval only after their signed determinants have
been added. The conditional Gram determinant is exactly the sum of squared minor carriers.
Its expectation is the sum of squared grouped coefficients, and each minor carrier has the existing
arbitrary-small-power fourth-moment bound. No individual tuple is incorrectly declared orthogonal
to another tuple with the same product.

`SmoothAFEZetaConditionalGramShape.lean` then removes common height *inside* each complete fibre.
Write `s_j=1/2+d_j+i*b_j` and, for a prime tuple `p`, put

```text
H_ij(m) = 1_{m <= N/p_i} W(r*p_i*m/N) exp((s_j-1) log(p_i*m/N)),
F_p(q)  = sum_{prod_i m_i=q} det(H_ij(m_i)),
V_N     = sum_{canonical J-element prime subsets p} sum_q |F_p(q)|^2.
```

The finite implementation pads each cofactor to `Fin N` and stores product `q` at index `q-1`.
The exact common-height factor of a complete fibre is

```text
[prod_j chi(s_j+i*tau) N^(s_j+i*tau-1)]
  * [(prod_i p_i)*q/N^J]^(i*tau).
```

The second bracket has modulus one. Consequently
`integral_reflectedPrimalConditionalGram_det_eq_shape` proves, for every positive prime family,
`N>0`, and real `tau`,

```text
E det(G_N(tau)) = [prod_j |chi(s_j+i*tau)| N^(d_j-1/2)]^2 * V_N.
```

This is an unconditional identity for the literal source, including every product collision.
`V_N` is an explicit nonnegative arithmetic expression independent of common height. Its needed
lower bound is not supplied by the C15.11 mean Gram theorem. Under that theorem's dyadic chi
scaling, a bound of order `N^J` for `V_N` would give a constant mean conditional determinant;
it would still require a joint eigenvalue/background event before a target probability follows.

### C16b — allow a slowly shrinking covariance floor

`[OPEN; revised sufficient probabilistic target]` A constant smallest eigenvalue is stronger than
necessary. Seek one small-prime phase event of probability `N^(-o(1))`, intersecting the fixed base
phase cell, on which the target-centre cost in the inverse conditional covariance is `o(log N)`
and the independent large-prime approximation error is smaller than the desired local mass.
For a bounded centre, a floor `lambda_N` with `1/lambda_N=o(log N)` is a useful sufficient scale;
one must also control the remaining Gaussian volume and channel-size factors.

External evidence: [Seth Hardy, arXiv:2503.06256](https://arxiv.org/abs/2503.06256), Theorems 1--3
and Proposition 5.1, gives a scalar Gaussian-mixture limit for unweighted largest-prime sums,
with a critical-chaos conditional variance and a `sqrt(log log N)` variance normalization.
This does not state the present weighted matrix theorem or deterministic orbit comparison.
The proposed matrix extension is an inference, not an imported result: derive simultaneous
weighted covariance kernels from the literal coefficients, prove their common limiting measure
has enough support, and control the centre on the same base-phase event.

The deep matrix search completed without execution errors and with complete inventory, but
compiler metadata and semantic coverage remain limited. Its returned prime bounds and generic
conditional-independence statements do not prove this weighted matrix estimate. No analytic
premise was inserted into a new Lean theorem.

### C17 — slow cofactor window with several coherent modes

`[OPEN; alternative producer construction, no claimed paper proof]` Instead of relying on typical
critical-chaos phases, seek a prescribed multiplicative small-prime phase pattern with several
coherent logarithmic modes. Restrict the independent large primes to `p` near `N/L`, where
`L=L(N)` grows slowly. A finite phase prescription below `L` can have subpower probability if
its total logarithmic cost is `o(log N)`. A genuinely full-rank channel Gram growing faster than
`1/log N` could then make fixed target costs sublogarithmic.

The constant phase pattern is not enough: its leading cofactor integral supplies only one mode.
The candidate is a unimodular periodic function of `log p` whose multiplicative extension has
several controlled leading partial-sum modes. Required proofs include the phase construction,
a uniform multi-singularity summatory estimate, full-rank literal weighted channel estimates,
the same-event background bound, and quantitative transfer to the actual height interval.
None follows merely by choosing `L` slowly: the moving prime support still depends on `N`, so
fixed-dimensional Kronecker recurrence gives no valid diagonal height bound.

Corpus audit: the deep Selberg--Delange search returned
`SquarefreeConvolutionHalfSelbergDelange.lean`; source inspection and an exhaustive name search
show that its fractional summatory conclusion takes `ZetaBinomialHalfKatoInversion` as an input.
It does not supply the multi-mode estimate needed here. Keep C17 as a paper conjecture; do not
formalize another receiver around that missing asymptotic.

### C17.1 — successive finite-prime extensions

`[PAPER ATTACK, not yet a theorem]` Replace C17's simultaneous multi-singularity asymptotic by
successive scale separation. Freeze a finite prime prefix `S` at arbitrary unit phases. Beyond
that prefix set the multiplicative phase equal to `n^(i*t_k)`, up to a new, much larger cofactor
cutoff `M_k`. After untwisting, the resulting function differs from `1` only at the finite prefix.
Its divisor-convolution correction has an absolutely convergent reciprocal series, with candidate
mean

```text
A_S(t_k) = prod_{p in S} (1 - 1/p) / (1 - u_p*p^(-i*t_k)/p),
```

which is nonzero. A weighted summatory asymptotic would give the node vector
`H_j(t_k)=integral_0^1 W(r*u)*u^(s_j-1+i*t_k) du`. Distinct twists and sufficiently small `r`
should make these vectors independent by the ordinary Cauchy determinant at `r=0`.
At each stage choose `M_k` after the frozen prefix, so `M_k*|A_S(t_k)|^2` can exceed any prescribed
constant. Prime channels with `N/p` near `M_k` would then contribute the corresponding rank-one
direction on scale `1/log N`. Finitely many stages preserve every earlier phase assignment.

Tasks before claiming this covariance producer: prove the literal finite-prefix mean and its
weighted uniform version, choose an independent node packet, transfer to disjoint actual prime
intervals using the fixed-cofactor asymptotic, and extend the finite phase point to a positive
volume cell. The background is a separate quantitative concern: coherent finite prefixes can
inflate its conditional second moment, so a large covariance alone does not prove a small
inverse-covariance target cost. No claim yet of a joint target event or vertical-orbit transfer.

**C17.1 finite-prefix mean — [LEAN-PROVED].**
`SteinhausFinitePrimeCofactorMean.lean` proves
`tendsto_finitePrimePhase_mean` and
`exists_eventually_finitePrimePhase_summatory_norm_lower` for every finite phase prefix, with no
unproved asymptotic premise. Define `f_S(n)=X_n(omega restricted to S)` for positive `n` and
`g_S=mu*f_S`. Multiplicativity and the exact convolution identity `g_S*zeta=f_S` give
`g_S(p^(k+1))=(f_S(p)-1)*f_S(p)^k`. The correction vanishes off the `S`-factored integers.
Each reciprocal prime-power series is geometric with ratio of norm `1/p<1`; the finite Euler
product proves absolute summability and evaluates `sum g_S(d)/d`. Its numerator and denominator
factors are nonzero. Exact hyperbola summation and Tannery then prove
`sum_{n<=M} f_S(n)/M -> prod_{p in S prime} (1-1/p)/(1-f_S(p)/p) != 0`.

The same module defines `finitePrimeTwistExtension`, proves exact agreement on the old prefix,
and factors its character into `n^(i*t)` times a finite phase defect. Thus its untwisted cofactor
mean is explicitly nonzero as well. The final leaf compilation passed without warnings.
The weighted asymptotic is closed in C17.2 below. Actual channel Gram growth, the same-event
centre estimate, and vertical-orbit transfer remain open. This closes the elementary mean step,
not the recurrence producer.

**C17.2 — weighted finite-prefix mean.** `[LEAN-PROVED]` For `0<Re z<1`, the exact theorem is
`M^(-z) sum_{n<=M} f_S(n)*n^(z-1) -> A_S/z`. The corpus already supplies the ordinary normalized
power-sum limit (`DeletionDilationGrowth.rawPrefix_mul_cpow_tendsto`). Twisting the finite divisor
correction by `d^(z-1)` leaves a reciprocal majorant after dividing by `M^z`, so its proven
absolute reciprocal summability permits Tannery without any fractional Tauberian premise.
For the coherent extension use `z=s_j+i*t`; the resulting Cauchy node vectors are the input to
successive scale-separated covariance directions.

`SteinhausFinitePrimeWeightedCofactor.lean` now proves this limit by exact divisor convolution,
the existing power-sum limit, and dominated Tannery. The domination is `C*|g_S(d)|/d`, including
the floor in `M/d`. `tendsto_finitePrimeTwistExtension_weighted_mean` supplies the coherent mode
`A_S(t)/(s_j+i*t)`, with the same nonzero scalar at every node. Both finite-prefix leaf modules
compile without warnings; all eleven exported theorem axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. No recurrence hypothesis enters these proofs.

**Uniformity audit for C17.** A common AFE height rotates the frozen finite-prime defect. A
pointwise mean for each fixed prefix does not justify one cofactor cutoff uniformly over the
moving height. The required strengthening is uniformity over all unit phases on a fixed finite
prefix. The explicit correction has the phase-independent bound
`|g_S(d)| <= 2^(card S)` on `S`-factored integers and vanishes elsewhere; their reciprocal series
is summable. This supplies a concrete candidate for a uniform Tannery proof. Do not silently
exchange the phase and cutoff quantifiers. The conditional-background issue recorded in C17.1
also remains; covariance growth alone does not close the producer.

**Next assembly after C17.2:** use distinct real twists to obtain independent Cauchy node vectors.
At each stage freeze every prime below the previous cofactor cutoff. The weighted asymptotic
then supplies a larger cutoff whose normalized prefix vector escapes the span of the old ones;
the old prefix vectors remain unchanged. This would construct one actual multiplicative phase
with a full-rank finite cofactor packet, extending any prescribed finite prefix. To obtain the
quantitative covariance event, the packet still needs stable cutoff intervals, prime counts,
normalization bounds, and the uniform-phase audit above.


**C17.3 — one compatible full-rank cofactor packet.** `[LEAN-PROVED]`
For distinct nodes `s_j` in `0<Re s_j<1`, any finite prescribed phase set `S`, any prescription,
and any lower cutoff bound `B`, there is one extending phase `omega` and cutoffs `M_i>=B` such
that the matrix with entries
`M_i^(-s_j) sum_{n<=M_i} X_n(omega)*n^(s_j-1)` has nonzero determinant.
The ordinary Cauchy determinant makes the vectors `1/(s_j+i*t)` at finitely many distinct real
integer twists span node space. For any proper subspace, one such vector lies outside it.
C17.2 and the nonzero finite-prefix mean imply that a coherent extension's normalized cofactor
vector eventually stays outside that subspace, after removal of its common unit phase.
Inductively freeze all phase coordinates below earlier cutoffs before applying this escape step.
Earlier rows stay exactly fixed; each new row raises rank. The final leaf module
`SteinhausFinitePrimeCofactorRank.lean` compiles without warnings; all four exported theorem
axiom audits pass with standard axioms only.

This supplies one compatible multiplicative phase, not merely a list of unrelated mode limits.
It remains qualitative: arbitrarily large cutoffs do not by themselves give an arbitrarily large
smallest Gram eigenvalue. A quantitative continuation should prescribe a distinct Cauchy mode at
each stage, use relative approximation after division by its nonzero finite-prefix mean, and
then select cutoffs large enough for the required channel energy. Smooth cutoff transfer,
actual prime interval counts, same-event background/target control, and orbit transfer remain.


**C17.4 — prescribed coherent modes on cofactor blocks.** `[LEAN-PROVED]` A single selected
cutoff gives only an interval of reciprocal width about `1/M^2` if its integer cofactor range is
held fixed. That loses the intended growing channel energy. Instead preserve an entire block
`M<=L<=2M`: C17.2 eventually approximates its Cauchy direction uniformly over all such `L`, after
removing the common phase `L^(i*t)` and dividing by the nonzero prefix mean `A`. Select `M` so
`M*|A|^2` exceeds a prescribed energy budget, then freeze every prime up to `2M`. Repeating with
prescribed distinct twists preserves all earlier blocks. The corresponding reciprocal prime
interval has width of order `1/M`, which retains the factor `M` in the channel covariance.
This stronger packet still requires the literal smooth cutoff and prime interval transfer.


C17.4's final leaf `SteinhausFinitePrimeCofactorModes.lean` and both exported axiom audits pass
with standard axioms only: `exists_prescribed_cofactor_mode_blocks` constructs
one extension, separated blocks `2*M_i<M_j` for `i<j`, nonzero scalars `A_i`, and arbitrary budgets
`M_i*|A_i|^2>=K`. On every integer `L` in each block the relative normalized cofactor vector is
within a prescribed `epsilon` of `1/(s_j+i*t_i)` in the finite node norm. The twists are prescribed
in advance; no distinctness assumption is needed until using their Cauchy matrix as a basis.
The construction freezes all coordinates through `2*M_i` before extending further.

**Literal transfer plan.** For finitely many constructed blocks, choose the AFE smoothing
parameter only after all block means and cutoffs are fixed. The proved bound
`|W(x)-1|<=C*x` makes the smoothing error uniformly small across these finitely many prefixes.
For an actual prime channel put `L=floor(N/p)`. Its extra node factor is
`((p/N)*L)^(s_j-1)`, with `(p/N)*L` between `L/(L+1)` and `1`; taking the initial lower cutoff
large makes this factor uniformly close to `1`. Prime intervals reciprocal to whole blocks have
width comparable to `1/M_i`; their counts must be proved using the actual prime-count source.
This is the next arithmetic covariance transfer, not yet a theorem. A large covariance still
needs same-event control of the conditional centre and the deterministic orbit transfer.

**C17.5 smoothing and prime-window audit.** The normalized Gaussian cofactor packet must hold
for every `0<r<=r0`, not merely at one selected smoothing scale: a literal prime channel uses
the effective scale `r*(p/N)*floor(N/p)`. The finite-prefix limit and a common one-sided
neighborhood of zero give this stronger statement without a new asymptotic premise. The final leaf
`SmoothAFEFinitePrimeCofactorModes.lean` compiles without warnings; both exported theorem
axiom audits pass with only `propext`, `Classical.choice`, and `Quot.sound`. Also, fixed cofactor blocks require primes comparable to `N/M_i`.
They eventually lie above the old `terminalPrimePowerWindow` upper cut `N^(2/3)`. Use the full
large-prime decomposition and prove counts in these new proportional intervals; do not claim
membership in that earlier terminal window.


**Next exact producer obligation after F33.** Establish the literal largest-prime channel
factorization with `L=N/p` and effective cutoff scale `r*p*L/N`, then control the remaining
node factor `((p/N)*L)^(s_j-1)` uniformly for `L` above the chosen initial bound. Use separated
prime intervals reciprocal to the constructed blocks. A verified existing counting input is
`GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge` in
`HTGeometry/AbelianZetaGas/PrimeWindowCount.lean`: for each `q>1`, the count in `(x,q*x]` is
eventually at least `(q-1)/2 * x/log x`. Its companion `card_primesInIoc` identifies the literal
prime set's cardinality. These supply a route to the actual covariance floor; the exact channel
conversion and Gram coercivity are not yet formalized. Same-event centre/target control and
vertical orbit transfer remain separate open obligations. No RH or recurrence claim follows
from the completed finite cofactor packets alone.

**Uniform-prefix alternative to uniform Tannery — [PAPER CANDIDATE].** After obtaining strict
packet error and energy margins, a finite packet certificate is open in its finitely many phase
coordinates. For each prescribed finite prefix point, F32/F33 gives such a certificate; compactness
of the prefix torus may reduce these neighborhoods to finitely many certificates. This could
provide uniform finite cutoff and phase-cell constants over the moving prefix without proving
uniform convergence of the weighted means. The finite phase-cell extension and compact-cover
quantifiers must still be proved; pointwise F32/F33 alone does not justify them. In the literal
height transfer, first remove the common-height row phase and rotate the cofactor variables;
only then estimate the fixed-node factor `((p/N)*L)^(s_j-1)`. Its imaginary part must not still
contain the unbounded common height.

**C17.6 — literal channel transfer.** `[LEAN-PROVED]` For `L=N/p>0`, shift cofactor phases by
`tau*log(q)/(2*pi)` to absorb the common height into `X_m`. The actual reflected-primal channel
then factors into
`chi(s_j+i*tau) * p^(s_j+i*tau-1) * L^s_j`
times F33's smoothed cofactor vector at effective scale `r*p*L/N`, with fixed node `s_j`.
Extracting `N^(s_j+i*tau-1)` leaves one common unit row phase, `L`, and the fixed-node floor
factor `(p*L/N)^(s_j-1)`. This exact identity is proved in `SmoothAFEReflectedCofactorTransfer.lean`; its floor factor
contains only the fixed node, with no hidden large imaginary-height error.

**C17.7 — reciprocal cofactor prime blocks.** `[LEAN-PROVED]` For each fixed `M>=1`, take actual
primes `N/(2M)<p<=N/M`, with integer endpoints interpreted by floor. Their cofactors obey
`M<=N/p<2M`, and different F32 blocks give disjoint prime sets. The corpus PNT window bound at
ratio `2` gives eventually `card>=N/(4M*log N)`, retaining the necessary `1/M` factor.
Combining this count with a channel of squared size `L^2*|A|^2/N` gives the intended
`M*|A|^2/(4*log N)` directional energy. This is only the arithmetic source target; no target law
or recurrence conclusion is assumed.

**C17.6 scratch validation.** The complete scratch file now contains and compiles the literal
channel factorization, the shrinking floor interval, the uniform fixed-exponent floor bound,
and the conductor-normalized channel identity. A scratch assembly omission was caught and
corrected before the full final leaf/axiom audit; the earlier compile covered only the basic
channel identity. No covariance conclusion was inferred from that incomplete audit.

**C17.7 common conditioning seam.** For finitely many blocks with `M_i<=K`, all selected primes
lie in `largePrimes N (N/(2K))`. Once `N/(2K)>=2K+2`, the elementary bound
`N<2K*(N/(2K)+1)` gives `N<(N/(2K))^2`, and all constructed cofactors are below that cutoff.
Thus the full exact largest-prime decomposition can use this one conditioning threshold;
it need not be the old square-root power-window threshold. The prime-block source proof has
no analytic input beyond the corpus's proved PNT interval bound.

**C17.8 — robust Cauchy direction.** `[LEAN-PROVED]` The covariance lower bound does not require
averaging over all choices of a prime from each block. Invertibility of the fixed Cauchy matrix
gives a constant `c>0` such that, for every node coefficient vector `u`, one mode row has pairing
at least `c*norm(u)`. Every row sufficiently close to that same mode preserves half this bound.
Thus every prime in the corresponding cofactor block contributes, and C17.7's count can be
applied to that single block. This avoids a determinant-moment or concentration substitution:
the desired bound is pointwise for every direction `u`. The robust row statement is proved by `exists_cofactorCauchyMode_robust_row_lower`; insertion
into the literal conditional channel energy remains open.

**Pointwise covariance assembly target.** For fixed distinct right-strip nodes and any requested
`A>0`, construct a finite phase extension, a smoothing scale, and a conditioning parameter `K`.
Eventually in `N`, uniformly over the permitted common-height window and all coefficient vectors
`u`, the actual conditional channel energy should exceed `A/log N * norm(u)^2` at the phase
obtained by undoing the exact common-height shift. Use F34 to write each channel as its nodewise
conductor factor times `L*A_i` times a unit row phase and a row close to the selected Cauchy mode.
F35 gives `N/(4*M_i*log N)` primes, while F32 gives `M_i*norm(A_i)^2` as large as needed.
The existing proved chi envelope supplies the remaining `1/sqrt N` conductor scale. The robust
row argument chooses one block for each `u`, so all primes in that block contribute a common
lower bound. This is a proposed full conditional Gram estimate, not yet a proved theorem.
Even after that estimate, a positive-volume phase cell, prescribed-prefix uniformity, same-event
centre/target cost, and deterministic orbit transfer remain to be established.

**C17.9 — uniformly corrected cofactor rows.** `[LEAN-PROVED]` F33 controls the smoothed mode,
whereas F34's literal row also contains `q^(s_j-1)` with `q=p*floor(N/p)/N`. Choose a positive
floor tolerance from the finite maximum Cauchy-row norm, then choose the initial cofactor bound
using F34 before constructing the F33 blocks. For `V` within `epsilon/4` of its Cauchy row `C`,
`|q^(s_j-1)-1|<=delta<=1` gives
`|q^(s_j-1)*V_j-C_j| <= 2*(epsilon/4)+delta*|C_j| < epsilon`.
The actual effective cutoff scale is `r*q`, and F33 applies since `0<q<=1`. `exists_corrected_cofactor_mode_blocks` proves one
finite phase certificate uniform over all actual channels with cofactor cutoffs in the selected
blocks, before the prime counts and robust-row lower bound are applied.


C17.9's final module `SmoothAFECorrectedCofactorModes.lean` now compiles without warnings. Its
statement is uniform over all `N,p` with `M_i<=N/p<=2*M_i`, all positive common smoothing scales
below one fixed threshold, and every node. It retains exact finite-prefix agreement, separated
blocks, positive cutoffs, nonzero means, and arbitrary budgets `M_i*norm(A_i)^2>=K`. Together
with F34's identity, these are the actual normalized rows rather than uncorrected mode limits.
The pointwise conditional covariance inequality described above remains the next unproved
assembly. No probability or recurrence conclusion is being inferred from row control alone.


**F34–F37 validation checkpoint.** All four final leaf compilations passed without warnings.
All thirteen exported theorem axiom audits in `/tmp/BagLiteralPrimeBlockAudit.lean` and
`/tmp/BagCorrectedCofactorAudit.lean` report only `propext`, `Classical.choice`, and `Quot.sound`.
All modules are wired into the umbrella; the formal index is refreshed. Global lint exits 1 on
fourteen unrelated unreachable modules and reports no issue in these BAG leaves. No full build,
numerical experiment, commit, or new analytic premise was used. Independent recurrence and RH
remain unproved; the active obligation is the pointwise conditional covariance assembly above.

**C18 — pointwise conditional covariance producer, LEAN PROVED.** First prove the normalized
literal cofactor channel energy can exceed `H*N/log N * norm(u)^2`, for every prescribed `H>0`,
using one finite phase extension and the common conditioning threshold `N/(2K)`. Use the mode
budget `4*H/c^2`, where `c` is F36's robust row constant. For each `u`, F36 selects a block whose
every prime contributes at least `M_i^2*norm(A_i)^2*c^2*norm(u)^2`. F35's count cancels one `M_i`.
Then transfer through F34's exact common-height identity and the proved chi envelope to the
actual reflected-primal channels, with lower bound `H/log N * norm(u)^2` throughout the height
window. This is a phase-point covariance construction; no phase-cell probability, centre bound,
or deterministic recurrence is assumed in this step.

**C18 normalized proof checkpoint.** The full scratch argument has no remaining mathematical
obligation; two redundant tactics were removed before the final leaf compilation. The normalized
channel retains the exact scalar `L*A*L^(i*t)` of each corrected mode. Squared norms and the
actual prime count prove the lower bound using one selected block for each coefficient vector.
The main statement preserves an arbitrary finite prefix and works for every sufficiently small
positive smoothing scale at every sufficiently large cutoff. Both final leaves compile without
warnings. The six exported theorem axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`.

**Next probability obligation after C18.** The selected conditioning threshold is proportional
to `N`: all its large-prime channel cofactors are bounded by the fixed integer `2K`. Thus the
conditional covariance depends on finitely many prime phases even as `N` grows. A uniform
phase-cell argument must quantify that finite dependence and preserve the covariance margin;
pointwise existence alone does not imply a fixed positive phase-cell measure. Common height
rotates those finite phases, so the eventual probability statement must handle periodicity and
measure uniformly. This does not address the separate conditional-centre/target cost.

**Common-height sign audit.** In F34 the cofactor phase shift is `+tau*log(p)/(2*pi)`.
Consequently C18's randomized phase point is obtained by applying the inverse shift to one fixed
constructed prefix. For the literal unrandomized carrier (`omega=0`), that same shifted prefix
is the ordinary fixed-prime logarithmic flow. A future covariance phase-cell condition can
therefore target a fixed finite torus cell in the shifted coordinates; it need not prescribe a
moving target there. This concerns only the bounded cofactors. It does not supply independence,
a local target law, or orbit transfer for the growing family of large-prime channels.


**C18 actual-channel closure.** `SmoothAFEReflectedConditionalEnergy.lean` proves the exact
node-conductor transfer and a uniform positive conductor lower envelope on
`[5*N/4, 7*N/4]`. Its main theorem constructs the reflected-primal conditional energy bound
`H/log N * norm(u)^2` for every requested `H>0`, eventually in `N`, for every node direction
and every sufficiently small positive smoothing scale. The phase is explicitly the inverse
common-height rotation of the fixed constructed prefix. Finite-prefix agreement belongs to
that unrotated prefix. No probability, conditional-centre, target or orbit assertion is hidden
in the statement.

**C19 — finite character cells, paper mechanism.** Define a cell by simultaneous strict
character inequalities `norm(X_n(eta)-X_n(omega))<epsilon` for `1<=n<=B`, where `B` is fixed.
Each character is continuous in finitely many prime coordinates and invariant under integer
translations of those coordinates. Reduce the centre coordinatewise modulo one. Every open
neighborhood of a point of the closed unit cube has positive Steinhaus product measure: extract
a finite open rectangle and intersect each factor with `[0,1]`; all finitely many factors have
positive interval length, including boundary points. This proves positive cell measure without
assuming the chosen real phase prescription already lies in the unit cube.

For covariance stability, first retain half the robust-row tolerance in C17.9. Its relevant
cofactor lengths are bounded. The cutoff satisfies `norm(W(x))<=1` for positive arguments;
the floor factor stays on `[1/2,1]`, hence has a fixed bound at each fixed node. Finite sums then
bound each corrected-row perturbation by a fixed constant times the maximum character error.
A sufficiently small fixed character cell preserves the mode margin simultaneously for all
cutoffs and allowed smoothing scales. Only after this uniform statement is proved may its
positive cell measure be applied. Common-height measure invariance and same-event centre/target
control remain further obligations.


**C19.1 — finite character cell positivity, LEAN PROVED.**
`SteinhausFiniteCharacterCells.lean` gives integer-period invariance and positive measure around
arbitrary real centres. The final leaf passes without warnings. The argument handles unit-cube
boundary points through genuine positive-length interval intersections.

**C19.2 — uniform cell stability, LEAN PROVED.**
`SmoothAFECofactorCellStability.lean` bounds each finite cofactor sum's perturbation by its
finite absolute coefficient sum times the maximum character error. Norm of the Gaussian cutoff
is at most one; norm of each floor power is at most two. One minimum tolerance over all modes
preserves the corrected rows simultaneously for every admissible `N,p` and positive smoothing
scale. The final leaf passes without warnings. The energy assembly is being strengthened to
quantify over every phase in this one cell; the original point theorem remains a corollary.

**C19.3 — common-height transport, paper proof.** Coordinatewise translation by arbitrary real
`a_p` is represented on `[0,1]` by the existing interval rotation with `fract(a_p)`, using identity
when that fraction is zero. Each coordinate map preserves uniform measure, so their countable
product preserves Steinhaus measure. The representative differs from the raw phase translation
by integer coordinates. Character periodicity removes that difference; multiplicativity under
phase addition shows character differences acquire only a common unit factor. Consequently
finite-character cells have exactly equal mass at every translated centre, in particular under
inverse common-height logarithmic rotation. This proves the required uniform cell mass once
formalised; it leaves the conditional-centre and target law untouched.

**Centre-cost quantifier audit.** A fixed positive covariance-cell mass may depend arbitrarily
badly on the requested covariance constant `H`. Applying an unconditional second-moment bound
and Markov after conditioning on that cell only gives a centre threshold involving the inverse
cell mass. It does not prove that the inverse-covariance target cost divided by `log N` tends
to zero as `H` grows. A slow diagonal in `H` cannot repair that circular comparison by itself.
The next centre argument must work on the same phase event and control the ratio of target
cost to the available covariance, or directly produce a local target lower law. Keep this
obligation explicit when strengthening the phase-point theorem to a positive-measure theorem.


**C19.4 — positive-mass actual covariance event, LEAN PROVED.**
`SmoothAFEReflectedCovarianceEvent.lean` constructs one positive-radius finite-character cell
whose centre is inverse-rotated with common height. Its exact Steinhaus mass is strictly
positive and independent of height. Eventually in `N`, its entire prefix lies below
`Y=N/(2K)`, and every phase in the cell gives the actual reflected-primal lower bound
`H/log N * norm(u)^2` throughout `[5*N/4,7*N/4]`, in every direction and for every common
positive smoothing scale below one threshold. The cell reads only primes below its prefix
bound. The centre before rotation preserves any supplied finite phase prescription.

The normalized and conductor-scaled energy proofs were strengthened to retain the cell; their
old pointwise statements are corollaries. No duplicate arithmetic-count or conductor argument
was introduced. All six affected final leaves pass without warnings, including the strengthened energy
modules. The combined twenty-theorem axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. This closes the fixed positive-measure covariance gate, not the independent
recurrence producer as a whole.

**Next exact mathematical obligation — C20, same-event target cost.** Search and derive the
conditional background law on the finite-character event, preserving the literal reflected
coefficients and the base direct-edge constraints. The first useful algebraic computation is
integration with a finite prime prefix frozen: cross terms survive precisely when the two
integer factorisations agree outside that prefix. Grouping by those exterior frequencies gives
an exact positive sum of squared grouped coefficients. This is a source formula to audit the
centre cost, not an assumed bound. Any proposed bound must keep its dependence on the frozen
prefix and covariance budget visible. The ordinary unconditional Parseval identity and a
cell-mass division are insufficient for the required ratio, as noted above.


**C18–C19 final integration checkpoint.** Six final leaf compilations pass; the initial six-export
C18 audit and final twenty-export C19 audit use only standard axioms. All new leaves are wired,
the search index is refreshed, and targeted whitespace checks pass. Global formal lint exits 1
on fourteen unrelated unreachable modules; no issue is reported in these BAG leaves. No full
build, numerical experiment, new analytic premise, commit or push was used. The RH goal remains
active. The sole research focus remains the independent recurrence producer, with C20's same-event
conditional centre/target law next and deterministic orbit transfer still open.

**C20.1 — frozen-prefix covariance kernel, dependency-closed paper proof.** Let `F_S(omega,eta)`
use the prescribed coordinates `omega_p` on finite `S` and the random coordinates `eta_p`
outside it. For every `n,m`, expand `X_n * conj(X_m)` as the finite product of integer-frequency
characters on the union of their prime factors. Integrate the free coordinates: each contributes
one exactly at zero frequency and zero otherwise, while coordinates in `S` remain fixed. Thus

`E_eta[X_n(F_S) conj(X_m(F_S))] = X_n(F_S(omega,0)) conj(X_m(F_S(omega,0)))`

when `v_p(n)=v_p(m)` for every `p` outside `S`, and equals zero otherwise. All factors have norm
one and are continuous, so the finite product integral and finite-sum expansions are integrable.
Consequently the exact second moment of any finite complex-weighted carrier retains precisely
those pairs. Regrouping by the exterior factorisation gives positive squares; neither this
identity nor positivity alone provides a bound uniform in `S` or the C19 covariance budget.

**C20.2 — possible centre route, OPEN/source search.** A stronger probability statement could
avoid the cell-mass/Markov circularity: if the actual normalized reflected smooth carrier tends
to zero in probability, then its background at the fixed threshold `N/(2K)` does too once the
large-prime part has vanishing second moment. For fixed `K`, the latter reads only bounded
cofactors and has coefficient mass of order at most `1/log N`. For every fixed C19 event of mass
`m_H>0`, background convergence in probability would eventually leave at least `m_H/2` of that
event with background norm at most one, independently of `H`; the cutoff threshold may depend
on `H` and `m_H`. This order of quantifiers is sufficient for a later slow diagonal, unlike a
centre norm bound proportional to `m_H^(-1/2)`. The normalized-carrier vanishing statement is
not established here: deep corpus search is running before any proof or formal premise is
introduced. Prime-only central-limit theorems do not supply this completely multiplicative sum.


**C20.1 FINAL — frozen-prefix source formula, LEAN PROVED.**
`SteinhausFrozenPrefixSecondMoment.lean` proves the explicit frozen-phase product kernel,
its exact exterior-factorisation selection rule, the finite complex quadratic identity, and
`integral_normSq_frozenPrefix_dpoly`: a positive sum of squared grouped coefficient sums.
No positivity restriction on indices or unproved analytic input is needed. Final leaf passes
without warnings; all seven public theorem axiom audits use only standard axioms. Wired and
indexed; targeted whitespace clean. Global lint reports seventeen unrelated unreachable modules
and no BAG issue. This closes the source identity, not the centre bound.

**C20.2 research result and revised paper attack.** Deep search
`/tmp/bag-centre-vanishing-deep.json` completed with full file inventory and no execution errors,
but compiler metadata is largely pending/stale and semantic coverage was not measured. Its
candidate/source lists contain no applicable completely multiplicative low-moment theorem;
the proposed prime-sum ingredient set is unverified and does not fit this carrier. Direct source
search finds Harper mentioned in `SecondMoment.lean`'s historical motivation, not a formal
low-moment theorem there. Granville–Harper–Soundararajan mean-value leaves are a different result.

Primary external evidence, read directly: [Harper, arXiv:1703.06654](https://arxiv.org/abs/1703.06654),
Theorem 1 and Corollary 1 (PDF page 10), proves that the unweighted Steinhaus partial sum divided
by its square-root second-moment scale tends to zero in probability, indeed in first mean. This
is paper evidence, not a Lean input. It supplies a concrete analytic target for C20.2.

The following weighted transfer is our inference and needs its own proof: Abel summation with
`n^(-beta)*W(r*n/N)`, `0<beta<1/2`, transfers an unweighted first-mean `o(sqrt N)` estimate to
`N^(-(1/2-beta))*sum_{n<=N} X_n*n^(-beta)*W(r*n/N) -> 0` in first mean. Positivity, monotonicity
and the bound `0<=W<=1` should make the transfer uniform over positive `r`; fixed logarithmic
node twists are handled by coordinatewise phase rotation. Then prove that the fixed-cofactor
large-prime sector has second moment tending to zero, and subtract it to obtain the background
statement. The main missing dependency is an unconditional Lean proof of the unweighted
low-moment decay. Do not replace it with an assumed receiver or cite the paper as a Lean axiom.

**C20.3 — fixed-cofactor channel upper envelope, paper proof.** Fix `K>0`. For
`p>N/(2K)` in the natural-number sense, `N < 2K*p`; hence every channel coefficient
at `n=p*m`, `1<=m<=N/p`, has `N/(2K)<n<=N`. On a fixed right node
`1/2+d+i*t`, `0<d<1/2`, with `N<=t<=2N`, the proved chi envelope gives
`|chi|<=C*N^(-d)`, while `|n^(s-1)|=n^(d-1/2)` and `|W|<=1`. Therefore
`|a_n|<=C*(2K)^(1/2-d)*N^(-1/2)`. Each channel has fewer than `2K` terms,
so its norm is bounded by a fixed constant times `N^(-1/2)`, for every phase
and every positive smoothing scale. The prime number theorem bounds the number
of channels by `2N/log N` eventually; summing squared norms yields `O_K(1/log N)`
uniformly. Fixed height offsets are absorbed by the common `[5N/4,7N/4]` window.
This closes neither full-carrier low-moment decay nor the same-event target law;
it supplies the vanishing large-prime sector needed by C20.2 and the maximal-channel
control needed by a later local target law. Constants may depend on the fixed
cofactor cutoff and nodes, never on phase, smoothing scale, or conductor.

**C20.2 dependency audit, after the remainder estimate.** The next genuinely missing
analytic source is the normalized full multiplicative first moment, not another conditional
second-moment receiver. Harper's [primary paper](https://arxiv.org/pdf/1703.06654), sections
4.1–4.3 (PDF pages 34–39), obtains its upper low-moment bound from an Euler-product
reduction and two barrier estimates: restricted mass under the barrier and small probability
of barrier failure. The restricted-mass proof uses the tilted random-walk estimate in
Proposition 5. This identifies concrete source obligations; no such estimate is imported
as a premise. Corpus applicability must be checked before reproducing this argument.

The weighted transfer has an elementary dependency-closed *deterministic inequality*:
for decreasing nonnegative weights `w_n=n^(-beta)*W(r*n/N)`, finite Abel summation gives
`sum w_n*X_n = w_N*S_N + sum_{n<N}(w_n-w_(n+1))*S_n`. Its expected norm is bounded by
the same positive combination of `E|S_n|`. Splitting at a fixed `M`, the finite prefix
contributes a constant independent of `N,r`, while an `epsilon*sqrt(n)` tail bound contributes
at most `epsilon*C_beta*N^(1/2-beta)`, since Abel summation again bounds the weighted
square-root increments by that power. Thus the proposed uniform weighted transfer is valid
once the full unweighted first-mean decay is actually proved. This is a paper derivation,
not a new assumed Lean input or a claim that C20.2 is closed.

**C20.3 / F45 — uniform small channels and actual nonsmooth remainder, LEAN PROVED.**
`SmoothAFEReflectedChannelUpper.lean` proves eight exports: the literal coefficient bound,
individual-channel envelope, scalar conditional energy ceiling, simultaneous finite-node
maximal-channel envelope, finite-node energy ceiling and uniform vanishing, exact nonsmooth
remainder second moment, and its uniform `C/log N` upper bound. The remainder statement is
for the actual full coefficient carrier minus `steinhausSmoothCarrier`, not a frozen surrogate.
The cutoff is any fixed positive natural `D` (use `D=2K` for C19). No analytic input is
assumed: the proof uses the existing chi envelope, Gaussian cutoff bound, arithmetic
largest-prime decomposition, Parseval, and proved prime-counting asymptotics. The finite-node
bounds retain all phases, all positive smoothing scales, all directions, and the common-height
window. Final leaf and the shared cutoff-bound export both compile without warnings; axiom
and index checks are running. Independent recurrence remains open at C20.2 full-carrier
low-moment decay, same-event target control, and deterministic orbit transfer.

**F45 verification and next-source search.** All nine axiom audits (eight new exports plus
shared cutoff bound) use only `propext`, `Classical.choice`, and `Quot.sound`. Global lint
reports 21 unrelated unreachable modules and no BAG issue. Targeted whitespace checks pass.

`/tmp/bag-critical-barrier-deep.json` completed with `partial=false`, no execution errors,
and 63,337/63,337 files inventoried. Compiler evidence is mostly pending/stale; semantic
coverage is unmeasured, and refresh deferred to the running background indexer. Its candidates
include finite-circle Laplace/cumulant facts but no applicable tilted Euler-product random-walk
barrier theorem. The proposed ingredient set combines a scalar sign inequality with circle
convexity; it does not establish the required barrier law and is rejected as inapplicable.
A targeted lexical query for `"random walk" barrier` found zero hits. Exhaustive matching of
barrier/random-walk and multiplicative-chaos phrases in project Lean, probability dependencies,
and notes likewise found contextual mentions, a Rajchman transport interface already audited,
and unrelated substring matches, not the required estimate. This is a search result, not a
claim that all possible alternate proofs have been excluded. Next: construct or find a genuine
low-moment source argument, beginning with its Euler-product/barrier dependencies; keep the
proved remainder and covariance-event gates closed and do not substitute a new assumption.

**C20.4 — audited alternatives and next source lemma.** Primary sources now checked:
[Gorodetsky–Wong, arXiv:2405.19151](https://arxiv.org/abs/2405.19151) and
[Hamdan, arXiv:2604.05563](https://arxiv.org/abs/2604.05563). The former short proof imports
Gaussian-chaos comparison; the latter section 2 supplies a direct level-set approach, but still
needs Gaussian increment comparison, a barrier estimate, and a spatial maximum bound. Thus
neither citation alone closes a Lean dependency. We will use their common deterministic source
step first: a uniform quadratic approximation to the literal random Euler product logarithm.

Paper proof of this step: for `|z|<1`, the third-order logarithm remainder is at most
`|z|^3/(3*(1-|z|))`. At a prime `p` and any `Re(s)>=1/2`,
`z=X_p*p^(-s)` has norm at most `p^(-1/2)<=2^(-1/2)<1`. Summing remainders over any finite
prime set therefore gives one bound independent of that set, all phases, and all imaginary
parts, since `sum_p p^(-3/2)` converges. The real part of the logarithmic sum is exactly the
logarithm of the product norm. Consequently the squared product norm lies between two fixed
positive multiples of `exp(2*Re(sum_p(z+z^2/2)))`. Formalize this exact arithmetic source
statement next, not a theorem assuming the desired critical-mass or recurrence bound.

**C20.5 — qualitative barrier route, new paper attack (OPEN).** We need qualitative
first-mean decay, not the sharp double-logarithmic rate. This suggests replacing Gaussian
increment comparison by a zero-one/anti-concentration argument. The following is our proposed
derivation, not a result imported from either source paper.

Let `L_j(h)=log|F_(exp(exp j))(1/2+ih)|` and
`M_j=E exp(2 L_j(0))=prod_(p<=exp(exp j))(1-1/p)^(-1)`. Tilt each independent prime circle
by its normalized squared Euler factor (the Poisson kernel). Under this consistent product law,
the exact mean of the prime logarithmic factor is `-log(1-1/p)`, so `L_j(0)-log M_j` is a
centered independent sum. Its variance grows proportionally to `j`, and a uniform fourth-moment
bound would force a fixed positive probability of exceeding `c*sqrt(j)` on the positive side.
The event that this centered sum stays below `A+2 log(j+1)` for some finite `A` is invariant under
finite prime changes. Zero-one plus that positive-side bound should force its tilted measure
to zero. Thus every fixed finite-time barrier survival probability tends to zero, without a
quantitative ballot theorem.

Separately, a planar mean-value bound for the holomorphic finite Euler product, on discs of
radius proportional to `exp(-j)` contained in one rectangle around `[1/2,1/2+i]`, should give
`E sup_(0<=h<=1)|F_(exp(exp j))(1/2+ih)|^2 <= C exp(2j)`. The arithmetic input is a bounded
ratio of Euler second moments at real parts within `O(exp(-j))` of `1/2`. Markov and a union
bound then control failure of `L_j(h)<=log M_j+A+2 log(j+1)` at any scale and height by
`C exp(-2A) sum_j(j+1)^(-4)`. On the complementary event, the normalized integrated Euler
mass equals its barrier-restricted version. The expectation of that restricted mass is exactly
the tilted survival probability, which tends to zero. Sending the conductor to infinity first,
then `A` to infinity, yields mass convergence in probability; unit mean gives vanishing moments
of every fixed order below one. The existing arithmetic reduction would then yield the missing
full multiplicative low-moment decay once its own sieve/Parseval dependencies are formalized.

Audit next: exact Poisson-kernel tilt law and its centered variance/fourth moments; applicability
of the generic product zero-one theorem; uniform planar mean-value and Euler second-moment
bounds; finite-event measurability and change of measure. Do not treat this outline as closed.

**C20.5 source applicability checkpoint.** The exact tilted mean can use
`GaloisForLFunctions.HTGeometry.circleAverage_poissonKernel_log_norm` with
`f(z)=1-r*z`, centre zero, unit radius, and evaluation point `r`: its value is
`log(1-r^2)`, and the Poisson kernel on the unit circle equals
`(1-r^2)/|1-r*z|^2`. Negating yields the stated mean of the negative log factor.
This source has the right literal integrand; the coordinate-interval measure conversion still
needs proof. By contrast, `EulerTiltCovariance.eulerTiltMass` is a Bernoulli occupancy variance
with weight `p^(-sigma)/(1+p^(-sigma))^2`, not this Poisson tilt; its name alone is no bridge.

`FiniteModificationZeroOne.measure_infinitePi_eq_zero_or_one_of_invariant` already accepts
general coordinate probability laws. The centered tilted factor has a uniform `O(p^(-1/2))`
bound; for a variance floor one can compare its tilted circle density to Haar and use separated
arcs (or the first Fourier coefficient). The sum of single-factor fourth moments is bounded by
`sum_p O(p^(-2))`, while total variance diverges. Independence then supplies a fourth-moment
bound proportional to the squared total variance. No symmetry under the tilted law may be
assumed: derive positive-side anti-concentration from mean zero, a lower bound on `E|Z|` via
second/fourth moments, and Cauchy–Schwarz for `Z_+`.

The available planar L2 submean leaves require an entire function; a finite Euler product is
only holomorphic in a half-plane. A local disc variant is required before using them. For the
spatial second-moment comparison, the key arithmetic difference is bounded by
`delta*exp(2*delta*log Y)*sum_(p<=Y) log(p)/p`, with `delta=O(1/log Y)`. This explicitly
identifies the Mertens input needed to make the rectangle bound uniform.

**C20.4 / F46 FINAL — quadratic Euler comparison, LEAN PROVED.**
`SteinhausEulerQuadraticApprox.lean` (172 lines) defines the literal prime argument, finite
Euler product, and quadratic logarithmic field. Its six public theorems prove the uniform
prime-argument bound, exact exponential/log-norm identities, complex and real uniform remainder
bounds, and two-sided squared-norm exponential comparison. Final leaf compiles without warnings;
six axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Wired, exact-name index
visibility verified, whitespace clean. Global lint reports fifteen unrelated unreachable modules,
no BAG issue. Passing scratch and audit retained; no owned build/search process remains live.
C20.5 remains an open proof strategy, with exact Poisson tilt mean/moments and local maximum
bound still required. Neither full-carrier low-moment decay nor independent recurrence is yet proved.

**C20.5a — coordinate moment source, paper proof.** Write `r=p^(-1/2)`, so
`0<=r<=3/4`, and `Z_r(x)=-log|1-r*e(x)|+log(1-r^2)`. The proposed Poisson law has density
`K_r=(1-r^2)/|1-r*e(x)|^2`. Its mass and mean identities follow from the exact Poisson
formula and the angle-to-interval conversion described above. Pointwise,
`1-r<=|1-r*e(x)|<=1+r`; hence `|log|1-r*e(x)||<=4r`, using
`1-u^(-1)<=log u<=u-1`. Also `|log(1-r^2)|<=2r`, so `|Z_r|<=6r` and
`E_tilt Z_r^4<=1296*r^4`. The same norm upper bound gives `K_r>=1/7`.
For `x` in `[1/3,2/3]`, cosine is at most `-1/2`, so `|1-r*e(x)|^2>=1+r`.
The inequality `log(1+r)>=r/2` gives `Z_r<=-r/4` on that arc, since `log(1-r^2)<=0`.
Integrating there yields `E_tilt Z_r^2>=r^2/336`. The pointwise bound also gives
`E_tilt Z_r^2<=36*r^2`. These are concrete coordinate estimates, without a symmetry
assumption. The corpus far-arc lemma for the *complex* log norm does not by itself establish
this centered *real* variance lower bound; the signed real argument above must be proved.

**C20.5b — positive-tail step, paper proof.** No tilted symmetry is needed. For a mean-zero
real random variable `Z`, put `V=E Z^2>0` and suppose `E Z^4<=C*V^2`, `C>0`.
For every `t>0`, splitting at `|Z|=t` gives the pointwise inequality
`Z^2<=t*|Z|+Z^4/t^2`. Choose `t=sqrt(2*C*V)` to get `E|Z|>=V/(2t)`.
Mean zero implies `E Z_+=E|Z|/2>=V/(4t)`. Set `a=V/(8t)`. Splitting the positive
mean at `a`, then applying Cauchy–Schwarz on `{Z>a}`, gives
`V/(4t)<=a+sqrt(V*P(Z>a))`, hence `P(Z>a)>=1/(128*C)`. Thus the threshold is a
fixed positive multiple of `sqrt(V)`. All these moment and integrability premises must be
derived for the actual product-law prime sums before use in the recurrence producer.
The corpus `FourthMomentEscape.measure_sq_gt_half_ge` bounds a two-sided squared tail,
so it does not directly supply this signed statement. `IntegralCauchySchwarz.sq_integral_mul_le`
is applicable to the last step. This is a paper derivation, not a formalized barrier theorem.

**C20.5a / F47–F48 FINAL — exact tilted coordinate law and moments, LEAN PROVED.**
`SteinhausEulerPoissonTilt.lean` (189 lines) constructs the normalized squared Euler density
and its probability measure, proves positivity and continuity, exact change of measure,
mean `-log(1-r^2)`, and zero centered mean. `SteinhausEulerPoissonTiltMoments.lean`
(169 lines) proves density lower bound `1/7`, centered pointwise bound `6r`, negative
far-arc bound `-r/4`, second-moment floor `r^2/336`, and every absolute-moment upper
bound `(6r)^k` for `0<=r<=3/4`. Both final leaves compile warning-free; fourteen public
theorem axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Both are
wired; exact-name index visibility and whitespace checks pass. Global lint reports nineteen
unrelated unreachable modules, no BAG error. This closes the literal coordinate input,
not the independent recurrence producer. Next: actual infinite product tilt, independent
prime-sum second/fourth moments, signed positive-tail estimate, and zero-one barrier decay;
the spatial maximum, arithmetic reduction, local target, and orbit-transfer gates remain open.

**C20.5c — actual product-law sum moments, paper proof.** Use the coordinate probability
law from F47 at `r_n=randomEulerRadius (1/2) n`, which is zero off primes. The countable
product is a probability measure and the centered log increments are independent. For any
finite set `P`, exact centering and independence give
`E S_P=0` and `E S_P^2=sum_P E Z_n^2`. F48 therefore bounds this variance between
`(sum_P r_n^2)/336` and `36 sum_P r_n^2`. If `n` is outside `P`, expansion and
independence give `E(S_P+Z_n)^4=E S_P^4+6 E S_P^2 E Z_n^2+E Z_n^4`; the cubic-linear
terms vanish by the proved means. Induction gives `E S_P^4<=3888*(sum_P r_n^2)^2`.
Thus the fourth moment is at most `3888*336^2` times the squared variance. The identity
`r_n^2=1/n` at primes and zero elsewhere, together with proved prime harmonic divergence,
forces growing-cutoff variance to infinity. This uses the actual tilted product law.

**C20.5d — variance-indexed barrier, next paper target (OPEN in Lean).** Write `V_N=E S_N^2`
for the actual tilted sum over `range N`. For any cofinal increasing cutoff sequence `u_j`,
consider `E_A={all j: S_(u_j)<=A+2 log(1+V_(u_j))}`. The positive-tail estimate has
threshold `c sqrt(V_(u_j))`; variance divergence and `log x=o(sqrt x)` eventually make
that threshold exceed `A+2 log(1+V_(u_j))`, for each fixed `A`. Consequently each `E_A`
has probability at most `1-delta`. The increasing union over natural `A` has the same upper
bound. Changing finitely many coordinates changes every partial sum by a uniformly bounded
amount, so this union is invariant under finite modifications. The proved product zero-one
law forces its measure to zero. Fixed-A finite-horizon survival then tends to zero.
This choice of barrier postpones quantitative Mertens asymptotics until the spatial maximum
step: at `u_j=floor(exp(exp j))+1`, the already-proved prime reciprocal asymptotics give
`V_(u_j)` comparable to `j`, so global barrier failure still has a summable `j^(-4)` bound.
Prove this literal event and its measurability; do not infer selected-scale barrier death
merely from unboundedness over all integer cutoffs.

**C20.5b–c / F49–F50 FINAL — actual prime-sum moments and signed tail, LEAN PROVED.**
`SteinhausEulerTiltPrimeSum.lean` (331 lines) constructs the actual countable product
probability law and independent centered prime variables, establishes all required finite
power integrability, exact variance additivity, the explicit second/fourth moment bounds,
the uniform fourth-to-variance-squared ratio, and variance divergence. Its eighteen public
theorems pass axiom audits. `SteinhausEulerTiltPositiveTail.lean` (167 lines) proves positive
variance for every cutoff `N>=3`, the explicit positive-tail probability bound, and fixed
`c,delta>0` with `P(S_N>c*sqrt(V_N))>=delta` for all those cutoffs. Its three public
theorems also pass axiom audits. Both final leaf builds are warning-free, both modules are
wired and indexed at their final export lines, and all twenty-one audits use only
`propext`, `Classical.choice`, and `Quot.sound`. Whitespace clean; global lint has fifteen
unrelated unreachable modules and no BAG error. C20.5d's literal zero-one barrier theorem
is next. No barrier decay, full multiplicative low-moment decay, or independent recurrence
producer has yet been claimed.


**C20.5d / F51 FINAL — literal tilted barrier death, LEAN PROVED.**
`SteinhausEulerTiltBarrier.lean` (234 lines) retains every selected cutoff and the exact
barrier `A+2*log(1+V_(u j))`, where `V_N` is the actual F49 variance. For every cofinal
`u : Nat -> Nat`, the union over finite offsets has tilted measure zero, every fixed
real-offset barrier is null, and finite-horizon survival probabilities tend to zero.
No monotonicity of `u`, Gaussian approximation, ballot premise, or recurrence assumption
is required. The proof uses F50's actual signed positive tail, `log(V)=o(sqrt(V))`,
uniform `9*card(D)` finite-phase perturbation bounds, the product zero-one law,
continuity from below (as the monotone-union measure formula), and continuity from above.
Final leaf compiles warning-free; all nine public theorem audits have only `propext`,
`Classical.choice`, `Quot.sound`. Wired into the theorem-area umbrella; exact-name search
finds the survival theorem at line 214. Global lint has seventeen unrelated unreachable
modules and no BAG error. This closes tilted survival, not critical-mass decay or the
independent recurrence producer.

**C20.5e — finite-event change of measure, dependency-closed paper proof.**
For finite cutoff `N`, write `D_N(omega)=prod_(n<N) W_(r_n)(omega_n)`, with the exact
F47 coordinate density. The projection of either actual infinite product law onto
its first `N` coordinates is its corresponding finite product measure. Multiplying
the original finite product measure by `D_N` gives the finite product of the tilted
coordinate measures. Thus for every nonnegative measurable head observable `f`,
`E_original[D_N*f(head_N)]=E_tilt[f(head_N)]`, including indicators.
For the literal finite barrier through `J` cutoffs, choose
`N_J=sup_(j<J) u(j)`. Every sum in the barrier depends only on coordinates `<N_J`;
zero-extending a head changes none of its summands. Its weighted original measure
therefore equals the actual tilted survival probability, and F51 makes this weighted
mass tend to zero for cofinal `u`. No infinite-product Radon--Nikodym derivative is
asserted. Corpus source: `GaussianShiftInformation.pi_withDensity` is a generic
finite-product theorem despite its file name; `Measure.map_infinitePi_infinitePi_of_inj`
and `Measure.infinitePi_eq_pi` supply the exact head distributions. Verify these
sources in the pinned Lean toolchain before finalizing the new leaf.


**C20.5f — variance-selected cutoffs remove the quantitative Mertens clock gate
(PAPER REDUCTION; source bounds still OPEN).** F49's divergent variance permits
cofinal integer cutoffs `u_j>=j+3` with `V_(u_j)>=j`; no prescribed double-exponential
clock is necessary. Write `M_N=prod_(p<N)(1-1/p)^(-1)` and
`F_N(s)=prod_(p<N)(1-X_p*p^(-s))^(-1)`. The needed spatial estimate can be weakened to
`E sup_(0<=h<=1)|F_N(1/2+ih)|^2 <= C*log(N)*M_N` for `N>=3`.
A disc radius `r=c/log(N)` gives this by planar submean: the enclosing rectangle has
area `O(r)`, and the disc prefactor is `O(r^(-2))`. It suffices to prove the uniform
Euler second-moment ratio for `|Re(s)-1/2|<=r`; its logarithm is bounded using
`sum_(p<N) log(p)/p <= C*log(N)`, an elementary Chebyshev/partial-summation input.
Also `M_N>=sum_(1<=n<N)1/n>=log(N)`: every integer below `N` uses only primes below
`N`, and the finite Euler expansion has nonnegative coefficients. Thus the spatial
failure probability at cutoff `u_j` is at most
`C*exp(-2A)*(1+V_(u_j))^(-4) <= C*exp(-2A)*(j+1)^(-4)`.
This removes both quantitative variance/clock synchronization and an upper Mertens
asymptotic from the proposed barrier argument; it does not remove the stated
prime-sum, Euler expansion, second-moment ratio, or local submean obligations.

Audit of passage from selected scales to all final cutoffs: for fixed `J`, the
barrier through `J` uses only the head `N_J=max_(j<J)u_j`. The change-of-measure
identity holds with *any* density cutoff `N>=N_J`. Hence the expected restricted
mass equals the same tilted survival probability, uniformly in every such `N`.
On the global good barrier event all spatial pointwise restrictions are inactive,
so original and restricted integrated masses agree. First choose `A` to make the
global bad event small, then `J` to make tilted survival small, and finally allow
all `N>=N_J`. Markov gives full-cutoff convergence in probability, with no separate
martingale interpolation premise. This audit still requires phase-rotation
invariance and measurable spatial integration; those are not yet claimed formal.


**C20.5e / F52 FINAL — exact finite-event tilt bridge, LEAN PROVED.**
`SteinhausEulerTiltFiniteDensity.lean` (171 lines) proves the exact finite-head
projection law, normalized product density, change of measure for every nonnegative
measurable head observable, and the literal finite-barrier identity for every density
cutoff containing all tested cutoffs. Taking the maximum tested cutoff yields vanishing
restricted original density mass. No global infinite-product density or unproved
probabilistic premise is used. Final leaf compiles warning-free; all six public theorem
axiom audits are standard-only. Wired; exact-name index finds the limit theorem at
line 157. Latest global lint reports twenty unrelated unreachable modules, no BAG error.
Combined F51/F52 close selected-cutoff barrier death and its exact finite-density
transfer. They do not yet prove decay of the spatially integrated critical mass or
independent recurrence.

**C20.5f corpus checkpoint.** Deep arithmetic and second-moment searches completed
non-partial; all twenty candidates and twenty source arguments from each were inspected.
Compiler freshness is mostly pending/stale and semantic coverage unmeasured. Direct
sources found: `Sieve.MertensFirst.mertensFirst_upper` gives
`sum_(p<=N)log(p)/p<=log(N)+log(4)`; `CreaseBudgetPrimeMass.harmonic_le_prod_primesBelow`
gives the required Euler lower bound; mathlib `log_add_one_le_harmonic` supplies its
logarithmic consequence. The second-moment search did not supply an existing theorem
for the literal finite Euler product: finite Dirichlet-polynomial moment identities
are not substitutes for that statement. Derive it from the exact coordinate Poisson
normalization and independence/phase rotation. `HolomorphicBallMeanSq` still assumes
an entire function; its planar bound must be localized to a pole-free closed disc.


**C20.6 — literal Euler second moment, dependency-closed paper proof.**
For complex `z` with `|z|<1` and unit `w`,
`|w-conj(z)|^2=|1-z*w|^2`; hence the Poisson kernel at `conj(z)` on the unit circle
is `(1-|z|^2)/|1-z*w|^2`. Its circle average is one. Pulling out the positive
constant gives `E_x |(1-z*exp(2*pi*i*x))^(-1)|^2=(1-|z|^2)^(-1)` under the original
uniform coordinate law. This handles an arbitrary complex `z`, so no phase-rotation
premise is needed for the second moment. For a prime `p`, the actual Steinhaus
character reads just the `p` coordinate and `|(p:Complex)^(-s)|=p^(-Re(s))<1` on
`Re(s)>0`. Finite-product integration thus proves the literal identity
`E |steinhausFiniteEulerProduct(P,s)|^2=prod_(p in P)(1-p^(-2*Re(s)))^(-1)`.
Measurability follows from continuous nonvanishing coordinate denominators; the
projection of the original infinite product onto `P` has the exact finite product law.
Prove this identity for the actual existing F46 product, then use its literal partition
function in the uniform second-moment ratio and local planar estimate.


**C20.7 — uniform second-moment strip ratio, dependency-closed paper proof.**
For `N>=3`, set `r_N=1/(16*(1+log N))` and let `sigma>=1/2-r_N`.
For prime `p<N`, put `a=1/p`, `b=p^(-2*sigma)`, `t=2*r_N*log p`.
Then `0<=t<=1`, `sigma>=1/4`, and `0<=b<=p^(-1/2)<=3/4`. Since
`b<=a*exp(t)` and `exp(t)-1<=t*exp(t)<=t*exp(1)`,
`b-a<=2*r_N*exp(1)*log(p)/p`. Therefore
`(1-a)/(1-b)=1+(b-a)/(1-b)
 <=1+8*r_N*exp(1)*log(p)/p
 <=exp(8*r_N*exp(1)*log(p)/p)`.
Multiplying the positive factor inequalities and using the verified prime-log bound
`sum_(p<N)log(p)/p<=log N+log 4` gives
`M_N(sigma)<=C*M_N(1/2)` with one fixed positive constant; for example
`C=exp(8*exp(1)*(1+log 4))` suffices, using `r_N<=1` and `r_N*log N<=1`.
This is uniform in the imaginary part by C20.6. No asymptotic Mertens error or
unproved second-moment estimate enters. The generic Euler-product search produced
no applicable replacement theorem (absolute-convergence Euler products apply only
right of one, not in this finite critical strip). Formalize this exact finite ratio.


**C20.6 / F53 FINAL — literal Euler-product second moment, LEAN PROVED.**
`SteinhausEulerSecondMoment.lean` (160 lines) proves complex-coordinate Poisson
normalization, phase-factor continuity, exact prime-character/circle identity, positive
arithmetic partition function, its critical reciprocal-prime specialization, and the
exact squared-norm expectation of the existing F46 finite Euler product throughout
`Re(s)>0`, uniformly in the imaginary part. Final leaf compiles warning-free; all six
public theorem axiom audits use only standard axioms. Wired; exact-name index sees
`integral_norm_sq_steinhausFiniteEulerProduct` at line 121. This closes the literal
second-moment source, not the spatial maximum or recurrence producer.


**C20.8 — local planar mean square, paper proof and source audit.**
The existing `HolomorphicBallMeanSq` result assumes an entire function and cannot
be applied unchanged to finite Euler products. Its proof does localize. Gutzmer's
`HardyDiskSpace.hasSum_circleAverage_normSq_diskCoeffOn` already accepts only
holomorphy on `ball(0,R)`; for every `0<=rho<R`, its constant term gives the circle
mean-square lower bound. For a function continuous on `closedBall(0,R)`, extend its
restriction continuously to the plane using the complex Tietze theorem. This extension
agrees on the closed ball and remains differentiable on the open ball by pointwise
congruence there. The existing polar-shell/Fubini calculation now applies to its
globally continuous squared norm, while every circle estimate uses only local
holomorphy. Integrating `2*pi*rho*|F(0)|^2` gives `pi*R^2*|F(0)|^2`. Restricting the
integral back to the ball and translating proves the desired local planar inequality.
For the actual finite Euler product, every prime factor is holomorphic on `Re(s)>0`:
`|X_p*p^(-s)|=p^(-Re(s))<1` excludes all denominator zeros. Thus every closed disc
of radius `R<c.re` satisfies both local hypotheses. Formalize the local result and
its literal Euler-product specialization; do not assume entire continuation.


**C20.7 / F54 FINAL — uniform literal second moments on spatial discs, LEAN PROVED.**
`SteinhausEulerSpatialPartition.lean` (206 lines) uses the explicit radius
`r_N=1/(16*(1+log N))`, proves it positive and at most `1/16` for `N>=3`, and proves
`M_N(sigma)<=C*M_N(1/2)` for every `sigma>=1/2-r_N`, with one fixed positive `C`.
The theorem is instantiated as an actual squared-norm expectation bound for F46's
Euler product at every complex point in that half-strip. The exact critical partition
is at least one and at least `log N`, giving `1+log N<=2*M_N(1/2)`.
Final leaf compiles warning-free; all eight public theorem axiom audits are standard-only;
wired and exact-name index-visible. Thus the arithmetic moment ratio and radius-cost
absorption are closed. The local planar estimate and global spatial envelope remain
separate obligations, with C20.8 now in scratch.

**C20.9 — explicit measurable spatial envelope, dependency-closed paper proof.**
Write `r=r_N`, `M=M_N(1/2)` and let `Q_N` be the closed rectangle with real
coordinates `[1/2-r,1/2+r]` and imaginary coordinates `[-r,1+r]`. Every disc
`ball(1/2+it,r)` for `t in [0,1]` lies in this rectangle. Its planar area is
`2*r*(1+2*r)<=4*r`. Define the nonnegative extended-real random variable
`Z_N=(pi*r^2)^(-1)*integral_Q_N |F_N(z)|^2 dz`, using the nonnegative Lebesgue
integral. Joint measurability follows from the finite product, measurable prime
characters, continuous nonzero-base complex powers, and measurable inversion.
C20.8 and monotonicity of the nonnegative integral give `|F_N(1/2+it)|^2<=Z_N`
simultaneously for every `t in [0,1]` and every sample. Tonelli and F54 give
`E Z_N <= 4*C*M/(pi*r) = (64*C/pi)*(1+log N)*M <= (128*C/pi)*M^2`.
The exact F53 expectation is positive and finite, which also certifies integrability
of every pointwise squared norm; thus the Bochner and nonnegative moment formulas
agree. All constants and measures are explicit. The envelope replaces an uncountable
supremum and will supply the global barrier estimate through Markov's inequality.
This closes a spatial domination mechanism on paper only; phase rotation, global
barrier assembly, critical-mass decay, and deterministic recurrence remain open.

**C20.8 / F55 FINAL — literal local planar mean square, LEAN PROVED.**
`SteinhausEulerLocalMeanSq.lean` (224 lines) proves the local planar inequality,
holomorphy of the actual finite Euler product on the positive half-plane, its mean
square on every disc with `R<c.re`, and the canonical critical-line-disc specialization.
Final leaf compiles warning-free; all four public axiom audits are standard-only.
Wired; exact-name index sees the canonical-disc theorem at line 212. Global lint
exit 1 lists 18 unrelated unreachable modules, no BAG error. The C20.9 spatial
envelope is now in scratch; it is not yet claimed formalized.

**C20.10 — one geometric aggregate controls every selected scale (paper proof).**
After C20.9 set `C_* = 128*C/pi` and, for any `u_j>=3`, define
`W_u = sum_j 2^(-j-1)*Z_(u_j)/M_(u_j)^2` as a nonnegative Lebesgue sum.
Measurability and Tonelli give `E W_u <= C_*`, since the geometric weights sum to
one and every partition is strictly positive. Consequently
`P(W_u>exp(2A)) <= C_* exp(-2A)`. Every summand is at most the sum, so on
`W_u<=exp(2A)` the bound
`|F_(u_j)(1/2+it)|^2 <= 2^(j+1)*exp(2A)*M_(u_j)^2`
holds simultaneously for all `j` and `t in [0,1]`.
Select the cofinal cutoffs more sparsely, using F49's actual variance divergence:
`u_j>=j+3` and `V_(u_j)>=2^j`. No upper bound or quantitative clock is needed.
Then `2^(j+1)<= (1+V_(u_j))^4`, giving exactly the spatial logarithmic barrier
`log|F_(u_j)(1/2+it)|-log M_(u_j)<=A+2*log(1+V_(u_j))`.
This replaces a countable union and a p-series calculation with one explicit random
variable and a geometric series; F51's survival theorem already accepts every
cofinal sequence, and F52 already accepts all later density cutoffs. The exact
field/centered-log identity, phase-rotation covariance, and spatial change of measure
must still be formalized before using this argument for critical-mass decay.

**C20.9 / F56 FINAL — measurable spatial envelope, LEAN PROVED.**
`SteinhausEulerSpatialEnvelope.lean` (204 lines) proves the rectangle containment
and area, joint measurability of the literal finite Euler product, its exact
nonnegative second moment, and measurability and simultaneous pointwise domination
by the explicit rectangle envelope. Tonelli and F54 yield
`E Z_N <= (128*C/pi)*M_N(1/2)^2` for every `N>=3`.
Final leaf compiles warning-free; all eight public axiom audits are standard-only;
wired and exact-name index-visible. Global lint exit 1: 16 unrelated unreachable
modules, no BAG error. The spatial maximum obligation is now replaced by a proved
explicit envelope. The multiscale aggregate, phase covariance, centered-log identity,
critical-mass decay and independent recurrence remain subsequent obligations.

**C20.11 — literal density and centered-log identification (paper proof).**
At a prime `p`, F53 identifies `X_p` with the coordinate circle phase, and the
positive real base identity gives `p^(-1/2)` as the critical radius. Thus the one-prime
weight is `(1-1/p)*|(1-X_p*p^(-1/2))^(-1)|^2`. At a nonprime coordinate the radius
is zero, the weight is one, and the centered logarithmic increment is zero.
Multiplying through coordinates below `N`, then filtering to primes, gives exactly
`D_N=ofReal(|F_N(1/2)|^2/M_N)`. Summing centered logs gives
`S_N=log|F_N(1/2)|-log M_N`. All logarithm product rules are justified: prime
Euler denominators are nonzero and `M_N>0`; alternatively the existing F46
`steinhausFiniteEulerProduct_eq_exp` and `log_norm_steinhausFiniteEulerProduct`
provide the log-norm sum without branch ambiguity.
For a vertical shift `t`, use the existing measure-preserving coordinate rotation
with shift `a_t(p)=-t*log(p)/(2*pi)`. At every prime this multiplies `X_p` by
`p^(-it)`, so evaluating `F_N` at `1/2+it` equals evaluating the critical-real field
at the rotated sample. The same rotation must transport the entire finite-barrier
event, not only each individual moment. For Tonelli, define the spatial barrier
directly from `log|F_(u_j)(1/2+it)|-log M_(u_j)` and the normalized squared norm.
F56 already gives joint measurability of the field; measurable logarithm and finite
intersections give joint measurability of this restricted density. Only the existing
rotation at each fixed `t` is needed for its expectation, so no joint-measurability
theorem for the rotation map is required. These exact identities and event transport
are next formal obligations; no critical-mass conclusion is claimed yet.

**C20.10 / F57 FINAL — one exceptional event for all selected fields, LEAN PROVED.**
`SteinhausEulerGlobalEnvelope.lean` (134 lines) defines the geometric aggregate
`W_u` and proves its measurability, expectation bound by `C_*=128*C/pi`, literal
Euler-field domination at every selected cutoff and every `t in [0,1]`, and
`P(W_u>=R)<=C_*/R` for every positive real threshold. Only `u_j>=3` is needed.
Final leaf compiles warning-free; all five public axiom audits are standard-only;
wired and exact-name index sees the Markov theorem at line 122. Global lint exit 1
lists 16 unrelated unreachable modules, no BAG error. The actual variance-selected
cutoffs, C20.11 identities/event transport, critical-mass decay and independent
recurrence remain open. F57 is an unconditional ingredient, not a recurrence result.

**C20.11a / F58 FINAL — literal field/tilt identities, LEAN PROVED.**
`SteinhausEulerExactIdentities.lean` (122 lines) proves the exact critical prime
argument, the finite coordinate density identity `D_N=ofReal(|F_N(1/2)|^2/M_N)`,
and the centered-sum identity `S_N=log|F_N(1/2)|-log M_N`, for every cutoff and
sample. Nonprime coordinates are eliminated exactly; no almost-everywhere or
asymptotic identification is substituted. Final leaf warning-free; three public
axiom audits standard-only; wired and index-visible. Latest lint exit 1: ten
unrelated unreachable modules, no BAG error. Phase covariance and whole-barrier
transport are now in scratch; spatial critical-mass decay remains open.

**C20.12 — actual cutoff selection and global good barrier (paper implementation).**
For each integer `j`, let `u_j` be the least `N>=j+3` for which the actual tilted
variance `V_N>=2^j`. F49's divergence proves this set nonempty; the lower bound
forces cofinality without any monotonicity assumption on the selected sequence.
On `W_u<=exp(2A)`, F57 bounds the squared norm by `M_(u_j)^2*2^(j+1)*exp(2A)`.
Since `V>=2^j>=1`, one has `2^(j+1)<=2V<=(1+V)^2<=(1+V)^4`. Taking nonnegative
square roots and then logarithms of the nonzero literal Euler product yields
`log|F_(u_j)(1/2+it)|-log M_(u_j)<=A+2log(1+V)` for all `j` and `t in [0,1]`.
Thus the same good event lies in every F59 finite spatial barrier. F57's Markov
bound gives exceptional measure at most `C_*exp(-2A)`. These operations use the
actual field, variance, and selected cutoffs, not witnesses assumed to have these
properties. Next combine joint measurable spatial integration with F59/F51.

**C20.11b / F59 FINAL — exact whole-barrier vertical transport, LEAN PROVED.**
`SteinhausEulerVerticalBarrier.lean` (132 lines) proves measurable, measure-preserving
vertical rotation; exact prime-character and finite-product covariance (at arbitrary
complex abscissa); exact rotated density and centered-log identities; the whole
finite spatial barrier as a preimage; and its literal restricted-energy expectation
as the tilted survival probability, for every final cutoff containing the tested heads.
Final leaf warning-free; all nine public axiom audits standard-only; wired and index
visible (main theorem line 111). Latest lint exit 1: eleven unrelated unreachable
modules, no BAG error. C20.12 actual cutoff/global good-barrier assembly is now in
scratch; spatial integration and critical-mass convergence remain open.

**C20.13 — full-cutoff critical spatial mass decay (dependency-closed paper proof).**
Define the literal normalized mass `Y_N(omega)=integral_(0<=t<=1) D_N(t,omega) dt`,
using the nonnegative integral and F59's actual spatial density. Let `Y_N^(A,J)`
insert the indicator of the first `J` spatial barriers for C20.12's selected sequence.
F56's joint field measurability gives joint density measurability; measurable real
logarithm and finite intersections give joint restricted-density measurability.
Tonelli and F59 show `E Y_N^(A,J)=nu(B_(A,J))` whenever every tested head is at most
`N`, because the unit spatial interval has measure one. On the single good event
`W_u<exp(2A)`, C20.12 makes all spatial indicators equal one, hence `Y_N=Y_N^(A,J)`
for every final `N`. Markov and set inclusion therefore give, for every `epsilon>0`,
`P(Y_N>=epsilon)<=C_*exp(-2A)+nu(B_(A,J))/epsilon` uniformly over all such final
cutoffs. First choose `A` to make the first term at most `eta/2`; F51 and actual
cofinality then choose `J` making the second term at most `eta/2`; every
`N>=max_(j<J)u_j` now satisfies the desired estimate. Thus the literal normalized
critical spatial mass tends to zero in probability along all natural cutoffs.
No subsequence interpolation, quantitative Mertens clock, uncountable supremum,
or recurrence hypothesis enters this proof. Formalize measurability, exact restricted
expectation, good-event equality, quantitative probability bound, and the limit.

**C20.12 / F60 FINAL — actual selected global barrier, LEAN PROVED.**
`SteinhausEulerSelectedBarrier.lean` (118 lines) constructs least actual cutoffs
`u_j>=j+3` with variance at least `2^j`, proves cofinality, proves the literal
logarithmic-variance barrier everywhere on the unit segment whenever the global
envelope is at most `exp(2A)`, puts that one good event inside every finite spatial
barrier, and bounds the complementary threshold event by `C_*exp(-2A)`.
Final leaf warning-free; all five public axiom audits standard-only; wired and
index-visible. Global lint exit 1: twelve unrelated unreachable modules, no BAG error.
The full-cutoff mass assembly in C20.13 is now in scratch and is not yet claimed proved.


**C20.14 — all subunit moments of critical mass (dependency-closed paper proof).**
For any `0<q<1`, any nonnegative threshold `epsilon`, and `B={Y_N>=epsilon}`,
pointwise `Y_N^q<=epsilon^q+Y_N^q*1_B^(1-q)`. Integrate and apply Holder with
exponents `q` and `1-q` in its weighted mean form. F61's exact unit expectation
then gives `E Y_N^q<=epsilon^q+P(B)^(1-q)`. For positive finite `epsilon`, F61
makes the second term tend to zero along all cutoffs. Given positive finite
`delta`, take `epsilon=(delta/2)^(1/q)` and then make the second term at most
`delta/2`. This proves `E Y_N^q -> 0` for every `0<q<1`, particularly the
square-root moment. Infinite thresholds/tolerances require only the extended-real
order conventions; no domination or uniform integrability premise is introduced.
This closes the probabilistic critical-mass input only. The arithmetic reduction
from Euler-product moments to Steinhaus summatory first mean remains a separate
obligation before weighted/frozen-prefix centre control and deterministic recurrence.


**C20.13 / F61 FINAL — all-cutoff critical mass decay, LEAN PROVED.**
`SteinhausEulerCriticalMass.lean` (181 lines) defines the literal normalized unit-segment
critical mass and its finite-barrier restriction. Ten public theorems prove joint and
integrated measurability, exact restricted expectation, exact unit mean, equality on
the global good event, the two-term probability estimate, and convergence to zero in
probability along all natural cutoffs. The final limit is at line 168. Final leaf
passes warning-free; all ten public axiom audits are standard-only; wired and exact-name
index-visible. Lint exit 1 lists fourteen unrelated unreachable modules, no BAG error.
F62 now formalizes C20.14's fractional-moment consequence. The arithmetic first-mean
reduction and independent recurrence producer remain open.


**C20.14 / F62 FINAL — all fractional critical-mass moments, LEAN PROVED.**
`SteinhausEulerCriticalMoments.lean` (88 lines) proves the exact tail-controlled
fractional-moment inequality, vanishing of every moment `0<q<1` along all natural
cutoffs, and the square-root specialization. Scratch and final leaf pass warning-free;
all three public axiom audits standard-only; wired and exact-name index-visible
(main theorem line 48). Lint exit 1 lists fifteen unrelated unreachable modules.

**C20.15 — fixed-prefix qualitative arithmetic bridge (paper proof; Lean obligations open).**
For a fixed prime cutoff `y`, split each positive integer uniquely as `a*b`, with
`a` supported on primes below `y` and `b` having none. Conditioning on the prefix,
exterior-character orthogonality gives conditional variance
`V_(y,x)=sum_(b rough, b<=x)|sum_(a smooth, a<=x/b) X_a|^2`.
Finite inclusion-exclusion gives `R_y(T)/T -> alpha_y=prod_(p<y)(1-1/p)=1/M_y`.
Expand the squared sums to pairs `(a,c)`. Their coefficient is
`R_y(x/max(a,c))/x`, bounded by `1/max(a,c)<=1/sqrt(ac)`, and converges to
`alpha_y/max(a,c)`. For this fixed finite prime set,
`sum_(a smooth) a^(-1/2)=prod_(p<y)(1-p^(-1/2))^(-1)<infinity`.
Thus dominated convergence for the pair series gives uniformly in all prefix phases
`V_(y,x)/x -> K_y=alpha_y*sum_(a,c smooth) X_a*conj(X_c)/max(a,c)`.
The Cauchy Fourier identity, or Mellin Parseval, gives exactly
`K_y=(1/(2*pi))*integral_R (|F_y(1/2+it)|^2/M_y)/(1/4+t^2) dt`.
Absolute convergence follows from the same finite-prime geometric majorant.
Conditional Cauchy--Schwarz and prefix integration yield
`limsup_(x->infinity) E|sum_(n<=x)X_n|/sqrt(x) <= E sqrt(K_y)` for every fixed `y`.
To show the latter tends to zero, use vertical stationarity and F61 on each of finitely
many unit intervals in a compact window. Markov bounds the complementary weighted
mass by the deterministic Cauchy-kernel tail, uniformly in `y`, since each normalized
pointwise density has mean one. First enlarge the compact window, then send `y` to
infinity: `K_y -> 0` in probability. Its exact mean is one because the chosen
Cauchy density integrates to one, so the same Holder argument as F62 gives
`E sqrt(K_y)->0`. This proves the qualitative first-mean target without any growing
sieve cutoff, rate comparison, or uniform-in-y rough-number estimate.

The limit order is essential: first the summation length with a fixed finite prefix,
then the prefix. All five formal obligations remain explicit: finite-prefix resampling
and conditional norm bound; smooth Dirichlet-series absolute convergence; rough-count
asymptotic and dominated pair limit; Cauchy/Mellin identity; whole-line weighted-mass
decay. The existing frozen-prefix second-moment formula is the exact conditioning
input. Current mathlib's finite-prime geometric theorem already provides the smooth
series once the actual multiplicative coefficient is supplied. Harper's primary paper
[section 2](https://arxiv.org/pdf/1703.06654) supplies adjacent quantitative reduction
and Mellin Parseval context; the fixed-prefix double-limit argument above is derived
here and is not treated as an imported formal theorem. No recurrence claim yet.


**C20.16 — actual smooth Dirichlet expansion (dependency-closed paper proof).**
For fixed sample and complex `s`, extend `X_n*n^(-s)` by zero at `n=0` to a
multiplicative map on naturals. At positive inputs, character multiplicativity and
positive-real-base complex powers give the product law; zero cases and value one
are exact. Its prime norm is `p^(-Re(s))<1` when `Re(s)>0`. Apply current mathlib's
finite-prime geometric theorem to obtain both absolute summability over
`Nat.smoothNumbers N` and exact sum equal to the literal finite Euler product.
Smooth numbers are nonzero, so the artificial zero convention disappears entirely
from the exported series. Norms equal `n^(-Re(s))`; specializing the real part gives
absolute summability of every fixed-prime smooth power majorant `n^(-sigma)` for
all `sigma>0`. No convergence of the full natural-number Dirichlet series is used.


**C20.17 — translated unit masses (dependency-closed paper proof).**
Vertical covariance from F59 gives `D_N(a+t,omega)=D_N(t,rotation_a(omega))`.
Lebesgue translation sends `[0,1]` to `[a,a+1]`, so the literal mass on that interval
is exactly `Y_N(rotation_a(omega))`. F59's measure-preserving rotation therefore
preserves every measurable nonnegative test expectation, hence every fractional
moment and threshold probability. F61/F62 transfer to every translated interval.
The pointwise density itself has exact mean one, by the empty-barrier case of F59.
These identities provide both compact-window decay and uniform tail expectation
for C20.15's whole-line Cauchy weight; no independence between spatial intervals is
asserted or needed.


**C20.16 / F63 FINAL — literal smooth series, LEAN PROVED.**
`SteinhausEulerSmoothSeries.lean` (76 lines) proves the exact coefficient norm,
absolute summability of the literal smooth Dirichlet series for every `Re(s)>0`,
its exact sum and Euler-product identity, and summability of the deterministic
smooth power majorant for every positive exponent. The zero extension is confined
to a private multiplicative map; all exported sums use the actual positive smooth
numbers and actual Steinhaus coefficients. Scratch/final pass warning-free; all
five public axioms standard-only; wired and index-visible (HasSum theorem line 58).
Lint exit 1: thirteen unrelated unreachable modules, no BAG error.


**C20.18 — literal rough-count pair coefficients (dependency-closed paper proof).**
The corpus already contains `roughCount`, exact finite-prime inclusion-exclusion,
and `|X*prod_(p in P)(1-1/p)-roughCount(P,X)|<=card(P.powerset)` in
`ThetaCutoffCommutatorShell.lean`. For every real `d>0` and `x>0`, substitute
`X=x/d` and divide by `x`. This gives
`|roughCount(P,x/d)/x-M_P(1/2)^(-1)/d|<=card(P.powerset)/x`, uniformly in `d`.
Also the literal rough count is bounded by `floor(x/d)`, so its coefficient lies
between zero and `1/d`. Thus it converges to the required inverse-partition
coefficient as `x->infinity`, on both real and natural cutoffs. Taking
`d=max(a,c)` gives precisely C20.15's smooth-pair kernel and domination. No new
sieve estimate is needed; formalize these actual endpoint specializations.


**C20.17 / F64 FINAL — exact spatial stationarity, LEAN PROVED.**
`SteinhausEulerTranslatedMass.lean` (73 lines) proves density covariance, exact
pointwise density mean one, actual translated-interval mass equality with a rotated
unit mass, measurability, stationarity of every measurable nonnegative test, exact
power-moment equality, and subunit-moment convergence on every translated unit
interval. Final leaf warning-free; seven public axioms standard-only; wired and
index-visible at line 66. Lint exit 1: twelve unrelated unreachable modules.


**C20.19 — compact-window fractional moments (dependency-closed paper proof).**
Every `t in [-m,m]` lies in `[floor(t),floor(t)+1]` with the integer floor in
`[-m,m]`. Nonnegative integration and a finite union bound therefore dominate the
literal compact-window mass by the sum of these `2m+1` translated unit masses.
For `0<q<1`, subadditivity of the q-th power gives an expectation at most
`(2m+1)*E Y_N^q`, using F64's exact stationarity. F62 makes this vanish for each
fixed compact window. Endpoint overlaps only enlarge the upper bound; no disjointness
or spatial independence is needed. This supplies C20.15's compact term while leaving
the uniformly integrable Cauchy tail as a separate next step.


**C20.20 — whole-line Cauchy mass (dependency-closed paper proof).**
Use the actual Cauchy probability measure `nu` with location zero and scale one half;
its density is `1/(2*pi*(1/4+t^2))`, bounded by one since `pi>2`. Define
`K_N=integral D_N(t) dnu(t)`. Joint measurability and F64's pointwise unit mean give
measurability and `E K_N=1`; restricting the spatial integral to any set `B` gives
exact expectation `nu(B)`. Split at `[-m,m]`. Domination `nu<=Lebesgue` bounds the
head by C20.19's compact mass. Subadditivity of powers and Holder on the probability
space bound the q-th moment of the tail by `nu([-m,m]^c)^q`, so
`E K_N^q<=E compactMass_(N,m)^q+nu([-m,m]^c)^q` for every `0<q<1`.
Continuity from above of the finite Cauchy measure makes the second term vanish
as `m->infinity`; C20.19 makes the first vanish as `N->infinity` for each fixed `m`.
Thus every subunit moment of the literal whole-line Cauchy mass vanishes. This is
exactly C20.15's required kernel normalization, with no change of abscissa or moving
spatial window. Formalization follows the compact-window leaf.


**C20.18 / F65 FINAL — exact rough-pair coefficient limit, LEAN PROVED.**
`SteinhausEulerRoughCount.lean` (75 lines) identifies the exact rough density with
the reciprocal critical partition, proves the uniform discrepancy bound for every
positive pair scale and summation length, proves reciprocal-scale domination, and
proves the real, natural and literal smooth-pair maximum-kernel limits. Final leaf
warning-free; six public axiom audits standard-only; wired and index-visible (pair
limit line 66). Lint exit 1: fourteen unrelated unreachable modules, no BAG error.


**C20.19 / F66 FINAL — compact-window subunit moments, LEAN PROVED.**
`SteinhausEulerCompactMass.lean` (86 lines) proves joint-integral measurability,
finite translated-interval domination, the exact finite-cover moment bound, and
vanishing of every subunit moment on every fixed compact window. Final leaf passes
warning-free; all four public axiom audits use only standard axioms; wired.
Lint exit 1: sixteen unrelated unreachable modules, no BAG error. Initial API probe
used the wrong namespace for `withDensity_one`/`withDensity_mono` and omitted
`noncomputable` for a density definition; corrected probe passes. No theorem changed.

**C20.21 — literal prefix resampling (dependency-closed paper proof).**
Take two independent Steinhaus samples `(omega,eta)`. Regard them as one independent
family indexed by `Nat + Nat`, using the corpus product-measure splitting theorem.
For each index p select `inl p` if p belongs to S and `inr p` otherwise. This selector
is injective, so its coordinate pullback still has the original infinite product
law. It is exactly `freezeSteinhausPrefix S omega eta`, not a conditional-model
surrogate. Every measurable nonnegative test therefore has the same expectation
under double resampling as under the original law. Apply Holder with exponent one
half to the inner integral of the square of a nonnegative measurable test, then
integrate in omega. This proves the needed first-moment bound by the mean square
root of the literal frozen-prefix second moment, without postulating conditional
expectation or independence of repeated exterior factorizations.


**C20.22 — existing smooth/rough split and exterior classes (paper proof).**
Use the literal `RHTower.Sieve.smoothPart (y-1) n` and `roughPart (y-1) n`.
For prime p, `p <= y-1` is equivalent to `p < y`, including y=0 because primes
are at least two. Their factorizations are the inside/outside filters of
`n.factorization`; current mathlib recovers a filtered prime-power product's
factorization exactly. The latter outside filter is exactly F41's
`steinhausExteriorFactorization (Nat.primesBelow y) n`. Both factors are positive;
for positive n their product is n, by the existing sieve theorem. The first is
literally in `Nat.smoothNumbers y`; no prime in the prefix divides the second.
Conversely, if a is y-smooth and b is positive with no prefix-prime divisor,
filtering `(a*b).factorization = a.factorization+b.factorization` recovers a and b.
Factorization injectivity on positive naturals gives uniqueness. Thus two positive
integers have the same exterior index precisely when they share their rough factor.
This supplies the exact arithmetic reindexing for C20.15, with no new surrogate
notion of roughness and no additional probability hypothesis.


**C20.23 — exact Cauchy smooth-pair kernel (dependency-closed paper proof).**
The corpus theorem `HTGeometry.integral_inv_sq_add_sq_mul_cexp_neg` evaluates
`integral exp(-i*L*t)/(a^2+t^2) dt = (pi/a)*exp(-a*abs(L))` for every a>0.
At a=1/2, multiplying by the literal Cauchy density normalization `1/(2*pi)`
gives characteristic function `exp(-abs(L)/2)` for precisely C20.20's measure.
For positive a,b, expand positive-real-base complex powers via real logarithms:
`a^(-1/2-it)*conj(b^(-1/2-it))` equals
`exp(-(log(a)+log(b))/2)*exp(-i*t*(log(a)-log(b)))`.
Its Cauchy integral is therefore
`exp(-(log(a)+log(b)+abs(log(a)-log(b)))/2) = 1/max(a,b)`.
The last equality follows by either order of a,b and monotonicity of logarithm.
Multiplying by the actual characters gives the required pair coefficient.
F63's absolute smooth-series majorant at 1/2 makes the double series of integrated
norms finite, uniformly in height: its bound is `(sum_smooth a^(-1/2))^2`.
Thus two sum/interchange steps identify the literal squared Euler integral with
the smooth-pair maximum kernel. F58's exact normalization by M_y then identifies
C20.15's arithmetic limit with the literal Cauchy mass from F67. No Plancherel
normalization or boundary-value premise remains implicit in this calculation.


**C20.20 / F67 FINAL — literal whole-line Cauchy mass, LEAN PROVED.**
`SteinhausEulerCauchyMass.lean` (139 lines) proves measurability, exact unit mean,
compact-head/Cauchy-tail fractional-moment control, vanishing of every subunit
moment along all natural cutoffs, and the square-root specialization needed by
C20.15. All five public axiom audits use only standard axioms; final leaf is
warning-free, wired and index-visible (general limit line 118). Lint exit 1:
ten unrelated unreachable modules, no BAG error. Holder uses the explicit original
probability measure; no conditional moment or arithmetic reduction is assumed.


**C20.24 — literal summatory smooth/rough reindexing (paper proof).**
Let R be exactly the finite set counted by `roughCount(P,N)`, with
`P=Nat.primesBelow y`; let A=`Nat.smoothNumbersUpTo N y`. Multiplication bijects
`{(a,b) in A*R : a*b<=N}` with `{1,...,N}`. Positivity gives image membership;
C20.22 gives injectivity; existing sieve factors give surjectivity because both
divide each positive n and their product is n. Hence any finite arithmetic sum
reindexes as `sum_b in R sum_a in A [a*b<=N]*F(a*b)`, including N=0.
For smooth a the frozen-prefix character is `X_a(omega)`, and for rough b it is
`X_b(eta)`, directly from the original prime-factor phase sum. Multiplicativity
therefore gives
`sum_(n<=N) X_n(freeze(omega,eta)) = sum_b in R X_b(eta)*
  sum_a in A [a*b<=N]*X_a(omega)`.
Full-law orthogonality on the positive distinct rough indices gives the exact
frozen-prefix variance as the sum over b of squared norms of these inner sums.
Expanding the finite squares and reversing finite sums counts b subject to
`b*max(a,c)<=N`; this is exactly `roughCount(P,N/max(a,c))`, since max(a,c)>0.
This proves C20.15's literal coefficient identity before any infinite-series limit.


**C20.21 / F68 FINAL — literal prefix-resampling law, LEAN PROVED.**
`SteinhausPrefixResampling.lean` (80 lines) proves joint measurability, exact
pushforward of the independent product law, preservation of every measurable
nonnegative test expectation under double resampling, and the first-moment bound
by the average square root of the literal frozen-prefix second moment. Final leaf
warning-free; all four public axiom checks standard-only; wired/index-visible
(bound line 62). Lint exit 1: ten unrelated unreachable modules. The combined
audit's separate future density-conversion probe had a wrong namespace; all four
F68 checks printed successfully and no F68 theorem was affected. That API is at
root namespace and its corrected probe is combined with the next scratch check.


**C20.25 — uniform arithmetic kernel error (paper proof).**
For fixed y define the deterministic nonnegative pair error
`e_(y,N)=sum_(a,c smooth) abs(roughCount(P,N/max(a,c))/N-alpha_y/max(a,c))`,
where `alpha_y=M_y(1/2)^(-1)`. Every coefficient tends to zero by F65. For N>=1,
its absolute value is bounded by `(1+abs(alpha_y))/max(a,c)` and hence by
`(1+abs(alpha_y))*a^(-1/2)*c^(-1/2)`. F63 makes this double majorant summable.
Dominated convergence of series gives `e_(y,N)->0`. Extend the finite coefficient
formula by zero outside bounded smooth pairs; its count already vanishes there.
Character norms are exactly one, so the normalized literal frozen-prefix variance
V satisfies `abs(V_(y,N)/N-K_y(omega))<=e_(y,N)` for every omega, with K_y the
literal Cauchy mass identified in C20.23. This bound is uniform in all prefix phases.
Thus `sqrt(V_(y,N)/N)<=sqrt(K_y(omega))+sqrt(e_(y,N))`. F68 and integration give
`E abs(sum_(n<=N) X_n)/sqrt(N)<=E sqrt(K_y)+sqrt(e_(y,N))` for every fixed y.
F67 first lets y make the first term arbitrarily small, then series convergence
lets N make the second term small for all sufficiently large N. This realizes
C20.15's order of limits without a separate outer dominated-convergence theorem,
and supplies an explicit deterministic error object for the weighted transfer.


**C20.22 / F69 FINAL — literal smooth/rough exterior classification, LEAN PROVED.**
`SteinhausSmoothRoughSplit.lean` (122 lines) identifies both existing sieve-factor
factorizations, proves actual smooth-number membership and prefix-prime exclusion,
identifies equality of exterior indices with equality of rough factors, recovers
both factors from arbitrary smooth/rough products, and proves pair uniqueness.
All eight public axiom checks standard-only; final leaf warning-free, wired and
index-visible (exterior classification line 67). Lint exit 1: twelve unrelated
unreachable modules, no BAG error. No new arithmetic decomposition object added.


**C20.23 / F70 FINAL — exact normalized Cauchy pair kernel, LEAN PROVED.**
`SteinhausEulerCauchyKernel.lean` (70 lines) proves the characteristic function of
the literal half-scale Cauchy probability measure and its exact critical-power
pair integral `1/max(a,b)` for all positive real a,b. Both public axiom audits
standard-only; final leaf warning-free, wired/index-visible (pair identity line40).
Lint exit 1: eleven unrelated unreachable modules, no BAG error. This discharges
the kernel normalization itself; the absolute smooth-series interchange and
identification with the normalized Euler mass remain separate required steps.


**C20.24 / F71 FINAL — literal finite split and rough variance, LEAN PROVED.**
`SteinhausSmoothRoughSum.lean` (119 lines) proves the exact finite multiplication
reindex for every arithmetic test, the literal smooth and rough frozen-character
identities, the summatory polynomial split, and its exact conditional variance as
a sum of squared smooth-coefficient norms over actual rough integers. Existing
complex-coefficient Parseval discharges orthogonality; no surrogate covariance is
introduced. All five public axiom audits standard-only; final leaf warning-free,
wired/index-visible (rough variance line107). Lint exit 1: twelve unrelated
unreachable modules. Finite-square expansion into literal rough-count pair
coefficients remains required before the limit handoff.


**C20.25 / F72 FINAL — deterministic total pair-count error, LEAN PROVED.**
`SteinhausSmoothPairError.lean` (109 lines) proves summability of the literal
smooth-pair majorant, an all-N absolute coefficient-error bound, absolute
summability and nonnegativity of the total error, and its convergence to zero.
All five public axiom audits standard-only; final leaf warning-free, wired and
index-visible (limit line90). Lint exit1: ten unrelated unreachable modules.
F73 exact integral/series API probes also pass. The uniform comparison with the
literal frozen variance still needs the finite count identity and mass identity.


**C20.23 / F73 FINAL — actual Euler mass equals the smooth-pair series, LEAN PROVED.**
`SteinhausEulerCauchySeries.lean` (179 lines) proves the exact complex smooth-pair
expansion of the whole-line squared finite Euler integral and identifies its
inverse-partition normalization with the original Cauchy mass. Uniform smooth
absolute convergence proves integrability; summable integral norms justify the
series interchange. Both public audits standard-only; final leaf warning-free,
wired/index-visible (mass identity line157). Lint exit1: twelve unrelated
unreachable modules. No arithmetic variance identity or recurrence assumed.


**C20.24 / F74 FINAL — literal finite rough-count pair coefficients, LEAN PROVED.**
`SteinhausSmoothRoughPairCount.lean` (111 lines) proves exact rough quotient
cardinality, zero coefficients beyond the arithmetic cutoff, and the full
finite smooth-pair expansion of the original frozen-prefix variance. All three
public axiom audits standard-only; final leaf warning-free, wired/index-visible
(variance identity line98). Lint exit1: twelve unrelated unreachable modules.
The finite-square expansion and exact maximum constraint are now discharged.


**C20.24 / F75 FINAL — exact infinite arithmetic coefficient series, LEAN PROVED.**
`SteinhausSmoothRoughPairSeries.lean` (69 lines) extends the literal finite pair
count by zero to all smooth pairs, proving its HasSum is exactly the original
frozen-prefix variance and its normalized counterpart for every natural cutoff.
Both public audits standard-only; final leaf warning-free, wired/index-visible
(normalized identity line59). Lint exit1: twelve unrelated unreachable modules.
Finite support and both subtype reindexings are explicit; no infinite arithmetic
interchange or moment asymptotic is assumed.


**C20.25 / F76 FINAL — uniform original variance-to-Cauchy comparison, LEAN PROVED.**
`SteinhausFrozenVarianceCauchyLimit.lean` (104 lines) defines the literal normalized
frozen-prefix summatory variance, proves its nonnegativity, proves pointwise finite
Cauchy mass and its exact real smooth-pair form, and bounds the absolute difference
by F72's deterministic total coefficient error for every cutoff and every phase.
The actual normalized variance therefore converges to the original Cauchy mass at
each fixed prefix. All five public audits standard-only; final leaf warning-free,
wired/index-visible (uniform bound line45). Lint exit1: twelve unrelated
unreachable modules. This closes C20.15's arithmetic variance handoff. The first-
mean consequence, weighted transfer and same-event centre control remain next.


**C20.26 — uniform monotone-weight transfer via a global mean envelope (paper proof).**
The unweighted first-mean limit implies, for every epsilon>0, a constant C>=0 with
`E|S_n| <= C+epsilon*sqrt(n)` for every n (use `E|S_n|<=n` below the threshold).
For any nonnegative decreasing weights at positive indices, exact finite Abel
summation with terminal weight w_(N+1) gives expected weighted magnitude at most
`C*w_1 + epsilon*(w_(N+1)*sqrt(N)+sum_(n=1..N)(w_n-w_(n+1))*sqrt(n))`.
A second finite Abel identity rewrites the parenthesized cost as
`sum_(n=1..N) w_n*(sqrt(n)-sqrt(n-1))`. If `w_n<=n^(-beta)` and
`0<beta<1/2`, the square-root increment is at most `n^(-1/2)`. Existing
`Sieve.sum_rpow_neg_subcritical_le` bounds this cost by
`N^(1/2-beta)/(1/2-beta)+1`. Also w_1<=1. Divide by `N^(1/2-beta)`;
first send N to infinity, then epsilon to zero. This proves uniformity over the
whole weight class, including every positive smoothing scale. The existing
`BourgainPartialSummation.sum_Ioc_weight_mul_eq` supplies the exact finite identity;
its applicability and all new mean/weight interfaces remain to be checked in Lean.


**C20.15 / F77 FINAL — unconditional original arithmetic first-mean decay, LEAN PROVED.**
`SteinhausSummatoryFirstMoment.lean` (151 lines) proves measurability of the literal
normalized summatory norm, its exact frozen conditional square, the first-mean
Cauchy/error inequality, vanishing of the nonnegative normalized moment, its exact
ordinary-real integral form, and
`E abs(sum_(n=1..N) X_n)/sqrt(N) -> 0` along all natural cutoffs.
The fixed-prefix double limit is fully discharged from the original product law;
no low-moment theorem or conditional variance asymptotic is assumed. All six
public axiom audits standard-only; final leaf warning-free, wired/index-visible
(real first-mean limit line138). Lint exit1: ten unrelated unreachable modules.
C20.15 is now closed. Uniform weighted transfer, fixed-cofactor subtraction,
same-event centre/target control and deterministic recurrence remain open.


**C20.26 / F78 FINAL — actual weighted mean Abel envelope, LEAN PROVED.**
`SteinhausWeightedSummatoryAbel.lean` (129 lines) proves finite weighted-norm
integrability, the all-cutoff unweighted mean ceiling, an unconditional global
`C+epsilon*sqrt(n)` mean envelope at every positive tolerance, the exact positive
Abel combination bounding the original weighted mean, and its transfer to the
square-root Abel cost. All five public audits standard-only; final leaf warning-
free, wired/index-visible (envelope transfer line95). Lint exit1: ten unrelated
unreachable modules. Existing sharper power-sum theorem also axiom-audited.
The uniform weight-class limit still needs the explicit cost bound and limit step.


**C20.26 / F79 FINAL — explicit uniform square-root Abel cost, LEAN PROVED.**
`SteinhausAbelSqrtCost.lean` (69 lines) proves the exact increment decomposition,
reciprocal-square-root increment bound, and sharper cost bound
`N^(1/2-beta)/(1/2-beta)` for every nonnegative weight below `n^(-beta)` when
`0<beta<1/2`. Monotonicity is needed by the mean inequality, not this cost bound.
All three public audits standard-only; final leaf warning-free, wired/index-visible
(cost bound line39). Lint exit1: eleven unrelated unreachable modules and two
proof-debt occurrences in unrelated `WeilPrimeDeficitSetRigidity.lean`; no BAG error.


**C20.26 / F80 FINAL — uniform original weighted first-mean decay, LEAN PROVED.**
`SteinhausUniformWeightedMean.lean` (65 lines) proves eventual normalized first-mean
bounds uniformly over all admissible weights at each cutoff, and convergence for
arbitrary cutoff-dependent weight families. Both public axiom audits standard-only;
final leaf warning-free, wired/index-visible (uniform theorem line13). Lint exit1:
twelve unrelated unreachable modules; no proof-debt errors. All four existing
Gaussian-cutoff positivity, upper-bound, monotonicity and reality results also
axiom-audited standard-only. The Gaussian specialization and exact logarithmic
phase/reflected carrier transfer remain to be formalized.

**C20.27 — logarithmic-phase transport, paper proof.**
For n>0, unique prime factorization gives sum_p v_p(n)*log(p)=log(n).
The existing coordinate rotation by -t*log(p)/(2*pi), reduced to the unit cell,
therefore sends X_n to X_n*n^(-it), for every n, not just primes. This rotation
preserves the original product probability law. Consequently every finite
coefficient sum has exactly the same absolute first mean after multiplication
of its n-th coefficient by n^(-it). Combining this identity with the uniform
Gaussian estimate proves uniformity over all real phases t and all positive
smoothing scales r. It does not assert invariance of a fixed conditioning event;
conditional event bounds must be derived separately from the unchanged original
law and actual event mass. Existing rotation/map and finite factorization sources
have been read; the all-integer and integral identities remain to be checked.

**C20.28 — actual reflected-carrier first mean, paper proof.**
For a fixed right displacement 0<d<1/2 set beta=1/2-d. The literal positive-index
coefficient is exactly chi(1/2+d+i*tau)*n^(-beta+i*tau)*W(r*n/N).
Taking the common chi factor outside the finite sum and its norm outside the
integral, C20.27 identifies the remaining mean with the untwisted Gaussian mean.
When tau>=N>0 the existing global chi envelope bounds its norm by C/N^d.
C20.26 therefore gives E|actual reflected carrier|->0, uniformly for tau>=N
and every r>0. For a prescribed epsilon use the Gaussian bound at epsilon/(C+1),
then C*epsilon/(C+1)<=epsilon. No moving-height equidistribution is used here;
this is an estimate in the original phase probability space. Combining it with
F45's fixed-cofactor nonsmooth remainder bound will yield vanishing of the
literal smooth background and hence the bounded-centre subset of each fixed
positive-mass covariance event. Neither local target probabilities nor orbit
transfer follow from this alone.


**C20.26 / F81 FINAL — literal Gaussian weight specialization, LEAN PROVED.**
`SteinhausGaussianWeightedMean.lean` (80 lines) proves nonnegativity, power
majorization, monotonicity, and exact real-to-complex equality for the actual
Gaussian cutoff weights, then uniform normalized first-mean decay over every
positive scale r. All five public audits standard-only; final leaf warning-free,
wired/index-visible (uniform bound line59). Lint exit1: ten unrelated unreachable
modules, no BAG errors. Exact logarithmic phase/reflected-carrier transport next.

**C20.29 — exact smooth projection, stronger paper transfer.**
Averaging X_n after retaining the prime coordinates in a finite set S gives X_n
itself if every prime factor of n lies in S, and zero otherwise. This is the
m=1 case of F44's exact exterior-factorization kernel. Thus the conditional
mean of the literal finite coefficient carrier is precisely its S-smooth sum.
The triangle inequality for this inner integral, followed by Fubini and F68's
resampling law, gives E|smooth sum|<=E|full sum|. With S=primesLE(Y), this is
exactly steinhausSmoothCarrier, for every Y; no fixed-cofactor or Y^2>N
restriction is needed. Combining with C20.28 proves uniform background first-
mean decay over every cutoff Y, every tau>=N and every r>0. This strengthens
C20.2's proposed subtraction transfer. F45 remains useful for small channels
and local limit work, but is unnecessary for this first-mean contraction.
Next audit the literal averaging identity and product integrability in Lean,
then apply Markov on each fixed positive-mass C19 event without rotating it.

**C20.30 — same-event bounded-centre selection, paper proof.**
For finitely many fixed right-strip nodes, sum the uniform first-mean background
bounds, using tolerance epsilon/(J+1) for each component. Markov at threshold
one makes the probability that any component norm exceeds one at most epsilon,
uniformly over the smoothing scale, retained cutoff, and node heights above N.
Hence for every event E with original probability at least m>0, taking epsilon=m/2
leaves probability at least m/2 in E intersected with the event that every
background component has norm at most one. E may depend on height: only its
uniform mass lower bound enters. For the existing C19 covariance cells, every
node height tau+b_j exceeds N throughout tau in [5N/4,7N/4] once N dominates
the finitely many offsets. Intersecting preserves the existing channel-energy
lower bound and the small-prime measurability seam. This closes the centre/mass
quantifier gap if formalized; it does not yet produce the simultaneous local
target probability or its deterministic vertical-flow transfer.


**C20.27 / F82 FINAL — exact logarithmic-phase first-mean transport, LEAN PROVED.**
`SteinhausGaussianPhaseMean.lean` (93 lines) proves all-positive-integer character
covariance under the actual unit-cell rotation, exact finite-sum first-mean
stationarity, the actual Gaussian complex-exponent identity, and uniform mean
decay for every real phase and every positive smoothing scale. All four public
audits standard-only; existing chi-envelope/coefficient-factorization source
audits standard-only. Final leaf warning-free, wired/index-visible (uniform bound
line80). Lint exit1: ten unrelated unreachable modules; no BAG errors.

### C21 — prescribed-mean circle densities for the local target law

**Paper candidate, not yet Lean proved.** The current source searches found the
regular-variation planar LDP and generic tilt material, but no theorem matching
these finite complex vector channels. A direct product-density construction may
supply the required lower bound without a central limit theorem.

Let independent uniform unit complex variables Z_p have vector coefficients
A_p in C^J. Use Euclidean norms here. Suppose the Gram operator
G=sum_p A_p A_p* satisfies G>=lambda*I with lambda>0. For a target v put
w=G^(-1)v and m_p=A_p* w. Then sum_p A_p m_p=v,
sum_p |m_p|^2=<v,G^(-1)v><=|v|^2/lambda, and
max_p |m_p|<=max_p |A_p|*|v|/lambda. Assume this last bound is at most 1/2.

On the p-th original circle use density
q_p(z)=1+2 Re(conj(m_p)*z). It is nonnegative, has mean one, and its tilted
circle mean is exactly m_p. Also E q_p^2=1+2|m_p|^2. The product density
Q=prod_p q_p therefore defines an independent probability law with
E_Q sum_p A_p Z_p=v and
E_Q |sum_p A_p Z_p-v|^2=sum_p |A_p|^2*(1-|m_p|^2)<=V,
where V=sum_p |A_p|^2. If V<=rho^2/2, Chebyshev gives tilted probability at
least 1/2 for the radius-rho target ball. Cauchy-Schwarz in the original law gives

`P(|sum A_p Z_p-v|<rho) >= (1/4)*exp(-2*|v|^2/lambda)`,

because E_P Q^2=prod_p(1+2|m_p|^2)<=exp(2 sum_p|m_p|^2).
For an open ball use Markov on the complement |sum-v|>=rho; the same estimate
holds. These are finite exact identities and inequalities, not a limiting law.

For C19/F45, the proved lower bound uses the sup norm on C^J, hence supplies
Euclidean lambda=H/(J*log N). The fixed-cofactor upper bound gives
max|A_p|=O(N^(-1/2)) and V=O(1/log N), uniformly on the same small-prime
conditioning event. A bounded-centre target with sup norm at most B has
|v|^2<=J*B^2. Thus the displayed lower bound is at least
`(1/4)*N^(-2*J^2*B^2/H)` eventually. For each fixed H the covariance event mass
is a fixed positive prefactor; choose H after the desired power loss and B,
then let N grow. No comparison of H with the inverse cell mass is required.

Required audits: literal one-prime circle identities; finite product-law and
second-moment computations; actual Gram right-inverse estimates with the correct
complex conjugations; measurability in the retained phases; integration of the
conditional lower bound on the bounded-centre covariance event. The direct-edge
constraints, boundary interpolation, deterministic growing-prime orbit transfer,
and full-strip zero-density gate remain separate. This candidate claims no
recurrence or RH result and no literature novelty.


**C20.28 / F83 FINAL — actual reflected-carrier first-mean decay, LEAN PROVED.**
`SmoothAFEReflectedCarrierFirstMean.lean` (79 lines) proves the exact identity
between the literal reflected carrier's absolute first mean and the untwisted
Gaussian mean times the actual chi norm. It then proves unconditional decay
uniformly for every tau>=N and every positive smoothing scale. Both public
audits standard-only; final leaf warning-free, wired/index-visible (decay line40).
Lint exit1: ten unrelated unreachable modules. Smooth projection, same-event
bounded centres and local target/orbit transfer remain to be formalized.

**C21 quantifier refinement.** The auxiliary biased density need only exist for
each retained phase separately. Prove the original conditional target probability
lower bound pointwise, then integrate that original probability. Joint measurability
comes from the literal finite carrier and the actual target event, not from any
chosen Gram inverse or auxiliary tilted-law family. Thus a measurable choice of
inverses or biases is unnecessary. The bounded target premise still must be
verified on the same event with the direct-edge constraints retained.


**C20.29 / F84 FINAL — exact smooth projection and first-mean contraction, LEAN PROVED.**
`SteinhausSmoothCarrierProjection.lean` (101 lines) proves exact averaging of each
character after exterior resampling, exact averaging of the literal finite
carrier to its smooth sum, and first-mean contraction for every finite retained
set, hence every actual smooth-carrier cutoff Y. All four public audits standard-
only; final leaf warning-free, wired/index-visible (actual contraction line96).
A concurrent umbrella edit removed the initial import; restored it and reran
lint. Latest lint exit1: eleven unrelated unreachable modules, no proof-debt or
BAG errors. Combining this with F83 and applying same-event Markov remains next.


**C20.29 / F85 FINAL — actual finite-node smooth first-mean decay, LEAN PROVED.**
`SmoothAFEReflectedSmoothFirstMean.lean` (50 lines) combines the literal reflected
mean theorem and exact smooth projection. It proves uniform background decay
for every retained cutoff and every positive smoothing scale, then simultaneous
summed first-mean decay for any finite collection of fixed right-strip nodes
whose actual heights exceed N. Both public audits standard-only; final leaf
warning-free, wired/index-visible (finite-node estimate line23). Lint exit1: ten
unrelated unreachable modules. Same-event probability selection is next.

**C21 Gram source audit.** The existing complex-Hilbert theorem
`GaloisForLFunctions.HTGeometry.exists_inverse_of_coercive` passes its axiom
audit. Apply it to `G=sum_p rankOne(A_p,A_p)`, whose quadratic form is exactly
`sum_p |inner(A_p,w)|^2`. Choosing `w=G^(-1)v` and
`m_p=inner(A_p,w)` fixes the complex-conjugation convention and gives the
required synthesis and energy bounds directly. Existing `pi_withDensity` and
`SteinhausModel.charInt` also pass standard-only axiom audits. The new affine
circle identities and their local-target assembly are still unformalized.


**C20.30 / F86 FINAL — same-event bounded-centre mass retention, LEAN PROVED.**
`SmoothAFEReflectedBoundedCentreEvent.lean` (81 lines) defines the literal event
that all finite-node smooth backgrounds have norm at most one; proves its
measurability and dependence only on the conditioning primes; bounds its
complement probability by the summed actual first mean; and proves eventual
half-mass retention inside every event of fixed positive original mass. All four
public axiom reports standard-only, as is the existing covariance-event source.
Final leaf warning-free, wired/index-visible (half-mass theorem line64). Lint
exit1: ten unrelated unreachable modules. The audit job's only error was a
future noncomputable rank-one API probe, corrected separately; no public theorem
failed. The actual covariance-cell intersection remains to be assembled in Lean.


**C20 / F87 FINAL — actual same-event covariance and bounded centres, LEAN PROVED.**
`SmoothAFEReflectedCovarianceCentreEvent.lean` (80 lines) constructs a measurable
selected event of fixed positive original mass inside the prescribed rotated
finite-character cell. It reads only the conditioning primes and simultaneously
supports every finite-node background norm at most one and the literal
`H/log N` channel-energy lower bound in every direction, uniformly throughout
the common-height window and over all sufficiently small positive smoothing
scales. The unrotated cell centre preserves the supplied finite phase prefix;
the explicit selected-event containment retains that link. No comparison with
the inverse covariance-cell mass is required. This closes C20's bounded-centre
quantifier gap. The public theorem's axiom audit is standard-only; final leaf
warning-free, wired/index-visible (line12). Lint exit1: ten unrelated unreachable
modules and two temporary proof-debt occurrences in unrelated
`ZetaNotchTruncatedDiagonal.lean`, no BAG error. C21 local target probability,
direct-edge constraints and deterministic orbit transfer remain open.


**C21 / F88 FINAL — exact target synthesis with controlled circle biases, LEAN PROVED.**
`SteinhausFiniteTargetBiases.lean` (57 lines) defines the literal finite rank-one
Gram operator, proves its exact application and energy identities, and derives
biases synthesizing every target from a coercive complex frame. Total squared
bias is at most `norm(v)^2/c`; each bias is at most `norm(a_i)*norm(v)/c`.
The proof uses the audited coercive inverse and fixes all complex conjugations
through the inner product's linear second argument. All three public audits
standard-only; final leaf warning-free, wired/index-visible (synthesis line30).
Lint exit1: twelve unrelated unreachable modules, no proof-debt or BAG error.
Affine circle moments, product probability comparison, and actual conditional
local-target specialization remain open in Lean.


**C21 / F89 FINAL — exact affine circle normalization and target mean, LEAN PROVED.**
`SteinhausAffineCircleMean.lean` (105 lines) proves the circle character algebra,
unit phase norm, continuity and integrability, then the concrete affine density
`q_m(x)=1+2*Re(conj(m)*charFactor(1,x))`. This density is nonnegative for
`norm(m)<=1/2`, has exact original integral one and exact weighted phase mean m.
All ten public axiom reports standard-only; final leaf warning-free, wired and
index-visible (normalization line83). Lint exit1: twelve unrelated unreachable
modules, no proof debt or BAG error. The audit's only error was a future API
probe for an unavailable `MeasureTheory.lintegral_mono_measure`; the actual
source is `lintegral_mono'`, now read. The normalized probability law, density
second moment and finite-product target event are still to be formalized.
