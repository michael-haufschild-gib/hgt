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
