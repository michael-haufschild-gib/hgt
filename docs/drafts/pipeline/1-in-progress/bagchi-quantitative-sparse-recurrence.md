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


**C21 / F90 FINAL — actual affine circle law and exact density energy, LEAN PROVED.**
`SteinhausAffineCircleMeasure.lean` (91 lines) proves the exact density second
moment `1+2*norm(m)^2`, constructs the actual withDensity law, proves probability
normalization for half-unit biases, provides its exact Bochner change of measure
and proves its phase mean is m. All four public axiom reports and the existing
finite-product Tonelli result are standard-only. Final leaf warning-free and
wired; exact second-moment index line11. Lint exit1: thirteen unrelated
unreachable modules, no proof debt or BAG error. Future generic API probes in
the audit failed solely from uninstantiated universe levels; their names resolved
and typed statements were printed. Corrected concrete-universe probes are queued
with the next audit. Event transfer and actual finite-product concentration remain open.


**C21 / F91 FINAL — exact original-event probability from density cost, LEAN PROVED.**
`SteinhausDensityEventCost.lean` (52 lines) proves the squared withDensity event
mass inequality by the existing generic squared Cauchy theorem, then the real
lower bound `q^2/C` and its specialization `(1/4)*exp(-A)` for tilted mass at
least one half and second density moment at most `exp(A)`. All three public
axiom audits standard-only; final leaf warning-free, wired/index-visible (line39).
The corrected concrete-universe future API probes also pass. Lint exit1:
fourteen unrelated unreachable modules, no proof debt or BAG error. These are
source inequalities; the actual affine-product target concentration remains open.


**C21 / F92 FINAL — actual finite affine product and exponential event cost, LEAN PROVED.**
`SteinhausFiniteAffineDensity.lean` (98 lines) defines the original finite uniform
phase law, the explicit affine product density and the independent biased phase
law. It proves probability normalization for half-unit biases, exact product
withDensity identification, exact second density moment `prod(1+2*norm(m_i)^2)`,
its upper bound `exp(2*sum norm(m_i)^2)`, and the original event lower bound
`(1/4)*exp(-2*sum norm(m_i)^2)` for every measurable event with at least half the
biased mass. The product density identification itself needs no bias-size
premise; the probability and moment theorems retain that essential premise.
All seven public axiom reports standard-only; final leaf warning-free,
wired/index-visible (event transfer line88). Lint exit1: thirteen unrelated
unreachable modules, no proof debt or BAG error. Exact centered variance and
concentration for the actual finite-vector target are next.


**C21 / F93 FINAL — exact centered affine-circle variance, LEAN PROVED.**
`SteinhausAffineCircleVariance.lean` (59 lines) proves every circle character
integrable under the actual biased law, exact centering after subtracting m,
and centered second moment `1-norm(m)^2`. All three public axiom reports in the
successor scratch are standard-only; final leaf warning-free, wired and
index-visible (variance line27). Lint exit1: fourteen unrelated unreachable
modules, no proof debt or BAG error. Product coordinate orthogonality and its
finite-Hilbert-sum variance remain next.


**C21 / F94 FINAL — exact covariance under the finite affine product, LEAN PROVED.**
`SteinhausFiniteAffineCovariance.lean` (88 lines) defines the literal centered
coordinate phases and proves continuity, a uniform norm bound, zero mean,
integrability of every pair product and exact diagonal covariance:
`E(conj(Z_i-m_i)*(Z_j-m_j))=delta_ij*(1-norm(m_i)^2)`. Off-diagonal vanishing
uses the actual independent product law and the exact centered mean. All five
public axiom reports in the successor scratch are standard-only; final leaf
warning-free, wired/index-visible (covariance line57). Lint exit1: fourteen
unrelated unreachable modules, no proof debt or BAG error.


**C21 / F95 FINAL — exact biased Hilbert-column variance, LEAN PROVED.**
`SteinhausFiniteAffineVariance.lean` (98 lines) defines the actual centered finite
sum of complex Hilbert columns, proves continuity and integrability of its
squared norm, and proves exact variance `sum_i (1-norm(m_i)^2)*norm(a_i)^2`.
It is therefore at most the original total column energy. No finite-dimensional
assumption on the Hilbert target space is needed for this identity. All four
public axiom reports in the successor scratch standard-only; final leaf
warning-free, wired/index-visible (upper bound line88). Lint exit1: fifteen
unrelated unreachable modules, no proof debt or BAG error.


**C21 / F96 FINAL — actual biased target-ball half mass, LEAN PROVED.**
`SteinhausFiniteAffineTargetMass.lean` (47 lines) proves that the actual centered
Hilbert-column sum lies in the open radius-r ball with at least half the biased
probability whenever the original total column energy is at most `r^2/2` and
r is positive. It uses the exact variance bound, integrability, measurable ball
and Markov inequality; no concentration premise is assumed. Its public axiom
report in the successor scratch is standard-only; final leaf warning-free,
wired/index-visible (line15). Lint exit1: sixteen unrelated unreachable modules,
no proof debt or BAG error. Target synthesis and original-law density cost are
ready to combine into the local lower law.


**C21 / F97 FINAL — finite original-law local target theorem, LEAN PROVED.**
`SteinhausFiniteLocalTarget.lean` (41 lines) proves the quantitative bound
`P(norm(sum_i Z_i*a_i-v)<r) >= (1/4)*exp(-2*norm(v)^2/c)` under the original
independent uniform finite phase law. Its exact structural premises are `c>0`,
`r>0`, actual frame coercivity `c*norm(w)^2<=sum_i |inner(a_i,w)|^2`, each
`norm(a_i)*norm(v)/c<=1/2`, and total column energy at most `r^2/2`.
It constructs the biases from the audited frame inverse, proves half the
actual biased mass lies in the target ball, and pays the explicitly proved
original-law density cost. No local-probability or Gaussian-approximation
premise is assumed. The public axiom report in the successor scratch is
standard-only; final leaf warning-free, wired/index-visible (line15). Lint
exit1: seventeen unrelated unreachable modules, no proof debt or BAG error.
This closes the generic finite local-target mechanism in Lean. Actual prime
carrier specialization, integration on the same retained event, direct-edge
constraints and deterministic orbit transfer remain open.


**C21 / F98 FINAL — local target law under the original infinite product, LEAN PROVED.**
`SteinhausOriginalFiniteLocalTarget.lean` (45 lines) proves that every injective
finite coordinate family in the original Steinhaus space has exactly the finite
uniform product law. It transfers F97's same quantitative target-ball lower
bound to the original infinite Steinhaus law with the same frame, individual
column and total-energy premises. Both public axiom reports in the successor
scratch are standard-only; final leaf warning-free, wired/index-visible (target
bound line22). Lint exit1: seventeen unrelated unreachable modules, no proof
debt or BAG error. Prime-carrier specialization and retained-event integration
remain open; this is an exact distribution transfer, not an orbit assertion.


**C21 / F99 FINAL — literal channel bounds to Hilbert frame bounds, LEAN PROVED.**
`SteinhausChannelEuclideanFrame.lean` (79 lines) proves the exact conjugation
identity between the original bilinear channel test and the complex Hilbert
functional. Sup-norm coercivity H becomes Euclidean coercivity H/J for positive
node count J; a uniform dot bound L bounds each Euclidean column norm by L;
a quadratic directional upper bound C bounds total column energy by J*C.
All four public axiom reports in the successor scratch standard-only; final
leaf warning-free using only its PiL2 import, wired/index-visible (lower bound
line21). Lint exit1: twenty-one unrelated unreachable modules, no proof debt or
BAG error. These formulas retain the original coefficients and supply the exact
interfaces required by the already-proved original-law local target theorem.


**C21 / F100 FINAL — original-law bound for literal finite channel matrices, LEAN PROVED.**
`SteinhausFiniteChannelLocalTarget.lean` (76 lines) reindexes the original local
target law to an arbitrary finite coordinate set, then combines the exact
channel-to-Hilbert bounds into a theorem expressed solely in the original
channel lower, maximal-dot and quadratic-upper inequalities. Its smallness
conditions are `L*norm(v)/(H/J)<=1/2` and `J*C<=r^2/2`; conclusion is original
probability at least `(1/4)*exp(-2*norm(v)^2/(H/J))` for the literal channel sum.
Both public axiom reports in the successor scratch standard-only; final leaf
warning-free, wired/index-visible (channel theorem line42). Lint exit1:
nineteen unrelated unreachable modules, no proof debt or BAG error.


**C21 / F101 FINAL — actual frozen-carrier target law, LEAN PROVED.**
`SteinhausFrozenCarrierLocalTarget.lean` (104 lines) identifies the actual
prime character with the first circle character, proves exact scalar and
Euclidean frozen-carrier decompositions, and applies the original local law
to target minus the literal smooth background. All actual large-prime channel
coefficients are unchanged. Final73748 exit0 warning-free; four public axiom
reports in successor scratch41739 standard-only; wired/index-visible (line77).
Lint89707 exit1: twenty-one unrelated unreachable modules, no BAG error or
proof debt. Actual reflected asymptotics and retained-event integration remain.

**C21 / F102 paper assembly — polynomial conditional cost.**
At fixed cofactor denominator D, original maximal channels are C*N^(-1/2),
and directional energy tends uniformly to zero. A covariance floor H/log N
and shifted Euclidean target norm at most B give eventual admissible biases
since log N/sqrt N tends to zero. F101 then gives conditional original mass
at least `(1/4)*N^(-2*J*B^2/H)`, uniformly in the common height window and
positive smoothing. This is conditional on the actual lower-bound event;
its hypotheses must be discharged with F87, then integrated under F68.


**C21 / F102 FINAL — polynomial actual reflected conditional cost, LEAN PROVED.**
`SmoothAFEReflectedConditionalLocalTarget.lean` (76 lines) combines the actual
maximal-channel and vanishing-energy theorems with F101. On the literal
covariance floor `H/log N`, every shifted Euclidean target bounded by B has
original conditional target probability at least `(1/4)*N^(-2*J*B^2/H)`
eventually, uniformly over common heights and every positive Gaussian scale.
No extra local law or asymptotic input remains in this statement.
Final3827 exit0 warning-free; public axiom report in successor63769 standard-only;
wired/index-visible (line13). Lint71539 exit1: eleven unrelated unreachable
modules, no proof debt/BAG error. Retained-event integration still in scratch.

**C21 prescribed-cell audit and repair (paper).** The existing event's centre
preserves a prescribed finite phase assignment, but its statement does not
guarantee a requested minimum cell prefix or maximum radius. Direct-edge
control needs those additional quantifiers. Starting with the covariance cell,
replace its prefix Bc by max(Bc,B₀) and radius δc by min(δc,δ₀). The smaller
cell still has fixed positive mass under every height rotation and inherits
all covariance inequalities. Its bounded-centre intersection retains half
that fixed mass for all sufficiently large N. Thus arbitrary prescribed
finite-character accuracy is compatible with the polynomial target mechanism.


**C21 / F103 FINAL — integrate the original conditional target law, LEAN PROVED.**
`SteinhausPrefixTargetEvent.lean` (57 lines) proves
`q*mu(E) <= mu(E intersect A)` when E reads only the retained prime coordinates
and every frozen exterior target section has original probability at least q.
The exact prefix-resampling pushforward and product section integral supply
the proof; no measurable selection of auxiliary biases is needed. It also
proves measurability of the literal Euclidean carrier. Final35290 exit0
warning-free; both public audits in F104scratch48649 standard-only; wired/index
visible (line12). Lint83732 exit1: eleven unrelated unreachable modules, no
proof debt/BAG error. Prescribed-cell refinement scratch also passes; final
and its public audit remain before integrated actual-target assembly.


**C21 / F104 FINAL — preserve any requested finite-cell accuracy, LEAN PROVED.**
`SmoothAFEReflectedPrescribedCellEvent.lean` (99 lines) strengthens the actual
covariance/bounded-centre event with arbitrary prescribed `B₀<=B` and
`δ<=δ₀`. It retains the original finite phase prescription, exact rotated
cell containment, fixed positive mass, small-prime dependence, arithmetic seam,
bounded actual backgrounds and every-direction covariance lower bound.
Final78588 exit0 warning-free; public audit in F105scratch2108 standard-only;
wired/index-visible (line13). Lint43918 exit1: eleven unrelated unreachable
modules, no BAG error or proof debt. F105 integrated assembly still in scratch.


**C22 — full Gaussian cofactor source (OPEN; conditional recurrence assembly remains).**
C21 controls the literal finite reflected carrier. Its smoothing is x=N/r;
for small r the omitted reflected tail beyond N is not automatically negligible.
An unconditional o(1) first mean cannot be subtracted from a lower mass
c*N^(-epsilon). Preserve the full Gaussian weight in the cofactor source instead.

The actual inverse-Mellin kernel is `K(w)=exp(w^2)/w`
(`SmoothAFEGaussianKernel.lean:31`), and the proved cutoff derivative is
`-exp(-(log x)^2/4)/(2*sqrt(pi)*x)`
(`HighBlockCutoffMonotone.lean:153`). F112 now proves the full cofactor mean
`A*K(s+i*t)` for a coherent twist with finite-prefix mean A, after the same
complex-power normalization as the sharp cofactor mean. F107 derives the literal
cutoff's Gaussian logarithmic tail formula; F108-F111 supply the exact moment,
real-scale limit, series-to-prefix identity and dominated convergence. The full
source identity is proved; actual full reflected conditional covariance remains
open.

The required mode separation has a direct paper proof. For distinct nodes s_j
with positive real parts, suppose sum_j c_j*K(s_j+i*t)=0 for all real t.
Multiplying by product_j(s_j+z) gives the entire function
`F(z)=sum_j c_j*exp((s_j+z)^2)*product_(k!=j)(s_k+z)`. It vanishes on the
imaginary axis, hence everywhere by the identity theorem. Evaluation at
z=-s_j leaves `c_j*product_(k!=j)(s_k-s_j)=0`, so every c_j=0. This proves
full mode separation without assuming a determinant formula for Gaussian
weights. Lean status: mode separation F106 and actual full-cofactor mean F112 proved.
Prefix-preserving simultaneous packets are proved in F116; conditional covariance, complete AFE
control, boundary interpolation and growing-prime orbit transfer remain open.


**C21 / F105 FINAL — actual finite reflected target event, LEAN PROVED.**
`SmoothAFEReflectedLocalTargetEvent.lean` (121 lines) constructs, for every
finite family of distinct right-strip nodes, every requested original finite
character cell, target norm bound M, tolerance rho>0 and epsilon>0, constants
r0,c>0 such that eventually every common height tau in [5N/4,7N/4], every
0<r<=r0 and every Euclidean target t with norm(t)<=M satisfy
`mu(requested rotated cell intersect {norm(actual finite reflected carrier-t)<rho})
 >= c*N^(-epsilon)`. The original phase prescription is arbitrary. The proof
chooses H=2J(M+J)^2/epsilon, uses the actual bounded-centre event to bound the
shifted target by M+J, applies F102, and integrates with F103. No local-law or
covariance premise remains. The finer event/cell construction is also public.
Final3192 exit0 warning-free; both public audits in F106scratch45046 standard-only;
wired/index-visible (prescribed-cell theorem line82). Lint38691 exit1: ten
unrelated unreachable modules, no BAG error/proof debt. This closes C21's
finite random-carrier target law with arbitrary finite phase constraints.
Full reflected tail/complement control, boundary interpolation and deterministic
growing-prime common-height recurrence remain open; RH is not proved.


**C22 / F106 FINAL — full Gaussian mode separation, LEAN PROVED.**
`SmoothAFEGaussianCofactorModes.lean` (104 lines) proves that the actual kernel
`exp(w^2)/w` has linearly independent imaginary-shift response functions at
every finite family of distinct right-half-plane nodes. Clearing poles gives
an entire function; the identity theorem and evaluation at each distinct pole
force every coefficient to vanish. The corresponding mode vectors span the
whole finite node space and admit a finite nonsingular response matrix.
Final98667 exit0 warning-free; all four public reports in F107scratch42927
standard-only; reused finite-evaluation exports also audited standard-only.
Wired/index-visible (packet theorem line96); lint37972 exit1: eleven unrelated
unreachable modules, no BAG error/proof debt. This closes the mode-separation
part of C22. The actual full-cofactor mean and covariance remain open.


**C22 / F107 FINAL — literal cutoff is a Gaussian log-tail, LEAN PROVED.**
`SmoothAFECutoffGaussianTail.lean` (56 lines) proves the exact logarithmic
derivative, upper-endpoint limit zero, and real/complex identities
`V(exp x)=integral_(y>x) exp(-y^2/4)/(2*sqrt(pi)) dy`. The proof uses the actual
cutoff derivative and rapid-decay source plus the nonpositive-derivative FTC.
Final60503 exit0 warning-free; all four public reports in F108scratch1659
standard-only; wired/index-visible (complex identity line49). Lint44494 exit1:
eleven unrelated unreachable modules, no BAG error/proof debt. Full-cofactor
Gaussian averaging and its mean limit remain to be identified formally.


**C22 / F108 FINAL — exact tilted Gaussian moment, LEAN PROVED.**
`SmoothAFELogGaussianMoment.lean` (57 lines) defines the normalized logarithmic
Gaussian and proves complex exponential integrability, its exact moment
`integral phi(y)*exp(s*y) dy = exp(s^2)`, and integrability of the real
exponential majorants. Final9178 exit0 warning-free; all three public reports
in F109scratch18329 standard-only; wired/index-visible (line28). Lint50176
exit1: thirteen unrelated unreachable modules, no BAG error/proof debt.
Full-cofactor Gaussian averaging and its mean limit remain open.


**C22 / F109 FINAL — real cutoff mean and global power majorant, LEAN PROVED.**
`SteinhausCofactorRealScale.lean` extends the actual coherent weighted cofactor
mean from natural cutoffs to all real floor cutoffs. Boundedness of the original
normalized sequence gives one constant C>0 bounding every prefix at x>=0 by
C*x^Re(s). Final12304 exit0 warning-free; both public audits in F110scratch47456
standard-only; wired/index-visible (line37). Lint36507 exit1: thirteen unrelated
unreachable modules, no BAG error/proof debt. These close the real-scale and
domination inputs for the full Gaussian cofactor mean.


**C22 / F110 FINAL — full Gaussian series as prefix integral, LEAN PROVED.**
`SmoothAFEGaussianPrefixIntegral.lean` proves the exact identity
`sum a_n*V((n+1)/R) = integral phi(y)*sum_(n<floor(R*exp(y))) a_n dy`
for R>0 and summable cutoff-weighted coefficient norms. Its proof identifies
the threshold indicators and their norm integrals, justifying the interchange.
Final25409 exit0 warning-free; public audit in F111scratch2948 standard-only;
wired/index-visible (line31). Lint27781 exit1: thirteen unrelated unreachable
modules, no BAG error/proof debt. The arithmetic summability discharge and
Gaussian normalized limit are drafted, not yet claimed.


**C22 / F111 FINAL — Gaussian prefix-limit transfer, LEAN PROVED.**
`SmoothAFEGaussianPrefixLimit.lean` proves that a real-cutoff sharp-prefix limit
`P(floor x)*x^(-z) -> L`, together with the all-cutoff bound
`norm(P(floor x)) <= C*x^Re(z)`, transfers to the exact Gaussian averaged limit
`(integral phi(y)*P(floor(R*exp y)) dy)*R^(-z) -> L*exp(z^2)`.
The Gaussian times a real exponential dominates the integrand; all measurability,
complex-power cancellation and moment evaluation are discharged. Final14141
exit0 warning-free; public audit in F112scratch41648 standard-only; wired/index
line49. Lint36045 exit1: twelve unrelated unreachable modules, no BAG proof debt.


**C22 / F112 FINAL — actual full Gaussian cofactor mean, LEAN PROVED.**
`SteinhausFullGaussianCofactorMean.lean` proves, for every finite prescribed
phase assignment S,omega, real twist t and 0<Re(s)<1, the literal full-series limit
`(sum_(n>=1) X_n(finitePrimeTwistExtension S omega t)*n^(s-1)*V(n/R))*R^(-z)
 -> A*exp(z^2)/z`, where z=s+i*t and A is the existing explicit nonzero
finite-prime mean. It also proves the exact arithmetic Gaussian-prefix integral
identity. Summability and the limiting argument are discharged; no analytic
mean premise is assumed and no reflected tail is discarded in this identity.
Final10195 exit0 warning-free; both public audits in F113scratch47730 standard-only;
wired/index-visible (line59). Lint94340 exit1: eleven unrelated unreachable
modules, no BAG error/proof debt. This closes C22's actual full-cofactor mean.
Simultaneous prefix-preserving Gaussian mode packets, actual full reflected
conditional covariance, complete AFE/boundary control, and deterministic
common-height growing-prime recurrence remain open. RH is not proved.


**C22 / F113 FINAL — phase-uniform full Gaussian tail control, LEAN PROVED.**
`SteinhausFullGaussianCofactorTail.lean` defines the literal full cofactor and
proves summability for A>0, Re(s)<A; the error after L terms is at most
`C*R^A*L^(Re(s)-A)/(A-Re(s))`, uniformly in every phase. Two phases whose
characters agree through L satisfy the same bound with a doubled constant.
Final29232 exit0 warning-free; all three public audits in F114scratch40925
standard-only; wired/index-visible (line64). Lint49545 exit1: eleven unrelated
unreachable modules, no BAG error/proof debt. This is deterministic tail control
for the full cofactor; it does not yet assert a full reflected target law.


**C22 / F114 FINAL — uniform finite-prefix preservation, LEAN PROVED.**
`SteinhausFullGaussianPrefixStability.lean` proves that, for every node s,
finite upper scale U and tolerance epsilon>0, some finite phase prefix B
preserves the literal full Gaussian cofactor within epsilon simultaneously
for every 0<R<=U and all later phase choices. Final35252 exit0 warning-free;
public audit in F115scratch53942 standard-only; wired/index-visible (line25).
Lint6672 exit1: ten unrelated unreachable modules, no BAG error/proof debt.


**C22 / F115 FINAL — normalized full Gaussian modes and one block, LEAN PROVED.**
`SteinhausFullGaussianCofactorModes.lean` proves finite-node convergence to the
actual Gaussian Mellin mode, normalized finite-prefix stability on 1<=R<=U,
and a prefix-preserving coherent extension realizing any one twist beyond an
arbitrarily late block start M, with arbitrarily large M*norm(A)^2. The mode
approximation holds at every real scale R>=M. Final97341 exit0 warning-free;
all three public audits in F116scratch9927 standard-only; wired/index-visible
(line99). Lint65370 exit1: eleven unrelated unreachable modules, no BAG debt.


**C22 / F116 FINAL — simultaneous full Gaussian mode packets, LEAN PROVED.**
`SteinhausFullGaussianModePackets.lean` constructs one extension of any finite
phase prescription realizing any finite list of Gaussian Mellin twists on
separated real-scale blocks [M_i,2*M_i]. Every block starts beyond a requested
bound and has M_i*norm(A_i)^2 above any requested budget. Quantitative prefix
preservation and a half-tolerance induction retain all earlier full responses.
Final64207 exit0 warning-free; public audit in F117scratch3952 standard-only;
wired/index-visible (line10). Lint4328 exit1: eleven unrelated unreachable
modules, no BAG error/proof debt. Character-cell stability, literal full-channel
conditional covariance and deterministic orbit transfer remain open.


**C22 / F117 FINAL — robust full Gaussian mode lower bound, LEAN PROVED.**
`SmoothAFEGaussianCofactorModeCoercivity.lean` chooses a finite family of actual
Gaussian Mellin twists and positive constants epsilon,c such that every node
coefficient vector has a selected mode whose epsilon-neighborhood retains
pairing norm at least c times the vector norm. The inverse matrix norm and
finite-row perturbation estimate discharge the quantitative frame bound.
Final82716 exit0 warning-free; public audit in F118scratch9534 standard-only;
wired/index-visible (line50). Lint28046 exit1: eleven unrelated unreachable
modules, no BAG error/proof debt.


**C22 / F118 FINAL — uniform full-cofactor character-cell tolerance, LEAN PROVED.**
`SteinhausFullGaussianCharacterStability.lean` constructs a positive tolerance
on finitely many literal characters that controls the complete Gaussian cofactor
uniformly at every 0<R<=U, for arbitrary phase centres. Two uniform tails and
the finite head are bounded separately; no tail is discarded or assumed small.
Final18069 exit0 warning-free; public audit in F119scratch44644 standard-only;
wired/index-visible (line42). Lint23486 exit1: twelve unrelated unreachable
modules, no BAG error/proof debt.


**C22 / F119 FINAL — simultaneous full Gaussian mode cell, LEAN PROVED.**
`SteinhausFullGaussianModeCells.lean` proves normalized finite-node character
stability and places all prescribed Gaussian mode blocks on one fixed
positive-radius finite-character cell. The centre preserves the original finite
phase assignment; every separated real-scale block retains its prescribed
mode and arbitrary mean-weighted energy budget throughout that cell.
Final28138 exit0 warning-free; both public audits in F120scratch92637 standard-only;
wired/index-visible (line58). Lint84656 exit1: eleven unrelated unreachable
modules, no BAG error/proof debt. Literal conditional Gram transfer remains open.


**C22.1 — finite free-prime window (paper refinement; assembly OPEN).**
At smoothing/height scale N and polynomial cutoff L>N, use free primes
`P_N=largePrimes N Y`, retaining the finite set `S_N=primesLE L minus P_N`.
Thus primes above N through L belong to the background. The constructed
reciprocal blocks lie in P_N, and `card(P_N)<=pi(N)` retains the logarithmic
variance saving from the existing prime-count bound. Under `L<Y^2`, every
positive index through L contains at most one free prime, with exponent one;
its remaining cofactor has only retained prime factors. The exact frozen-carrier identity is now Lean proved (F124).

The existing original-law resampling and Jensen projection theorems accept
arbitrary finite S_N, so this conditioning does not require a new probabilistic
law. F129 now proves a uniform Gaussian cofactor absolute bound, each free channel
norm O(N^(-1/2)), and total directional energy O(1/log N). The source covariance
lower bound already sums over this same free window. This avoids an unnecessary
variance estimate over every prime through L.

For the background, a further required source estimate is uniform first-mean
decay with smoothing scale N and independent polynomial cutoff L. The proved
square-root summatory envelope and exact positive Abel-cost identity reduce it
to a Gaussian cost bound: split at N, use the existing N^d/d head bound and
`V(n/N)<=C*N/n` in the tail. The tail p-series then has the same N^d scale,
independent of L. The uniform Gaussian cost and original first-mean consequence are now Lean
proved (F126); the literal reflected/Jensen consequences are being assembled. Complete AFE/boundary control and a quantitative deterministic
common-height return count remain required.


**C22 / F120 FINAL — exact full Gaussian channel normalization, LEAN PROVED.**
`SteinhausFullGaussianNormalizedChannel.lean` proves the exact common-scalar
mode identity, its norm pairing, real cofactor-scale bounds for the existing
reciprocal prime blocks, and
`p^(s-1)*fullCofactor(s,N/p) = N^(s-1)*normalizedFullChannel(s,N/p)`.
The normalization has no floor correction. Final66772 exit0 warning-free;
all four public audits in F121scratch5212 standard-only; wired/index-visible
(line61). Lint49627 exit1: twelve unrelated unreachable modules, no BAG debt.


**C22 / F121 FINAL — full Gaussian source energy, LEAN PROVED.**
`SteinhausFullGaussianChannelEnergy.lean` proves an arbitrary H*N/log N
lower bound in every node direction throughout one fixed character cell,
for the full Gaussian channels on the exact free window
`largePrimes N (N/(2*K))`. The centre preserves the original finite phase
assignment. This is full cofactor source energy; the literal finite conditional
Gram transfer remains open. Final95681 exit0 warning-free; public audit in
F122scratch61373 standard-only; wired/index-visible (line14). Lint24043 exit1:
twelve unrelated unreachable modules, no BAG error/proof debt.


**C22 / F122 FINAL — phase-uniform literal Gaussian truncation, LEAN PROVED.**
`SteinhausFullGaussianTruncation.lean` proves literal finite cofactors converge
to full Gaussian responses uniformly in all phases and bounded positive real
scale ranges. The exact coherent finite-node normalization converges uniformly
on 1<=R<=U. Final97061 exit0 warning-free; all three public audits in
F123scratch81732 standard-only; wired/index-visible (line27). Lint82290 exit1:
twelve unrelated unreachable modules, no BAG error/proof debt.


**C22 / F123 FINAL — exact enlarged-cutoff reflected channel, LEAN PROVED.**
`SmoothAFEReflectedTruncatedGaussianTransfer.lean` identifies the literal
reflected-primal channel at independent smoothing N and polynomial cutoff L
with the truncated Gaussian cofactor at scale N/p and cutoff L/p, after the
exact common-height phase shift. Final89281 exit0 warning-free; public audit
in F124scratch93161 standard-only; wired/index-visible (line12). Lint89108
exit1: thirteen unrelated unreachable modules, no BAG error/proof debt.


**C22.1 / F124 FINAL — literal bounded-free-window decomposition, LEAN PROVED.**
`SteinhausFreePrimeWindow.lean` proves the exact frozen affine decomposition
for free primes (Y,N], retaining all other primes through polynomial cutoff L,
under Y<=N<=L and L<Y^2. Its background is the literal projection onto the
retained primes, and every free channel is the actual length-L channel.
Final5404 exit0 warning-free; public audit in F125scratch10167 standard-only;
wired/index-visible (line17). Lint6240 exit1: eleven unrelated unreachable
modules, no BAG error/proof debt.


**C22 / F125 FINAL — literal truncated Gaussian source energy, LEAN PROVED.**
`SteinhausTruncatedGaussianChannelEnergy.lean` proves exact finite-channel
normalization and mode pairing, uniform fixed-cell mode stability for all
sufficiently long cofactor truncations, and arbitrary H*N/log N directional
energy for every polynomial cutoff L>=N*D. Smoothing N and polynomial L remain
independent. Final56782 exit0 warning-free; all five public audits in
F126scratch14923 standard-only; wired/index-visible (line126). Lint84030
exit1: eleven unrelated unreachable modules, no BAG error/proof debt.


**C22.2 — enlarged-cutoff assembly (paper proof; Lean verification in progress).**
Keep free primes in (N/(2K),N] and retain every other prime through L.
F125 supplies arbitrary directional source energy for every L>=N*D. The
existing chi lower bound and exact common-height unit row phase should transfer
this to the actual H/log N Gram floor (F127 FINAL). Gaussian monotonicity and
the absolute Gaussian mass bound give a uniform cofactor bound over
0<R<=2K, independently of L. Thus each actual free column is O(N^-1/2),
and at most pi(N) free columns give total directional energy O(1/log N)
(F129 FINAL). These constants may depend on the fixed cell and nodes.

The uniform independent-cutoff Abel-cost/first-mean proof is now FINAL in F126. Exact phase transport and arbitrary
finite-S Jensen projection then bound the actual retained background uniformly
in L (F128 FINAL). The fixed cell can therefore retain bounded-centre mass
without discarding an o(1) event against the rare target probability.

Choose smoothing N=n^2 and polynomial length L=n^3. Eventually L>=N*D,
L<(N/(2K))^2, and every fixed character prefix is retained (F130 FINAL).
The original full reflected-primal tail is uniformly O(n^-q) for every q>0:
use Gaussian tail exponent A=q+d+2 and the chi bound at height>=n^2.
The resulting exponent is -q-1/2, stronger than required (F131 FINAL).
This is pointwise in all phases; it requires no subtraction from rare-event
mass. The polynomial target law, full AFE/complement and boundary control,
and deterministic quantitative common-height return count are still open.
Cofinal square windows must carry the full return count, not one shift each.


**C22.1 / F126 FINAL — Gaussian mean uniform in polynomial length, LEAN PROVED.**
`SteinhausGaussianIndependentCutoffMean.lean` proves the absolute Gaussian
Dirichlet mass bound at smoothing N, the resulting square-root Abel cost
C*N^(1/2-beta) for every independent cutoff L, and unconditional original
first-mean decay normalized by that smoothing power, uniformly all L.
Final34074 exit0 warning-free; all three public audits in F127scratch73418
standard-only; wired/index-visible (line100). Lint25738 exit1: ten unrelated
unreachable modules, no BAG error/proof debt.


**C22.2 / F127 FINAL — actual enlarged-cutoff reflected Gram floor, LEAN PROVED.**
`SmoothAFEReflectedWindowConditionalEnergy.lean` proves exact conductor and
unit row-phase separation and arbitrary H/log N directional energy for the
literal reflected channels at every L>=N*D. One fixed character cell works
throughout the common-height window; the original prescribed phases survive.
Together with F124 this is the actual conditional Gram floor when the affine
seam holds. Final22680 exit0 warning-free; all three public audits in
F128scratch87432 standard-only; wired/index-visible (line81). Lint50464 exit1:
eleven unrelated unreachable modules, no BAG error/proof debt.


**C22.2 / F128 FINAL — literal retained-background mean decay, LEAN PROVED.**
`SmoothAFEReflectedWindowFirstMean.lean` proves exact Gaussian phase and
reflected chi mean transport with independent cutoff L, then unconditional
first-mean decay of the actual reflected carrier and every finite retained-prime
projection, uniformly all L and heights above smoothing N. Final13628 exit0
warning-free; all five public audits in F129scratch57497 standard-only;
wired/index-visible (line128). Lint40589 exit1: eleven unrelated unreachable
modules and two unrelated sorry lines in WeilIntegerMassAtomicRigidity;
no BAG error/proof debt.


**C22.2 / F129 FINAL — independent-cutoff channel upper bounds, LEAN PROVED.**
`SmoothAFEReflectedWindowChannelUpper.lean` proves phase-uniform truncated
cofactor bounds on every bounded real scale range, actual bounded-free-window
channels O(N^-1/2), and their finite-node maximal-dot and total directional
energy O(1/log N) bounds. Every estimate is uniform over all polynomial lengths
L and the stated height window. Final3386 exit0 warning-free; all four public
audits in F130scratch74049 standard-only; wired/index-visible (line152).
Lint38838 exit1: twelve unrelated unreachable modules, no BAG/proof debt.


**C22.2 / F130 FINAL — compatible square/cubic cutoff scales, LEAN PROVED.**
`SteinhausSquareScaleWindowSeam.lean` proves that smoothing n^2 and polynomial
cutoff n^3 eventually satisfy the long-cofactor condition n^2*D<=n^3, affine
seam n^3<(n^2/(2K))^2, and every fixed retained-prefix bound. Final95469 exit0
warning-free; public audit in F131scratch46365 standard-only; wired/index-visible
(line11). Lint1867 exit1: twelve unrelated unreachable modules, no BAG debt.
This scale choice retains the requirement of a quantitative return count in
each selected height window; one return per square scale does not suffice.


**C22.3 — Gaussian mode density on a disc (larger-disc formulation FINAL below).**
Target: for a closed disc K centred at c with 0<r<Re(c), every function
holomorphic on a neighbourhood of K is uniformly approximable on K by finite
complex linear combinations of `exp((s+i*t)^2)/(s+i*t)`, with real t.
This is linear-span density, not merely density of the generated algebra.

Paper argument: take a continuous complex-linear functional Lambda on C(K)
annihilating every such mode. The translated-kernel transform
`F(w)=Lambda_s(exp((s+w)^2)/(s+w))` is holomorphic on the connected exterior
of -K: locally, the pole denominator is uniformly separated from zero over K,
so the kernel is holomorphic as a C(K)-valued map. F vanishes on the imaginary
axis, hence throughout that exterior by the identity theorem. Choose a slightly
larger disc on which f is holomorphic and its reflected boundary circle Gamma.
Then the contour integral of `f(-w)*F(w)` is zero. Continuous linearity permits
Lambda to commute with this continuous C(K)-valued contour integral. For each
s in K, Cauchy's formula for
`f(-w)*exp((s+w)^2)/(w+s)` gives `2*pi*i*f(s)`: the numerator at w=-s is f(s).
Thus Lambda(f)=0. Complex Hahn-Banach separation puts f in the closed mode span.
The Banach-valued holomorphy, connected-exterior, contour-interchange and
linear separation steps are now checked in F146-F151, in the exact
larger-disc formulation recorded below.

This suggests a route to the random holomorphic target event: prove locally
uniform full-cofactor mean convergence, preserve mode packets in the C(K) norm,
and use bounded-background families on a larger disc plus tilted free-channel
variance control on that disc. Pointwise F112 convergence alone is insufficient.
A possible compact-uniform upgrade uses Cauchy's formula on a larger circle,
pointwise convergence there, and a uniform absolute Gaussian majorant across
its abscissa interval. The literal complementary AFE edge and deterministic
common-height return count remain separate open inputs.

Source audit: deep Gaussian-density search returned no ready theorem closing
this statement; finite-node Gaussian mode separation is available. Read
HTGeometry/DiscPolynomialDensity and RungeInterfaceDischarge: useful nearby
infrastructure, but neither supplies this Gaussian linear-span theorem.
Read CauchyKernelDensityVanishing lines1-190: its real-line support requires
two half-plane controls and does not replace the compact-disc argument.


**C22.2 / F131 FINAL — full reflected tail at square/cubic scales, LEAN PROVED.**
`SmoothAFEFullReflectedCubicTail.lean` identifies the full reflected-primal
series and its literal finite carrier, then proves a pointwise all-phase
C*n^-q tail for every q>0 at smoothing n^2 and cutoff n^3, uniformly over
heights at least n^2. Final9758 exit0 warning-free; all three public audits
in F132scratch36120 standard-only; wired/index-visible (line43). Lint46946
exit1: thirteen unrelated unreachable modules, no BAG/proof debt.


**C22.2 / F132 FINAL — original conditional free-window target law, LEAN PROVED.**
`SteinhausFrozenWindowLocalTarget.lean` proves prefix retention, the exact
finite-node frozen decomposition with literal retained background, and the
original conditional local-target probability bound. Final73721 exit0
warning-free; all three public axiom reports in audit58613 standard-only
(the separate auxiliary API witnesses in that scratch failed universe inference).
Wired/index-visible (line56). Lint47831 exit1: twelve unrelated unreachable
modules, no BAG/proof debt. Arithmetic bounds and retained-event integration
are still being assembled.


**C22.4 — conductor-uniform literal complement (paper candidate; NOT LEAN PROVED).**
The existing coupled deep edge Re(w)=d-4 fixes the chi numerator on Re(s+w)=-7/2.
Its sharp fourth-power height bound yields an explicit factor
`C(d)*x^(d-4)*(1+|tau|)^4*(n+1)^(-9/2)` for the literal deep coefficient.
The published local lemma hides x inside its constant; its proof exposes x
exactly and permits a new bound with the constant chosen before x.
Coefficient-by-coefficient contour identification and reflection give
`complement(d,tau,x,n) = -chi(right(d,tau))*deep(d,-tau,x,n)`.
For x=N and N<=tau<=2N, the chi factor is O(N^-d); hence
`N^-d*N^(d-4)*(1+tau)^4` is bounded uniformly in N. This supplies a summable
`C(d)*(n+1)^(-9/2)` envelope for the actual complement, preserving every term.
Consequently a fixed sufficiently long character prefix controls the entire
complement uniformly in this window, and full-primal targets can be translated
by its bounded centre and the actual pole term. No deterministic orbit count follows.

Current source lemmas for this deep edge assume 0<d<=1/4. Extending their
analytic/contour estimates to all 0<d<1/2, or explicitly restricting the resulting
theorem, is mandatory; that wider range is not supplied by the existing statement.
Needed Lean work: expose x before the constant, exact reflected coefficient
identity, conductor cancellation, all-phase summability/tail and prefix control,
and uniform pole bound. No new complement Lean leaf has been written yet.


**C22.4 / F138 FINAL — explicit complement smoothing scale, LEAN PROVED.**
`SmoothAFEReflectedComplementScale.lean` puts x^(d-4) outside the deep-coefficient
constant and proves the exact original complement = minus right chi times the
literal deep coefficient. Both statements retain 0<d<=1/4. Final60915 exit0
warning-free; both public audits in F139scratch20096 standard-only; wired/index10.
Lint35368 exit1: eleven unrelated unreachable modules, no BAG/proof debt.


**C22.4 / F139 FINAL — uniform literal complement envelope, LEAN PROVED.**
`SmoothAFEReflectedComplementBound.lean` proves `C*(n+1)^(-9/2)` for the actual
complementary coefficient, for every real smoothing N>=1 and N<=tau<=2N,
with one constant independent of N,tau. Restriction 0<d<=1/4 retained.
Final58244 exit0 warning-free; public audit F140scratch61083 standard-only;
wired/index10. Lint13464 exit1: eleven unrelated unreachable modules, no BAG debt.


**C22.4 / F140 FINAL — full reciprocal-phase complement and tail, LEAN PROVED.**
`SmoothAFEReflectedComplementTail.lean` proves absolute admission, a uniform
all-phase full-series bound, and a cutoff tail at most `C*L^(-7/2)/(7/2)`
throughout N>=1,N<=tau<=2N, for 0<d<=1/4. The reciprocal character is retained.
Final9884 exit0 warning-free; all three public audits in F141scratch50767
standard-only; wired/index48. Lint18052 exit1: thirteen unrelated unreachable
modules, no BAG/proof debt.


**C22.4a — full strict-strip complement extension (paper audit; Lean pending).**
The d<=1/4 restriction in the coupled deep-edge proof is not analytically
necessary. Source audit of the pointwise bound, integrability, horizontal
decay and coefficient identification finds only these upper-range uses:
`d-4 != 0`, `d-4 <= -1`, and `0 < 1/2-d`. They all hold for 0<d<1/2.
The shifted numerator stays exactly on Re=-7/2. Along the connecting rectangle
its real part stays in [-7/2,-1/2], so the existing polynomial chi majorant
and holomorphy argument remain applicable. Both horizontal edges retain
Gaussian decay, and the base parameter has real part 1/2-d in (0,1),
as required by the original -1-edge integrability theorem.
Thus the same coefficient-level contour proof and conductor cancellation
should supply C22.4 throughout 0<d<1/2. All broadened statements must compile
and pass axiom audits before changing the verified range of F138-F141.


**C22.4 / F141 FINAL — fixed-prefix full-complement stability, LEAN PROVED.**
`SmoothAFEReflectedComplementCharacterStability.lean` proves that one finite
character prefix and one positive tolerance control the whole reciprocal-phase
complement uniformly over N>=1,N<=tau<=2N, for 0<d<=1/4. Final74565 exit0
warning-free; public audit F142scratch78055 standard-only (that scratch's
separate pole proof then failed one redundant dsimp). Wired/index16.
Lint83875 exit1: twelve unrelated unreachable modules, no BAG/proof debt.

**C22.4 / F142 FINAL — actual reflected pole bound, LEAN PROVED.**
`SmoothAFEReflectedPoleBound.lean` keeps the literal shifted-pole correction
and bounds it uniformly for 0<d<1/2, N>=1 and tau>=N. The denominator
|1-s_left|>=tau cancels the smoothing growth after the actual chi factor.
Final6115 exit0 warning-free; public audit F133scratch5018 standard-only
(the independent F133 proof errors do not affect that report). Exact lexical
index1; lint88102 reports eleven unrelated unreachable modules, no BAG debt.
This supplies a bounded target translation, not a deterministic return count.

**C22.5 — complete reflected AFE finite-node target law (paper assembly; now FINAL below).**
Use the full primal law F137, keeping the original complement
with reciprocal character and the actual pole. For each fixed node j, F141
chooses a prefix B_j and tolerance delta_j making the complement oscillation
less than rho/(2*(J+1)); F140 and F142 bound its centre and pole uniformly.
Refine the requested prefix to max(P,B_j over j), and its tolerance to the
minimum of the requested tolerance and all delta_j. The centre is the same
rotated prescribed phase omega(-tau) used by F137. Apply F137 at radius rho/2
to the target t minus the complement at that centre plus the actual pole.
This translated target stays in one fixed bounded ball independently of
smoothing and tau. On the refined cell, the complement-error vector has norm
less than rho/2, by summing coordinate squares; the exact pole cancels.
Thus the original product measure of the full-AFE finite-node target event
has the same c*(n^2)^(-epsilon) lower bound for all sufficiently large n.
At the zero phase assignment, the literal full AFE equals zeta by
`riemannZeta_rightDisplaced_eq_reflectedPrimal_add_complement`; this identity
alone supplies no probability-to-orbit transfer. The verified complement
range is the full 0<d<1/2 after C22.4a. No deterministic count,
holomorphic boundary event, or RH consequence is claimed here.

**C22.2 / F133 FINAL — all-retained bounded centres, LEAN PROVED.**
`SmoothAFEReflectedWindowBoundedCentreEvent.lean` proves measurability and
retained-coordinate invariance of the actual background event, its original
Markov cost, uniform summed first-mean decay for every polynomial cutoff and
retained prime set, and half-mass retention for any fixed-mass event.
Final3524 exit0 warning-free; all five public audits F134scratch91589
standard-only; exact lexical index7; lint78882 eleven unrelated unreachable
modules, no BAG proof debt. This closes the retained-background selection
step at independent cutoff; the complete target/count assembly remains open.

**C22.2 / F134 FINAL — retained covariance-and-centre event, LEAN PROVED.**
`SmoothAFEReflectedWindowCovarianceCentreEvent.lean` constructs one measurable
retained-coordinate event of fixed positive original mass, inside any
prescribed refinement of the rotated character cell. It simultaneously bounds
all literal retained centres and supplies the actual H/log(N) Gram floor,
uniformly for every L>=N*D with L>=N and common height in [5N/4,7N/4].
Final83451 exit0 warning-free after rebuilding one existing cache dependency;
public audit F135scratch27878 standard-only. Exact index1; lint47136 eleven
unrelated unreachable modules, no BAG proof debt. No vertical count inferred.

**C22 transfer obligation — moving actual coefficients and the physical phase.**
The finite-node random law is pointwise in common height: for each tau in the
conductor window, the original product measure of E(N,tau) is bounded below.
The arithmetic producer instead needs a lower bound for the height set
{tau : zeroPhase belongs to E(N,tau)}, followed by boundary zero transfer and
distinct-zero counting. Integrating the product-law lower bound over tau
only controls an average over phase assignments; it does not select the
physical zero phase. Moreover, E(N,tau) includes the actual varying chi and
complement coefficients, so fixed-target torus equidistribution cannot be
applied without deriving the precise transport and quantitative error.
F133-F145 and the C22.4a range extension are ingredients for this obligation,
not its discharge. Fixed-smoothing long-time limits do not preserve the
conductor-sized scaling used in their covariance and complement estimates.

**C22.2 / F135 FINAL — independent-cutoff conditional target cost, LEAN PROVED.**
`SmoothAFEReflectedWindowConditionalLocalTarget.lean` proves the actual frozen
carrier target probability is at least (1/4)*N^(-2*J*B^2/H), for every compatible
independent cutoff L, whenever its actual retained-shifted target has norm<=B
and its actual Gram matrix has floor H/log(N). The small-bias and variance
conditions follow from the unconditional column and energy estimates.
Final57349 exit0 with no errors/warnings (one informational ring suggestion);
public audit F136scratch78538 standard-only. Exact index1; lint63493 twelve
unrelated unreachable modules, no BAG proof debt. This is conditional on the
explicit Gram event already constructed by F134, not an assumed producer.

**C22.2 / F136 FINAL — original independent-cutoff target law, LEAN PROVED.**
`SmoothAFEReflectedWindowLocalTargetEvent.lean` integrates the actual
conditional law over the fixed-mass retained event. Every prescribed finite
character cell supports every bounded finite-node target with original
probability >=c*N^(-epsilon), for any fixed epsilon>0, uniformly over common
heights and all compatible independent cutoffs L>=N*D, N<=L<floor(N/(2K))^2.
Final51511 exit0 warning-free; both public audits F137scratch61827
standard-only (that scratch has an independent final set-membership
normalization error). Exact index2; lint7431 thirteen unrelated unreachable
modules, no BAG proof debt. Full-series and deterministic-count steps remain.

**C22.2 / F137 FINAL — literal full-primal target law, LEAN PROVED.**
`SmoothAFEFullReflectedLocalTarget.lean` combines the uniform all-phase cubic
tail at square smoothing with the independent-cutoff original target law.
For every prescribed finite character cell, every bounded finite-node target
and every epsilon>0, its full reflected-primal target event has original
probability >=c*(n^2)^(-epsilon), uniformly over tau in [5*n^2/4,7*n^2/4]
for all sufficiently large n. No subtraction of a tail exceptional event
is used. Final60504 exit0 warning-free; both public audits F143scratch62120
standard-only; exact index3; lint41466 twelve unrelated unreachable modules,
no BAG debt. C22.2 is closed for the full random primal. The complete AFE,
holomorphic boundary target, and deterministic physical-height count remain open.

**C22.3a — compact Gaussian kernel holomorphy (paper step; Lean pending).**
On a plane compact K, write Q(w)=coord_K+w*1 in C(K,C). Off -K, the existing
compact resolvent inverse gives Q(w)^(-1)=-resolventInv(K,-w). Therefore
exp(Q(w)^2)*(-resolventInv(K,-w)) evaluates exactly to exp((z+w)^2)/(z+w).
Banach-algebra exponential is entire; the existing resolvent derivative and
composition/product rules make this C(K,C)-valued map holomorphic off -K.
Every continuous complex functional composed with it is holomorphic there.
This verifies the analytic-transform input of C22.3 once formalized; identity
continuation, weighted Cauchy reproduction, and annihilator separation still
remain. Reuse compact-resolvent infrastructure, with no heartbeat increases.

**C22.4a / F143 and F138-F141 FULL-STRIP FINAL — LEAN PROVED.**
`SmoothAFEReflectedDeepFullStrip.lean` proves the deep-line norm bound,
absolute integrability, horizontal contour decay, and exact identification
with the original reflected coefficient throughout 0<d<1/2. Final88365 exit0
warning-free; index4; lint94476 twelve unrelated unreachable modules.
The four dependent complement leaves now use that exact wider range:
explicit smoothing scale (final76251), conductor coefficient envelope
(final47389), full reciprocal-phase series and tail (final66505), and fixed
character-prefix stability (final71233). Every final build exited0 without
warnings. The combined lexical index has9 declarations; lint11731 reports
twelve unrelated unreachable modules, no BAG debt. All eleven public axiom
reports in F144scratch82466 use only propext/Classical.choice/Quot.sound;
that scratch's separate vector-expression type-inference error does not
affect these imported reports. This supersedes the earlier quarter-strip
restriction. Complete-AFE finite-node assembly and the boundary/count gates
remain open.

**C22.3b — exterior continuation geometry (paper step; Lean pending).**
For r>=0, the exterior of closedBall(c,r) is the continuous image of C\{0}
under z |-> c+(1+r/|z|)*z. For a point w in the exterior, its preimage is
(1-r/|w-c|)*(w-c), with norm |w-c|-r>0. Thus the exterior is path connected.
An analytic scalar transform vanishing at every it has zeros at i/(n+1)
approaching0 through nonzero points; if0 belongs to its connected domain,
the identity theorem kills it on that domain. For the reflected right-half-
plane disc,0 lies outside it. This supplies the continuation part of C22.3
once formalized. Weighted Cauchy reproduction and annihilator separation
still remain; no full Gaussian density theorem is claimed by these steps.

**C22.5 / F144 FINAL — exact complete AFE and bounded correction, LEAN PROVED.**
`SmoothAFEFullReflectedAFE.lean` defines the literal full reflected carrier
with its reciprocal-phase complement and unchanged pole. At zero phase it
is exactly zeta, node by node. The whole finite-node complementary correction
has a conductor-uniform norm bound and fixed finite-character tolerance,
throughout 0<d_j<1/2. Final88884 exit0 warning-free; all four public audits
F145scratch58809 standard-only. Exact index8; lint86770 ten unrelated
unreachable modules, no BAG proof debt. Its target-event assembly is F145;
physical-phase equality alone is not an orbit count.

**C22.3c — annihilator continuation outside the reflected disc (paper assembly).**
For K=closedBall(c,r), r>=0 and r<Re(c), its reflected complement is exactly
the exterior of closedBall(-c,r). The origin belongs to this exterior since
r<Re(c)<=|c|. Combining C22.3a and C22.3b, any continuous complex functional
annihilating all imaginary translates of the Gaussian Cauchy kernel has zero
transform everywhere outside -K. This is the precise input for the weighted
Cauchy reproduction argument, not yet the full density or recurrence result.

**C22.3a / F146 FINAL — compact Gaussian kernel holomorphy, LEAN PROVED.**
`SmoothAFECompactGaussianKernel.lean` identifies the exact translated Gaussian
Cauchy kernel in C(K,C), proves its Banach-valued differentiability off -K,
and proves analyticity of every continuous functional transform. Final89700
exit0 warning-free; all three public audits F147scratch26928 standard-only.
The latter's separate rank/sequence errors do not affect those reports.
Exact index5; lint73747 thirteen unrelated unreachable modules, no BAG debt.
Exterior continuation, Cauchy reproduction and full mode density remain open.

**C22.3b / F147 FINAL — exterior geometry and analytic uniqueness, LEAN PROVED.**
`SmoothAFECompactGaussianExterior.lean` proves path connectedness of every
closed-disc exterior with nonnegative radius, and the imaginary-axis identity
principle on a connected domain containing zero. Final60365 exit0 warning-free;
both public audits F148scratch90507 standard-only. That scratch's separate
not_le projection error does not affect these reports. Exact index2;
lint65056 thirteen unrelated unreachable modules, no BAG proof debt.

**C22.3c / F148 FINAL — Gaussian annihilator exterior continuation, LEAN PROVED.**
`SmoothAFECompactGaussianAnnihilator.lean` proves the transform vanishes
everywhere outside the reflected right-half-plane disc when it annihilates
the imaginary Gaussian modes. Final38137 exit0 warning-free; public audit
F149scratch85072 standard-only; exact index1; lint82712 twelve unrelated
unreachable modules, no BAG proof debt. Cauchy reproduction remains next.

**C22.3d / F149 FINAL — Gaussian Cauchy reproduction, LEAN PROVED.**
`SmoothAFECompactGaussianCauchy.lean` proves exact scalar reproduction of
holomorphic values by the Gaussian Cauchy contour and commutation of compact-
carrier contour integration with any continuous complex functional.
Final57261 exit0 warning-free; both public audits F150scratch77062 standard-only
(that scratch's separate zero-integral simplification error does not affect
them). Exact index2; lint8363 twelve unrelated unreachable modules, no BAG debt.

**C22.3d / F150 FINAL — holomorphic target annihilation, LEAN PROVED.**
`SmoothAFECompactGaussianHolomorphicAnnihilator.lean` proves that every
continuous complex functional annihilating the imaginary Gaussian modes
annihilates the restriction of every function holomorphic on a larger disc.
It constructs the continuous C(K)-valued contour, checks evaluation against
the exact scalar reproduction, and cancels the nonzero 2*pi*i factor.
Final6950 exit0 warning-free; public audit F151scratch29100 standard-only
(separate complexification/coercion errors in that scratch do not affect it).
Exact index1; lint91139 twelve unrelated unreachable modules, no BAG debt.

**C22.3e / F151 FINAL — finite linear Gaussian mode approximation, LEAN PROVED.**
`SmoothAFECompactGaussianDensity.lean` puts every target holomorphic on a
larger disc in the closed complex linear span of imaginary Gaussian Cauchy
modes on the smaller right-half-plane disc. Its second theorem supplies
explicit finitely supported complex coefficients with arbitrary positive
supremum-norm accuracy. This closes the larger-disc form of C22.3 without
substituting a generated algebra. Final36112 exit0 warning-free; both public
audits F152scratch90732 standard-only; exact index2; lint17461 eleven unrelated
unreachable modules, no BAG proof debt. Compact-uniform actual cofactor
convergence, the random holomorphic target event, and deterministic counts
remain open.

**C22.5 / F145 FINAL — complete reflected-AFE finite-node target law, LEAN PROVED.**
`SmoothAFEFullReflectedAFELocalTarget.lean` proves that the literal full AFE
hits every bounded finite-node target in every prescribed finite phase cell
with original probability at least c*(n^2)^(-epsilon), for each epsilon>0,
uniformly across the conductor window and full strict strip 0<d_j<1/2.
The exact reciprocal complement and pole remain in the carrier. Final6325
exit0 warning-free; public audit F146scratch49838 standard-only. The latter
scratch's unrelated missing constant argument in its kernel proof does not
affect this imported report. Exact index1; lint81066 eleven unrelated
unreachable modules, no BAG proof debt. C22.5 is closed at finite nodes;
holomorphic boundary control and physical common-height counting remain open.

**C22.3d — weighted Gaussian Cauchy reproduction (paper step).**
For z in closedBall(c,r), choose R>r on whose closed disc f is holomorphic.
The function w |-> f(-w)*exp((z+w)^2) is holomorphic on closedBall(-c,R).
Its value at the interior point -z is f(z), so Cauchy's formula yields
the exact integral of f(-w)*exp((z+w)^2)/(z+w) as 2*pi*i*f(z).
The corresponding C(K)-valued contour integral exists by continuity on the
outer circle; evaluation and any continuous complex functional commute with
it via their interval-integral commutation theorem. Thus an annihilating
functional vanishes on f restricted to K. Formalization pending.

**C22.3e — closed complex span separation (paper step).**
If the restriction g of f is outside the closed complex Gaussian mode span,
real Hahn-Banach separation supplies a continuous real functional l vanishing
on that closed subspace and nonzero at g. Its complexification is
L(x)=l(x)-i*l(i*x). Because the subspace is complex-linear, both terms vanish
on every mode, whereas Re(L(g))=l(g) is nonzero. C22.3d forces L(g)=0,
a contradiction. Membership in the closed span gives arbitrarily small
supremum-norm error from finite complex mode sums. No generated algebra or
closure under products is substituted for the required linear span.

**C22.6 — compact-uniform actual cofactor modes (paper programme).**
First establish that the literal full Gaussian cofactor is entire in s for
every positive fixed scale R and every phase. On Re(s)<b, each summand's
norm is dominated by its norm at the real abscissa b, since n>=1. Existing
Gaussian absolute summability at b supplies the local uniform majorant.
The normalized function F_R(s)=cofactor(s,R)*R^(-(s+i*t)) is then entire.

For 0<a<=Re(s)<=b<1, its norm is bounded by the sum of the positive real
normalized cofactors at a and b: termwise use q^Re(s)<=q^a+q^b with q=n/R.
The two endpoint sums have finite limits by the existing scalar mean theorem
at the untwisted zero character, hence give an eventual uniform bound in s.
The existing pointwise coherent-twist limit is the Gaussian mode. A compact
Cauchy/dominated-convergence or existing Vitali argument should upgrade it
to uniform convergence on smaller discs. Holomorphy F152, endpoint-majorant
F154 and the actual compact-uniform limit F155 are now FINAL. Whole-disc
mode packets and their quantitative holomorphic target law remain next.

Source audit: deep search50012 returned partial results (inventory63647
complete, compiler metadata largely pending/stale, semantics unmeasured).
All20 candidate lemmas,20 source arguments,one proof idea andone ingredient
set inspected. They supply actual cofactor summability/tails and scalar
means, not this compact-uniform conclusion. Existing VitaliConvergence
supplies a sequence normal-family theorem once actual bounds are discharged.

**C22.6 / F152 FINAL — actual full-cofactor holomorphy, LEAN PROVED.**
`SteinhausFullGaussianHolomorphy.lean` proves the literal infinite Gaussian
cofactor is entire in s for every positive fixed scale and every phase,
including the actual coherent normalization by R^(-(s+i*t)). The summable
majorant is an actual real-abscissa coefficient sequence. Final96414 exit0
warning-free; all three public audits F153scratch4457 standard-only (its
separate cast/limit projection errors do not affect these reports).
Exact index3; lint15695 ten unrelated unreachable modules, no BAG proof debt.

**C22.6a — actual real-scale compact convergence (paper assembly).**
Choose a larger disc strictly inside 0<Re(s)<1. The two-endpoint envelope
is uniform on this whole disc for all scales above one threshold R0.
For any real scale sequence tending to infinity, replace finitely many
small scales by max(R_n,R0). The resulting holomorphic family is bounded
on the disc and has the actual coherent Gaussian mode as its pointwise
limit there. Existing Vitali identification gives locally uniform convergence,
hence uniform convergence on the smaller closed disc. The sequential
criterion for uniform convergence over the countably generated real atTop
filter gives the full real-scale limit; no integer-only limit is substituted.
This assembly remains pending the exact envelope and Lean API checks.

**C22.6 / F153 FINAL — actual positive coefficient mass, LEAN PROVED.**
`SteinhausFullGaussianAbsoluteMass.lean` defines the normalized absolute
coefficient mass, proves summability of its exact positive terms, identifies
it with the real zero-phase cofactor, proves its finite scalar limit for
0<sigma<1, and bounds every normalized phase/twist by that mass.
Final63402 exit0 warning-free; all four public audits F154scratch51282
standard-only (its separate cast-rewrite ordering error does not affect them).
Exact index7; lint74376 eleven unrelated unreachable modules, no BAG debt.

**C22.6 / F154 FINAL — uniform endpoint envelope, LEAN PROVED.**
`SteinhausFullGaussianEndpointEnvelope.lean` proves the exact positive-mass
interpolation inequality and one eventual bound for the literal normalized
cofactor throughout any closed abscissa band inside (0,1), uniformly over all
imaginary parts, phases and coherent twists. Final53431 exit0 warning-free;
both public audits F155scratch73659 standard-only (separate filter-elaboration
errors in that scratch do not affect these reports). Exact index4;
lint95650 ten unrelated unreachable modules, no BAG proof debt.

**C22.6b — full-cofactor stability across an abscissa half-plane (paper step).**
The existing actual Gaussian tail bound has one constant for all Re(s)<A.
Fix b and A=|b|+2. For Re(s)<=b and L>=1, compare L^(Re(s)-A) to L^(b-A)
and A-Re(s) to A-b. For 0<R<=U this gives the common tail bound
C*U^A*L^(b-A)/(A-b), tending to zero as L grows. Thus one cutoff works for
all spectral points in that half-plane and all phases. The finite head is
uniformly continuous in its characters because each coefficient norm is
bounded by its value at b and the cutoff norm is at most1. Two small tails
plus this finite head give one character tolerance for the entire half-plane
and every positive scale below U. This preserves a whole-disc mode packet,
not merely a finite node list. Formalization pending.

**C22.6a / F155 FINAL — actual compact-uniform coherent mean, LEAN PROVED.**
`SteinhausFullGaussianCompactMean.lean` proves the exact coherent Gaussian
cofactor mean converges uniformly on every smaller closed disc inside the
open unit strip, along the full real smoothing-scale filter. The finite
prescribed prefix and its actual scalar remain unchanged. Final60001 exit0
warning-free; public audit F156scratch93190 standard-only, including the
existing Vitali dependency; exact index1; lint17447 twelve unrelated
unreachable modules, no BAG debt. This closes C22.6a. Whole-disc mode packets
and the random holomorphic target event still remain before physical counts.

**C22.6c — normalized compact mode blocks (paper assembly).**
Divide the exact compact coherent limit by its nonzero finite-prefix mean A.
This yields exp((s+i*t)^2)/(s+i*t) uniformly on the disc. The convergence
threshold can be enlarged so M>=B and M*|A|^2>=K for any prescribed budget K.
For 1<=R<=U and Re(s)>=0, the norm of R^(-(s+i*t)) is R^(-Re(s))<=1.
Thus the uniform character tolerance from C22.6b, tightened by |A^-1|+1,
preserves the normalized mode on the entire disc. These are the exact
single-block inputs for the existing separated-block induction, now with
supremum-norm accuracy. Formalization pending.

**C22.6b / F156 FINAL — whole-half-plane cofactor stability, LEAN PROVED.**
`SteinhausFullGaussianCompactStability.lean` proves one cutoff controls the
actual full Gaussian tails throughout Re(s)<=b, at every bounded positive
scale and in every phase. One finite-character tolerance then preserves the
full cofactor over that whole half-plane and scale range. Final7973 exit0
warning-free; both public audits F157scratch60205 standard-only (its separate
associativity-rewrite error does not affect them). Exact index2;
lint89011 ten unrelated unreachable modules, no BAG proof debt.

**C22.6d — simultaneous whole-disc mode packets (paper assembly).**
Repeat the existing finite-node separated-block induction with whole-disc
error bounds. At each step use half the remaining tolerance for old blocks
and half for the new mode. Freeze every old block's finite character prefix
before choosing the next coherent extension; exact phase agreement gives
exact character agreement via the existing prime-factor congruence theorem.
Choose the new lower scale beyond twice every prior scale, retaining every
mean-weighted budget. The induction preserves the original prescribed prefix
and realizes the entire finite mode list uniformly on the disc. Lean pending.

**C22.6c / F157 FINAL — normalized compact mode blocks, LEAN PROVED.**
`SteinhausFullGaussianCompactModes.lean` defines the exact scalar normalized
response, proves whole-disc convergence to its Gaussian mode, constructs a
prefix-preserving block with any minimum scale and mean-weighted length
budget, and gives a finite-character tolerance preserving that normalized
response across its entire bounded scale interval and abscissa band.
Final84241 exit0 warning-free; all three public audits F158scratch5466
standard-only; exact index5; lint80535 ten unrelated unreachable modules,
no BAG proof debt. The simultaneous packet/cell and target-event assembly
remain separate steps.

**C22.6e — one finite character cell for all compact mode blocks (paper assembly).**
Construct the separated packet with half the target error. Each block has a
whole-disc normalized character tolerance on its bounded scale interval.
Take the minimum of the finitely many positive tolerances and one prefix
containing every individual prefix, all 2*M_i and the prescribed lower bound.
Every phase in that same cell then approximates every mode on its entire
scale block and whole disc, by the triangle inequality. The original
prescribed phase coordinates and every mean-weighted budget remain intact.
The existing finite-character cell theorem gives positive original mass;
this does not yet construct a tilted holomorphic target event or height count.


**C22.6d / F158 FINAL — simultaneous compact-disc mode packets, LEAN PROVED.**
`SteinhausFullGaussianCompactPackets.lean` proves exact-prefix stability and
constructs one phase assignment realizing any finite list of Gaussian modes
on separated scale blocks, uniformly on the whole disc, preserving the
original prefix and arbitrary mean-weighted budgets. Final59786 exit0 clean;
both public audits F159scratch56920 standard-only. Its separate Icc ambiguity
was in the uncompiled successor. Exact index2; lint66638 eleven unrelated
unreachable modules, no BAG proof debt. Common-cell and target-event assembly
remain separate obligations.


**C22.6f — compact-uniform literal truncation (paper assembly).**
For nonzero scalar A and 1<=R<=U, 0<=Re(s)<=b, the coherent normalizer
R^(-(s+it)) has norm at most one. Apply F156's whole-half-plane tail with
absolute error epsilon*|A|; division by A then gives normalized error less
than epsilon, uniformly in every phase and every cutoff above one fixed C.
Apply F159 with half the final tolerance and choose one such C for each of
the finitely many mode blocks. The sum of those cutoffs works for every
block, every phase in the same character cell, every point on the disc and
every later cutoff. Triangle inequality transfers the Gaussian mode packet
to the literal truncated cofactors. This establishes a coefficient-faithful
compact approximation step, not yet a probability or physical-height count.

**C22.7 — direct compact Gaussian synthesis (paper candidate, obligations explicit).**
Write the literal prime channel at s+i*tau, R=N/p, as the common row
lambda(s)=sqrt(N)*chi(s+i*tau)*N^(s-1) times
alpha_p=(R/sqrt(N))*A*R^(it)*p^(i*tau) times the normalized truncated
cofactor mode. This is an exact identity, with |alpha_p|=R*|A|/sqrt(N).
For p in a reciprocal block, M<=R<2M and the proved prime count gives
E=sum_p|alpha_p|^2 >= M*|A|^2/(4*log N). The scalar bias
mu_p=gamma*conj(alpha_p)/E satisfies sum_p mu_p*alpha_p=gamma and
sum_p|mu_p|^2=|gamma|^2/E. Moreover mu_p*alpha_p is gamma times a positive
partition of unity. A whole-disc mode error eta therefore contributes at
most |gamma|*eta, with no inverse-frame loss. The maximal bias tends to zero
for fixed blocks, since |alpha_p|<=2M*|A|/sqrt(N) and E has the preceding
lower bound. Disjoint reciprocal blocks synthesize a finite Gaussian linear
combination with total cost at most sum_i 4|gamma_i|^2*log N/(M_i|A_i|^2).
Arbitrary mean-weighted budgets make this coefficient of log N arbitrarily
small. These algebraic and prime-block estimates still need Lean assembly.

Remaining analytic obligations are uniform holomorphic control of the row
lambda and its inverse, bounded-centre selection and tilted variance on a
larger disc, and a finite mode catalogue for the normalized varying target
family chosen before the phase cell. None follows from finite-node target
laws alone. Even a completed random holomorphic target probability law would
leave the deterministic common-height quantitative return count open.


**C22.6e / F159 FINAL — one common compact mode cell, LEAN PROVED.**
`SteinhausFullGaussianCompactModeCells.lean` constructs one finite character
cell preserving all prescribed modes on their separated scale blocks and
throughout the closed disc, retaining original phase coordinates and every
mean-weighted budget. Final11287 exit0 warning-free; public audit
F160scratch27518 standard-only; exact index1; lint84044 ten unrelated
unreachable modules, no BAG debt. This closes the common-cell step.

**C22.8 — normalize before compact fluctuation control (paper candidate).**
The exact C22.7 row factor should also remove chi from the random fluctuation
estimate. A normalized literal channel is (R/sqrt(N))*R^(-s) times its
truncated cofactor, up to a unit prime phase. On the whole free window
N/(2K)<p<=N, one has 1<=R<2K. F156's half-plane tail and a fixed finite
head give a bound for every literal cofactor truncation, uniformly in phase,
cutoff, R<=2K and Re(s)<=b; the head is bounded by the positive real-b
coefficients because the Gaussian cutoff has norm at most one. The coherent
normalizer has norm at most one when Re(s)>=0. Thus every normalized column
is O(N^(-1/2)) uniformly on the disc and its larger boundary. The prime-count
upper bound gives total pointwise variance O(1/log N). A Cauchy boundary
inequality should then turn this into a compact supremum fluctuation bound
under the actual finite affine tilted law. This still needs an explicit
measurable envelope and integral interchange; no uncountable supremum or
uniform-in-s estimate is being assumed from the finite-node law.


**C22.6f / F160 FINAL — literal compact truncated mode packets, LEAN PROVED.**
`SteinhausFullGaussianCompactTruncation.lean` defines the exact scalar
truncated normalization, proves a cutoff-uniform normalized tail across the
whole abscissa band, and transfers every compact mode packet to literal
finite cofactors in the same character cell. Final35529 exit0 warning-free;
both public audits F161scratch81040 standard-only; exact index3; lint25501
ten unrelated unreachable modules, no BAG debt. This closes C22.6f.

**C22.8 refinement — reuse the proved planar mean-square envelope.**
The public `norm_sq_value_mul_area_le_integral_ball_local` supplies the
analytic inequality already. For z in closedBall(c,r), choose a fixed small
radius a>0 with r+a<rho. Then ball(z,a) lies in ball(c,rho). The local
inequality and monotonicity of the nonnegative planar lintegral give
|F(z)|^2 <= (pi*a^2)^(-1) integral_ball(c,rho) |F(w)|^2, simultaneously for
all z. `SteinhausEulerSpatialEnvelope` already demonstrates the measurable
lintegral and Tonelli mechanism. Reuse it for the finite affine centered
holomorphic channel sum; the remaining new estimates concern the actual
normalized channels and the selected target, not the analytic mean-square law.

**C22.9 — choose the target catalogue before the coherent phase cell.**
To avoid circular dependence of the mode catalogue on its eventual phase
centre, first choose a finite character prefix controlling the complete AFE
correction near the originally prescribed reference phase. Preserve this
prefix exactly in every coherent extension. Approximate the normalized
reference targets lambda^(-1)*(f-referenceCorrection) by a finite Gaussian
catalogue on the inner disc, using a uniform holomorphic bound on a larger
disc. Only then choose packet tolerances and mean-weighted budgets from the
finite catalogue coefficients and construct the mode cell. Its radius is
also bounded by the earlier correction tolerance. The fixed reference
correction, rather than the subsequently constructed phase centre, breaks
the circularity. Still OPEN: compact-uniform complete-correction stability,
holomorphy and bounds for the reference correction and lambda inverse, and
the finite-catalogue compactness argument. This is an assembly candidate,
not an assumed producer or a proved probability law.


**C22.7a / F161 FINAL — exact compact-channel factorization, LEAN PROVED.**
`SmoothAFEReflectedCompactChannel.lean` identifies the scalar and node-vector
normalizations, defines the common spectral row and literal prime amplitude,
proves its exact phase-independent norm R*|A|/sqrt(N), and factors the actual
reflected-primal coefficient channel into that row, amplitude and truncated
compact mode. Final21122 exit0 warning-free; all three public audits
F162scratch54758 standard-only; exact index5; lint8959 ten unrelated
unreachable modules, no BAG debt. Both coherent prime phases and the exact
floor cofactor cutoff are retained.


**C22.7b / F162 FINAL — actual prime-block amplitude energy, LEAN PROVED.**
`CompactGaussianPrimeBlockEnergy.lean` gives both endpoint bounds for each
literal prime amplitude and the eventual energy floor
M*|A|^2/(4*log N), uniformly in both coherent frequencies and the scalar A.
Final84188 exit0 warning-free; both public audits F163scratch40443
standard-only (successor algebra normalization errors were separate).
Exact index3; lint90205 ten unrelated unreachable modules, no BAG debt.


**C22.7c / F163 FINAL — exact scalar synthesis with uniform error control, LEAN PROVED.**
`SteinhausScalarAmplitudeSynthesis.lean` reuses the corpus's exact conjugate
port minimizer. Its finite supported biases synthesize gamma, have squared
cost |gamma|^2/sum|alpha|^2 and the exact individual norm formula, and transfer
any uniform mode error epsilon to at most |gamma|*epsilon. This last estimate
uses unit absolute contribution mass. Final89508 exit0 warning-free; public
audit F164scratch76211 standard-only; both reused port audits were also
standard-only. Exact index1; lint82045 ten unrelated unreachable modules,
no BAG debt. This is an algebraic synthesis theorem, not a recurrence premise.

**C22.9 phase-coordinate clarification.**
The prescribed reference is fixed in cofactor coordinates. At physical
height tau its original-law phase is xi_tau=steinhausLogPhaseShift(omega,-tau),
exactly as in the proved finite-node complete-AFE theorem F145. Thus the
reference correction in the target catalogue is evaluated at xi_tau, not at
one unrotated original-law phase for every height. Character-distance
rotation preserves the fixed prefix tolerance. The catalogue may vary through
this bounded reference target family before choosing its finite approximation
list; the final coherent extension preserves omega's controlling prefix.
This clarification retains the original product law and does not assert
that the zero-phase physical orbit enters those moving events.


**C22.7d / F164 FINAL — actual prime-block bias budgets, LEAN PROVED.**
`CompactGaussianPrimeBlockBiases.lean` combines actual prime-block energy
with the exact minimizer. For every fixed block, nonzero mean scalar A,
mode coefficient gamma and positive individual tolerance, all sufficiently
large N admit supported biases at every pair of coherent frequencies. Their
squared cost is at most 4*|gamma|^2*log(N)/(M*|A|^2), every bias is smaller
than the requested tolerance, and uniform mode error is multiplied by only
|gamma|. Final97765 exit0 warning-free; public audit F165scratch35253
standard-only; exact index1; lint98379 ten unrelated unreachable modules,
no BAG debt. Compact event and deterministic return-count assembly remain open.


**C22.8a / F165 FINAL — one literal normalized holomorphic channel, LEAN PROVED.**
`CompactGaussianNormalizedChannel.lean` defines the channel independently of
any chosen Gaussian mode. It proves exact agreement with every coherent
mode representation and the actual reflected-primal common-row factorization,
entire dependence on the spectral variable for every finite cofactor and
normalized channel, and the exact phase-independent norm formula.
Final87367 exit0 warning-free; all five public audits emitted by F166scratch91374
standard-only; exact index6; lint86573 ten unrelated unreachable modules,
no BAG debt. Bounds for the removed row and its inverse remain separate.

**C22.8b — compact tilted fluctuation event (paper assembly).**
For entire finite columns a_i and actual affine-circle means |m_i|<=1/2,
the centered sum is entire and jointly measurable. Its pointwise second
moment is at most sum_i|a_i(z)|^2 by the proved finite affine variance law.
Choose delta=epsilon^2*(rho-r)^2/(2*rho^2), rho>0 and r<rho. If the actual
outer-disc column energy is at most delta, the planar envelope has expectation
at most epsilon^2/2. Its measurable sublevel event below epsilon^2 therefore
has at least half the tilted probability and controls the centered sum by
epsilon at every point of the inner closed disc. Existing affine-density
transfer gives original finite-phase mass at least (1/4)*exp(-2*sum|m_i|^2).
The proposed whole-band C/log(N) bound will discharge this energy threshold
for actual normalized channels. This is the compact fluctuation component;
it does not yet assemble the retained centre, reference correction or target.

**C22.8c — discharge compact fluctuation energy for literal windows (paper assembly).**
Apply the compact affine threshold to the actual normalized columns indexed
by any injective finite enumeration of primes in largePrimes N (N/D).
Their entire dependence is F165. The sum of their squared norms is bounded
by the complete window energy, uniformly in height, polynomial cutoff and
retained phase. On a larger disc contained in Re(s)>=0, the proposed F167
whole-band C/log(N) estimate is eventually below the fixed threshold delta.
Thus every admissible family of half-unit biases obtains a measurable
whole-inner-disc fluctuation event with the same half tilted mass and exact
original finite-phase density cost. This assembly has no growing-dimension
loss. Lifting to the retained infinite product event still requires the
actual compact target event's measurability, rather than selecting arbitrary
conditional witness sets as a measurable family.


**C22.8a / F166 FINAL — compact-uniform column bound, LEAN PROVED.**
`CompactGaussianNormalizedChannelUpper.lean` bounds every literal cofactor
truncation uniformly over Re(s)<=b, all phases and bounded positive scales.
It then bounds the literal normalized column by C/sqrt(N) uniformly over
the nonnegative abscissa band, every cutoff and retained phase, every common
height and every scale 1<=R<=U. Final32764 exit0 warning-free; both public
audits F167scratch9952 standard-only; exact index2; lint8251 ten unrelated
unreachable modules, no BAG debt. No chi-factor bound is assumed here.


**C22.8a / F167 FINAL — whole-band literal normalized window energy, LEAN PROVED.**
`CompactGaussianNormalizedChannelEnergy.lean` proves total squared column
energy at most C/log(N) on the complete actual free-prime window, uniformly
over the entire nonnegative abscissa band, imaginary part, common height,
retained phase and independent polynomial cutoff. Final4793 exit0 warning-free;
public audit F168scratch76186 standard-only; exact index1; lint93614 eleven
unrelated unreachable modules, no BAG debt. The analytic local mean-square
dependency audit in the same scratch run was also standard-only.

**C22.10 — assemble the fixed finite mode list with harmless finite-k cost (paper candidate).**
For a fixed list of k Gaussian modes and coefficients gamma_i, choose packet
mode tolerance below targetError/(2*(1+sum|gamma_i|)). F164 supplies block
biases mu_i with the correct scalar coefficient and error at most
|gamma_i| times that tolerance. Extend each by zero and set mu=sum_i mu_i
on the full free window containing every block. Linearity and finite sum
interchange give the required mean approximation uniformly on the disc,
all later cofactor cutoffs and all retained phases in the common cell.

Using triangle and finite Cauchy–Schwarz costs a fixed factor k in squared
bias energy: sum_p|sum_i mu_i(p)|^2 <= k*sum_i sum_p|mu_i(p)|^2. Arbitrary
mean-weighted block budgets absorb this factor, so no optimal disjoint-support
gluing theorem is needed for an arbitrarily small logarithmic probability
cost. Choose each individual tolerance below 1/(2*(k+1)) to keep every
combined bias below 1/2. The blocks are already disjoint, but that sharper
fact is unnecessary for these bounds. The number k is fixed before N grows;
no factor proportional to the number of free primes is introduced.

The resulting mean theorem should quantify the biases before the retained
phase and cutoff: for each sufficiently large N and common height tau,
one finite supported bias family works for every retained phase in the cell,
every sufficiently long literal cutoff, and every point of the compact disc.
This is the next synthesis assembly after the compact fluctuation component.


**C22.8b / F168 FINAL — measurable planar compact envelope, LEAN PROVED.**
`CompactDiscMeanSqEnvelope.lean` constructs a measurable outer-disc
mean-square envelope, bounds every inner-disc value of every entire sample,
and transfers pointwise second-moment bounds to its expectation by Tonelli.
Final33042 exit0 warning-free; all three public audits F169scratch52270
standard-only; exact index5; lint13580 ten unrelated unreachable modules,
no BAG debt. No uncountable supremum measurability premise is required.


**C22.8b / F169 FINAL — whole-disc tilted fluctuation event, LEAN PROVED.**
`SteinhausCompactAffineFluctuation.lean` proves the explicit outer-disc
energy threshold gives one measurable event controlling the centered affine
sum everywhere on the inner closed disc, with at least half the tilted mass
and original mass at least one quarter times exp(-2*sum squared biases).
Final24731 exit0 warning-free; public audit F170scratch31919 standard-only;
exact index1; lint39225 ten unrelated unreachable modules, no BAG debt.


**C22.11 — canonical compact target event avoids conditional selection (paper candidate).**
For fixed N, cutoff, height and target f, define the joint event in retained
phase eta and free phase xi by the literal normalized window sum having
error at most epsilon at every s in the closed disc. At each fixed s this
sum is continuous in (eta,xi): it is a finite sum of continuous characters
and finite Gaussian cofactors. The canonical event is therefore an arbitrary
intersection of closed sets, hence closed and measurable; no measurable
selection of fluctuation witness sets is needed.

Use synthesis and fluctuation at epsilon/2 each. Every witness fluctuation
event lies inside the corresponding section of this one canonical closed
event, by the exact centered-plus-mean identity and triangle inequality.
Its section mass is at least (1/4)*exp(-2*kappa*log(N)), uniformly for every
retained phase in the chosen cell and every sufficiently long cutoff. This
proves the actual compact normalized free-window target component. Integrating
against retained variables still requires its exact retained/free coefficient
identity and good retained-centre/correction event. Physical orbit transfer
remains independent and open.


**C22.8c / F170 FINAL — literal-window compact fluctuation, LEAN PROVED.**
`CompactGaussianWindowFluctuation.lean` discharges the compact energy
threshold with the actual normalized whole-window C/log(N) estimate. For
every height, cutoff and retained phase, every selected injective prime
enumeration and every half-unit bias family, one measurable original-law
event controls centered fluctuations on the full inner closed disc. Its mass
is at least one quarter times exp(-2*sum squared biases). Final8509 exit0
warning-free; public audit F171scratch63371 standard-only; exact index1;
lint28363 ten unrelated unreachable modules, no BAG debt.


**C22.12 — fixed holomorphic normalized target (paper candidate).**
Apply the proved Gaussian linear-span density to any target holomorphic on
a larger closed disc, at half the final tolerance. Enumerate the finite
coefficient support after adjoining frequency zero with zero coefficient
when absent; this guarantees a nonempty mode list without changing its sum.
Apply C22.11 to that list at half tolerance. Triangle inequality embeds
its canonical target event in the canonical event for the original target.
The same original section mass lower bound and prescribed-prefix retained
cell survive. This closes only the fixed holomorphic normalized free-window
target component: the full AFE target depends on height through its common
row and correction and still needs the finite-catalogue/retained-centre
assembly described in C22.9.


**C22.10 / F171 FINAL — actual compact mode mean synthesis, LEAN PROVED.**
`CompactGaussianWindowModeSynthesis.lean` constructs one finite retained
character cell preserving any prescribed prime prefix. At all large N and
every height, literal full-window biases have norm at most one half and
squared cost at most kappa*log(N), for arbitrary kappa>0. The same biases
approximate the fixed finite Gaussian target sum uniformly on the inner
disc, for every retained phase in that cell and every later cutoff.
Final85934 exit0 warning-free; public audit F172scratch93087 standard-only;
exact index1; lint78495 eleven unrelated unreachable modules, no BAG debt.


**C22.13 — uniform analytic common row and inverse (paper candidate).**
For lambda(s,N,tau)=sqrt(N)*chi(s+i*tau)*N^(s-1), the exact norm is
|chi(s+i*tau)|*N^(Re(s)-1/2). For 1/2<=Re(s)<=1/2+d0<1, existing
moving-line chi estimates give constants Kr,Kl independent of displacement:
|chi|<=Kr/T^d and |chi|^(-1)<=Kl*T^d, where d=Re(s)-1/2 and
T=max(1,|Im(s)+tau|). The second uses the exact chi reflection product.
If N/2<=T<=3N, the row norm is at most Kr*(N/T)^d<=2Kr and its inverse
at most Kl*(T/N)^d<=3Kl. Thus one fixed positive bound controls both.
Analyticity and nonvanishing on the open critical strip follow from the
proved Gamma and cpow identities; the inverse is holomorphic there.
On every fixed right-half-strip disc and tau in [N,2N], the height comparison
holds for all large N. This supplies the bounded analytic normalizers for
the finite target catalogue; no physical return count is assumed.


**C22.11 / F172 FINAL — canonical compact mode target, LEAN PROVED.**
`CompactGaussianWindowModeTarget.lean` proves the literal joint retained/free
target event is closed and measurable, and every fixed finite Gaussian mode
target has section mass at least quarter*exp(-2*kappa*log(N)) for arbitrary
kappa>0 throughout one prescribed-prefix cell, all heights and later cutoffs.
Final23526 exit0 warning-free; all four public audits F173scratch31188
standard-only; exact index3; lint32404 eleven unrelated unreachable modules,
no BAG debt. No conditional witness-selection premise is used.


**C22.14 — finite catalogue of a bounded holomorphic family (paper candidate).**
Let every f_i be holomorphic and bounded by C on ball(c,rho), and r<rho.
For each z in closedBall(c,r), the ball of radius rho-r centered at z lies
inside the outer ball. Apply the existing local Cauchy derivative estimate
there to obtain |f_i'(z)|<=2C/(rho-r), uniformly in i and z. Convexity
of the inner disc gives one Lipschitz modulus, hence equicontinuity.
Arzela-Ascoli makes the closure of the restrictions compact in supremum
norm. Total boundedness then gives finitely many representatives from the
actual family, each function within epsilon uniformly on the inner disc.
Choosing representatives from the family preserves outer-disc holomorphy;
no properties of unknown limit functions are needed. This catalogue is
chosen before constructing any coherent phase cells.


**C22.12 / F173 FINAL — fixed holomorphic compact window target, LEAN PROVED.**
`CompactGaussianWindowHolomorphicTarget.lean` reaches every target
holomorphic on a larger closed disc with the literal normalized free-window
sum on the whole inner disc. A retained cell preserves any prescribed finite
prime prefix; the original section mass is at least quarter*exp(-2*kappa*log(N))
for arbitrary kappa>0, every height and every sufficiently long cutoff.
Final39274 exit0 warning-free; public audit F174scratch54567 standard-only;
exact index1; lint82631 ten unrelated unreachable modules, no BAG debt.
The full AFE compact target and physical height-count producer remain open.


**C22.15 — translate the complementary contour to expose spectral holomorphy (paper candidate).**
At full spectral point z=1/2+d+i*t, the complementary coefficient is minus
chi(z) times the deep coefficient at 1-z. Its contour w=d-4+i*v_old has
1-z+w=-7/2+i*(v_old-t). Substitute v=v_old-t. Then

    w = z-9/2+i*v,
    1-z+w = -7/2+i*v.

Thus the literal coefficient becomes -chi(z)/(2*pi) times the integral of
chi(-7/2+i*v)*(n+1)^(-9/2+i*v)*N^(z-9/2+i*v)*K(z-9/2+i*v).
The chi numerator and integer exponent are independent of z. The remaining
parameter dependence is holomorphic on the strip, with the Gaussian denominator
away from zero. After division by the common row, the N power has real
exponent -4, cancelling the polynomial growth of chi near v=-Im(z) on
conductor windows. Exact translation invariance must identify this representation
with the original coefficients before using it; local dominated holomorphic
integration and summable n^(-9/2) bounds should then give the complete
complement holomorphy, compact bounds and prefix stability. No theorem from
this candidate has yet been formalized.


**C22.13 / F174 FINAL — compact row and inverse bounds, LEAN PROVED.**
`CompactGaussianReflectedRowBounds.lean` proves the exact common-row norm,
nonvanishing and holomorphy of both row and inverse on the open strip,
and simultaneous uniform bounds on any fixed right-strip disc throughout
the actual dyadic height window tau in [N,2N] for every large N.
Final78215 exit0 warning-free; five public audits F175scratch88188 and
reused Cauchy audit standard-only; exact index6; lint48414 ten unrelated
unreachable modules, no BAG debt.


**C22.16 — locally uniform integrable complementary majorant (paper candidate).**
For fixed N>0, 0<=Re(z)<=1 and |Im(z)|<=B, the translated deep integrand
is bounded by (n+1)^(-9/2) times one integrable function of v, independent
of z and n. The chi numerator is bounded by K*(1+|v|)^4. The conductor
power is bounded by N^(-9/2)+N^(-7/2). The Gaussian denominator is at
least one and its real-square exponent at most 81/4. The inequality
(v+Im(z))^2>=v^2/2-Im(z)^2 gives the common majorant

    K*(N^(-9/2)+N^(-7/2))*exp(81/4+B^2)
      *(1+|v|)^4*exp(-v^2/2).

Polynomial Gaussian integrability is already available. The corpus theorem
differentiableAt_integral_of_cauchy_dominated then supplies local complex
holomorphy without a derivative-majorant premise. Integrating the same bound
retains the summable n^(-9/2) coefficient envelope for every compact spectral
set, allowing reciprocal-character tsum holomorphy and phase continuity.
Conductor-uniform bounds remain the separate cancellation in C22.15.


**C22.14 / F175 FINAL — finite holomorphic catalogue, LEAN PROVED.**
`HolomorphicDiscFiniteCatalogue.lean` gives equicontinuity on any strictly
smaller closed disc for a uniformly bounded holomorphic family, followed by
finitely many representatives from that actual family approximating every
member uniformly. No half-radius restriction is needed. Final2237 exit0
warning-free; both public audits F176scratch87429 standard-only; exact
index2; lint26927 eleven unrelated unreachable modules, no BAG debt.


**C22.15 / F176 FINAL — exact compact complementary contour, LEAN PROVED.**
`ReflectedCompactComplementIntegral.lean` translates the original deep
coefficient exactly into complex spectral coordinates, identifies the actual
complement with its original negative chi prefactor, and proves integrand
holomorphy on Re(z)<9/2. Final36035 exit0 warning-free; three public audits
F177scratch55580 standard-only; exact index5; lint87028 eleven unrelated
unreachable modules, no BAG debt.


**C22.17 — full reciprocal-character complement holomorphy (paper candidate).**
For fixed positive N and arbitrary phase, multiply each translated deep
coefficient by the original conjugate character, of norm one. C22.16 gives
one summable n^(-9/2) bound on every bounded rectangle in the open unit strip.
The Weierstrass theorem makes the complete series holomorphic there. Multiply
by the original -chi(z), which is holomorphic on that strip. C22.15 identifies
this function exactly with the original complementary series at every right
spectral point, with no conductor restriction needed for the identity.
This step supplies holomorphy, not a conductor-uniform bound; the latter still
requires the cancellation between the N power and translated chi growth.


**C22.18 — displacement-uniform deep scale estimate (paper candidate).**
The original deep-contour norm estimate depends on 0<d<1/2 only through
N^(d-4) and exp((d-4)^2)/|d-4|. Since |d-4|>=1 and (d-4)^2<=16, replace
the latter factor by exp(16) before integration. The same integrable
(1+|v|)^4*exp(-v^2) majorant then gives one D, independent of d, N and t,
with deep coefficient norm at most
D*N^(d-4)*(1+|t|)^4*(n+1)^(-9/2).
For z=s+i*tau on a fixed right-strip disc and tau in [N,2N], common-row
normalization cancels the chi factor exactly, and divides this bound by
N^(Re(s)-1/2). The resulting N^-4 cancels the height polynomial. This is
the conductor-uniform summable envelope needed for compact prefix stability;
the local majorant in C22.16 serves a separate holomorphy purpose.


**C22.19 — compact conductor cancellation for original coefficients (paper candidate).**
Fix 0<=d0<1/2. On 0<d<=d0, N>=1 and N/2<=max(1,|t|)<=3N,
F174 bounds |chi(1/2+d+it)|*N^d by a constant independent of d,N,t.
C22.18 bounds the deep coefficient by D*N^(d-4)*(1+|t|)^4*(n+1)^(-9/2).
Since 1+|t|<=4N, the exact original complement identity combines these
into one 256*D*C*(n+1)^(-9/2) bound. Every fixed right-strip disc shifted
by tau in [N,2N] eventually satisfies this same wider height band. This
retains the exact original coefficients and leaves a summable, compact-uniform
arithmetic envelope for tail control and finite-prefix phase stability.


**C22.16 / F177 FINAL — local summable integral majorant, LEAN PROVED.**
`ReflectedCompactComplementDomination.lean` gives one integrable polynomial
Gaussian majorant on each compact spectral rectangle, preserving the literal
summable (n+1)^(-9/2) coefficient factor. Final34332 exit0 warning-free;
public audit F178scratch51679 standard-only; exact index2; lint64404 eleven
unrelated unreachable modules, no BAG debt. Holomorphy assembly is next.


**C22.20 — uniform first means across an abscissa band (paper candidate).**
For 0<a<=beta<=b<1/2, normalize the Gaussian Abel square-root cost by
N^(1/2-beta). In its positive-increment representation, each normalized
weight equals N^(-1/2)*(N/n)^beta*cutoff(n/N). Monotonicity in beta,
split at n=N, bounds it by the sum of the two endpoint normalized weights.
The already proved endpoint costs therefore give one constant uniform in
beta, polynomial cutoff L and smoothing N>=1. Apply the original universal
summatory first-mean envelope C_epsilon+epsilon*sqrt(n) before Abel summation.
The finite-constant contribution satisfies C/N^(1/2-beta)<=C/N^(1/2-b)
and vanishes uniformly. This extends actual normalized Gaussian
first-mean decay across every compact beta-band, all cutoffs and phase shifts.
It will also control every retained-coordinate projection by contraction.

**C22.21 — one circle first-moment envelope for the whole disc (paper candidate).**
For r<R and f holomorphic near the closed outer disc, Cauchy's exact circle
average gives f(z) as the average of ((w-c)/(w-z))*f(w), for every inner
point z. On the outer circle, the multiplier norm is at most R/(R-r).
Thus the same boundary L1 integral bounds every inner value. The resulting
nonnegative measurable random envelope has expectation bounded by
R/(R-r) times the uniform original first mean on the outer circle, by Tonelli.
Together with C22.20 it gives compact-uniform vanishing first means for the
literal retained normalized background. This uses first moments directly;
the nonvanishing second moment is not substituted for them.


**C22.16 / F178 FINAL — compact complementary coefficient holomorphy, LEAN PROVED.**
`ReflectedCompactComplementHolomorphy.lean` proves continuous real contour
integrands, complex holomorphy of every deep coefficient on 0<Re(z)<1,
and one summable coefficient envelope on every compact spectral rectangle.
Final91931 exit0 warning-free; three public audits F179scratch38579 standard-only;
exact index3; lint53082 twelve unrelated unreachable modules, no BAG debt.


**C22.17 / F179 FINAL — full holomorphic reciprocal complement, LEAN PROVED.**
`SteinhausCompactReflectedComplement.lean` admits the complete original deep
reciprocal-character series absolutely for every positive scale, proves its
holomorphy throughout the open unit strip, restores the original negative chi
factor, and identifies it exactly with the literal full complementary series.
Final34936 exit0 warning-free; four public audits F180scratch80303 standard-only;
exact index5; lint16839 thirteen unrelated unreachable modules, no BAG debt.


**C22.22 — one character tolerance for a uniformly summable family (paper candidate).**
For arbitrary coefficients a_i(n) bounded by one nonnegative summable u(n),
the full reciprocal-character series has a finite-prefix tolerance uniform
in i and in the reference phase. Choose B so the u-tail is below epsilon/4.
The two phase tails each obey that same bound. On n<B, a character cell
of radius delta controls the difference by delta*sum_{n<B}u(n). Choose
delta=epsilon/(4*(1+sum_{n<B}u(n))). The head plus two tails is below epsilon.
C22.19 supplies the actual family's u(n)=C*(n+1)^(-9/2), indexed by every
smoothing, height and spectral point after its eventual threshold. Thus
one fixed prefix controls the whole compact complement simultaneously.


**C22.18 / F180 FINAL — displacement-uniform deep scale bound, LEAN PROVED.**
`ReflectedCompactDeepUniformScale.lean` strengthens the actual deep coefficient
scale estimate to one constant for every 0<d<1/2, positive smoothing and
real height. The exact N^(d-4), height polynomial and summable n-factor remain.
Final45592 exit0 warning-free; public audit F181scratch88491 standard-only;
exact index1; lint59980 fourteen unrelated unreachable modules, no BAG debt.


**C22.23 — exact compact pole correction (paper candidate).**
Write the original reflected pole in spectral coordinates as
chi(z)*N^z*exp(z^2)/z, where z=s+i*tau. This identity retains its denominator.
It is holomorphic on the open unit strip. On a fixed right-strip disc and
large dyadic conductor windows, |z|>=N/2 and Re(z)^2<=1, hence
|exp(z^2)|<=exp(1). The exact row identity gives
|pole|=|row(s,N,tau)|*sqrt(N)*|exp(z^2)|/|z|.
For N>=1, sqrt(N)<=N, so F174 gives the uniform bound 2*C*exp(1).
The pole has no phase dependence, so the compact correction inherits all
complement prefix tolerances unchanged. Combined with complement holomorphy,
this supplies the bounded holomorphic correction family needed by the finite
catalogue, with every original AFE term retained.


**C22.19 / F181 FINAL — original conductor-band coefficient envelope, LEAN PROVED.**
`ReflectedCompactComplementConductor.lean` combines the displacement-uniform
deep scale estimate with the exact common-row norm. One summable coefficient
bound now holds for every 0<d<=d0<1/2, N>=1 and
N/2<=max(1,|tau|)<=3*N. Final98792 exit0 warning-free; public audit
F182scratch61511 standard-only; exact index1; lint1151 fourteen unrelated
unreachable modules, no BAG debt.


**C22.24 — bounded holomorphic reference-target catalogue (paper candidate).**
Assemble the exact scalar correction as full reciprocal complement minus
original reflected pole. C22.17 and C22.23 give its spectral holomorphy;
C22.19 and C22.23 give one compact conductor bound over all phases. C22.22
controls its phase difference uniformly on the same disc, since the pole
cancels from that difference. For a fixed larger-disc holomorphic target f,
form h_{N,tau,xi}(s)=row(s,N,tau)^(-1)*(f(s)-correction(s+i*tau,N,xi)).
F174 gives a uniform inverse-row bound and holomorphy. Thus the entire
reference-target family is bounded and holomorphic on one larger disc.
F175 gives finitely many actual representatives on a strictly smaller disc,
before any coherent phase cell is selected. Each representative can use its
own F173 prefix-preserving cell, window constants and eventual threshold;
finite minima and maxima suffice. No common free window across representatives
is required. Phase-prefix stability ties the reference xi to the eventual
retained phase; C22.20-21 make the retained normalized background small on a
positive-mass part of each fixed cell. The physical common-height return count
remains a separate open producer after this original-law compact assembly.

**C22.20 refinement — reuse the actual positive Gaussian mass.**
The normalized Abel square-root-increment bound is exactly bounded by
normalizedGaussianAbsoluteMass(1/2-beta,N). F153 already gives the actual
summable positive coefficient series and endpoint limits; F154 bounds its
intermediate masses by the two endpoints. These existing results supply
the uniform beta-band cost directly, without a second endpoint-power proof.


**C22.19 / F182 FINAL — compact conductor complement bound, LEAN PROVED.**
`ReflectedCompactComplementDisc.lean` bounds every original complementary
coefficient uniformly on a fixed strict right-strip disc throughout all large
dyadic conductor windows. Summing the original reciprocal series gives one
bound for the complete holomorphic complement, uniform in every phase.
Final32531 exit0 warning-free; both public audits F183scratch79386 standard-only;
exact index2; lint52121 fourteen unrelated unreachable modules, no BAG debt.


**C22.22 / F183 FINAL — uniform reciprocal-family prefix tolerance, LEAN PROVED.**
`SteinhausReciprocalSeriesStability.lean` proves one finite character prefix
and positive radius control every reciprocal series dominated by one
nonnegative summable coefficient sequence, uniformly in the reference phase.
Final70173 exit0 warning-free; public audit F184scratch42851 standard-only;
exact index1; lint7354 fourteen unrelated unreachable modules, no BAG debt.
Explicit tail-sequence types resolved elaboration cost at default heartbeats.


**C22.22 / F184 FINAL — actual compact complement prefix stability, LEAN PROVED.**
`ReflectedCompactComplementStability.lean` discharges the summable-family
bound against the actual conductor coefficients. One finite prefix and positive
radius now control the complete literal complement simultaneously on every
point of a fixed right-strip disc, for all reference phases and every large
dyadic conductor window. Final32922 exit0 warning-free; public audit
F185scratch29165 standard-only; exact index1; lint32475 fifteen unrelated
unreachable modules, no BAG debt.


**C22.23 / F185 FINAL — exact compact pole, LEAN PROVED.**
`ReflectedCompactPole.lean` retains the exact original residue, proves its
open-strip holomorphy and bounds it uniformly on fixed right-strip discs
throughout all large dyadic conductor windows. Final87330 exit0 warning-free;
four public audits F186scratch82189 standard-only; exact index5; lint46886
seventeen unrelated unreachable modules, no BAG debt.


**C22.24 / F186 FINAL — complete compact correction, LEAN PROVED.**
`ReflectedCompactCorrection.lean` assembles the original reciprocal complement
minus its pole, proves open-strip holomorphy, a uniform compact conductor bound
and one phase-prefix tolerance, and identifies the original full AFE exactly
as primal carrier plus this correction. Final27622 exit0 warning-free; four
public audits F187scratch69716 standard-only; exact index5; lint5632 eighteen
unrelated unreachable modules, no BAG debt.


**C22.24 / F187 FINAL — actual reference-target catalogue, LEAN PROVED.**
`ReflectedCompactTargetCatalogue.lean` proves the original row-inverted target
family is holomorphic and uniformly bounded on every fixed larger right-strip
disc, across all phases and large conductor windows. One finite collection of
actual holomorphic members approximates this entire family on a smaller disc,
before any coherent cell is selected. Final99748 exit0 warning-free; three
public audits F188scratch79618 standard-only; exact index5; lint59311 ten
unrelated unreachable modules, no BAG debt.


**C22.20 / F188 FINAL — uniform band first moment, LEAN PROVED.**
`SteinhausGaussianBandFirstMean.lean` bounds the exact normalized Abel cost by
the actual positive Gaussian coefficient mass. Two endpoint limits and the
unconditional summatory first-mean envelope give one decay threshold for every
exponent in a fixed compact subcritical band, uniformly over all independent
polynomial cutoffs. Final71232 exit0 warning-free; three public audits
F189scratch63321 standard-only; index3; lint27442 twelve unrelated unreachable
modules, no BAG debt.


**C22.25 — actual retained compact small-centre event (paper candidate).**
For the exact normalized retained carrier N^(1/2-s)*sum_smooth n^(s-1)*cutoff*X,
phase stationarity and smooth projection contract the band first moment from
C22.20. On an outer circle of radius R and inner disc radius r<R, C22.21
defines a measurable ENNReal envelope G from the boundary absolute integral,
with pointwise norm<=G and E[G]<=R/(R-r)*eta. Choose
eta=delta*(R-r)/R to make E[G]<=delta uniformly in every retained prime set
and polynomial cutoff. G depends only on those retained coordinates. Taking
delta=m*epsilon/2, Markov removes at most m/2 mass at threshold epsilon,
so every prescribed event of mass at least m retains at least m/2 on which
the entire compact background is smaller than epsilon. This is original
product measure, not a physical-height count; the latter remains open.


**C23.1 — sharp mean-value transport budget (candidate under audit).**
The corpus theorem Sieve.dirichlet_meanValue_sharp controls the signed second-
moment error by 104*sum_n (n+1)*|a_n|^2. It is stronger than the absolute
inverse-log-gap sum used in the initial physical-count search. Applying it
to an actual tilt still requires its frequency-weighted coefficient cost.
A necessary synthesis budget follows from Cauchy-Schwarz: if all free primes
exceed Y, total channel energy is E and |sum_p mu_p*a_p|>=v, then
Y*v^2 <= E*sum_p p*|mu_p|^2. Since the actual normalized channel energy is
O(1/log N), macroscopic target displacement across a conductor-sized prime
window forces a large frequency-weighted bias budget. Whether that lower
budget defeats a proposed spectral-factor mean-value transfer must be checked
against its exact coefficients; no physical transport or no-go is claimed yet.
The positive cost law is the next concrete audit target if this transfer fails.


**C22.26 — compact normalized cubic tail (paper candidate).**
For any fixed b>=0, Re(s)<=b, square smoothing N=n^2 and cubic cutoff L=n^3,
the existing full Gaussian tail is at most K*N^A*L^(Re(s)-A)/(A-Re(s)).
Multiplying by the exact normalized carrier factor N^(1/2-s) changes its
size to K*n^(1+Re(s)-A)/(A-Re(s)). Choose A=q+b+1 for any q>0.
Then A-Re(s)>=q+1 and 1+Re(s)-A<=-q, uniformly over the entire half-plane
and every phase. Thus one K/(q+1) gives arbitrary power decay, and the
compiled common-row bound transports it to the complete reflected primal
on every fixed right-strip disc and dyadic physical window. No probabilistic
tail subtraction is required.


**C22.20 / F189 FINAL — actual retained carrier first mean, LEAN PROVED.**
`CompactGaussianRetainedFirstMean.lean` defines the exact normalized retained
Gaussian arithmetic sum, proves it entire and jointly measurable, identifies
its normalization and integrable norm, and proves first-mean decay uniformly
across every fixed strict right-strip abscissa band, all imaginary parts,
retained prime sets and independent cutoffs. Final31880 exit0 warning-free;
five public audits F190scratch51368 standard-only; index6; lint67643 ten
unrelated unreachable modules, no BAG debt.


**C22.21 / F190 FINAL — compact boundary first-mean bound, LEAN PROVED.**
`CompactDiscFirstMeanBound.lean` proves the norm of the circle average is
bounded by the average norm and derives one Cauchy boundary L1 bound for
every point on a smaller closed disc, with exact factor R/(R-r). No second
moment replaces the needed first mean. Final32257 exit0 warning-free; both
public audits F191scratch82886 standard-only; index2; lint82405 eleven unrelated
unreachable modules, no BAG debt.


**C22.21 / F191 FINAL — measurable compact first-mean envelope, LEAN PROVED.**
`CompactDiscFirstMeanEnvelope.lean` supplies one measurable ENNReal boundary
integral dominating every point on the inner disc. Tonelli bounds its expectation
from the actual boundary first moments, with explicit radius-gap and circle-length
factors. Final56580 exit0 warning-free; three public audits F192scratch88407
standard-only; index5; lint79954 eleven unrelated unreachable modules, no BAG debt.


**C23.2 — target-class compatibility check (audit pending).**
The required physical producer is zeta self-return. The proved random target
laws are stronger in target class and allow arbitrary holomorphic functions,
including a linear target with a zero inside the disc. A future transport
lemma must not silently preserve this entire target class: Rouche would turn
sufficiently many returns to such a fixed zero-bearing target into many
right-strip zeta zeros. The source statement of the currently unwired
ZetaZeroDensityPowerSaving.exists_zetaZeroDensity_powerSaving gives exponent
1-delta/40, but has not been independently compiled or axiom-audited in this
continuation. Audit this compatibility before proposing a target-independent
rare-event transport. The actual arithmetic self-target may need a feature
absent from arbitrary holomorphic targets. No no-go or physical count is
claimed from this source-level observation.


**C22.25 / F192 FINAL — actual retained compact envelope, LEAN PROVED.**
`CompactGaussianRetainedEnvelope.lean` applies the boundary first-mean envelope
to the exact normalized retained Gaussian carrier. Its expectation tends to
zero uniformly over all retained prime sets and polynomial cutoffs; it
dominates every point on the disc and depends only on retained coordinates.
Final92554 exit0 warning-free; four public audits F193scratch39410 standard-only;
index5; lint13159 ten unrelated unreachable modules, no BAG debt. Explicit
function and cast types resolve elaboration at default heartbeats.


**C22.27 — exact normalized retained/free assembly (paper candidate).**
For N>0, the common row lambda=sqrt(N)*chi(s+i*tau)*N^(s-1) satisfies
lambda*N^(1/2-s)=chi(s+i*tau), by the exact positive-real complex-power law.
The existing all-integer logarithmic phase identity then identifies every
original retained coefficient sum with lambda times the new normalized
retained carrier at shifted phase. The already proved affine free-window
identity and exact normalized channel factorization give the complete frozen
finite carrier as lambda*(retained normalized background + normalized free
window sum), preserving the original polynomial cutoff and all phases.


**C22.25 / F193 FINAL — compact retained small-centre event, LEAN PROVED.**
`CompactGaussianRetainedSmallCentre.lean` constructs one measurable event
depending only on retained coordinates, on which the entire compact normalized
background is smaller than any prescribed positive threshold. The discarded
original mass tends to zero uniformly over retained sets and cutoffs; every
fixed positive-mass phase event retains at least half its mass. Final50971
exit0 warning-free; five public audits F194scratch22250 standard-only; index6;
lint27915 ten unrelated unreachable modules, no BAG debt.


**C22.26 / F194 FINAL — normalized compact cubic tail, LEAN PROVED.**
`CompactGaussianNormalizedCubicTail.lean` proves arbitrary-power deterministic
error for square smoothing and cubic truncation, uniformly over every phase
and every point in a fixed left half-plane. The exact normalization cancels
the conductor exponent before the tail estimate is applied. Final52043 exit0
warning-free; public audit F195scratch6370 standard-only; index1; lint30544
eleven unrelated unreachable modules, no BAG debt.


**C23.1 / F195 FINAL — actual frequency-weighted synthesis cost, LEAN PROVED.**
`CompactGaussianFrequencyWeightedBias.lean` proves the necessary exact bound
floor(N/D)*log(N)*|sum_p mu_p*channel_p|^2 <= C*sum_p p*|mu_p|^2
for the literal compact-window channels, uniformly over heights, retained
phases, independent cutoffs and bounded nonnegative abscissas. This is not
an orbit-transfer theorem or a no-go. Final79939 exit0 warning-free; public
audit F196scratch44685 standard-only; index1; lint74206 ten unrelated
unreachable modules, no BAG debt.


**C22.28 — full compact event admission (paper candidate).**
At each fixed spectral point the Gaussian primal and reciprocal complement
are sums of continuous phase characters with phase-independent summable norm
majorants. The literal full reflected AFE is therefore continuous in phase.
A closed error bound at every point of a compact disc is an arbitrary
intersection of closed phase sets, hence closed and measurable. Exact
zero-phase identification preserves the original zeta self-return event.
This supplies admission for original-law disintegration, not a physical count.


**C22.27 / F196 FINAL — exact normalized carrier assembly, LEAN PROVED.**
`CompactGaussianReflectedCarrierIdentity.lean` proves exact cancellation of
the common spectral row, identifies the literal retained background after
one logarithmic phase shift, and assembles the entire original frozen finite
carrier into that background plus the actual normalized free-window channels.
No coefficient or cutoff is replaced. Final83589 exit0 warning-free; three
public audits F197scratch27360 standard-only; index3; lint71523 ten unrelated
unreachable modules, no BAG debt.


**C23.3 — exact spectral-factor transport cost (paper candidate).**
For a literal affine circle density 1+2*Re(conj(m)*z), |m|<=1/2, set
x=(1+sqrt(1-4*|m|^2))/2, a=sqrt(x), b=conj(m)/a. Then
a^2+|b|^2=1, a*conj(b)=m, and the density is exactly |a+b*z|^2.
Since 0<a<=1, |b|^2>=|m|^2. Multiplying these degree-one factors over
actual free primes yields squarefree Dirichlet coefficients. Their exact
frequency-weighted squared mass is product_p(a_p^2+p*|b_p|^2), which is
at least 1+sum_p(p-1)*|m_p|^2. Combine this actual coefficient cost with
F195 before testing a sharp-MV transfer certificate. This is a proposed
exact positive cost law, not a claim that actual signed orbit error is large.


**C22.26 / F197 FINAL — original compact primal tail, LEAN PROVED.**
`ReflectedCompactPrimalCubicTail.lean` transports the normalized cubic bound
through the exact original chi factor and common-row norm. The complete
original primal has arbitrary-power deterministic tail decay uniformly on
every fixed strict-right-strip disc, every phase and full square-conductor
height window. Final87202 exit0 warning-free; both public audits
F198scratch15084 standard-only; index2; lint30923 ten unrelated unreachable
modules, no BAG debt.


**C22.28 / F198 FINAL — complete compact target event, LEAN PROVED.**
`ReflectedCompactTargetEvent.lean` proves phase continuity of both literal
full series, exact complex-coordinate full AFE identity and zero-phase
equality with zeta. Simultaneous closed target error throughout a compact
disc is a closed measurable event. Final31679 exit0 warning-free; seven
public audits F199scratch99727 standard-only; index9; lint15612 ten unrelated
unreachable modules, no BAG debt.


**C22.29 — rotated compact retained event (paper candidate).**
The existing measure-preserving vertical phase rotation at -tau has exactly
the characters of raw logPhaseShift(omega,tau), for all integer characters.
Pull back the intersection of a fixed finite-character cell and the compact
small-centre event under this actual rotation. Its original probability is
the unrotated intersection probability, hence at least half the fixed cell
mass eventually, uniformly in tau, cutoff and retained set. If the retained
set contains primes through the cell cutoff, this event depends only on
retained coordinates. Every point gives both the raw shifted cell condition
needed by compact mode synthesis and the small shifted retained background.
No raw real translation is treated as measure preserving.


**C23.3 / F199 FINAL — exact affine spectral factor, LEAN PROVED.**
`SteinhausAffineSpectralFactor.lean` constructs a normalized degree-one factor
for every actual admissible affine circle bias. Its squared modulus equals
the original density pointwise, and its nonconstant squared coefficient is
at least the squared bias. Final73156 exit0 warning-free; both public audits
F200scratch45074 standard-only; index2; lint46371 ten unrelated unreachable
modules, no BAG debt.


**C22.30 — exact full target error assembly (paper candidate).**
Write the actual finite frozen primal as lambda*(B+W), reference target
H=lambda^-1*(f-C0), and original full primal as finite primal plus tail T.
Then the complete AFE error is exactly
T + lambda*(B+(W-g)+(g-H)) + (C-C0).
Consequently its norm is at most eT+Crow*(eB+eW+eG)+eC whenever
those five literal errors are bounded. The row is nonzero on the strip,
so no reference-target cancellation premise is needed. Apply this identity
pointwise to the canonical whole-disc event before original-law disintegration.


**C23.4 — spectral budget rigidity (paper candidate).**
F201's proposed actual cost law forces every synthesis displacement to
vanish uniformly when its frequency-weighted spectral cost is at most A*N
for a fixed A. Indeed |displacement|^2 <= C*A/log(N). Hence a nonzero
macroscopic target cannot be obtained from a spectral factor with a bounded
normalized sharp-MV cost, much less a vanishing one. This is a precise
limitation of the frequency-cost certificate. It does not forbid actual
signed cancellation, another density, or an arithmetic self-target argument.
The positive survivor is the exact spectral-cost/target-size rigidity law.


**C23.3 / F200 FINAL — literal spectral product coefficients and cost, LEAN PROVED.**
`SteinhausSpectralProductCost.lean` expands the original phase factor product
into its exact distinct squarefree integer frequencies and proves the exact
frequency-weighted squared coefficient mass equals the product of local
weighted masses. Normalization gives the lower bound
1+sum_p(p-1)*|bias_p|^2. Prime-factor recovery excludes all collisions.
Final80859 exit0 warning-free; five public audits F201scratch79743 standard-only;
index8; lint13319 ten unrelated unreachable modules, no BAG debt.


**C23.3 / F201 FINAL — actual synthesis/transport cost, LEAN PROVED.**
`CompactGaussianSpectralTransportCost.lean` proves
N*log(N)*|actual normalized synthesis displacement|^2 <= C*frequency cost
for every normalized spectral factor realizing those actual free-window biases,
uniformly over heights, retained phases, independent cutoffs and the abscissa
band. Final30389 exit0 warning-free; public audit F202scratch49221 standard-only;
index1; lint78589 eleven unrelated unreachable modules, no BAG debt. This is
not a lower bound on actual signed orbit error.


**C22.31 — complete original-law compact target assembly (next dependency plan).**
For one fixed catalogue member g, choose error e=epsilon/(10*(Crow+1)).
Use the correction tolerance at epsilon/4 and requested phase tolerance to
set a fixed preserved prime prefix. The compact holomorphic target theorem
chooses one coherent centre preserving that prefix, window B,D and cell
radius; shrink the radius to satisfy both correction and prescribed-cell
conditions. C22.29 intersects that rotated cell with the compact small-centre
event at e, preserving fixed positive mass. On square/cubic scales the
retained set includes the whole cell prefix and the affine window seam holds.
Every selected retained section has original free-phase target probability
>=exp(-2*kappa*log(N))/4 by the compiled compact target theorem. Exact
C22.30 error assembly, the fixed correction prefix and uniform cubic tail
place this section in the full compact target event. The compiled prefix
resampling inequality then integrates the conditional bound. The moving
reference target is compared to g at error e; this is the only conditional
branch of this intermediate fixed-g result. C22.24 supplies a finite
catalogue of such g. Take finite minima of positive masses and common
eventual thresholds, and choose the applicable member separately for each
N,tau. This requires no measurable branch selection. It closes only the
original product-law compact target mass, not the physical count.


**C22.29 / F202 FINAL — actual rotated retained event, LEAN PROVED.**
`CompactGaussianRotatedRetainedEvent.lean` proves exact character/carrier
compatibility of raw logarithmic shift with the measure-preserving vertical
rotation, exact shifted-cell/moving-centre equivalence, and one positive-mass
retained event supporting both the prescribed cell and small compact centre
uniformly in height and cutoff. Final11447 exit0 warning-free; four public
audits F203scratch25808 standard-only; index4; lint28678 thirteen unrelated
unreachable modules, no BAG debt. Raw translation was not used as a
measure-preserving map. Physical recurrence remains open.


**C22.30 / F203 FINAL — complete target error assembly, LEAN PROVED.**
`ReflectedCompactTargetAssembly.lean` proves the exact five-error estimate
for the original full AFE, retaining the true row, free-prime channels,
retained background, reciprocal correction and cubic polynomial cutoff.
Row nonvanishing is discharged on the strict strip. Final72858 exit0
warning-free; public audit F204scratch82317 standard-only; index1;
lint94037 twelve unrelated unreachable modules, no BAG debt.


**C22.32 — finite catalogue removal of the fixed-branch condition (paper proof).**
C22.31 fixes one approximation accuracy before choosing any holomorphic
catalogue member. Apply the compiled finite catalogue to the literal moving
reference family at this accuracy. Each member has its own positive branch
mass and eventual cutoff; finitely many members give one positive minimum
mass and one common cutoff. At each conductor/height choose the applicable
member, then apply its branch estimate. No measurable choice across heights
is used. Choosing kappa=epsilon/2 turns the factor exp(-2*kappa*log(N)) into
N^(-epsilon). This yields the full complex original-law compact target event
inside every prescribed moving finite-character cell. It still contains no
statement about the physical zero-phase point or a count of return heights.


**C23.4 / F204 FINAL — exact spectral budget rigidity, LEAN PROVED.**
`CompactGaussianSpectralBudgetRigidity.lean` proves that actual normalized
window synthesis tends uniformly to zero whenever its spectral frequency
cost is bounded by A*N. No separate nonnegative-A premise is needed.
Final47796 exit0 warning-free; public audit F205scratch76437 standard-only;
index1; lint88426 thirteen unrelated unreachable modules, no BAG debt.
This closes the positive rigidity survivor for this mean-value certificate;
actual signed-orbit cancellation remains outside the statement.


**C23.5 — general Dirichlet square-density transport cost (paper proof).**
For finite nonzero integer support S and complex coefficients with
sum_S |a_n|^2=1, set D=sum_S a_n X_n and let mu_p be the original-law
integral of X_p*|D|^2. Character orthogonality gives exactly
mu_p=sum_{n in S, p*n in S} a_n*conj(a_(p*n)). Cauchy bounds |mu_p|^2
by sum_{m in S, p divides m}|a_m|^2: the first coefficient mass is <=1,
and multiplication by p injects the second indices into the divisible support.
For any finite prime set P, one+sum_{p in P, p divides m}(p-1)<=m:
finite product growth bounds one+sum by the product of distinct divisors,
and that product divides m. Sum over m to obtain the unconditional law
1+sum_{p in P}(p-1)|mu_p|^2 <= sum_S m|a_m|^2.
Thus the earlier cost/mean constraint is not restricted to product-factor
densities. The strongest immediate positive survivor is this exact arithmetic
first-moment budget. Fourier identification and coefficient inequalities are
separate Lean obligations; no actual signed orbit-error lower bound follows.


**C22.31 / F205 FINAL — exact compact target branch mass, LEAN PROVED.**
`ReflectedCompactTargetBranch.lean` supplies one target accuracy before the
holomorphic branch is chosen. Each branch has a fixed positive original-law
mass factor, uniform over later square conductors, whole height windows and
all targets whose actual moving references lie within that accuracy.
The prescribed finite cell, full reciprocal correction, retained centre and
original cubic tail are all included. Final39192 exit0 warning-free; public
audit F206scratch55874 standard-only; index1; lint53852 fourteen unrelated
unreachable modules, no BAG debt.


**C23.6 — logarithmic frequency budget (paper proof).**
The same exact coefficient-correlation Cauchy bound used in C23.5 can be
charged by log(p), rather than p-1. For each nonzero frequency n, the sum
of log(p) over distinct selected prime divisors is at most log(n), because
their product divides n. Hence every normalized Dirichlet square density
satisfies sum_p log(p)*|mu_p|^2 <= sum_n |a_n|^2*log(n). Concavity of log
and normalization give the stronger bound by log(sum_n n*|a_n|^2).
On the actual window p>N/D, eventually log(p)>=log(N)/2. Combined with the
compiled O(1/log(N)) channel energy and Cauchy, this forces
(log(N))^2*|normalized target mean|^2 <= C*log(frequency cost).
Thus any fixed polynomial frequency-cost budget forces target means to
vanish. This is a stronger positive rigidity law for certificate design,
not a claim that actual signed orbit errors are large. Each logarithmic
and Jensen step requires Lean verification before promotion.


**C22.32 / F206 FINAL — full original-law compact target mass, LEAN PROVED.**
`FullReflectedAFECompactTarget.lean` proves that every target holomorphic on
a larger strict right-strip disc is reached on the whole inner compact disc,
inside every prescribed moving finite-character cell, with original-law
probability at least c*(n^2)^(-epsilon) for every epsilon>0 and all sufficiently
large square conductors and every height in [n^2,2*n^2]. All actual AFE terms
remain present. Finite catalogue choice is fully discharged. Final14664
exit0 warning-free; public audit F207scratch35952 standard-only; index1;
lint64754 twelve unrelated unreachable modules, no BAG debt. C22 compact
original-law target assembly is closed. Physical zero-phase common-height
recurrence MUST-270 remains OPEN.


**C23.5 / F207 FINAL — arithmetic prime-correlation budget, LEAN PROVED.**
`SteinhausPrimeCorrelationBudget.lean` bounds distinct prime divisor charge
by frequency minus one, bounds squared multiplicative coefficient correlation
by mass on divisible frequencies, and proves the normalized total weighted
frequency-cost inequality for arbitrary finite complex coefficient families.
Final93256 exit0 warning-free; three public audits F208scratch97454 standard-only;
index5; lint14290 twelve unrelated unreachable modules, no BAG debt. The
literal density/Fourier identification is the next leaf, not assumed here.


**C23.7 — density-weighted window second moment (paper proof and next audit).**
Let W=sum_{p in P} v_p X_p for a finite prime set, and let
D=sum_{n in S} a_n X_n have unit coefficient mass on nonzero frequencies.
Write b_m=sum_{p*n=m} v_p*a_n, with the exact multiplicative product support.
Parseval gives integral |W*D|^2=sum_m|b_m|^2. Put d(m)=number of distinct
selected primes dividing m. Each coefficient fibre contains at most d(m)
pairs, because p determines n. Cauchy therefore gives
sum_m|b_m|^2 <= sum_{p,n} d(p*n)*|v_p|^2*|a_n|^2.
Primality gives d(p*n)<=1+d(n), including repeated prime factors. Thus
integral |W|^2*|D|^2 <= (sum_p|v_p|^2)*(1+sum_n d(n)|a_n|^2).
If all p>Y>1, d(n)*log(Y)<=log(n); normalized Jensen bounds the last mean
by log(total frequency cost)/log(Y). For the actual compact window, energy
O(1/log(N)) and polynomial cost imply a vanishing weighted second moment.
Markov then rules out fixed positive density-weighted probability of a target
ball separated from zero. This is stronger than mean rigidity but remains a
restriction on this family of positive density certificates. Exact complex
convolution, collision-fibre bounds, prime occupation and the final event
inequality are separate Lean obligations; none is promoted as proved yet.


**C23.5 / F208 FINAL — actual Dirichlet-density moment cost, LEAN PROVED.**
`SteinhausDirichletDensityCost.lean` identifies the literal original-law
prime moment of every finite complex Dirichlet square density with its exact
multiplicative coefficient correlation. Normalized densities obey the
frequency-cost lower bound without any product-factor assumption. Original
complex Parseval and all F207 ingredients audited standard-only. Final44478
exit0 warning-free; both public audits F209scratch76149 standard-only;
index2; lint68661 eleven unrelated unreachable modules, no BAG debt.


**C23.6 / F209 FINAL — logarithmic density frequency cost, LEAN PROVED.**
`SteinhausDirichletLogCost.lean` proves the exact selected prime-divisor
logarithmic charge and applies normalized Jensen to obtain
sum_p log(p)*|actual density prime moment|^2 <= log(sum_n n*|a_n|^2)
for arbitrary normalized finite complex Dirichlet square densities.
Final62572 exit0 warning-free; all three public audits F210scratch56076
standard-only; index3; lint70721 twelve unrelated unreachable modules,
no BAG debt. No actual signed orbit-error bound is inferred.


**C23.6 / F210 FINAL — polynomial density-cost mean rigidity, LEAN PROVED.**
`CompactGaussianDirichletTransportRigidity.lean` proves the exact integer-window
logarithm lower bound, then log(N)^2*|mean window displacement|^2 <= C*log(cost)
for every normalized finite Dirichlet square density. Every fixed cost budget
N^A forces the normalized window mean to vanish uniformly. Final26038 exit0
warning-free; all three public audits F211scratch94536 standard-only; index3;
lint66426 twelve unrelated unreachable modules, no BAG debt. Mean rigidity
alone does not rule out concentration with cancellation elsewhere; C23.7 tests
that gap with actual weighted second moments. Physical return count OPEN.


**C23.7 / F211 FINAL — exact complex convolution energy, LEAN PROVED.**
`SteinhausComplexConvolution.lean` extends finite multiplicative convolution
and product Parseval to arbitrary complex coefficients, preserving every
frequency collision. Final50195 exit0 warning-free; two public audits
F212scratch19082 standard-only; index3; lint69438 thirteen unrelated
unreachable modules, no BAG debt. The occupation estimate is next.


**C24.1 — exact nonzero chi grades (paper audit; physical sum still open).**
The actual critical-line identity is chi(1/2+i*t)=exp(-2*i*theta(t)). Hence
its integer grade k, twisted by frequency omega, has exact real phase
omega*t-2*k*theta(t). On every subinterval of [T,2*T], T>=4, the audited
Hardy phase-rate curvature gives 2*theta''(t)>=1/(100*T). For every nonzero
integer k the second derivative has constant sign and magnitude at least
|k|/(100*T). The existing positive/negative van der Corput tests therefore
give integral norm <=6/sqrt(|k|/(100*T)), uniformly in omega and subinterval.
This includes negative grades and uses no gamma asymptotic approximation.
The grade-zero terms require separate arithmetic cancellation. Nonzero-grade
atom bounds alone do not control their growing-support sum or height-dependent
amplitude variation, and give no positive recurrence count. Corpus chi-power
lexical search returned no existing extension; filtered aggregate search is
pending. Formalize the exact grade atom before testing aggregate mechanisms.


**C23.7 / F212 FINAL — exact prime occupation energy bound, LEAN PROVED.**
`SteinhausPrimeConvolutionEnergy.lean` proves that a convolution frequency
has at most one representation per selected prime divisor. Its actual
Dirichlet-density-weighted prime-polynomial second moment is bounded by
original prime energy times weighted cofactor occupation plus one. Repeated
prime factors cause no extra loss. Final1064 exit0 warning-free; all three
public audits F213scratch92352 standard-only; index4; lint95689 fourteen
unrelated unreachable modules, no BAG debt. Jensen/log-cost assembly next.

C24.1 amplitude extension: anchor each grade primitive at a. The preceding
subinterval bound controls it at every x in [a,b]. Exact integration by parts
therefore multiplies the same oscillatory constant by |u(b)|+integral|u'| for
any complex amplitude with integrable derivative. This is the required cost
when actual target coefficients depend on height; fixed-coefficient estimates
cannot silently cover that dependence. Grade aggregation remains open.


**C23.7 / F213 FINAL — actual density second-moment log-cost law, LEAN PROVED.**
`SteinhausDirichletDensityEnergy.lean` proves selected-prime occupation
<=log(frequency cost)/ell whenever each selected prime has logarithm at
least ell>0. Consequently integral |W|^2*|D|^2 is at most original window
energy times (1+log(cost)/ell), for every normalized finite complex Dirichlet
square density. Final38773 exit0 warning-free; both public audits
F214scratch27630 standard-only; index2; lint80879 sixteen unrelated
unreachable modules, no BAG debt. This exact quantitative positive law is
the survivor of the proposed low-cost density transport mechanism.


**C24.2 — actual compact chi-amplitude variation (paper proof; Lean pending).**
Corpus source `ChiLogDerivHigherDerivatives.norm_iteratedDeriv_logDeriv_zetaChi_le`
gives every derivative order, in particular |(chi'/chi)'(z)|<=5/|Im z| on
-2<Re z<3 and |Im z|>=2. Its cached leaf exists; standard-axiom audit is
still required before adoption. For 0<=Re s<=1, tau>=4 and 2|Im s|<=tau,
the segment from 1/2+i*tau to s+i*tau stays in that strip with imaginary
part at least tau/2. Complex mean value therefore gives
|chi'/chi(s+i*tau)-chi'/chi(1/2+i*tau)|<=10*|s-1/2|/tau.
The exact quotient derivative then makes the common reflected row divided
by critical-line chi slowly varying: derivative norm <= row norm times
10*|s-1/2|/tau. Existing compact row bounds make its dyadic total variation
bounded uniformly in conductor. This pays height dependence of actual row
amplitudes. It does not bound the Fourier coefficient mass of a target
minorant or sum growing-support resonant terms; those remain the producer gap.


**C23.7 / F214 FINAL — polynomial density-cost energy vanishes, LEAN PROVED.**
`CompactGaussianDirichletDensityEnergy.lean` combines exact log-cost energy
with the original compact-channel C/log(N) bound. Every normalized finite
Dirichlet square density of cost <=N^A, for any fixed A, gives uniformly
vanishing actual window second moment. Final70110 exit0 warning-free; public
audit F215scratch81865 standard-only; index1; lint73177 fifteen unrelated
unreachable modules, no BAG debt. Actual weighted tail mass is the next leaf.


**C23.7 / F215 FINAL — polynomial density-cost concentration boundary, LEAN PROVED.**
`CompactGaussianDirichletDensityTail.lean` discharges all finite-polynomial
integrability/measurability obligations and proves weighted Markov for the
literal Dirichlet square density. Under every fixed polynomial frequency-cost
budget, weighted mass above every fixed positive normalized-window amplitude
vanishes uniformly. Final36637 exit0 warning-free; both public audits
F216scratch15452 standard-only; index6; lint36451 ten unrelated unreachable
modules, no BAG debt. The proposed polynomial-cost positive square-density
concentration certificate is excluded. Positive survivor: F212/F213 exact
occupation/log-cost energy law, paper and Lean closed. This does not exclude
signed transport mechanisms or prove anything about actual return counts.


**C24.1 / F216 FINAL — actual nonzero integer chi-grade oscillation, LEAN PROVED.**
`ZetaChiIntegerGradeOscillation.lean` proves the exact Hardy phase and both
derivatives for chi^k, for every integer k, then the physical subinterval
integral bound 6/sqrt(|k|/(100*T)) whenever k!=0 and [a,b] lies in [T,2*T],
T>=4. The estimate is uniform in the Dirichlet frequency. Final6077 exit0
warning-free; all four public audits F217scratch84172 standard-only; index5;
lint31218 ten unrelated unreachable modules, no BAG debt. Summing growing
support and selecting an actual self-return minorant remain open.

C24.2 literal-row consequence: multiply the slow row back by its exact
critical chi phase and apply C24.1 with integer grade one. The bounded
endpoint-plus-variation then gives a uniform square-root physical integral
bound for the full common reflected row times any Dirichlet frequency,
throughout every fixed compact right-strip disc. This keeps the actual
complex row, not a frozen or critical-line replacement. Its finite/growing
coefficient aggregate still needs an independent arithmetic estimate.


**C24.1 / F217 FINAL — integer chi grades with moving amplitudes, LEAN PROVED.**
`ZetaChiIntegerGradeAmplitude.lean` proves continuity and bounds each actual
integer-grade physical integral with complex differentiable amplitude by
6/sqrt(|k|/(100*T)) times its endpoint norm plus derivative variation.
Final24306 exit0 warning-free; both public audits F218scratch9881 standard-only;
index2; lint31621 thirteen unrelated errors (eleven unreachable modules,
two sorry occurrences in WeilFormConverseExplicitFormula), no BAG debt.
Actual compact-row amplitude variation remains the next obligation.


**C24.2 / F218 FINAL — actual compact chi-slope variation, LEAN PROVED.**
`ZetaChiCompactHeightVariation.lean` proves differentiability of chi'/chi
off the real axis and bounds its actual compact-strip displacement by
10*|s-1/2|/tau when 0<=Re s<=1, tau>=4 and 2|Im s|<=tau. The segment
mean-value proof reuses the corpus's all-order chi derivative bound, now
audited standard-only. Final38558 exit0 warning-free; both public audits
F219scratch27876 standard-only; index2; lint27295 eleven unrelated unreachable
modules, no BAG debt. Literal slow-row derivative assembly is next.


**C24.2 / F219 FINAL — literal slow reflected row, LEAN PROVED.**
`CompactGaussianSlowRow.lean` defines the actual common row divided by
critical-line chi, proves its exact quotient identity and norm preservation,
and identifies its height derivative through the actual chi-slope difference.
Derivative norm is bounded by row norm times 10*|s-1/2|/tau on the conductor
window. Final17044 exit0 warning-free; all four public audits F220scratch85195
standard-only; index5; lint1659 eleven unrelated unreachable modules, no BAG
debt. Compact uniform derivative and total variation are the next assembly.


**C24.2 / F220 FINAL — compact slow-row variation, LEAN PROVED.**
`CompactGaussianSlowRowVariation.lean` proves uniform compact bounds
|u|<=C and |u'|<=C/N throughout the dyadic conductor window, discharges
derivative integrability, and bounds endpoint norm plus total variation
by one constant independent of N. Final50575 exit0 warning-free; both
public audits F221scratch88541 standard-only; index2; lint18282 fourteen
unrelated unreachable modules, no BAG debt. Physical row integral follows.


**C24.2 / F221 FINAL — literal compact row physical cancellation, LEAN PROVED.**
`CompactGaussianRowOscillation.lean` bounds the physical integral of the
full reflected row times any Dirichlet frequency by C/sqrt(1/(100*N)),
uniformly on each compact right-strip disc and all sufficiently large N.
The proof retains the complex row and pays its exact height variation.
Scratch88541/final15566 exit0 warning-free; public audit15841 standard-only;
index1; lint7653 fourteen unrelated unreachable modules, no BAG debt.
C24.2 is closed. This is an individual-frequency upper estimate; an actual
self-target lower count and growing-support signed aggregate remain open.

**C25 — self-target structure and moving-cofactor transport (OPEN, source audit).**
The next producer must use the target f=riemannZeta itself. C23.2 forbids
silently treating the random arbitrary-holomorphic-target law as a physical
law. Searches for self-recurrence and self-target positive kernels returned
only the existing dual-target equivalence, the receiver, and generic kernel
positivity; none gives a physical lower count. A coefficient-positive
Dirichlet polynomial does not automatically make its value-return kernel
translation-positive: for F(z,w)=z+w, H=|F-2|^2 on two independent circles,
the mixed Fourier coefficient of H at z*conj(w) is +1. The same coefficient
of exp(-beta*H) is therefore -beta+O(beta^2), negative for small beta>0.
Thus positivity of the original coefficients alone cannot justify a Bochner
lower bound for the self-value kernel. This rules out that inference, not
all self-target kernels; no new Lean no-go is claimed.

A separate live possibility is to let the cofactor range grow with N, using
primes between N^alpha and N (alpha>1/2 at linear cutoff). F215 excludes
polynomial-cost square-density concentration only for each fixed ratio
window (N/D,N]. Its constant and threshold depend on D; substituting a
moving D is unjustified. For a growing cofactor range the actual energy may
remain order one, so the fixed-window argument does not settle it. Required
before formalization: a source-faithful joint compact cofactor energy law,
a positive self-target certificate, and a physical signed-error bound at
the same height. The existing largest-prime decomposition requires cutoff
L<Y^2; with L=n^3 and N=n^2 this forces alpha>3/4, not merely alpha>1/2.
No chosen moving window, certificate or count is yet proved.


**C25.1 — testing a short linear self-target certificate (paper proof).**
Let W=sum_p u_p X_p, B=sum_p b_p X_p over a finite prime set, and
D=a+B with |a|^2+sum|b_p|^2=1. Put V=sum|u_p|^2,
c=sum u_p*conj(b_p), and J=sum |u_p|^2|b_p|^2. Exact prime-pair
collisions give E|W|^2|B|^2=V*sum|b_p|^2+|c|^2-J,
E(W|D|^2)=a*c, and hence
E(|W-g|^2|D|^2)=V+|g|^2+|c|^2-J-2Re(conj(g)*a*c).
If |u_p|^2<=eta, then J<=eta and |a*c|<=sqrt(V)/2. Therefore
E(|W-g|^2|D|^2)>=3|g|^2/4-eta. Increasing conditional variance
alone cannot make this normalized linear square density certify small
mean-square error at a fixed nonzero self-target. This is only a boundary
for a linear positive mean-square certificate, not for signed minorants,
higher-degree densities, or actual recurrence. Positive survivor is the
exact collision/target-error identity, now selected for formalization.
Corpus search: 32 fourth-moment hits fully inventoried; existing real prime
fourth moment and general complex convolution Parseval do not already give
the mixed complex prime identity. General character fourth correlation and
prime product two-diagonal classification provide its source proof.

C25.1 scale refinement, still OPEN as an actual transport construction:
a coherent cofactor range D~log(N), with primes p~N/D, suggests individual
normalized channels of size D/sqrt(N) and conditional energy D/log(N).
These are scale calculations, not an established moving-D uniform theorem.
They explain why widening the window can remove the fixed-D energy decay,
but not why the physical target event occurs. Exact product-density cost
retains every prime product, while a degree-k truncation reaches frequencies
of order (N/D)^k. Neither finite-prime equidistribution nor a mean-square
bound over height N controls that target-selecting aggregate automatically.
C25.1's linear target-error identity tests the k=1 alternative without
assuming a conditional physical distribution. A future extension to short
integer supports would need the actual prime-degree decomposition and its
same-event retained target; neither is claimed here.


**C25.1 / F222 FINAL — exact complex prime mixed moment, LEAN PROVED.**
`SteinhausPrimeMixedFourthMoment.lean` proves
E|W|^2|B|^2=V_W*V_B+|sum u_p*conj(b_p)|^2-sum |u_p|^2|b_p|^2.
Both prime-pair matchings and their common diagonal are preserved. Scratch47754
and final58373 exit0 warning-free; public audit F223scratch64813 standard-only;
index2 (one private); lint31040 eleven unrelated unreachable modules, no BAG
debt. Exact target-error assembly is next; no physical count follows.


**C25.1 / F223 FINAL — exact linear-density target energy, LEAN PROVED.**
`SteinhausLinearPrimeTargetEnergy.lean` proves the actual total density mass
|a|^2+sum|b_p|^2 and decomposes the target-error product into its disjoint
constant, prime and prime-product frequencies. Parseval and F222 give the
exact error energy, retaining every collision. Scratch64813/final89723
exit0 warning-free; both public audits F224scratch23084 standard-only;
index2; lint8835 twelve unrelated unreachable modules, no BAG debt.
The quantitative nonzero-target floor is the next formal leaf.


**C25.1 / F224 FINAL — linear self-target mean-square floor, LEAN PROVED.**
`SteinhausLinearPrimeTargetGap.lean` proves the exact-diagonal lower bound
3|g|^2/4-sum |u_p|^2|b_p|^2 for every coefficient-normalized linear prime
square density. If each |u_p|^2<=eta, the error is at least 3|g|^2/4-eta.
Scratch23084/final69309 exit0 warning-free; both public audits56787 standard-only;
index2; lint75343 ten unrelated unreachable modules, no BAG debt. C25.1's
linear positive mean-square certificate is closed as a failed mechanism when
the target stays nonzero and maximal channel tends to zero. Positive survivor:
F222/F223 exact mixed collision law and target-energy decomposition, paper
and Lean closed. This does not exclude positive event mass, higher-degree
or signed certificates, moving retained targets, or physical recurrence.

**C26 — coherent chi stationary terms (OPEN; source and paper audit).**
C24 controls absolute atom sizes; a producer needs signed arithmetic sums.
Search for an actual chi stationary leading term found reflection identities
but no applicable aggregate lower theorem. The literal Hardy source currently
bounds rate error by O(1/t), giving only phase error o(t), insufficient to
retain a common oscillatory orientation. A stronger existing source is
HTGeometry.GammaDigammaStirlingBound.norm_digammaStirlingDefect_le:
|psi(z)-log(z)+1/(2z)|<=6/|z|^2 for Re(z)>0, |z|>=2.
It still needs current-toolchain axiom audit before reuse.

At z=1/4+i*t/2, t>=4, Q=|z|^2>=t^2/4 and
Re(1/(2z))=1/(8Q). Hence the Hardy rate differs from
(1/4)log(Q)-(1/2)log(pi) by at most 49/(16Q)<=49/(4t^2).
The exact radial logarithm correction is nonnegative and <=1/(16t^2),
so |theta'(t)-(1/2)log(t/(2*pi))|<=13/t^2. This paper bound is
integrable at infinity. It would give a fixed limiting phase offset and
O(1/t) phase error, preserving a common orientation without first identifying
the offset numerically. Formalize this exact bound and its integration before
any stationary leading term. A uniform stationary-phase remainder, coherent
integer-frequency aggregate, and self-return minorant are all still open;
no leading-term formula or physical count has been adopted as a premise.

C26 phase-model consequence (dependency-closed paper step, Lean pending):
integrating the 13/t² rate error gives a real constant C with
|theta(t)-thetaMain(t)-C|<=13/t. Set kappa=exp(-2*i*C), of norm one.
The elementary unit-circle Lipschitz inequality then gives, for every
integer k and t>=4,
|chi(1/2+i*t)^k-kappa^k*exp(i*k*(t-t*log(t/(2*pi))))|
<=26*|k|/t. This retains a common phase across all frequencies and includes
negative grades. The bound alone does not prove stationary-phase main terms
or control a growing coefficient aggregate; those remain separate tasks.


**C26 / F225 FINAL — integrable Hardy phase-rate error, LEAN PROVED.**
`HardyPhaseIntegrableError.lean` proves
|theta'(t)-(1/2)log(t/(2*pi))|<=13/t^2 for all t>=4, keeping the
real part of the reciprocal Stirling term. The reused complex digamma
bound is now axiom-audited standard-only. Corrected scratch58729 and
final80469 exit0 warning-free; public audit F226scratch29417 standard-only;
index1; lint47835 ten unrelated unreachable modules, no BAG debt. The
fixed phase-offset limit and quantitative phase error remain in scratch.


**C26 / F226 FINAL — fixed Hardy phase offset, LEAN PROVED.**
`HardyPhaseOffset.lean` defines the actual limiting offset and proves both convergence and the quantitative phase error <=13/t for t>=4. Corrected scratch15383/final51290 exit0 warning-free; both public audits F227scratch11528 standard-only. Index6 includes definition/private helpers; lint37406 ten unrelated unreachable modules, no BAG debt. The common-unit integer-grade model passed scratch11528 and is awaiting its final/audit.

C26.1 local coherent integer packets (dependency-closed paper step; Lean pending):
write a=2*pi*n, n>=1, t>=4 and D=t*log(t/a)-t+a. The inequalities
1-1/x<=log(x)<=x-1 give 0<=D<=(t-a)^2/a. The conductor phase at
frequency log(n) equals a-D, and exp(i*a)=1 exactly for integer n.
F227 and unit-circle Lipschitz therefore imply one common unit kappa with
|chi(1/2+i*t)*exp(i*t*log(n))-kappa|<=26/t+(t-2*pi*n)^2/(2*pi*n).
For t>=104 and every selected n satisfying (t-2*pi*n)^2<=2*pi*n/4,
the real part after rotation by conjugate(kappa) is at least 1/2.
Thus every finite sum with nonnegative real coefficients on this actual
stationary packet has rotated real part at least half its coefficient mass.
This is a signed physical aggregate on a localized integer window, with no
random phase or RH premise. It does not cover arbitrary complex cofactor
weights, the packet complement, or target-event minorants. Those are required
before any self-return count; no recurrence producer is claimed.


**C26 / F227 FINAL — coherent integer chi phase model, LEAN PROVED.**
`ZetaChiCoherentPhaseModel.lean` proves one fixed unit kappa approximates every integer chi grade by its conductor phase with error26abs(k)/t for t>=4. Scratch11528/final95020 exit0 warning-free; sole public audit F228scratch48678 standard-only; index1; lint89909 ten unrelated unreachable modules, no BAG debt. Negative grades included. Actual self-return count remains open.

C26.1 capacity audit (paper consequence; Lean pending, source audit pending):
local alignment does not make a square-root-width free-prime packet large.
The actual normalized channel has norm <=C/sqrt(N), uniformly in all phases,
cutoffs, heights and a fixed abscissa band, when 1<=N/p<=D. Existing
`Sieve.primesBetween_le_div_log` bounds every positive interval of length
H>1 by 292H/log(H) primes. Hence a sum of actual channels over primes in
any interval of length sqrt(N), N>1, has norm <=584C/log(N), uniformly even
with unit phase multipliers. This applies to every location, not only the
stationary center. For any fixed finite number of such windows it vanishes.
Thus a finite collection of narrow coherent prime packets cannot alone
synthesize a fixed nonzero normalized target. The positive survivors are
the exact complex aggregate error and common-direction lower bound from
C26.1, together with this quantitative capacity law. A growing collection,
wide signed transform or source-specific rare-event mechanism remains open;
the whole stationary route is not retired by this limited obstruction.


**C26.1 / F228 FINAL — integer stationary alignment, LEAN PROVED.**
`ZetaChiIntegerStationaryPackets.lean` proves the exact quadratic pointwise error from C26.1, uniformly for all positive integer frequencies and t>=4, with one fixed unit. Scratch69506 passed; final18948 passed warning-free after tactic cleanup. Public audit F229scratch99858 standard-only; index2 (includes private entropy helper); lint87231 ten unrelated unreachable, no BAG debt. Complex aggregate and positive cone consequences passed F229scratch99858, final/audits pending.


**C26.1 / F229 FINAL — signed packet sum and positive cone, LEAN PROVED.**
`ZetaChiStationaryPacketSums.lean` proves the exact complex-coefficient aggregate error and the common-direction half-coefficient-mass lower bound for nonnegative coefficients in the explicit stationary window, t>=104. Scratch99858/final40592 exit0 warning-free; both public audits25170 standard-only; index3 includes private rotation helper; lint40878 ten unrelated unreachable, no BAG debt. The actual prime-window capacity obstruction remains in scratch.

**C27 — growing cofactor physical mean (OPEN; investigation only).**
A fixed finite collection of sqrt(N)-width prime packets is too small under the pending C26.1 capacity law. A power-growing cofactor range could expose many centers for the composite frequencies p*k; the actual zero-phase height rotation includes both factors. A first-moment calculation would require a full stationary leading term with summed remainder, uniform in the growing range and compact target variable. It would still need a source-specific return minorant or deviation lower bound; a nonzero first mean is insufficient. The cubic cutoff enforces the existing seam Y^2>L, hence Y=N^alpha with alpha>3/4 when L=N^(3/2). No growing-cofactor mean, variance law, arithmetic density asymptotic or self-return count is assumed. Deep search77002 returned partial results with no applicable theorem. Continue from exact actual coefficients, not an independent product-law replacement.

C27.1 analytic next step (paper target; no Lean claim): a full stationary
leading term must control both the center and exterior tails. Put
D_a(t)=t*log(t/a)-t+a, a>0. For |t-a|<=a/2, the elementary log bounds give
|log(t/a)-(t-a)/a|<=2*((t-a)/a)^2. Applying the mean-value bound on the
segment from a to t gives
|D_a(t)-(t-a)^2/(2*a)|<=2*|t-a|^3/a^2.
Together with F227 this gives a local quadratic model for actual chi times
frequency log(a/(2*pi)), with error26/t+2*|t-a|^3/a^2, when t>=4.
On |t-a|<=R*sqrt(a), the integrated cubic error is O(R^4); after dividing
by sqrt(a), it vanishes for fixed R as a grows. The exterior model phase
has monotone derivative -log(t/a), bounded away from zero by a constant
multiple of R/sqrt(a) when t is between a/2 and 2a and outside the center;
a first-derivative integral bound would give O(sqrt(a)/R) tails. A verified
Fresnel limit then permits R to grow after taking the height limit. This
proposes a uniform stationary leading term; exact constants, endpoint
conditions and aggregate error must be formalized before use. No physical
first mean or recurrence conclusion follows from this paper sketch alone.


**C26.1 / F230 FINAL — actual narrow prime-packet capacity, LEAN PROVED.**
`CompactGaussianPrimePacketCapacity.lean` proves <=C/logN for sums of literal normalized channels over any prime interval of length sqrtN, for N>1, fixed abscissa band and 1<=N/p<=D. Uniform in all heights, retained phases, per-prime cutoffs and arbitrary unit-bounded multipliers. Corrected minimal-import scratch83400/final58908 exit0 warning-free; public audit F231scratch23187 standard-only; index4 includes private sieve-error helpers; lint34455 eleven unrelated unreachable modules, no BAG debt. Underlying BrunTitchmarsh source also standard-only audited. The narrow-prime-packet standalone synthesis mechanism is closed as insufficient for a fixed nonzero normalized target. Positive survivors F228/F229 physical phase alignment and exact complex sum error, plus F230 quantitative capacity law, are paper/Lean closed. This does not retire growing cofactor or wider signed aggregate mechanisms, nor prove a recurrence no-go.

C27.1 sharpened full-integral paper target (Lean pending): corpus search
found `GaloisForLFunctions.RHTower.norm_integral_quadPhase_conj_sub_le`
in `QuadraticPhaseStationary.lean`, giving the exact reversed Fresnel value
and error8/(mu*h). Current-toolchain axiom audit is still required.
For a>=8, 0<h<=a/2, a/2<=l<=a-h and a+h<=u<=2a, the intended bound is
|integral_l^u chi(1/2+i*t)*exp(i*t*log(a/(2*pi))) dt
 -kappa*exp(i*a)*sqrt(2*pi*a)*exp(-i*pi/4)|
<=78+4*h^4/a^2+40*a/h.
Derivation: actual conductor-model error <=26/t<=52/a integrated over
length<=3a/2 costs78; local cubic phase error bounded by2h^3/a^2 over
length2h costs4h^4/a^2; reversed Fresnel truncation costs8a/h; two
nonstationary tails cost16a/h each. All factors have unit norm except the
explicit sqrt main amplitude. This avoids a new improper-integral proof.
For integer saddles a=2*pi*n the exponential exp(i*a) is exactly one,
so the leading direction is common. Summing weighted errors and controlling
endpoints/actual cofactor masks remain required before a physical first
mean, and first means alone remain insufficient for the recurrence producer.

**C27.1 / F231 FINAL — cubic saddle entropy remainder, LEAN PROVED.**
`ChiStationaryQuadraticError.lean` proves
|t*log(t/a)-t+a-(t-a)^2/(2a)|<=2|t-a|^3/a^2 for a>0 and |t-a|<=a/2.
Corrected scratch17148/final42854 exit0 warning-free; public audit F232scratch14823
standard-only; index2 includes private log bound; lint48693 eleven unrelated
unreachable modules, no BAG debt. Only Mathlib log-derivative/MVT imports
remain in this leaf. The actual global entropy/local quadratic chi models
are being packaged with one shared unit before integration.


**C27.1 / F232 FINAL — shared global and quadratic chi models, LEAN PROVED.**
`ZetaChiStationaryQuadraticModel.lean` exposes one common unit for the global conductor entropy model (error26/t) and local quadratic saddle model (error26/t+2|t-a|^3/a²). Revised scratch80012/final63654 exit0 warning-free; public audit F233scratch6669 standard-only; index2 includes private phase-addition helper; lint72585 ten unrelated unreachable modules, no BAG debt. Source first-derivative test and reversed Fresnel integral theorem also axiom-audited standard-only in F233scratch6669. Full stationary integral still pending.

**C27.1 / F233 FINAL — both exterior model tails, LEAN PROVED.**
`ChiStationaryExteriorBound.lean` proves <=16a/h on either side of the
stationary point, for every comparable-height subinterval, for both phase
signs. Scratch6669/final75112 exit0 warning-free; both public audits
F234scratch79410 standard-only; index3 includes entropy definition;
lint48535 eleven unrelated unreachable modules, no BAG debt. Exact reversed
Fresnel and first-derivative source inputs audited standard-only. Central
quadratic approximation and these tails still need final assembly.


**C27.1 / F234 FINAL — actual chi integral model error, LEAN PROVED.**
`ZetaChiStationaryIntegralModel.lean` proves one common unit gives actualchi-to-conductor-model integral error at most78 on every interval a/2<=l<=u<=2a with a>=8. Scratch79410/final12949 exit0 warning-free; public audit F235scratch55342 standard-only; index1; lint5847 eleven unrelated unreachable modules, no BAG debt. Full pure-entropy stationary value is still being checked.

C27.2 next aggregate (paper consequence conditional only on completion of
C27.1 formal proof, not adopted as a Lean premise): set a_n=2*pi*n for
positive integers n. For any finite S, complex coefficients c_n and
positive margins h_n satisfying the full-integral endpoint conditions,
one common unit psi=kappa*exp(-i*pi/4) should give
|integral_l^u sum_(n in S) c_n*chi(1/2+i*t)*exp(i*t*log(n)) dt
 -psi*sum_(n in S) c_n*sqrt(2*pi*a_n)|
<=sum_(n in S) |c_n|*(78+4*h_n^4/a_n^2+40*a_n/h_n).
This follows by finite integral linearity, exact exp(i*2*pi*n)=1 and
triangle inequality. It retains complex coefficients and the full growing
support error. It would be a coherent physical aggregate, not yet a
self-target event lower count. Actual compact slow amplitudes, endpoint
bands, growing cofactor masks and a source-specific return minorant remain
required. Positive first means do not supply that minorant.


**C27.1 / F235 FINAL — full model stationary integral, LEAN PROVED.**
`ChiStationaryEntropyIntegral.lean` proves positive-interval integrability and the full reversed entropy stationary value with error4h^4/a²+40a/h, retaining the left and right exterior integrals. Corrected scratch93346/final30205 exit0 warning-free; both public audits F236scratch31298 standard-only; index4 includes private center helpers; lint24631 eleven unrelated unreachable modules, no BAG debt. Actualchi assembly passed scratch31298, final/audit pending.


**C27.1 / F236 FINAL — full actual chi stationary leading term, LEAN PROVED.**
`ZetaChiStationaryLeadingTerm.lean` proves one fixed unit kappa and the full actual critical-chi leading term kappa*exp(i*a)*sqrt(2*pi*a)*exp(-i*pi/4), with error78+4h^4/a²+40a/h under the explicit comparable-height endpoint/margin conditions. Scratch31298/final10008 exit0 warning-free; public audit F237scratch69915 standard-only; index1; lint79829 eleven unrelated unreachable modules, no BAG debt. All center/exterior/model errors retained. This is an integral theorem, not a physical self-return lower count.

**C27.2 / F237 FINAL — coherent finite physical sums, LEAN PROVED.**
`ZetaChiCoherentIntegralSum.lean` proves one fixed unit psi for every finite complex-coefficient physical integer-frequency sum with eligible saddles a_n=2*pi*n. Main term psi*sum c_n*sqrt(2*pi*a_n); exact total error sum |c_n|*(78+4h_n^4/a_n²+40a_n/h_n). Arbitrary finite/growing supports are allowed, but their complete weighted error must be paid. Scratch69915/final69220 exit0 warning-free; standalone audit87433 standard-only; index1; lint38776 ten unrelated unreachable modules, no BAG debt. C27.1/C27.2 analytical targets are closed. Actual compact slow amplitudes, endpoint bands, cofactor masks and a source-specific return minorant remain open; no physical mean asymptotic or event count is inferred.


**C28 — signed physical self-target minorant (OPEN).**
The next candidate uses a polynomial event minorant for the literal full reflected carrier, retaining all chi grades and the exact arithmetic phase of every mixed term. Neither positive first means nor product-law mass determines its physical sign. Before proposing a lower count, identify the fixed unit in C27 and audit the higher-grade terms; no such minorant or moment lower bound is assumed.

C28.1 phase identification (paper argument; Lean pending): the C27 unit should be kappa=exp(i*pi/4), so the integer-saddle integrated direction psi is exactly1. This follows from Gamma duplication and horizontal Gamma ratios without evaluating an absolute logarithmic Gamma constant. Put z=1/4+i*t/2, w=1/4+i*t, and write Gamma(z+1/2)=Gamma(z) exp(I_t), Gamma(w+1/4)=Gamma(w) exp(J_t). The exact integrated-digamma shifts give Im(I_t)->pi/4 and Im(J_t)->pi/8. Duplication gives Gamma(w)=Gamma(z)^2 exp(I_t-J_t) 2^(-1/2+i*t)/sqrt(pi). Taking conjugate ratios yields
chi(1/2+2i*t)=chi(1/2+i*t)^2 exp(-2i*t*log2) exp(-2i*(Im(I_t)-Im(J_t))).
The already formal conductor model has q(2t)=q(t)^2 exp(-2i*t*log2), hence its fixed unit satisfies kappa=kappa^2 exp(-i*pi/4), and unit nonvanishing forces kappa=exp(i*pi/4). Corpus `GammaShiftRatioAsymptotic`/`GammaShiftRatioTube` supplies horizontal ratios; source and toolchain audits are required before reuse. This identifies a sign needed by mixed-moment analysis; it does not establish a return-event minorant or count.


**C28.1 / F238 FINAL — exact horizontal Gamma log shift, LEAN PROVED.**
`GammaHorizontalLogShift.lean` defines the literal integrated digamma shift, proves its exact Gamma exponential identity, and proves both full complex asymptotic and imaginary limit lam*pi/2. Corrected scratch53582/final19887 exit0 warning-free; all three public audits F239scratch38575 standard-only. Index5 includes definition/private integrability helper. Lint38951 reports twelve unrelated unreachable leaves and one unrelated active sorry in ZetaLocalWindowTail; no BAG debt. The duplication identity is still being formalized, so the exact C27 leading unit is not yet promoted.

C28.2 certificate shape (OPEN, no positivity claim): for a finite compact-target error observable E(t)>=0 and a source-built finite chi/Dirichlet polynomial D(t), the signed expression (rho²-E(t))*|D(t)|² is nonpositive outside E(t)<rho². A positive physical integral, together with an explicit upper bound on |D|² inside that target event, would force a quantitative return count. This keeps the sign and the complete nonzero-chi mixed moments. C23.7 already forbids obtaining the needed concentration from a fixed polynomial-cost positive Dirichlet density under the independent product law; inserting chi grades requires actual physical mixed-moment estimates, not a product-law substitution. No D with a positive lower integral is yet constructed, and a finite-node observable still needs a compact-disc error transfer. Search of the existing signed-kernel/moment corpus is in progress.


**C28.1 / F239 FINAL — exact chi phase doubling, LEAN PROVED.**
`ZetaChiDuplicationPhase.lean` proves the critical chi factor's pi-phase/Gamma quotient and its exact doubling identity with the two literal horizontal shift corrections. Corrected scratch66174 passed; corrected final45174 exit0 warning-free after cast/style cleanup; both public audits F240scratch18497 standard-only. Index5 includes three private algebra helpers; lint85830 twelve unrelated unreachable leaves, no BAG debt. Combining this identity with the shift limits and conductor model is still in scratch; the limiting unit is not yet promoted.

C28.3 arithmetic cross-term target (paper consequence of pending exact phase identification): the existing `zetaChiCriticalDirichletCross` expands frequencies log(m/n), not only log of integers. Its grade-one saddle is a=2*pi*m/n, so the intended leading coefficient is sqrt(2*pi*a)*exp(2*pi*i*m/n). At fixed denominator n this is an additive residue-class character, with positive direction only on integer ratios. Thus identifying the unit does not make every mixed term positive. A complete signed finite cross transform should retain these rational phases and the full weighted saddle remainder; endpoint/nonstationary terms remain separate. This exposes an arithmetic matrix for a source-built certificate D. No additive-character sum, growing-modulus cancellation or positive target-kernel integral is assumed. A corpus search for an existing physical rational-saddle transform is in progress.


**C28.1 / F240 FINAL — exact conductor orientation, LEAN PROVED.**
`ZetaChiConductorOrientation.lean` proves exp(-2i*gammaHardyPhaseOffset)=exp(i*pi/4) from exact Gamma duplication and horizontal shift limits, then the explicit model for every integer grade with error26abs(k)/t. Corrected scratch82878 passed; final19543 exit0 warning-free after unit-exponential cleanup; both public audits F241scratch5988 standard-only. Index3 includes private continuity helper; lint45925 eleven unrelated unreachable leaves, no BAG debt. The real offset is not identified beyond this phase identity. Full explicit stationary integral and rational cross transform remain in scratch. No target-event lower count follows from phase identification alone.

C28.4 higher-grade analytical paper target (OPEN; no Lean draft): the phase identification also fixes the orientation of every higher chi grade. For a positive integer k, the exact entropy dilation is D_(k*a)(k*t)=k*D_a(t). Applying the full entropy integral at parameters (k*a,k*h,k*l,k*u) and dividing by k gives main sqrt(2*pi*a/k)*exp(-i*pi/4) and error4*k*h^4/a²+40*a/(k*h). The actual grade-k conductor error adds78*k, while its prefactor contributes exp(i*k*pi/4+i*k*a). Hence the intended actual main phase is exp(i*(k*a+(k-1)*pi/4)). At perfect-power arithmetic frequencies q=n^k, a=2*pi*n and the surviving grade phase is exp(i*(k-1)*pi/4), not universally+1. Negative grades should follow by conjugation. This must be formalized with exact dilation/endpoint conditions before expanding any signed target certificate; full mixed-grade moment sums and target positivity remain open.


**C28.1 / F241 FINAL — explicit actual stationary phase, LEAN PROVED.**
`ZetaChiExplicitStationaryTerm.lean` proves actual critical chi times frequency log(a/(2*pi)) has full integral leading term exp(i*a)*sqrt(2*pi*a), with the unchanged error78+4h^4/a²+40a/h and all comparable-height endpoint/margin conditions. Corrected scratch88544 passed; final54915 exit0 warning-free; public audit F242scratch66110 standard-only; index2 includes private pointwise model; lint98381 twelve unrelated unreachable leaves, no BAG debt. Integer saddles now have positive real leading value; rational saddles retain their signed additive phase. No physical return-event lower bound is inferred.


**C28.3 / F242 FINAL — signed finite physical transform, LEAN PROVED.**
`ZetaChiFiniteStationaryTransform.lean` proves the complete coefficient-weighted stationary transform for finite real frequencies, preserving exp(2*pi*i*x). A second theorem covers an arbitrary complete finite family and any eligible selected saddle subset: every unselected term is charged the existing actual chi O(sqrt(T)) bound, with its full coefficient norm. Rational-frequency phases are periodic in the numerator modulo the denominator. Corrected scratch58997/final45407 exit0 warning-free; all3 public audits F243scratch71918 standard-only; index5 includes2 private helpers; lint26865 ten unrelated unreachable leaves, no BAG debt. The signed residue-class sums and complementary error may still be large. This is no target-event lower bound.


**C28.4 / F243 FINAL — exact graded entropy dilation, LEAN PROVED.**
`ChiGradedStationaryEntropy.lean` proves integrability for every real grade on positive compact intervals, exact simultaneous entropy scaling and integral dilation, and the full positive-real-grade model error4*k*h^4/a²+40*a/(k*h). The exact main scalar is k^-1*sqrt(2*pi*k*a), with reversed Fresnel phase. Corrected scratch91830/final2768 exit0 warning-free; all4 public audits F244scratch2987 standard-only; index4; lint82782 eleven unrelated unreachable leaves, no BAG debt. Actual higher-chi-grade assembly and negative grades remain in scratch.

C28.4 grade-cost audit (paper calculation, not an additional Lean claim): choosing h=a^(3/5)*k^(-2/5) in the proposed positive-grade estimate gives stationary remainder44*a^(2/5)*k^(-3/5), plus78*k from the actual conductor model. Relative to sqrt(2*pi*a/k), these are (44/sqrt(2*pi))*(a*k)^(-1/10) and (78/sqrt(2*pi))*k^(3/2)/sqrt(a). Thus the analytical error can in principle accommodate growing grades k<=a^eta with eta<1/3, provided the stated interior margin fits the endpoints. This does not control the sum of coefficient norms, rational/root phases, the complement or target-event positivity; those remain separate arithmetic requirements. No uniform growing-grade limit theorem is yet formalized.


**C28.4 / F244 FINAL — actual positive-grade stationary value, LEAN PROVED.**
`ZetaChiPositiveGradeStationary.lean` proves every positive Nat grade k has full main scalar k^-1*sqrt(2*pi*k*a), phase exp(i*(k*a+(k-1)*pi/4)), and full remainder78*k+4*k*h^4/a²+40*a/(k*h) under the stated interior saddle conditions. Corrected scratch57421/final90118 exit0 warning-free; public audit F245scratch78577 standard-only; index2 includes private pointwise model; lint71177 eleven unrelated unreachable modules, no BAG debt. Negative grades passed scratch; no aggregate signed lower bound or physical recurrence count is inferred.

C28.5 full signed-grade audit (paper consequence of C28.4): for every nonzero integer k, put mu=abs(k), A(k,a)=mu^-1*sqrt(2*pi*mu*a), and theta(k,a)=k*a+(k-k/mu)*pi/4. Positive and negative-grade conjugation give actual main A(k,a)*exp(i*theta(k,a)) and error78*mu+4*mu*h^4/a²+40*a/(mu*h). For an arbitrary complete finite family of nonzero grades, select any subset of eligible interior saddles and retain its complex coefficient-weighted main sum. Charge every unselected term its full coefficient norm times6/sqrt(mu/(100*T)). This gives a complete signed physical transform, including root/rational phases, not positivity. Grade-zero terms and actual height-dependent compact amplitudes remain separate. Candidate next test: whether a source-built resonator makes the full target-error quadratic form strictly positive after these costs; no such resonator is assumed.

C28.6 height-dependent amplitude audit (paper target, not a Lean claim): constant-coefficient stationary matrices do not yet apply to actual compact rows. For a complex differentiable amplitude v with norm(v)<=U and norm(v-prime)<=L on [l,u], splitting at a+-h gives a model freezing correction at most2*L*h²+40*L*a²/(k*h) for k>0. The central bound uses norm(v(t)-v(a))<=L*abs(t-a); each exterior bound follows by Abel summation and the graded entropy primitive bound16*a/(k*h). The left endpoint plus derivative variation costs at most L*a/2; the right costs at most2*L*a, hence total40*L*a²/(k*h). Add norm(v(a))*(4*k*h^4/a²+40*a/(k*h)) for the pure model, and78*k*U for the actual conductor approximation. At L=O(U/a) the freezing error is smaller than U*sqrt(a/k) for suitable h, but coefficient sums and target positivity still require independent arithmetic control. No frozen-amplitude replacement is assumed.


**C28.4 / F245 FINAL — exact negative-grade conjugation, LEAN PROVED.**
`ZetaChiNegativeGradeStationary.lean` proves every negative natural chi grade with reversed frequency is the exact complex conjugate of its positive partner. Its full stationary value has conjugate phase and identical amplitude/remainder. Scratch78577/final50494 exit0 warning-free; both public audits F246scratch91635 standard-only; index2; lint51379 ten unrelated unreachable modules, no BAG debt. Complete mixed-grade summation remains in scratch; physical target-kernel positivity remains open.


**C28.5 / F246 FINAL — complete mixed-grade physical transform, LEAN PROVED.**
`ZetaChiMixedGradeStationaryTransform.lean` gives an explicit signed stationary value for every nonzero integer grade, combines arbitrary positive/negative grades with their full complex coefficients, and covers complete finite support by retaining selected main terms and charging every complementary term6*norm(c)/sqrt(abs(k)/(100*T)). Corrected scratch64020/final58749 exit0 warning-free; all3 public audits F247scratch68064 standard-only; index7 includes2 definitions/2 private helpers; lint87464 ten unrelated unreachable modules, no BAG debt. The full signed sum and error are explicit; no source-built coefficient choice with positive target integral is proved.


**C28.6 / F247 FINAL — graded exterior amplitudes, LEAN PROVED.**
`ChiGradedExteriorAmplitude.lean` proves global continuity of every real-grade entropy phase, the full positive-grade exterior primitive bound16*a/(k*h), and its complex-amplitude version with the complete endpoint-plus-derivative-variation cost. Scratch68064/final86332 exit0 warning-free; all3 public audits F248scratch64234 standard-only; reused Abel and continuous_mul_log audits standard-only; index3; lint54827 eleven unrelated unreachable modules, no BAG debt. Full saddle freezing passed scratch and still awaits final/audit.

C28.7 actual compact-row stationary target (paper consequence of C28.6): the existing exact factorization is reflectedCompactGaussianRow(s,N,t)=compactGaussianSlowRow(s,N,t)*chi(1/2+i*t). Uniformly on any fixed right-strip disc, the slow row has norm<=C and derivative norm<=C/N on [N,2N], with integrable derivative. Thus each eligible saddle a has actual row main compactGaussianSlowRow(s,N,a)*sqrt(2*pi*a)*exp(i*a), with full error bounded by C*(78+2*h²/N+40*a²/(N*h)+4*h^4/a²+40*a/h). The coefficient is evaluated at that saddle, not at a common frozen height. This closes an actual-source amplitude requirement if formalized; it still leaves cofactor/endpoint coefficient summation and the signed self-target minorant unresolved.


**C28.6 / F248 FINAL — full saddle-amplitude freezing, LEAN PROVED.**
`ChiStationaryAmplitudeFreezing.lean` derives norm(v(t)-v(a))<=L*abs(t-a) from the actual derivative bound, and proves full freezing error2*L*h²+40*L*a²/(k*h) with both exterior intervals retained. It then supplies the full graded model stationary value with the literal factor v(a) and its complete weighted phase remainder. Scratch64234/final28148 exit0 warning-free; both public audits F249scratch28149 standard-only; index2; lint32635 eleven unrelated unreachable modules, no BAG debt. Actual chi assembly passed scratch; no physical return count follows from freezing alone.


**C28.6 / F249 FINAL — actual chi with full complex amplitude, LEAN PROVED.**
`ZetaChiAmplitudeStationary.lean` proves the full actual positive-grade stationary value v(a)*k^-1*sqrt(2*pi*k*a)*exp(i*(k*a+(k-1)*pi/4)). All errors remain explicit:78*k*U+2*L*h²+40*L*a²/(k*h)+norm(v(a))*(4*k*h^4/a²+40*a/(k*h)), given the actual amplitude/derivative bounds and integrable derivative. Scratch28149/final27856 exit0 warning-free; public audit F250scratch50084 standard-only; index2 includes private pointwise conductor model; lint57508 twelve unrelated unreachable modules, no BAG debt. No certificate positivity is assumed or proved.

C28.8 canonical saddle coefficient audit (OPEN; paper mechanism only): set delta=s-1/2. The exact critical logarithmic derivative is -2*gammaHardyPhaseRate(t), so its difference from -log(t/(2*pi)) has norm<=26/t². Along the compact complex segment from1/2 to s, the existing log-slope difference bound gives an intended normalized ratio chi(s+i*t)/chi(1/2+i*t)*exp(delta*log(t/(2*pi)))=exp(E_s(t)), with norm(E_s(t))<=26*norm(delta)/t²+10*norm(delta)^2/t. Derive this from the actual nonvanishing chi factor along the segment; no zeta nonvanishing is used. Consequently the slow-row model should be exp(delta*log(2*pi*N/t)) times this controlled relative error. At integer saddle t=2*pi*n, multiplying by the literal unweighted dual coefficient N^(1/2-s)*n^(s-1) and the stationary scalar2*pi*sqrt(n) cancels the compact s-dependence in the leading value, leaving2*pi. This identifies the canonical dual coefficient only; smoothing/cofactor masks, full pole/primal cancellation and mixed target-error moments must still be retained. No full reflected mean or recurrence conclusion follows.


**C28.7 / F250 FINAL — literal compact-row stationary main, LEAN PROVED.**
`CompactGaussianRowStationary.lean` proves, uniformly on every fixed right-strip disc, the actual reflected row has main compactGaussianSlowRow(s,N,a)*sqrt(2*pi*a)*exp(i*a), with full errorC*(78+2*h²/N+40*a²/(N*h)+4*h^4/a²+40*a/h) at every eligible interior saddle. The coefficient is the literal slow row at that saddle. Corrected scratch26548/final25587 exit0 warning-free; public audit F251scratch42863 standard-only; index1; lint99266 twelve unrelated unreachable modules, no BAG debt. Cofactor/mixed-moment summation and a positive self-target minorant remain open.


**C28.8 / F251 FINAL — full complex conductor log slope, LEAN PROVED.**
`ZetaChiConductorLogSlope.lean` proves the full complex critical chi slope differs from -log(t/(2*pi)) by at most26/t², and every compact strip shift differs by at most10*norm(s-1/2)/t+26/t² under the explicit conductor-window conditions. Scratch42863/final64271 exit0 warning-free; both public audits F252scratch59648 standard-only; reused critical-slope/compact-shift audits standard-only; index2; lint15095 ten unrelated unreachable modules, no BAG debt. Exact segment integration and normalized ratio error remain in scratch.


**C28.8 / F252 FINAL — exact normalized chi transport, LEAN PROVED.**
`ZetaChiSegmentLogRatio.lean` defines the literal segment integral of chi logarithmic slope and proves both exact shift quotient=exp(segmentLog) and its conductor-normalized exponential form. The strict-strip chi nonvanishing follows from the Gamma factors; zeta nonvanishing is not used. Corrected scratch49985/final33013 exit0 warning-free; both public audits F253scratch83428 standard-only; imported interval FTC and ZetaNotch continuity audits standard-only; index3 includes definition; lint82011 eleven unrelated unreachable modules, no BAG debt. The quantitative error bound remains in scratch.

C28.8 actual-atom handoff (paper consequence, Lean draft pending): b(s,N,n)=n^(s-1)/(sqrt(N)*N^(s-1)) cancels the compact-row normalization exactly. Multiplying the full F250 integral by b and applying the canonical saddle bound gives the literal unweighted dual atom chi(s+i*t)*n^(s-1)*exp(i*t*log n) main2*pi with errornorm(b)*C*E(N,2*pi*n,h)+K(s)/n. No smoothing, cofactor or complementary term is absorbed into this statement. With n comparable to N and h=N^(3/5), the expected single-atom error is O(N^(-1/10)); coefficient normalization and growing-support summation still need proof. Even a positive unweighted first mean is not the signed target-error lower integral.


**C28.8 / F253 FINAL — quantitative normalized chi error, LEAN PROVED.**
`ZetaChiNormalizedShiftBound.lean` proves the exact segment error bound26*norm(delta)/t²+10*norm(delta)^2/t, and actual normalized chi ratio differs from1 by at most(52*norm(delta)+20*norm(delta)^2)/t above the explicit compact-shift threshold. Corrected scratch29131/final74560 exit0 warning-free; both public audits F254scratch46975 standard-only; index2; lint52896 eleven unrelated unreachable modules, no BAG debt. Canonical saddle cancellation remains in scratch.


**C28.8 / F254 FINAL — canonical positive integer saddle, LEAN PROVED.**
`ZetaChiCanonicalSaddleCoefficient.lean` proves exact cancellation of the unweighted dual power and stationary square root into2*pi times the normalized actual chi ratio. Every real frequency retains exp(2*pi*i*x); integer saddles have positive leading value2*pi with error(52*norm(delta)+20*norm(delta)^2)/n under explicit height thresholds. Corrected scratch4534/final55051 exit0 warning-free; all3 public audits F255scratch8479 standard-only; index5 includes definition/private power helper; lint44251 thirteen unrelated unreachable modules, no BAG debt. This is the canonical unsmoothed coefficient, not a full AFE mean or target-event count.

C28.9 growing physical first-mean target (OPEN): the exact reflected finite carrier has literal summands chi(s+i*t)*n^(s-1)*exp(i*t*log n)*smoothAFECutoff(n/N). The cutoff is independent of t, so it can be retained as its exact coefficient in the integer-saddle sum. For N=m^10 and marginh=m^6, the complete normalized single-atom stationary cost should be <=648*pi*C/m, plusK(s)/n. A finite interior block therefore has main2*pi*sum cutoff(n/N) and the complete weighted error. This would expose a physical arithmetic bias absent from the centered independent phase law. The complete carrier still requires all endpoint/exterior terms; a positive first mean does not supply the signed self-target minorant. Source handoff checked in CompactGaussianReflectedCarrierIdentity retained/frozen identities. No target lower bound or full mean is assumed.


**C28.8 / F255 FINAL — literal dual atom stationary integral, LEAN PROVED.**
`ZetaChiDualAtomStationary.lean` defines the exact row-normalizing dual coefficient, proves its row/saddle cancellation, and proves the actual unsmoothed dual summand chi(s+i*t)*n^(s-1)*exp(i*t*log n) has integral2*pi with complete errornorm(b)*C*E(N,2*pi*n,h)+K(s)/n. Uniform on fixed right-strip discs with explicit eligible-saddle/size conditions. Corrected scratch89552/final69768 exit0 warning-free; all3 public audits F256scratch98565 standard-only; index4 includes definition; lint88732 twelve unrelated unreachable modules, no BAG debt. Uniform small error and literal cutoff-weighted summation remain in scratch.

C28.9 cutoff positivity paper sublemma (not yet Lean): the literal derivative ofReV(x) is strictly negative forx>0, since exp(-(logx)^2/4)/(2*sqrt(pi)*x)>0. Strict antitonicity plus the already provedV(x+1)>=0 givesV(x)>0. Together withImV=0, each actual cutoff weight is positive real and its norm equals its real part. Hence a complete relative errorD/m times the sum of the cutoff weights preserves a positive interior-block first mean for largem. This is a first-moment fact only; it neither controls omitted terms nor bounds target-error energy. Corpus strict-cutoff lexical0 and exhaustive relevant-name source search found no existing strict-positivity theorem.

C28.9 concrete growing block (paper plan, no Lean claim): take the F258 parameterq=5m, heightN=q^10, and the literal integer block S_m=[5^9*m^10,6*5^8*m^10]. The bounds3<pi<4 place every saddle2*pi*n between(6/5)N and(48/25)N. For m>=1 both endpoint margins dominateq^6. The block has cardinality5^8*m^10+1>=N/25, while0<n/N<=6/25<1 forces each Gaussian cutoff weight at leastV(1)>0 by antitonicity. The intended complete relative-error interior transform then gives an actual smoothed physical integral real part>=pi*V(1)*N/25 eventually, uniformly on the compact disc. This exposes a quantitative growing-support physical first mean. It retains the chosen block exactly and says nothing about the sign of the full complementary carrier or the target-error quadratic form.


**C28.9 / F256 FINAL — uniform actual dual coefficient scale, LEAN PROVED.**
`ZetaChiDualCoefficientBound.lean` proves exactnorm(b)=(N/x)^(1-Re(s))/sqrtN andnorm(b)<=M/sqrtN when0<x<=N<=M*x andRe(s)>=0. Every dyadic saddleN<=2*pi*x<=2N therefore hasnorm(b)<=2*pi/sqrtN, uniformly inIm(s). Corrected scratch39318/final14007 exit0 warning-free; all3 public audits F257scratch16576 standard-only; index3; lint21825 ten unrelated unreachable modules, no BAG debt. Complete small-remainder and growing-block summation remain in scratch.

C28.10 physical leading-profile audit (OPEN conjecture): the canonical integer-saddle main2*pi is independent of the compact variable s. Thus any complete eligible block with fixed nonnegative weights independent of s has a constant leading first-mean profile, uniformly on the disc, once F258/F259 close. This rules out synthesizing a nonconstant compact target from that first mean alone, but not from higher mixed moments or signed target certificates. A stronger source question is whether stationary Poisson summation identifies the actual heightwise or mean-square block profile, retaining every endpoint and nonzero Poisson frequency. No such variance collapse or profile theorem is assumed. Corpus search for that exact mechanism is in progress.

C28.10 sharper paper conjecture (UNPROVED): on the explicit blockn/N in[1/5,6/25], Poisson frequencyk has stationary pointn=t/(2*pi*k). For t/N in[1,2], the bounds3<pi<4 exclude k>=2 and k<=0; onlyk=1 can be stationary. Away from the two resulting height edges, its stationary factor should cancel the actual chi factor and leave the s-independent profile V(t/(2*pi*N)) times the indicator thatt/(2*pi*N) lies in[1/5,6/25]. An integrated or mean-square version must retain the transition bands and sum every nonstationary Poisson mode. This would explain the already targeted positive first mean as a deterministic profile, not arbitrary compact-target synthesis. It is a conjecture to audit, not a premise for current Lean work.


**C28.9 / F257 FINAL — complete decaying saddle remainder, LEAN PROVED.**
`ZetaChiDualSaddleRemainder.lean` proves thatN=m^10,h=m^6 andN<=a<=2N make the complete coefficient-normalized stationary error at most648*pi*C/m, for m>=1. Every central, exterior and conductor cost remains included. Corrected scratch79288/final98032 exit0 warning-free; public audit F258scratch65510 standard-only; index1; lint75315 ten unrelated unreachable modules, no BAG debt. Actual uniformly-small atom assembly remains in scratch.


**C28.9 / F258 FINAL — uniform actual dual atom asymptotic, LEAN PROVED.**
`ZetaChiDualAtomUniform.lean` proves every integer saddle at marginm^6 inside[m^10,2*m^10] has literal dual-atom integral2*pi+O(1/m), uniformly across each fixed closed right-strip disc. All analytic height/compact-shift conditions are derived, leaving only the literal interior geometry. Corrected scratch5140 passed; final90383 exit0 warning-free after style cleanup; public audit F259scratch37468 standard-only; index1; lint11028 ten unrelated unreachable modules, no BAG debt. Full coefficient-weighted interior sums remain in scratch.

C28.11 next signed-certificate bottleneck (OPEN): all current finite mixed-grade transforms pay the full sum of coefficient norms. A polynomial target minorant with growing degree expands into many prime-product frequencies; the absolute coefficient sum can overwhelm the single-term stationary saving even when its quadratic coefficient energy is small. After finishing the actual interior first-mean source, test an aggregate quadratic-form estimate for the complete signed stationary matrix, retaining rational/root phases, every grade, endpoints and actual compact amplitudes. A useful replacement must control the real signed target-error integral, not merely an unsigned norm. No square-sum error bound, positive eigenvalue, physical concentration or explicit resonatorD is assumed. Corpus operator inventory is in progress.

C28.9 scale handoff: N=(5m)^10=((5m)^5)^2 lies exactly on the square-cutoff height schedule of FullReflectedAFECompactTarget. The planned block lower bound therefore uses the literal full-source cutoff and height window, not an independent smoothing radius or incompatible scale. The exact per-atom equality to smoothAFEZetaRightReflectedPrimalPositiveCoefficient is in F260 scratch; the full complement/pole and target-error contributions remain unestimated by this block result.


**C28.9 / F259 FINAL — complete weighted interior first mean, LEAN PROVED.**
`ZetaChiDualWeightedInteriorMean.lean` defines the literal physical dual atom, proves strict positivity of the actual Gaussian cutoff on the positive ray, and proves the full finite nonnegative-weight interior transform has main2*pi*sum weights and error<=D/m*sum weights, uniformly on each fixed compact disc. Every selected coefficient is retained; the relative error has no support-size loss. Corrected scratch98642/final96613 exit0 warning-free; both public audits F260scratch90715 standard-only; imported cutoff derivative/nonnegative audits standard-only; index5 includes definition/two private helpers; lint45368 eleven unrelated unreachable modules, no BAG debt. Literal smoothed-source specialization remains in scratch.

C28.9 source-scope caution / next paper audit: the explicit integer block includes the retained smooth background; it is not the free-prime window alone. At fixed cofactor boundH, integers with a selected prime factorp>N/H lie among pairs(p,k) withk<=H, so a prime-count upper boundO(N/logN) would give onlyO_H(N/logN) such terms. F259 withliteral cutoff weights<=1 would then make their normalized physical first meanO_H(1/logN), leaving the order-one block mean primarily in the retained part. This counting/specialization is not yet formalized; verify source prime-count and exact window definitions before using it. Neither the full block positivity nor this proposed decomposition supplies target-error concentration.


**C28.9 / F260 FINAL — literal smoothed-source first mean, LEAN PROVED.**
`ZetaChiDualSmoothedInteriorMean.lean` proves exact equality of the cutoff-weighted dual atom and the actual reflected primal positive coefficient at smoothing parameter1. Every eligible finite interior block eventually has real integral at leastpi times its complete actual Gaussian coefficient mass, uniformly on the compact disc. Corrected scratch68296/final48738 exit0 warning-free; both public audits F261scratch65223 standard-only; imported literal source and cutoff-imaginary audits standard-only; index2; lint62554 ten unrelated unreachable modules, no BAG debt. Explicit growing-block cardinality and length-order lower bound passed scratch, final/audit pending.


**C28.9 / F261 FINAL — explicit growing physical block, LEAN PROVED.**
`ZetaChiDualCoherentBlock.lean` proves the exact cardinality of S_m=[5^9*m^10,6*5^8*m^10], every required saddle margin at N=(5m)^10, and the literal Gaussian-weighted block integral has real part at least kappa*N eventually, uniformly on the compact disc, with kappa=pi*V(1)/25>0. Scratch65223/final17571 exit0 warning-free; standalone audit67643 all3 publics standard-only; index4 includes definition; lint36140 eleven unrelated unreachable modules, no BAG debt. This closes the selected growing-support first-mean construction. The block includes retained background, so free-window allocation, full complementary carrier and signed target-error positivity remain separate requirements. No recurrence count follows.

C28.12 retained/free allocation (paper target, not yet Lean): for integer cofactor budget H>=1 and N>=H², each p in largePrimes(N,N/H) satisfies p>H and N<p². Chebyshev sum(log p)<=N log4 then gives card(largePrimes)*logN<=2Nlog4. Every positive n<=N divisible by one such p has n=p*k with k<H, so any complete selected free subset has card*logN<=2H*Nlog4. For the F261 interior block, F259 and 0<V<=1 should imply a complete free-block physical integral norm<=C_H*N/logN, uniformly on the fixed disc. Removing it from F261 leaves an order-one positive retained-block real mean. This is a source-allocation law, not a recurrence obstruction or a statement about the whole cubic cofactor tail. It will prevent misidentifying the constant first-mean bias as an independent free-window producer. No quantitative growing-H target synthesis is assumed.


**C28.12 / F262 FINAL — complete free-window occupancy, LEAN PROVED.**
`PrimeWindowMultiplicity.lean` defines the literal free-prime-supported part of any finite integer support and proves card*logN<=2H*Nlog4 when1<=H andH²<=N. Proof uses the exact Nat floor window, prime Chebyshev and complete prime/cofactor image; no uniqueness or density premise. At fixedH its occupancy is o(N), uniformly across all supports0<n<=N. Corrected scratch57833/final55416 exit0 warning-free; all4 public audits F263scratch43037 standard-only; index5 includes definition. Lint42103 reports twelve unrelated unreachable modules and unrelated proof debt in HTGeometry/BoundedStripAlmostPeriodicThreeLines:155, no BAG debt. Actual physical mean allocation remains in scratch.

C28.13 sharper moving-cofactor first-mean allocation (new paper conjecture): F262 bounds all prime/cofactor pairs by H times the largest prime count. Keeping the product cutoff p*k<=N separately should instead give card(free)*logN<=2Nlog4*sum_(1<=k<=H)1/k<=2Nlog4*(1+logH), whenever H²<=N. Indeed every p>N/H has logp>=logN/2, while its k-th slice is bounded by Chebyshev at floor(N/k). Thus the complete free-block physical first mean should remain o(N) for every logH=o(logN), including logarithmic H. This is sharper than the crude H/logN estimate and exposes the polynomial-cofactor boundary of this first-moment mechanism. It does not exclude rare phase-conditioned target events, higher signed moments, or the entire cubic source tail; C25's conditional-energy mechanism must not be confused with unconditional first-mean mass. Search for existing harmonic multiplicity tools before formalizing.


**C28.12 / F263 FINAL — uniform physical subset means, LEAN PROVED.**
`ZetaChiDualBlockSubsetMean.lean` proves every complete subset of the concrete growing block has actual Gaussian-weighted real integral>=pi*V(1)*card and norm<=(2*pi+1)*card, uniformly on the fixed compact disc. The block's positive/cutoff support is explicit. Corrected scratch73875/final90745 exit0 warning-free; both public audits F264scratch82619 standard-only; index2; lint5902 fourteen unrelated unreachable modules, no BAG debt. Exact retained support and physical free/retained allocation passed initial scratch except one redundant tactic; final still pending.


**C28.12 / F264 FINAL — physical retained/free allocation, LEAN PROVED.**
`ZetaChiDualRetainedAllocation.lean` identifies the complementary integer support exactly with the literal retained-prime support. Its complete free-block norm integral timeslogN is <=2Hlog4*(2*pi+1)*N, uniformly forH²<=N. FixedH gives free mean o(N), while the retained block has real integral>=pi*V(1)*N/50 eventually. Corrected scratch93868/final52337 exit0 warning-free; all4 public audits F265scratch96891 standard-only; index4; lint32779 twelve unrelated unreachable modules, no BAG debt. No event count or statement about the whole cubic cofactor tail follows. C28.13 harmonic improvement passed scratch, final/audit pending.

C28.14 signed rational-saddle aggregate (paper target, OPEN): for the literal grade-one phase exp(2*pi*i*a*n/q), the complete q-residue sum is zero unless q divides a, in which case every phase is one. For q not dividing a, periodic zero-block sums give every unweighted partial sum norm<=q; Abel summation against the actual decreasing Gaussian cutoff then bounds the complete weighted main byq*V(start/N), independent of the integer block length. This can reduce a rational mixed-moment main before paying its stationary remainder. It does not apply automatically after a prime/cofactor mask destroys the complete residue blocks, and it does not bound the full stationary error matrix. The physical coefficient rescaling, eligible endpoints, growing denominators and actual signed self-target quadratic form remain required. Source inventory found exact Complex exponential/divisibility and existing finite Dirichlet-test norm bounds, but no BAG rational aggregate specialization. No positive certificate D is constructed.


**C28.13 / F265 FINAL — harmonic cofactor occupancy, LEAN PROVED.**
`PrimeWindowHarmonicMultiplicity.lean` keeps p*k<=N in every complete cofactor slice and proves card(free)*logN<=2Nlog4*sum_(1<=k<=H)1/k<=2Nlog4*(1+logH), uniformly for1<=H,H²<=N and every selected positive support<=N. No masked terms are discarded. Scratch96891/final36628 exit0 warning-free; both public audits F266scratch30073 standard-only; imported harmonic bound standard-only; index3 includes private slice lemma; lint75431 twelve unrelated unreachable modules, no BAG debt. Physical harmonic bound and its necessary power-size cofactor floor remain in scratch.

C28.14 actual coefficient handoff (paper derivation, not yet Lean): for positive ratio xi=a/q, the literal cross atom chi(s+it)*n^(s-1)*exp(i*t*log(n*xi)) equals xi^(1-s) times the real-frequency dual atom atx=n*xi. The canonical main is therefore2*pi*xi^(1-s)*exp(2*pi*i*n*xi), with the unchanged uniform real-atom error multiplied bynorm(xi^(1-s)). Combining complete Gaussian residue cancellation with full finite weighted errors should bound an eligible lengthK block bynorm(xi^(1-s))*(2*pi*q+D*K/m) when q does not dividea, onN=m^10. This preserves the actual complex ratio coefficient and every selected error. It would control off-divisibility first cross moments for short denominators; a complete mixed-grade target-error matrix, all ineligible terms and actual return-event lower count remain open. Real-frequency extension of the atom theorem is drafted separately so integer positivity is never substituted at rational saddles.


**C28.13 / F266 FINAL — moving-cofactor physical first-mean boundary, LEAN PROVED.**
`ZetaChiDualHarmonicAllocation.lean` proves the complete free-block norm integral timeslogN is <=C*(1+logH)*N, C=2log4*(2*pi+1), uniformly inH²<=N. Any such actual norm integral>=rho*N forcesH>=exp(rho*logN/C-1). Conversely100log4*(1+logH)<=logN preserves a retained real mean>=pi*V(1)*N/50. These explicit source inequalities identify the first-moment power-cofactor boundary, without assuming any target-event law. Corrected scratch43475 passed; corrected final79598 exit0 warning-free after style cleanup; all3 public audits F267scratch80947 standard-only; index3; lint49600 ten unrelated unreachable modules, no BAG debt. No recurrence route is retired.


**C28.14 / F267 FINAL — complete signed rational saddle cancellation, LEAN PROVED.**
`ZetaChiRationalSaddleCancellation.lean` proves exact rational phase powers, complete q-residue sum=q ifq dividesa and0 otherwise, translated partial sums of norm<=q, and actual Gaussian-weighted complete-block sum norm<=q*V(A/N) whenq does not dividea. No prime mask is inserted. Scratch80947/final11151 exit0 warning-free; all4 public audits F268scratch37926 standard-only; imported finite Dirichlet-test audit standard-only; index6 includes two private character helpers; lint41515 eleven unrelated unreachable modules, no BAG debt. Actual ratio coefficient and complete physical cross integral remain in scratch.

C28.15 narrow-resonator first-moment matrix (paper plan, OPEN): the explicit coherent block should retain all saddle margins uniformly for49/50<=a/q<=51/50. In the strict strip norm((a/q)^(1-s))<=2. The intended F270 bound then gives every nondivisibility cross integral <=C*(q+N/m), N=(5m)^10. For distinct integer frequencies a,q in one narrow positive interval[Q,(51/50)Q], q cannot dividea. Expanding a source-built finite square |D|² and using (sum|c|)²<=card(S)*sum|c|² should therefore give a quadratic-form error <=C*(Q²/N+Q/m)*N*sum|c|² from the scalar diagonal mean. This is a concrete first mixed-moment operator estimate for the complete block; it leaves |carrier-target|², other chi grades, masks and the positive signed self-target minorant open. No recurrence conclusion or matrix bound is yet formalized.


**C28.14 / F268 FINAL — uniform signed real dual atoms, LEAN PROVED.**
`ZetaChiRealDualAtomUniform.lean` proves every eligible positive real-frequency atom has actual physical integral2*pi*exp(2*pi*i*x)+O(1/m), uniformly on the fixed compact disc on[m^10,2m^10] withm^6 margins. It retains the signed phase and derives all compact-shift thresholds; no integer positivity is substituted. Scratch37926/final27291 exit0 warning-free; public audit F269scratch85536 standard-only; index2 includes private stationary transfer; lint48260 eleven unrelated unreachable modules, no BAG debt. Actual ratio coefficient transfer passed scratch, final pending.


**C28.14 / F269 FINAL — literal ratio cross coefficient, LEAN PROVED.**
`ZetaChiDualRatioAtom.lean` proves exact xi^(1-s) scaling of the real-frequency atom and identifies the cross atom with the original physical dual atom timesexp(i*t*logxi). Its actual integral has main2*pi*xi^(1-s)*exp(2*pi*i*xi*n), with complete errornorm(xi^(1-s))*D/m uniformly on the disc and every eligible positive ratio. Scratch85536/final1644 exit0 warning-free; all3 public audits F270scratch49778 standard-only; index3; lint99594 ten unrelated unreachable modules, no BAG debt. Complete Gaussian-weighted off-divisibility block bound remains in scratch.


**C28.14 / F270 FINAL — complete physical rational cross block, LEAN PROVED.**
`ZetaChiDualRationalBlock.lean` proves the literal Gaussian-weighted rational cross integral is bounded by norm((a/q)^(1-s))*(2*pi*q+(D/m)*K) whenever q does not divide a and every selected saddle lies at the explicit interior margins. The complete integer block and every stationary remainder are retained. Corrected scratch51492/final97403 exit0 warning-free; public audit F271scratch54235 standard-only; index3 includes two private helpers; lint31190 twelve unrelated unreachable modules, no BAG debt. No masked-block cancellation or signed target-error positivity follows.


**C28.15 / F271 FINAL — complete coherent first cross moments, LEAN PROVED.**
`ZetaChiDualCoherentCrossMean.lean` defines the literal coherent carrier, proves every saddle margin survives ratios49/50<=a/q<=51/50, and bounds its complete off-divisibility cross integral by C*(q+N/m), N=(5m)^10, uniformly in numerator, denominator and compact variable. Corrected scratch18543/final95311 exit0 warning-free; both public audits F272scratch6369 standard-only; index5 includes definition/two private helpers; lint78286 twelve unrelated unreachable modules, no BAG debt. Matrix and exact resonator-square integral are still in scratch.

C28.15 growing-family handoff (paper proof plan): on the explicit schedule m=k², N=(5k²)^10, take any complete S subset[100k,101k]. Then card(S)<=k+1, and (101k+N/k²)*(k+1)<=204N/k for k>=1. Thus the intended actual physical quadratic-form error is <=204C*N/k*sum|c|². Together with the proven unweighted coherent-block real mean>=kappa*N, this gives a positive weighted first mean >=kappa*N*energy/2 eventually for every coefficient family. This still is not a positive integral of (rho²-targetError)*|D|²; no target-error energy or recurrence is asserted.


**C28.15 / F272 FINAL — actual first-moment quadratic form, LEAN PROVED.**
`ZetaChiDualCoherentMomentMatrix.lean` defines the literal physical kernel and proves every complete S subset[100Q,101Q] has scalar-diagonal quadratic-form error at most C*(101Q+N/m)*card(S)*sum|c|², N=(5m)^10. Every cross pair is retained. Corrected scratch52373/final14285 exit0 warning-free; public audit F273scratch15486 standard-only; index4 includes definition/two private helpers; lint70941 thirteen unrelated unreachable leaves, no BAG debt. Exact weighted physical-integral identity passed scratch; final still pending.


**C28.15 / F273 FINAL — actual resonator-square integral, LEAN PROVED.**
`ZetaChiDualResonatorIntegral.lean` defines the literal finite Dirichlet resonator, expands its complete norm square into all rational cross frequencies, proves actual coherent-carrier continuity, and identifies the weighted physical integral exactly with F272 quadratic form. Thus its complete first-moment error obeys the same coefficient-energy bound. Scratch15486 passed with two deprecated-alias warnings; final20354 exit0 warning-free after cleanup; all4 public audits F274scratch8273 standard-only; index6 includes definition/private phase helper; lint91118 fourteen unrelated unreachable leaves, no BAG debt. Explicit growing-family decay and positive weighted first mean remain in scratch.


**C28.15 / F274 FINAL — growing resonator physical first mean, LEAN PROVED.**
`ZetaChiDualGrowingResonatorMean.lean` specializes to m=k², N=(5k²)^10 and every complete S subset[100k,101k]. Its actual weighted first-moment error is at most C*N/k*sum|c|², uniformly on the compact disc and in every coefficient family; its actual real weighted first mean is at least kappa*N*sum|c|² eventually for some kappa>0. Every support/pair cost and the explicit height schedule are retained. Corrected scratch49099/final53768 exit0 warning-free; both public audits F275scratch31332 standard-only; index4 includes two private helpers; lint38967 fourteen unrelated unreachable leaves, no BAG debt. Physical mass normalization remains in scratch. No signed target-error integral or recurrence count follows.

C28.10 source refinement (OPEN): source search now found `PoissonSummationPiecewise.tendsto_sum_cosTransform`, an unconditional C² finite-interval Poisson identity with all endpoint contributions retained through its symmetric-transform limit. It applies to real amplitudes and noninteger endpoints; use real/imaginary parts for the literal complex amplitude V(x/N)*x^(s-1)*exp(it logx), and half-integer endpoints around the exact integer block. This can expose the actual full Poisson decomposition without silently deleting the conditional Fourier tail. A quantitative complete nonstationary-mode sum and the unique k=1 stationary profile are still unproved. Generic Schwartz-only identities from deep search did not close these obligations.


**C28.15 / F275 FINAL — actual physical resonator mass, LEAN PROVED.**
`ZetaChiDualResonatorMass.lean` identifies the literal resonator with the corpus generalized Dirichlet polynomial and proves its physical norm-square integral differs from interval-length times coefficient energy by at most2R*card(S)*energy for positive frequencies<=R. On S subset[100k,101k] this is at most404k²*energy, independent of the interval position/length and all coefficients. Scratch31332/final79855 exit0 warning-free; both public audits F276scratch3063 standard-only; generalized mean-value and log-gap imported audits standard-only; index3 includes private exact identification; lint30016 eleven unrelated unreachable leaves, no BAG debt. Physical normalization remains in scratch; no target-error estimate follows.


C28.10 quantitative Poisson-tail paper target (UNPROVED): choose half-integer endpoints around the literal block. At every endpoint, exp(+2*pi*i*k*x)=exp(-2*pi*i*k*x)=(-1)^k for integer k. For the paired spatial phases t*logx +/-2*pi*k*x, the first integration-by-parts endpoint denominators therefore combine exactly as1/(lambda+omega)+1/(lambda-omega)=2*lambda/(lambda²-omega²), giving k^(-2) rather than separate k^(-1) costs. Here lambda=t/x is bounded on the block, omega=2*pi*k, and k>=2 is uniformly nonstationary (using3<pi and x approximately N/5). A second integration by parts should make the complete interior remainders summable in k, using actual amplitude bounds |v^(j)|<=C*N^(Re(s)-1-j), j=0,1,2. Multiplication by chi then predicts total nonstationary error O(N^(-1/2)), with the unique negative-sign k=1 stationary mode retaining the scalar profile V(t/(2*pi*N)). Endpoint transition bands still require separate full estimates. This is a proposed dependency-closed proof mechanism to audit, not an established asymptotic or a recurrence producer.


**C28.15 / F276 FINAL — actual physical normalization, LEAN PROVED.**
`ZetaChiDualNormalizedResonatorMean.lean` defines the real physical resonator mass at N=(5k²)^10 and proves N*energy/2<=mass<=2N*energy for every k>=1 and every complete narrow family. Every nonzero coefficient family therefore has strictly positive physical mass and a uniform positive normalized coherent-carrier real first mean eventually on the compact disc. Scratch3063/final4423 exit0 warning-free; both public audits F277scratch1164 standard-only; index3 includes mass definition; lint61722 ten unrelated unreachable leaves, no BAG debt. This closes growing-family normalization only. Full target-error positivity and recurrence remain open.


**C28.10 / F277 FINAL — full complex finite-interval Poisson identity, LEAN PROVED.**
`ZetaChiDualPiecewisePoisson.lean` extends the exact real C² finite-interval Poisson theorem to arbitrary complex amplitudes via their actual real/imaginary derivatives and integrals. The complete symmetric Fourier transform tail remains a limit; lattice and noninteger endpoint conditions are explicit. Corrected scratch30565 passed with two unused simp warnings; final86774 exit0 warning-free after cleanup; public audit F278scratch93225 standard-only; source real Poisson audit standard-only; index1; lint56843 eleven unrelated unreachable modules plus unrelated HTGeometry/LogCesaroAbelMellin:64 sorry, no BAG debt. Literal dual-amplitude C²/source transfer remains in scratch.

C28.10 phase audit for any later multi-mode extension (paper identity of the proposed stationary main, not a Lean asymptotic): the spatial negative Fourier mode k>0 has saddle x=t/(2*pi*k). Its stationary phase combined with the exact critical chi orientation retains exp(-i*t*logk), and its power/square-root factors combine to k^(-s). Thus the predicted general leading term is k^(-s)*exp(-i*t*logk)*V(t/(2*pi*k*N)), with the block-membership indicator and complete remainder. Only k=1 has the constant compact profile already conjectured for the selected block. Do not extend its common phase to all spatial Fourier modes or drop the remaining low-frequency Dirichlet phases.

C28.10 spatial stationary-phase audit (OPEN): at k=1 and a=t/(2*pi), the literal phase is phi(x)=t*logx-2*pi*x, with phi(x)-phi(a)=t*log(x/a)-2*pi*(x-a), second derivative -t/x² and third derivative2*t/x³. This differs from the previously formalized height-entropy phase D_a(t); F241 cannot be substituted without proving a new Taylor/error transfer. The expected local Fresnel direction is exp(-i*pi/4), cancelling actual chi orientation exp(i*pi/4). Use the actual amplitude and full nonstationary exterior pieces, then treat both height transition bands explicitly. The expected compact-variable scalar profile and any resulting second-moment law remain conjectural until these exact spatial estimates and the complete Poisson tail are proved.


**C28.10 / F278 FINAL — literal spatial-amplitude Poisson transfer, LEAN PROVED.**
`ZetaChiDualSpatialAmplitude.lean` proves the actual Gaussian cutoff is C² on the positive ray, defines the literal amplitude V(x/N)*x^(s-1)*exp(it logx), identifies its natural samples times chi with the actual smoothed dual atoms, proves its C² regularity, and obtains the full finite-interval Poisson transform limit with all modes retained. Corrected3 scratch46353/final55871 exit0 warning-free; all4 public audits F279scratch92767 standard-only; index5 includes definition; lint17323 thirteen unrelated unreachable leaves, no BAG debt (earlier unrelated LogCesaro sorry absent in this lint). Exact natural-block half-integer transfer remains in scratch; quantitative tail/profile and recurrence remain open.

C28.10 complete paired-tail proof obligations (paper target, unproved): for G=phiPrime=lambda+/-omega and v the actual slow spatial amplitude, use B=v/(iG), C=-vPrime/G²+v*GPrime/G³. The exact second IBP remainder derivative is CPrime=-vSecond/G²+3*vPrime*GPrime/G³+v*GSecond/G³-3*v*GPrime²/G⁴. On the half-integer block, prove |G|>=k/2, |GPrime|<=100/N, |GSecond|<=1000/N² and |v^(j)|<=C*N^(Re(s)-1-j), j=0,1,2. Then all C endpoints and the entire CPrime integral are summable O(N^(Re(s)-1)/k²), while the paired B endpoints use the exact cancellation recorded above. The spatial amplitude bounds can use compactness at x/N in a fixed positive interval, but their actual derivative/scaling identities must be proved. These estimates, plus the new spatial stationary calculation and transition bands, are still open.


**C28.10 / F279 FINAL — complete literal integer-block Poisson identity, LEAN PROVED.**
`ZetaChiDualIntegerBlockPoisson.lean` places the exact natural block[A,B] between half-integer endpointsA-1/2,B+1/2, proves every floor/noninteger condition and the full Int/Nat sample bijection, then identifies the actual Gaussian-smoothed chi-dual block with chi times its spatial mean plus complete symmetric Fourier-tail limit. No mode or endpoint is discarded. Corrected scratch30687/final87166 exit0 warning-free; public audit F280scratch19865 standard-only; index2 includes private sum bijection; lint5389 twelve unrelated unreachable leaves, no BAG debt. The complete quantitative tail and spatial stationary profile remain open.


**C28.10 / F280 FINAL — exact signed repeated integration by parts, LEAN PROVED.**
`ChiDualSignedIntegrationByParts.lean` proves one and two exact complex oscillatory integration-by-parts identities, retaining the combined signed boundary and complete final remainder. Corrected scratch17408/final83533 exit0 warning-free; both public audits F281scratch63780 standard-only; index2; lint38590 ten unrelated unreachable leaves, no BAG debt. These are calculus infrastructure, not a quantitative full Fourier-tail estimate.


**C28.10 / F281 FINAL — signed paired endpoint cancellation, LEAN PROVED.**
`ChiDualPairedEndpointCancellation.lean` proves opposite Fourier phases agree at every half-integer endpoint, the exact paired reciprocal coefficient is (v/i)*2lam/(lam²-omega²), and its norm is at most22*norm(v)/k² for0<=lam<=11,k>=2,omega=2*pi*k. Corrected scratch55353/final3886 exit0 warning-free; all3 public audits F282scratch15934 standard-only; index3; lint18112 ten unrelated unreachable leaves, no BAG debt. Full interior remainders and total Poisson-tail bound remain open.


**C28.10 / F282 FINAL — complete spatial frequency geometry, LEAN PROVED.**
`ChiDualSpatialFrequencyBounds.lean` proves the entire half-integer block has2N/11<=x<=N/4 and4<=t/x<=11 forN>=50,t in[N,2N]. Both Fourier signs k>=2 have derivative gap at leastk/2; the next phase derivatives are bounded100/N and1000/N². Corrected scratch16403/final86228 exit0 warning-free; all3 public audits F283scratch18485 standard-only; index3; lint64520 ten unrelated unreachable modules, no BAG debt. These bounds include both extra endpoint halves. Actual amplitude scaling and complete quantitative tail remain open.


**C28.10 / F283 FINAL — actual unit-amplitude derivative identities, LEAN PROVED.**
`ChiDualUnitAmplitudeJets.lean` defines the literal V(x)*x^(s-1) amplitude and its explicit first/second spatial derivatives, derived from actual cutoff C² and positive-real complex-power differentiation. Scratch18485/final73349 exit0 warning-free; both public audits F284scratch99483 standard-only; index6 includes3 definitions/private helper; lint5282 ten unrelated unreachable modules, no BAG debt. Uniform compact bounds and actual height scaling remain in scratch.

C28.10 full paired-mode assembly target (paper, NOT YET LEAN): withu=C*N^(Re(s)-1), derived amplitude/phase bounds imply second coefficient norm<=804*u/(N*k²) and full derivative norm<=490404*u/(N²*k²). On a complete block of length<=N, the two signed modes have total first-boundary cost<=44*u/k², all four second-boundary costs<=3216*u/(N*k²), and both full remainder integrals<=980808*u/(N*k²). ThusN>=1 permits the coarse complete paired bound10^6*u/k². The corpus finite inverse-square tail theorem sum_Ico_one_div_sq_le bounds the entire k>=2 sum; its applicability/axioms and the paired integral estimate still require verification. No mode deletion, prime-mask insertion or recurrence inference is permitted.


**C28.10 / F284 FINAL — actual compact-uniform amplitude jets, LEAN PROVED.**
`ChiDualUnitAmplitudeBounds.lean` proves joint continuity in the complex parameter and positive spatial variable for all three literal amplitude jets, and one positive bound for them on any fixed closed disc times[1/6,1/3]. Corrected scratch14932/final95954 exit0 warning-free; both public audits F285scratch1610 standard-only; index3 includes private joint-power helper; lint73242 ten unrelated unreachable modules, no BAG debt. Actual height scaling and quantitative full spatial tail remain in scratch.

C28.10 spatial quadratic remainder refinement (paper, UNPROVED in Lean): at t=2*pi*a define E(x)=phi(x)-phi(a)+(pi/a)*(x-a)^2 for phi(x)=t*logx-2*pi*x. Its derivative simplifies exactly to2*pi*(x-a)^2/(a*x). On[a-r,a+r],0<=r<=a/2, this is bounded4*pi*r²/a²; E(a)=0 then gives |E(x)|<=4*pi*r³/a². This avoids substituting the wrong height-entropy Taylor theorem. Corpus LogPhaseCubic has profilev-(1+v)*log(1+v), not the spatial log(1+v)-v phase; it cannot be directly applied. The pending actual spatial derivative identities support the new rational remainder calculation. No Fresnel/amplitude/exterior or transition-band estimate is proved by this observation.

C28.10 stronger corpus-backed quadratic target (still UNPROVED application): source `HTGeometry.GammaStirlingCubicLog.norm_log_one_add_sub_taylor_two_le` proves the exact complex log Taylor bound norm(log(1+u)-u+u²/2)<=norm(u)^3 fornormu<=1/2. Substitutionu=(x-a)/a in the actual spatial phase at t=2*pi*a should give |E(x)|<=2*pi*|x-a|³/a², improving the direct derivative majorant above. Its source axioms, positive-real log conversion and exact spatial phase identity must be checked before adoption.

**C28.10 / F285–F294 consolidated FINAL — complete physical Poisson high-tail bound, LEAN PROVED.**
`ChiDualSpatialFourierTail.lean` closes the pending scaling, coefficient, paired-mode, full finite-tail and Poisson-limit chain in one module. On every compact disc the complete paired k>=2 integral is at most C*N^(Re(s)-1)/k², with both half-integer endpoint terms and all four interior derivative terms retained. Summing and passing through the literal integer-block Poisson limit bounds the difference from the spatial mean and both first-mode signs by C*N^(Re(s)-1)*norm(chi). On every fixed right-strip disc this becomes C*N^(-1/2), uniformly in t∈[N,2N] and every complete integer subblock inside[N/5,6N/25], for all sufficiently large natural N. All amplitude/phase size bounds are derived from actual sources, with no analytic estimate assumed. This supersedes the separate uncompiled F285–F294 drafts. Corrected combined scratch34898 exited0; final `lake --old env lean -o ... GaloisForLFunctions/RHTower/ChiDualSpatialFourierTail.lean`59745 exited0 warning-free. Both tail capstones and the inverse-square source audit72996 list only propext, Classical.choice, Quot.sound. Wired in RHTower; lint68456 reports ten unrelated unreachable leaves and no BAG errors. The actual spatial stationary profile, height transition bands and signed self-target bound remain open; this is no deterministic recurrence count.

**C28.10 / F295 FINAL — actual spatial stationary value with full amplitude error, LEAN PROVED.**
`ChiDualSpatialStationary.lean` proves the spatial phase at t=2*pi*a differs from its centered quadratic by at most2*pi*|x-a|³/a². The complete unweighted integral on an interval containing[a-h,a+h] has main sqrt(a)*exp(-i*pi/4) and error4*pi*h^4/a²+20*a/(pi*h). Actual complex-amplitude freezing adds2*L*h²+20*L*a²/(pi*h), retaining both exterior intervals and the literal amplitude at a. Its source capstone derives every bound for the actual Gaussian/power amplitude and obtains full first negative spatial-mode error C*N^(Re(s)-1)*(2*h²/N+20*a²/(N*pi*h)+4*pi*h^4/a²+20*a/(pi*h)), uniformly on fixed compact discs, with t∈[N,2N] and the stated interior saddle margin. No height-entropy substitution or assumed derivative estimate is used. Corrected scratch25687 and final leaf71607 exited0 warning-free; all three capstone audits27602 list only propext/Classical.choice/Quot.sound. Wired; lint25299 has eleven unrelated unreachable leaves and no BAG error. The chi-normalized scalar cutoff profile, transition bands and signed self-target bound were not conclusions of this module.

**C28.10 / F296 FINAL — complete interior Gaussian scalar profile, LEAN PROVED.**
`ChiDualSpatialProfile.lean` proves actual critical chi cancels the spatial Fresnel direction, with complete reciprocal-height error. Every nonnegative spatial Fourier frequency is uniformly nonstationary; combining that bound with the full high tail reduces the literal entire integer block to its negative first mode. The complete block therefore has scalar profile V(a/N), not an arbitrary compact-variable function. The capstone proves, on N=m^10 with spatial margin m^6, norm(sum of all literal dual atoms over[A,B] minus V(a/N))<=C/m, uniformly on every fixed right-strip disc, for all sufficiently large natural m and every physical saddle a=t/(2*pi) in the stated interior region. Every Fourier mode, spatial endpoint, amplitude variation, conductor error and compact-shift error is retained. Broad arithmetic automation initially timed out; targeted monotonicity/threshold deductions resolved it without raising heartbeats. Corrected scratch50045 and final leaf19002 exited0 warning-free; all five source/profile capstones audit35729 use only propext/Classical.choice/Quot.sound. Wired; index finds the capstone; lint52802 reports ten unrelated unreachable modules, no BAG debt. The exterior/transition-band completion and complete signed self-target bound remain open. No recurrence count or RH conclusion follows from this block profile.

**C28.10 / F297 FINAL — uniform transition-band control, LEAN PROVED.**
`ChiDualSpatialTransitionBound.lean` proves a source-derived all-real-frequency spatial bound C*N^(Re(s)-1)*sqrt(N), using actual logarithmic curvature and the full complex-amplitude derivative budget. Combined with the complete Poisson reduction, the literal whole dual integer block is bounded by C*norm(reflectedCompactGaussianRow); actual chi normalization gives one uniform bound on every fixed right-strip disc for all dyadic physical heights and every complete eligible integer subblock. In particular, neither endpoint transition band is excluded. A real-derivative instance mismatch from simplification was fixed by exact derivative-coefficient equality substitution. Corrected scratch2100 and final leaf53878 exited0 warning-free; all three capstone audits43303 list only propext/Classical.choice/Quot.sound. Wired; source index refreshed; lint83683 reports twelve unrelated unreachable modules, no BAG error. Full exterior decay and small-transition-measure/L² assembly remain open; no signed target-error or recurrence count follows.

**C28.10 / F298 final leaf passed — exterior profile decay.**
`ChiDualSpatialExterior.lean` retains the complete first-mode amplitude variation and the entire complementary Fourier error. For a saddle outside either endpoint by h it proves the whole block bound C*N^(Re(s)-1)*norm(chi)*(1+a/h). Actual row normalization gives C/m uniformly on every fixed right-strip disc at N=m^10, h=m^6. Corrected scratch94218 and final direct leaf86492 exit0 warning-free; wired. Three-capstone axiom audit and lint pending below.

**C28.10 / F299 conjecture — full-height mean-square spatial profile.**
Let S be the literal dual integer block [A,B] and P(t)=V(t/(2*pi*N)) times the indicator of [2*pi*(A-1/2),2*pi*(B+1/2)]. At N=m^10 conjecture N^(-1)*integral_[N,2N] norm(S-P)^2 <= C/m², uniformly for every s in each fixed right-strip disc and every eligible whole block. Dependency-closed paper assembly: outside bands of spatial width m^6 around both endpoints, F296/F298 give E/m; on either band F297 and normV<=1 give M. Thus norm(S-P)^2 <= E²/m²+M²*1_left+M²*1_right. Each physical band has length4*pi*m^6, whether or not bands overlap or cross the integration window. Integrating gives E²/m²+8*pi*M²/m^4 after normalization, hence the claim. Continuity of the actual chi path and finite block plus positive-ray cutoff continuity derive measurability; the integrable indicator majorant derives integrability. Formal assembly in progress. This is not a complete-AFE signed target estimate or deterministic self-return theorem.

F298 closure: all three capstones audit86164 list only propext/Classical.choice/Quot.sound. Lint34312 reports thirteen unrelated unreachable modules, no BAG error; exact source search finds exterior capstone. F298 FINAL. F299 first scratch86164 verified the complete pointwise majorant but failed a source namespace check and cutoff-continuity inference; corrected Real namespace and explicit composition, and added full integrability/mean-square assembly in scratch34542. No heartbeat changes.

**C28.16 / F300 conjecture — physical resonator-weighted spatial profile.**
The existing finite physical resonator is D(t)=sum_{a in S} c_a exp(i*t*log a). Its source Cauchy–Schwarz law gives |D(t)|²<=card(S)*sum|c_a|² at every height. Once F299 is audited, integrating the full profile error against this literal weight should give N^(-1)*integral |S_s-P|²|D|² <= C*card(S)*sum|c_a|²/m² on N=m^10, for every finite frequency set and every coefficient family; derive integrability from the continuous actual resonator. In the corpus growing narrow family S subset[100k,101k], m=5k², card(S)<=2k and physical mass>=N*energy/2. Therefore the normalized physical weighted profile error should be O(k^-3), uniformly in all nonzero coefficient families and the whole fixed disc. This attacks the selected carrier's quadratic-error gap in C28.15. It does not control the complementary AFE carrier or manufacture a full self-return minorant. Source: ZetaChiDualResonatorIntegral, ZetaChiDualResonatorMass, ZetaChiDualNormalizedResonatorMean; exact formulas read, new use not yet Lean checked.

**C28.17 next conjecture — actual masked-block physical second moment.**
Corpus audit found a usable stronger source beyond HighBlockDualMeanSquare's logarithmic error: `HTGeometry.MontgomeryVaughanIntervalMeanSquare.interval_integral_normSq_expSum_le` gives `(length+26/(pi*D))*energy` for an arbitrary finite family of D-separated actual frequencies. `Sieve.DirichletMeanValueSharp.dirichlet_meanValue_sharp` also gives the unconditional 104*sum n|a_n|² error. For an arbitrary selected subset F of the literal block [N/5,6N/25], frequencies log(n)/(2*pi) have gap at least a constant/N. Actual Gaussian/power coefficient bound from ChiDualSpatialSlowJets and compact chi normalization should give integral_[N,2N] |sum_F dualAtom|² <= C*card(F), with C uniform on the disc and no logarithmic loss. For F=primeWindowSupported, the proved harmonic cardinality bound then predicts normalized second moment <=C*(1+logH)/logN for all H²<=N. Subtracting this full masked subset from F299's full-block profile would yield an actual retained-background L² profile with error O(m^-2+(1+logH)/logN). This addresses actual prime/cofactor allocation of quadratic energy; it does not prove concentration of the complete ζ self-target or a return-count minorant. Source formulas read; new applications/axioms not yet checked. Deep source search was partial (budget), with applicable MV source hits; no inference from absent results. Current priority remains finishing F299/F300 final audits before opening this source proof.

**C28.10 / F299 final leaf passed — complete physical-height mean-square profile.**
`ChiDualSpatialMeanSquare.lean` proves the literal whole-block Gaussian step profile with normalized squared error<=C/m² on N=m^10, uniform over every s in the fixed right-strip disc and every complete eligible block. Its explicit majorant retains both transition intervals, whose full physical lengths are4*pi*m^6 each, even when they overlap or leave the integration window. Source continuity/measurability and integrability are derived. Corrected scratch71758 and final direct leaf73730 exit0 warning-free; wired; exact index refreshed. Two-capstone axiom audit queued in F300 scratch. Lint77106 reports thirteen unrelated unreachable modules, no BAG errors. This closes C28.10's selected-block spatial profile; no ζ self-return or full signed AFE error is inferred.

F299 closure: both public capstones audit4492 use only propext/Classical.choice/Quot.sound; F299 FINAL. F300 scratch4492 elaborated all three theorem bodies, including the normalized O(k^-3) result; only an unused interface-check probe had a wrong explicit argument order. Corrected the probe, omitted scratch-only probes/audits from production, wrote/wired ChiDualSpatialResonatorProfile, and launched final direct leaf81166. F300 final/axiom closure pending.

**C28.16 / F300 FINAL — physical resonator-weighted profile, LEAN PROVED.**
`ChiDualSpatialResonatorProfile.lean` proves the full cardinality-energy envelope for the actual Dirichlet resonator, hence full normalized weighted profile error<=C*card(S)*energy/m² at N=m^10 for every finite support/coefficient family. On S subset[100k,101k], N=(5k²)^10, the actual mass lower bound gives normalized weighted profile error<=C/k³ for every nonzero coefficient family. All physical heights, coefficients and the complete selected block remain. Direct final leaf81166 exit0 warning-free; all3 capstones audit31047 standard-only. Wired; exact index refreshed; lint53777 ten unrelated unreachable modules, no BAG errors. This is actual selected-carrier quadratic control; no full complementary AFE or signed self-target conclusion.

C28.17/F301 scratch31047 audited both sharp MV and integer log separation with only standard axioms. Its first application failed finite-subtype sum inference and explicit real/natural casts; all source ingredients remain applicable. Corrected these and added the complete free-prime-mask specialization with logarithmic cofactor budget. Scratch40124 now checks the actual cardinality quadratic bound and resulting physical mask second moment. Neither is claimed final until audited.

C28.17 retained-profile paper assembly (next after masked quadratic audit): let X=S_full-P and Y=S_free for the exact primeWindowSupported subset; Finset.sum_sdiff gives S_retained-P=X-Y. Pointwise norm(X-Y)²<=2*normX²+2*normY². The full-block F299 bound and proposed F301 mask bound therefore give normalized retained-profile error<=C*(m^-2+(1+logH)/log(m^10)), at N=m^10 and H²<=N. Every s on the fixed disc shares one constant; this is initially a per-s integrated estimate, not an asserted integral of the compact supremum. Source continuity and the actual positive-height cutoff derive measurability/integrability. A compact-sup/common-height upgrade and the complete signed AFE target bound remain separate hard obligations. No fixed-H mask disappearance is used as a substitute for the complete self-target.

C28.17/F301 corrected scratch87396 exit0: the literal positive-frequency resonator mean-square bound has sharp constant length+52N and no support-cardinality loss; actual unit-amplitude/chi normalization then gives complete masked-block integral norm²<=C*card(F). Applying the existing complete harmonic cofactor count gives free-mask integral norm²*logN<=C*(1+logH)*N for all H²<=N. Every selected term/product cutoff is retained. Wrote/wired ChiDualMaskedMeanSquare, removed redundant tactic warnings, final leaf76523 pending. Source continuity helper is public for the next retained-profile assembly; no unproved analytic inputs added. Four public axiom audits queued in retained scratch; no final claim yet.

**C28.18 common-height masked compact envelope (new paper conjecture, NOT LEAN).**
Source `CompactDiscMeanSqEnvelope` has a measurable planar envelope and Tonelli transfer for entire finite functions. Apply it to the actual normalized polynomial P(t,s)=sum_F chiDualUnitSpatialAmplitude(s,n/N)*exp(i*t*logn), rather than incorrectly claiming chi is entire. Each n is positive, hence the exact unit-amplitude formula V(n/N)*(n/N)^(s-1) is entire in s; joint continuity follows termwise. Choose outer radius r+1, so no outer-strip restriction is needed for this polynomial. The sharp MV source gives outer-disc mean square<=53*N*Cunit²*card(F). The existing envelope then dominates EVERY s in the inner closed disc at each same height, with mean O(N*card(F)). Actual factorization S_free=chi*N^(s-1)*P and the uniform inner-disc reflected-row bound contribute Crow²/N, producing a measurable common physical envelope of expectation O(card(F)); normalized expectation is O(card(F)/N). Harmonic prime/cofactor count predicts O((1+logH)/logN). Combining this with F299's explicit common all-height majorant gives a common retained-profile envelope with expectation O(m^-2+(1+logH)/logN). This would upgrade per-s averages to simultaneous compact control without an uncountable supremum measurability premise. The complete complementary AFE and signed self-target positivity remain open; no recurrence conclusion is assumed. Source definitions/formulas read; envelope applicability and new actual-source proof still require Lean audit.

**C28.17 / F301 FINAL — complete actual masked physical quadratic energy, LEAN PROVED.**
`ChiDualMaskedMeanSquare.lean` direct final76523 exit0 warning-free; all four publics audit33743 standard-only. Wired; exact source index refreshed; lint52604 ten unrelated unreachable leaves, no BAG error. Sharp integer-frequency mean-square bound has error52N*energy; actual chi normalization and unit Gaussian amplitudes give integral<=C*card(F) for every literal eligible subset. Complete harmonic prime/cofactor allocation gives integral_free_norm²*logN<=C*(1+logH)*N for H²<=N. No independent-law replacement or omitted selected term.

C28.17/F302 retained-profile scratch33743 exit0 warning-free first check. It derives actual retained-background integrability and normalized profile squared error<=C*(m^-2+(1+logH)/log(m^10)), for all H²<=m^10 and every eligible block; constant uniform in each s on the disc. Wrote/wired ChiDualRetainedProfile; final69260 pending. This is per-s integrated control; C28.18 is the stronger common-envelope target.

**C28.17 / F302 FINAL — actual retained-background quadratic profile, LEAN PROVED.**
`ChiDualRetainedProfile.lean` direct final69260 exit0 warning-free; capstone audit6676 standard-only. Wired; exact source index refreshed; lint99792 ten unrelated unreachable leaves, no BAG error. The exact full-minus-prime-mask identity and both actual energy estimates give normalized retained squared profile error<=C*(m^-2+(1+logH)/log(m^10)), deriving integrability and retaining every selected term. This is uniform per-s integrated control, not yet a common compact-envelope conclusion.

C28.18/F303 core scratch6676 exit0; common-disc physical masked envelope proved, with only deprecated/redundant tactic warnings. Actual normalized polynomial is entire and jointly measurable; exact chi factorization and sharp outer-disc energy give a measurable envelope G that dominates norm(masked carrier)^2 for EVERY s in the inner disc at the SAME height, with integral<=C*card(F). Source envelope audits standard-only. Wrote/wired ChiDualMaskedCompactEnvelope with warnings cleaned; added the full prime-mask harmonic-cost specialization. Direct final94580 pending; no final F303 claim until its audit.

C28.18 common retained assembly (paper target): use F299's explicit common real majorant for full-block profile error and the F303 common free-mask envelope. Exact finite subtraction and norm-square inequality give one envelope G_ret=2*G_full+2*G_free simultaneously on the entire inner disc. Preserve the logarithmic budget without ENNReal division: expected integral(G_ret)*logN<=C*N*(logN/m²+1+logH) on N=m^10,H²<=N. The full-profile transition indicators retain their complete lengths; this implies the normalized rate already proved per s but now at common physical heights. No full signed ζ self-target positivity follows merely from these source envelopes.

**C28.18 / F303 FINAL — simultaneous compact masked envelope, LEAN PROVED.**
`ChiDualMaskedCompactEnvelope.lean` direct final94580 exit0 warning-free; all five public theorem audits18257 standard-only (propext/Classical.choice/Quot.sound). Wired; refreshed exact corpus index finds the prime-mask capstone. Lint35346 reports eleven unrelated unreachable leaves, no BAG error. One measurable physical envelope controls the actual complete mask at every disc point at the same height, with integral<=C*card(F); complete prime/cofactor specialization pays integral*logN<=C*(1+logH)*N. The entire object is the normalized finite polynomial, not chi. No self-return or signed complete-AFE conclusion follows.

C28.18/F304 common retained scratch86664: first actual implementation contains a full-block common envelope (integral<=C*N/m²) from F299's exact pointwise transition majorant, and the complete retained common envelope with logarithmic budget C*N*(logN/m²+1+logH). Every selected mask term and both full transition-band lengths retained. Exact no-hit retained/common corpus search broadened to common-envelope and found F303's two applicable sources; source signatures verified. Scratch still unverified; no production module yet.

C28.19 weighted-source conjecture (paper, NOT LEAN): remove F300's support-cardinality loss before constructing a physical target certificate. The crude bound |D|²<=card(S)*energy is unnecessary for the two transition bands. For every resonator with positive integer frequencies<=Q, F301's sharp interval bound gives integral_band|D|²<=(4*pi*m^6+52Q)*energy, uniformly in band location. The full-window integral is<=(N+52Q)*energy. Thus the very same common F299 profile majorant G has weighted integral<=C*(N/m²+Q)*energy, N=m^10, with no cardinality factor and simultaneous disc control. The sharp lower mass bound (N-52Q)*energy follows by reversing the interval in the existing upper theorem; when104Q<=N it yields normalized common error<=2C*(m^-2+Q/N) for every nonzero coefficient family. This would allow arbitrarily large supports below o(N), beyond F300's narrow support schedule. It remains a full-block profile estimate, not a free-mask conditional estimate or ζ return minorant.

C28.19 source audit/failed shortcut: deep prime-resonator sieve search was partial; all20 candidate/20 source names inspected. Actual sources Section4BlockClosed, DyadicPrimeMeanSquare, MarkerPairBudget, PrimeWindowSharpDelta and LogPolyTranslation were read. Their prime-pair inputs bound additive shifted prime pairs or single prime polynomials, not the general dilation pairs ap-bq created by multiplying the entire prime/cofactor mask by a growing target weight. No direct conditional mask estimate follows. Do not silently replace these dilation pairs by additive prime pairs. The concrete replacement above attacks a distinct existing loss in full-block transition occupation using already applicable sharp interval energy; conditional mask/complete AFE remain hard open obligations.

**C28.18 / F304 FINAL — common retained compact profile, LEAN PROVED.**
`ChiDualRetainedCompactEnvelope.lean` final78988 exit0 warning-free; both public audits95729 standard-only. Wired; exact index has both public envelope theorems; lint36597 eleven unrelated unreachable leaves, no BAG error. Full-block common envelope has integral<=C*N/m²; retained common envelope pays integral*logN<=C*N*(logN/m²+1+logH), N=m^10. All disc points share the same envelope at the same height, with both transition bands and full mask retained. Conditioning on the rare window target remains open.

C28.19/F305 corrected scratch49568 elaborated sharp reversed-interval mass, both complete weighted transition integrals, the raw common envelope and its actual-mass normalized capstone. Only a redundant ring after field_simp remained; removed in production. Wrote/wired `ChiDualSpatialSharpWeightedProfile.lean` with substantive F301 import; final61414 pending. The bound is C*(m^-2+Q/N), N=m^10, for every positive integer support<=Q with104Q<=N and every nonzero coefficient family. G is chosen before the resonator and controls every disc point at the same height. This strictly improves the earlier cardinality/narrow-schedule estimate. Final/axiom closure still required.

C28.19 next hard target remains the complete masked prime/cofactor field under a target-selecting weight. The full-block estimate alone cannot establish overlap with a rare free-window target, nor can one replace the remaining dilation correlations ap-bq by additive prime-pair counts. Existing C28.11 mixed-grade absolute coefficient costs also remain unpaid. Search of higher spatial modes was partial; all20 candidate/20 source names inspected, no direct complete higher-mode profile found. General Fourier dilation alone is not a new source estimate. Do not spend a new module merely restating that identity.

**C28.19 / F305 FINAL — sharp weighted common profile, LEAN PROVED.**
`ChiDualSpatialSharpWeightedProfile.lean` direct final61414 exit0 warning-free; all three public audits56568 standard-only. Wired; exact index finds normalized capstone; lint56250 eleven unrelated unreachable leaves, no BAG errors. Sharp mass lower bound is (length-52Q)*energy. One real measurable envelope controls the full spatial-profile error for all disc points at each height and every resonator with frequencies<=Q, with weighted integral<=C*(N/m²+Q)*energy. For104Q<=N and nonzero coefficients, its normalized integral is<=C*(m^-2+Q/N). No cardinality loss, deleted transition height or assumed mass lower bound remains. Complete masked conditional energy and signed self-target positivity remain open.

C28.20 next substantive conjecture: aggregate the actual degree-two root-phase matrix instead of paying each coefficient absolutely. F244's exact grade-two main phase at product frequency pq is exp(i*(4*pi*sqrt(pq)+pi/4)). On a narrow positive integer block comparable toN, conjecture the matrix exp(4*pi*i*sqrt(pq)) has operator norm<=C*sqrt(N*(1+logN)), uniformly for arbitrary coefficients and prime restrictions. Paper mechanism to audit: TT* reduces row p,p' correlations to the actual single sum exp(4*pi*i*(sqrt(p)-sqrt(p'))*sqrt(q)). A lattice first-derivative bound, with no integer alias on the narrow block, should give correlation<=C*N/|p-p'|, diagonal<=C*N; the harmonic row sum then gives the stated operator bound. This would replace an absolute coefficient sum in a genuine signed mixed-grade aggregate. All exact coefficient weights, saddle margins and stationary remainders must still be transported before any physical target claim. No operator estimate, derivative-gap inequality or physical minorant has been proved here. Search for the corpus discrete first-derivative source is in progress.

C28.20 failed high-moment shortcut: `SelbergPrimePolynomialHighMoments.integral_norm_edPoly_pow_displaced_le` was read at its actual statement. Its error contains8*N^k*(1+log(N^k)); at physical window lengthN and primes of scaleN, this does not provide the growing-degree physical moment transfer required by C28.11. The exact factorial convolution energy is useful, but the full frequency-length term cannot be dropped. No additional wrapper module was written.

C28.20 concrete paper constants: on the full integer block[N,2N], for p<p' put d=p'-p and delta=d/(4N). The exact TT* phase divided by2*pi is g(x)=2*(sqrt(p)-sqrt(p'))*sqrt(x), with derivative g'(x)=-(d/((sqrt(p)+sqrt(p'))*sqrt(x))). Its denominator lies[2N,4N], so -1/2<=g'<=-delta and delta<=1/4; g' is monotone increasing. The source `Sieve.kuzminLandau_interval` applies in integer bandm=-1 and gives row correlation<=3/(2delta)+1<=7N/d. Diagonal isN+1<=2N. Sum reciprocal integer distances to obtain O(N*(1+logN)) for the Gram row; finite Schur/duality then gives squared operator norm of that size. IMPORTANT: Kuzmin–Landau sums the full integer block, not a prime subset. First prove the full matrix estimate; only then restrict rows/columns via zero-extended coefficient vectors. Applicability/source axioms and every inequality still need Lean verification. Both KuzminLandauInterval and its log-phase application have been read; generic deep search was partial and returned no more applicable source.


**C28.20 / F306 FINAL — full degree-two root-phase matrix, LEAN PROVED.**
`ChiDegreeTwoRootMatrix.lean` direct final89883 exit0 warning-free; all six public theorem audits13427 use only propext, Classical.choice, Quot.sound. Wired; exact index finds operator capstone; lint76685 reports twelve unrelated unreachable leaves, no BAG error. The complete integer matrix exp(4*pi*i*sqrt(p)*sqrt(q)) on [N,2N] has squared operator norm at most16*N*(1+log(N+1)). Complete lattice row correlations are retained before restriction by zero coefficients. This controls the leading degree-two matrix, not its physical stationary remainder, complete signed self-target form, or MUST-270.

C28.21 hard physical-kernel continuation: user explicitly rejects further numerical/bound-only refinements. Target remains an actual positive signed self-target integral retaining every AFE term. F306 does not transport its root-phase matrix through the physical stationary remainder. Investigate smooth physical height localization with exact logarithmic Morse substitution and a uniform remainder whose aggregate is controlled in coefficient energy. Sharp endpoint remainders might support coherent rank-one contributions; this is an unproved risk, not a no-go. Deep stationary/Morse search is partial, all20 candidate and20 source names inspected, no applicable complete smooth stationary theorem returned. Source `LogPhaseMorse.lean` supplies exact quadratic identity, near-identity and strict monotonicity, but no Jacobian/inverse regularity. These are concrete missing analytic obligations; build them rather than assume them. No positive certificate D or complete physical transfer is claimed.

C28.21 regularity progress (SCRATCH ONLY): exact Morse factorization is w(v)=v*sqrt(-2*dslope(dslope psi 0)0 v), with radicand analytic and center value1. Source generic analytic divided-slope/Taylor-jet theorem derives the center value from psi''(0)=-1. Current scratch has elaborated real analyticity of w throughout(-1,infinity), exact Jacobian log(1+v)/w(v) away from0 and derivative1 at0, plus existence of an analytic inverse with positive Jacobian on a fixed neighborhood. Last failure is a complex-cast annotation in the final integral substitution statement; no mathematical assumption was introduced.

C28.21 stronger remainder mechanism (PAPER CONJECTURE): avoid expanding the logarithmic phase in a shrinking interval. After the exact inverse substitution, write the full transformed amplitude B(w)=B(0)+w*C(w), using its removable divided difference. One signed integration by parts gives the difference from B(0) times the full Fresnel integral as -(i*lam)^(-1) times the oscillatory integral of C', with both finite endpoints retained before their limits. Curvature cancellation applies to C', charging endpoint norms and the full integral of |C''|. For a smooth compactly supported B analytic near0, C behaves as -B(0)/w outside support, so its endpoint terms vanish and C'' has an integrable w^-3 tail. This predicts full-line stationary remainder O(lam^(-3/2)), hence O(a^(-1/2)) after physical scaling lam=k*a and dt=a*dv. This removes the per-entry order-one obstruction to aggregating an N-by-N physical stationary matrix. It does not establish target positivity: actual compact-amplitude family uniformity, the exact chi/model perturbation, every mixed grade, and construction of the self-target weight remain obligations. No tail is discarded.

**C28.21 / F307 FINAL — exact analytic Morse substitution, LEAN PROVED.**
`LogPhaseMorseSubstitution.lean` direct final95631 exit0 warning-free; all five public audits29096 standard-only. Wired; exact index finds substitution capstone; lint13505 eleven unrelated unreachable leaves, no BAG errors. The actual signed square-root coordinate is real analytic across0, has derivative1 there, exact Jacobian log(1+v)/w(v) elsewhere, and a source-constructed analytic local inverse with positive Jacobian. The entire signed integral across its saddle interval changes to an exact quadratic phase with full Jacobian, even for arbitrary amplitude functions; no amplitude regularity premise is needed by the monotone substitution theorem. No stationary remainder or positive target certificate is inferred.

C28.21/F308 scratch progress: full real-line vanishing-saddle amplitude theorem is drafted, deriving smoothness/compact support of its removable divided difference and retaining every endpoint before compact-support closure. The first scratch29096 failed only finite quadratic derivative conversion and kernel simplification; all support and full-line assembly bodies elaborated. Corrected scratch also instantiates the analytic inverse from F307 with an actual smooth bump supported strictly inside its analytic neighborhood. The amplitude cutoff(w)*(j'(w)-1) has source-derived smoothness, compact support, analytic center and value0; these are proved, not adopted as an unresolved analytic premise. Proposed full physical Jacobian correction decays after stationary scaling. Still UNVERIFIED until final/audit.

**C28.21 / F308 FINAL — complete localized logarithmic stationary remainder, LEAN PROVED.**
`LogPhaseLocalizedStationary.lean` direct final73746 exit0 warning-free; all five public audits43936 standard-only. Wired; exact source index finds both actual producer capstones; lint76909 twelve unrelated unreachable leaves, no BAG errors. Source construction supplies r>0, analytic inverse j with j(0)=0,j'(0)=1, and a smooth bump strictly inside its analytic neighborhood. The complete localized integral of cutoff(w(v))*exp(i*lam*psi(v)) on[j(-r),j(r)] differs from the corresponding smooth quadratic integral by at most C/(lam*sqrt(lam)). No Jacobian regularity or remainder bound is assumed. The proof divides out the zero saddle value of cutoff(w)*(j'(w)-1), retains signed IBP endpoints, and uses quadratic cancellation of the derivative; full support is integrated. This is a source-level stationary cancellation mechanism, not a changed numerical constant. The universal quadratic main has not yet been replaced by the full Fresnel value, and actual compact chi amplitude families/full signed target positivity remain open.

C28.21/F309 next actual-chi error mechanism (paper derivation, scratch UNVERIFIED): let delta(t)=theta(t)-thetaMain(t)-offset and u_k(t)=1-exp(2*i*k*delta(t)). Exact source phase identities give actual-minus-fixed-conductor-model=u_k(t)*actualChiGrade(t). Source bounds yield |u_k|<=26|k|/t and |u_k'|<=26|k|/t². Applying the existing exact chi-grade oscillatory-amplitude theorem therefore gives a uniform dyadic subinterval difference bound (6/sqrt(|k|/(100T)))*(52|k|/T), for every real frequency and nonzero signed integer k. This preserves cancellation and vanishes for fixed k; integrating the old pointwise error absolutely gave an order-one cost. The complete smooth amplitude version must be derived before matrix transport. First scratch43936 failed continuity/cast simplification and scalar normalization only; corrected75199 pending. No new model assumption or omitted height.

**C28.21 / F309 FINAL — oscillatory actual chi/model error, LEAN PROVED.**
`ZetaChiModelOscillatoryError.lean` corrected direct final94311 exit0 warning-free; both public audits54140 standard-only. Wired; exact index finds both capstones; lint3390 eleven unrelated unreachable leaves, no BAG errors. Every nonzero signed integer grade and every real Dirichlet frequency has full dyadic subinterval model-error integral bounded by (6/sqrt(|k|/(100T)))*(52|k|/T). Under any actual differentiable complex amplitude the same factor multiplies its endpoint norm plus the full integral of derivative norm. The proof uses the exact relative phase error and its source-derived derivative, preserving chi oscillation; fixed-grade error now vanishes, including under smooth localization. No actual chi factor is replaced by an assumed model equality. The positive signed target kernel remains unproved.

C28.21/F310 full smooth Fresnel main (paper proof, SCRATCH): for an actual ContDiffBump cutoff eta, define c(x)=(eta(x)-1)/x, extended by zero near0 because eta=1 there. This is smooth. Outside eta's compact support c=-1/x, c'=1/x² and c''=-2/x³ exactly. Existing source power-tail integrability proves integral|c''| finite across BOTH rays. F308's signed divided-remainder identity gives a bound uniform in outer truncationR; source full Fresnel limit then lets all c/c' endpoint terms vanish. Expected complete smooth main error C/(lam*sqrt(lam)), with no infinite tail deletion. Combining with F308 would identify the actual localized logarithmic main with its full oriented Fresnel value at the same remainder scale. First54140 failed only support-radius proof, exact cast algebra, type-inference and limit-inequality orientation; corrected69243 sole Lean. No result claimed until final/audit.

C28.22 smooth physical amplitude frontier (PAPER, not yet Lean): F308's analytic-at-center premise cannot be assumed for W(t/T) when the moving saddle crosses a smooth cutoff transition. Corpus ParametricSmoothness.contDiff_paramAvg supplies the missing smooth division mechanism. For a jointly smooth B(p,x), set C(p,x)=integral_0^1 partial_x B(p,t*x)dt. FTC gives B(p,x)-B(p,0)=x*C(p,x); parametric averaging gives joint smoothness, including x=0. On any compact parameter set with a common spatial support, C and its x derivative vanish at sufficiently distant endpoints when B(p,0)=0, while joint continuity bounds its second x derivative uniformly. F308 signed IBP then gives one O(lam^-3/2) remainder constant for the entire family, without analyticity or a per-parameter choice of constants. Subtracting B(p,0) times the F310 bump gives the complete uniform Fresnel formula. Intended actual family is eta(w)*j'(w)*W(p*(1+j(w))), p=a/T, retaining physical cutoff transitions. The nonstationary complement, chi-model transfer, complete matrix aggregation and signed positivity must still follow; none is assumed. This is removal of a false applicability shortcut, not optimization of a numerical bound.

C28.22 complete physical continuation (PAPER obligation, not proved): after smooth family closure, instantiate B(p,w)=eta(w)*j'(w)*W(p*(1+j(w))), where p=a/T ranges over a fixed compact positive interval. Joint smoothness follows inside the source inverse interval and local zero of eta outside; no analytic assumption on W. This gives the localized part of the physical fixed-window integral, including saddle crossings of W's transition. The complementary amplitude (1-eta(w(v)))*W(p*(1+v)) vanishes near v=0 and at fixed exterior endpoints enclosing all physical supports. Divide it by psi'(v)=-log(1+v), extend by zero around0, and integrate by parts twice. Uniform compact bounds on the resulting second divided derivative should give O(lam^-2) for the ENTIRE complementary integral, so it can be added to the localized O(lam^-3/2) remainder. No endpoint can be deleted and no pair-dependent cutoff can replace W. Only after this complete transport can F306/F309 be used for the degree-two physical matrix; positivity of the complete signed self-target form is still a separate hard obligation.

**C28.21 / F310 FINAL — full localized Fresnel main, LEAN PROVED.**
`SmoothLogPhaseFresnel.lean` direct final9914 exit0 warning-free; all three public audits79339 standard-only (propext, Classical.choice, Quot.sound). Wired; exact corpus index finds actual logarithmic capstone. Lint45371 reports twelve unrelated unreachable leaves, no BAG error. The full smooth quadratic main, both orientations, and the actual localized logarithmic integral now have the exact Fresnel main with O(lam^-3/2) remainder. Both infinite divided-difference tails were retained and integrated; no limiting premise was added. This closes F308's unidentified smooth main, not the full physical window or self-target positivity.

**C28.22 / F311 FINAL — uniform smooth stationary families, LEAN PROVED.**
`SmoothQuadraticFamily.lean` direct34088 exit0 warning-free; all three public audits55084 standard-only. Wired; exactindex2; lint65104 eleven unrelated unreachable leaves, no BAG error. Complex-valued parametric averaging now proves uniform complete Fresnel remainders across compact real parameter sets, with both orientations and no analytic-at-center requirement. Common support and smoothness are ordinary supplied amplitude data in this generic theorem; the actual physical family is the next producer and is not assumed solved by this lemma.

C28.22/F312 actual physical-family scratch55084 and91107: all joint smoothness, uniform cutoff-transition and actual source-window obligations elaborated. First failure was layout in the inverse derivative proof; second only beta-reduction of the exact substitution integrand. Corrected LogPhasePhysicalWindow is now in direct final audit, wired, not yet claimed final. The source window is ContDiffBump centered3/2 with radii1/4 and1/2, supported in[1,2]; no smoothness input is assumed in the actual producer.

C28.23 complete complementary-window proof (SCRATCH, unverified): for every eta:ContDiffBump0, multiply the full complementary amplitude by a fixed auxiliary bump theta centered9/8, inner radius15/8, outer radius2. It equals1 on[-3/4,3], which contains EVERY scaled physical support for p in[1/2,4], and vanishes outside[-7/8,25/8]. Thus it changes no actual integral while giving global joint smoothness. Since eta(w(v))=1 on a source-derived neighborhood of0, the amplitude and its derivatives vanish there. The total quotient A/(-log(1+v)) is therefore smooth through0, and also across the logarithmic singularity at-1 because theta vanishes in a neighborhood. Repeat after a vertical derivative. Both quotients have the same exterior and saddle zero regions. Exact two-antiderivative IBP on a fixed interval larger than the support kills all derived endpoints and bounds the ENTIRE complementary integral by C/lam², uniformly in p. Actual cutoff support and zero neighborhood are proved from source geometry, never supplied as conjectural premises.

C28.23 final full-window assembly obligation: strict monotonicity of the actual Morse map shows eta(w(v))*W(p*(1+v)) vanishes outside[j(-r),j(r)] on v>-1; at v<=-1 the physical window itself is zero. Therefore the full localized integral equals F312's literal interval integral. All three terms have common physical support[-3/4,3], so establish the exact local+complement split on a slightly larger positive-domain interval with actual continuity/integrability, then pass to the full real line. F312 and the proposed complementary bound would give the COMPLETE fixed-window Fresnel formula (no pair-dependent deleted tail). This must be done before transporting the degree-two physical matrix and attacking signed self-target positivity.

**C28.22 / F312 FINAL — actual physical-window saddle family, LEAN PROVED.**
`LogPhasePhysicalWindow.lean` direct87170 exit0 warning-free; both public theorem audits13839 standard-only. Wired; exactindex; lint40936 twelve unrelated unreachable leaves, no BAG error. One actual source-defined window supported in[1,2] has the complete localized Fresnel formula with one remainder constant for all saddle ratios in[1/2,4]. The generic producer works for every smooth physical window and compact ratio set. All inverse/cutoff/joint-smoothness inputs are derived, including smooth transition parameters. The complementary physical integral is still a separate obligation.

C28.23/F313 corrected scratch48340 passed warning-free. Smooth division through the saddle and the actual full complement are now checked in scratch; LogPhaseNonstationaryFamily is in direct final audit76783, wired. Its source complement bound holds for EVERY actual eta:ContDiffBump0, so the SAME eta produced by F312 can be used in exact full-window assembly. No replacement cutoff or deleted tail is introduced. Public axiom audit is queued in the F314 scratch after final completion.

**C28.23 / F313 FINAL — entire actual physical complement, LEAN PROVED.**
`LogPhaseNonstationaryFamily.lean` direct76783 exit0 warning-free; all three public audits93276 standard-only. Wired; exactindex actual capstone; lint63253 twelve unrelated unreachable leaves, no BAG error. For every saddle cutoff eta, the entire complementary physical-window integral is bounded by C/lam² uniformly over p in[1/2,4]. All common zero neighborhoods, exterior support, joint smoothness and divided amplitudes are constructed. Both integration-by-parts endpoints are retained until their vanishing is proved. The complete fixed-window assembly F314 passed every support/integrability/monotonicity obligation in scratch93276; its only remaining error was addition-order presentation in the final scalar comparison, now corrected for the direct leaf audit.

C28.24 literal conductor/chi transport (PAPER, unverified): exact substitution t=a*(1+v), frequency k*log(a/(2*pi)), gives phase k*a+(k*a)*psi(v). At v=-1 the identity is proved separately; elsewhere it follows from the literal log product identity. Full-line affine Haar substitution preserves the entire physical window. F314 therefore predicts main a*W(a/T)*sqrt(2*pi/(k*a))*exp(i*(k*a-pi/4)) and error a*C/((k*a)*sqrt(k*a)), uniformly in a/T in[1/2,4], k*a>=1. The actual chi grade adds its exact conductor phase factor and F309's oscillatory model error. For the actual W(t/T), endpoint norm and total derivative variation are uniformly bounded independently of T; construct that source bound and combine, retaining the entire interval[T,2T]. This is the next literal actual-kernel producer, not an assumed model equality. Matrix aggregation must subsequently keep W(a/T)*sqrt(a), and all grades/target weights must be charged before positivity.

**C28.23 / F314 FINAL — complete fixed physical-window formula, LEAN PROVED.**
`LogPhaseFullPhysicalStationary.lean` direct30710 exit0 warning-free; public audit65576 standard-only. Wired; exactindex; lint3358 eleven unrelated unreachable leaves, no BAG error. The full real-line integral of W(p*(1+v))*exp(i*lam*psi(v)) has main W(p)*sqrt(2*pi/lam)*exp(-i*pi/4), with one C/(lam*sqrt(lam)) remainder for every p in[1/2,4], lam>=1. The proof retains the fixed physical window, both cutoff transitions and the entire complement. Every support/integrability/monotonicity step is source-proved. This closes the previously missing complete model-kernel remainder; literal actual chi transport, smooth matrix multiplication and the signed self-target certificate still remain.

C28.25 hard weighted-matrix continuation (PAPER, not yet Lean): F315's complete degree-two physical main still has multiplier sqrt(pi*a)*W(a/T), a=2*pi*sqrt(p*q), multiplying F306's root-phase matrix. Bounding this multiplier entrywise destroys the required cancellation. Set h(u)=exp(u/2)*W(exp u), a source smooth compact amplitude supported on[0,log2]. Corpus HasCompactSupport.toSchwartzMap and Fourier inversion give an integrable Fourier transform and an exact L1 mixture of separate unit-modulus row and column phases for h((log p+log q)/2+log(2*pi/T)). Each diagonal phase preserves coefficient energy, so the complete weighted matrix should retain F306's operator norm up to one fixed source L1 budget and the explicit sqrt(pi*T) factor. Prove the multiplier theorem and its ACTUAL h instantiation, then aggregate every F315 remainder. Only afterwards attack all resonator/mixed-grade couplings and signed self-target positivity. The earlier scalar-Schur-seam no-go is not being used or contradicted: this candidate asserts a norm estimate from an explicit Fourier representation, not positivity of an arbitrary entrywise multiplier.

C28.25 source audit: exact lexical Schur-multiplier query returned9 declarations, all inspected; none supplies this Fourier norm transport. The wider smooth-matrix and Fourier queries were partial, with all20+20 returned names inspected. Applicable verified source mechanisms are F306's full root matrix, F315's physical saddle form (direct final passed, axiom audit pending), SchwartzSpace.Basic HasCompactSupport.toSchwartzMap at555, SchwartzSpace.Fourier Fourier-pair instance and integrability at110–142, and Fourier.Inversion continuous inversion at155–184. No external literature or recalled theorem is substituted for these corpus sources.

**C28.24 / F315 FINAL — complete actual positive-grade chi kernel, LEAN PROVED.**
`ChiPhysicalStationaryKernel.lean` direct99613 exit0 warning-free; all four public theorem audits40659 use only propext, Classical.choice, Quot.sound. Wired; exactindex actual capstone; lint23863 ten unrelated unreachable leaves, no BAG error. For every positive integer k, T>=4, a>0 and a/T in[1/2,4], the literal physical integral W(t/T)*chi(1/2+it)^k*exp(i*k*log(a/(2*pi))*t) on[T,2T] has full main exp(i*pi/4)^k*a*W(a/T)*sqrt(2*pi/(k*a))*exp(i*(k*a-pi/4)). Its complete error is bounded by Cm*a/(k*a*sqrt(k*a))+Ce*(6/sqrt(k/(100T)))*(52k/T), with universal source constants Cm,Ce. Exact affine rescaling is proved for every real v, including v=-1. The actual height window supplies its entire derivative variation; F309 supplies the oscillatory actual/model error for all signed grades. This closes literal per-entry kernel transport. It does NOT prove the weighted physical matrix bound, all mixed-grade/resonator aggregation, positive signed self-target certificate, MUST-270, or RH. C28.25's pending-axiom remark above is now superseded by this completed audit.

C28.26 complete physical matrix (PAPER): on T=2*pi*N every root saddle a=2*pi*sqrt(N+r)*sqrt(N+s), 0<=r,s<=N, lies in[T,2T]. F315 therefore applies to EVERY entry. Its complete remainder is uniformly bounded by E(T)=Cm/(2*sqrt(2*T))+Ce*(6/sqrt(2/(100*T)))*(104/T). Full finite-sum Cauchy–Schwarz bounds the remainder form by E(T)*(N+1)*sqrt(energy(c))*sqrt(energy(d)). Combine this with C28.25's actual weighted stationary matrix. Exact finite integral expansion should identify the resulting matrix with the literal W*chi² times both complete logarithmic exponential sums. No pair or height is removed. This handles this entire degree-two block; it does not yet supply all-grade/mixed-resonator control or a positive signed self-target certificate.

**C28.25 / F316 FINAL — actual weighted stationary matrix, LEAN PROVED.**
`ChiPhysicalMatrixMultiplier.lean` direct53350 exit0 warning-free; all nine public theorem audits17860 standard-only. Wired; lint48666 eleven unrelated unreachable leaves, no BAG error. Exact Fourier inversion writes the source-built smooth logarithmic window as an L1 mixture of separate unit phases, preserving both coefficient energies. The complete physical degree-two main therefore has bilinear norm bounded by sqrt(pi*T)*FourierBudget*sqrt(16*N*(1+log(N+1)))*sqrt(Ec)*sqrt(Ed), for every T>0,N>=1 and coefficient families. The identity with F315's actual main retains its global Fresnel phase and every pair-dependent saddle amplitude. This closes the previously missing smooth physical matrix transport. It does not prove small signed prime-restricted/mixed-grade error or positive self-target mass. C28.26 must retain an explicit integral-minus-signed-main approximation; a coarse bound on the whole integral alone cannot establish that sign.

C28.27 next hard arithmetic conjecture (PAPER, unverified): the actual resonator/cofactor products create dilation correlations A*p-B*q=h, not merely p-q=h. For g=gcd(A,B), no pair exists unless g divides h. After reduction and parameterization, the prime pair becomes two affine forms b*n+p0 and a*n+q0, with a*p0-b*q0=h/g. At each sifting prime ell not dividing a*b, each form has one forbidden residue, and these residues coincide exactly when ell divides h/g. Thus the complete local density should be the existing pairClassCount law with the reduced shift, while primes dividing a*b must be excluded with their full Euler cost or handled separately. The zero-shift diagonal must retain exact cofactor convolution collisions; it cannot be charged as a generic off-diagonal pair. Build the complete two-affine-form sieve, CRT root density, residue remainder and explicit bad-prime factors from the source, then aggregate the resulting actual dilation kernels before claiming any conditional energy bound. Applying F317 separately to each resonator pair would reintroduce the support-cardinality loss and does not solve this joint problem.

C28.27 source audit: deep dilation search8369 was partial, inventory64157/64157 with compiler freshness largely pending/stale; all20 candidate and20 source names inspected. Applicable hits PrimePairCount and PrimePairAverageSharp concern additive shifts only. Read actual PrimePairCount, RoughPairCount, RoughPairSieveBound, RoughPairSieve's source construction, PairDensityRootCount and the relevant ResiduePartitionCount statements. Their existing mechanisms are a literal SelbergSieve, injective product support, exact CRT local root density and full finite-residue remainder. The proposed affine extension is not yet a theorem, nor is the subsequent signed/conditional coefficient aggregation or target-certificate positivity.

**C28.26 / F317 FINAL — complete signed degree-two physical matrix, LEAN PROVED.**
`ChiCompletePhysicalMatrix.lean` direct30710 exit0 warning-free; all five public theorem audits91103 standard-only. Wired; exact index signed-approximation capstone; lint48189 thirteen unrelated unreachable leaves, no BAG error. At T=2*pi*N the literal full physical chi-square product integral differs from its ENTIRE signed stationary matrix by at most E(T)*(N+1)*sqrt(Ec)*sqrt(Ed), with the explicit universal-source budget defined in C28.26. The source proves every saddle lies in[T,2T], exact logarithmic frequencies, every entry error, full coefficient-energy summation and equality with the actual integral. No pair or height is deleted. This closes complete degree-two physical transport; it does not produce the target-selecting D, a positive signed self-target integral, MUST-270 or RH. C28.27 now targets the missing actual dilation arithmetic rather than another norm-constant refinement.

C28.27/F318 complete affine-sieve scratch10586 passed warning-free. The source identity x=a*b*n+b*c modulo any e coprime to a*b gives x*(x+Delta)=a*b*(a*n+c)*(b*n+d). Hence the entire root set, not only local cardinality, matches the existing quadratic with Delta=a*d-b*c; squarefree density is exactly pairNu(abs Delta). Exact residue splitting supplies the whole remainder. A literal SelbergSieve now gives an actual two-affine-prime count with explicit finite denominator and every slope-prime exclusion retained. No discriminant-nonzero assumption is needed: merged roots are retained. The zero-shift large-prime equation A*p=B*q is classified as A=B and p=q under the actual positive-cofactor/large-prime conditions. Wrote/wired AffinePairSieve; direct final pending.

C28.28 actual dilation-count continuation (PAPER): for coprime A,B>0 and fixed signed h, choose the least p-coordinate of a nonempty finite prime-pair solution set A*p-B*q=h. Every other solution has exactly p=p0+B*n,q=q0+A*n with n>=0, and n<=P/B when p<=P. Separate the single n=0 anchor, then apply F318 to the full n>=1 family. Its affine discriminant is B*q0-A*p0=-h, so the denominator is independent of the chosen anchor and uses abs(h). This should yield a uniform actual pair-count bound 1+(P/B)/S+the full finite remainder, with all slope primes retained explicitly. The gcd-incompatible case and exact zero-shift diagonal must remain separate when restoring arbitrary A,B. This is an actual source count, not yet the subsequent coefficient-weighted signed/conditional energy bound.

**C28.27 / F318 FINAL — complete two-affine-form prime sieve, LEAN PROVED.**
`Sieve/AffinePairSieve.lean` direct16098 exit0 warning-free; all eight public audits60570 standard-only. Wired; exact index; lint53536 twelve unrelated unreachable leaves, no BAG error. Actual finite prime-pair count for a*n+c and b*n+d has a source-defined positive Selberg denominator with every slope prime explicitly excluded, and the entire finite remainder sum. The density uses abs(a*d-b*c), including coincident roots; no local-density or remainder premise is assumed. Exact large-prime zero-shift collisions retain precisely equal cofactors and equal primes. This supplies the previously missing affine sieve producer, not conditional physical target energy or positivity.

C28.28/F319 primitive dilation scratch60570 passed warning-free on first attempt. Every actual pair is parametrized from a least anchor; the complete count has denominator depending only on abs(h) and the reduced slopes, plus the single anchor and every finite Selberg error. Added the gcd-incompatible empty-set theorem and exact gcd reduction with both finite cutoffs retained; corrected scratch now sole Lean. All arbitrary positive slopes will be covered through their compatible shifts, without silently replacing dilation pairs by additive shifts.

C28.29 next joint-coefficient conjecture (PAPER, unverified): retain the exact convolution energy before estimating the prime mask under a resonator. For the actual spatial block inside[N/5,N], take 1<=H,1<=Q, free primes p>N/H, cofactors m<=H, and positive resonator indices a<=Q with Q*H²<N. Then p>Q*H, so F318's zero-shift law forces a*m*p=b*n*q precisely through p=q and a*m=b*n. Writing a=g*u,b=g*v gives m=v*k,n=u*k and reciprocal-square-root weight g/(sqrt(a*b)*k). The source prime-window slice count, with BOTH product cutoffs kept, should bound the remaining prime reciprocal sum by C/logN; the scale sum costs 1+logH. Proposed actual diagonal convolution-energy bound is C*(1+logH)/logN times sum_{a,b}|c_a*c_b|*gcd(a,b)/sqrt(a*b), rather than support-cardinality times coefficient energy. First prove this full masked convolution statement, then instantiate the actual compact Gaussian coefficient envelope from the source. F319 supplies the separate nonzero-dilation count; its complete signed/weighted aggregation is still required before a conditional physical bound or positive self-target certificate. No such consequence is assumed from the diagonal alone.

C28.29 corpus evidence: deep search10561 completed nonpartial, inventory64171/64171, all20 candidate and20 source names inspected (compiler freshness largely pending/stale). Applicable exact hit Sieve.TwistedDiagonalAdapted.twistedDiagonalAdapted_sum_eq identifies the full weighted diagonal with gcd(h,k)/sqrt(h*k)*harmonic(D); its source124-139 and the two-cutoff reindex73-105 were read. Sieve.TwistedDiagonalGCDReindex supplies exact reduced rays; PrimeWindowHarmonicMultiplicity12-105 supplies actual prime-slice/cardinality and logarithmic cofactor budgets. Do not re-prove the generic GCD identity in a wrapper module. The missing new producer is the complete prime-masked, resonator-convolved source energy and its actual Gaussian application.

**C28.28 / F319 FINAL — actual dilation-pair count, LEAN PROVED.**
`Sieve/PrimeDilationPairs.lean` direct28883 exit0 warning-free; all five public audits65566 standard-only. Wired; exact index; lint60761 twelve unrelated unreachable leaves, no BAG error. A least anchor parametrizes the full primitive solution set; its discriminant is the exact signed shift. Gcd-incompatible shifts have no pairs, while gcd-compatible pair sets agree exactly with their reduced sets, preserving both finite cutoffs. The complete general count retains one anchor, the explicit finite Selberg denominator and every error term. This closes the false additive-pair substitution identified in C28.19. It does not yet prove a useful joint coefficient-weighted physical bound, the full signed self-target positivity, MUST-270 or RH.

C28.29 actual Gaussian applicability check: ChiDualMaskedMeanSquare81-155 uses the literal spatial block[N/5,6N/25], contained in[N/5,N], with exact factorization chi(s+it)*N^(s-1) times the unit-spatial-amplitude polynomial. Its source common-row bound gives squared prefactor<=C/N. Thus normalize that finite polynomial by sqrtN and use the source uniform unit-amplitude bound to obtain the needed coefficient envelope C/sqrt(n) on the entire actual block. The conjecture above was written for this actual geometry after this check. A public weighted producer must derive/reuse these source facts; the existing unweighted mean-square capstone alone cannot be applied under the target-selecting resonator.

C28.29 refinement2026-10-02 (PAPER, unverified): actual unit-spatial Gaussian coefficients have a uniform constant envelope before the chi factor, so count the exact reduced collision ray instead of replacing coefficients by reciprocal square roots. For a,b<=Q<=N/H, primes p>N/H cannot divide either reduced resonator index. Every masked collision a*n=b*m therefore gives n=(b/g)*d,m=(a/g)*d with d carrying a free prime, and max(a/g,b/g)*d<=N. The source prime-slice estimate at cofactor R*k, R=max(a/g,b/g), bounds the number of such d times logN by (2*N*log4/R)*sum_{k<=H}1/k. Thus the full convolution energy should be at most 2*B²*N*log4*(1+logH)/logN times sum_{a,b}|c_a*c_b|*gcd(a,b)/max(a,b) for every literal masked coefficient family bounded by B. After actual Gaussian normalization this is stronger than the proposed GCD/sqrt kernel. It needs only H²<=N and Q<=N/H. The proof must include the full convolution-square expansion, both masked collision endpoints, and actual Gaussian coefficients; neither a random-law estimate nor the diagonal alone is a physical conditional bound.

C28.29/F320 scratch93853 exited0 warning-free. Complete dilated mask counting, free-prime descent, exact collision reindexing and the full complex convolution-square bound all verify. The resulting kernel is gcd(a,b)/max(a,b), with no support-cardinality factor. Wrote/wired PrimeWindowResonatorDiagonal; direct final50530 pending. Actual chi-weighted Gaussian coefficient instantiation is drafted next; no physical mean-square or positive self-target consequence is inferred from the coefficient diagonal alone.

**C28.29 / F320 FINAL — complete masked resonator convolution diagonal, LEAN PROVED.**
`PrimeWindowResonatorDiagonal.lean` direct50530 exit0 warning-free; four public capstone audits66378 standard-only, as is the reused newly public prime-slice lemma. Wired and exact-indexed; lint6745 thirteen unrelated unreachable leaves, no BAG errors. For H>=1,H²<=N, positive spatial indices<=N and positive resonator indices<=N/H, the entire complex masked convolution energy times logN is at most 2*B²*N*log4*(1+logH) times sum_{a,b}|c_a*c_b|*gcd(a,b)/max(a,b), where B is the actual coefficient envelope. Every multiplicative collision is retained. The proof uses exact reduced GCD rays and the full dilated prime-product cutoff. This removes support-cardinality loss and improves C28.29's proposed kernel; actual source normalization is supplied by F321 below. Nonzero physical shifts, mixed chi grades, signed target positivity and RH remain open.

C28.29/F321 actual Gaussian scratch66378 passed first time, warning-free. It proves source coefficient normalization, exact original carrier reconstruction, complete resonator-product convolution and the uniform physical-height chi-weighted coefficient diagonal bound. Wrote/wired ChiDualMaskedResonatorDiagonal; direct final pending. The chi row removes the full N factor. This remains a coefficient-diagonal theorem, not a physical conditional mean-square bound.

C28.30 next physical continuation (PAPER, unverified): use the nonnegative actual smooth height window W and source upper chi-row bound to reduce the positive weighted quadratic integral to a constant-coefficient masked convolution. Two integrations by parts in the full smooth window should replace the non-summable 1/shift envelope by min(1,C*(Q/|v|)^2), where v=a*m*p-b*n*q is the actual nonzero dilation shift and a,b<=Q. The exact diagonal is now F320/F321. F319 supplies complete finite counts, but a usable denominator lower bound and the full coefficient-weighted shift aggregation still need proof. No fixed-point/random-law substitution is permitted.

C28.30 denominator insight (PAPER, unverified): for reduced coprime affine slopes a,b and a prime anchor c,d above the entire sieve range, a prime dividing one slope has exactly one affine-product root, because the corresponding anchor constant is nonzero and the other slope is a unit. Away from a*b the root count is already F318's one-or-two law. Thus the full local class count should be pairClassCount(abs(a*d-b*c)*a*b,p), INCLUDING slope primes. CRT over the full squarefree primorial would give exact density pairNu of that enlarged shift, allowing reuse of RoughPairSieveSharp's full two-log Euler lower bound instead of losing the slope primes. This is stronger structural information, not a numerical-constant refinement. Must derive anchor nonvanishing from actual primes>h, prove the full affine CRT/root law and all residue remainders, and transport into the actual reduced dilation-pair set. When the nonzero shift shares a small slope prime, the actual pair set may be empty; that exclusion must also remain explicit. No full affine-density or denominator result is yet in Lean.

C28.30 corpus evidence: denominator search57784 nonpartial, inventory64188/64188, all20+20 statements inspected, compiler freshness largely pending/stale. Relevant existing statements selbergBoundingSum_roughPairSieve_ge_sharp, sum_selbergTerms_roughPairSieve and selbergBoundingSum_roughPairSieve_ge. Read RoughPairSieveSharp1-126, PairEulerFactor full, RoughPairSieveBound1-77, and ReducedFrequencyMobiusAliasCollapse112-143,478-500. The existing CRT equivalence is specifically x*(x+h); build the affine analogue rather than pretending it applies unchanged. The actual smooth-window shifted-kernel bound and average singular factors are separate subsequent obligations.

**C28.29 / F321 FINAL — actual chi-weighted masked resonator diagonal, LEAN PROVED.**
`ChiDualMaskedResonatorDiagonal.lean` direct25812 exit0 warning-free; all four public audits19345 use only propext, Classical.choice, Quot.sound. Wired and exact-indexed; lint99365 fourteen unrelated unreachable leaves, no BAG errors. The actual physical coefficients are reconstructed exactly, including chi, the literal cutoff and all complex powers. Their full resonator product equals the complete multiplicative convolution. Source compact amplitude and reflected-row bounds cancel the full N factor from F320, yielding coefficient energy*logN<=C*(1+logH)*GCD/max resonator energy uniformly at every physical height t in[N,2N] and every disc point. No source coefficient/row bound is assumed. C28.29 is closed in this stronger form. Nonzero physical shifts, mixed chi grades, positive signed D, MUST270 and RH remain open; C28.30 is the next hard producer.

C28.30/F322 complete affine-density scratch87739 passed warning-free. The local count is exactly one at either slope prime and otherwise the existing discriminant law; genuine affine CRT gives the full squarefree density pairNu(absDelta*a*b). Actual prime anchors above the sifting range discharge every local nonvanishing fact, and the entire root budget remains2^omega(e). Wrote/wired AffinePairFullDensity, final audit pending. The next actual full-primorial sieve reuses this density and the corpus complete pair denominator. Factoring F319's already proved least-anchor cardinality transport into a public helper avoids duplicating that proof for the new denominator.

**C28.30 / F322 FINAL — full affine local density including slope primes, LEAN PROVED.**
`Sieve/AffinePairFullDensity.lean` direct4711 clean; all eight public audits73294 standard-only. Actual affine CRT proves root-count multiplicativity without invertible slopes. At a slope prime the source prime anchors force exactly one root; elsewhere F318 gives the discriminant law. The full squarefree density is pairNu(absDelta*a*b), and its root budget is2^omega(e). Wired and exact-indexed. The reused affine product injectivity was publicized and directly audited27415; standard-only source audit73294.

**C28.30 / F323 FINAL — complete actual dilation sieve denominator, LEAN PROVED.**
`Sieve/PrimeDilationFullSieve.lean` direct10102 clean; all ten public audits10334 standard-only. The actual affine support uses the entire range primorial. Its density and every residue remainder come from F322's prime anchors; its denominator equals the corpus full rough-pair denominator at absDelta*a*b. The complete Mertens/Rankin lower bound therefore transports to literal A*p-B*q=v counts, including the least anchor and every finite divisor error. Arbitrary positive slopes use exact gcd reduction and retain both finite source cutoffs. A small prime dividing a reduced slope and the signed shift makes the actual pair set empty. The actual free-prime cutoff Y and the sifting cutoff h are distinct, with h<=Y; this avoids imposing the Rankin level condition at Y=N/H. Existing F319 least-anchor proof was extracted, reused and directly audited43301; existing capstones and new helper audits73294 standard-only. Wired/exact-indexed; lint69454 fourteen unrelated unreachable leaves, no BAG error. No coefficient-weighted physical aggregate, positive D, MUST270 or RH follows from these counts alone.

**C28.31 PAPER — source smooth-window signed dilation kernel.**
Corpus search89215 completed nonpartial, inventory64200/64200; all candidate and source statements inspected. Existing CGL Schwartz decay and ChiPhysicalMatrixMultiplier supply the mechanism, but no actual linear-log kernel for the BAG window was returned. The actual W=bagPhysicalHeightWindow is smooth and compactly supported. Build its Schwartz Fourier transform directly and prove the exact full physical identity K(T,L)=T*Fourier(W)(-T*L/(2*pi)). Its zero and second Schwartz seminorms give |K|<=C*T*min(1,1/(T*|L|)^2). The corpus full log separation then yields |K(T,logj-logk)|<=C*T*min(1,(Q/|j-k|)^2) for positive j,k<=T*Q. Preserve the complete signed complex-coefficient double sum before taking this bound. This is the missing summable physical shift kernel, not yet the weighted arithmetic operator estimate. Counting absolute pairs can still pay an unacceptable coefficient L1-square cost; the next source-specific aggregation must address that cost rather than claim arbitrary resonator conditioning. Mixed chi grades and positive signed self-target mass remain open.

C28.31/F324 scratch91731 passed warning-free: exact raw-window Fourier transform, uniform zero/second frequency moments, full product-frequency squared-shift decay, literal interval support, positive actual window mass, and full complex signed Gram-minus-diagonal equality all verify. Wrote/wired BagPhysicalWindowGram; direct final pending. The absolute error theorem retains the complete coefficient-weighted shift sum. No uniform conditioning follows from this expression alone.

**C28.32 PAPER — actual chi-weighted signed physical Gram.**
Source search32303 nonpartial64209/64209; all20 candidate/20 source statements inspected. It returned the existing actual normalized block and unweighted envelopes, not a full resonator-weighted signed producer. Use chiDualMaskedBlock_eq_normalized and the source row normalization to identify D times the actual block as (chi*N^(s-1)) times the FULL convolution of D with the static source unit amplitudes. Unlike the earlier F320 bound, this identity should permit arbitrarily large positive resonator indices. F324 then gives the exact signed Gram of that convolution. The source reflected-row bound should dominate the literal W-weighted physical square by C times [windowMass*coefficientEnergy + Re(full signed offDiagonal)/N], uniformly on the fixed right-strip disc. No cross term may be deleted, no bound on D's support is added, and no absolute coefficient L1 sum replaces the signed term. This is an actual source producer for subsequent sign/shift analysis, not a target-positivity conclusion. The remaining hard problem is choosing D and proving its complete signed self-target form positive while retaining all mixed chi grades.

**C28.31 / F324 FINAL — actual smooth signed Gram and quadratic shift decay, LEAN PROVED.**
`BagPhysicalWindowGram.lean` direct68426 exit0 warning-free; all nine public audits59412 standard-only. Exact source Fourier scaling, fixed positive window mass, full interval support and signed complex coefficient Gram are closed. For any positive j,k<=T*Q, j!=k, the entire kernel obeys C*T*min(1,(Q/|j-k|)^2), with one source constant. The physical integral-minus-diagonal equals the full signed off-diagonal sum; its absolute bound retains the complete weighted shifted correlations. Wired/exact-indexed. This removes the nonsummable bare-window shift envelope, not the remaining coefficient aggregation or self-target sign.

C28.32 source normalization direct91036 clean; newly public helper norm_chiDualScaledFactor_sq audit59412 standard-only. F325 first scratch proved the exact normalized masked-resonator Gram. Its actual weighted capstone failed on Nat/Real/Complex cast presentation, not a mathematical premise. Corrected explicit casts, rerunning the same conjecture. The source Gram keeps all cross terms and arbitrary positive resonator support. No positive target conclusion claimed.

**C28.33 new higher-grade conjecture audit — PAPER, not yet Lean.**
The remaining C28.11 problem is a complete growing-degree target weight, not another scalar kernel bound. Source F306 proves a square-root-scale bilinear bound for exp(4*pi*i*sqrt(p*q)). Source F315 and ZetaChiMixedGradeStationaryTransform show that grade4 instead has root phase exp(8*pi*i*(p*q*r*s)^(1/4)), up to its common orientation and actual saddle amplitude. A tempting conjecture is that F306's square-root saving extends unchanged to arbitrary four coefficient families. A source-grounded coherent-box argument indicates that this conjecture is FALSE; this is not yet a formal no-go and does not retire BAG.

Paper obstruction and positive survivor to prove: let p,q,r,s lie in the same integer interval[N,N+H], N>0. Put u=sqrt(p*q), v=sqrt(r*s), G=sqrt(u*v). Each u,v also lies in[N,N+H]. For any x,y in this interval, x+y-2sqrt(x*y) is nonnegative and at most H²/(4N), by multiplying by x+y+2sqrt(x*y) and using (x-y)²<=H². Hence 0<=p+q+r+s-4G<=H²/N. The integer linear phase exp(2*pi*i*(p+q+r+s)) is exactly1. The source oscillation Lipschitz bound then gives |exp(8*pi*i*G)-1|<=2*pi*H²/N. For arbitrary nonnegative coefficient families supported in this common box, the ENTIRE fourfold packet differs from the product of their coefficient masses by at most this same relative factor. If H is proportional to sqrt(N), the all-one packet has order H^4 mass while the product of four coefficient L2 norms is order H². Thus its required operator factor has order N, rather than the degree-two square-root scale. Formalize the exact positive packet law and a genuine parameterized counterexample before closing this candidate.

This exposes a necessary replacement: all-grade physical aggregation must use actual source flatness and local packet masses, not blindly extrapolate the degree-two arbitrary-coefficient L2 estimate. The actual normalized coefficient and signed physical Gram producers F321/F324/F325 retain that information. Higher-grade packet aggregation, control of the truncated target-selecting weight, and full signed self-target positivity remain unsolved. A random-law Laplace product alone cannot discharge them. Source search48951 was partial (inventory64310/64310); all20 candidate/20 source statements inspected, no applicable quartic phase packet theorem returned. Follow-up lexical root/phase search is running. No numerical experiment or literature assumption used.

**C28.32 / F325 FINAL — actual chi-weighted full signed physical Gram, LEAN PROVED.**
`ChiDualMaskedSignedGram.lean` direct21144 clean; both public audits90805 standard-only. The literal normalized masked block under any finite positive-frequency resonator has an exact complete convolution Gram, with every collision and signed cross term retained. Actual source chi-row normalization bounds its full W-weighted physical square by C*[windowMass*coefficientEnergy+Re(full offDiagonal)/N], uniformly on the fixed right-strip disc. There is no upper bound on resonator indices or replacement by a coefficient L1 sum. Source norm_chiDualScaledFactor_sq was publicized, direct91036 clean, standard-only audit59412. Wired/exact-indexed; lint37050 fifteen unrelated unreachable leaves, no BAG debt. This closes the actual moving-chi normalization/physical-Gram connection. The sign/size of the complete weighted correlations and the target-selecting D still require proof; no RH consequence asserted.

C28.33 first scratch90805 passed on its first attempt: the full nested square-root radius lies in its original box, its four-variable arithmetic/geometric defect is at most H²/N, and every integer fourth-root phase is within2*pi*H²/N of1. The all-positive weighted fourfold packet law is now drafted and checking. Follow-up lexical search77274 returned F306's pair correlation and existing physical root kernel, no applicable fourfold coherent packet statement among the returned20. No claim of a completed asymptotic operator no-go until the actual parameterized counterexample is also proved.

**C28.34 actual physical coherent quartic packet — PAPER conjecture.**
F326's complete integer phase law and F315's actual full physical kernel suggest a stronger source conclusion. Set T=(4*pi/3)*N, G=(pqrs)^(1/4) for p,q,r,s in[N,N+H], and H<=N/6. Then a=2*pi*G lies in the physical cutoff plateau because a/T=(3/2)*(G/N) lies in[3/2,7/4]. The exact grade-four main is exp(3*pi*i/4)*pi*sqrt(G)*exp(8*pi*i*G). F326 controls the last phase with epsilon=2*pi*H²/N. The entire actual chi integral should therefore have oriented real part at least pi*sqrt(N)*(1-epsilon) minus the complete source kernel remainder, uniformly for every quadruple. Summing all nonnegative coefficients retains the full packet mass; no physical endpoint or complementary term is discarded. First prove this literal source positivity and audit its exact orientation. This is a positive survivor of the failed arbitrary-coefficient bound, not a claim that the complete signed self-target form is positive. The next hard problem remains simultaneous local-packet/flatness control of all grades and target-weight construction, including the complete complementary AFE.

**C28.33 / F326 FINAL — coherent quartic packets and exact operator obstruction, LEAN PROVED.**
`ChiDegreeFourCoherentPackets.lean` direct52855 exited0 warning-free; all eight public audits61265 standard-only. Complete nonnegative weighted packet coherence, exact root fourth power/log frequency, half-mass lower bound and a parameterized counterexample for every C all verify. The explicit family N=16*m^4, S=[N,N+m²], m>16|C|+4 defeats the degree-two square-root/log factor times the product of four coefficient L² norms. Positive survivor and failed candidate are closed together in `../5-failed/bag-fourth-grade-square-root-operator.md`. Wired/exact-indexed; lint59950 twelve unrelated unreachable modules, no BAG debt. This is a structural obstruction, not a numerical bound optimization, and it does not retire BAG. C28.34 now addresses the literal physical positive packet with every source remainder retained. Search42498 partial64322/64322, all20 candidate and20 source statements inspected; only existing physicalChiStationaryMain/root factorization applicable, no new higher-grade flatness estimate returned.

C28.34 scratch91789 passed: complete actual physical packet has eventual lower bound (pi*sqrtN/4)*full nonnegative tensor mass after rotation by exp(-3*pi*i/4). Every endpoint, smooth transition and actual/model remainder remains. This is not positivity in the original real direction. The exact orientation exposes a stronger signed conjecture: for epsilon<=1/4, the unrotated physical chi-four packet has eventually negative real part bounded above by -(pi*sqrtN/8)*its mass. Prove this literal sign before using coherent packets in any target-minorant argument. The entire signed target form, containing all other grades, is still open.

**C28.34 / F327 FINAL — actual coherent quartic physical mass and sign, LEAN PROVED.**
`ChiPhysicalQuarticPackets.lean` direct7713 exited0 warning-free; all eight public audits8864 use only propext, Classical.choice, Quot.sound. For T=(4*pi/3)*N, the complete source cutoff is identically1 at every saddle generated by a common integer box[N,N+H], H<=N/6. The exact main is exp(3*pi*i/4)*pi*sqrt(G)*exp(8*pi*i*G). Both full physical kernel remainders are retained before summing arbitrary nonnegative tensor coefficients. For all sufficiently large N, coherence epsilon<=1/2 gives rotated real mass at least(pi*sqrtN/4)*total coefficient mass. More strongly, epsilon<=1/4 gives ORIGINAL real physical integral at most-(pi*sqrtN/8)*mass. This is a literal signed source theorem, not a declaration that positive integer grade means a positive real term. Nonzero mass gives strict negativity. The complete mixed-grade/inter-packet target form remains open. Wired/exact-indexed; lint2960 eleven unrelated unreachable modules, no BAG debt; targeted whitespace check clean.

Next source audit: prime/masked signed-phase search43390 nonpartial64328/64328, all20 candidate and20 source statements inspected. `MatomakiTeravainenWattProductMeanSquare` was checked: its useful long-height energy bound still requires the complete triple-product support below physical height, so it does not pay the growing prime-product resonator cost. `MenonHarmonicMaskedActiveReceiver` retains actual large-value set volumes; it is not a closed conditional estimate for the BAG target. No wrapper module is warranted. Investigate a source-built prime-product resonator directly in F325's complete signed Gram: its squarefree coefficient structure could replace the arbitrary-coefficient bound, but support growth, free-prime collisions and signed physical transfer must all be derived. Search35285 now audits existing exact tilted convolution/prime-product identities before a new conjecture.

**C28.35 source-structured moving-chi product weight — OPEN, no Lean claim.**
Search35285 completed nonpartial64330/64330; all20 candidate and20 source statements inspected. Direct corpus reads then found `SteinhausFiniteAffineDensity` and `SteinhausFiniteAffineVariance`: exact original-law density factorization and prescribed-mean variance already exist. `SteinhausComplexConvolution` identifies the exact full finite coefficient energy; `SteinhausLinearPrimeTargetEnergy` and `SteinhausPrimeConvolutionEnergy` already retain prime collisions/occupation. Repackaging these random-law identities would not advance the physical frontier.

Candidate to attack: for actual prime channels and prescribed source biases, use the literal weight `D(t)=prod_p(1+u_p*chi(1/2+i*t)*exp(i*t*log p))`, with the actual compact/cofactor factors restored before a target conclusion. At the pure critical prime level each normalized square factor is the existing affine circle density with mean determined by `conj(u_p)/(1+norm(u_p)^2)` after the common chi rotation. This is only an algebraic observation, not physical averaging. A weight omitting chi biases the unrotated prime phases and does not by itself track the actual moving chi field. Expanding the correct weight yields the full mixed chi grades and prime-subproduct frequencies; no short-support assumption can be imposed.

Hard conjectural producer is control of the COMPLETE signed target-error integral for this source-structured coefficient family, strong enough to beat its physical mass. Must first choose biases from the actual self-target catalogue/cofactor field, retain the moving correction and every cross-grade term, and derive the physical mass and error jointly. The F327 negative-real quartic packets must remain in this expansion; an arbitrary-coefficient sqrt(NlogN) bound or a Haar-product substitution is ruled out as a shortcut. Do not assert a uniform arbitrary-target theorem: the existing zero-bearing target compatibility obstruction still applies. This candidate remains BAG, does not presume RH, and has no currently proved positive D certificate.

**C28.36 genuine physical mass of the moving-chi product — PAPER conjecture.**
Use C28.35's literal D(t)=prod_j(1+u_j*chi(linePt t)*exp(i*freq_j*t)), with norm(u_j)<=1/2 and no support or degree bound. The current corpus supplies uniform first-grade curvature cancellation and the actual smooth height-window variation. For a unit z, the elementary logarithm lower bound should give log(norm(1+u*z)^2)>=2Re(u*z)-25norm(u)^2. Multiplication retains the full product: normD²>=exp(2ReF-25E), F=chi*sum u_j exp(i*freq_j*t), E=sum normu². The tangent inequality for exp, integrated against the actual nonnegative W(t/T), then predicts

`integral W*normD² >= T*windowMass*exp(-25E-C*sum normu/sqrtT)`

with a single source constant C, for every T>=4 and every finite coefficient/frequency family. Dividing by prod(1+normu²) costs at most another E in the exponent. Thus actual E<=kappa*logT and sum normu<=A*sqrtT give polynomial physical mass without expanding the growing grades or assuming phase independence. All high-grade terms remain in the product. This is a source mass producer, not a target-error bound or RH consequence. Prove the pointwise logarithm law, obtain the actual W-weighted chi first mean from the corpus, and derive the entire product integral lower bound. The hard remaining C28.35 obligation is the full signed self-target error under this very same weight.

**C28.37 fixed chi-grade bandwidth, growing radial degree — new candidate, OPEN.**
C28.36 controls mass without expanding grades, but does not yet control target error. Source `SteinhausLinearPrimeTargetEnergy` and `ReflectedCompactTargetAssembly` suggest separating the two roles of degree before attempting another all-grade estimate. For a literal finite prime polynomial P(t), put F(t)=chi(linePt t)*P(t) and consider

`D_{k,d}(t)=P(t)^k * sum_{r=0}^d b_r*F(t)^r`.

This is a concrete family of physical weights. Its radial degree k can grow with conductor, while the chi-grade differences in normD² are confined to[-d,d]. Multiplying by the actual scalar error F-g enlarges this only to[-d-1,d+1]. The common high radial degree does not itself create high chi grades. This algebra alone is not a target certificate and warrants no wrapper module. It exposes a more precise hard producer: actual balanced prime moments with growing k, and the finitely many adjacent twisted moments of the same source polynomial, retaining every signed product-frequency collision.

First scalar conjecture to test, not assume: for P_N built from the actual critical dual prime coefficients on the existing interior prime window, write v_N=sum norm(coeff_p)^2 and M_{k,N}=integral W(t/N)*norm(P_N(t))^(2k). Determine whether there is a source range k<=c*logN, c>0, in which adjacent ratios M_{k+1,N}/M_{k,N} approach (k+1)*v_N and the corresponding radial variance tends to zero when k*v_N has a fixed positive limit; simultaneously control the finitely many nonzero chi-grade moments against M_{k,N}. This would supply a physical radial selector with fixed angular bandwidth. Neither the Gaussian ratios nor the off-grade cancellation are currently proved. No claim for every c or arbitrary target amplitude is made. Actual self-target catalogue/cofactor/correction compatibility must still be established even if this scalar conjecture succeeds.

Why the previous generic candidates do not settle it: F326/F327 preserve coherent higher-grade packets; energy and coefficient flatness alone do not justify a Gaussian physical law. `SelbergPrimePolynomialHighMoments` retains its full product-support error, and the source `CumulantInductionStep` supplies coercivity/induction algebra but not the required actual physical prime cumulants. Source counts cannot be substituted for signed cancellation between near-product terms. Investigate the centered prime coefficients and complete signed balanced moments, not a new name for an assumed moment estimate. Corpus search77377 was nonpartial64349/64349, all20 candidate/20 source statements inspected; no applicable physical connected-moment producer returned. Grade-band search78426 pending.

**C28.36 / F328 FINAL — complete chi-product physical mass, LEAN PROVED.**
`ChiProductPhysicalMass.lean` direct65596 exited0 warning-free; all three public theorem audits, the product definition, and exposed source-window variation audit70599 use only propext, Classical.choice, Quot.sound. For arbitrary finite frequency families and norm(u_j)<=1/2, the entire actual W-weighted chi-product square has lower mass T*windowMass*exp(-25E-C*L/sqrtT), with E=sum normu², L=sum normu, one source C>0, all T>=4. Normalizing every affine factor by1+normu² gives the same lower bound with26E. The pointwise logarithmic inequality and integrated exponential tangent retain all product terms; first-grade curvature alone controls the linear mean. There is no degree or support-length restriction, numerical experiment, phase-independence premise, or assumed analytic estimate. Source exists_physicalWindow_variation was publicized/reused, direct21499 clean. Wired/exact-indexed. Lint88389 reports twelve unrelated unreachable leaves, no BAG debt; global lint is not clean. This is a structural mass producer for the literal proposed weight. C28.35’s complete signed target error and actual positive self-return count remain open; no RH consequence asserted.

C28.37 grade-band search78426 completed partial64350/64350; all20+20 statements inspected, no applicable physical prime-moment producer. Candidate still needs direct signed arithmetic work. In particular, an all-height/all-target Gaussian moment claim is not licensed by F328’s mass lower bound, the random-law moment identities, or formal connected-moment recursions. No new conditional wrapper added.

**C28.38 actual prime packet fourth-moment obstruction — PAPER, Lean in progress.**
The C28.37 scalar moment conjecture concerns the actual full-window coefficient family. Before asserting any broader energy/flatness-only producer, test the prime-supported case of the F327 coherent kernel. The source prime-window PNT and pigeonhole principle give the following concrete construction, without short-interval lower-bound assumptions: for every sufficiently large natural m, partition (64*m^8,128*m^8] into64*m^4 integer cells of width m^4. The PNT gives at least64*m^7 primes in the full dyadic interval, so one cell contains at least m^3 primes. Its lower endpoint N lies between64*m^8 and128*m^8; H=m^4 satisfies the exact F327 coherence and plateau conditions. Thus the entire physical chi-four packet with all-one prime coefficients has negative real integral at most-(pi*sqrtN/8)*card(S)^4. Taking absolute values, with no omitted terms, forces

`integral W*norm(sum_{p in S} p^(it))^4 >= T*(m^2/128)*card(S)^2`,

where T=(4*pi/3)*N and the constant is deliberately non-sharp. Dividing all coefficients by sqrt(card S) gives unit quadratic energy, maximum coefficient tending to zero, and an unbounded actual physical fourth moment per unit height. This would disprove a uniform Gaussian/energy-only fourth-moment bound even for actual prime supports. Positive survivor is the explicit unbounded prime-supported physical fourth-moment family, together with its signed chi-four orientation. It does not falsify C28.37's particular full-window family or retire BAG. Source CompactGaussianPrimePacketCapacity already says a coherent narrow packet contributes onlyO(1/logN) in the actual normalized target channels; the new conclusion must not be misreported as arbitrary target synthesis.

Corpus searches3256 and64414 completed nonpartial64353/64353 and64354/64354, all20+20 statements inspected. No direct dense short-prime packet producer returned. Read actual PrimeWindowLogPowerCount lower theorem, F327 complete physical packet, and mathlib finite pigeonhole statements; the construction above derives its own dense packets by partitioning a dyadic PNT interval. The available Selberg/Dirichlet-power high moments retain full support error; inspected Type-I Heath-Brown source receiver controls a different large-value set with its block costs, not the required signed moments.

**C28.38 / F329 FINAL — actual prime-supported signed quartic obstruction, LEAN PROVED.**
`ChiPrimePacketFourthMoment.lean` direct43285 passed without warnings; all five public theorem and both definition audits64654 use only propext, Classical.choice, Quot.sound. Dyadic source PNT and finite pigeonhole construct the required prime packets unconditionally. On the identical witnesses, the normalized polynomial Q has coefficient energy1, maximum coefficient<=1/m, original real integral of W*chi^4*Q^4<=-T*m²/128, and integral W*normQ^4>=T*m²/128. The negative orientation is retained before the norm consequence; every prime quadruple and both physical source remainders remain. The exact no-uniform-bound theorem is proved by eventual contradiction. Positive survivor and failed estimate are closed together in `../5-failed/bag-prime-energy-only-fourth-moment.md`. Wired/exact-indexed; lint54118 thirteen unrelated unreachable leaves, no BAG debt. The global gate is not clean.

This advances the moment obstruction from arbitrary integers to actual prime supports, exact unit energy and vanishing individual coefficients. It does not falsify the actual full-window coefficient candidate C28.37. The next producer must exploit its source cofactor structure. Exact source `CompactGaussianNormalizedChannel` defines the coefficient through the truncated Gaussian cofactor at R=N/p; its physical application uses the height-shifted retained phases. Consequently a static arbitrary flat vector, or a frozen-cofactor moment substituted without transport, would not discharge the actual field. Full signed balanced moments, adjacent chi grades and the complete compact self-target error remain the hard open obligations. Search15571 nonpartial64364/64364 returned no applicable physical high-moment producer; all20+20 statements inspected. Its suggested zero-configuration logMoment ingredients have a different domain and are not used.

**C28.39 actual Gaussian prime rational-saddle law — PAPER candidate, OPEN.**
The C28.37 adjacent-grade problem must keep arithmetic phase bias. Source `ZetaChiDualRatioAtom` and the complete F315 kernel identify a rationally twisted prime saddle with phase exp(2*pi*i*a*p/q). On primes this does not have the complete-integer geometric cancellation of `ZetaChiRationalSaddleCancellation`. The source already proves PNT in each reduced residue class (`PNTPlus.Consequences.chebyshev_asymptotic_pnt`, from `WeakPNT_AP`). Thus the conjectured leading coefficient is the finite reduced-residue character average, not zero.

Concrete producer to prove: fix positive rational xi=a/q and take the ENTIRE prime band N<p<=2N with literal critical dual coefficient V(p/N)/sqrt(p), where V is the actual Gaussian AFE cutoff. At T=2*pi*xi*N, multiply its physical field by chi(linePt t), exp(i*t*log xi), and the actual W(t/T). The full F315 main is 2*pi*sqrt(xi)*W(p/N)*V(p/N)*exp(2*pi*i*a*p/q). After multiplying the full integral by logN/N, its limit should be

`2*pi*sqrt(xi) * [sum_{r<q,gcd(r,q)=1} exp(2*pi*i*a*r/q)/phi(q)] * integral_1^2 W(x)*V(x) dx`.

All primes in the band, the actual Gaussian factor, and both physical kernel remainders must remain. The plan is to derive the smooth weighted prime-residue limit by Abel summation from the source AP PNT, then aggregate the complete actual kernel. This is a needed fixed-rational source main inside the mixed moments, not the growing-degree closure: uniform control of growing product denominators and all signed target couplings remain open. No conditional AP estimate, Gaussian law, or missing cancellation may be introduced as a premise. In particular denominator2 predicts a negative main rather than cancellation.

C28.39 dependency-closed paper proof: source AP Chebyshev PNT gives theta_r(x)/x ->1/phi(q). For a C1 profile f with f(1)=f(2)=0, scaled Abel summation gives sum_{N<p<=2N,p=r(q)}log(p)f(p/N)/N -> integral(f)/phi(q). On this band abs(log(p)-log(N))<=log(2), and the source global Chebyshev bound gives card*log(N)<=2N*log(4); hence removing the logarithmic prime weight changes the normalized sum by O(1/log(N)). Every sufficiently large prime is coprime to fixed q, so exact residue-fibre decomposition gives the full periodic weighted limit. The literal f=W*V is C1 and vanishes at both endpoints by the actual bump support.

For the full physical kernel at T=2*pi*xi*N and a_saddle=2*pi*xi*p, the grade-one Fresnel phases cancel exactly. Multiplication by V(p/N)/sqrt(p) gives 2*pi*sqrt(xi)*f(p/N)*exp(2*pi*i*xi*p). The complete stationary plus actual/model error is at most C(xi)/N per prime. The elementary full-band cardinality bound <=2N therefore leaves a bounded TOTAL error, which vanishes after log(N)/N normalization. No prime or endpoint error is deleted. The profile integral has strictly positive real part since both factors are positive on (1,2). At xi=1/2 the only reduced class has phase -1; the complete physical integral thus has eventually negative real part. This is an actual signed prime-field result. It is not an estimate for the full cofactor field or growing radial moments. Production leaf ChiPrimeGaussianRationalSaddle is wired; final direct check and axiom audit remain pending.

**C28.39 / F330 FINAL — full Gaussian prime rational saddle and negative half-frequency, LEAN PROVED.**
`ChiPrimeGaussianRationalSaddle.lean` direct final89276 exited0; all18 public theorem/definition axiom checks81766 use only propext, Classical.choice, Quot.sound. The final rational saddle formula and eventual strict negative real integral at xi=1/2 are both unconditional source theorems. No AP bound, amplitude regularity or stationary approximation is assumed. The direct check emits an informational `ring_nf` suggestion, with no errors or linter warnings. Wired into RHTower without an umbrella build; exact source index37086 finds the capstone. Lint30580 reports twelve unrelated unreachable modules and no error for this BAG leaf; global gate remains unclean. This closes the fixed-rational arithmetic component only. The full growing-degree/cofactor target problem and RH remain open.

**C28.40 inverse stationary operator remainder — conjecture history; closed in Lean below.**
C28.39 succeeds for one prime band because its complete coefficient-weighted remainder sums to O(1). For the growing adjacent moment chi*P^(k+1)*conj(P)^k, taking the absolute value of every expanded kernel remainder introduces the (2k+1)-st power of the coefficient L1 mass. The fixed-entry kernel estimate alone therefore cannot justify a useful relative moment error. This is an obstruction to that proof step, not a falsification of the actual moment conjecture. The full signed remainder must be controlled before expansion.

Candidate mechanism from the corpus's complete grade-one kernel and both-orientation smooth Morse/Fresnel family: put a(lambda)=2*pi*exp(lambda), K_T(lambda)=sqrt(2*pi*a(lambda))*W(a(lambda)/T)*exp(i*a(lambda)), and let R_T(t)=(1/(2*pi))*integral_R K_T(lambda)*exp(-i*t*lambda) d lambda. K_T is the entire compact smooth stationary frequency kernel. Conjecture one source C with |R_T(t)-W(t/T)*chi(linePt t)|<=C/T for T>=4 and t in[T,2T]. Then Cauchy-Schwarz bounds the COMPLETE remainder against any two L2 physical inputs supported in[T,2T] by (C/T)*norm(f)_2*norm(g)_2, independent of prime-product support cardinality or moment degree. The signed main remains the full frequency integral against the Fourier transform of f*conj(g); finite-window smearing must be retained, not replaced by a bare discrete saddle matrix.

Corrected paper route: substitute a=t*(1+v) in the inverse integral. Its phase is t-t*log(t/(2*pi))-t*logRemainder(v), where the actual corpus logRemainder(v)=log(1+v)-v. It is NOT logPhaseProfile(v)=v-(1+v)*log(1+v); that proposed identification was false and is rejected. The amplitude is sqrt(t/(2*pi))*(1+v)^(-1/2)*W((t/T)*(1+v)). The positive Fresnel orientation should give exp(i*(t-t*log(t/(2*pi))+pi/4))*W(t/T), precisely the critical conductor model. The proposed next remainder has order1/t after this scaling, but requires the inverse phase analysis below. Need build a jointly smooth compact extension of the actual weighted amplitude, retain and estimate its entire nonstationary complement, and use the source pointwise chi/model error. No inverse-kernel bound may be assumed. Existing LogPhaseFullPhysicalStationary covers W without this inverse amplitude; SmoothQuadraticFamily supplies both orientations but requires an actual smooth compact family. Search97531 is auditing prior inverse-operator work. This candidate would remove a growing-degree remainder cost; arithmetic signed moments, finite-window convolution, the moving Gaussian cofactor and full self-target positivity still require proof.

C28.40 source audit97531 completed nonpartial64397/64397; all20 candidate and20 source statements inspected. No inverse stationary operator remainder returned. The applicable source remains the existing exact conductor model, full forward kernel, arbitrary-smooth-window local Morse family and general nonstationary family; the suggested arithmetic-reflection remainder has a different domain and is not applicable. A useful simplification of the new inverse amplitude is H(x)=W(x)/sqrt(x), set by ordinary total real division. Since W vanishes outside[1,2], H is globally smooth despite the apparent singularity at zero. For p=t/T in[1,2], (1+v)^(-1/2)*W(p*(1+v))=sqrt(p)*H(p*(1+v)). The H amplitude simplification survives, but the required complete formula must use logRemainder, not logPhaseProfile. The source ChiDualSpatialStationary already treats the correct phase through a cubic local approximation, with central/exterior variation costs; it does not supply the required complete smooth inverse-operator remainder. Build the exact signed Morse coordinate for logRemainder, its analytic inverse, H's source smoothness/support, the full complement, exact logarithmic substitution and L2/Fubini transfer. No inverse reconstruction theorem is presently claimed in Lean.

C28.40 dependency-closed corrected paper argument: put H(x)=W(x)/sqrt(x), globally smooth because the literal W vanishes on x<=1 and x>=2. For F(v)=log(1+v)-v, define M(v)=sgn(v)*sqrt(-2F(v)). The second divided difference removes the apparent singularity at zero, giving M analytic, M'(0)=1. For v>-1 and v!=0, M'(v)=[1-(1+v)^(-1)]/M(v)>0. Thus a single analytic local inverse has positive Jacobian, and exact substitution gives a quadratic saddle. Joint smoothness of H(p*(1+v)) for p in[1/2,4] gives the uniform local C/(t*sqrt(t)) error. On the complete complementary compact amplitude, F' has no zeros; two signed integrations by parts give C/t² with every endpoint term zero by the actual support. This proves the full oriented inverse-phase formula, with both transitions and exterior retained.

Define Rheight(T,t)=sqrt(T/(2*pi))*integral_R H(x)*exp(i*(T*x-t*log(T*x/(2*pi))))dx. Exact x=(t/T)*(1+v) substitution and conjugation give main W(t/T)*exp(i*(t-t*log(t/(2*pi))+pi/4)), with one C/T error on[T,2T]. The literal frequency kernel vanishes outside[log(T/(2*pi)),log(2*T/(2*pi))]. On x in[1,2], lambda=log(T*x/(2*pi)) has derivative1/x, and its full Jacobian identity is sqrt(2*pi*T*x)*W(x)/((2*pi)*x)=sqrt(T/(2*pi))*H(x). Hence Rheight equals the originally defined inverse-frequency R_T exactly. The source actual/model bound26/t and W<=1 yield |R_T-Wchi|<=C/T.

For arbitrary physical L2 inputs on[T,2T], Hölder bounds the complete remainder pairing by(C/T)*normf*normg. K_T is continuous and compactly supported. The full Fubini integrand is dominated by normK_T(lambda)*norm(f(t)*conj(g(t))), an integrable product. Thus the signed main is exactly (1/(2*pi))*integral_lambda K_T(lambda)*[integral_[T,2T] exp(-itlambda)*f(t)*conj(g(t))dt]d_lambda. This preserves finite-window smearing and every coefficient before expansion. Scratch implementation /tmp/BagChiInverseStationaryKernel01a0.lean is checking this capstone; production/direct/axiom audit pending. No signed-main positivity, growing moment asymptotic, cofactor transport, or RH proof is inferred.


**C28.40 / F331 FINAL — complete inverse stationary operator remainder, LEAN PROVED.**
LogRemainderMorse direct67664 and ChiInverseStationaryKernel direct53640 both exited0 warning-free. All23 public theorem/definition audits98968 use only propext, Classical.choice, Quot.sound, including the simp zero theorem. Both leaves are wired into RHTower; no umbrella build was run. Exact source index finds exists_chiStationaryFrequencyKernel_bilinear_remainder. Lint16109 reports twelve unrelated unreachable modules and no error for these BAG leaves; the global gate remains unclean.

The complete original K_T inverse is uniformly within C/T of actual W*chi on[T,2T]. Its exact frequency pairing preserves the full finite-height Fourier transform, and its bilinear error is bounded by(C/T)*normf_L2*normg_L2 for arbitrary physical L2 inputs. No coefficient support, moment degree, supplied asymptotic bound, amplitude regularity, or Fubini integrability premise enters the final producer. The source constructs all analytic inputs. This solves C28.40's analytic remainder problem, not C28.37's full signed arithmetic main or moment-ratio problem. The L2 norms are physical norms on[T,2T]; relative comparison to a W-weighted growing moment still requires the appropriate norm/window control. Actual moving Gaussian cofactor transport, complete C28.35 target error, MUST270 and RH remain open.

**C28.41 complete cubic signed prime main — signed cancellation OPEN; analytic reduction proved below.**
Take the literal F330 field P_N=primeGaussianChiField 1 N and T=2*pi*N. Its complete adjacent cubic moment is integral W(t/T)*chi(linePt t)*P_N(t)^2*conj(P_N(t)). The F315 kernel applies to EVERY prime triple p,q,r in(N,2N], since a=2*pi*p*q/r satisfies a/T in[1/2,4]. Its predicted full arithmetic main is

`2*pi * sum_{p,q,r} V(p/N)*V(q/N)*conj(V(r/N))/r * W(p*q/(r*N))*exp(2*pi*i*p*q/r)`.

Here V is the actual smoothAFECutoff, not an arbitrary coefficient family. The full kernel entry error is O(N^(-1/2)); the three source coefficients supply O(N^(-3/2)). Source PNT would therefore make the summed analytic error O(N/log(N)^3), below the repeated-prime scale N/log(N)^2. These cubic reductions are paper calculations, not yet Lean theorems.

The repeated-prime part p=r or q=r has exact contraction form 2*v_N times the untwisted first saddle main, minus the all-equal intersection. The hard unresolved term retains ALL triples with p!=r and q!=r, phase exp(2*pi*i*(p-r)*(q-r)/r), and the coupled window W(p*q/(r*N)). Test whether this signed off-diagonal is o(N/log(N)^2), rather than assuming it. Fixed-modulus Fourier/Kloosterman norm bounds and absolute affine-pair sieve counts do not supply the required saving. The phase has not been identified with a Kloosterman sum. A Gaussian cubic asymptotic, growing-degree moment law, or target-error certificate is not asserted.

Current source audit: physical-cofactor search15347 nonpartial64423/64423 and cubic-prime search71859 partial64425/64425, all20 candidate and20 source statements inspected for each; proposed ingredients do not prove the signed off-diagonal. The existing ChiDualMaskedSignedGram already expands the moving physical coefficients exactly, so no duplicate transport wrapper is needed. Next attack is signed near-diagonal/modulus interaction, not coefficient-energy or constant optimization.

C28.41 paper refinement: the entrywise argument needs only the corpus Chebyshev upper count, not a new PNT error. Exact cubic amplitude cancels sqrt(p*q*r) to 1/r; the source kernel bounds every weighted entry by C/N^2, and card(primeProfileBand N)*logN<=2*log4*N gives the complete C*N/logN^3 error. Consequently logN^2/N times the full analytic error tends to zero. The pending Lean draft includes the literal P_N integral, the explicit signed three-prime main, its exact repeated-prime contraction minus the all-equal intersection, and exp(2*pi*i*p*q/r)=exp(2*pi*i*(p-r)*(q-r)/r). No off-diagonal sign is inferred from these identities.

The tentative cancellation mechanism must also retain rational resonances away from the central triple diagonal. The fixed-rational F330 producer shows that the inner prime phase has nonzero arithmetic bias near low-denominator rational q/r. An argument replacing the prime weights by a smooth density solely near p=q=r would miss these regions. Existing von Mangoldt scaled envelopes and TypeIIEnergyBound concern logarithmic/nearDiagonalPhase twists, not the literal additive phase p*q/r; no transfer has been proved. The off-diagonal o(N/logN^2) candidate remains a conjecture, not an estimate supplied to Lean.

C28.41 failed bound attempt, not a falsification: after separating the smooth coupled window by its source logarithmic Fourier representation, a fixed-r Parseval/Cauchy bound costs sqrt(r) times the two prime coefficient L2 norms. With card~N/logN, summing r absolutely and retaining the 1/r amplitude gives size N^(3/2)/logN^2, a factor sqrtN above the contraction scale. Thus this particular norm argument cannot establish the cubic candidate. A pointwise minor-arc bound for the inner p sum followed by absolute q,r aggregation likewise leaves an extra full summation scale. The next signed arithmetic argument must preserve cancellation across the q,r average, including rational resonant regions; no fixed-modulus energy estimate or pointwise linear prime-sum bound is being substituted for that task.

**C28.41 / F332 FINAL — complete cubic analytic reduction and exact contractions, LEAN PROVED.**
`ChiPrimeGaussianCubicMain.lean` direct39221 exited0 warning-free. All14 public/new/reused declaration axiom checks9433 exited0 with only propext, Classical.choice and Quot.sound. Source ChiPrimeGaussianRationalSaddle publicized primeProfileBand_mem and physicalChiGradeOne_second_error for reuse; its direct96494 passed. The new leaf is wired into RHTower without an umbrella build, and exact source index92035 finds tendsto_primeGaussianCubic_normalized_error. Lint24675 reports ten unrelated unreachable modules, no BAG error; global lint remains unclean.

The literal full cubic moment, its explicit complete arithmetic main, the uniform C*N/logN^3 total error and the normalized vanishing error are all proved without an assumed analytic estimate. Exact contraction decomposition subtracts the all-equal overlap once and retains the complete noncontracting signed sum. The gap-phase recentering is exact. This closes the analytic reduction and identifies a concrete arithmetic invariant; it does NOT close C28.41's off-diagonal conjecture, C28.37's growing moments or C28.35's self-target error. Next determine the actual normalized signed off-diagonal limit; zero is a conjecture to test, not a premise. A nonzero limit would correct the proposed moment law, not retire BAG. MUST270 and RH remain unproved.

**C28.42 hyperbolic coherent core in the actual full prime band — new conjecture, OPEN.**
F332's exact gap phase suggests a source-specific arithmetic obstruction to discarding coherent off-diagonal terms. Conjecture: along cofinal conductors there is a subfamily of noncontracting triples from a fixed interior portion of the literal full prime band whose phases have uniformly positive real part and whose actual Gaussian cubic-main contribution is at least c*N/log(N)^2, c>0. This does not assert that the COMPLETE off-diagonal has nonzero limit: the remaining signed terms may cancel it. The target is a positive arithmetic survivor on the actual coefficient family, not an arbitrary flat-coefficient packet.

Proposed paper mechanism, to be proved: choose a fixed large integer K and N=K^(4m). For j<m take coarse width L_j=K^(2m+j) and fine width h_j=K^(2m-j-1), so h_j*L_j=N/K. Use all primes in a fixed interior interval, for example[3N/2,25N/16]. Source PNT supplies total mass >=c*N/logN. Independently partition the full length-N frame into h_j and L_j cells. Discard cells whose prime population is below a fixed fraction of width/logN; the total discarded prime mass is bounded by that fraction of N/logN. Every retained anchor r consequently has >=c*h_j/logN distinct fine-cell partners p and >=c*L_j/logN coarse-cell partners q. The source Brun--Titchmarsh upper bound 292*H/logH, already proved in CompactGaussianPrimePacketCapacity, excludes only a small fraction of q with abs(q-r)<=L_j/K when K is fixed sufficiently large. Thus at each scale there are >=c*N^2/logN^3 triples with abs(p-r)<=h_j and L_j/K<abs(q-r)<=L_j. These q-gap annuli are disjoint as j varies, yielding the essential factor m~logN. The exact F332 phase has abs(2*pi*(p-r)*(q-r)/r)<=2*pi/K, while all saddle ratios stay in the actual W=1 plateau; the actual V has a positive minimum on this fixed compact interval.

This argument requires real finite-fiber counting, disjoint-scale aggregation, actual source prime counts and uniform short-interval upper bounds. None is to be assumed in a final producer. It is not yet a Lean theorem. Signed-modulus query41683 returned partial64440/64440; all20+20 statements and proposed ingredients inspected, no applicable signed-average theorem. Its suggested Hahn/triLinear algebra is unrelated to the cubic phase. New hyperbolic-core search92810 pending.

C28.42 dependency-closed paper proof, strengthened to the ORIGINAL physical cubic contribution: set K=10000000 and N=K^(4m). The source PNT gives at least N/(64 logN) primes in (3N/2,25N/16]. For each j<m, fine/coarse sparse-cell deletion costs at most N/(512 logN) each; at least N/(128 logN) anchors remain. Fine width h_j eventually exceeds 2048 logN, leaving h_j/(2048 logN) distinct partners after deleting the anchor. The source Brun--Titchmarsh bound, with D=L_j/K and log(2D)>=logN/4, bounds all near coarse partners by 2336 L_j/(K logN)<=L_j/(2048 logN). Thus each scale supplies at least N^2/(536870912 K logN^3) triples. Disjoint q-gap annuli and logN=4m logK give card(core)>=c_card*N^2/logN^2, c_card=1/(2147483648 K logK)>0.

Every triple has p!=r and q!=r, all three primes in the literal full band. Its saddle pq/(rN) lies in [5/4,7/4], where the source height window equals 1. The exact hyperbolic phase has absolute argument at most 2*pi/K<=1/2; source one-Lipschitz oscillation gives real part at least 1/2. The source real antitone Gaussian cutoff bounds all three factors below v=Re V(2)>0. Hence every arithmetic main entry has real part at least v^3/(2N). F332's unconditional uniform full physical entry remainder C/N^2 leaves real part at least v^3/(4N) eventually. Summing over the actual core gives physical real contribution at least (c_card*v^3/4)*N/logN^2. No short-interval PNT, prime-pair asymptotic or assumed correlation is used. Lean counting and source geometry have checked; final phase/amplitude transfer and production audit remain pending.

Scope: this is a positive noncontracting subfamily at the SAME scale as the repeated-prime contractions, using the ACTUAL full-band Gaussian coefficients. It is not a signed lower bound on the whole off-diagonal. Any proof that the complete off-diagonal is negligible must retain and balance this contribution with its complement. The complete signed arithmetic average, growing moments, moving cofactor compatibility and self-target positivity remain open.

C28.41 next proof mechanism under investigation, grounded in F332 and the C28.42 actual core: organize p*q=n as the literal weighted semiprime convolution of length N^2 before averaging r~N. For prime r, p!=r and q!=r are exactly r not dividing n. Separate the uniform nonzero-residue component (whose complete additive-character sum is -1) from the centered residue discrepancy, retaining W(n/(rN)), the Gaussian factors, and the signed sum over r. This is a proposed arithmetic mechanism, not a proved cancellation theorem. The target is the actual centered additive discrepancy summed over prime moduli at the square-root-of-convolution-length scale; ordinary fixed-r Parseval, absolute residue discrepancies, or the N+M^2 Farey sieve factor do not discharge it. No new Lean wrapper is warranted until a source arithmetic saving is proved. Corpus semiprime-dispersion search is pending.

**C28.42 / F333 FINAL — actual noncontracting hyperbolic prime core, LEAN PROVED.**
Module: `formal/GaloisForLFunctions/RHTower/ChiPrimeGaussianHyperbolicCore.lean`. Public declarations: explicit `primeGaussianHyperbolicConductor`, its cofinality, actual triple set `primeGaussianHyperbolicCore`, `exists_primeGaussianHyperbolicCore_card`, `exists_primeGaussianHyperbolicCore_physical_mass`, and full-band/noncontraction/gap membership. The physical-mass capstone has no external analytic or prime-distribution premise. The pre-existing source `bagPacket_primesBetween_le_div_log` was publicized without changing its proof.

Final direct leaf53590 exited0 without warnings using `lake --old env lean -o ... <leaf>`. All six public declarations and the publicized source theorem passed /tmp axiom audit58527: only propext, Classical.choice and Quot.sound. Umbrella wired, exact source index34365 finds the capstone, no umbrella build. Lint90928 remains globally unclean because of thirteen unrelated unreachable leaves; no new BAG error. The failed first direct run's one real-part simplification was repaired before the successful final audit.

New knowledge: actual full-band Gaussian coefficients contain a positive noncontracting physical core at precisely the repeated-prime contraction scale, without any short-interval prime asymptotic or higher prime-correlation premise. This advances the arithmetic frontier beyond the arbitrary packet obstruction. It neither determines the full signed cubic limit nor supplies the growing-moment/self-target certificate. The next proof must retain cancellation between this core and the actual complementary triples.

Semiprime-distribution search95340 completed nonpartial with inventory64456/64456; all20 candidate+20 source statements and the proposed ingredient set were inspected. Returned prime-reservoir existence, generic convolution and summatory-swap statements do not supply the needed centered prime-modulus additive discrepancy bound. In particular, merely regrouping p*q or applying the ordinary Farey/Parseval bound does not solve it. The semiprime organization remains a mathematical mechanism to attack; no cancellation theorem has been asserted or formalized from those hits. C28.41, C28.37, C28.35, MUST270 and RH remain OPEN.

**C28.43 actual cubic signed-part divergence — new conjecture, OPEN.**
F333 proves a positive coherent core at the contraction scale. The next source-specific test is stronger: along its same cofinal conductors, BOTH positive and negative real parts of the COMPLETE physical noncontracting prime-triple family, normalized by log(N)^2/N, tend to infinity. This would establish a genuine signed-cancellation obstruction on the actual Gaussian family, not merely on arbitrary coefficients. It does not assert any value for the net off-diagonal.

Corpus basis: F333's global PNT/sparse-cell/BT pair construction; `PrimeShortIntervalsFiveEighths.exists_theta_window_lower_five_eighths` (every-window theta lower bound for exponent above 5/8); F332's exact gap phase and complete per-entry C/N^2 remainder; actual Gaussian positivity and W plateau. Semiprime residue search17033 nonpartial64458/64458 returned all12 candidate+12 source statements, inspected: none supplies the signed discrepancy estimate. The suggested cardinal/Mobius matching ingredients do not bound additive characters. Direct source inspection confirms the ndPhaseExp Vaughan estimates use T*log(1+r/u), so they cannot be substituted for pq/r. Ordinary Parseval and Farey bounds preserve the known loss. This is a failed proof attempt, not a falsification of the signed cubic conjecture.

Proposed dependency-closed paper mechanism: use N=K^(4m), K=10000000 and h=K^m=N^(1/4). Global central prime mass, deletion of sparse width-h cells and the source upper sieve give >=c*N*h/log(N)^2 ordered prime pairs (r,p) in the central band with h/K<d=abs(p-r)<=h. For each such pair take k=1,...,floor(d/128). Positive q-windows satisfy d*(q-r)/r in[k,k+1/12]; negative windows satisfy it in[k+1/2,k+7/12]. All lie between r and r+N/32 eventually, remain in the literal full prime band and keep pq/(rN) in the W=1 plateau. Their common length r/(12d) is >=N/(12h), so it eventually dominates (2N)^(2/3). The source every-window theta lower bound then gives >=c*N/(d*logN) primes in EACH window. Disjoint k-windows, of which there are >=d/256, supply >=c*N/logN q partners of EACH sign for every pair. Exact integer phase shifts and the source Lipschitz oscillation give real phase >=1/3 or <=-1/3, also when p<r by conjugation. The actual positive Gaussian factors and uniform physical entry error preserve the sign with size >=c/N. Hence each signed part has mass >=c*N*h/logN^3. Its normalization is >=c*h/logN -> infinity. No prime-pair asymptotic, short-interval equality, probabilistic model or assumed cancellation is required. All of this is still pending proof/Lean audit; do not claim the signed-part capstone yet.

This test addresses the complete physical family's signed variation, not an optimization of constants. If proved, no uniformly bounded positive-part or negative-part majorant at the contraction scale can settle the net sum. The remaining arithmetic producer must genuinely balance these growing contributions.


**C28.43 / F334 FINAL — both complete actual signed parts diverge, LEAN PROVED.**
`RHTower.primeGaussianCubicSignedVariation` in `ChiPrimeGaussianCubicSignedVariation.lean` is the complete full-band physical Jordan part, with Bool false/true selecting positive/negative real part and only the repeated-prime contractions excluded. `RHTower.tendsto_primeGaussianCubicSignedVariation` proves that BOTH parts multiplied by `log(N)^2/N` tend to infinity on the explicit cofinal conductors. The preceding paper mechanism is now fully formalized, including the source near-pair producer and complete physical entry error. Definitions and all auxiliary universal binders introduce no external mathematical premise.

Final source67882 and leaf66593 checks passed without warnings using `lake --old env lean -o ... <leaf>`. All16 new/reused public declarations passed /tmp axiom audit96086, with only propext, Classical.choice and Quot.sound. The leaf is wired and exact-indexed. Lint10435 reports eleven unrelated unreachable leaves and no new BAG error; global gate remains unclean. No umbrella/full build, computation, heartbeat change or subagent was used. The precise one-sided/absolute estimate is retired with its positive survivor on `../5-failed/bag-actual-cubic-one-sided-control.md`.

This IS new actual-family frontier knowledge: every contraction-scale proof must balance signed contributions individually diverging at that scale. It is NOT a bound on their difference. The complete signed cubic, growing moments, actual moving cofactors, C28.35 self-target error, MUST270 and RH remain open.

**C28.44 signed source pairing — investigation, not a proved conjecture.**
Inspecting the actual source of C28.43 shows that `chebyshevLagWindow_div_eq` retains an absolutely convergent SIGNED zero response, while `psi_window_ge_sub_tsum` takes absolute values afterward. Thus there is source information that the lower-window theorem discards. A possible proof mechanism is to pair opposite q-phase sectors inside each actual prime pair BEFORE bounding the zero response, and then retain the p,r average. Prime-power corrections and endpoint windows must remain.

The first attempted shortcut fails at the level of what the estimate would establish: even uniform relative o(1) agreement of the two sector masses leaves o(N*h/log(N)^3), which need not be o(N/log(N)^2) because h/logN diverges. The new producer must gain from signed oscillation at the required scale, not merely improve the lower-window constant or prove equidistribution with no rate. The source every-window bound alone supplies neither such a rate nor pairing. The exact lag formula concerns a smoothed psi statistic, so replacing literal prime weights by it also requires a proved transport and prime-power correction. No new wrapper or conditional theorem is being formalized from this observation.

Search16605 completed nonpartial64478/64478; all20 candidate and20 source statements plus its ingredient set inspected. Its prime-deletion, generic Perron and conditional short-window hits do not discharge signed cubic cancellation. Compiler metadata is source-only; refresh incomplete/background-indexer. Direct source reads of ChebyshevLagZeroWindowTerm and ChebyshevShortWindowLowerBound identify the retained signed formula; WeilPositiveAlmostAllShortIntervals has a Weil-positivity premise and cannot be used unconditionally. Next attack remains joint signed p,q,r arithmetic, with a targeted reciprocal/trilinear corpus search in progress.


C28.44 reciprocal/trilinear search31247 completed nonpartial64480/64480; all20 candidate,20 source, the proposed proof idea and ingredient set inspected. The returned residue-field Gauss identities and additive-character definitions do not control the cubic. Direct source inspection of `KloostermanAnalyticFrontier` confirms an exact completion decomposition with full coefficient-L1 residual budgets, not the missing prime-modulus saving. `KloostermanGlobalCollisionCentered` subtracts the common-period mean exactly but its receiver still charges (#Q+1) times pointwise and average source energies. Neither gives the needed joint actual-prime cancellation by substitution. No failure of RH or the full signed cubic follows from these unsuccessful estimates.

A proposed algebraic pairing also fails: swapping p,q preserves the phase; reflecting q to 2r-q conjugates it and therefore preserves its REAL part, even before the unresolved requirement that the reflected integer be prime. Thus reflection cannot pair opposite real sectors. The remaining C28.44 target is arithmetic cancellation of the full centered semiprime residue discrepancy with its coupled physical weight, or an explicit signed-zero-response construction achieving the same contraction-scale saving. Exact regrouping, norm-only completion and qualitative window equidistribution have not solved this target.


**C28.45 complete-row cancellation across a widening near-diagonal band — LEAN PROVED (F335; final audit below).**
Corpus basis: F332 complete physical entry/main error and exact gap phase; F334 actual opposite-sign sectors; `exists_chebyshev_theta_power_log`; the source scaled Abel proof in ChiPrimeGaussianRationalSaddle; the actual smooth Gaussian/window profile. Proposed producer: on N=K^(4m), complete each q-row for central actual prime pairs with m^2/K<|p-r|<=m^3. Prove the sum of NORMS OF COMPLETED ROWS is o(N/log(N)^2), while both Jordan parts of the SAME triple family diverge after normalization. This would establish actual cancellation of individually divergent contributions, rather than another absolute obstruction. It does not settle the wider-gap complement, which remains required for full BAG cubic control.

Paper mechanism, now verified: set L=logN and a=p/r. Replacing W(a*q/N) by W(q/N) costs O(m^3/(N*L)) per physical row by the actual window's uniform derivative bound. Retain exact unweighting through g_l(x)=V(x)W(x)/(1+l*logx), l=1/L. The compact profile and its first two derivatives have uniform bounds for 0<=l<=1; g_l and its first derivative vanish at both endpoints. Two signed integrations give its Fourier integral O(1/tau^2), tau=2*pi*(p-r)*N/r. Quantitative theta-Abel summation gives the actual prime row O((1/d^2+epsilon_N*(1+d))/L), with epsilon_N decaying faster than every log power. The number of prime pairs is at most O(N*m^3/L), using global prime count and the integer gap bound. After normalization, the Fourier term is O(1/m), the coupled-window and full physical-kernel errors vanish exponentially, and the PNT error vanishes. No prime-pair asymptotic or cancellation assumption is introduced.

For signed variation, sparse-cell deletion at width m^3 retains >=c*N*m^3/L^2 actual pairs; deleting integer gaps <=m^2/K costs only O(m^2/K) partners per anchor. F334's q-sector mechanism applies since m^3<=N^(1/4) eventually, and gives both sign masses >=c'*N*m^3/L^3. Normalization grows like m^2. Every q is retained in the completed row. This mechanism is now fully formalized and audited in F335 below. Exact logarithmic unweighting is essential: its crude O(1/logN) replacement error is too large after summing the growing family.


**C28.45 / F335 intermediate checkpoint — row cancellation proved; superseded by full closure below.**
`RHTower.tendsto_primeGaussianCubicGapRowMass` in `ChiPrimeGaussianCubicRowCancellation.lean` proves the normalized sum of complete ACTUAL physical row norms tends to zero over ALL full-band pairs m²/K<|p-r|≤m³, K=10000000, on the existing conductors. This is stronger in pair coverage than the central-pair paper target. The proof retains exact logarithmic unweighting, C² endpoint cancellation, source theta error, the coupled-window transport, exact q=r subtraction and both complete physical remainders. Uniform actual prime Fourier and physical row estimates are also proved, without an external mathematical hypothesis.

Direct65060 passed via `lake --old env lean -o ... ChiPrimeGaussianCubicRowCancellation.lean`; its log contains an informational ring diagnostic, no errors or warnings. All nine public/new/reused declarations passed axiom audit18797, with only propext, Classical.choice and Quot.sound. Existing source publicizations passed direct11416 (RationalSaddle, informational ring diagnostic) and38734 (CubicMain, clean). New leaf wired and exact-indexed. Lint82228 reports ten unrelated unreachable leaves, no new BAG error; global gate remains unclean. No full/umbrella build, numerical experiment, heartbeat change or subagent.

This is verified signed-cancellation progress beyond F334's obstruction. It does NOT yet establish that the same band has divergent Jordan parts. That remaining part uses a drafted actual m³-cell pair producer and a generalization of F334's central-pair sector argument, both pending Lean checks. Full complementary gaps, the complete signed cubic, growing moments, actual moving cofactors, C28.35 self-target error, MUST270 and RH remain OPEN.


C28.44 continuation after completed-band cancellation: the remaining target retains the entire signed p,r average in the complementary gap ranges, including the small-gap range. Search99602 returned partial coverage64527/64527, with reranker/judge errors but usable20 candidate and20 source arguments plus ingredients, all inspected. Source compiler metadata is source-only; refresh incomplete/background indexer. Direct reads of BVPrimeWindowReciprocalReflection give reciprocal CONJUGATION, not an opposite-real-sign identity for the actual prime cubic. PrimeTailCoPoissonBoundary's Mellin identity is a right-half-plane Euler-log divided difference; it supplies no additive pq/r cancellation estimate. The Menon/Heath--Brown source retains a complete signed dyadic aggregate, but its actual `vonMangoldtTwist` is n^(-i*tau), as verified in VonMangoldtTwistPerron; its existing localization/box-selection bounds do not transport to pq/r or furnish the missing joint gain. No substitution, cancellation premise or wrapper was added. Building a source-specific joint additive-phase producer remains the mathematical task; the unsuccessful transfer is not a falsification of the full cubic conjecture.


**C28.45 / F335 FINAL — actual cancellation of individually divergent signed parts, LEAN PROVED.**
On the existing conductors N=10000000^(4m), `primeGaussianCubicGapPairs N (m²/10000000) (m³)` contains EVERY full-band pair in that gap annulus. Each `primeGaussianCubicCompleteRow` retains EVERY q in the literal prime band except its exact q=r contraction. The two unconditional capstones in `ChiPrimeGaussianCubicRowCancellation.lean` now establish:

- `RHTower.tendsto_primeGaussianCubicGapRowMass`: log(N)²/N times the SUM OF NORMS OF COMPLETED ROWS tends to zero.
- `RHTower.tendsto_primeGaussianCubicGapSignedVariation negative`: for EACH Bool sign, log(N)²/N times the real Jordan part of the EXACT SAME triple family tends to infinity.

The positive mass is itself source-built: `exists_primeGaussianPolylogPairs_mass` constructs at least c*N*m³/log(N)² actual central pairs by sparse-cell deletion and an elementary count of the excluded smaller integer gaps. `primeGaussianPolylogPairs_mem` proves exact prime/central/gap membership. `exists_primeGaussianCentralPair_signed_row` generalizes the already proved two-sign physical sector mechanism to every actual central pair with 256<=d<=N^(1/4). Their combination gives normalized variation >=A*m², A>0, on the very band whose complete rows cancel. No prime-pair asymptotic, cancellation input, external hypothesis or added axiom appears.

Final direct audits: HyperbolicCore11994 exit0 with one unnecessarySeqFocus style warning; generalized SignedVariation54339 exit0 clean; extended RowCancellation93703 exit0 with an informational ring diagnostic but no error or warning. Each used `lake --old env lean -o ... <leaf>`. Full32-public-declaration /tmp axiom audit1375 passed with only propext, Classical.choice and Quot.sound, including all three touched leaves and all reused publicized helpers. Leaf wired; both capstones exact-indexed. Lint28148 reports twelve unrelated unreachable leaves and no BAG error; global gate remains unclean. No umbrella/full build, numerical experiment, heartbeat change or subagent.

This advances the actual signed arithmetic frontier beyond F334's necessary-cancellation obstruction: an explicit widening family has genuine cancellation between contributions individually diverging at the required scale. Its SMALL-gap and LARGE-gap complements remain uncontrolled. The full signed cubic, C28.37 growing mixed moments, actual moving cofactors, C28.35 self-target error, MUST270 and unconditional RH remain OPEN. Goal remains ACTIVE; F335 is not an RH proof or falsification.

**C28.46 removing the small-gap obstruction — LEAN PROVED (F336; final audit below).**
The next conjecture strengthens F335 to every actual noncontracting pair with
`0 < |p-r| <= m^3`, with no lower cutoff, keeping the complete original physical q-row.
This is a new cancellation regime, not a change to a numerical constant. Source
`Sieve/GenericMarkerAnalytic.generic_pair_le'` gives, at the literal integer conductor N,
the complete averaged shifted-prime count up to d at most
`d*(2*pairMainConst*N/log(N)^2 + 2*N^(3/4))`. Thus its individual d-fibre is bounded by
that same expression. Summing the F335 row's inverse-square term over both orientations
gives at most `2*A_N*(1+log H)`, H=m^3, by the source harmonic-sum bound. After physical
normalization and the row's 1/logN factor this is
`O((1+log H)/logN + logN*(1+log H)/N^(1/4))`, which tends to zero.
The row's remaining three errors are uniform for d<=H and use the already proved
`#pairs <= #band*(2H+1)` and `#band*logN <= 2*log4*N`; their budgets still tend to zero.
All source sieve remainders are retained. No prime-pair asymptotic or unproved uniformity
is introduced. The large-gap range d>m^3, full signed cubic asymptotics, growing moments,
self-target error and RH remain open. The exact cutoff-free capstones and final audits are recorded below.

**C28.46 / F336 FINAL — all noncontracting near rows, LEAN PROVED.**
The complete 312-line scratch77375 and production
`ChiPrimeGaussianCubicNearCancellation.lean` direct79689 both pass with exit0 and no diagnostics.
The leaf is wired into RHTower without an umbrella build. Its two unconditional capstones are
`tendsto_primeGaussianCubicNearRowMass` and
`tendsto_primeGaussianCubicNearSignedVariation`: at the same N=10000000^(4m), every full-band
prime pair with `0 < abs(p-r) <= m^3` is retained, every physical q-row is complete apart from
its exact q=r contraction, normalized row norms tend to zero, and both normalized Jordan
parts tend to infinity. Thus the small-gap complement is closed, including fixed prime gaps.
The source sieve remainder is absorbed through the proved log²(N)/N^(1/4) limit; the row's
inverse-square term sums to a harmonic factor with an extra prime-density saving.
Both public capstones and the reused literal pair-sieve producer pass axiom audit9061 with
only `propext`, `Classical.choice`, `Quot.sound`. Authoritative lint8309 reports FIFTEEN unrelated unreachable modules,
no new BAG error; global lint remains unclean. Large-gap joint signed arithmetic, full cubic,
growing moments, self-target recurrence and RH remain open.

**C28.44 next attack after F336 — full large-gap arithmetic remains unproved.**
Organize the actual frequencies p/r into rational neighborhoods while retaining the complete
signed prime/cofactor sum; the target remains the centered semiprime residue discrepancy
averaged over prime moduli with its actual coupled weight. Source rational-profile and
full affine-sieve theorems suggest studying b*p-a*r, but they do not by themselves control
the joint complement. Search19857 is nonpartial64544/64544 with source/compiler freshness
mostly pending/stale; all candidate/source/ingredient statements inspected. Its generic
theta results are inapplicable. Directly checked `ChiPrimeGaussianRationalSaddle` and
`PNTPlus/Consequences.chebyshev_asymptotic_pnt`: reduced-class theta density is qualitative.
One cannot silently multiply this o(1) error by a growing frequency window or replace real
pq/r by modular unit inversion. A uniform source cancellation estimate must be constructed;
no such estimate, rational-ray capstone, full cubic asymptotic or RH theorem is claimed.

**C28.47 actual large-gap half-integer resonance — LEAN PROVED (F337; final audit below).**
Target the actual full q-rows with `abs(2*p-3*r)<=m^3`, p,r in the original full prime
band, at N=10000000^(4m). This is a macroscopic p-r gap, disjoint from F336 eventually.
Prime parity gives exact `exp(3*pi*i*q)=-1`; the residual frequency is
`pi*(2*p-3*r)*N/r`. No AP equidistribution hypothesis is needed for this phase split.
The actual frozen profile is `W(3*x/2)*V(x)`, whose lower band endpoint is NONZERO.
Thus the previous two-IBP endpoint-vanishing proof does not apply. Retain both Abel
endpoints and use one integration by parts, giving inverse-FIRST-power frequency decay.
The moving W amplitude differs by at most C*abs(2*p-3*r)/N; both physical kernel
remainders and q=r contraction exclusion remain explicit.

Arithmetic mechanism: use F323's literal full dilation-pair sieve with A=2,B=3,
P1=3 and its actual finite remainder. Every sifting prime is at least5, hence
p/(p-1)<=p^(1/4), since (p-1)^4-p^3=p^3*(p-5)+2*p*(3*p-2)+1>=0.
For nonzero v, the primes in the correction for6*abs(v) divide abs(v), so the entire
inverse singular factor is at most abs(v)^(1/4). The exact anchor and source remainder
are retained: each signed v-fibre is bounded by
`1+C*N*abs(v)^(1/4)/log(N)^2+2*N^(3/4)` eventually. Multiplying by the completed-row
1/abs(v) term and summing gives normalized budget
`C*H^(1/4)*(1+log H)/logN + C*logN*(1+N^(3/4))*(1+log H)/N`, H=m^3, tending0.
The other row errors use the elementary full-band pair count and also tend0.
Exact v=0 cannot occur for large primes (or directly by odd parity). This proposed
capstone would remove a genuine large-gap rational resonance while preserving the
hard original boundary. It is not the full large-gap discrepancy estimate, a lower
bound for affine prime pairs, a growing-moment theorem or RH. Formalization pending.

**C28.47 intermediate formal results (aggregate audit pending).** The actual frozen-profile
Fourier theorem and complete physical-row theorem are directly audited in
`ChiPrimeGaussianCubicHalfResonance` (production17659 exit0). The exact correction bound
and eventual actual dilation-pair producer passed scratch77812; production90739 is running
for `Sieve/PrimeDilationThreeHalves`. The full finite remainder and anchor can be absorbed
uniformly because every nonzero shift has fourth root≥1. This yields the cleaner total
budget `C*[H^(1/4)*(1+logH)/logN + H²*((1+H)/logN^13+(1+H)/(N*logN)+1/N)]`.
At H=m³ it tends to zero. Exact family aggregation is drafted; no aggregate theorem is
yet certified, and no full cubic or RH result is asserted.

**C28.47 / F337 FINAL — actual three-halves large-gap cancellation, LEAN PROVED.**
`RHTower.tendsto_primeGaussianCubicHalfResonanceRowMass` in
`ChiPrimeGaussianCubicHalfCancellation.lean` proves the complete stated family, with
no prime-pair asymptotic or cancellation premise. The literal definition retains
all band pairs at residual distance≤m³ and every q except the exact contraction.
At these conductors this is a genuine macroscopic p-r region, outside F336 eventually.
Unlike the old near family, no lower bound or divergence theorem for this family's
Jordan parts is claimed.

Exact proof: classify each nonzero Nat.dist(2p,3r) fibre into the positive and negative
actual dilation sets. The source sieve with its entire denominator and finite remainder
gives two prime-density savings. Combine the fourth-root singular cost with the actual
1/residual row decay; bound the resulting harmonic sum, and retain all uniform row
errors. The displayed normalized budget tends0 at H=m³. No endpoint, prime, coefficient,
physical kernel term or source remainder is silently discarded.

Scratch53515, physical source17659, arithmetic source90739 and aggregate source55859
all exit0 cleanly. Final direct commands use `lake --old env lean` and write the three
production oleans. All three leaves are wired in RHTower; no umbrella/full build.
Axiom66643 exits0: all seven public/new/reused declarations, including the exported
actual theta rate and prior complete-row/gap capstones, use only `propext`,
`Classical.choice`, `Quot.sound`. Exact index33564 finds the new
capstone. Formal lint7714 exits1 for12 unrelated unreachable modules, with no new BAG
error. All seven owned scratch sources/body/audit files were removed after verified success;
logs and search results remain. All owned Lean processes are terminal.

This is PROGRESS on the hard signed cubic route: it closes a macroscopic resonance with
an actual nonvanishing boundary, beyond the solved small-gap family. The full joint
signed complementary p,q,r discrepancy is still unproved, followed by C28.37 growing
moments, moving cofactors, C28.35 positive self-target error, MUST270 recurrence and RH.

**C28.48 — BAG rational major-arc arithmetic: actual character zero-free strip (LEAN PROVED, F338; AP transport remains open).**
F337 closes one parity resonance; the full joint signed cubic remains the target.
The current joint-dispersion attempt does not close it: the centered Kloosterman receiver
retains the common-period terminal-orbit budget, and the physical kernel is a complete
Kloosterman sum rather than the actual e(pq/r). Vaughan's exact identity alone supplies
no cancellation estimate. These are failed applications, not no-go theorems for BAG.

Construct the missing arithmetic source for rational neighborhoods instead of assuming
uniformity of the existing qualitative AP prime-density limit. Frozen target: for every
fixed positive modulus, every character has a high-height zero-free strip of width
c/(log|t|)^9. First prove the actual nonprincipal L-function's bounded-periodic-sum
truncation formula and O(log|t|) growth in Re(s)>=1-1/log|t|; Cauchy gives O(log²|t|)
derivative control. Apply the installed character 3-4-1 product (which couples chi and
chi²) and the actual principal-character Euler factors. Low heights require separate
compactness using installed nonvanishing on Re(s)>=1. Subsequent Perron transport to
quantitative reduced-class theta, then growing-frequency rational profiles, remains
part of this BAG input construction. No quantitative AP rate is inferred from a
qualitative limit, no conditional receiver is counted as a new result, and closing
this source input will not itself prove full joint cubic cancellation.

Corpus basis: `DirichletAbel`, `DirichletUniformAbel`, `DirichletLSeriesBridge`,
`ZetaVerticalGrowth`, `ZetaDerivGrowth`, `ZetaZeroFreeRegion`, installed
`LSeries/DirichletContinuation` and `LSeries/Nonvanishing` (actual character product).
Use the actual finite-period cancellation to discharge bounded sums; preserve conditional
ordered convergence separately from absolute summability. This is a construction of a
missing zero-exclusion mechanism, not optimization of F337's numerical constants.

**C28.49 — actual character Perron control (next frozen target; not Lean-proved).**
The C28.48 derivative and literal character 3-4-1 product suggest a stronger constructive
input than qualitative nonvanishing. Write K=characterLogStripConstant(Q), L=log|t|,
choose a=1/(4*32^4*K^8), and eta=a/L^9. Target all actual characters at |t|>=9 and
|sigma-1|<=eta:
`norm(L(chi,sigma+it)) > 16*K*a/L^7`, hence
`norm(L'(chi,sigma+it)/L(chi,sigma+it)) <= L^9/(2*a)`.

Paper argument to formalize: derivative control bounds the horizontal drift to 1+eta
by 16*K*eta*L². If the displayed lower bound failed, the value at 1+eta would be at
most32*K*eta*L². The principal pole factor is at mostK/eta and the actual chi² value
at2t at most2*K*L. Their 3-4-1 product would be at most
`(K/eta)^3*(32*K*eta*L²)^4*(2*K*L)=1/2`, contradicting its lower bound1.
Thus the lower bound is source-produced; it is not an added inverse-function premise.
Multiply its inverse by the proved derivative estimate to get the Perron integrand bound.
This is needed to construct quantitative AP prime asymptotics, not to optimize constants.

Next mathematical obligations: generalize the source zeta Perron contour argument to
actual chi*Lambda, retain all tails and horizontal edges, and unsmooth correctly. Complex
character sums are not monotone: either dominate their short-interval defect by the
already proved ordinary Lambda estimate or combine characters into positive AP sums
before applying the monotone sandwich. Then remove proper prime powers and perform
exact reduced-class orthogonality. Only after those source obligations close can growing
rational-frequency profiles use a quantitative AP error. The full joint complementary
p,q,r cancellation remains the principal BAG arithmetic target throughout.

**C28.48 / F338 FINAL — actual character zero-free input, LEAN PROVED.**
`DirichletLLogStrip.lean` proves the actual truncation remainder throughout Re(s)>0,
logarithmic growth for nonprincipal characters, then a common logarithmic bound for
all characters using exact principal Euler factors. The coefficient partial sums are
proved bounded by their period, and analytic uniqueness identifies the ordered Abel
limit with the literal LFunction. No absolute convergence below Re(s)=1 is asserted.
`DirichletLZeroFreeLogStrip.lean` proves the actual Cauchy derivative bound and
`exists_character_zero_free_log_strip`: for every positive Q there is c>0, common to
ALL characters modulo Q, excluding zeros for |t|>=9 and Re(s)>1-c/log^9|t|.
The character 3-4-1 product retains chi², including its principal case; the proposed
zero would force its norm to be at most1/2 instead of at least1.

The stronger complete-height capstone
`exists_nonprincipal_character_zero_free_log_strip` proves, for each actual
nonprincipal character, a positive width c_chi/log^9(3+|t|) at EVERY height.
A compact line segment thickens inside the actual nonvanishing locus, and the
high-height theorem supplies the complement. Its width may depend on the character;
no effective conductor-uniform low-height bound is claimed.

Scratch6 proves the analytic/derivative construction; scratch85849 proves the full
zero-exclusion package. Production40277 and64795 both pass cleanly with
`lake --old env lean <leaf> -o <olean>`. Axiom47323 passes cleanly: all nine new public
declarations and the reused exact character product depend only on `propext`,
`Classical.choice`, `Quot.sound`. Both leaves are wired into RHTower; no umbrella/full
build or heartbeat change. Exact lexical index finds the complete-height capstone at318.
Formal lint51021 exits1 for13 unrelated unreachable modules, with no new BAG error.

Evaluation: verified progress on a missing analytic prerequisite of quantitative
rational major arcs. The main joint signed cubic problem is NOT solved, and no AP
prime-rate or growing-frequency transfer follows without further proof. The next
constructive target is C28.49, followed by actual Perron/AP arithmetic and the full
joint p,q,r cancellation, growing moments, moving cofactors, self-target positivity,
MUST270 recurrence and RH. The goal remains active.

**C28.49 — constructive proof complete in scratch; production audit pending.**
Scratch91724 passes cleanly. It proves the frozen actual lower floor, reciprocal
bound, and log-derivative estimate, then constructs positive c_chi,B_chi with
`|sigma-1| <= c_chi/log(3+|t|)^9` implying both actual nonvanishing and
`norm(L'_chi/L_chi) <= B_chi*log(3+|t|)^9` at EVERY height. Bounded heights use a
closed rectangle strictly inside the proved zero-free region and the continuous
actual quotient. Constants can depend on the character; no conductor-uniform
bounded-height claim. Source installed as DirichletLLogDerivativeStrip, audit28928.

**C28.50 — actual signed character Perron transport (frozen construction).**
Corpus search77920 (nonpartial64610/64610, compiler mostlypending/stale) confirms
actual scalar PerronVonMangoldtSwap and zeta-specific contour assembly, plus
mathlib's literal character twist identity. Proposed imaginary power twists are
not periodic Dirichlet characters and cannot discharge this target.
Construct the exact tent identity for chi(n)*Lambda(n) from the existing weighted
kernel. Absolute integral summability follows by |chi(n)|<=1 domination by the
source scalar von Mangoldt majorant; pointwise summation uses the actual character
L-series/log-derivative identity. For nonprincipal chi the zero-free rectangle
has zero contour integral (no pole main term). Use C28.49 to CONSTRUCT the rectangle
and its bounds, rather than accepting zero-freeness as a new source premise.
Tails, horizontal edges, quantitative decay and complex unsmoothing remain exact
obligations; no AP prime rate or joint cubic cancellation is claimed at this stage.

**C28.49 FINAL — LEAN PROVED.**
Production28928 (`lake --old env lean` direct leaf with olean output) exits0 with
empty diagnostics. Axiom33128 exits0: the new segment helper, both preserved zero-free
capstones and all six new public declarations use only propext, Classical.choice,
Quot.sound. New leaf is wired; no umbrella or full build. The lower floor and reciprocal
are actual constructions, including principal-square degeneracy in the character
product. No quantitative AP theorem or full joint cubic cancellation is inferred.

**C28.50a — exact signed identity and constructed rectangles (scratch PROVED).**
Scratch30205 exits0 with empty diagnostics. `LSeries_character_vonMangoldt_eq`
identifies the actual twist with -L'_chi/L_chi on Re(s)>1.
`smoothed_character_vonMangoldt_eq_perron_integral` keeps every complex character
coefficient through the kernel integral and the absolutely justified sum/integral
interchange. `exists_nonprincipal_character_perron_rectangles` constructs c,B>0,
c<=log(3)^9/2, such that at every T>=0 the FULL rectangle
`1-delta <= Re(s) <= 1+delta, |Im(s)|<=T`, delta=c/log(3+T)^9,
has positive real part, actual nonvanishing and norm(L'/L)<=B*log(3+T)^9.
For every x>0 its actual Perron integrand has zero boundary integral. This includes
s=1 for nonprincipal chi and needs no pole subtraction. Source installed as
DirichletCharacterPerron; final production8623 and axiom audit pending.
The scalar source's existing integral-majorant and term/kernel proofs are exposed
as reusable theorems; source32340 passes cleanly with its scalar capstone preserved.

**C28.50b — all contour errors and signed unsmoothing (next formal target).**
The corpus PerronTailBound and PerronEdgeBounds supply the proof mechanisms; their
current theorems are zeta-specific. Construct the character right-line estimate
`norm(L'_chi/L_chi)<=8/(a-1)^2` by the literal twisted series and |chi(n)|<=1.
For b=1-delta, a=1+delta, M=B*log(3+T)^9, the exact identity plus zero boundary
integral should give the complete bound
`norm(S_chi(x)) <= 2*(8/(a-1)^2)*x^a/(2*pi*T)
 + (2*pi)^(-1)*(M*x^b*pi/b + 2*M*x^a/T^2*(a-b))`.
No tails or horizontal edges may be dropped. Integrability must also be proved.
One can shrink c to <=1/4. Choose u=(log x)^(1/10), T=exp(u)-3, so log(3+T)=u
exactly and eventually T>=exp(u)/2. Then the tails have polynomial u^18 times
x*exp(-(1-c)u), the vertical edge u^9*x*exp(-c*u), and the horizontal edges
x*exp(-(2-c)u) after cancellation of the width. Corpus polynomial absorption
then gives an actual fixed-character tent rate C*x*exp(-k*u), k>0.
This is a rate construction, not optimization of the exponents or constants.

For complex unsmoothing, prove the actual finite identity/defect
`norm(S_chi(y)-S_chi(x)-log(y/x)*Psi_chi(floor x))
 <= log(y/x)*(psi(floor y)-psi(floor x))` for y>=x>0.
It follows termwise from the tent kernel, preserving chi(n), and |chi(n)|<=1.
Use the corpus ordinary-psi rate to dominate the short interval, and set
log(y/x)=exp(-k'*u) with k' below half both source decay constants. The resulting
fixed-character partial-sum rate feeds exact reduced-class orthogonality and
prime-power removal. None of these rate/unsmoothing conclusions is yet claimed
Lean-proved. Fixed-modulus AP information alone also does not settle the full
joint cubic main; joint p,q,r cancellation remains a separate hard obligation.

**C28.50a FINAL — LEAN PROVED; C28.50b remains open.**
Production8623 passes cleanly with `lake --old env lean <leaf> -o <olean>`.
Axiom50502 passes: all three actual character declarations, both exposed scalar
ingredients and the preserved scalar Perron capstone depend only on propext,
Classical.choice, Quot.sound. New leaf wired into RHTower. Exact corpus index
finds the signed identity at35 and constructed rectangles at98. Formal lint68152
exits1 for ten unrelated unreachable leaves; it reports no BAG error. No full
or umbrella build, extra axioms, numerical computation or heartbeat changes.

Turn evaluation: C28.49 and C28.50a close actual analytic source obligations
needed for character prime sums. They do not settle C28.50b's quantitative rate
or C28.44's full joint signed cubic. The next construction is the complete
character contour error plus complex unsmoothing described above. Growing mixed
moments, moving cofactors, positive signed self-target error, MUST270 physical
recurrence and unconditional RH remain open. Goal ACTIVE.

**C28.50b contour stage — complete master estimate proved in Lean.**
Scratch4490 and production82313 pass cleanly. DirichletCharacterPerronBounds
constructs the literal character right-line bound, absolute integrability, both
infinite tails (without assuming chi is real), the physical-coordinate signed
Perron identity, and the complete contour master bound. The final existential
statement has no zero-free or norm-bound premise: it instantiates C28.50a's actual
constructed rectangle and includes every edge and both tails. Leaf is wired;
axiom audit pending after the dependent rate construction.

**C28.50b rate refinement — actual source width retained.**
The earlier paper choice suggested shrinking c<=1/4. The cleaner construction
uses the rectangle theorem's actual c directly: D=1+c, k=c/D^9 and d=min(1,k).
For u>=6, x=exp(u^10), T=exp(D*u)-3, log(3+T)=D*u and T>=exp(D*u)/2.
The tail coefficient is (32*D^18/c²)*u^18*x*exp(-(D-k)u), the vertical coefficient
at most(2*pi*B*D^9)*u^9*x*exp(-ku), and the horizontal coefficient at most
16*B*c*x*exp(-(2D-k)u). Since k<=c, both D-k and2D-k>=1. Hence all terms are
bounded by a fixed coefficient times u^18*x*exp(-d*u); source polynomial
absorption gives exp(-(d/2)u). Scratch rate construction now checks this exact
argument and then transfers from exp(u^10) to every sufficiently large real x.
No prime-sum rate is asserted until this and signed unsmoothing are audited.

**C28.50b tent-rate stage — production Lean check passed.**
Scratch77670 and production37529 exit0. DirichletCharacterPowerLog gives actual
κ>0,C>=0,x₀>=3 such that every x>=x₀ satisfies
`norm(sum chi(n)*Lambda(n)*max(log(x/n),0)) <= C*x*exp(-κ*(logx)^(1/10))`.
No zero-free, inverse-L, contour or convergence premise remains. One polynomial
tactic advisory is emitted; no errors, heartbeat limits unchanged. Leaf wired.

**C28.50b signed recovery — exact quantitative construction.**
The structural defect proof uses D_n>=0 for the real tent-kernel remainder after
subtracting the full n<=x step; multiplication by chi(n) has norm at most D_n.
Summing D_n and applying the existing scalar tent upper sandwich gives the exact
complex defect bound recorded above. For the final rate, take
lambda=min(κ/2,κ_psi), epsilon=exp(-lambda*(logx)^(1/10)), y=(1+epsilon)*x.
The installed log lower bound 2*epsilon/(epsilon+2)<=log(1+epsilon) implies
log(y/x)>=epsilon/2 for epsilon<=1. The two tent values divided by log(y/x)
are at most6*C*x*epsilon; the scalar psi short interval is at most
(1+3*C_psi)*x*epsilon. Thus the actual unsmoothed character sum should have
constant6*C+1+3*C_psi at rate lambda. Structural scratch and this source-specific
quantitative transfer are under verification; no AP prime theorem is claimed yet.

**C28.51 — source character prime sums and reduced progressions (frozen extension).**
Search29143 returned the exact installed finite-character orthogonality and residueClass_apply,
not an actual quantitative AP prime theorem. Coverage64636/64636, nonpartial; compiler metadata
mostly pending/stale, semantic coverage unmeasured and refresh background. Proper-prime-power
candidate transformations alone do not supply the character cancellation rate. From C28.50b,
define theta_chi(x) with the actual chi(p)*log p on all primes p<=x. The exact difference from
Psi_chi is supported on proper prime powers; norm is at most ordinary psi(x)-theta(x).
The corpus psi-theta bound and sqrt_log_le_power_log_decay absorb this into the same character
rate, giving norm(theta_chi)<= (C+1)*x*exp(-rho*(logx)^.1). For the principal character, only
prime divisors of Q are removed, so the error against ordinary theta is at most theta(Q).
Finite-character orthogonality then yields reduced-class AP theta, with constants dependent
on Q and uniform over the finite reduced classes. This constructs missing arithmetic input;
it does not establish any conductor-uniform rate or full p,q,r cubic cancellation.

**C28.50b signed recovery — production LEAN PROVED.**
Scratch15310 and production64709 exit0 with empty diagnostics. The exact positive
kernel-defect domination and actual nonprincipal characterChebyshevPsi power-log
rate are installed in DirichletCharacterUnsmoothing and wired. All contour edges,
both tails and the signed-to-unsmoothed transfer have now passed direct leaf audits.
The combined axiom audit remains pending until the dependent character-prime leaf.
C28.51 character-prime and fixed-modulus AP source proofs are written in scratch;
no AP claim is promoted before checking them.

**C28.51 character-prime main terms — scratch LEAN PROVED.**
Scratch92823 exits0, empty diagnostics. The norm of Psi_chi-theta_chi is at most the
actual ordinary psi-theta proper-power mass. Thus the proved character cancellation
rate survives on the full prime set. The principal difference is bounded by theta(Q),
because only primes dividing Q are removed. Combining this with the actual scalar
power-log theta theorem constructs the main term `if chi=1 then x else0` for EVERY
character. DirichletCharacterTheta installed/wired; production35121 under audit.
Fixed-modulus finite uniformity and reduced-class orthogonality are next to check.

**C28.52 — growing-frequency rational prime profiles (next hard producer, not yet Lean).**
Source search28266 is nonpartial64645/64645 with mostly pending/stale compiler metadata.
Its residue-martingale summability proposal does not control the literal pq/r phase.
Direct reads of the actual half-resonance edge_abel_error and primeResidueLogCoefficient
identify the needed upgrade: for each fixed Q>0 and xi>0, construct c,C,N0 such that
for all N>=N0, every reduced class a and every real tau, the full residue-restricted
prime sum with weight W(xi*p/N)*V(p/N)*exp(i*tau*p/N), normalized by logN/N, differs
from (1/phi(Q)) times the integral on[1,2] of
`W(xi*x)*V(x)*exp(i*tau*x)/(1+log(x)/logN)` by at most
`C*(1+abs(tau))*exp(-c*(logN)^(1/10))`.
The source endpoint-inclusive Abel identity retains both f(1) and f(2); the actual
smooth W,V profile supplies its derivative uniformly for 1/logN in[0,1]. C28.51
will discharge the cumulative AP error rather than assume it. Summing the exact
residue phases recovers the signed rational main, including nonzero arithmetic
bias; one integration by parts pays all boundary terms and only claims 1/abs(tau).
This would cover growing determinant neighborhoods b*p-a*r around each fixed rational
ray. Full joint complementary cancellation, growing moduli, mixed moments, moving
cofactors and positive self-target recurrence remain distinct unsolved obligations.

C28.52 paper mechanism, with the actual AP input now production-checked: let
G_l(x)=W(xi*x)*V(x)/(1+l*logx), l in[0,1], x in[1,2]. The denominator is>=1;
source smoothness on this compact set gives one B bounding both G_l and its x-derivative.
For f(x)=G_l(x)*exp(i*tau*x), norm(f)<=B and norm(f')<=B*(1+abs(tau)).
C28.51 gives the cumulative class error<=C*x*exp(-c*(logN)^.1) for EVERY x in[N,2N],
since log and positive rpow are monotone. The existing exact edge Abel identity then
bounds the normalized full-band discrepancy by5*B*C*(1+abs(tau))*exp(-c*(logN)^.1),
retaining both endpoints. At l=1/logN the exact identity
G_l(p/N)*logp=logN*W(xi*p/N)*V(p/N) removes the prime logarithmic weight.
No limit is multiplied by a growing parameter. Formal construction must establish
these actual parameter-family regularity and cumulative-support equalities; it may
expose the existing private edge Abel theorem for reuse but must not assume its AP
premise in the new capstone. This is the next producer after the completed audits.

**C28.50b and C28.51 FINAL — quantitative AP source input LEAN PROVED.**
All five final leaf audits use `lake --old env lean <leaf> -o <olean>`:
DirichletCharacterPerronBounds82313, DirichletCharacterPowerLog37529,
DirichletCharacterUnsmoothing64709, DirichletCharacterTheta35121,
PrimeProgressionPowerLog52221 all exit0. Only the tent-rate leaf emits one ring
advisory; remaining diagnostics empty. Combined axiom audit73788 exits0: all22
public theorem/definition queries depend only on propext, Classical.choice,
Quot.sound. No added analytic premises, sorry, computation or heartbeat changes.
All leaves wired; no umbrella or full build. Exact corpus index finds the actual
AP capstone at PrimeProgressionPowerLog:87. Lint48654 exits1 solely on eleven
unrelated unreachable leaves (full log /tmp/bag-character-ap-lint-01a0.log);
no new BAG leaf lint error. Frontier map updated.

Turn evaluation: this closes the precise missing quantitative character/AP arithmetic
input recorded in C28.48, through actual contour, signed unsmoothing and prime removal.
It does not prove contraction-scale cancellation for the full signed cubic. C28.52
now attacks its rational neighborhoods with the actual frequency-dependent Gaussian
profile and retained endpoints. Growing moduli, the full complementary p,q,r average,
growing mixed moments, moving cofactors, positive signed self-target recurrence,
MUST-270 and RH remain open. Goal remains ACTIVE.

**C28.52 strengthened target — actual moving physical window.**
Revalidated C28.51 production source and the existing endpoint-inclusive Abel/Fourier
identities. Rather than constants depending on a fixed xi, construct ONE profile bound
for all xi in[1/2,2], exactly the physical p/r range. The actual derivative of
W(xi*x)*V(x) is xi*W'(xi*x)*V(x)+W(xi*x)*V'(x). Compact bounds for W' on[0,4]
and V' on[1,2], together with normW,normV<=1, make this uniform. This retains the
moving window itself and removes the need for freezing it to a rational ray.
The exact logarithmic unweighting and quantitative AP error then give a common
all-frequency signed main-term estimate; both nonzero band endpoints remain.
Search20853 nonpartial64656/64656 returned unrelated Gaussian/resolvent profiles;
those are not substitutes for this actual W,V family. A targeted corpus search
uses the exact already-read Abel, cutoff smoothness and AP capstone names.

C28.52 actual-row consequence to pursue after verification: take xi=p/r and
 tau=2*pi*N*(p/r-A/Q). Exact phase splitting gives e(2*pi*p*q/r) as the
Q-periodic rational phase times e(tau*q/N). For N>Q every prime q in the full band
is a unit modulo Q; finite residue partition applies without discarded primes.
The ratio-uniform profile theorem therefore controls the complete moving-window
main row directly. The physical coefficient has norm<=8/N; the source stationary
error over all q costs C/(N*logN), and removing q=r costs8/N. Unlike freezing the
window, this construction needs no extra abs(Q*p-A*r)/N window-error term.
A proof still needs the exact phase/partition transport; no row capstone is claimed
from the currently checking profile alone. This addresses rational neighborhoods,
not the full signed complementary three-prime average.

**C28.53 — full actual rational-neighborhood q-row (frozen next construction).**
For each fixed positive Q, seek c,C,N0 constructed from C28.52, uniform in every
numerator A, physical primes p,r, and N>=N0. Set tau=2*pi*N*(p/r-A/Q).
For tau!=0 the full contraction-removed physical q-row should satisfy
`norm(row)<=C/logN*(1/abs(tau)+(1+abs(tau))*exp(-c*(logN)^.1))
             +C/(N*logN)+8/N`.
All q in the original prime band are retained. Exact finite unit-residue partition
and the source primeRationalPhase_mod identity recover the signed rational main
before taking its norm. The profile ratio xi=p/r stays in[1/2,2]. The entire physical
stationary remainder costs C/(N*logN); q=r removal costs8/N. There is no freezing
of the window and no added determinant-sized amplitude error. This constructs a
q-row producer for fixed-denominator rational neighborhoods, not cancellation of
the remaining full signed p,r sum. Corpus90851 partial64666/64666 has usable band
and finite-residue hits; generic infinite residue sums do not themselves give this
finite prime partition. Actual prior prime_periodic_profile proof supplies the
finite fibre-sum mechanism, with complete support checked directly.

**C28.52 — actual uniform moving-profile theorem scratch LEAN PROVED.**
Scratch53497 exits0 with empty diagnostics. The source-instantiated capstone constructs
one quantitative signed AP-profile main term for ALL xi in[1/2,2] and ALL real tau.
The Fourier corollary retains both boundaries and proves the full residue prime sum
bounded by C*N/logN times[1/abs(tau)+(1+abs(tau))*exp(-c*(logN)^.1)]. No AP error,
amplitude regularity or Fourier estimate is left as a premise. Constants depend Q,
not the class, xi or tau. Installed/wired ChiPrimeGaussianProgressionProfile; production
under audit. Earlier derivative error was a real/complex instance-transparency issue,
resolved with the source's using! pattern; norm aggregation required an explicitly
typed integral bound, and reciprocal algebra was normalized before linarith.
Limits unchanged. The exact rational-phase assembly is now in independent scratch.
