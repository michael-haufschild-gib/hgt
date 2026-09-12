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
so it cannot give a uniform floor. Remaining arithmetic task is to count linearly many
prime--cofactor samples in each disjoint evaluation neighborhood and sum their `N^J` colored
selections through Cauchy--Binet.

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
