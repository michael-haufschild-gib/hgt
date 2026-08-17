# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Scope and verdict

This document is a state map of the `HTGeometry`, `HilbertMetric`, and `RHTower` research corpus.
It records current proof architectures, theorem chains, first open source statements, terminal
mechanisms, and structural conclusions shared across routes. It is not a chronology or build log.

**Corpus cutoff:** 17 August 2026, commit `65cde572f80a9b6eacc13326da4ca08d533fef52`, plus declaration-level working-tree review. Unconditional theorems remain distinct from supplied interfaces.

RH and its negation remain unproved. Current live architecture count is:

- ten lettered routes: **C1, D2, E, G, L, O, P, Q, T, U**;
- one unlettered live architecture: **CCM-FU**;
- six incomplete CCM candidate openings: **CCM-HG** (Hankel boundary relative-trace slope),
  **CCM-GS** (cofinal ground-separating incidence), **CCM-UR** (unit-Riesz completed-current
  smoothing), **CCM-RF** (rectangular adjacent-block floor), and **CCM-EP** (dephased
  Euler--Pick boundary transfer), plus **CCM-BS** (finite-peripheral Birman--Schwinger reduction);
- seven non-CCM candidate openings: **SP-E** (prime--Gamma signed-permutation Pluecker determinant),
  **TC-HS** (theta--Cayley half-step reflection transport), and **UQ-QC** (Route U/Q source-pure
  quadratic concentration), **HA-SW** (height-adaptive cancelled-source socle--Weyl descent), and
  **HJ-GR** (hard-Jacobi reserve versus boundary controllability Gramian), plus **PH-TC**
  (parabolic heat--Turan curvature) and **MC-CS** (sub-square-root mass-chirp separation), both
  source-isogenous to Route T;
- one reopened, still unlettered disproof opening: moving-degree reverse-Bessel completed-source
  pulse capital;
- no instantiated Route V;
- Route R terminalized as an independent producer.

An **endpoint** is a Lean-proved implication or equivalence ending in RH. It is a receiver, not
evidence for its premise. An **open core** is first unproved source theorem after proved connectors
and RH-equivalent reformulations are removed. An **independent route** requires a literal source,
an unconditional chain to an RH endpoint, and an open producer not already identified with another
route under corpus source-isogenies.

## Executive route map

| Route | Architecture | First open core |
|---|---|---|
| CCM-FU | literal completed Guinand–Weil source → centered cubic Loewner incidence → Xi-screw Green reporter → second-Abel/Cesàro continuation → RH | Prove linear growth of one Cesàro primitive of the literal third-grade prime-minus-polar cumulative source. This strictly includes oscillatory cases excluded by every fixed pointwise subcubic envelope. |
| C1 | theta source inverse → entire Fredholm determinant/Weil form → real spectrum or positive closure → RH | Prove a source-derived real-spectrum/positive-closure theorem for fixed theta inverse, or a genuinely pre-divisor centered covariance controlling deviation energy. Raw critical-feature lattice budgets are impossible; corrected budgets are RH-equivalent off-line energy. |
| D2 | safe-line Euler deficit → analytically continued prime–Gamma trace → finite high-frequency ceiling → RH | Continue literal positive deficit through Euler wall and prove any finite uniform ceiling above frequency four. |
| E | squarefree central Wold shell → explicit parity-coalesced/whole-anchor opposite-sign relation → physical Carleson and co-moving flux → Mertens cancellation → RH | Upgrade fixed-relation near-Hall and polylog/subpower incoming bounds to unit interval Carleson load and normalized moving-seam flux. Exact log-window transfer is closed. The required upstream short-window rate is Menon's `(log log L)^2/(log L)^2`, not Matomäki--Radziwiłł's weaker logarithmic power; all-interval `E_3` is separately needed. Neither import proves unit capacity. |
| G | Suzuki/CCM source → restricted-Weil Morse floor or one-sided Euler--Gamma/Carleman wall → aperture-dressed FE light completion → Hermite–Biehler orientation → RH | Floor: aperture-Morse exhaustion/boundary-rough exclusion. Coalescing high-assisted branch is now exactly source-cyclic: prove literal low-source cyclic singular mass above `1/113` is `o(r/log^2(1/r))`, or construct the opposite lower-bound family already forced by Lean. Low-only schedules retain their aperture ceiling. Wall: compare prime-minus-regular-screw Ward mass with dressed negative light and holonomy. |
| L | arithmetic Poisson/Green complex → source Green closure and harmonic complement → faithful cup-isometric Meyer comparison → positive Hodge block → critical line → RH | Construct the source-derived arithmetic Calderón intermediate extension and its closed Lagrangian boundary relation at the critical `x^(1/2)` scale. Scalar descent on the completed one-leg graph is exactly constant-profile descent. Operator-valued fixed-coordinate divisor encoding is also impossible when reciprocal-mass continuity lands in Hilbert--Schmidt topology. A survivor must retain a proved arithmetic-discontinuous critical-scale invariant, change the carrier before completion, or leave the Hilbert--Schmidt class. |
| O | restricted-Weil operator → canonical exact-ground Gamma--Slepian heads → arithmetic sign on those heads → nonnegative floor → RH | Ground selection is closed: canonical literal finite heads converge in form norm to exact restricted-Weil ground, while constrained prolate grounds converge to explicit two-mode seeds. Prove that finite von-Mangoldt compression cannot overcompensate identity, scalar Gamma, and polar terms along canonical cofinal heads. |
| P | primitive Euler/Burnol budget → Julia--Krein completion → spectrum-moving prime--Gamma transport or non-spectral contraction → RH | Direct `det₂`/scalar welding and compression-monotone Ward budgets are closed negatively. Two-sided completed Gamma/polar residue gauges now transport the exact precompression Julia short to every Xi multiplicity copy, but the landed nonzero coordinate still has zero short. Prove an independent completed-source budget/order law for its positive split corner, or the non-spectral conormal contraction. |
| Q | theta–Cassini source → separated finite prime–Gamma packet sign → transverse charge zero → RH | Produce nonnegative energy cofinally toward orientation vector. Null boundaries have hidden mixed incidence `-E/2`; diagonal budgets and adaptive complex phases cannot repair fusion. Alternative UQ-QC asks for finite pre-divisor quadratic-concentration budget. |
| T | centered prime--Gamma source → detector/Mellin packet, Wold residual ODE, caustic-null true-prime Bessel cone, or sub-square-root massive chirp → RH | All-order jet/Fourier identification and reduction of the prime-line receiver to a finite moving atom core modulo uniformly bounded retreated exterior are closed. Identify that core with true-prime-cone quadrature and prove signed interior/type-zero control; residual/sub-`3/2` and growing-Xi chirp branches remain. |
| U | shifted-Xi Hankel first crossing → boundary-rough completed null ground → restricted-Weil positivity → RH | Lean proves `RH ∨ CCMFirstContactBoundaryRoughness`: off RH the least zero aperture has a genuine null ground absent from every strict smooth interior source. Exclude this completed-boundary state by a trace/quotient or whole-ground theorem. |

## Live architectures

### CCM-FU — four-unit source-codiagonal incidence

**Endpoint.** A moving Gamma/Sonin/Hodge incidence carrying continued Xi Ward column with
nonincreasing four-unit energy gives required Ward orientation and RH.

**Architecture.** Literal finite Sonin source `sigma_S` lands in actual module-one invariant class
space. Its finite periodization is a Boolean Euler cube with coefficient `mu(n)/n`; Fourier
transport preserves coefficients. The published finite restricted-Weil packet and its simple-
ground Fourier receiver remain exact. New continuous source dictionary identifies the whole
completed Guinand–Weil matrix entrywise, and its first noncentral centered response occurs at cubic
order. That cubic Loewner incidence is exactly the Xi-screw Green curvature. Three Abel derivatives
recover critical Mellin completed error. A further source primitive and second Abel transform now
show that linear Cesàro growth alone closes RH, even for large oscillatory cumulative sources that
obey no fixed pointwise subcubic envelope.

**Established structure.** Corpus proves:

- source-faithful whole-`L2` finite-stage Sonin comparison and density of literal cores;
- published finite CCM packet, parity blocks, simple-ground visibility, and parity-free real-zero
  theorem;
- exact finite Shannon band-limited Fourier factorization and real-zero theorem for the published
  simple odd ground; the cofinal passage remains conditional on coefficient convergence;
- complex mixed CCM form and exact CCM–Suzuki screw/Weil identification;
- compact-Fourier zero transfer under fixed-support mean-square convergence;
- finite Guinand–Weil source quotient for every continuous source functional, including measures;
- pre-quotient pole density and finite von-Mangoldt atoms giving exact polar–prime sine source;
- endpoint-cancelled singular Gamma density giving exact archimedean sine source;
- universal Gamma first-jet law and mode-independent weighted-cosine endpoint counterterm;
- complete mixed-order odd and diagonal dictionaries at every integer mode;
- whole completed centered source packet equal to published restricted-Weil matrix entrywise;
- four-unit prime-entry event law: odd tangent equals mode times mode-independent diagonal tangent;
- prime-entry whole-matrix tangent is a negative-semidefinite rank-one constant-boundary contraction;
- every finite visible prime-event aggregate remains the same negative rank-one boundary contraction;
- every nontrivial atomic packet has exact rank one, strictly negative trace, and kernel equal to
  the zero-sum coefficient hyperplane, so canonical centering annihilates its complete first jet;
- arbitrary atom-dependent scalar dressing retains that same blind hyperplane and rank-one direction;
- prime-entry second jet is still central and is annihilated by centering, while third jet is a
  cubic Loewner matrix whose centered quadratic form is the positive clock-moment square
  `2*pi^2*q_k*(sum_i clock_i*v_i)^2` at every genuine prime power;
- every finite nonnegatively dressed third-jet event packet is one nonnegative scalar arithmetic
  rate times that universal cubic Loewner matrix; literal visible cutoff is centered PSD at every
  aperture;
- Route P's literal P-G189 primitive tail-flux coefficient is a strictly positive arithmetic
  dressing of this same CCM third-jet scale, label by prime and depth; the resulting finite
  P-tail/CCM matrix is centered PSD and its first aperture derivative is exactly the transverse
  CCM connection;
- a two-sheet Gamma-six singular graph removes scalar-trace blindness: antisymmetric finite
  packets have zero mass trace, unit orientation trace, vanish in ambient `ell^2`, and converge to
  a nonzero vertical orientation class; each P-G189-labelled cell reads out exactly corresponding
  CCM third-jet matrix and transports to its coefficient times fixed Sonin horizontal detector;
- local field-one/Suzuki four-half-step factorization and four-unit detector;
- cubic-Green identification of each critical prime atom with Route P primitive base mass;
- phase-complete local weld `q_k exp(i t log k)=(4/a_k^3)W_k(t)^2` between CCM cubic incidence and
  the symmetric square of Suzuki's prime-entry wall field;
- forced global inverse-cubic grade `32/h^3`, exact finite Stieltjes cancellation of prime and polar
  channels into completed-error endpoint/flux, and absolute integrability of the Gamma tail;
- exact identification of the completed third-grade reporter with affine-normalized Xi-screw Green
  curvature and hence with the literal Xi divisor codiagonal;
- cubic Abel cancellation: three spectral derivatives remove inverse-cubic grade and recover the
  critical Mellin defect, with base-wall dependence confined to an entire finite/compact head;
- RH completeness of any uniformly bounded literal cumulative third-grade source and of any finite
  cofinal completed third-grade limit;
- grade--growth threshold: every bound `|E(h)|<=C h^alpha` with real `alpha<3` gives the exact
  completed limit and forces RH; under non-RH, `E` escapes every such subcubic envelope beyond every
  positive wall;
- second-Abel/Cesàro completeness: if, for one `b>0`, the primitive
  `Q_b(H)=integral_b^H E_b(h) dh` satisfies `|Q_b(H)|<=C(H+1)`, its second Abel transform is analytic
  on `Re u>0`, agrees with the original prime-minus-polar transform on `Re u>1`, and after three
  derivatives yields the regularized critical Mellin defect on `Re s>0`; this forces RH;
- contrapositive rigidity: under non-RH, for every positive wall `b` and every `C>=0`, some `H>b`
  satisfies `|Q_b(H)|>C(H+1)`. Thus non-RH forces superlinear Cesàro excursions, not merely failure
  of pointwise subcubic control.

Finite matrix quotient has only `2N+1` source coordinates; even strictly positive source weights
are not recoverable beyond observer dimension. Canonical selection must therefore occur before
finite quotienting.

**Open core.** Local producer, continuous completion, Suzuki/Xi identification, and both first- and
second-Abel analytic completeness are closed. The broadest current source-side gate is:

```text
for some b>0 and C>=0, every H>b satisfies
|integral_b^H E_b(h) dh| <= C(H+1),
```

where `E_b` is the literal third-grade prime-minus-polar cumulative source. This condition permits
large oscillatory `E_b` excluded by the earlier pointwise criteria. The following stronger
sufficient conditions also remain available:

```text
bounded literal cumulative prime-minus-polar third-grade source;
finite cofinal limit of completed-error cubic flux;
finite cofinal limit of completed Xi-screw third-grade Green reporter;
one subcubic envelope |criticalMellinCompletedError(h)|<=C h^alpha, alpha<3.
```

Each condition is proved to imply RH; none is routine infrastructure. Existing unconditional
completed-error bounds are exponential at critical square-root scale and do not discharge even the
Cesàro gate. Next work must prove source-level average cancellation between literal prime staircase
and polar channel. Recomputing finite jets, changing scalar damping, choosing another positive base
wall, or restating screw positivity cannot advance CCM-FU: Abel theory confines wall choice to an
entire head, and scalar renormalization cannot remove the singular obstruction.

The unit-Riesz reporter now gives an exact source-side coherent decomposition of this same
completed current at integer apertures: positive von-Mangoldt increment-Gram energy minus explicit
polar energy `(2/3)sqrt N`, with strict two-lag separation. This supplies canonical source
covariance but no average cancellation. An FU merger must transport the signed coherent trace into
the Cesàro primitive without replacing prime-minus-polar cancellation by separate positive bounds.
Bare polar-frame domination is now formally excluded at a fixed lag: a four-column coherent packet
has nonzero fixed sample but polar response energy smaller by an arbitrary localization factor.
The exact positive survivor is its first-order lag graph energy, equal to four times source-Gram
energy. Hence FU must carry generator/source-Gram control through the Cesàro primitive or prove
literal signed cancellation; polar `L2` averaging alone cannot close the route.
That survivor is no longer abstract: the complex graph leak `2g'+i g` is an admissible HG profile
whose initial boundary-relative-trace density equals exactly four times coherent source-Gram
energy, and its boundary slope recovers the fixed coherent sample. Thus FU has a concrete
source-faithful boundary receiver. Missing step is cofinal transport of literal signed
prime-minus-polar current into this graph leak with a four-unit bound, not construction of another
scalar reporter.
Direct transport is now exactly excluded. Literal completed coherent response has constant
right-tail charge `R_1(log N)/2`; it decays, and its amplitude is square-integrable, only when that
resolvent value vanishes. FU codiagonalization must therefore cancel this charge while retaining it
as signed endpoint flux. Subtracting it without recording boundary charge would erase precisely the
arithmetic quantity FU must control.
Canonical repair is now unconditional in Lean. For every `h>0`, shift codiagonal
`Delta_h C_N(u)=C_N(u+h)-C_N(u)` has an exact decaying two-exponential tail and a continuous HG
leak-profile lift. Finite telescoping plus `C_N(0)=0` gives source-faithful identity

```text
R_1(log N)/2 = lim_(m->infinity) sum_(j<m) Delta_h C_N(jh).
```

Thus forbidden constant mode is neither retained as nonintegrable bulk nor discarded: it becomes
reconstructible boundary flux of admissible bulk increments. Stronger finite-mode elimination is
now proved: taking `h=log N`, exact rank-two tail recurrence gives

```text
R_1(log N)/2 = D_N(0)
  + ((1-r-r^2)D_N(log N)+D_N(2 log N))/((1-r)^2(1+r)),
r=exp(-log N/2)<=3/4.
```

Hence readout is uniformly conditioned and bounded by coefficients `1,48,16`; no infinite dual is
needed. FU's open core narrows to source-specific subpower control of these three literal samples,
or transport of that finite law to its Cesàro primitive.

There is now an even more compressed source-faithful boundary sector. Literal prime outgoing
charge minus literal continuum polar outgoing charge is exactly `R_1(log N)/2`; multiplying this
coefficient by `exp(-u/2)` gives an HG leak profile whose boundary trace is
`(R_1(log N)^2/4)(1-exp(-u))`. Domination by the canonical pole packet at one aperture, every
aperture, or at initial slope is exactly `R_1(log N)^2<=16`. This is a rigidity warning for FU:
scalar HG comparison merely restates an arithmetic bound and cannot supply Cesàro cancellation.
A genuine FU/HG merger must derive outgoing-coefficient contractivity from literal bulk or ground
incidence. Downstream transport is now closed in Lean: any uniform natural-log bound on this
coefficient extends to a global critical-resolvent bound, and the resulting holomorphic defect
continuation forces RH. In particular, pole domination of every literal integer outgoing block
implies RH. FU/HG's sole remaining core is the non-circular source/ground producer.

Converse with sharp constant is now closed in Lean. Under RH, reciprocal-square trace identity
gives total Xi screw weight `normalizedPrimeArchMoment 0 < 29/625`, hence Suzuki relation hull
`<58/625`. At forced base `1/2`, first Lerch atom and corrected Gamma constant give
`|Psi'_+(1/2)|<1`; reporter caps are `|F_H|<=1/4`, `|F'_H|<=1/2`. Suzuki Green term is therefore
`<241/500`, while exact polar and archimedean corrections are each `<7/10` for `H>=log 2`. Hence
`|R_1(log N)/2|<2` under RH. Together with reverse implication:

```text
RH iff every literal completed integer outgoing profile is pole dominated.
```

Sharp four-unit HG inequality is exactly RH-strength, not downstream FU estimate. Only independent
bulk/ground/source law proving it without RH can advance route; optimizing scalar constants or
re-proving boundedness cannot.

**Route relations.** CCM–E is only an opening until a cofinal Hall/load/flux-to-floor theorem is
proved. CCM–P–L has exact local two-sheet singular carrier and dual CCM/Sonin readouts, but shares
Route L/P boundary wall: no source theorem annihilates or globally budgets cofinal oriented class.
It is a cross-route mechanism, not independent route.

**Principal Lean evidence.** `CCMGuinandWeilContinuousSourceQuotient.lean`,
`CCMGuinandWeilLiteralPolarPrimeSource.lean`, `CCMGuinandWeilArchimedeanOddSource.lean`,
`CCMGuinandWeilArchimedeanFirstJet.lean`,
`CCMGuinandWeilCompletedCenteredSourceMatrix.lean`,
`CCMGuinandWeilPrimeEntryIncidence.lean`,
`CCMGuinandWeilPrimeEntryRankOneTangent.lean`,
`CCMGuinandWeilPrimeEntryAtomicConnection.lean`,
`CCMGuinandWeilPrimeEntryFirstClockBridge.lean`,
`CCMGuinandWeilPrimeEntryCentralChannel.lean`,
`CCMGuinandWeilPrimeEntryScalarDressingRigidity.lean`,
`CCMGuinandWeilPrimeEntryThirdJetTransverse.lean`,
`CCMGuinandWeilPrimeEntryThirdJetConnection.lean`,
`FrankensteinRoutePTailFluxCCMThirdJetBridge.lean`,
`CCMGuinandWeilPrimeEntryWallFieldWeld.lean`,
`CCMGuinandWeilThirdGradeCompletedConnection.lean`,
`CCMGuinandWeilXiScrewGreenConnection.lean`,
`CCMGuinandWeilThirdGradeAbelCompleteness.lean`,
`CCMGuinandWeilThirdGradeSubcubicCompleteness.lean`,
`CCMGuinandWeilThirdGradeCesaroCompleteness.lean`,
`CCMShannonFourierFactorization.lean`, `CCMPublishedOddGroundRealZeros.lean`,
`FieldOneFiniteStageThetaSourceNormalization.lean`, and CCM–Suzuki comparison modules.

### Route C1 — complete Xi–Weil / Hedenmalm positivity

**Endpoint.** Positivity of complete Xi–Weil form on faithful singular domain implies RH.

**Architecture.** Fixed theta-cusp source defines compact nonnormal inverse `B`, entire determinant,
weighted derivative, shifted cokernel, and singular Weil form. Corpus proves

```text
thetaSourceEntireDet2(z) = XiC(z)/XiC(0),
thetaSourceEntireDet2(z)=0  iff  XiC(z)=0.
```

Analytic order equals reciprocal-eigenvalue algebraic multiplicity. Thus source construction,
divisor realization, and multiplicity accounting are closed. Required producer is not another
spectral model: it is a source law making nonzero spectrum of this specific `B` real, or making
complete Xi–Weil form positive.

**Established structure.** Closed operator, shifted-cokernel, supersymmetric Dirac, essential
inverse-flow trace, and prime–Gamma coefficient interfaces are formal. Gauss–Hodge/Weil fusion
identifies off-line obstruction as deviation-weighted divided-difference mass and as negative odd
sector of an unconditional Krein decomposition. Known arithmetic input gives a strict wall-repulsion
ceiling below `1/4`, but RH is vanishing of entire deviation mass. Probe-circle laws show holomorphic
ray samples cannot determine required Hermitian circle relation. Three-component Gauss source now
closes full cubic propagated relative-error convergence: exact physical cubic moment converges to
moving-amplitude cubic moment. This removes cubic transport defect but supplies no sign for complete
deviation sector.
The closure is quantitative: exact Gamma ratios have two-sided central-band defect
`O((|j|+j^2)/I)`, infinite translation defect satisfies `I^(1/3) E_I^2 -> 0`, and triple-defect
AM--GM/energy bounds isolate depth two as summability endpoint. Thus another qualitative Gauss
translation estimate or higher positive power cannot advance C1; missing datum is signed relative
orientation.

Positive-power regularization is now excluded at every depth. For literal folded Gauss block,
positive-operator moment log-convexity propagates coefficient-faithful first Fourier diagonal to
every power, and two-orientation critical diagonal partial sums diverge for every component depth
`m>=1`. Raising positive Gauss operator to higher power cannot create finite critical trace or
annihilate deviation sector; required C1 mechanism must be relative/signed before diagonal sum.

The critical-feature lattice sublane is now sharply classified. Every Xi multiplicity copy puts at
least `32/25` into its nearest raw prime--Gamma channel, so the proposed 75% raw budget misses by a
factor `324` and forces an empty packet. Subtracting exact critical-line feature energy gives the
sharp 75% receiver at scale `(4/25)N`, but Lean proves this corrected excess lies between one half
and one times exact off-line energy and vanishes iff RH; every nonempty corrected lattice budget
vanishes iff RH. The subtraction is still zero-indexed. Thus it is not a pre-divisor producer.

**Open core.** Either:

1. prove source-derived real spectrum/positive closure for fixed theta inverse; or
2. construct a pre-divisor centered covariance or critical-line projector and prove its pole--
   Gamma--von-Mangoldt ceiling, strong enough to dominate deviation energy without using zeros.

Complete monotonicity of source-resolvent field is already unconditional outside exact wedge
`n>=19`, `0<X<(n+1)^2`; missing theorem is source-derived positivity inside that wedge. More finite
ray jets, probe samples, post-divisor moments, or indefinite GNS repackaging do not advance C1.

**Principal Lean evidence.** `HedenmalmThetaSourceDeterminantMultiplicity.lean`, shifted-cokernel and supersymmetric
theta modules, `GaussHodgeWeilPolarizationFusion.lean`,
`GaussHodgeWeilDeviationMoment.lean`, `GaussHodgeWeilArithmeticDeviationGap.lean`, and
`XiProbeCircleCriterion.lean`, together with `GaussCubicOuterConvergence.lean`,
`GaussComponentQuantitativeRatio.lean`, `GaussSampleQuantitativeRatio.lean`,
`GaussSampleTranslationCubicRate.lean`, `GaussTripleDefectCap.lean`, and
`GaussCubicTripleEnergyBound.lean`,
`HTGeometry/PositiveOperatorPowerMoment.lean`, and
`GaussPositiveAllDepthCriticalMass.lean`, together with
`HedenmalmCriticalFeatureLatticePrimeGammaBudget.lean`.

### Route D2 — continued prime–archimedean ceiling

**Endpoint.** A finite upper bound for continued positive-frequency relative trace above frequency
four is equivalent to RH. If RH fails, continued source is cofinally unbounded.

**Architecture.** On safe line `sigma=1+1/log x`, corpus proves uniformly in `tau`

```text
log log x - log|zeta(sigma+i tau)|
  = sum_(p<=x) (1-cos(tau log p))/p + O(1).
```

Euler logarithm, prime-square correction, head shift, cutoff tail, and Mertens normalization are
closed. For every fixed `B>0`, Lean now proves uniformly on the full polynomial horizon
`1<=|tau|<=x^B`

```text
|zeta(1+1/log(x)+i tau)| <= C_B log(x)/log(log(x)),
zetaLineDeficit(tau,x) >= log(log(log(x))) - O_B(1).
```

One quarter of this deficit lower-bounds pretentious distance from every real prime sequence
`|r(p)|<=1` to every archimedean twist. Thus safe-line positivity is quantitatively divergent,
not merely nonnegative or bounded away from zero.

**Open core.** Continue this positive source through critical strip with literal prime–Gamma
completion and prove any finite uniform high-frequency ceiling. Larger safe-side bands, more
Euler-convergent sieve tails, and real-twist geometry do not cross continuation wall.

**Principal Lean evidence.** `ZetaEulerLogPrimeSum.lean`, `ZetaOneLineDeficit.lean`,
`RealTwistDeficitTransfer.lean`, `ZetaLittlewoodDeficit.lean`, and continued prime–archimedean trace
modules.

### Route E — squarefree Möbius parity transport

**Endpoint.** Source-predeclared physical transport with square-root Gibbs cost, unit incoming
capacity, interval Hall control, and normalized friable/one-large-prime flux yields critical
Mertens cancellation and RH.

**Architecture.** Prime-power depth is a negligible tail; hard cancellation lives on squarefree
depth-zero central Wold breadth. Corpus now contains two explicit source-first relations. The
grade-recurrent relation splits ordered prime factors into central blocks, distributes fresh
annular reservoir primes, inserts structured three-prime tokens, and uses parity-coalescence when
active arity is even. Its physical corners reverse Möbius sign while total Wold drift is zero or
one. The simpler whole-anchor relation replaces the entire anchor by one reservoir and one
structured three-prime token in either breadth direction. Neither relation inspects a Mertens
imbalance or divisor observation.

**Established structure.** Two-large-prime and positive-depth tails, every fixed off-normal breadth
tail, coprime opposite-sign supply, prime-anchor capacity, and finite Wold-moment blindness are
closed. Patch seams are exact coboundaries; finite differential-algebraic Euler germs cannot see
the free infinite prime-clock orbit. For the explicit grade-recurrent relation Lean proves the
finite sparse-forbidden deletion law, reservoir elementary-symmetric factorial bounds, exact
checkerboard parity and Wold drift, square-root row supply, mixed Gibbs cost, physical co-degree
bound, and moving-seam sector law. Physical collision quotient leaves opposite-sign near-Hall
supply at only `X^(-o(1))` loss, and parity coalescence removes selected-mass loss while forcing the
distinguished large-prime coordinate to be replaced. Existence of enough seam-compatible physical
cells is no longer open.

The whole-anchor relation gives both grade directions with exact reservoir decoding, exact
row-stochastic reciprocal kernel, one-edge cost `X^(-1/2+o(1))`, same `1->0` seam crossing, and a
polylogarithmic incoming bound. The reciprocal square-root Jacobian cancels reservoir magnitude,
but current structured all-interval `E_3` supply leaves a genuine logarithmic deficit. The
prime-log/Pluecker bridge identifies projective two-column load dispersion with Route P's cubic
Gram separation up to universal factor three; it does not remove the deficit.

Cross-route information geometry now identifies a quantitative capacity coordinate. For a
balanced two-column physical packet with positive rates `a,b`, Route-E chi-square is
`chi=((a-b)/(a+b))^2`. Route P's cubic Cauchy Pluecker defect is exactly
`chi(3-3chi+chi^2)`, between `chi` and `3chi`. Thus projective rate dispersion and cubic Gram area
are equivalent producers. Orbit count or pair-switch connectivity without rate dispersion can
still coalesce quadratically and cannot force capacity.

Finite phase randomization is exact at relevant low degrees and gives collision concentration, but
the singular return graph is below the generic Sobolev trace threshold. It can support relation
admissibility; it does not prove physical capacity.

The analytic import interface is now exact rather than Gallagher-lossy. For every finite
logarithmic window Lean proves
`integral |S(u)|^2 du = integral |K_delta(w)|^2 |A(w)|^2 dw`, with
`|K_delta(w)|^2<=min(delta^2,(pi w)^(-2))` and no supremum remainder. Route E's product fibres
already have one common multiplicative width, so the additive-window conversion is unnecessary.
Lean also transfers this line mean square to every separated finite family of starting windows,
with an explicit endpoint-oscillation cost controlled by coefficient size and interval counts.
This closes both continuous and discrete analytic interfaces and removes the artificial
square-root-window barrier. It does not prove Möbius frequency cancellation. Formal import starts
with Vinogradov--Korobov twisted sums/zero-free input, then large values and Halász--Montgomery;
the separate all-interval `E_3` input remains external too.

**Open core.** On one of the now-fixed relations, prove the subpower/polylog-to-unit upgrade:

- unit physical incoming Carleson load uniformly on every ordinary interval and central Wold layer;
- normalized co-moving `1->0` sector flux for the same row-stochastic kernel;
- retention of the already-proved strict-half total Gibbs cost under that unit normalization.

For the whole-anchor relation this requires a short-interval almost-prime density/local Wold-layer
law stronger than current structured `E_3` input, with parity synchronized before reservoir scale is
chosen. Natural-density rough `P_5` alone fails because observed token breadth changes the defining
interval. For the coalesced cube it is the same analytic problem in higher-dimensional form:
upgrade near-Hall cardinality to unit weighted interval capacity without losing forced seam flux.

The required short-window import is now identified sharply. The three upstream Route-E cards use
Menon's quantitative mean-square rate
`(log log L)^2/(log L)^2`, because their Markov step needs `R_L log X=o(1)`. The older
Matomäki--Radziwiłł rate `(log L)^(-c)` with `c<1` cannot meet that gate on any admissible window.
Formalization must carry the quantitative Halász distance of Möbius through the MR ladder to obtain
`(log L)^(-2+o(1))`; Matomäki--Teräväinen all-interval `E_3` remains a separate input. Even both
imports are upstream of the final weighted-Hall/Carleson and co-moving-flux theorem.

Multi-node and slot-sequence separation preserve squarefree jet multiplicity, but do not create
capacity. Additional scalar moments, Gaussian approximations, patch estimates, or complete-
bipartite flows are dead work.

**Principal Lean evidence.** Route-E depth/breadth reduction modules,
`MobiusSparseForbiddenDeletion.lean`, `ReservoirElementarySymmetric.lean`,
`MobiusParityCoalescedFullMassCube.lean`, `MobiusParityCoalescedProductLaws.lean`,
`MobiusReciprocalAllocationJacobian.lean`, `MobiusReciprocalAllocationColumnBound.lean`,
`WholeAnchorHarmonicE3.lean`, `Sieve/HarmonicReservoirCapacity.lean`,
`RouteESourceFaithfulEulerTiltUnitShell.lean`, saddle/escape no-go modules,
`MultiNodeInjectiveParameter.lean`, `SlotSequenceSeparation.lean`,
`HTGeometry/BooleanConjunctionParity.lean`, `HTGeometry/ReedMullerEvaluationRank.lean`,
`HTGeometry/MultilinearEvaluationUniformity.lean`,
`HTGeometry/FinitePhaseCharacterTransfer.lean`, `HTGeometry/FinitePhaseTrigProduct.lean`,
`HTGeometry/CubicPhaseCollisionMoments.lean`, and
`HTGeometry/CubicPhaseCollisionConcentration.lean`; `Sieve/LogWindowPlancherel.lean` and
`Sieve/LogWindowDiscreteTransfer.lean`.

### Route G — Suzuki two-angle meromorphic source

**Endpoint.** A source-admitted Suzuki Hermite–Biehler/de Branges carrier implies RH.

Route G contains two primary producer branches sharing completed Suzuki source. A coalescing-anchor
Schur sublane is an equivalent floor-side classifier, not a third independent route.

#### G-floor branch

Literal restricted-Weil form has a Friedrichs operator, compact resolvent, attained ground vector,
dense smooth source range with same Rayleigh infimum, formally self-adjoint `D†G_aD`, exact complex
mixed source form, real corrections on real core, and strict Beurling–Deny modulus irreducibility.
The canonical coercive energy renorm constructs Suzuki's actual Hilbert space `H(T_a)`, proves its
topological equivalence with the closed form domain, embeds it continuously and injectively in
physical interval `L2`, and makes the smooth compactly supported CCM source core dense in that
energy space. That core is now literally mathlib's native complex `C_c^infinity(-a,a)` test-function
space, with linear injective dense realization and native complex-linear `i d/dx`. Thus Hilbert-
space completion, linear smooth-core structure, and source-core density are no longer hidden
premises.
For every real shift, Lean now identifies closure of shifted smooth derivative range with kernel of
one exponential moment functional and proves adjoint kernel has complex dimension one. The two
deficiency shifts therefore have exact indices `(1,1)`. Boundary port count is fixed inside
Suzuki energy space; this does not identify aperture Morse charge with Xi zeros or orient port.
The limiting logarithmic variational constant is exactly the bottom eigenvalue of complete closed
operator, and its bottom eigenspace is one complex line. More strongly, throughout one explicit
punctured neighborhood of aperture zero, exact finite-aperture ground energy is positive, has
Suzuki's sharp logarithmic main term with explicit `O(a)` error, and has one nonzero even generator.

The aperture-Morse programme now has a precise global target. Paper-level source analysis identifies
the supremal negative index with number of right-half Xi zeros and with supremal model-space
dimension. Lean certifies algebra that makes this plausible but not full source identification:
one real divisor packet is positive rank one, a conjugate off-line pair supplies one negative
square, negative subspaces survive small perturbation and linear transport, finite packets admit
one uniform horizontal shift, and cofinal finite indices squeeze to global Morse charge. Thus
off-line charge cannot hide at infinite aperture once analytic screw-series and Krein--Langer
identification are supplied.

Visible prime torque is now exactly a locally finite nonnegative tent series, with each prime-power
term born at `L=log n`. Lean proves continuity/exponential order, absolute termwise Laplace
summation, exact archimedean transform, and full identity with completed-Xi curvature continuation
on `Re(s)>3/2`; that continuation is analytic at every nonzero real point because Xi has no real
zeros. Lean also proves exact double pole of continuation above every open-strip Xi zero. Complex
Laplace holomorphy, entire head transform, existence/rigidity of convergence abscissa, and Landau
singularity are formal. For any eventual one-sign tail, reference thickening by `exp(u/4)` now
constructs nonnegative measure with convergence abscissa pinned inside `[1/4,3/2]`, eliminating
possible everywhere-convergent escape. Lean now completes the cofinal conclusion: complete position
torque is neither eventually nonnegative nor eventually nonpositive, changes sign cofinally, and
crosses every fixed baseline. Scalar position torque is therefore closed negatively as an
orientation producer: it is an irreducibly oscillatory source observable, not a positivity law.

The scalar wall receiver is also exact. Literal Suzuki Cauchy-height transport is isometric to the
unit-Riesz coherent frame; the polar continuum, lower Hardy values, and outgoing CCM charge are
evaluated without a dictionary hypothesis. The resulting point inequality is equivalent to RH.
This closes carrier and scalar classification, but supplies no source-side bound. Separately, the
rank-zero/one aperture below the second visible prime has coefficient-faithful `H^1_0` closure by
three integrations by parts and complementary primitive cancellation. It does not cross the second
prime or identify the full completed Evans kernel. Arbitrary bounded nonnormal adjacency now also
has an exact finite source-forced prime-normal tower with one residual, so normality is not the
remaining exterior obstruction.

Reporter secants now expose a concrete interscale sign channel. Their Cauchy-height packet obeys
the exact Ward-capacity inequality against lower-Hardy evaluation, while a cross-Gram with one lag
at least twice the other is strictly negative. Lean now classifies the intervening band exactly:
for every shallow lag `p>0` there is one transition depth in `(3p/2,2p)`, with positive Gram before
it and negative Gram after it. Positive coefficients therefore create a source-localized signed
interscale channel. The raw literal natural-packet Cauchy energy has a linear lower bound along
apertures `8n`, whereas rectangular Xi curvature has an unconditional `O(sqrt n)` envelope. Their
exact natural Ward defect therefore tends to `-infinity` along `8n`, whether RH is true or false.
Anchor-visible linear mass must be removed before Gram/cofinal passage, and the renormalized
remainder must still orient Morse charge (`SuzukiNaturalApertureCauchyEnergyEscape.lean`,
`SuzukiNaturalApertureWardScalingNoGo.lean`).

The first-crossing target is also sharper. Exact scaling to full CCM form plus small-aperture
positivity, continuity, antitonicity, and attainment prove that false RH has a least zero aperture
whose null ground is absent from every strict smooth interior source. G-floor must therefore
identify/exclude this completed-boundary rough mode; no smooth-core index argument can see it
directly.

The coalescing-anchor sublane now has exact tangent, normal-family, and receiver laws. Its singular
quotient has first-order limit `i/z-H/G`, degenerating to `i/z` without an adjacent mode. Finite
Schur members have positive real part; two-sided compact-local normality is closed. In chart
`s=1/2-iz`, any locally bounded source family with nonnegative real part converging on one
accumulating set to a nonzero multiple of `Xi/Xi'` forces RH. Constructing that source-admitted
Herglotz family—not analytic landing—is the producer.

The coalescing gate is now quantitative and branch-complete. In the literal half-interval
decomposition `q_e=C+H_a`, `q_o=C-H_a`, midpoint reflection gives the `sech(a)` Cayley bound. If
`K=C^(-1/2)H_aC^(-1/2)` and `r=max(0,-inf spec K)`, every Xi-matching family has
`liminf r>77/85` and odd/even source-energy ratio above `81/4`. Lean proves source-alignment,
bottom-edge deficit integrals, parity phase clocks, hard-edge separation, low-only/high-assisted
exhaustion, ridge-matched visibility, polynomial ordinate horizon, and cross-coherence barriers.
Generic ultranull packets exist but are source-invisible; a localized prime seam has zero
normalized Hankel strength.

The high-assisted branch is no longer a vague edge-construction problem. Schur whitening splits it
into direct-tail amplification or singular mass of `TT*` generated by the literal low source;
capacity-gap inequalities eliminate direct-tail amplification. Every survivor therefore satisfies

```text
mu_w((1/113,1]) > r/(128 C_T) >> r/log(1/r)^2,
```

with `C_T` logarithmic in the polynomial source horizon. The first falsifiable source theorem is
the opposite upper bound `mu_w((1/113,1])=o(r/log^2(1/r))`; alternatively an actual source family
meeting the forced lower bound would keep the branch alive. The low-only branch remains possible
only under its proved aperture-rate ceiling. Marginal hard-edge laws, finite moments, tail
completeness, and generic small singular values cannot decide either branch.

Boundary-layer schedules still sweep from literal-ground to reduced-resolvent coefficients, and
low-only/high-assisted schedules are exhaustive. Aligning negative light at apertures `8n` leaves
positive-light mass tending to infinity. A live construction must compensate before light
projection while retaining first-order lag energy, or exclude schedules by source admission.
The literal Suzuki interval is now a bounded coordinate and the model-free coalescing theorem gives
its exact first visible even/odd rates. Three-turn Blaschke fragmentation attains antipodal Clark
levels arbitrarily close to every physical point; together with the general shrinking-level
obstruction, this rules out a continuous-uniform-limit shortcut unless source admission excludes
that fragmentation. For every even `C1` truncated-convolution kernel, Fourier compression is a
centered divided-difference packet. Under a simple isolated odd ground and positive gap, compressed
minima converge to the floor and phase-normalized grounds converge in mean square to the true
ground, yielding the real-zero receiver. This remains a G/O adapter, not a route: no theorem
identifies a literal RH-bearing kernel or proves those ground hypotheses for it.

The exterior wall has moved beyond finite Gram search. Completed unit-Riesz prime--polar--Gamma
Ward wall is exactly finite prime wall minus regular-screw continuum at every complex height. At
lower Hardy point both masses are nonnegative and Suzuki Green is their exact imbalance. Literal
atomic--continuous source decomposition is therefore closed. Cubic aperture innovation before
light split makes full prime/depth field square summable and yields completed PSD positive/negative
light kernels with exact global Ward identity. Marked halfgap debt has exact total-mass law and an
aperture-, height-, and halfgap-uniform cofinal ceiling. Completed light diagonal is height-flat;
what remains is comparison, not source occurrence.

**Open core.** Floor branch needs aperture-Morse exhaustion and exclusion of the classified
completed-boundary rough first-contact mode. Coalescing branch needs the literal low-source cyclic
mass upper bound above `1/113`, or a construction realizing the opposite forced lower bound; the
older generic `77/85` edge formulation is superseded. Wall branch needs
`SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`. All-prime light completion and marked halfgap uniformity
and atomic--continuous prime--Gamma weld are closed. Missing theorem must compare explicit positive
prime/regular-screw imbalance and remaining division-free Robin/Neumann-holonomy jump with completed
negative-light channel, pay exact Schur coupling tax, and leave a uniformly lower-semibounded
height-dependent rectangular residual. Equivalently, for one curvature-selected admissible shift
pair, prove Loewner growth-versus-deficit inequality for full one-sided Euler--Gamma plus Neumann-
holonomy jump kernel. Bare resolvent squares and height-flat dressed light carrier remain formally
insufficient.

The common unit-Riesz completed current now has a canonical positive exponential increment Gram,
with exact prime-minus-polar trace and explicit source-side crowding determinant. It does not
instantiate Suzuki's screw kernel or orient aperture Morse charge. A genuine G merger must identify
that Gram as a source-admitted subcarrier of the literal Suzuki form while retaining the polar
subtraction and prove index-preserving cofinal transport; scalar trace equality is insufficient.
This restriction is sharp: finite coherent packets disprove every fixed sample-versus-polar
Loewner constant, while their piecewise generator energy equals four times source-Gram energy.
Route G admission must therefore be graph-bounded and retain first-order lag energy; a trace-only
Suzuki merger is now excluded before any aperture limit.
The literal completed outgoing projection makes trace-only failure exact. It is one HG exponential
mode with coefficient `R_1(log N)/2`, and its full boundary trace is collinear with canonical pole
trace. Thus all-aperture pole domination is equivalent to `R_1(log N)^2<=16`; aperture variation
adds no Suzuki orientation. Any G merger must couple this rank-one outgoing charge to retained
root/bulk modes or Morse index before scalar trace, rather than use it as standalone positivity.

#### G-exterior branch

Weak Gamma equation is classified on each full frequency ray; point-supported solutions vanish.
Homogeneous channels glue through upper strip exactly when `c_-=-i c_+`, equivalently zero half-log
endpoint trace. One Fourier profile represents every interior height. Two-sided Gamma carrier,
forced-ray Hardy, one-prime nonnormal similarity, and terminal pruning are closed. Normalized Gamma
jump is bounded nonnegative accretive Hilbert-valued multiplier with exact first-order control.
Endpoint-centered one-prime polar trace is an unconditional whole-line `L2` weak-derivative pair;
continuous codomain maps and finite sums preserve such pairs. Literal two-endpoint one-prime
terminal vector, both forced Hardy rays, paired cutoff event geometry, and uniform paired-source
`ell2` bound are closed. Gamma cutoff commutator has an exponentially localized block kernel and a
global `L2` convolution bound; abstract terminal Volterra blocks then acquire exponential decay and
weighted `L2` admission.

Literal paired source assembly is now closed at source-equation level. Rooted left/right cosets
have exact opposite valuation transport, canonical scale-buffered cutoff is supported exactly in
physical aperture, event windows have width `log 2`, physical roots have forced outward-zero/
inward-one behavior, cutoff derivative is uniformly bounded on support, paired source is uniformly
`ell2`, finite-recurrence polynomial clock weights are summable under exact slope gap, and
coordinatewise primitive-flux identity extends to whole finite-`p` carrier by density.
Critical aperture dressing now survives cofinal prime/depth summation: squared dressed boundary
atoms and rooted completion are summable, and complete marked local--global compound factors
exactly as dressed determinant line times undressed compound. This closes a prior cofinal
admissibility concern without deciding compound sign or completed return orientation.

Generic root-retained projection is also exact. If full carrier solves
`(2L I+R-T)F'+F=0`, projection commuting with jump and differentiation yields interior equation
forced solely by `P T (I-P)F'`; this source is `L2` whenever exterior derivative is `L2`, and
classical Schur complement can be recovered afterward from exterior inverse witness. No concrete
completed Suzuki carrier yet instantiates this retained equation. Its terminal analytic support is
now substantially closed: projected prime-normal profile begins at grade one and decays as
`L^-3/2`; its first two derivatives have the required power decay; one Fourier derivative pays for
the affine Gamma jump; the Gamma correction derivative and projected exterior source are
unweighted `L2`; dyadic terminal blocks sum beyond exact derivative-loss threshold; low germs are
weighted-subcritical for every exponent below one. Generic unweighted energy law gives
`(mu-tau)||E'||<=||forcing||` above `2L_0>tau`. The Gamma jump difference now has an integrable
commutator majorant `C |chiHat(t)| (|t|+t^2)`, hence a Young `L2` bound on the `H1` side. Strip
propagator and inverse have whole-line decay, homogeneous square-integrability, finite-window
bounds, and forced global `L2` assembly. Physical wall blocks carry an explicit finite numerical
floor `Re wallSymbol_sigma >= -gammaShiftKappa(sigma)`. These close the generic cutoff-residual,
commutator, window, block, and numerical-range gates. Scattering lemmas also prove that an `L2`
remainder cannot cancel a non-`L2` leading charge. None identifies the actual completed modes,
proves their global cutoff equation, or orients their return.

Derivative-level wall analysis is closed as well. Lean constructs the third generator jet, proves
three integrations by parts leave a cubic-decay remainder, upgrades the tested weak equation to
physical `H1` for shifts `sigma>1/2`, and proves the whole-line frequency-weighted profile is
square-integrable exactly when both outgoing scattering charges vanish. Compact block solutions
are genuine `L2` vectors and their source-weighted series converges. These results remove the
derivative/scattering/block-source regularity gate; they do not show the literal completed source
has both charges zero or identify its return with Xi orientation.
`StripPropagatorCancellation.lean` proves propagator and inverse cancel exactly in first
boundary term, so its frequency behavior is pure physical-phase resolvent average. Transport
growth is not remaining obstruction there; source realization and resolvent charge are.

The literal wall-generator adapter is now substantially closed. Lean differentiates Gamma ratio,
constructs its holomorphic square-root branch, proves exact inverse and phase-shifted generator
equations, obtains a logarithmic coercive floor and first/second frequency-jet decay, and combines
inverse-family differentiation with two integrations by parts to give quadratic amplitude tails.
Under the strict numerical-floor hypothesis, the shifted Gamma-wall inverse is now identified
exactly with the Laplace transform of its accretive semigroup orbit. This turns the first boundary
resolvent into Plancherel-compatible semigroup slices; it supplies representation, not source
reconstruction or return orientation.
For a block profile supported in `[m,m+1]`, Lean now proves exact angular slice energy bound
`2*pi*exp(-2sm)` times physical block energy. This closes semigroup-slice hypothesis used by block
Laplace estimate; it still assumes literal completed source profile and does not determine sign.
The first boundary term itself is now represented as that Laplace superposition and has a uniform
terminal-ray `L2` bound `mu_0^-1` times block energy under the literal wall-floor hypotheses.
Propagator ray mass and sharpened Hardy estimates also make second boundary and quadratic remainder
bounds quantitative with constants independent of terminal threshold. Boundary integrability is
therefore closed; source realization and oriented return are not.
Compact-interval hypotheses now imply required integrability automatically. Literal one-block
source transform commutes with inverse propagator and frequency window; evaluated twofold
expansion and endpoint transport cancellation are formal. These theorems remove generator/block-tail
regularity as obstacle; they do not construct completed source mode or decide return sign.
The four resulting ray terms are now measurable before integration and their squared composition
costs only explicit factor sixteen. Their sum bounds literal moving tail on entire terminal ray;
accumulated threshold datum has exact one-extra-power growth compatible with propagator ray decay.
Inward remainder ray follows by reflection, and forced terminal profile is bounded by propagated
threshold datum plus moving tail. Window profile splits with no extra threshold power, and window
plus both rays compose to full frequency-line bound. Thus generic one-block forced-profile estimate
is closed. Block-source frequency energy is exactly `pi/2` times physical profile energy, fixing
normalization consumed by window estimate. The remaining threshold arithmetic is now exact too:
`X_m=max(C_0,1) exp(max(0,-m))` opens the wall floor uniformly on `[m,m+1]`; the one-block `L1`
mass costs at most its `L2` mass; and exponent cancellation lands every tail term on precisely
`X_m^2`. Consequently propagated datum on the outward ray has one uniform energy bound
`C(||c||^2+Y^2 integral||g||^2)`. No literal completed source vector, kernel identification, or sign
is created by this bookkeeping.

The exterior Evans problem is now source-shaped rather than formally infinite-dimensional. Finite
analytic characteristic packets have exact exponential-polynomial mode spaces. Complete Gamma
boundary is nevertheless infinite rank, so a raw finite characteristic determinant is invalid.
After exact rational/logarithmic reconstruction, Lean isolates a residual space of dimension `2L`
with explicit right/left Bessel-tail modes. The reconstructed characteristic source also has
dimension `2L`; consequently the residual Evans map is square, and under the still-missing
kernel isomorphism its determinant is nonzero exactly when the restricted-Weil eigenspace is
trivial. The exterior-kernel/Laplace identification, logarithmic Dirichlet reconstruction, and
actual Bessel residual computation remain outside this square criterion, so it is an exact
conditional reduction, not a proved Suzuki injectivity theorem.

Recent exterior-symbol, logarithmic-Dirichlet, spectral-parameter, and stabilized-Evans modules
formalize conditional operator algebra only. They prove no-lower-bound behavior for a decaying
positive injective symbol, coercive reconstruction once a positive log-symbol floor is supplied,
kernel/Morse transfer under an assumed fibrewise isomorphism, and positivity of root-free real
stabilizing factors. Actual Suzuki compression, closed graph, Grushin bundle, determinant-line
gluing, and zero-Morse orientation remain outside their Lean statements. They narrow admissible
completion architecture but do not close reconstruction or create another route.

Determinant-only Evans orientation is formally excluded only for the earlier screw-variable
presentation: dimension `d` maps into `d+3`, and its Gram determinant is a squared Pluecker norm
that cannot retain crossing orientation. The reconstructed restricted-Weil eigenfunction variable
removes those three excess conditions and yields the square `2L` map above. This repairs the
determinant-line mismatch, but not the source theorem: one must instantiate reconstruction and
kernel transfer, glue the line across characteristic strata, and prove nonvanishing on
`lambda<=0` at every aperture. Squareness is a faithful receiver, not orientation or positivity.

Uniform logarithmic recurrence control is impossible on all apertures: for prime-log rank at least
two, apertures of infinite logarithmic type form a dense comeagre set. Weighted lattice evolution
is polynomially bounded on its natural shell domain, but an all-aperture exterior theorem must
cross this Liouville set by closed-graph or nontempered continuation, not a uniform event clock.

**Open core.** Identify every completed zero mode with full root-retained Gamma normal family and
the reconstructed infinite boundary, prove exact global cutoff/logarithmic Dirichlet intertwining,
and show resulting finite residual source map is injective at every aperture. Then lift nonvanishing
to an oriented two-port return class. Generic `H1(dL)`/`L2(dL)`, wall-generator, commutator,
strip-window, block, finite-residual, and numerical-range estimates are closed; literal source
realization and oriented injectivity are not.

More one-prime regularity, generic weak-derivative theory, homogeneous strip estimates, or Gamma
symbol bounds do not advance exterior branch.

**Principal Lean evidence.** Suzuki restricted-Weil/Friedrichs modules,
`SuzukiTaHilbertSpace.lean`, `SuzukiTaSmoothCore.lean`,
`SuzukiTaDeficiencyIndices.lean`,
`SuzukiTorqueTentSeries.lean`, `SuzukiTorquePrimeSeries.lean`,
`SuzukiTorquePrimeLaplace.lean`, `SuzukiTorqueArchLaplace.lean`,
`SuzukiTorquePrimeOrder.lean`, `SuzukiTorqueArchOrder.lean`,
`SuzukiTorqueTotalTransform.lean`, `SuzukiTorqueEulerTransform.lean`,
`SuzukiTorqueContinuationAnalytic.lean`, `RiemannXiRealAxisNonvanishing.lean`,
`SuzukiTorqueContinuationPole.lean`, `ComplexLaplaceHolomorphy.lean`,
`HeadLaplaceEntire.lean`, `LaplaceAbscissaExists.lean`, `RealJetsOfHolomorphic.lean`,
`LandauSingularAtAbscissa.lean`, `TailMeasureLaplace.lean`,
`SuzukiTorqueCofinalSign.lean`, `SuzukiCauchyWallUnitRieszIsometry.lean`,
`SuzukiCauchyWallHardyEvaluation.lean`, `SuzukiCauchyWallGammaSecantAssembly.lean`,
`SuzukiCauchyReporterSecantWardCapacity.lean`,
`SuzukiCauchyReporterSecantSharpTransition.lean`,
`SuzukiOnePrimeChartClosure.lean`, `SuzukiOnePrimeOneBlockEstimate.lean`,
`SuzukiNonnormalForcedPrimeNormalTower.lean`,
`SuzukiFirstContactBoundaryRoughness.lean`,
`SuzukiLimitingLogGroundIdentification.lean`, `SuzukiLimitingLogGroundSimplicity.lean`,
`SuzukiSmallApertureTheoremOneFour.lean`, `SuzukiCoalescingFullQuotientLimit.lean`, `SuzukiCoalescingHalfPlaneUniqueness.lean`, `SuzukiWardFixedTwoLightPhaseLeakage.lean`, Gamma weak-equation classification modules,
`GammaJumpFourierMultiplier.lean`, `SuzukiOnePrimePolarTerminalSource.lean`,
`SuzukiLiteralPairedSourceAssembly.lean`, `SuzukiPairedCutoffEventGeometry.lean`,
`SuzukiPairedSourceL2Bound.lean`, `SuzukiCoordinateCutoffPrimitiveFlux.lean`,
`SuzukiApertureDressedMarkedCompoundCofinal.lean`,
`SuzukiRootRetainedProjectedSource.lean`, `SuzukiRootRetainedEnergyEstimate.lean`,
`SuzukiRootRetainedTerminalBlocks.lean`, `SuzukiRootRetainedJumpSource.lean`,
`SuzukiGammaWallTailEstimate.lean`, `GammaRatioLineDecay.lean`,
`StripPropagatorLineDecay.lean`, `WallSymbolFrequencyJets.lean`,
`GammaRatioBranchDerivative.lean`, `WallGeneratorEquation.lean`,
`WallGeneratorLogCoercivity.lean`, `WallGeneratorFrequencyJets.lean`,
`WallResolventLaplace.lean`,
`WallBlockSliceProfile.lean`, `WallBlockResolventRegularity.lean`,
`WallFirstBoundaryLaplace.lean`, `WallFirstBoundarySquareIntegrable.lean`,
`StripPropagatorRayMass.lean`,
`HTGeometry/InverseFamilyDerivative.lean`, `HTGeometry/ResolventSymbolTailDecay.lean`,
`HTGeometry/PhaseGeneratorIntegrationByParts.lean`,
`HTGeometry/BlockWindowFubini.lean`, `WallBlockSourceExpansion.lean`,
`WallPropagatedExpansion.lean`, `WallBoundaryTransportCancellation.lean`,
`WallTailIntegrationByParts.lean`,
`WallTailRayEstimates.lean`, `WallTailBlockDecomposition.lean`,
`WallTailRayComposition.lean`, `WallMovingTailBound.lean`, `WallThresholdDatum.lean`,
`WallInwardRayReflection.lean`, `WallForcedProfileRay.lean`, `WallForcedProfileWindow.lean`,
`WallBlockSourceEnergy.lean`, `WallThresholdArithmetic.lean`, `WallBlockThreshold.lean`,
`WallDatumRayBound.lean`,
`WallGeneratorThirdJet.lean`, `WallThirdIntegrationByParts.lean`,
`WallVectorDerivativeWall.lean`, `WallScatteringCriterionLine.lean`,
`WallForcedProfileMemLp.lean`, `WallBlockSeries.lean`, `ScalarAnalyticForcingH1.lean`,
`ShiftedGammaConjugation.lean`, `ShiftedGammaJumpDerivative.lean`,
`GammaTestPairingMajorant.lean`, `GammaJumpTranspose.lean`,
`GammaCutoffCommutatorBridge.lean`, `GammaCompactSupportWall.lean`,
`GammaWallTerminalBlockSource.lean`, and `GammaWallBlockTransfer.lean`,
`GammaJumpNearDiagonalLipschitz.lean`, `GammaJumpCommutatorKernel.lean`,
`SuzukiWallBlockSliceBound.lean`, `SuzukiWallWindowEstimate.lean`,
`ShiftedGammaNumericalRange.lean`, `FrequencyLineSplit.lean`,
`GlobalPowerTailSquareIntegrable.lean`, `MinkowskiIntegralInequality.lean`,
`CCMApertureMorseExhaustion.lean`, `CCMCharacteristicCrossingModes.lean`,
`CCMEvansBoundaryInfiniteRank.lean`, `CCMRationalResidualEvansMatrix.lean`,
`CCMRestrictedWeilSquareEvans.lean`,
`CCMEvansDeterminantLine.lean`, `CCMExteriorInverseSymbol.lean`,
`CCMLogSymbolDirichlet.lean`, `CCMSpectralParameterEvans.lean`,
`CCMWeierstrassStabilizedEvans.lean`, `StripPropagatorCancellation.lean`,
`SuzukiToeplitzSechWall.lean`, `SuzukiSourceAlignmentDeficitIntegral.lean`,
`SuzukiRelativeEdgeFloorRigidity.lean`, `SuzukiPrimeSeamMicrolocalStrength.lean`,
`SuzukiSourceCyclicBandEdge.lean`, `SuzukiSchurLeverageCertificate.lean`,
`SuzukiCrossCoherenceBarrier.lean`, `SuzukiNearNullPhaseDiagram.lean`,
`SuzukiUltranullPacket.lean`, `SuzukiRidgeDefectMonotone.lean`,
`SuzukiExponentialSourceCayley.lean`, `HTGeometry/GapOccupancyTraceMoment.lean`,
`HTGeometry/LpSingleExtension.lean`, `ScatteringChargeNecessity.lean`, and flat-flux block modules.

### Route L — Deninger/Green/Hodge source descent

**Endpoint.** A source-formed arithmetic Poisson/Green complex whose harmonic complement maps
faithfully and cup-isometrically to Meyer nuclear cohomology carries a positive Hodge block;
weight-one flow then forces every Xi divisor to the critical line. The strict Green/BV physical
landing below is an exact receiver for the same conclusion, not now an independent producer.

**Architecture.** Required commutative square is fixed:

```text
completed Green ⊗ BV_1  --id⊗b-->  completed Green ⊗ BV_0
          | F_1                              | F_0
          v                                  v
    resolved target_1  -----d_T----->  resolved target_0
                                                |
                                                v
                                      fixed physical reader.
```

Existing comparison supplies fixed Burnol/Deninger physical landing and source-derived singular
class. Physical evaluation of `(t^-1-1)(t-1)` is `-2(cosh(a)-1)`; nonnegativity is equivalent to
trivial holonomy, fixed Deninger boundary, unit Meyer-character norm, and critical placement. The
latest parametric classification shows that reciprocal Big-Witt/Gamma/Green naturality cannot
produce this positivity. Route L therefore survives only through a stronger source Green/Hodge
construction that retains critical-scale prime information before scalar landing.

**Established structure.** Completed Xi Green primitive, coefficient-faithful Green-to-Calderón–
Witt comparison, Tate boundary/top-coordinate reader, actual Burnol conormal identity,
ordinary-integer BV/Hochschild boundary, all-cross-prime Koszul cycle, rational-adelic relative
complex, and strict resolved-Xi chain provenance are closed. Big-Witt prime-seam source has first
ghost zero and second ghost `-2` times physical Dirichlet energy.
Tate descent over `Q` is also closed: rational real Milnor amplitude has only degrees zero and one, so no higher rational-real product can supply missing Hodge interaction.
Cartan contraction makes every unit-coordinate Koszul complex explicit. Lean now instantiates it:
off the critical line every coordinate `U_p-p^(1/2-s)` is invertible, with uniform worst bound at
`p=2`, so every finite commuting prime-translation Koszul complex contracts. This still does not
identify its boundaries with the fixed Burnol/Deninger physical landing
(`PrimeTranslationKoszulOffLine.lean`).

The Meyer strong logarithmic target now has a canonical injective half-density map into ordinary
`L2(C,2,volume)`. Centered Meyer flow becomes literal unitary translation, and each Xi-selected
prime Koszul coordinate intertwines coefficient-faithfully with normalized `L2` translation. Off
the critical line that ambient coordinate is a unit, but its inverse cannot preserve the full
strong-source image. Conversely, preservation of the strong image at one prime forces
`Re(rho)=1/2`; preservation for every Xi divisor implies RH. This closes generic source-to-Hilbert
comparison and exposes a second exact RH-bearing descent statement, not its source proof.

Integral bidirectional Cartier descent is now classified in the same source language. Full Laurent
source has an unconditional, coefficient- and multiplicity-faithful Gamma evaluation at every Xi
divisor and ordinary-prime clock. Strict inversion closes only after retaining its quadratic ghost;
factoring this canonical producer through additive Cartier conormal `I/I^2` erases that ghost iff
centered grade is zero. Lean identifies this condition exactly with simultaneous integral Big-Witt
lifts, centered Hurwitz monodromy, rational Cartier landing, genuine two-prime source/Gamma
naturality, bilateral formation admission, and summability of derivative-free Gamma-six determinant
current. Global conormal descent is RH. Reflection-folded Green--Stokes normal form realizes ghost
and literal cyclic anomaly on one pinned harmonic line with exact Ward sum zero. Both lie in adjoint
kernel and an artificial relative-boundary range; each enters coefficient-faithful physical range,
or vanishes, exactly on critical line. Global physical Stokes-flatness is RH. Missing theorem is a
source law admitting this selected coefficient into physical range without quotienting it away.

Frobenius, incidence, BV, and Calkin bookkeeping is closed. Division-free Frobenius two has the
full ghost law over every commutative ring; each ordered seam ghost is negative twice the squared
essential norm of its literal Sonin--Euler Calkin corner. Pairwise cyclic repair and finite Witt
powers preserve rather than reduce this obstruction. All-cross polarization constructs exact
diagonal/off-diagonal cancellation before scalarization, but coefficient-faithful transport proves
the ground reader kills that compensator iff it already kills the physical pair. These mechanisms
are terminal algebraic identities, not candidate annihilation laws.

The singularity required by the label-faithful completion is also explicit.
Finite right-edge coefficients embed faithfully into the actual ordered-edge
Calderón packet Hilbert space. Their algebraic one-leg trace is coordinate
summation, and the coherent Frobenius fiber factors exactly as
`(-2 L_pq)` times this trace of the right-leg packet. No continuous linear
functional on the completed `ell^2` packet extends that algebraic trace.
More sharply, uniform averages of `N` distinct packet coordinates converge to
zero in `ell^2` while their trace remains exactly one, so the algebraic trace
is sequentially nonclosable. Thus a bounded or closed-graph one-leg extension
on the existing completion is formally impossible.

Its exact singular graph completion is nevertheless known. The full finite one-leg graph is dense
in `ell^2 direct-sum C` and contains a nonzero vertical trace generator invisible to ambient packet
projection. Complete coherent Frobenius right-leg fibres lie in the closed trace kernel, so their
graph closure cannot reach that generator. Puncturing one source-selected ordered edge before
coherent summation escapes the kernel and its continuous graph readout is exactly the negative
four-label Frobenius coefficient. This supplies a lawful selected singular compensator, not the
canonical Xi-fibre selection or physical annihilation theorem required by Route L.

The vertical generator is arithmetic rather than an arbitrary averaging artifact. On the
canonical ordered row from prime two to every later prime, literal Big-Witt coefficients are
`1/(2q)`: their finite trace diverges while their ambient cross-prime `ell^2` norm stays uniformly
bounded. Dividing each finite row by its own trace gives labelled source packets with trace one,
ambient realization tending to zero, and singular-graph realization tending to the vertical
generator. Weighting by an actual completed Xi Green coefficient preserves the Xi fibre exactly;
undoing finite normalization on every retained edge recovers the raw all-cross-prime incidence,
and continuous graph readout converges coefficient-faithfully. Source production of the singular
class is therefore closed. The actual normalized Gamma boundary is now a continuous readout on
that source-derived vertical sector; for reflected-Gaussian completed-Xi provenance, its vanishing
is equivalent to `Re(s)=1/2`, by comparison at the literal nonzero `(2,3)` Big-Witt coefficient.
Thus Gamma/co-Poisson boundary identification is also closed. The exact remaining core is an
unconditional source Green--Stokes theorem forcing this explicit readout to vanish at every
completed-Xi zero; neither the new graph construction nor its Gamma comparison supplies that
annihilation.

A separate source-specific Gamma-six analysis now identifies why every ordinary strict comparison
failed and supplies the first source-natural carrier beyond that wall.  The literal complete
corrected Möbius tensor source has a nonzero principal class in rectangular weak trace class modulo
trace class.  Its ordinary Wold coface is trace class.  Any linear comparison which sends
rectangular trace-class source operators to compact Sonin operators therefore leaves the physical
Calkin class unchanged; exact comparison is possible only at critical horizontal grade.  This
formally excludes grade-uniform relative cyclic, determinant, Dixmier, and arbitrary trace-class
repairs.  The survivor must be divisor-selective, nonlocal, and nonextendable freely in grade.

The logarithmic Wold--Jordan transgression constructs that missing non-trace-class source coface.
If `G_6` is the actual Gamma-six shell principal operator and
`J_6(n)=log(6) log_6(n+216) G_6(n)`, literal Wold compression satisfies

```text
C_6(J_6) - (1/6) J_6 = (log 6 / 6) G_6.
```

`J_6` is not weak Schatten one, while every positive shell-power regularization is trace class;
affine shell jets with this coface are exactly `J_6+bG_6`.  After tensoring with the actual leading
Gamma-six source vector, the identity is coefficient-faithful.  More importantly, the complete
corrected logarithmic source is constructed: exponential tensor-remainder control survives the
extra shell-depth factor, its logarithmic correction is rectangular trace class, and its complete
coface differs from `(log 6/6)` times the literal full source by rectangular trace class.  The
complete coface is proved not trace class.  Thus the trace-ideal/Sonin no-go no longer applies to
the distinguished source boundary.  Neutral exponent differentiation itself was already known in
Route T; new Route-L content is exact Gamma-six ideal placement and full corrected-source nuclear
control.

The logarithmic primitive now has an actual Gamma/co-Poisson boundary realization, closing the
first place/depth comparison rather than merely renaming its shell coefficient.  Put
`V_23=log(2)log(3)(log(3)-log(2))/2`.  At every honest depth `m`, orientation of the canonical
ordered `(2,3)` Calderon--Witt Green witness after genuine common-test Gamma/co-Poisson transport
at equal depth `m-1` is exactly `-m V_23 6^(-m/2)`.  Forced half-density countertransport gives

```text
m log(6) 6^(-m)
  = -(log(6)/V_23) 6^(-m/2) * actualGammaBoundary_(2,m-1),(3,m-1)(0).
```

Thus the diagonal operator reconstructed from actual boundary evaluations is literally `J_6`,
its tensor lift is the principal logarithmic source operator, and its Wold coface is
`(log 6/6)G_6`.  This is source-specific and retains ordered primes, valuation depth, common test,
and incidence witness.  It does not yet compare with the fixed noncompact Sonin orientation Gram
or prove a Xi-fibre annihilation.

The fixed-Sonin comparison is now closed by a cofinal **total-grade connection**, rather than the
already-ruled-out constant-local-grade shell transport.  At honest depth `m`, holding total grade
`g` fixed forces local half-grade `g/(2m)`.  The resulting reflection multiplier is exactly
`6^(-g)`, independent of depth and hence Wold-flat for every `g`; this does not assert stationarity
of a fixed local grade.  Both logarithmic branches are constant inverse multiples of `J_6`, their
cofaces remain in the same non-trace-class principal class, and genuine equal-depth Gamma/co-Poisson
evaluations reconstruct them.  The actual reflection-odd exterior has the depth-independent
frequency `sinh(g log(6)/2)`.  Lean proves a division-free operator identity: its literal two-sheet
Euler orientation Gram, multiplied by the positive Route-R gauge, equals the fixed `(2,3)` Sonin
commutator multiplied by the strictly positive source calibration
`m V_23 6^(-m/2)`.  Thus prime/depth/full-grade labels and the fixed target boundary class are
simultaneously retained without `1/Xi`, a declared quotient, or compactness.

The singular cofinal graph carrier is now explicit and exact.  Finite depth packets `c` map to
`(c, sum c)` in `ell^2 direct-sum C`; their graph is dense in the full Hilbert product.  Uniform
averages disappear in ambient `ell^2` but converge in graph norm to the nonzero vertical generator
`omega_6=(0,1)`.  After normalization by the strictly positive *source* calibration, every genuine
equal-depth Gamma/co-Poisson orientation Gram is literally the same fixed `(2,3)` Sonin
commutator.  Hence finite actual-Gamma transport equals `(sum c) T_g` and has a unique continuous
extension on the graph completion, sending `omega_6` to `T_g`.  This transport factors through
ambient `ell^2` exactly at neutral total grade.  Thus required singular source object and transport
are constructed; remaining issue is neither completion nor target identification.

The vertical class now has a literal arithmetic degree-one producer.  At every cofinal Tate stage,
the new top atom is proved coordinatewise to be the naturality commutator of the finite forward
arrow with zero extension.  Top-coordinate readout is an exact left inverse.  Tensoring this
differential with the actual rational-adelic CCM cyclic-bar source preserves ordinary-prime
provenance: every literal `p tensor p^{-1}` atom has trace one and maps to the full Tate boundary.
After graph completion, uniform prime-labelled chains converge to `omega_6`.  Weighting by the
existing reflected-Gaussian completed Green coefficient at an actual divisor copy gives a
multiplicity-faithful vertical boundary whose singular trace is exactly the existing Xi Green
fibre and whose ambient projection is zero.  Genuine actual-Gamma transport agrees at every finite
stage and on the limit, producing `g_G(q) T_(2 Re(q)-1)`.

This construction also proves a sharp new restriction: the Meyer--Tate completed differential has
dense range because one fixed ordinary-prime atom realizes every finite graph packet.  Therefore
every continuous graph reader annihilating *all* arithmetic boundaries is zero.  Universal
continuous Stokes descent on this completion is impossible and cannot be advertised as the final
step.

Covariant source flatness is now completely classified. Replacing `t-1` by source-selected
local-system differential `t-exp(a)` makes every physical character Stokes-flat unconditionally,
and coefficient faithfulness forces that holonomy. It equals fixed Deninger differential only at
neutral grade. Full integral quadratic ghost is exactly negative square of Meyer modular norm
imbalance. Canonical Abelian-zeta-gas GNS does not untwist it: its Toeplitz generator is a proper
isometry, positive temperature detects the nontrivial range projection, and no Laurent ring
landing can send generator and inverse to that one-sided pair.

Fixed-star descent is now minimal and cross-route exact. For `chi=chi_p(rho)`, positivity of any
matrix with literal off-diagonals `chi,chi^(-1)` forces `star chi=chi^(-1)` regardless of both
diagonal masses; this is equivalent to canonical unit-diagonal positivity, integral Gamma
reporter, critical placement, and unit self-pairing of the same Xi coordinate in CCM/Weil form.
The unconditional modular receiver instead changes inverse coefficient by unique source-derived
weight `Delta=|chi|^2`; it is always positive and therefore cannot supply fixed-star descent.

Gamma-six provides a second exact formulation of same wall. At true source-selected abscissa its
filtered boundary value and first jet are nonnegative and absolutely summable on every Xi fibre.
Second boundary jet factors into positive Gauss/Fisher terms, is comparable to `1/p` off neutral
grade, and is summable exactly at neutral grade. It is now literally the second complex derivative
of the coefficient-faithful translated Gamma-six source primitive at Xi-selected boundary, so no
independently fitted current remains. Universal second-jet control is RH. Missing regularity is
one prime-log graph derivative, not meromorphic continuation or coefficientwise `C^1` control.

The subsequent Wold--Jordan comparison closes this proposed producer negatively. Its nondecaying
carrier square is `A_q/p`; the Gamma Hessian is two-sided comparable to the same harmonic class.
Genuine normalized all-left Big-Witt rows converge to one singular vertical vector but their
physical readings are `A_q/p_a`, so continuous descent exists exactly when `A_q=0`. Lean frees
`A_q` to an arbitrary real parameter and proves the entire predicate is just `A=0`. All rows,
singular graph, one-leg trace, Gamma and Green--Stokes naturality remain defined at `A=1`, where
descent is false. The two-port secondary source character and every naturality-only repair in this
data class are therefore terminal; global RH equivalence is a pullback receiver.

The scoped retirement is now exact for arbitrary prime-labelled coefficients, not only the
reciprocal profile. For every `c : Nat.Primes -> R`, Lean proves

```text
PrimeLabelledActualSourceDescends c
  <-> exists z : R, forall a : N, c(nthPrimeSubtype(a)) = z.
```

Continuity forces every genuine normalized fixed-left row, all converging to the same singular
vector, to have the same reading. Conversely `z` times the continuous one-leg graph trace realizes
every constant profile. This is the sharp positive survivor: constants are exactly the descending
profiles. It eliminates every repair that merely changes the prime-dependent scalar coefficient
while retaining this completed carrier. It does **not** exclude a critical-scale finite-core map
that changes the carrier before completion or retains additional non-scalar incidence.

The Beurling sensitivity theorem explains the wall: this branch consumes reciprocal-scale `1/p`,
`1/(pq)`, or `Lambda(n)/n` data. Positive generalized-prime perturbations preserve such data
arbitrarily closely while creating an off-line zero once their abscissa exceeds `1/2`. A surviving
Route-L producer must be discontinuous in reciprocal-mass topology and retain `x^(1/2)`-scale
prime discrepancy or an equivalent source boundary invariant.

The operator-valued loophole is now closed at its natural Hilbert--Schmidt boundary. Lean proves
fixed-evaluation continuity of the canonical entire Hilbert--Carleman determinant `entireDet2`
under Hilbert--Schmidt convergence. Applying the explicit Beurling sequence shows that no
reciprocal-mass-continuous Hilbert--Schmidt kernel assignment can encode every selected off-line
zero at one normalized spectral coordinate while keeping the base determinant nonzero there.
Thus “replace the scalar by an operator” does not evade retirement unless the construction proves
an arithmetic discontinuity, changes target ideal, or abandons fixed-coordinate coefficient
faithfulness. Evidence: `HTGeometry/EntireDet2HilbertSchmidtContinuity.lean` and
`RHTower/BeurlingReciprocalOperatorFirewall.lean`.

**Open core.** Construct the arithmetic Calderón Green intermediate extension before Hilbert
completion: prove its total arithmetic Cauchy relation is closed Lagrangian, its harmonic
complement realizes the nuclear quotient faithfully, and its Hodge comparison is cup-isometric
and strict on every multiplicity jet. Prime-periodic packets, archimedean conormal jets, and the
critical-scale source current must remain distinct. Same-fibre fixed-star, Wold--Jordan singular
descent, summable `1/p` Gamma-Hessian alternatives, and arbitrary nonconstant prime-labelled scalar
descent on the existing one-leg graph are terminal receivers, not open producers.

**Principal Lean evidence.** Completed-Green/Calderón--Witt/Burnol comparison modules;
Big-Witt Frobenius/Calkin/singular-graph descent modules; Gamma-six Wold--Jordan/Meyer--Tate
transport modules; `FrankensteinMeyerHalfDensityL2KoszulDescent.lean`;
`FrankensteinXiGreenStokesQuadraticGhostNormalForm.lean`;
`SourceHorizontalGammaSixCovariantStokesFlat.lean`;
`SourceHorizontalGammaSixPositiveStarUntwisting.lean`; and
`SourceHorizontalGammaSixMeyerModularUntwisting.lean`;
`XiSelectedBilateralPositiveSourceReceiver.lean`; `XiFixedStarWeilAtomDescent.lean`;
`XiGammaSixCurvaturePrimeTraceWeld.lean`; `XiGammaSixFilteredBoundaryControl.lean`;
`XiGammaSixWoldJordanHessianDomination.lean`;
`XiGammaSixWoldJordanSingularSourceDescent.lean`; and
`XiGammaSixWoldJordanParametricVacuity.lean`.

### Route O — Connes restricted-Weil/prolate ground space

**Endpoint.** Let `epsilon_lambda` be true restricted-Weil ground floor. Floors are antitone; one
negative trial pins all later floors below fixed negative value. Therefore nonnegative cofinal
floor, or convergence `epsilon_(lambda_j)->0` on one cofinal nested family, implies RH.

**Architecture.** Explicit constrained prolate source supplies Rayleigh value `r_lambda>0`
eventually with `r_lambda->0`; Rayleigh--Ritz still gives only `epsilon_lambda<=r_lambda`.
The prolate side is no longer missing spectral indexing. Lean proves every positive-aperture even
signed rung is live and simple, squared band values are globally strictly decreasing, separation
constants globally strictly ordered, all rungs have exact small-aperture power laws and moment-flag
limits, every fixed rung converges to its exact even oscillator level, moving bounded oscillator
energy locks the mode index, and sufficiently large subunit ground is uniquely canonical index
zero. Thus cross-spectral ordering, cofinal branch-index retention for bounded-energy families,
and canonical prolate ground selection are closed.

The literal restricted-Weil form has an exact compact self-adjoint Birman--Schwinger model on the
complete Gamma form domain. At zero energy it is `I-K_a`; a reducing finite peripheral block and
strictly coercive exterior have zero mixed form. Whole positivity is exactly positivity on that
block, equivalently absence of above-one dangerous spectrum.

The reduction is now source-aligned and arbitrarily accurate. Exact factorization through physical
Gamma--Slepian aperture mass gives a source-relative lower bound. For every `delta>0`, Lean selects
a finite peripheral Gamma--Slepian head and coercive exterior such that the full form is bounded
below by its head compression minus `delta` times the projected head norm. Every nonzero
nonpositive direction has nonzero head projection and forces, on that finite vector,

```text
(1-delta)||h||^2 + scalar-Gamma(h) + polar(h) <= finite-von-Mangoldt(h).
```

Thus a negative direction cannot hide in an ill-conditioned source projection, and neither a
fixed quarter-loss nor generic compactness is the frontier. Scientific open core is the opposite
source theorem: exclude this literal finite-prime overcompensation on accuracy-selected heads
cofinally as aperture and head dimension grow.

Ground selection itself is now closed. The exact restricted-Weil ground satisfies an adjoint-
forcing equation using its literal scalar, polar, and finite-prime terms. At accuracy
`(n+1)^(-1)`, Lean projects that exact ground onto a canonical finite peripheral Gamma--Slepian
head and proves form-norm convergence with one cutoff factor and physical-mass convergence with
the squared cutoff. This construction assumes neither RH, ground simplicity, parity, nor a
replacement prolate operator. The required finite-head sign theorem may therefore be targeted on
this canonical sequence; an exhaustive classification of arbitrary near-ground directions is no
longer the first open theorem.

Unit-Riesz/HG work remains a guardrail. Shift codiagonal plus one outgoing boundary coordinate
gives lawful completed carrier, and three bulk samples reconstruct its charge. Uniform scalar pole
domination is exactly RH, so it cannot be imported. Any comparison must act before scalar outgoing
projection and control finite dangerous block in source graph norm with signed polar channel intact.

**Established structure.** Finite restricted-Weil matrix, reflection, real-rooted completion,
nested-floor monotonicity/no-evacuation, true Friedrichs ground attainment and continuity,
small-aperture asymptotic, limiting-core modulus irreducibility, abstract prolate ladder algebra,
and sharp Gaussian trial are closed. Compact band operator is injective, so zero
eigenspace and zero band
component vanish. For every `c>0`, Lean selects a nonzero even joint band/prolate mode with
oscillator-scale separation `mu_c=c s_c<1`; every live nonzero band eigenvalue has multiplicity at
most one. A boundary-free aperture virial identity gives the
sharp lower bound `c<=mu_c(c+3)`, hence one selected family satisfies `mu_c->1`. The same theorem
controls normalized Gaussian defect `c x Psi_c+(1-x^2)Psi_c'` by
`(mu_c-1)+3mu_c/c`, which tends to zero. No eigenfunction asymptotics, window averaging, or
oscillator spectral theorem enters this ground-mode pin. From this mode corpus
constructs explicit even compactly supported mean-zero source, proves bounded variation, sums every
radial channel from common left endpoint, and obtains unconditional primitive and polar-charge
bounds, including `O(1/lambda)` polar charge. The four constraint targets are identified with
actual origin values of normalized self-dual Hermite modes `h_0,h_2,h_4,h_6`; in particular, CCM
seed weights are exactly `h_0` and `h_4` origin values. This closes analytic normalization and
target identification. The exact theta/Xi normalization extends to a source-specific two-channel
aperture metric: its determinant is a positive scalar multiple of strict Xi moment variance and
its normalized Schur coefficient is positive under that displayed variance hypothesis. This is a
finite target metric, not whole-ground coercivity. For actual constrained two-mode PSWF source, Lean now
proves fixed off-diagonal radial Gram entries vanish, diagonal entries converge to exact arcsine
spectrum `8/(11 pi k) arcsin(1/k)`, diagonal is uniformly `O(k^-2)`, and divisor-weighted diagonal
series converges to negative constrained-prolate prime constant. High-radial tail, Poisson center,
lattice/channel transport, and diagonal physical-PSWF realization are closed.

Countable log-chirp and endpoint modules isolate universal leading archimedean scalar law, including
endpoint constant `8*pi/33`; scalar identity renormalization leaves Rayleigh excess/gap ratio
unchanged. This prices exact closed-Weil remainder cancellation but cannot provide ground lower
bound. It strengthens seed comparison, not RH-bearing whole-ground control.

Generic first-derivative nonstationary-phase test is formal: a phase-speed lower bound `m>0`
controls bare oscillatory integral by `1/c` times endpoint/variation terms with costs `m^-1` and
`m^-2`. Actual radial prolate phase now supplies uniform separation: for `j>=k>=2`, difference
speed is at least `(2/3)(j-k)` and sum speed at least `j+k`, uniformly in radius and admissible
turning parameter. Lean now also proves exact interaction-picture two-branch decomposition,
Grönwall control of total amplitude, total amplitude variation one bandwidth power smaller, the
half-power symbol-class product bound, and the resulting two-index off-diagonal integral with
explicit `(j-k)^-1` and `(j-k)^-2` costs. Remaining certification debt is narrower: instantiate
these symbol records for the concrete normalized PSWF modes with uniform index constants. Generic
high-row theory already sums weighted radial rows and proves the shifted logarithmic tail tends to
zero; abstract head-plus-three-errors assembly then closes once literal source dictionary is
supplied.

Band-endpoint comparison is now explicit. Lean constructs Liouville phase
`Xi_s(y)=integral_y^1 sqrt((t^2-s)/(1-t^2))dt`, its sharp square-root endpoint envelope, and exact
modified-Bessel model `I_0(c Xi_s)`. True band equation and model share first-order and aperture
terms; their difference is an aperture-free comparison defect whose apparent double poles cancel
to one simple pole. Positive integrating weight `Xi/P` vanishes linearly at endpoint, converts
defect to bounded Wronskian density, and satisfies exact drift transport differential identity.
Generic Volterra contraction converts comparison mass `<1` into uniform relative control, and the
actual endpoint-normalized prolate band solution now satisfies the resulting two-sided estimate

```text
(1/3) I_0(c Xi_s(y)) <= Phi(y) <= 3 I_0(c Xi_s(y))
```

through a fixed absolute collar. Its amplitude ratio tends to one at the endpoint. The elementary
lower bound `exp(z)/(2*pi*sqrt(z))<=I_0(z)` and the collar/WKB ratio theorem then give sharp
exponential action with only square-root aperture overhead and no mode-index loss. Under the
literal positivity, interior-mass, and normalization hypotheses, Lean assembles the corresponding
`C c exp(-2c Xi_s(y_0))` leakage estimate. Model selection, indexed-mode boundary matching, and
analytic leakage barrier are therefore closed. Remaining work is actual-family uniform
normalization/positivity where required for radial source estimates; spectral ordering is closed.

The barrier is now two-sided at the same WKB action. Lean transports endpoint amplitude through
the band, proves a sharp aperture-mass upper bound without the former turning-layer loss, derives
a positive Bessel energy floor and exterior-mass lower bound, and matches the leakage upper bound
with a sharp lower law. A complementary interior-window lower bound is also formal at the current
cutoff. Oscillator-ladder pairing, derivative transfer to Hermite weights, and every fixed-rung
Hermite window limit are exact. These statements are conditional only through their displayed
mode positivity, normalization, and eigen-equation hypotheses; unresolved step is uniform
instantiation for actual indexed PSWF family, not ordering or another seed asymptotic.

Limiting radial first-row phase geometry is now exact. Bulk difference phase has critical point
`r=1/k` with curvature `-(k^2-1)/k`; endpoint Weber phase is nonstationary. Under supplied uniform
row estimate `|M_k|<=C/(sqrt(c)k^2)`, full logarithmically weighted row is `O(c^-1/2)` by convergent
`sum log(k)/k^2`. Dunster/Bessel symbol realization, stationary-phase estimate, and actual Weber
transform remain outside Lean statement, so this narrows dictionary work without closing it.
Exact first-row reduction is now formal too: raw finite prime charge splits into diagonal,
first-row, and `j,k>=2` sectors; truncated finite-aperture von Mangoldt charge is nonnegative and
bounded by `log k`; limiting difference phase has unique coalescing stationary point
`sqrt(1+1/k^2)` with curvature `-(k^3-1/k)` and endpoint distance asymptotic `1/(2k^2)`. This
pinpoints remaining literal Dunster expansion, phase-preserving Gram bound, stationary-phase
estimate, and Weber--Abel transform. Evidence is `CCMRadialPrimeFirstRow.lean`.

Corpus also changes shape of ground problem. Exact global defect-mass transport shows old outer
coordinate `r=lambda^2(x-1)` carries no limiting mass. Exact two-mode exterior energy shows
endpoint slope lives at scale `lambda^3`, total mass at scale `lambda`, and their ratio is
`lambda^2`. A one-scale near-ground normal form is therefore incomplete. Independent profile
modules derive global profile/derivative decay, oscillator ladder pin

```text
(mu-(2n+1)) <u,phi_n> = <D,phi_n>,
```

transfer unknown profile derivatives onto explicit Hermite weights, and show nonzero centre
pairing pins limiting ladder distance to zero when its convergence hypotheses are supplied.

The limiting ODE classification itself is now closed without spectral-theorem or assumed-decay
shortcuts: every nontrivial real solution of `v''=(x^2-mu)v` with integrable square has
`mu=2n+1` for some natural `n`. Energy/product monotonicity, recessive limits, boundary vanishing,
lowering identity, and spectral rigidity are Lean-proved. Rescaled prolate coefficients have exact
oscillator normal form and uniform fixed-window errors. For a genuine smooth nonzero even joint
band/prolate eigenmode, Lean now proves nonzero centre, normalization `u(0)=1`, `u'(0)=0`, and the
exact rescaled ODE. The explicit Gaussian comparator then gives pointwise convergence on every
fixed window from `mu_c->1` and `c->infinity`. A uniform phase bound is derived from the ODE;
evenness gives quantitative Gaussian window mass. Aperture virial supplies the uniform second
moment, Chebyshev squeeze proves normalized total mass tends to `sqrt(pi)`, and exact rescaling gives
`sqrt(pi/c)*Phi_c(0)^2/integral Phi_c^2 -> 1`. Unknown-profile compactness and global dominated
convergence are no longer required. Fixed-rung Hermite trial assembly is now Lean-proved: every
fixed finite even trial family is eventually positive, its band classes are linearly independent,
and at least `j+1` joint even modes lie below separation threshold `(4j+1+epsilon)c`. The
complementary lower-counting mechanism is also exact: window masses and cross-pairings converge,
every integrable even limit is an even oscillator rung, orthogonal prolate families have distinct
limits, and `j+1` such limits cannot all lie below `4j+1`. Remaining work is to instantiate uniform
normalization, mass, pairing, and subsequential convergence for actual indexed eigenfamilies and
identify oscillator rung with global prolate mode index.

Endpoint jets cannot replace that work. Exact prolate endpoint logarithmic derivative has leading
scale `-2*pi^2*lambda^3+kappa/(2*lambda)`, while the second/first jet ratio grows at least like
`pi*lambda^2-O(1)`. No fixed endpoint-jet truncation is cofinal. A valid boundary channel must
retain a resummed endpoint carrier inside the two-scale whole-ground classification.

`HTGeometry/OscillatorMassNoEscape.lean` adds exact tightness adapter: unit nonnegative Hermite
mass with uniform first oscillator moment cannot escape to high ladder indices; if every other
fixed coefficient vanishes, selected coefficient tends to one. `HermiteCoefficientPin.lean`
combines this with ladder equation: bounded defect pairing, escaping bandwidth, ladder convergence,
unit mass, and uniform oscillator energy force every off-rung coefficient to zero and selected
coefficient square to one. Route O must still derive those bounds and pins uniformly from literal
restricted-Weil near-ground equation; generic saturation is no whole-ground classification.
`SecondMomentIntegralTail.lean` adds far-field bridge: uniform second moment makes every
tail integral `O(K^-1/2)`, permitting integral passage from local/norm convergence once literal
family supplies hypotheses. `ProlateTailIntegralBound.lean` now discharges that uniform tail for
the actual normalized prolate profiles, and the growing-window transfer theorem assembles local
profile convergence with both tails. `ProlateWindowProfileDistance.lean` supplies the unsquared
full-window bound and `ProlateProfileIntegralLimit.lean` the Gaussian target/reflection transfer.
`ProlateGroundProfileIntegral.lean` performs the actual-family substitution and proves convergence
of the natural-window profile integral to `sqrt(2*pi)`; the normalization-free ground shape ratio
therefore tends to `2 sqrt(pi)`. The abstract secular-root theorem converts convergent selected
coordinate, tail, and gap data into exact limiting ratio `A/(A+B)`. Ground-coordinate and secular
landing are closed. Higher source coordinates still need uniform radial estimates, while actual
indexed-family ordering is now closed independently.

The constrained clock is now unconditional. True signed prolate leakages themselves form
`LadderEnvelope`s in both Fourier parity sectors; hence exact secular eigenpairs, all earlier
raw-defect collapse, depth-vector limits, and adjacent ratios need no supplied envelope. Lean proves
positive-sector ground/gap ratios `8/11` and `3/11`, negative-sector ratios `8/13` and `5/13`,
leakage-normalized parity collapse, and every eventual spectral gap below `3/11`. Common-clock
assembly is closed. These ladder laws select constrained prolate sectors; they do not compare the
literal prime compression with Gamma plus polar energy on an arbitrary finite source head.

The clock now controls vectors, not only eigenvalues. In both signed parity sectors the exact
constrained ground eigenvector converges in `ell2`, up to sign, to the normalized two-mode seed
built from its own first two constraint coordinates. Exact leakage mass identities, matching sharp
interior/exterior mass ratios, a nonzero Hermite anchor, and same-action collar/barrier ratios close
the remaining local prolate normalization and WKB-scale questions. These theorems identify the
seed geometry; they do not sign the finite von-Mangoldt term on the exact restricted-Weil ground.

The optional determinant landing now has a sharp rate gate. Mellin evaluation on
`[lambda^(-1),lambda]` has squared norm `sinh(2a log lambda)/a` at strip height `a`, hence grows
like `lambda^(2a)`; restricting to even sources removes no power. Therefore ordinary `o(1)`
ground-vector convergence cannot yield locally uniform determinant convergence. One needs
`lambda^a ||xi_lambda-k_lambda||_2 -> 0` for every `a<1/2`; at form level it suffices that
`lambda^(2a)(r_lambda-epsilon_lambda)/Gap_lambda -> 0`, with `O(lambda^-1)` a convenient uniform
rate. This is a sharp transfer requirement, not a new positivity mechanism, and it becomes relevant
only after whole-ground selection and a target gap are proved.

**Open core.** Prove the reverse arithmetic inequality on the canonical cofinal ground-head
sequence: literal finite von-Mangoldt compression must not exceed identity plus scalar-Gamma and
polar energy by the vanishing head error. Passing this sign to exact ground gives
`epsilon_lambda>=0`; equivalently it is enough to prove `epsilon_(lambda_j)->0` or
`r_lambda-epsilon_lambda->0` on one cofinal nested family. Antitone floors prevent a negative
direction from evacuating. Ground selection, profile exhaustion, conditioning, common clocks,
construction, ordering, and another seed asymptotic are closed.

Additional seed asymptotics, finite real-zero determinants, or renamed ground comparisons do not
control true floor.

**Principal Lean evidence.** Restricted-Weil/Friedrichs modules; radial PSWF/Weber assembly;
prolate endpoint/leakage and oscillator-ladder modules; actual ground-profile/secular modules;
`ProlateIndexedJointSpectrum.lean`, `ProlateIndexedSeparationOrder.lean`,
`ProlateCanonicalOscillatorLower.lean`, `ProlateOscillatorIndexProperness.lean`,
`ProlateCanonicalGroundMode.lean`, `ProlateSmallApertureEvenFullIndex.lean`,
`CCMRestrictedWeilActualBirmanSchwinger.lean`,
`CCMRestrictedWeilGammaSlepianDecomposition.lean`,
`CCMRestrictedWeilGammaSlepianStrictSource.lean`,
`CCMRestrictedWeilReducingFiniteBlock.lean`,
`CCMRestrictedWeilOneSidedFiniteBlock.lean`, and
`CCMRestrictedWeilExactFiniteSchur.lean`,
`CCMRestrictedWeilSourceAlignedFiniteBlock.lean`, and
`CCMRestrictedWeilSourceAlignedArbitraryAccuracy.lean`,
`CCMRestrictedWeilCanonicalGroundHeadConvergence.lean`; plus `ProlateIndexedProfileRungLimit.lean`,
`ProlateConstraintCoordinateLimit.lean`, `ProlateIndexedLeakageTwoSided.lean`,
`ProlateSignedLadderEnvelope.lean`, `ProlateNegativeSectorLadder.lean`, `ProlateGroundDistance.lean`,
`ProlateLeakageMassIdentity.lean`, `ProlateSharpMassRatio.lean`, `ProlateAnchorComparison.lean`, and
`ProlateBarrierRatioSharp.lean`.

### Route P — primitive cubic Euler/Burnol trace

**Endpoint.** Every strict-right Xi zero contributes at least one indivisible cubic conormal charge,
while entire primitive Euler source has total trace budget below that charge. Completed trace
contraction therefore excludes all strict-right zeros and proves RH.

**Architecture.** Primitive Euler cells `(p,e)` carry resolved von-Mangoldt amplitude and cubic
Cauchy Gram. P-G181 base cube is PSD with total budget `<2`; P-G182 identifies target feature as
normalized completed-Xi conormal residue; P-G183 resolves multiplicity; P-G184 identifies budget
with balanced Euler codiagonal; P-G185 proves exact joint damping wall `s>=0`; P-G186 constructs
inverse-Burnol-window features whose entire finite-aperture Gram is exactly base cube before zeros;
P-G187 identifies `s=2c` as energy time of a contractive weighted-aperture semigroup and proves
that every negative time creates a nonintegrable boundary pole on an explicit finite-energy datum;
P-G188 constructs the two explicit positive defect channels--deleted boundary interval and tail
cocycle--and proves exact transported-plus-defect conservation of the full primitive budget.
P-G189 proves the hard-edge channel is first-order flat, concentrates the complete opening flux in
the tail cocycle, computes its summable arithmetic density, and proves every Hilbert realization
of that channel has intrinsic square-root rather than differentiable boundary scale. P-G190--P-G194
close critical Gamma-sewn Green threshold, classify finite-aperture hidden budget, and construct
matrix-complete source colligation. P-G195/P-G196 exclude constant and aperture-intertwining
landings and isolate mandatory commutator anomaly. P-G197 constructs actual positive Xi
Ward--Herglotz tangent; P-G198 excludes cross-mode polarization; P-G199 identifies exact common
radial generator from resolved Ward columns to cubic source/target conormal columns and proves its
strict-right graph amplification is unbounded. P-G200 canonically quarter-turns each actual
primitive mode into Deninger's strict source sector and identifies its coefficient-weighted
generated reporter with the forced negative square of the reflected source Cauchy evaluation.
P-G201 constructs each such square as the strong `ell^2` limit of explicit zero-independent
two-atom upper source secants and proves their raw coefficients diverge exactly linearly. P-G202
classifies the canonical two-leg Hodge diagonal as phase-unstable, constructs explicit conjugate
lower secants, and proves their four-leg completion is exactly the full upper graph Gram at every
finite matrix level. P-G203 proves that collapsing the positive fourth leg back onto the original
upper squared-Cauchy graph, for any fixed nonzero amplitude and upper pole, is equivalent to RH.
P-G204 keeps their difference, proves it is a pure reflection-odd negative Weil channel, and
constructs explicit finite mixed upper/conjugate-lower source secants converging to it. P-G205
classifies every finite stage: conjugate-lower leg is exact line reflection of upper leg, raw Weil
energy is `-||d_n||^2`, and adding twice amplitude-weighted positive fundamental-symmetry gap gives
zero identically.

**Established structure.** Arbitrary ordinate clusters are PSD with spacing-free trace. Source
summability, depth-square contraction, source-window formation, Burnol target support, and
multiplicity accounting are closed. P-G185's arithmetic wall and P-G186's source Gram are now one
unilateral semigroup wall at `L=0`. Cubic Green test in CCM maps every critical prime atom to same
base mass and writes pole–prime completion as polar surplus minus truncated `<2` budget. P-G188
shows that the semigroup loss is not merely an abstract deficit: it factors through source-defined
positive channels whose total mass remains inside that same `<2` budget.
P-G189 upgrades finite-time conservation to a global infinitesimal law: differentiation commutes
with the full primitive sum and yields the trace-finite current
`J(p,e)=1/[2 p log(p)] p^(-e)(e+1)^(-2)`. The later Ward analysis shows cubic landing is a
source-selected graph-domain problem: generated cross-Gram is exact cubic Cauchy kernel, but
generator/base energy ratio `1/(2a^2)` is unbounded at centered rate wall.
The same P-G189 coefficient is now identified atomwise with the strictly positive dressing
`log(n)/(64 sqrt(n))` of CCM's literal prime-entry cubic jet. Thus P's square-root boundary current
and CCM's first centered transverse clock direction are one coefficient-faithful source channel,
not two independent producers.
A two-sheet Gamma-six singular carrier closes next local obstruction. One scalar graph trace kills
centered zero-mass clock direction; reflected graph pair instead separates mass and orientation
traces. Antisymmetric actual-Gamma packets have mass zero and orientation one at every finite stage,
disappear in ambient `ell^2`, and converge in graph norm to nonzero vertical orientation class.
Scaling by each P-G189 coefficient preserves prime/depth label. Orientation reader is exact
P-tail/CCM third-jet matrix, while actual-Gamma transport is same coefficient times fixed Sonin
horizontal detector and vanishes iff horizontal grade is zero. Active
`FrankensteinRoutePCCMGammaSixMeyerTateSourceBridge.lean` removes remaining local provenance
ambiguity: each finite P-tail cell is literally produced from ordinary-prime rational-adelic CCM
degree-one atom, completed Meyer--Tate differential, and two-sheet anti-lift; it converges to
retained horizontal class and has exact P-tail physical readout at every stage. This constructs
source-derived moment-neutral pre-scalar handoff; it does not sum full source within `<2` budget or
prove arithmetic Stokes annihilation.
P-G200 additionally closes object identity with the polar--Gamma source: every actual primitive
Burnol generated column is its resolved von Mangoldt amplitude times a canonical Deninger
negative Cauchy square. What remains is the sign and budget of the finite source quadratic form,
not identification of its columns.
P-G201 closes source-domain membership: those squares lie in the strong completion of explicit
prime--Gamma packets, but only through linearly divergent coefficients. Remaining issue is the
source-derived Hodge/shorting map turning this upper graph completion into the positive lower/upper
energy required by W-H184. P-G202 closes the sign half of that issue: the natural two-leg cup
reverses under phase `i`, while the minimal four-leg completion supplies exact Hilbert energy and
matrix-complete graph Gram. It deliberately leaves the full graph energy unchanged. P-G203 then
shows the four-leg distinction stores exactly the off-critical displacement: equality of fourth
and original upper graph legs is RH-equivalent, with no alternative resonance inside upper-pole
geometry. P-G204 makes that displacement finite-source visible: `not RH` forces an explicit mixed
prime--Gamma secant packet with negative Weil energy and is equivalent to those source energies
converging to a strictly negative limit.

P-G205 makes finite sign exact rather than asymptotic. At every index, finite mixed packet is
reflection-odd part of one upper secant and equals amplitude times conjugated lower pair
difference. Its raw Weil energy is unconditionally nonpositive. For every nonzero amplitude,
packet vanishing, energy nonnegativity, and zero fundamental-symmetry gap at any single index are
each equivalent to RH; under `not RH`, every index is strictly negative. Exact augmented law is

```text
raw finite Weil energy + 2 |A|^2 (fundamental-symmetry gap) = 0.
```

Thus raw finite passivity is a terminal receiver, while positive correction is exact object a
source completion must retain and control.

The fixed-secant capacity shortcut is now formally closed. Every phase-matched strict-Euler
lower secant detects horizontal displacement, but its reflection energy vanishes quadratically as
the zero approaches the critical line, while cubic Hellinger self-charge has inverse-cubic scale;
no scalar multiple uniformly dominates the latter by the former. The sharp survivor is an
adaptive coalescent secant at doubled horizontal rate `lambda=2a`: after multiplication by
half-density and universal factor `345/2048`, its squared reflection defect equals the cubic
Hellinger self-charge exactly. For `a<=1/4`, however, `2a` is below every primitive Euler
frequency. This rate must be generated collectively by the completed pre-divisor bichamber
current; it cannot be selected from one Euler cell after divisor formation.

There is now also an exact source-side information law for the base cubic carrier. For positive
primitive rates `a,b`, its normalized Schur/Pluecker defect is the cubic transform
`Delta_3=chi(3-3chi+chi^2)` of balanced Route-E load chi-square
`chi=((a-b)/(a+b))^2`, and `chi<=Delta_3<=3chi`. Twice iterating the primitive depth-square map
gives a canonical rate-four partner and exact unit-diagonal ratio `11529/62500`. This proves
quantitative source separation and supplies SP-E's first viable unit-diagonal local metric block.
The source-faithful audit is negative and exact: two coefficient-preserving depth-square steps
contract transported cubic diagonal by `1/64`, so actual pair ratio is
`737856/66015625 < 13/98 < 1/6`. Restoring balance uniquely requires extra nonnegative amplitude
`8` and incurs trace debt `63w/64`. Completed four-leg shorting must produce and pay this exact
Radon--Nikodym correction inside global `<2` budget.

Scalar coherent restriction is now excluded even abstractly: PSD Gram of columns `[1,-1]` has
trace two and coherent sum zero, so no universal trace-to-squared-sum inequality exists. Genuine
finite Loewner domination avoids this cancellation and implies required conormal trace bound, but
the universal matrix-complete boundary-restriction law is itself equivalent to RH. It is exact
receiver specification, not permissible producer premise.

Inserting the unconditional Weil fundamental symmetry does not repair the sign seam. For every
square-summable test, positive `J`-energy minus ordinary Weil diagonal is exactly half the
reflection-difference energy. For one fixed nondegenerate lower-Euler Cauchy secant this gap
vanishes iff RH and is strictly positive under `not RH`. Identifying those metrics is therefore an
RH receiver; a completion must retain and bound the gap one-sidedly.

The formerly missing correction is now source-realized. Restoring depleted energy `w/64` uniquely
forces a negative pivot `-w`, cross term `(sqrt 63/8)w`, and determinant `-w^2`. The Julia defect of
the quarter-scale co-Poisson contraction produces exactly these coefficients on Burnol's actual
even carrier; Gamma cyclic amplitude equals the same defect. The construction tensorizes over the
entire finite P-G186 Gram as universal `2x2` Krein block tensor source Gram, retaining every
off-diagonal prime/depth incidence. Literal source and co-source are not scalar-intertwined: exact
survivor is `source(p,e)=log(p) coSource(p,e)`, so completion carries a prime-log diagonal.

That diagonal exposes the unique cofinal obstruction: depth-zero trace is exactly `1/(4p)` and
therefore not trace class. The aperture Radon--Nikodym multiplier transports this face labelwise
into the oriented Stokes first trace; positive depths are summable and the polar/Gamma
countercurrent cancels the wall residue. Physical pivot ratio tends to one and is eventually
positive, so every finite physical pencil is stable. Cofinal child kernel and its Hellinger
completion are Hilbert--Schmidt and self-adjoint, finite sections converge to an entire `det₂`, all
its zeros are real, and its diagonal sum is exactly the completed prime--Gamma current. Local
correction provenance, cofinal operator assembly, finite stability, and regularized determinant
are therefore closed.

Transported child is now stronger than Hilbert--Schmidt. Every finite principal block is an actual
positive aperture-conjugated Burnol Gram; zero-padded sections converge in operator norm, so full
child is positive. Exact Stokes diagonal is summable, hence child is Schatten-one with ordinary
trace equal oriented Stokes current. Finite Hellinger channel preserves trace class. Its ordinary
determinant is trace-restored from `det2`, and literal finite determinants converge locally
uniformly for every fixed aperture. At balanced wall the channel square is `64I`; determinant is
even and reduces to positive child-square determinant. Raw prime-log face remains nonnuclear, but
source-faithful aperture transport restores ordinary trace without deleting cross-prime incidence.

The singular wall has now been resolved through quadratic order. Normalized valuation-one wall
coordinates converge weakly to the unit exponential clock; cubic coherence has exact mean
`16/35`. Consequently child Hilbert--Schmidt energy converges to `256/35`, with a positive
uniform floor already at finite apertures. Pulling the wall law back by its quantile map gives
fixed-carrier `L2` convergence of the full cubic kernel, so the limit is not an artifact of mass
escaping in moving coordinates. The balanced physical determinant retains this law in its square
coordinate: its wall jet converges to `-64 E(d)` and is eventually bounded away from zero. Thus
wall noncollapse and nontrivial quadratic determinant retention are Lean-proved.

The whole wall passage is now closed for the literal physical child. Exact diagonal congruence
identifies every ordered-prime physical coefficient with `S_d^n` times normalized wall coefficient;
one Hadamard majorant gives locally uniform convergence on every closed disc at forced scaling
`z -> 4z`. Cofinal finite sections and balanced products transfer real-rootedness to the
exponential-wall determinant. No tuple, repetition, order, or cross-prime incidence is discarded.

This closure exposes a terminal mismatch. Every ordinary trace-class Xi-divisor landing is
impossible because reciprocal centered Xi zeros are not absolutely summable. Lean now also builds
the strongest survivor rather than merely specifying it: literal prime-log density is square
summable but not summable; its forced balanced signed diagonal is self-adjoint Hilbert--Schmidt,
not Schatten-one; and its entire `det₂` vanishes exactly at the explicit symmetric real reciprocal
source multipliers. A source-native genus-one real-zero carrier therefore exists.

Direct divisor identification is now closed negatively. The source determinant has a forced zero
at `z=1`, whereas `XiC(1)` is nonzero; it is neither Xi nor normalized Xi, and no pointwise scalar
multiplier can repair it. The completed Ward budget also fails on the literal source before any
divisor identification: normalize the reciprocal-promotion co-source on depth-zero primes two and
three, couple it to the exact diagonal Gamma--Julia energy `c log p`, and take the rank-one Ward
commutator. Lean proves its energy is
`2 w_2(u) w_3(u) (E_2-E_3)^2`, strictly positive at `u=0`, while
`8(1-exp(-u)) -> 0`. Hence the completed eight-unit budget is eventually smaller. This excludes
every coefficient-faithful Ward comparison hereditary/nonexpansive under that two-cell source
compression. Evidence: `RoutePPrimitiveGammaJuliaTwoPrimeWardBudgetNoGo.lean`.

The strongest survivor is now constructed rather than conjectured. Before finite packet selection,
canonical Gamma-sewn Julia transport supplies an all-prime-depth exterior coupling using both literal reciprocal-promotion amplitudes.
On the `(2,3)` packet its resolved source/environment block is a positive rank-one Gram, its source corner is exactly finite-aperture Ward energy, and its Schur short through the Julia pivot is zero.
As aperture tends to the lossless wall, compressed corner tends to strictly positive P-G205 energy, so short-then-compress is eventually strictly smaller than compression without environment.
P-G207 now transports this exact coupling through the literal completed Gamma/polar quadratic
source current. Separate pole gauges keep the environment pivot equal to one; iterated residues
retain the full coefficient and analytic-multiplicity product. Canonical legwise splitting is
performed before the divisor limits, giving one exact Julia-weighted conormal coordinate on every
actual Xi support-fibre copy. Same-support raw and split landings are Hermitian PSD rank-one blocks,
their short is zero, codiagonals recover raw residues, and split corner energy is linear in
multiplicity.

**Open core.** Completed-source compatibility and coefficient/multiplicity-faithful divisor
identification are closed. The transport is kinematic, not annihilating: Lean proves a nonzero Xi
coordinate can coexist with the landed zero short. Next producer must be an independent
completed-source budget/order law comparing the positive split corner with a source quantity not
erased by the environment pivot, or the original non-spectral conormal contraction. Repeating
rank-one Schur transport is retired. Entire gauges, scalar counterterms, trace restoration, direct
`det₂` welding, and compression-monotone completed Ward budgets are dead. Alternative curvature
lane still needs a finite uniform high-tail ceiling.

More cluster estimates, seed/source-window construction, target support identification, scalar
capacity, or multiplicity normalization are closed work.

**Principal Lean evidence.** P-G174--P-G206 Burnol/Julia--Krein/Stokes modules;
`RoutePPrimitiveGammaJuliaLogPrimeHarmonicGenusOne.lean` constructs the genus-one carrier;
`RoutePPrimitiveGammaJuliaLogPrimeHarmonicXiDivisorNoGo.lean` proves its direct Xi and scalar-weld
no-go; `RoutePPrimitiveGammaJuliaWardPrecompressionShorting.lean` constructs the nonmonotone
precompression survivor; `RoutePPrimitiveGammaJuliaCompletedXiDivisorShorting.lean` proves the
two-sided residue-gauged raw and copywise divisor descent and its nonannihilation boundary;
completed conormal modules retain the non-spectral alternative.

### Route Q — theta–Cassini boundary saturation

**Endpoint.** Cassini inward saturation, source dominance, transverse-charge vanishing, and RH are
equivalent.

**Architecture.** Theta source supplies aperture-independent positive likelihood, finite positive
Hankel blocks, analytic boundary-to-seam continuation, and selected exponent. Absolute centered
moments obey height-damping recurrence, giving geometric `1/81` ratio from certified height floor.

**Closed negative result.** Selected continuous power-reciprocal carrier cannot satisfy all-degree
closure. Its pushforward has positive mass outside countable Xi thermal nodes, while any positive
all-degree witness is rigidly canonical atomic Xi measure. Continuous injective or strictly
monotone scalar transforms are therefore impossible.

**Closed plateau-existence result.** A measurable reporter from the literal theta law to the
canonical self-weighted Xi thermal measure now exists unconditionally.  It has positive-measure
fibres over every enumerated thermal atom and reproduces every positive thermal moment.  Its first
moment excess over the completed source is exactly the nonnegative thermal orientation energy, and
both zero excess and complete moment-witness status are equivalent to RH.  Thus arbitrary
positive-fibre plateau existence is kinematic and cannot be the missing producer.

**Closed monotone-plateau result.** The reporter can be chosen explicitly and nondecreasing:
compose the strictly increasing literal theta CDF with the generalized inverse of the normalized
compact Xi measure.  Lean proves this canonical quantile maps native theta mass exactly to the Xi
atomic measure, including all positive fibres and moments, while retaining the same nonnegative
RH-equivalent first-moment defect.  Thus even ambient one-dimensional source order and canonical
ordered plateau widths are kinematic.  Scalar rank is a gauge: CDF normalization erases the source
density before the target quantile is applied.

**Positive survivor.** Deeper corpus already makes the required rank-breaking incidence concrete.
The Cassini logarithmic response is welded to the inward theta boundary, the reflection defect is
welded to reciprocal-square adjoint response and first-prime/Hurwitz seams, and one unconditional
sequence of pairwise-separated finite continued-Cauchy prime--Gamma packets converges to the
orientation vector with source energies tending to minus the orientation energy.  Route Q now
needs only cofinal nonnegative recurrence for one such source sequence: for every cutoff, some
later packet has nonnegative source energy.  If RH is false, Lean proves every convergent separated
reconstruction is eventually trapped strictly below minus one half of the positive orientation
energy, independently of approximation choice.  Arithmetic packet separation, convergence, exact
energy reconstruction, and this universal negative-basin law are closed; source-defined recurrence
is not.  Merely being discontinuous, monotone, or quantile-canonical cannot work.

**Sharp cone geometry.** The asymptotic negative basin has an exact global metric form. Every
Weil-nonnegative vector, hence every source-nonnegative separated packet, has squared Hilbert
distance at least `xiHurwitzOrientationEnergy/2` from the orientation vector. The constant is
attained by a canonical zero-energy boundary vector obtained by balancing signed orientation with
its reflection-even absolute-coordinate companion. This equality witness is target-defined and
does not solve source recurrence; it proves abstract Hilbert geometry cannot improve the radius.

The equality locus is now classified beyond that canonical witness. For every reflection-even
vector with the same norm as the anti-fixed orientation vector, their balanced half-sum is an
exact closest zero-energy boundary point. In the Xi carrier, the absolute-coordinate companion and
its negative give two distinct exact points whenever orientation energy is positive. Lean proves
that uniqueness of the exact closest boundary point is equivalent to RH. Hence metric projection
cannot select the missing source packet: away from RH it forgets an entire fixed-sector phase, and
proving uniqueness abstractly would already contain the full RH conclusion.

Direct source-boundary saturation is now closed negatively in a stronger literal form. The
reflection-even absolute companion belongs to the continued prime--Gamma Cauchy Hilbert subspace,
so both exact boundary witnesses lie in closure of actual pairwise-separated finite packet
evaluations. If orientation energy `E` is positive, the two source-closure paths obtained by
increasing even amplitude by `t>0` have exact energy `(t+t^2)E`. Openness of the positive-energy
chamber and separated-packet density therefore produce genuine packets approaching both boundary
points with strictly positive exact source energies tending to zero. If `E=0`, both targets
collapse and empty packets suffice. Hence positive-side boundary incidence is unconditional even
off RH; it cannot select the missing orientation phase or replace cofinal recurrence toward the
anti-fixed vector.

The two boundary witnesses now have an exact joint classification. Writing them `b_+` and `b_-`,
Lean proves reflection exchanges them with a minus sign, each has squared norm `E/2`, and their
entire real span obeys

```text
Q(alpha b_+ + beta b_-) = -alpha beta E.
```

Thus off RH this span is a genuine hyperbolic plane: same-sign quadrant is exactly negative,
opposite-sign quadrant exactly positive, and two coordinate axes are complete null cone. This law
persists for arbitrary separated-packet reconstructions: same-sign scaled fusions are eventually
strictly negative and opposite-sign fusions eventually strictly positive, independently of their
diagonal packet energies. In particular `w=b_++b_-` lies in negative quadrant. Boundary
approximation has therefore exposed, rather than supplied, missing datum: any source-first selector
toward `w` must retain a transverse mixed-incidence compensation not measurable from two diagonal
source energies.

That compensation is now quantitatively classified. If `z` is real-orthogonal to both canonical
boundary axes, Lean proves

```text
Q(alpha b_+ + beta b_- + z) = -alpha beta E + Q(z),
4 alpha beta E + ||z-Jz||^2 <= ||z+Jz||^2
```

whenever fused source energy is nonnegative. Thus fixed transverse channel must pay full
hyperbolic defect plus every anti-fixed transverse contribution. Anti-fixed correction alone
strictly deepens false-RH orientation defect. Route Q needs a source-derived reflection-fixed
incidence budget, not arbitrary transverse norm.

Diagonal source budgets are now excluded sharply. For every pair of separated positive-side
packet reconstructions converging to the two null axes, their individual source energies tend to
zero but their polarized incidence converges to

```text
mixed(b_+,b_-) = -E/2.
```

Off RH this fixed negative term eventually dominates `C` times the geometric mean of the two
diagonal source energies for every prescribed `C>0`. Thus no Cauchy--Schwarz estimate using only
the two diagonal packet energies can control fusion. Missing reflection-fixed channel must be
present before diagonalization and transport signed mixed incidence itself; making each null axis
arbitrarily cheap does not approach target orientation law.

Complex scalar phases do not repair this failure. The complexified boundary plane has same two
coordinate axes as null rays; off RH every nonnegative complex-phase fusion must move its
coefficient pair a definite distance from target `(1,1)`, with sharp squared displacement equal to
one. Any adaptive complex coefficients tending to `(1,1)` along separated reconstructions are
eventually negative. Missing channel is therefore not an unchosen scalar phase but a genuine
reflection-fixed transverse source incidence.

The first candidate cross-route invariant is now exact. One line-conjugate off-line resolvent pair
has Poisson-difference profile with signed integral zero but quadratic frequency energy

```text
pi*y^2/(b*(b^2-y^2)),   0<y<b,
```

which diverges as probe height approaches transverse displacement. This explains why all signed
first-moment averages miss false-RH pairs while mixed incidence sees them. It opens a Q--U bridge:
construct before divisor reconstruction one finite arithmetic quadratic-concentration budget that
dominates both this profile and U's Christoffel wall. No such source budget or domination theorem
exists yet, so this is a candidate bridge, not an eleventh route.

Centered source-budget hierarchy has advanced one finite step: complete sixth reciprocal trace
equals `normalizedPrimeArchMoment 2`, and Lean now proves this moment strictly positive at the
functional-equation center term by term from the reciprocal-square sector bound. Consequently
every nonzero linear source test with same-sign coefficients has strictly positive Hankel value;
only the opposite-sign coefficient sector can contain unresolved first-minor failure. Any off-line
zero in the order-twenty-one residual annulus forces source charge strictly above `2/3050000`.
These are unconditional finite-degree sign/floor results, not annulus emptiness or all-degree
positivity; no matching source upper bound is yet proved. Lean now evaluates the same completed
second moment at `x=10`, proves it strictly negative by explicit rational Gamma/Euler bounds, and
therefore refutes global right-even polynomial factorization for `P=X`. Center and far-right signs
form an exact no-go, not Cassini saturation. Paper analysis gives a later positive region and four
reflected sign-changing crossings; that wider crossing package is not yet fully formal.

First Liouville/Gibbs atom now has exact obstruction-scale quadrature scaffolding. On each
`1/64` cell through `j<56`, Lean gives certified affine-exponential upper/lower density envelopes
and exact closed interval-mass formulas for every even power weight. This replaces numerical
quadrature at first-atom level, but no theorem yet sums certificates into missing global source
upper bound or Cassini saturation.

**Open core.** Produce nonnegative source energy at arbitrarily late indices along one unconditional
separated finite continued-Cauchy prime--Gamma reconstruction, equivalently the theta-specific
reverse Cassini--Jensen/jet boundary sign. Lean proves this cofinal recurrence gate is equivalent to
RH and strictly weaker than eventual nonnegativity: false RH traps every convergent reconstruction
a definite distance inside the negative source chamber. This is the concrete arithmetic-incidence law not measurable
from scalar theta rank, sharp target-space projection, or positive-side boundary saturation, all
of which retain both fixed-sector phases in literal separated-source closure. Exact boundary-plane
law rules out every same-sign fusion of independently reconstructed null rays off RH, while exact
transverse budget rules out unpolarized or anti-fixed compensation. Mixed-incidence limit further
rules out every repair controlled only by geometric mean of diagonal source energies.
The next lawful theorem must select packets cofinally toward the anti-fixed orientation vector from finite
theta/prime--Gamma source data before target closure. Paper-level verified
low-zero height floor `T>9` and signed first-moment comparison remain formal certification backlog,
but they do not revive retired continuous carrier, arbitrary measure-theoretic quantization, or
canonical monotone quantization.

**Principal Lean evidence.** Cassini/theta saturation modules,
`ThetaCuspCalibratedPowerReciprocalAllDegreeNoGo.lean`, and structural absolute-moment height-gate
modules, including `XiCenteredOrderTwentyOneSixthTraceFloor.lean` and
`PrimeArchThetaFirstAtomWardObstructionScaleQuadrature.lean`, together with
`CompletedPrimeGammaSecondMomentCenterPositive.lean` and
`PrimeArchThetaCanonicalPlateauQuantizerOrientationWall.lean`, and
`PrimeArchThetaCanonicalMonotonePlateauOrientationWall.lean`, together with
`XiSquaredSeamCassiniResolventSourceLaw.lean`,
`XiHurwitzOrientationSeparatedSourceReconstruction.lean`, and
`XiHurwitzOrientationUniversalityLaw.lean`, together with
`XiHurwitzOrientationCofinalSourceSignGate.lean` and
`XiHurwitzOrientationSharpNonnegativeConeDistance.lean`, and
`XiHurwitzOrientationExactBoundaryMultiplicity.lean`, together with
`XiHurwitzOrientationPositiveBoundarySourceSaturation.lean`,
`XiHurwitzOrientationBoundaryFusionObstruction.lean`, and
`XiHurwitzOrientationBoundaryHyperbolicPlane.lean`, together with
`XiHurwitzOrientationBoundaryTransverseCompensation.lean` and
`XiHurwitzOrientationBoundaryMixedIncidence.lean`,
`XiHurwitzOrientationBoundaryComplexPhaseWall.lean`, and
`PrimeArchConjugatePairQuadraticConcentration.lean`.

### Route T — mass-shifted critical outgoing current

**Endpoint.** Route T has two RH-closing receivers for the centered prime--Gamma current:
holomorphic first-order zeta ODE after Wold residual continuation and type-zero true-prime
Bessel-cone quadrature defect. Detector/Mellin is now an unconditional prime-supply producer feeding
the first lane, not an RH endpoint by itself.

**Established structure.** Literal primal, reflected dual, and confluent-pole AFE pieces give
global symmetric critical fourth moment; mollifier second moment and detector-error `4/3` moment
are closed. Gaussian window absorption upgrades these to uniform translated left endpoint, while
right endpoint has power-saving translated `L2` bound. Actual Gabriel interpolation at center
`699/1000` and polylog endpoint closure give exponent `82571/118590<7/10`; raw detector
logarithmic moment is closed.
Weighted Littlewood now allows zeros on left edge. Admissible horizontal slices, pole-gauge exact
cancellation, far-right nonvanishing, horizontal-tube argument variation, and complete selected
rectangle are all formal. Capstone gives analytic-multiplicity zero count in
`[7/10,4] x [-(X-2),X-2]` bounded by
`K X^(82571/118590)(1+log X)^2`.
Conservative Gabriel arithmetic closes numerical geometry: uniform exponent is at most
`(16/5)(1-sigma)`, leaving height margin `1/25` and density-to-short-ranges margin `1/80` at
`sigma=7/10`. This is interpolation budget, not prime-supply handoff.
Discrete Abel summation removes the earlier fixed-power loss from the exponentially smoothed
critical divisor carrier: weighted mass is `O(X(1+log X)^3)`, plain mass is
`O((1+log X)^4)`, and affine mean square has only those polylogarithmic coefficient prices,
uniformly in truncation. This closes the smoothed-divisor budget.
Exact approximate-functional-equation control now propagates those budgets to actual analytic
objects: dyadic and symmetric critical zeta fourth moments are `O(N(1+log N)^4)`, critical
mollifier second moment is `O(N(1+log N))`, and detector error `4/3` moment is
`O(N(1+log N)^2)`. Gaussian translation absorbs retained polylog endpoint loss uniformly. These
results remove moment-loss objection from detector deployment. Exponent room is closed.
Moving right edge itself now has exact `X^(-delta)` mean-square saving, conditional only on
explicit divisor-count envelope already used by interpolation; Gaussian translation preserves this
saving uniformly in ordinate.
Source-selected Gabriel dual datum is now algebraically configured on every
`7/10<=sigma<=1`: interior moment power lies in `[4/3,2]`, seed exponent is positive, and affine
dual exponent lands exactly on both strip endpoints. Lean now also constructs the analytic complex
power carrying a center datum across this moving strip, proves exact fourth-power left-boundary and
second-power right-boundary norm identities, and proves continuity through the zero datum. This
dual now pairs with a shifted field in a scalar integral family whose center value is exactly the
moving interior moment; Hölder gives the required `L^(4/3)` left-edge and `L^2` right-edge bounds.
This closes construction and endpoint bookkeeping of the Gabriel scalar family. Remaining analytic
work inside that standalone family is parameter-holomorphy/three-lines passage, but Route T's
fixed-gap detector density is already proved independently.

The density-to-weighted-zero and prime-supply steps are now closed unconditionally. Lean proves a uniform zero-free
edge, uniform `16/5` density with explicit gap-polynomial loss, and exact exponential layer cake.
At physical interval exponent `701/1000`, the multiplicity-weighted high-zero packet tends to zero
with exact slack `216/1495`; the low strip also tends to zero by the global Xi multiplicity bound,
so the complete common packet vanishes. Buffered Mellin kernels then give an absolutely summable
full exact-multiplicity Xi zero sum tending to zero. The adjacent-window Mellin source is entire,
admissible prime--archimedean contours approximate that sum, and the scheduled `Re(s)=-1/2` left
edge tends to zero. Lean now fixes vertical rectangle edges at `Re(s)=-1/2` and `Re(s)=2`, proves
both are residue-unit-zero-free, and at every large natural scale selects a nearby height whose
whole boundary is zero-free and whose boundary integral equals negative full zero packet. Route T
no longer lacks density-to-zero summation, contour selection, horizontals, or left-edge control.
The exact arithmetic weld makes literal von Mangoldt edge minus pole continuum plus complete zero
packet equal three synchronized error edges. Normalized physical von Mangoldt mass tends to one,
proper-prime-power leakage tends to zero, and prime theta mass eventually exceeds one quarter of
window width. Lean proves one threshold `X_0`, independent of upper-phase height exponent `mu`,
such that every Route-T window `(x,x+x^(1-1/mu)]` beyond it contains a prime: fixed exponent
`71/100` lies between density threshold `2/3` and every physical width. Consecutive gaps are at
most `p^0.71`, giving gap-square exponent `1.71`, still above Wold threshold `3/2`. Detector is a
completed unconditional unsigned prime producer, not RH producer.

The high-twist prime side is now an explicit theorem rather than an unexpanded contour plan.
Perron inversion, pole/no-pole shifts, quantitative edge bounds, uniform Route-T log-derivative
control, smoothing removal, and prime-power deletion give an unconditional displayed bound for
`sum_(p<=K) log(p) p^(-i tau)`. This is the weighted prime-twist input to the
Matomäki--Radziwiłł programme. Parameter collapse and Abel summation to `sum p^(-i tau)` remain;
the theorem does not imply Route T's signed Wold or Bessel cancellation.

The Maynard physical-slice branch is also coefficient-faithful. Finite-support Perron inversion
recuts each observed aggregate to the literal von Mangoldt slice before cell extraction, preserving
the normalized target-minus-reference sign. Local `Lambda(n)/n` energy retains additive interval
length and closes the lower physical phase; proper prime powers are negligible throughout the full
range. Uniform `0.71` Hoheisel supply deletes upper-window existence as an independent problem;
signed cancellation remains. More strongly, every sufficiently late polynomial-width
prime-free target below the physical reference now forces a literal signed defect on one adjacent
dyadic rung, with fixed positive margin divided by ladder length. This closes the inverse-log
adjacent-defect producer under the exact prime-free premise, but not the sub-`3/2` gap moment.
Localization and cell extraction are now exact at arbitrary Mellin order. The full aggregate recuts
to the physical slice; explicit low-frequency and order-`j` far-tail costs leave a positive
central/outer wing. Central and outer interval receivers either place it in the base layer or in a
separated dyadic superlevel with additive-length Montgomery energy. The literal floor envelope and
dyadic telescope cost only logarithms, and Lean proves that on every strict base-phase margin an
inverse-log adjacent defect forces the second alternative. Thus Perron recutting, all-order wing
localization, count normalization, prime-free composition, and prime-free-to-defect handoff are
closed. Missing source theorems are half-height residual variation and a sufficiently strong signed
gap-energy estimate, not another large-value decomposition.

Low-time polynomial filtering has a sharp boundary. Inside the universal parabolic wedge
`t(d+1) <= (log 2/16)^2`, Lean puts every arithmetic frequency beyond the translated degree-`d`
oscillator disk and proves absolute summability of the von Mangoldt Gaussian tail. The paper
assembly makes the completed filtered source positive there. Fixed-degree/small-time filters
therefore cannot expose the obstruction; any successor must work at the transition `td` of order
one (`ParabolicDegreeTimeWedge.lean`).

A sharper Wold lane is also formal. The ordered residual edge has exact upper-Abel mass

```text
|R_N| exp(a h_N) (exp(a Delta h_N)-1)
  asymp a |R_N| Delta h_N exp(a h_N),   0<a<=1.
```

Summability of the explicit variation at `a=1/2` makes residual Hardy source holomorphic on the
strict half-strip. Under the separate critical prime-gap energy, canonical logarithmic mesh
continuation is holomorphic and has zero residue at every candidate off-critical Wold pole;
static holonomy has zero residue too. The surviving source identity becomes
`-zeta'(s+1)=G(s)zeta(s+1)`. Lean proves first-order holomorphic ODE cannot acquire an isolated
zero, hence critical gap energy plus half-height residual variation implies RH. Relative-orbit
classification proves global cubic Wold exactness alone is insufficient: discarded shifts carry
exact compensating quotient-orbit charge, and reflected physical-head exactness is equivalent to
`Re(rho)=1/2`.

Harmonic-primitive arithmetic is closed: Mertens' second theorem gives
`sum_(n<=N) Lambda(n)/n-log N -> -gamma` and Chebyshev-error primitive `J_N->-2gamma`. This does not
improve Route T's exponent: mass-adjoint quotient scales as `sqrt N`, and real or Mellin-twisted
tails recover `beta-1/2`. Only signed primitive--adjoint correlation survives.

Reciprocal-floor lane is now exact rather than schematic. For prime source `Lambda(m)-1`, Lean
rewrites centered maximal-floor path as full-range term minus triangular transport and one
reciprocal-sawtooth correlation. Total variation is `O(M)` rather than an `O(M^2)` collection of
independent floor errors. Harmonic primitive and sawtooth term occur at same critical scale, so
separate absolute bounds do not close route. Missing theorem is signed cancellation in coupled
`(N,D,m)` statistic.

Sub-square-root massive chirp is a second candidate lane, MC-CS. For `a(u)=u^theta`,
`1/3<theta<1/2`, Lean proves exact finite-packet theorem: conjugation-stable massive trace tends to
zero iff every point in packet lies on critical line. Off-line top growth layer is nonzero finite
exponential sum and Bohr--Cesàro mean square prevents cancellation. This is not yet a full route:
effective Xi packet grows with `u`, tails may cancel selected packet, and no literal prime-side
cofinal chirp projector exists.

The Bessel lane is finite and source-only. True-prime cone differs from outgoing current by an
explicit uniformly bounded eight-term coboundary; legal cone depths differ by bounded families.
Fourier--Bessel analysis rewrites criterion as bounded quadrature defect between true-prime
logarithmic measure and continuum density. For a positive coefficient chamber and sufficiently
small `L>0`, Lean now proves RH equivalent to uniform boundedness of literal prefix defect at
retreated cutoff `floor(exp(kappa_B*u-L*u^(1/10)))`; difference from caustic cutoff tends to zero.
New shell modules compute exact stationary leading
term, prove its phase constant across every fixed spacelike shell, give uniform relative `O(1/u)`
Schlaefli asymptotic, and show shell prime mass has correct positive exponential order. They also
prove square-root-gain exterior tail with shifted-shell factor `exp(-(a-1/2)L)` and exact antitone
shell modulus law. Moving cone annulus is now exact finite set difference, and projection onto fixed
shell phase gives pointwise nonnegative lower bound `(1-C/u)` times shell modulus for every prime
in coherent first shell. Thus exterior tail, higher prime powers, continuum layer, first-shell
phase coherence, phase projection, and main shell mass are closed. Missing theorem is arithmetic
boundedness of fixed subcaustic defect, equivalently global annular assembly comparing summed
positive first shell with all remaining interior true-prime cells while retaining sign. It is no
longer generic Bessel asymptotics.

Sharpness is now formal. For every pair of slopes `1<kappa<lambda` below Bessel balance, raw moving
prime annulus has eventual lower bound
`c u^(-1/2) exp((kappa/2-a sqrt(kappa^2-1))u)` and therefore diverges when exponent is positive.
First shell coherence plus PNT mass beats shifted exterior tail. Hence bounded cone cannot be
obtained by shrinking below critical slope; only cancellation/renormalization at sharp interior
boundary can close Bessel lane.
The boundary layer is coefficient-sharp even below linear scale. At logarithmic retreat
`H=kappa_B*u-q*log u`, raw exterior tail is `O(u^(m_B q-1/2))`; it vanishes for
`q<1/(2m_B)` and is bounded at equality. Thus polynomial retreat in subcaustic criterion is safe,
but any attempt to close route by moving boundary alone stops at explicit logarithmic threshold.

The invariant endpoint is now type zero rather than one chosen retreat. For every moving boundary
asymptotic to the Bessel caustic, exterior prime and continuum tails have vertical exponential type
zero. RH is equivalent both to type zero of the moving prime cone and to type zero of its quadrature
defect. This is a sharp receiver classification, not a bound. Fixed analytic multipliers cannot
supply it: timelike saddle dispersions fill an interval, so a multiplier killing every leading
timelike saddle is identically zero and also kills the receiver. Finite source-safe caustic jets
survive only at isolated spacelike saddles. Moreover dyadic physical apertures at
`u_X=(log X)^4` have common phase, norm growing at least on scale `sqrt(X)/(log X)^2`, and are not
Cauchy in vertical sup norm. Finite-aperture uniform completion is therefore closed negatively;
cancellation must be cofinal and observation-coupled.

The caustic analytic and exterior-retreat layers are closed. Lean builds the Bessel height system,
coefficient ring, jet recursion, exact caustic-symbol cancellation, and holomorphic Cauchy
transport. On the full square-root balance window it proves

```text
||(4a^4-partial_h^2)^n XiMass(u,h)||
  <= C u^(-(n+1)/2) exp(-a sqrt(h^2-u^2)).
```

This is `(22.7)`: one half-power per caustic-null step, without stationary phase. Far-field jets for
every `h >= kappa_B u` have no polynomial height loss. The exact retreat
`H=kappa_B u-q_n log u`, `q_n=(n+1)/(2(2a^2-1/2))`, now splices window and far field and gives a
uniformly bounded full exterior prime tail, uniformly in truncation. This is the corrected endpoint
reading of `(22.8)`--`(22.11)`; no false all-`q` decay is claimed.

The receiver is now source-exact through a finite moving atom core. Arbitrary nowhere-vanishing
subexponential spectral weights preserve line-bound rigidity; the caustic jet is a polynomial
weight. Lean proves all-order integrability and Fourier differentiation, recursion by
`(4a^4-partial_h^2)`, and equality of filtered prime atoms with iterated caustic jets. RH is
equivalent to boundedness on one positive vertical line of the absolutely convergent jet-modified
prime-power atom series. At the exact logarithmically retreated integer cutoff, the whole exterior
series is uniformly bounded in height and truncation. The receiver is therefore a finite moving
atom prefix modulo bounded error. Missing connector is identification of that prefix with
true-prime-cone moving quadrature; RH-bearing science is signed interior/type-zero control, not
another atomization or tail estimate.

**Open core.** Three non-equivalent producer options remain:

1. use the now-constructed prime-free adjacent physical-slice defect, prove half-height residual
   variation (or a phase-sensitive substitute) from pre-divisor Wold source, and obtain a critical
   prime-gap square moment below exponent `3/2`; corpus detector consequence `1.71` is insufficient;
2. identify the finite retreated atom core with true-prime-cone moving quadrature, then prove
   signed interior/type-zero control with phase intact;
3. upgrade finite-packet mass-chirp separation to growing complete Xi divisor with a positive or
   projected mean-square bound stable under tail, and derive that observable from literal
   prime--Gamma source.

These are source theorems. Assuming residual holomorphy or type-zero cone control merely restates
the receivers; existing unsigned prime supply does not imply any option.

Repeated short-block freezing is dead at `T^(5/3)`. More AFE decomposition, contour bookkeeping,
endpoint moments, Gabriel optimization, or detector repackaging are closed work.

**Principal Lean evidence.** Smooth-AFE/Ingham moment and Gabriel detector modules; `Sieve/`
negative-half contour, Hoheisel prime-supply, ordered-gap, and Maynard physical-slice chains;
`XiHeatCassiniWoldResidualODEClosure.lean`; `XiMassBesselConeQuadratureDefect.lean`;
`XiMassSubcausticCriterion.lean`; `XiMassTypeZeroCore.lean`; `XiMassTypeZeroDefect.lean`;
`XiMassLogRetreatTail.lean`; `XiMassJetTransport.lean`; `XiMassJetRetreatEndpoint.lean`;
`XiMassCausticJetTraceCriterion.lean`; `XiMassJetPolynomialBridge.lean`;
`XiMassJetEulerSourceCriterion.lean`; `XiMassJetFourierDerivative.lean`;
`XiMassJetFourierIdentity.lean`; `XiMassJetAtomSeriesCriterion.lean`;
`XiMassJetAtomTail.lean`; `XiMassJetAtomTruncation.lean`; `XiMassJetRetreatExterior.lean`;
caustic-symbol/window modules;
`ReciprocalSawtoothGate.lean`;
`HarmonicPrimitiveScaleAudit.lean`; `ExponentialSumMeanSquareLower.lean`; and
`FinitePacketChirpSeparation.lean`; `Sieve/RouteTFixedShortIntervalPrimeSupply.lean`.

### Route U — shifted-Xi null-face Krein–Lorentz flow

**Endpoint.** Lean proves the sharp alternative

```text
RH or CCMFirstContactBoundaryRoughness.
```

Off RH, restricted-Weil ground energy has a least zero aperture, every smaller aperture is
strictly positive, and a genuine completed null ground exists there but is represented by no
strict smooth interior source. Excluding this boundary-rough state proves RH.

**Architecture.** False RH is equivalent to one fixed polynomial–Gaussian carrier producing
negative Hankel packets at every sufficiently large hard-edge mass. Finite periodization is exact
Chebyshev evaluation at complex Cayley nodes. Antipodal split `P=E+O` yields exhaustive anomaly:
negative even diagonal, negative odd diagonal, or negative even–odd cross capital. Each branch has
literal completed Gamma–polar–von-Mangoldt source disintegration.

**Finite super-apex ancestry and radial flux.** Lean identifies diagonal sign loss before any limiting
passage. For a positive moment functional and its Gauss nodes,

```text
E_y(q)=L((1-yX)q^2)=sum_i omega_i (1-y x_i) q(x_i)^2.
```

The Lagrange quotient at node `x_i` has sign exactly `1-y x_i`; negative hard coordinate
`u=x_i^-1-y` is therefore equivalent to a positive quadrature node above moving apex `1/y`.
Every negative terminal hard root has finite super-apex ancestry. If shifted moments satisfy
`s_y'(k)=-(k+1)s_y(k+1)`, derivative of explicit radial primitive is exactly first
Hausdorff-difference quadratic; `XiShiftedSuperApexFlux.lean` instantiates both moment ODE and
Hurwitz ancestry for shifted-Xi reciprocal moments. Fixed-degree arcsine/weak-moment recession is
not a valid exclusion mechanism: a vanishing-weight endpoint outlier can carry the sign while
disappearing from every fixed moment.

The finite positive-chamber Padé worldline is now exact in Lean. At fixed absolute centre `Y`, its
quadrature resolvent has one-monomial derivative
`2N*L(p^2)*(Y-y)^(2N-1)/D_y(Y)^2`; individual hard poles move left while total reciprocal residue
grows. This is generic positive-moment dynamics and countermodels show it cannot anchor the
absolute hard edge. Its positive survivor is the literal source-error zero attached to each Padé
pole. The highest-moment absolute-divisor repair is also formally closed: when mode order is small
relative to hard-edge height, every fixed divisor-ratio power tends to one and the partial absolute
sum diverges. Route U still must retain phase/common-operator correlation and control that source
factor or Julia-normalized boundary atom.

The first flat-contact jet is now exact. Writing
`delta_(2n+2)=s_y(2n+2)-sum_i w_i x_i^(2n+2)`, vanishing of this top quadrature defect makes every
hard coordinate `x_i^(-1)-y` stationary, and Lean proves

```text
delta'_(2n+2) = -(2n+3) delta_(2n+3).
```

Therefore first-order boundary motion is governed by the next omitted moment, not by node capacity
or the resolved Padé denominator. The hard-edge normalized admission
`S(u)=(1+u/y_0)^N p((y_0+u)^(-1))` now also has an exact derivative at every root,
`S'(u_i)=-(1+u_i/y_0)^N x_i^2 p'(x_i)`, so normalization introduces no hidden root-motion sign.
Generic Leibniz bookkeeping for that induction is now closed as well: if all jets of one smooth
factor through order `m` vanish, the order-`m` jet of its product with any smooth factor vanishes.
What remains is the route-specific all-contact-order Gauss-node/defect induction and the literal
shifted-Xi parity sign orienting the first nonzero defect; the generic flat-face calculation alone
does not exclude contact.

`HTGeometry/DegreeOneDiscriminantTailStability.lean` gives complementary exact warning. A genuine
nonreal conjugate pair has strictly negative isolated degree-one shifted determinant, but its
effect inside nonnegative real bulk contains explicit cross terms and bounded tails preserve bulk
positivity under quantitative margin. One low Hankel minor cannot detect every off-line pair
without source-derived isolation; this is not substitute for super-apex/flux theorem.
The cross term is now completely signed: for `y=u+iv`, `u>0`, it is negative only on one explicit
interval between two algebraic roots and is positive once `x>=1.18|y|`. Fixed-rank Hankel and
finite-degree perturbation countermodels show arbitrarily many low blocks may remain positive;
monomial-tail admissibility margin is exponentially weak in degree. Moving-degree, source-relative
isolation is essential.
There is one exact positive survivor: for a genuine Stieltjes bulk whose shifted form
`L((X-a)p^2)` is nonnegative, every orthogonal-polynomial node lies in `[a,infinity)` and exterior
Christoffel threshold is strictly increasing toward support. Route U could use this only after
proving literal completed signed source has that shifted positivity; without it boundary location
has no formal threshold order.

**Established structure.** Null flags, odd contact, Lorentz crossing, adaptive all-jet Cassini
transport, degree growth, source disintegration, hard-edge inversion, and fixed-carrier cofinal
witness are closed. Nyquist signed current `E^2-O^2` has unconditional complete-divisor exchange
and normalized mixed-source flux tending to zero, so Nyquist lane is spectrally silent. Source-
matched Kelvin heat integration leaves exact Gamma commutator; two-chart theorem rules out every
global scalar counterterm.
The parity-free Fourier receiver now applies to every reflection-symmetric PSD displacement packet:
a simple visible odd kernel and rank-one cross commutator produce a band-limited Fourier transform
with only real zeros, and the analytic limit transfer is formal. This removes parity and published-
packet specificity, but not the missing cross-parity admission or completed-ground selection.
The density theorem proves Route-U archimedean rate is exactly Gamma--Hardy phase rate used by
Connes--Consani source, eliminating any separate archimedean normalization at this seam; it supplies
no sign.

Polar cross term is classified exactly at spectral point `i/2`. For mass `a_k=k+1` and transported
Cayley node `z_k`:

```text
P_k(z_k)  -> Re(F_n(i/2)),
P_k(-z_k) -> 0,
N_k = (P_k(z_k)^2-P_k(-z_k)^2)/(2(a_k^2-1/4)),
a_k^2 N_k -> Re(F_n(i/2))^2/2,
N_k -> 0.
```

Every shifted-reversal degree power cancels under actual common filter. Pole is direct-polyphase
selector with hard-edge valuation two, not logarithmic chart-charge reservoir.

Prime-wall first failure is now source-quantized and parity-complete. Literal hard-edge density is constant inside each
`floor(exp(2 sigma))` chamber; first negative odd form can occur only at
`sigma=log(n)/2` for prime power `n`, and exact jump is subtraction of one von Mangoldt cosine atom.
Under natural integrability, any incoming-nonnegative/outgoing-negative crossing gives strictly
positive response of entering atom. Endpoint Paley--Wiener geometry now proves that every genuinely
admitted odd state at that wall has exactly zero response: its Fourier band is
`[-log(n)/(4 pi),log(n)/(4 pi)]`, while entering cosine is extreme difference frequency `log(n)`.
Translated supports meet only at one Lebesgue-null endpoint. Suzuki logarithmic form-domain
membership supplies this forward support from its inverse-Fourier aperture condition. The same
support law now kills the even response: both parity forms are unchanged across every prime-power
wall on admitted endpoint bands. Thus an admitted state cannot lose sign at a prime wall. Compact symmetric-root division now closes
admission for every simple or repeated root descendant once literal compact factorization is
available: every even quotient and odd twin stays at same Suzuki aperture with exact residual
Fourier factor. For real squared-variable repeated-root profiles, every mixed odd prime response
also vanishes, so entire repeated-root odd Gram matrix is unchanged across wall. Remaining
obstruction lies in passing actual source-selected first-contact limit into that compact real
factorized class and proving incoming nonnegativity/strictness before wall, not jump orientation or
degenerate wall algebra.

Degree escape is now quantitatively compactified. If RH fails, least defective shifted-Hankel size
`D(y)` satisfies `c sqrt(y)<D(y)<=C sqrt(y)` eventually. Exact Cayley/Chebyshev lift turns every
negative Gaussian divisor witness into degree-`O(sqrt(y))` hard-edge packet, so diagonal failure
lands in finite-exponential-type Paley–Wiener space. For rational hard-edge tests corpus proves
complete polar–Gamma–von-Mangoldt source formula, coefficient-uniform prime-information cone,
mass-uniform prime bound, Gamma logarithmic height tightness, and rational Bernstein translation
bound. Adaptive arithmetic producer is exactly reverse-Euler source on one complete Hausdorff
diagonal; it loses no finite hard-edge information, but pointwise positivity is explicitly false.
Strong `L2` precompactness is now closed. For every normalized nonpositive rational hard-edge
family with mass at least four and degree bounded by `C` times mass, Lean proves total boundedness
using exact derivative formula, uniform Bernstein bound, Gamma/source tightness, and finite-grid
Kolmogorov--Riesz. Every sequence has a strongly convergent subsequence with unit-norm nonzero
limit.

Finite-type control operator is explicit. Cayley half-density conjugates angular derivative to
first-order physical operator `A_a=((a^2+x^2)/(2a)) d/dx+x/(2a)`. Descendants raise angular order
exactly, Cayley lift is an `L2` isometry up to factor `a/2`, and every order `m` satisfies
transported Bernstein bound `||A_a^m g||_2<=N^m||g||_2`. All-order angular-momentum estimates
now complete the Paley--Wiener passage: for normalized packets with `N_k<=C a_k`, `a_k->infinity`,
every strong limit has Fourier transform zero almost everywhere where `2 pi |xi|>2C`. The nonzero
subsequential limit is therefore a finite-exponential-type state unconditionally.

Abstract bandlimit is now connected to a literal Route-U source. For any continuous representative
`f` of the actual hard-edge strong limit, Lean selects the open-band indicator of its unitary
Fourier transform as a pointwise compact source `q`. This source lies in `L1 cap L2`, vanishes
literally at and beyond `±C/pi`, and satisfies at every real frequency

```text
routeURealFourier(q)(w)=f(w/(2 pi)).
```

The proof uses L2 Fourier reflection plus the corpus L2/classical bridge, then upgrades almost-
everywhere inversion by continuity. If `f(x)=(x^2-r^2)^m K(x^2)` with continuous `K`, source
transform has exact factor `(w^2-(2 pi r)^2)^m` with continuous rescaled squared-variable profile.
Thus compact-source selection, integrability, endpoint support, and multiplicity transport are no
longer open. The later escaping-pole theorem also derives the required global root quotient from
selected first-contact packets; incoming sign remains open.

The local-uniform and strong-L2 extractions are now connected on any common subsequence. Lean proves
actual rational packets converge pointwise to `x -> F(x^2)` because Cayley half-density tends to
one. An almost-everywhere convergent subsequence of strong L2 convergence then identifies this
candidate with `ofRealLp L`, derives its L2 membership, and proves `Im(F(x^2))=0` pointwise from
reality of every finite packet. Hence representative equality, square-integrability, even
squared-variable shape, and physical reality no longer require separate hypotheses. Moreover, the
only possible pole of the `n`th squared-angular approximant is `-a_n^2`; these poles escape every
fixed complex neighbourhood. Eventual local holomorphy plus locally uniform convergence makes `F`
entire. Unit `L2` normalization makes it nonzero. Therefore every root `F(r^2)=0` has automatically
supplied positive finite multiplicity `m`, a global entire quotient `H` nonzero at `r^2`, and an
exact literal compact-source factorization. `XiShiftedHardEdgeEntireRootFactorization.lean` closes
the global squared-variable root quotient with no entireness or factorization premise.

The hard-edge form also has an exact literal signed-density representation in squared variable
`u=x^2`, including polar atom at `u=-1/4`; even and odd sectors differ by multiplication by `u`,
and terminal divided-jet recursion gives terminal odd energy as root times terminal even mass.
Committed declarations add exact quadratic expansion on form domain and general semidefinite
Hankel bootstrap: null jets through order `m` force every Hankel entry below `2m` to vanish, leaving
only terminal corner. `XiShiftedHardEdgeParityJet.lean` instantiates this algebra on
literal hard-edge density: it gives exact even and odd descendant Gram entries, obtains moment
Cauchy--Schwarz from PSD, propagates every lower-jet vanishing from one null-state moment, kills
every nonterminal even Gram entry, and identifies terminal odd energy as root times terminal even
mass. Distinct roots are orthogonal. For roots `r_i` of multiplicities `m_i`, repeated roots force
an independent parity-doubled zero-energy family of dimension at least
`1+2 sum_i (m_i-1)`; zero terminal mass adds two directions and zero root with positive terminal
mass adds one. Under full even/odd nonnegativity, positive terminal mass forces `r_i>=0`, and a
nonzero terminal odd energy forces `r_i>0`. Consequently a simple full ground can have only simple
positive roots with positive terminal masses. These are exact source-density theorems conditional
on form-domain, PSD, nullity, and factorization hypotheses. Repeated-root descendant admission is
now exact for compact sources, and actual hard-edge bandlimit supplies such a source once its
continuous representative is fixed: continuity closes quotient identities at `±c`, preserving full
residual multiplicity through recursive symmetric division; every even quotient and odd twin is
an exact same-aperture Suzuki vector. When factor is real in squared variable, odd twins have
literal real `L2` profiles, and bilinear endpoint orthogonality kills every mixed prime-wall entry.
Thus an admitted repeated-root odd kernel cannot be newly born at wall if incoming direction was
strictly positive. Entire-limit root extraction now derives global squared-variable factorization
with full multiplicity from literal first-contact packets. What remains unproved is required
completed-boundary exclusion at least contact; compact source realization, exact factor transport,
prime-wall invisibility, and quotient admission are closed.

Hard-edge complex normality is now substantially closed. Exact circle-energy reproducing bound and
degree-linear aperture control make normalized Cayley numerators locally uniformly bounded; Montel
gives a locally uniform subsequence. Cleared denominators converge to one when `d/a^2->0`, and a
nonzero packet limit has only real zeros in squared variable. Exact root-division Cauchy law is also
formal once limit state `(u-r)G` is admitted as null. Dominated convergence for literal hard-edge
density now passes finite zero pairings to the limit and preserves every smaller-aperture
nonnegative pairing under exact form-domain domination hypotheses. Thus normal extraction,
real-root closure, null-row passage, positivity passage, and root division are no longer open
mechanisms. Finite-degree Hankel tails have exact
Frobenius and row-sum positivity gates, but only relative to a lower bound for the bulk smallest
eigenvalue. Absolute monomial-tail control cannot replace source-relative margin at degree linear
in hard-edge height.

Padé/Carathéodory analysis identifies wrong scale in ordinary disk coordinates. Lean now constructs
the positive-real divisor resolvent and its exact disk chart. It proves an ordinary pole residue is
`O(1/y)`, while Julia normalization remains comparable to physical residue, and gives the exact
odd-coefficient reserve hierarchy and balance. Thus ordinary capacity, unweighted finite jets, and
finite-head depletion can erase a physical atom even though its Julia-normalized charge survives;
Lean proves whole fixed jet head tends to zero when its length is sublinear at boundary depth.
Route U is therefore a boundary-angular-derivative problem: lawful target is absence of a cofinal
Julia-normalized atom, not stronger ordinary Padé convergence.

The source wall is now identified exactly with CCM restricted-Weil positivity. Normalized dilation
by `2*pi` is a continuous linear equivalence from Route U form domain onto the entire CCM
archimedean form domain at scaled aperture, and Lean proves pointwise

```text
Q_CCM(2*pi*a, scale(f)) = 2 Q_U(a,f).
```

Consequently pointwise sign, zero, global nonnegativity, and existence of a negative vector agree
in both directions. Route U is not testing a smaller privileged family. It is a hard-edge
first-contact architecture for the same full restricted-Weil positivity wall attacked globally by
O and through Morse index by G-floor. This creates a real merger: O's whole-ground classification
could exclude U's first negative state, while U's no-birth classification could localize O's first
negative direction. It does not itself prove either.

First contact is now localized further. Small-aperture positivity, antitonicity, continuity, and
ground attainment prove `RH ∨ CCMFirstContactBoundaryRoughness`. If RH fails, least contact has a
nonzero completed null ground, all smaller floors are strictly positive, and compact containment
forces every nonzero strict smooth interior source to retain positive energy at contact. False RH
therefore cannot first enter through an arithmetic prime wall or a literal smooth source; it must
enter through loss of compact containment in completed form domain.

Route Q supplies a possible width-sensitive invariant for this boundary channel. An off-line
conjugate resolvent pair has zero signed frequency mass but quadratic concentration
`pi*y^2/(b*(b^2-y^2))`, diverging at transverse wall. A finite source-pure quadratic-energy budget
dominating both that Q profile and U's Christoffel boundary layer would exclude both defects. The
common energy and two domination maps remain conjectural; exact pair profile alone is not a new
route.

**Open core.** Exclude `CCMFirstContactBoundaryRoughness`: prove a boundary trace/quotient theorem
showing every completed least-contact null ground is approximable strongly enough by smaller-
aperture interior sources to preserve strict positivity, or derive whole-ground coercivity that
rules it out directly. In hard-edge coordinates this is exclusion of a nonzero state
`f(z)=F(z^2)` with `F` Laguerre--Pólya, `ord(F)<=1/2`, Paley--Wiener `L2`, finite-prime Gamma null
equation, and nonnegativity at every smaller aperture. Incoming PSD/strictness is no longer a vague
missing assumption: Lean proves only possible false-RH state lies outside strict smooth interior
core.
Bandlimit canonically supplies required literal compact integrable source; escaping-pole entireness
and unit-norm noncollapse automatically supply and transport every physical root with its full
multiplicity. Once remaining sign bridge holds, exact
recursive Suzuki admission and endpoint
invisibility preclude both simple and repeated-root odd birth at quantized prime-power wall with no
additional source-sign inequality: full repeated-root odd Gram jump is identically zero. Hence any
admitted degenerate kernel must already exist in incoming chamber; source theorem must exclude that
pre-wall formation rather than orient wall jump.
Equivalent diagonal alternatives are source-specific exclusion of bounded super-apex nodes,
positivity of first Hausdorff radial flux, or vanishing of Julia-normalized boundary atom. Pole
cannot orient cross branch. More ordinary Padé capacity, unweighted Carathéodory
jets, finite-head depletion, fixed-degree recession, or source-free compactness is dead work.
Post-formation strict-frontier wall integrability is also dead: numerator is continuous and
positive while newborn admission norm vanishes at most linearly, forcing a nonintegrable `1/(v-y)`
pole. The all-frontier integrability predicate is exactly RH; any cross-route bridge must prevent
frontier formation before division, not regularize its quotient afterward.

**Principal Lean evidence.** shifted-Hankel/null-flag modules,
`XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean`,
`XiShiftedHardEdgePrimeGammaAntipodalPolarization.lean`, Kelvin current/detailed-balance/two-chart
modules, `XiShiftedHardEdgePrimeGammaPolarPolyphaseValuation.lean`,
`XiShiftedHardEdgeLeastDefectiveSize.lean`, `XiShiftedHardEdgeCompletedDensity.lean`,
`XiShiftedHardEdgeUniformPrimeSum.lean`, `XiShiftedHardEdgeTightness.lean`, and
`XiShiftedHardEdgeAdaptiveArithmeticSourceLaw.lean`, `HTGeometry/L2GridApproximation.lean`, and
`XiShiftedHardEdgePrecompactness.lean`, `CosinePhaseParseval.lean`, and
`XiShiftedHardEdgeAngularMomentum.lean`, `XiShiftedHardEdgeDerivativeBound.lean`,
`XiShiftedHardEdgePaleyWiener.lean`, `XiShiftedHardEdgeDensityMeasure.lean`,
`XiShiftedHardEdgeOddFirstFailurePrimePowerJump.lean`,
`L2FourierEndpointOrthogonality.lean`, `SuzukiHlogEndpointSupport.lean`, and
`XiShiftedHardEdgeOddPrimeWallEndpointInvisibility.lean`,
`XiShiftedHardEdgeEvenPrimeWallEndpointInvisibility.lean`,
`CompactL2FourierRootDivision.lean`,
`XiShiftedHardEdgeOddRootSuzukiAdmission.lean`,
`XiShiftedHardEdgeRepeatedRootSuzukiAdmission.lean`, and
`XiShiftedHardEdgeRepeatedRootPrimeWallNoBirth.lean`,
`XiShiftedHardEdgeBandlimitedCompactSource.lean`,
`XiShiftedHardEdgeCCMScalingBridge.lean`,
`SuzukiFirstContactBoundaryRoughness.lean`,
`XiShiftedHardEdgeLocallyUniformL2Source.lean`,
`XiShiftedHardEdgeCayleyPacketBound.lean`, `XiShiftedHardEdgeCayleyNumerator.lean`,
`XiShiftedHardEdgeCayleyLimit.lean`, `XiShiftedHardEdgeRootDivision.lean`,
`XiShiftedStrictFrontierSourceWallIntegrabilityGate.lean`,
`HTGeometry/CaratheodoryCoefficient.lean`, and
`PositiveRealResolventChart.lean`, and
`HTGeometry/FiniteDegreeShiftedHankelTailStability.lean`. `SliceWeierstrassDivision.lean` supplies
local division infrastructure only.
`DiscriminantCrossPositiveInterval.lean`, `FiniteDegreeReciprocalPerturbation.lean`,
`FixedRankHankelNonStieltjes.lean`, and `MonomialTailGateBound.lean` close low-degree/tail shortcuts.
`HTGeometry/StieltjesExteriorChristoffelMonotone.lean` is sharp positive survivor under shifted
Stieltjes positivity.
`HTGeometry/PsdHankelJetVanishing.lean`, `XiShiftedHardEdgeParityJet.lean`,
`HTGeometry/HausdorffDifferenceInertia.lean`, `HTGeometry/RadialMomentFlux.lean`, and
`XiShiftedSuperApexFlux.lean`, together with `HTGeometry/MovingGaussNodes.lean`,
`HTGeometry/IteratedDerivVanishing.lean`, `HTGeometry/GaussResolventError.lean`, and
`HTGeometry/MovingCenterResolvent.lean`, close generic
parity, finite ancestry, radial-flux, and Padé-worldline algebra; `HTGeometry/PowerSequenceLimitOne.lean`
closes absolute-divisor majorant failure. None proves source-specific exclusion theorem.
`PrimeArchConjugatePairQuadraticConcentration.lean` supplies exact Q--U candidate invariant but no
arithmetic source ceiling or U-side domination.

## Terminal and retired routes

Closure applies to stated mechanism, not every future construction using similar vocabulary.

| Route | Closed mechanism | Positive survivor or lawful successor |
|---|---|---|
| A | Fixed source-faithful physical-phase transports are identity; nonidentity transport has explicit connection defect. Under two-gap rational independence, every exact centralizer-line local logarithm is physical time plus scalar phase. Canonical folded generator exists only through spectrum/time-fitted integer branch ledger. Positive Markov feasibility is original source sign; universal feasibility is RH. | Phase-natural/local-logarithm rigidity and barycentric orientation completeness test any successor; branch-fitted folding is not source orientation. |
| B | Fixed-width rectangular Weil quadrature has no orientation. No unitary can transport both scaling and grading, or two distinct prolate parameters; first Jacobi contraction is strict. | Only a new common graph/boundary realization of grading deformation, with relative-resolvent correction and noncancellation, could succeed. |
| C2 | Finite theta detector saturates its available width; missing width is already RH-bearing. | Interfaces survive inside Q. |
| D | Finite prime–archimedean Hankel reconstruction/local positivity cannot orient completed all-degree source. | All-degree compact moment survivor is P; continued tail survivor is D2. |
| F | Finite-height Sonin/Burnol completion and compact multiplicative correction have wrong asymptotic order or collapse source. | An order-one pre-Gamma packet-diagonal primitive would be new route. |
| G2 | Required relative-Volterra germ is RH-equivalent. | Route G retains exterior source problem without Volterra repackaging. |
| H | Moving completed-source Taylor parity loses orientation after even factorization. | Relation-valued indefinite primitive would be new route. |
| Heat echo | Additive heat aperture has exact all-order Jonquière expansion and a zeta zero removes exactly rung zero while every strict rung remains nonzero. Descent from this echo defect to reflected prime-sector compatibility is exactly RH; canonical nonzero tangent is noncovariant off line. | Heat echo is a source detector/tomography tool, not an independent producer. Any successor needs a new non-scalar pre-on-shell covariance mechanism. |
| I | Claimed sharp dyadic width is same saturated C2 coordinate. | No independent premise. |
| J | For `L_m=6 log m`, `m>=25`, Lean proves `E_bad(x,L_m)>=log(m)/20` for every Julia scale. Uniform unrenormalized energy budget is impossible; off-diagonal cancellation cannot remove unit diagonal; post hoc subtraction breaks one-node capacity. | Principal-relative current must be defined before good/bad projection. Existing concrete realization is R. |
| K | Quadratic spectral mechanism fails. | Strong all-order marked-prime/quartic content belongs to P. |
| M | Source-faithful Gamma–Jacobi reader is complete; remaining anchored cofinal flatness is RH. | No lower producer inside M. |
| N | Prime-normal/common-forcing and conormal carriers are exact, but response equality, endpoint contractivity, or bounded polar work is RH-equivalent. | These are coefficient-faithful receivers shared with L/P/R, not producer. |
| R | Intrinsic pre-polar producer category is empty. Every audited external positive-polar, Calkin, compactness, first-Xi-jet, and loss-zero Fisher interface—and their disjunction—is RH-equivalent. Hyperbolic-gauge quadratic positivity is identically zero; quartic Stokes amplitude annihilation is RH-equivalent. | Only nonfunctorial external polar/compression admission can survive. Quantitative Burnol collar decay strengthens receiver but does not reopen R. |

Route S remains upstream source-algebraicity/dynamical infrastructure, not independent RH route:
it lacks both Xi-typed source handoff and non-circular critical-line producer.

Additional interfaces are terminally classified without receiving route letters:

- ordinary connected positive prime-loop quantum graphs are impossible: isolated loops reproduce
  Euler factors, but any connection between distinct nonzero loops creates a mixed primitive word
  absent from Euler product; killing all mixed words block-diagonalizes the graph. Only graded or
  indefinite scattering with supertrace cancellation, archimedean vertex, and Xi superdeterminant
  could survive, and no such source identification exists;
- cofinal line, second-moment outer-power, anchor-mass, and integral-ledger window packages are each
  exactly RH; their existence is not an independent supply theorem;
- finite rank-one repair selects positive side exactly by Schur scalar, and any finite-rank
  counterterm is invisible on kernel of its boundary map.
  `FiniteRankCountertermXiVisibility.lean` proves that, at Xi level, repaired Weil positivity still
  forces RH whenever every off-real sign test lies in that kernel. A zero-fed counterterm can
  cancel a bad atom by construction. `ZeroFedUvarovRepairTautology.lean` sharpens this:
  subtracting an atom and adding the identical rank-one Uvarov channel returns base form exactly,
  and Schur scalar records only ordinary inertia crossing. Source-built boundary visibility and
  kernel exhaustion are mandatory;
- full differential-translation freeness is divisor-blind: for every prescribed nonzero entire
  divisor, a dense residual set of entire zero-free gauges gives full complex-translation
  differential-algebraic independence while preserving divisor exactly. The stronger symmetric
  construction preserves functional equation, Schwarz reality, and any prescribed finite jet
  passport while producing both critical-line and off-line divisors with same freeness property.
  Hypertranscendence, symmetry-caged translation freeness, or finite jets therefore cannot select
  critical line;
- prescribed local gap statistics are equally nonselecting. Lean now realizes every stationary
  ergodic positive mean-one gap law as positive zeros of an even real entire exact-order-one
  function whose symmetric carrier has a dense residual set of maximally translation-free
  parameters. The insertion factor is now Lean-explicit:
  `(z^2-tau^2)(z^2-conj(tau)^2)` is nonzero, even, Schwarz-real, has exactly the quartet
  `{±tau,±conj(tau)}`, has no real zero when `Im(tau)≠0`, and has an order-one envelope.
  Its product with the moving-divisor canonical carrier is now formal too: real zeros are unchanged,
  the quartet is the complete added zero set, maximal translation freeness survives at every
  positive power, and every complete positive-power translation profield is literally unchanged.
  Thus exact order, arbitrary local gap law, maximal differential-algebraic freeness, and even the
  whole translated-power differential field still do not select RH without pointed
  source/operator admission. Evidence is `HTGeometry/QuartetPolynomial.lean`,
  `HTGeometry/TranslationPowerProfield.lean`, `HTGeometry/MovingDivisorQuartetSurgery.lean`, and
  the stationary-ergodic capstone `HTGeometry/PrescribedGapProcessEntireProfield.lean`;
- the firewall now survives global analytic guards without any moving-divisor host. Lean constructs
  an explicit exact-order-one entire realizer that is even, Schwarz-real, strictly positive and
  zero-free on its imaginary axis, aperiodic, and free of nonzero quasi-periods. In strip
  coordinates it satisfies `X(1-s)=X(s)`, Schwarz symmetry, and real-axis zero-freeness while
  retaining an off-axis quartet passport. Exact symmetry laws for its derivative jets are also
  available in the declaration-level working tree. Functional equation, reality, order, axis
  zero-freeness, aperiodicity, and finite symmetry-compatible jets therefore remain generic
  firewalls, not Xi source admission (`QuartetPassportRealizer.lean`, `QuartetSymmetryJets.lean`);
- global right-even polynomial factorization of completed odd logarithmic-derivative moments is
  false already for `P=X`: second moment is positive at `x=1/2` and negative at `x=10` in Lean.
  Its explicit Euler-source upper certificate survives as a quantitative finite-source tool, not a
  Route-Q producer;
- unrestricted nonnegative source weights cannot prove a fixed Loewner budget: under a uniform
  budget every pointwise kernel must vanish, and with mass cap `C` the budget is equivalent to the
  pointwise inequality `C K_x <= B`. Positive coefficients or a positive scalar shadow cannot
  replace kernel-block PSD, source magnitude control, and exhaustion;
- finite exact source normalizations leave affine recession directions. A fixed PSD budget on a
  one-sided ray forces recession direction itself PSD; on a two-sided line it forces direction
  zero. Likewise scalar real-axis inverse-kernel positivity is nonselecting: an exact `3x3`
  Hermitian counterexample has kernel `1+t^2+t^4>0` on whole real moment curve but two negative
  squares off curve;
- low-order positivity does not propagate through signed boundary modification: positive Stieltjes
  bulk minus pole plus first trivial-zero atom can remain negative, and even the `N=1` signed bulk
  need not inherit exterior Christoffel monotonicity. These countermodels bar local-moment repair of
  P/Q/U without source-specific global control.
- coefficientwise-positive Li-to-shifted-moment transfer is impossible: exact reciprocal-Chebyshev
  kernel has positive first Taylor coefficient and negative second coefficient for every positive
  degree. Li positivity cannot feed Route U through a nonnegative scalar coefficient bridge;
  operator-valued or signed source geometry would be required.
- finite or one-sided operator tests do not upgrade to global positivity: every fixed Hankel rank
  can be positive while next rank is negative; every fixed-degree reciprocal block can hide a
  small nonreal pair; and a one-sided quadratic bound need not define any bounded operator.
  Shifted moments at every positive order do not determine unshifted tail class, whose divergence
  may vary from logarithmic to stretched exponential;
- boundary repair has no source-free order law. Independent boundary functionals can realize
  arbitrary Weyl thresholds, and a positive bulk minus one pole square can remain negative after
  every Uvarov repair at a different boundary. Pole budget alone does not select repair channel;
- positive Euler coefficients do not imply PF2: shifted local Euler orbit has positive coefficients
  but negative first nontrivial Toeplitz minor. Variation-diminishing transport cannot be inferred
  from coefficient positivity;
- positive Xi jets, functional equation, Schwarz reality, and order-one growth do not determine
  zero level: subtracting constant preserves every positive jet and those symmetries while placing
  a real off-critical zero. A real point-supported source can likewise insert an arbitrary
  off-axis quartet. Analytic-to-real theta-defect comparison has exactly off-real divisor as
  kernel, so its injectivity is RH rather than a localization theorem;
- naive Hilbert closure of finite coefficient summation is maximally multivalued and nonclosable.
  Cofinal source summation requires graph norm/boundary coordinate, not bare `ell2` closure.
- the resulting one-leg singular graph does not restore arbitrary prime dependence. Its actual
  source-descent predicate is completely classified: a continuous reporter agrees with a
  prime-labelled scalar profile on every genuine normalized fixed-left row iff that profile is
  constant on `nthPrimeSubtype`. Constants descend through scalar multiples of one-leg trace;
  reciprocal, prime-log, inverse-Gamma, and every other nonconstant scalar relabelling do not.
  This closes the existing graph mechanism, not carrier-changing finite-core maps. Evidence:
  `XiGammaSixWoldJordanParametricVacuity.lean`, theorem
  `primeLabelledActualSourceDescends_iff`;
- positive even-frequency seam germs do not form a Stieltjes repair: shifted moments alternate,
  and half-turn parity correction still has negative first shifted determinant. Full reciprocal
  seam has infinite zeroth mass although every positive moment converges. Its raw unshifted form
  converges exactly on ideal `y R[y]`, where it equals shifted Route-U form `Q1`; no finite `T0`
  makes the full unshifted Hankel tower PSD. Zeroth-moment repair is closed, not an open route;
- relative Loewner positivity is exactly bounded contraction after congruence normalization and
  preserves negative index. Dense compression exhaustion recovers it only for a bounded operator;
  every fixed finite depth is blind to a violating rank-one direction.
- reciprocal-atom test spaces expose an exact circularity boundary. Uniform density strong enough
  to isolate every atom is already RH-strength; polynomial `Q_0`, finite boundary channels,
  hard-edge ideals, and Uvarov-kernel positivity become RH equivalences. A finite-map counterterm
  is invisible on its kernel, while an atom-fed counterterm pays the bad atom's bill by construction;
- every finite collection of real-linear probes, finite seam jets, or finite-codimension conditions
  is nonselecting: an even Schwarz-real order-one perturbation can preserve them all while inserting
  an off-line quartet. Finite verification cannot replace pointed infinite-source incidence;
- source-selected Gamma ghost repair is rigid but terminal. The local repair is unique; one shared
  prime-independent ghost compatible at primes two and three exists exactly at centered rate zero.
  On Xi divisors, shared-ghost descent, Gamma naturality, and all-cell vanishing are equivalent to
  RH, so they classify the receiver rather than supply a producer.

Evidence for these latest closures is `FixedRankHankelNonStieltjes.lean`,
`FiniteDegreeReciprocalPerturbation.lean`, `OneSidedCompressionUnbounded.lean`,
`ShiftedTowerTailClasses.lean`, `BoundaryWeylThresholdNonMonotone.lean`,
`PoleBudgetUvarovNoGo.lean`, `ShiftedEulerPrimeOrbitPF2.lean`,
`PositiveJetHorizonLevelBlindness.lean`, `RealSourceMicrolocalQuartet.lean`,
`ThetaAnalyticRealDefectKernel.lean`, `SummationGraphDenseCollapse.lean`,
`HTGeometry/EvenFrequencySeamMoments.lean`, `ReciprocalSeamZerothMoment.lean`,
`LoewnerCongruenceNormalization.lean`, and `HTGeometry/ContractionCompressionExhaustion.lean`.
Further evidence is `ReciprocalAtomTestSpaceClosure.lean`,
`ReciprocalAtomCounterterm.lean`, `ReciprocalAtomPolynomialApproximation.lean`,
`FiniteProbeRHNonselection.lean`, `SourceSelectedGammaWardSharedGhostDescent.lean`,
`SourceGammaNaturalitySharedGhostProducer.lean`, and
`FrankensteinParacyclicGhostTwoSheetAnomaly.lean` together with
`FrankensteinParacyclicPrimeClockBigWittGhost.lean`.

Finite squarefree functional-equation complement is also terminal as approximation mechanism.
Exact Boolean-complement coefficients force `a_p^2=p` for every finite prime and conversely, but
then the sign is forced and every zero of finite Euler product lies on `Re(s)=1/2`. This is a sharp
positive finite rigidity theorem, not an approximation to RH: all-prime Euler source has no top
coefficient or cofinite Dirichlet coefficient. Increasing finite inventories do not create missing
infinite complement; required compatibility must be defined on pointed infinite source--divisor
incidence.

## What routes have in common

### 1. Information is usually lost before endpoint, not absent at source

Corpus routinely constructs prime labels, depth, reflection, multiplicity, and horizontal grade.
Failures occur when later operation forgets decisive coordinate:

- scalarization erases parity, phase, or incidence (E, U);
- finite CCM quotient erases overcomplete source provenance (CCM-FU);
- positive square/Gram formation erases reflection-odd current (C1, P, R);
- compact topology erases noncompact escape required by singular physical landing (L);
- one trial Rayleigh quotient supplies upper, not lower, ground control (G, O).
- ordinary disk residue or finite jets erase Julia-normalized boundary charge (U).

Any successor must preserve route's missing coordinate until producer theorem acts.

### 2. R, L, CCM, and Gauss–Hodge see one horizontal obstruction

Source-zero horizontal carrier, Gamma Bockstein, Deninger Green obstruction, Burnol seam energy,
and Gauss–Hodge mass are coefficient-faithful realizations of same reflection-odd horizontal class.
Corpus constructs and orients class; global vanishing is RH-equivalent. Different target geometries
do not constitute independent evidence. A viable merged mechanism needs source-generated nonzero
mixing before divisor specialization, preserving prime/depth/divisor/multiplicity and both
reflections. Rank-one, holomorphic, compact, or fitted contractible repairs only re-present or erase
obstruction.

The completed one-leg graph can no longer be that mixing mechanism when its only new datum is a
prime-labelled scalar. `primeLabelledActualSourceDescends_iff` proves continuity collapses every
such profile to one constant, and every constant already comes from the ordinary graph trace.
Therefore any surviving L/R/CCM/P Frankenstein must act before this completion, change the carrier,
or retain a genuinely non-scalar critical-scale incidence. Reweighting the same graph cannot
advance the frontier.

The Faddeev--Popov/shared-ghost reinterpretation is now classified exactly.  An inverse-oriented
positive ghost can repair one prime-local Gamma rotation at every centered rate, but positivity
forces the fitted value `c_p=p^(-t)`.  Hence local ghost existence contains no arithmetic
information.  One source-selected Gamma ghost independent of retained prime label repairs both
prime two and prime three iff `t=0`; on an Xi divisor this is equivalent to the existing Big-Witt
prime-clock selected Ward descent and therefore to critical-line placement.  A viable producer
must consequently derive **prime-independent shared-ghost existence** from genuine source/Gamma
naturality.  Primewise countercharacters, common same-orientation determinant corrections, and
contractible ghost pairs cannot supply it.  Evidence:
`RHTower/SourceSelectedGammaWardSharedGhostDescent.lean`.

Ordinary Gamma cover composition does not produce that ghost: `(mn)^(-t)=m^(-t)n^(-t)` is coherent
for every real grade, and Lean gives an explicit `t=1/2` countermodel where prime-two and prime-three
fitted ghosts differ. The strongest survivor is two-orientation scale-zero descent. If forward and
reflected coefficient-faithful characters extend continuously and unital through the same collapsed
source scale, they force `t<=0` and `-t<=0`, hence `t=0`; this constructs Cartier landing and the
genuine source-natural reporter. Literal terminal theta multiplicity-jet gains equal the fitted
prime ghosts, so labels and multiplicity are retained. Lean now constructs both forward and inverse
prime-character Fisher fields from that same literal jet: forward `ell2` admission is exactly
`Re(rho)<=1/2`, inverse admission exactly `Re(rho)>=1/2`, and bilateral admission is the critical
line, globally RH. Field construction and full-Laurent multiplicative Gamma production are closed;
RH-strength step is additive conormal descent, equivalently erasure of forced quadratic inversion
ghost. Exact open producer is a pre-divisor singular/physical law forcing that descent without
assuming it. Evidence:
`FrankensteinGammaCompositionScaleZeroDescent.lean` and
`FrankensteinThetaTerminalGammaSharedGhost.lean`, together with
`FrankensteinThetaTerminalFisherEntranceWall.lean`.

### Common completed source does not make reporters equivalent

CCM-FU, CCM-UR, and CCM-RF are three source-isogenous views of the literal completed
prime-minus-polar Stieltjes current. FU measures cumulative/Cesàro size, UR is affine-blind signed
curvature with a canonical two-channel lift, and RF is a fixed-width adjacent-block Haar
coefficient. FU's linear bound controls UR, but UR has no reporter-only converse; no current theorem
turns either into RF's eventual lower floor. These are distinct candidate mechanisms but not three
independent arithmetic sources. Combining their RH endpoints does not multiply evidence unless a
new source law couples their signed reporters before scalarization.

Within UR branch there is now an exact collapse: completed-current response is an explicit
elementary remainder minus a positive multiple of unit critical-Mellin aperture resolvent. Thus UR
lower-law card and aperture-resolvent upper-sector card name same pointwise source inequality. FU
remains a stronger one-way reporter and RF remains a different Haar reporter.

### 3. Ground selection is common spectral wall

CCM-FU, C1, G-floor, O, and U all possess explicit sources, operators, local positivity or
compactness, and spectral receivers. G controls one punctured small-aperture chamber and has finite-
packet Morse algebra but not full screw-source index theorem. O has oscillator spectral rigidity,
global indexed prolate order, exact-solution off-diagonal/high-row assembly, and two-scale carrier.
Its literal restricted-Weil form now reduces to finite peripheral Birman--Schwinger block at every
aperture, but no source estimate controls that block uniformly. U compactifies degree escape, proves finite Paley--Wiener
type, classifies parity-doubled root jets, and proves every false-RH least contact is a completed
boundary-rough null ground absent from strict smooth core. None excludes that boundary ground or
promotes local/selected sectors to source control of complete global spectrum.
Required mathematics is
finite-peripheral prime--polar sign control, continuation through first spectral loss,
reduced-resolvent control, relative coercivity, or source-derived real-spectrum law—not more seed
vectors, prolate ordering, or determinants.

CCM-GS adds a quantitative warning: fixed-cutoff separating vectors are open dense, but cofinal
prime-log crowding forces any positive separating margin to be paid by inverse-spacing growth of
ground-state generator energy. Qualitative genericity cannot substitute for cofinal margin,
reduced-resolvent, and Mellin evaluation bounds.

### 4. Singular boundary orientation is common geometric wall

L and P have source carriers and target readers on both sides, and both reach singular boundary
with coefficient fidelity. Their surviving producers now differ:

- L: reciprocal-weight fixed-star/Wold--Jordan descent is terminal by parametric vacuity and the
  Beurling half-abscissa firewall; surviving Hodge branch must form a critical-scale arithmetic
  Green intermediate extension and faithful cup-isometric harmonic comparison;
- P: completed source construction and budget domination of explicit positive
  fundamental-symmetry correction.

CCM–P–L does more than identify a shared coefficient: two-sheet singular graph preserves centered
orientation while killing mass trace and lands exactly in CCM cubic jet and fixed Sonin detector.
Remaining wall is cofinal source assembly plus selected fixed-star/Stokes/budget control; local
carrier no longer causes scalar blindness.

### 5. Arithmetic routes need non-scalar all-prime control

D2, E, T, and U have exact finite/safe-side/one-prime source identities. D2 now has divergent
safe-line deficit on every polynomial horizon, and T now has complete detector zero-density chain.
Remaining statements are continuation through Euler wall, fixed-relation interval incidence,
structured short-window cancellation, or signed von-Mangoldt cross control. Modulus-only bounds,
coefficient-free positivity, fixed finite prime bands, and post hoc scalar renormalization are
formally insufficient.

### 6. Quantization is a real constraint

Q proves a continuous monotone source carrier cannot land on atomic Xi all-degree measure, while an
explicit canonical **nondecreasing plateau** carrier always can and still leaves exactly the
RH-equivalent orientation energy.  Therefore discontinuity, atomic realization, positive fibres,
and ambient one-dimensional order are not constraints strong enough to produce RH.  Scalar rank is
a gauge shared by every atomless ordered source.  P and U also expose indivisible conormal/contact
charges.  Successful source selection must break rank-gauge invariance by retaining arithmetic
labels, conditional incidence, boundary indices, singular graphs, or multiple observables beyond
the scalar pushforward law—not merely a smoother, more discontinuous, or monotone reporter.

### 7. Formal source complexity need not constrain divisor

The fixed-divisor gauge theorem proves full complex-translation differential-algebraic freeness on
arbitrary prescribed entire divisors. Finite jets, hypertranscendence, and translation freeness can
be scientifically strong while remaining orthogonal to zero location. Any RH use must couple such
complexity to Euler/Gamma source, positivity, ground selection, or a divisor-sensitive boundary
law. Merely proving a source is maximally nonalgebraic cannot distinguish RH from non-RH divisor.
New scalar-monodromy theorem strengthens algebraic side: arbitrarily many distinct monodromy
multipliers force moved germ transcendental over fixed subalgebra and yield pairwise algebraic
independence with a fixed germ. Without Xi-typed source coupling this remains admissibility, not
zero-location mechanism. Evidence is `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean`.

Period escape proves noncompact period quotient for hypertranscendental meromorphic elements; Rolle gives multiplicity-exact zero descent; Voros identifies regularized `-xi'/xi` coefficients, not zero
sums or positivity. Arithmetic hard cells give positive-density phase avoidance; exact rational
all-order anomalies have every maximal proper subcontext PSD but full kernel indefinite, alongside
a PSD Wilson sector with noncommuting loops. They supply no Euler--Gamma sign or new RH route.

### Reciprocal-scale data has a sharp RH-sensitivity firewall

Positive generalized-prime perturbations of reciprocal abscissa at most `1/2` cannot move zeros
in the right half-strip, while for every `beta>1/2` arbitrarily small reciprocal- and Mertens-mass
perturbations can create zeros on `Re(s)=beta`. Arbitrarily regular generalized-integer counts can
coexist with off-line zeros; log-lattice systems have no power saving. Functional equation, order,
and reality are separately blind: a symmetric quadratic inserts an off-line real pair, whereas
positive-prime realizability fails exact balance/trace tests. Thus a continuous criterion using
only `1/p`, `Lambda(n)/n`, Mertens windows, finite log-jet Grams, or integer-counting regularity
cannot select RH. A live arithmetic route must see the half-power scale, a discontinuous source
invariant, or a genuinely joint functional-equation/positive-measure mechanism.

### 8. No serial super-route exists

C1, D2, E, G, L, O, P, Q, T, U, and CCM-FU share connectors but have different admission and
producer theorems. Combining endpoints does not multiply evidence. Merger becomes mathematical
only when one literal source map transports open premise of one route into producer of another
without assuming RH-equivalent orientation.

Route U now supplies one such literal identification, but not a proof: after forced `2*pi` scaling,
its closed source quadratic is exactly twice full CCM restricted-Weil quadratic and its form map is
onto. O, G-floor, and U therefore attack one operator wall at three resolutions—whole-ground
coercivity, global Morse index, and first hard-edge contact. Their obstacles are compatible pieces
of one possible architecture: classify first negative direction, prove it lies in prolate
ground/near-ground normal form, then exclude it by U's compact-source no-birth law. Missing step is
source-relative classification/coercivity, not another equivalence between their endpoints.

### 9. Two-dimensional carrier structure can be intrinsic

Periodic-pencil corpus proves every nondegenerate boundary wedge has intrinsic
hypertranscendental realization dimension exactly two, while faithful facet separation dimension is
four; one complex coordinate is impossible. Together with P's phase-unstable two-leg cup and U's
even/odd split, this warns that scalar collapse can destroy source geometry rather than simplify it.
This is an admissibility law for future architectures, not an Xi-typed route by itself.

Latest differential-field theorem gives geometric form of same warning. For one
hypertranscendental scalar, first-derivative horizons are faithfully indexed by projective
denominator covectors; two distinct horizons generate whole source field and intersect exactly in
Schwarzian field. Ordered boundary pairs, not one scalar observer, recover source. Separately,
`g^2=1` forces `g=+-1` only in coefficient hosts without nontrivial idempotents; product/operator
hosts carry additional involutions. Neither generic theorem is Xi-typed, so neither is new route,
but future two-sheet/projective architectures must preserve this host and boundary-pair data.
Evidence is `HTGeometry/ProjectiveHorizonCelestialSphere.lean` and
`HTGeometry/InvolutionIdempotentHost.lean`.

### 10. Vanishing mass can retain decisive boundary sign

Route O's endpoint slope and total mass live on different scales. Route U's super-apex outlier can
have vanishing quadrature weight and disappear from every fixed moment while retaining negative
Hausdorff sign. Weak convergence, fixed-degree moments, or one-scale recession therefore cannot
classify near-ground/first-loss states. Exhaustion must retain boundary location, weight, and flux
at their natural scales.

### 11. Phase concentration is singular, not Sobolev-generic

Independent product phase seeds have exact small collision moments and regularized collision
polynomials, but return incidence lies on a singular phase graph. Corpus proves restriction to that
graph is unbounded below half-dimensional Sobolev threshold. Finite collision concentration can aid
admissibility; no subcritical Sobolev hierarchy can justify Route E's source-fixed Hall relation or
select a spectral ground state.

Finite endpoint-sheared transform is exactly a Gram entry, hence PSD and Cauchy--Schwarz controlled,
but endpoint-swap parity requires physical source Gram to be real, not merely Hermitian. Explicit
two-point complex Gram violates ridge equality. Therefore odd endpoint annihilation cannot be
deduced from Hilbert positivity alone; routes using it must prove real-source structure before
frequency fusion. Evidence is `EndpointShearedGramRidgeParity.lean`.

### 12. Cofinal completed sources require growing index or boundary normalization

CCM relative logarithmic derivatives acquire one negative Cauchy square per active Fourier
coordinate, while Route U physical atoms shrink to ordinary residue `O(1/y)` but retain fixed
Julia-normalized charge. Fixed-index scalar backgrounds and unweighted boundary limits therefore
lose exactly structure that survives cofinal completion. Lawful limits must carry growing
indefinite index, operator-valued covariance, or invariant angular derivative.

### 13. False-RH obstruction is width-sensitive quadratic concentration

Q and U now share an exact concentration primitive. A line-conjugate off-line pair has zero signed
Poisson mass but squared frequency energy `pi*y^2/(b*(b^2-y^2))`, which blows up at transverse
wall. Q's null-axis diagonals likewise vanish while mixed incidence stays `-E/2`; U's first contact
is invisible to every strict interior source and lives at completion boundary. First moments,
diagonal energies, weak limits, and pointwise source bounds can all erase obstruction by shrinking
its width. A viable Q--U merger would construct one pre-divisor arithmetic quadratic energy,
prove finite cofinal source budget, and show nondegenerate domination of both continued-Cauchy and
Christoffel boundary profiles. Exact profile theorem exists; source energy and shadow maps do not.
This is a candidate bridge, not a new independent route.

### 14. Finite-dimensional observers cannot resolve replica proliferation

Ordered replica law pushes exactly to multiplicity histograms. In a fixed `d`-dimensional observer
space, volume packing and vector central-cell estimates force distinct high-order multiplicities
to have nearby observed actions; explicit crowding floor eventually exceeds collision budget after
soft-light flattening. The same close pair gives a nonzero balanced character with small observed
action, so transversality tail cannot be made uniformly small by tuning constants. Collective
Hamiltonian centralizer dimension is exactly histogram collision probability, and annealed
dephasing removes oscillatory off-diagonals but retains invariant codimension floor. Any replica-
based successor must increase observer dimension, retain noncommutative labels, or use singular
incidence; more scalar annealing cannot produce source separation. Return-sector excision also
fails to commute with convolution: lost term is exactly twice mixed
off-return product, another instance of decisive incidence erased by early projection.
Evidence is
`HTGeometry/OrderedReplicaPushforward.lean`, `HTGeometry/EuclideanPackingPigeonhole.lean`,
`HTGeometry/VectorLawCentralCellCrowding.lean`, `HTGeometry/ReplicaObserverActionCrowding.lean`,
`HTGeometry/SoftLightFilterCollisionBound.lean`,
`HTGeometry/ReplicaCrowdingCollisionAssembly.lean`,
`HTGeometry/PackingScaleBinomialBound.lean`,
`HTGeometry/BalancedCharacterTransversalityTail.lean`,
`HTGeometry/HistogramCentralizerDimension.lean`, `HTGeometry/SpectralResponseVectorBound.lean`,
`HTGeometry/SignedReplicaConvolutionLift.lean`, and
`HTGeometry/QuenchedCentralizerPropagatorSplit.lean`, and
`HTGeometry/AnnealedSpectralDephasing.lean`.

## Candidate architectures not yet routes

### CCM-HG — completed-source Hankel boundary relative trace

`CCMBoundaryRelativeTrace.lean` constructs boundary carrier itself. For a one-sided
output cutoff, squared boundary-block mass is unconditional `ENNReal` integral with antidiagonal
weight `min(t,u)`; under sole leak-profile hypothesis it is finite, equals Hankel-gap decrement,
and splits into local corner plus cutoff-interface energy. Corner is first-order negligible and
complete initial density crosses interface. Incoming pole trace is exactly `4(1-exp(-u))`. For
every finite right-half divisor packet, initial density is exact positive Cauchy residue energy,
and density at most four holds exactly when a strict-right packet is empty. Thus both positive
carrier and sharp finite-packet exclusion law are Lean-proved without a trace-class premise.

`CCMTwoChannelGraph.lean` also constructs canonical closed paired graph of source multiplier,
splits Cauchy pole exactly, computes residue-vector energy `|c|^2/(2 Im w)`, and gives bilateral
atom factorization. Thus a coefficient-faithful logarithmic two-channel carrier exists; missing
object is source-derived endpoint density/slope law, not graph closure. Conversely,
`CCMRelativeLogDerivCoordinateIndex.lean` proves every active Fourier coordinate contributes one
negative Cauchy square and any cofinal Xi-carrying relative determinant needs linearly growing
negative index. No fixed-index scalar relative background can absorb completed source.

Gamma-damped Cauchy synthesis is now a positive channel-resolved Hilbert--Schmidt frame: trace is
additive without deleting off-diagonal covariance. Exact Euler-log diagonal is obtained by bounded
positive Radon--Nikodym correction, but critical von-Mangoldt correction grows cofinally like
`(log p)p^(k/2)` and cannot live in same bounded frame. Distinguished Sonin compression plus
archimedean relative channel and trace-slope domination are exact remaining carrier theorem.

Sonin three-grade carrier is now algebraically forced rather than schematic. Lean proves exact
projection-compressed commutator split into internal commutator plus polarized leakage, and exact
projection/resolvent correction factors every position anomaly through one edge commutator. It
also proves observability allocation: finite Euler directions invisible to scalar jet inject into
relative state, so bounded scalar jet depth forces cofinally growing relative negative index.
These close algebraic splitting and finite-dimensional index bookkeeping. They do not construct
closed principal--relative carrier, rigged Sobolev edge pairing, cyclic finite-part descent,
cofinal contraction, or index-preserving source transport.
Principal new evidence is `CCMSoninCompressedCommutator.lean`,
`CCMSoninEdgeCommutatorAlgebra.lean`, and `CCMEulerObservabilityAllocation.lean`.

The FU-to-UR curvature transport supplies a canonical leak pair, now exact in Lean. Fast and slow
positive exponential channels are valid leak profiles; their signed HG boundary-relative trace is

```text
(3/32)(exp(-u/2)-exp(-u)) > 0,
```

bounded sharply by `3/128` with equality at `u=2 log 2`. This removes arbitrary leak-profile choice
and proves a scalar positive boundary pulse. Four-unit normalization still undershoots the incoming
pole boundary trace by the exact positive square `4(1-exp(-u/2))^2`; it cannot by itself discharge
HG's sharp four-unit exclusion. Moreover it cannot be upgraded to the proposed EP positive
operator covariance: every separated two-sample compression has strictly negative determinant.
HG therefore remains a scalar-trace candidate requiring an additional literal completed-source
channel, while this particular UR-to-HG/EP closure is negative. Evidence is
`CCMUnitRieszHankelBoundaryPulse.lean`.

The literal unit-Riesz source now supplies a different canonical object: a positive exponential
increment Gram whose diagonal trace is exactly prime coherent energy and whose completed trace is
that energy minus `(2/3)sqrt N`. This avoids the fast-minus-slow two-sample determinant failure at
the prime-frame level. It still does not prove HG's boundary-density `<=4` law: a lawful HG advance
must transport the full prime-plus-polar operator frame into boundary relative trace and identify
the divisor-side density, not retain only its scalar trace.
The source-side norm needed by such transport is now exact. Four-lag coherent packets satisfy
`G_lag=integral(4|g'|^2+|g|^2)=4 c^T K c`, whereas no finite constant controls their fixed sample by
bare polar `L2` energy. This makes HG's boundary slope/generator channel structurally forced. The
packet-level identification is now exact: `ell=2g'+i g` is an admissible complex leak profile and

```text
lim_(u->0+) boundaryRelativeTrace(ell,u)/u = 4 c^T K c.
```

On this coherent family, HG density `<=4` is equivalent to source-Gram energy `<=1`, and a positive
multiple of the boundary slope recovers the fixed sample. The open theorem has narrowed to a
linear/cofinal extension from codiagonal packets to the literal completed prime-minus-polar source,
together with its arithmetic source-Gram unit-ball bound.
The need for “codiagonal” is now exact rather than architectural. Prime tail charge is
`E_prime/2`, polar tail charge is `E_polar/2`, and completed tail charge is
`R_1(log N)/2`. Unless this charge vanishes, direct completed amplitude is not an HG leak profile.
Lawful HG carrier must be a relative pair: charge-free graph leak plus boundary counterterm that
still records `R_1`.
That pair is now constructed. `Delta_h C_N` has exact decaying tail, admits a closed continuous HG
profile, and its translates telescope to `R_1(log N)/2-C_N(u)`; at `u=0` they recover exactly
`R_1(log N)/2`. Hence HG carrier construction and source-faithfulness are closed for this unit-Riesz
source. Moreover aperture-matched codiagonal collapses infinite reconstruction to uniformly
conditioned samples at `0`, `log N`, and `2 log N`, with explicit coefficient bound `1,48,16`.
Remaining theorem is quantitative boundary-density/graph control of those three samples. Generic
leak-profile integrability is still too weak, but divergent counting-measure dual is no longer an
obstruction.

A second canonical HG carrier is now available directly from literal source, without summing the
codiagonal orbit. Prime outgoing charge is finite von-Mangoldt tail sum; polar outgoing charge is
retained as its continuum integral and evaluates to `sqrt N/3`; their difference is exactly
`R_1(log N)/2`. The outgoing profile

```text
ell_N(u)=(R_1(log N)/2)exp(-u/2)
```

is an HG leak profile with density and gap `(R_1(log N)^2/4)exp(-u)` and boundary trace
`(R_1(log N)^2/4)(1-exp(-u))`. Hence domination by incoming pole packet
`4(1-exp(-u))` for all `u>0` is equivalent to `R_1(log N)^2<=16`; same condition follows from
initial slope. This closes literal profile construction but also proves a scalar-rigidity no-go:
HG aperture dependence supplies no cancellation because source and pole traces are collinear.
Missing science is independent CCM contractivity of outgoing coefficient from bulk/ground
coupling, or a genuinely operator-valued source order. Rechecking scalar trace shapes cannot
advance route.

Receiver side is now terminalized. `CCMUnitRieszLogLatticeHandoff.lean` proves no-loss passage from
uniform natural-log bounds to a global resolvent bound, and
`CCMUnitRieszResolventRHCriterion.lean` proves this bound yields a holomorphic regularized defect
and RH. Its final theorem states directly that pole domination of all literal integer outgoing
blocks implies RH. Thus HG's only missing theorem is independent production of that domination;
there is no remaining lattice, Abel, Landau, or divisor-selection task.

`CCMUnitRieszSharpPoleClassification.lean` now proves reverse direction too, quantitatively and
without zero computation. Thus HG's canonical sharp condition is an unconditional equivalence,
not merely receiver. This closes question whether constant four might be easier auxiliary bound:
uniform sharp domination itself is RH. Open core moves strictly upstream to non-circular
source-selected contractivity or operator-valued order before scalar trace.

It is not yet a route. Missing theorem must construct one canonical completed-Xi leak profile from
literal Euler--Gamma source before divisor selection, prove the profile hypotheses and source-side
boundary-density bound `<=4`, and identify its divisor-side density strongly enough that any
off-line finite packet violates that bound. No current theorem maps this infinite completed source
trace to `RiemannHypothesis`. Shift-covariant scalar transfer cannot provide missing step: its norm
is at least total divisor multiplicity, so one FE pair already exceeds contractive budget. The
lawful opening is source-selected non-covariant/commutator transport into the now-constructed
boundary relative trace, not another finite residue calculation.

### CCM-BS — finite-peripheral Birman--Schwinger reduction

This is a new exact mechanism inside Route O/G-floor/U source, not independent eleventh lettered
route. Lean constructs actual compact self-adjoint Birman--Schwinger pencil on complete Gamma form
domain and proves exact equivalence between fixed vectors and literal restricted-Weil eigenvectors.
Energy changes pencil affinely by positive Gamma--Slepian Gram.

At zero energy form is `I-K_a`. Compact spectral reduction gives closed reducing exterior with
strict coercivity and finite-dimensional peripheral orthogonal block; mixed form vanishes. Whole
restricted-Weil positivity is equivalent to positivity on this finite block, and equivalent to
vanishing of its above-one dangerous eigenspace. Exact Schur complement exists, but reducing
version shows no coupling tax is intrinsic.

Gamma--Slepian Gram is positive compact injective, has norm below one, and its eigenspaces form a
complete Hilbert sum. The newer source factorization selects, for every `delta>0`, a finite
Gamma--Slepian head with coercive exterior and an arbitrarily accurate head lower bound. Any
nonpositive whole-space vector then produces a nonzero head vector on which literal finite
von-Mangoldt compression overcompensates identity plus scalar Gamma and rank-two polar by
`1-delta`. Missing theorem is the source-specific reverse inequality, cofinally. Finite reduction,
source alignment, conditioning escape, and fixed-loss removal are closed; the arithmetic sign is
not. CCM-BS is whole-ground selection inside O/G-floor/U, not a new source or endpoint.

### CCM-GS — cofinal ground-separating incidence

Lean proves fixed-cutoff compressed prime channels have separating vectors on open dense locus,
prime-power labels are distinct, the Weil floor is concave and Lipschitz in coefficient source, and
simple-ground response has negative-semidefinite reduced-resolvent Gram Hessian with exact divisor
readout. It also proves crowding law: separating margin is at most half squared nearest-channel
distance times generator energy. Prime-free aperture already has symmetric real characteristic
pair, so real characteristic roots alone are not arithmetic ground selector.

The common unit-Riesz source now has a canonical nongeneric separating frame. Exponential
half-line states have overlap `exp(-|x-y|/2)`; the physical Riesz atom is their squared increment
distance. The increment Gram has an exact strictly positive two-lag determinant whose crowding
factor is `1-exp(-Delta/2)`. Thus source-side two-atom incidence is automatic and quantitatively
priced. This does not prove the true CCM ground avoids its incidence seam: the missing object is an
index-preserving source-to-ground comparison retaining that determinant through cofinal crowding.
Moreover separation alone does not control leverage: four-lag source packets remain strictly
Gram-positive while concentrating a fixed evaluation beyond every polar-energy budget. Their
exact graph energy equals four times source-Gram energy. Cofinal GS separation must therefore be
quantitative in generator/source-Gram norm, not merely open-dense nonvanishing.
The graph norm now has an exact HG realization by the leak `2g'+i g`; fixed sample is an explicit
positive multiple of its boundary slope. This closes receiver design for finite coherent packets,
but not the cofinal margin: GS must show true ground incidence is bounded by the same transported
boundary/source norm under prime-log crowding.
Moreover literal source response carries nondecaying charge `R_1(log N)/2`; GS graph transport
must separate this one-dimensional boundary coordinate before measuring cofinal incidence. Treating
it as ordinary bulk norm makes the source nonintegrable, while discarding it deletes arithmetic
readout.
Shift codiagonal now performs this separation canonically and reconstructs charge from translated
bulk. At step `log N`, rank-two tail eliminates orbit and recovers charge from three uniformly
conditioned samples. GS may therefore formulate cofinal margin on finite observed bulk plus one
boundary coordinate. Still missing is quantitative incidence inequality controlling those three
samples; open-dense separation alone gives no magnitude bound.
That boundary coordinate now has a literal one-dimensional HG realization:
`(R_1(log N)/2)exp(-u/2)`. Its total energy is coefficient square and pole domination is exactly
`R_1(log N)^2<=16`. GS therefore need not discover a boundary norm, but must prove true CCM ground
contracts this coefficient through nontrivial incidence with remaining bulk. Rank-one block by
itself is circular and cannot turn generic separation into quantitative control.
Uniform contraction of these blocks is now Lean-equivalent to RH in both directions. GS margin
must therefore arise before scalar outgoing projection, from genuine cofinal ground incidence.
Any argument beginning with uniform scalar block contractivity has already assumed terminal
theorem in equivalent form.

Generic graph-local algebra has advanced but does not change this verdict. Connected two-local
Pauli generators span the full traceless Lie algebra, fixed-edge Hall expansion is exact modulo
the collective commutant, and a self-adjoint family common kernel is the orthogonal complement of
the span of its ranges. Adjoining the common-kernel projector makes simultaneous kernel trivial,
but that projector is source-derived only when arithmetic construction supplies it. All-replica
Pauli conjugations preserve completed family, greatest obstruction, singlet sector, and its
orthogonal complement. On singlet input, distinct edge-word commutator images carry distinct
conjugation characters; any conjugation-stable subspace containing their sum contains every image
separately. Reduced obstruction splits into singlet/nonsinglet layers and nonsinglet layer
reproduces in one generator step; mixed Hall assembly still requires output-independence and
kernel-recovery hypotheses rather than proving them arithmetically. Generic completion, character
detection, stabilizer incidence, and scalar-centralizer rigidity therefore provide a GS toolkit,
not missing Xi-typed quantitative margin or arithmetic source-to-ground comparison.

It is not yet a route. Missing theorem must prove true CCM ground, not generic vector, stays outside
incidence seam with quantitative cofinal margin; pay prime-log crowding by controlled generator
growth; combine margin with reduced-resolvent/Mellin norms; and preserve divisor or complete Weil
positivity through limit. No completed source-to-RH implication with these premises exists in Lean.

### CCM-UR — unit-Riesz completed-current smoothing

Corpus constructs a positive unit-Riesz profile as a cumulative distribution with sharp tail
`1-W(exp(v))<=3 exp(-v)`, exact layer-cake/quadrature defect, and atomic Markov transform

```text
D(z)=3 z zeta(1+z)/(2(z+1)(z+3/2)),   D(0)=1.
```

Its coefficient transform exposes zeta plus logarithmic derivative, and every off-critical zero
remains a genuine pole with explicit residue. New Lean factorization shows its pole-filled
coefficient is a zero-free rational multiplier times the regularized completed critical-Mellin
defect plus an analytic source-free correction. The correction is strictly negative and lies
between `-(t+4)exp(-t)` and `-2exp(-t)`. More decisively, the literal finite-aperture Stieltjes
response is exactly a difference of two exponentially weighted moments of the completed
prime-minus-polar error; no Möbius coordinate remains.

Paper-level Laplace uniqueness completes the time-domain weld: the old Markov--virial coefficient
is positive two-exponential smoothing of `exp(-t/2)dE` plus that negligible negative correction.
Thus its all-epsilon lower estimate is equivalent, with no exponent loss, to a completed-current
lower law. CCM-UR and CCM-FU have the same literal source but different reporters: translation-
invariant two-exponential smoothing here, polynomial cumulative/Cesàro smoothing in CCM-FU.
Lean now proves literal reporter transport itself: two genuine absolutely-continuous integrations
by parts identify completed-error unit-Riesz response exactly with endpoint term plus curvature
pairing against actual CCM-FU Cesàro primitive, without differentiating prime staircase. Subsequent
log-lattice and resolvent theorems close the continuation-to-RH endpoint; only arithmetic lower
estimate remains unproved.
Transport through CCM-FU Cesàro primitive proves one-way ordering: FU's absolute
linear bound controls UR, but UR annihilates affine drift and detects signed second-order curvature,
so no reporter-only converse exists. Its normalized kernel has one sign wall tending to
`log 16=4 log 2` and a trace/barycenter-neutral fast-minus-slow two-channel limit. After
`t>log 4`, the literal test is not a positive autocorrelation. Thus Route O/G scalar ground
positivity cannot close UR; any merger must retain signed two-channel orientation. Lean now proves
this derivative algebra, exact fast/slow moments, four-unit wall, and two-unit loss of origin
monotonicity; only the arithmetic lower law remains unproved.

Literal-source composition is now stronger than earlier Laplace-level identification.
Substitution of completed-error Volterra law cancels fast source channel exactly and Lean proves,
pointwise for `t>=0`,

```text
U(t)=3(t-3)exp(-t)+8exp(-3t/2)
     -(3/2)exp(-t/2)R_1(t),

R_1(t)=exp(-t) integral_0^(exp t) (psi(y)-y)y^(-1/2)dy.
```

Exact `0<y<1` tail is `-2/3`. Hence every UR lower bound is exactly oppositely oriented upper
bound for existing unit CCM aperture resolvent, with no exponent loss. Aperture-resolvent
Riesz-sector gate and CCM-UR are therefore one arithmetic frontier, not two. This removes Laplace
uniqueness from literal source identification but does not supply common all-epsilon source bound.

At every integer aperture `N>=1`, the same source now has exact coherent trace form

```text
R_1(log N)=E_prime(N)-E_polar(N),
E_prime(N)=1/sqrt N sum_(2<=n<=N) Lambda(n)
  ||v_(log N)-v_(log n)||_2^2,
E_polar(N)=1/sqrt N integral_0^N
  ||v_(log N)-v_(log y)||_2^2 dy=(2/3)sqrt N,
v_x(s)=1_(x<s)exp(-(s-x)/2).
```

This is Lean-proved from the literal Chebyshev staircase, not introduced as an abstract diagonal
model. Its off-diagonal increment kernel is a positive Gram and separates every distinct two-lag
packet with an exact crowding determinant. Therefore prime positivity and source separation are no
longer missing. Bare domination of an atomic projector by the explicit polar frame is now ruled
out: even at fixed lag one, finite coherent source packets violate every finite Loewner constant.
The exact survivor is first-order lag graph energy, equal to four times source-Gram energy. The hard
arithmetic/core operator problem is therefore either signed prime-minus-polar cancellation itself
or graph-bounded transport of that discrepancy into actual CCM ground/boundary positivity.
The source now also exists as one literal signed `L2(R)` barycenter at every finite integer
aperture. Its incoming half is exactly the moving square-root-weighted von Mangoldt discrepancy;
its outgoing half is `(R_1(log N)/2) exp(-s/2)`. Total energy splits orthogonally into incoming
bulk plus squared resolvent boundary energy. Carrier construction is therefore closed without
assuming the scalar charge vanishes. Missing theorem is a source-specific quantitative order
between incoming bulk and outgoing boundary, not another Hilbert realization.
Finite coherent graph-bounded transport into HG is now exact: `g -> 2g'+i g` sends total leak
energy and initial boundary slope to `4` times source Gram, and recovers fixed evaluation. The
remaining UR problem is wholly arithmetic/cofinal: extend this packet isometry to the literal
completed source while retaining its prime-minus-polar sign and prove source-Gram energy `<=1`.
Exact tail classification shows naive extension is impossible: completed coherent response tends
to `R_1(log N)/2`, and direct amplitude fails HG integrability whenever this value is nonzero. UR
must apply a canonical aperture/codiagonal difference whose removed constant is carried as boundary
flux. This constant is not nuisance renormalization; it is half the literal UR resolvent.
This demanded object is now Lean-proved. For every positive step, shift codiagonal is an HG
`LeakProfile`, and exact telescoping at zero reconstructs
`R_1(log N)/2` as infinite sum of translated codiagonal values. Carrier and no-loss problems are
closed. Infinite discrete integration is subsequently eliminated: logarithmic-step two-mode tail
recurrence expresses charge through only three codiagonal samples with aperture-independent
conditioning. Arithmetic frontier is now source-specific subpower control of those samples from
literal prime-minus-polar covariance; generic weighted `L2` admissibility still does not supply
point evaluation.

Literal outgoing projection further collapses observations into canonical rank-one HG block. Its
coefficient is exactly `R_1(log N)/2`, total HG energy is its square, and all-aperture pole
domination is exactly `R_1(log N)^2<=16`. Thus HG formulation does not prove UR lower law; it is an
equivalent scalar normalization of same arithmetic frontier. Useful new target is source-derived
contractivity of outgoing projection before scalarization. The no-loss natural-log handoff and
analytic continuation to RH are now unconditional Lean theorems, so no downstream Landau premise
remains.

Suzuki Green reverse direction and sharp constant are now formalized. RH bounds exact Xi screw
hull by `58/625` and gives `|R_1(log N)/2|<2`; conversely uniform sharp pole domination forces RH.
UR's scalar rank-one receiver is therefore exactly RH-equivalent. Surviving producer remains signed
prime-minus-polar cancellation or operator/ground contractivity with provenance retained before
trace; no reporter, lattice, Green, or Landau completion remains.

The surviving producer can be written as a signed lower bound for that completed-current response,
equivalently the original causal complement:

```text
<h0,K_T> >= -C_epsilon exp(-(1/2-epsilon)T).
```

It is not an independent route under this map's definition: source-level completion collapses it
onto CCM-FU. Lean now formalizes wavelet compensation, renewal/frontier algebra, Markov--virial
split, pole margin, the exact log-lattice handoff, continuous resolvent continuation, and the
resolvent-to-RH implication. No downstream Laplace uniqueness, Landau, lattice, or residue theorem
remains missing; only the source-side signed lower/contractivity estimate is unproved. Generic
coisometry and uniquely
Möbius first-crossing interpretations are retired. Only a signed inequality for the common literal
completed current advances it. Principal new evidence is
`CCMUnitRieszCompletedSourceWeld.lean`, `CCMUnitRieszApertureResolventWeld.lean`,
`CCMUnitRieszExponentialCoherentTrace.lean`,
`CCMUnitRieszCompletedCoherentBarycenter.lean`,
`CCMUnitRieszCoherentPolarSamplingNoGo.lean`,
`CCMUnitRieszCoherentRelativeCarrier.lean`,
`CCMUnitRieszFiniteBoundaryReadout.lean`,
`CCMUnitRieszOutgoingChargeHankel.lean`, `CCMUnitRieszLogLatticeHandoff.lean`,
`CCMUnitRieszResolventRHCriterion.lean`,
`CCMUnitRieszSuzukiGreenProducerClassification.lean`,
`CCMUnitRieszSharpPoleClassification.lean`,
`CCMUnitRieszWaveletFrontier.lean`, and
`CCMUnitRieszVirialConnector.lean`, together with `CCMUnitRieszCesaroCurvature.lean` and
`CCMUnitRieszFUCurvatureTransport.lean`.

### CCM-RF — rectangular adjacent-block floor

This candidate has a complete Lean endpoint and a newly isolated source reporter. For every fixed
width `L>0`, one logarithmically sampled rectangular two-edge Weil family is nonnegative under RH
and cofinally unbounded below under false RH. Hence mere eventual lower boundedness is equivalent
to RH. The sharp Guinand--Weil formula identifies each sample with an explicit finite von-Mangoldt
autocorrelation plus completed Gamma term. Stieltjes autocorrelation then reduces its moving part
to one signed Haar coefficient of the completed critical-Mellin error:

```text
integral_[c,c+L] R(h) dh - integral_[c-L,c] R(h) dh.
```

Lean now also formalizes moving-tent support, two-edge overlap, adjacent-block identity, Haar-shell
localization, and uniform two-translate quadratic bound. This removes window algebra and gives an
exact finite-shell target. It does not prove any lower floor: separate absolute prime and polar
bounds lose their square-root-scale cancellation.

**Open core.** Construct one unconditional positive, source-first cross-scale synthesis proving an
eventual lower bound for that fixed adjacent-block imbalance while retaining prime and polar
channels jointly. Direct compact/coisometric critical transfer is excluded by mass escape. Because
the reporter is another functional of the same completed current driving CCM-FU and CCM-UR,
CCM-RF is a candidate opening, not an independent live route. Principal evidence is
`CCMRectangularWeilCompleteness.lean`, `CCMPrimeGammaSourceEnergySpectrum.lean`,
`CCMRectangularStieltjesAutocorrelation.lean`, and `CCMRectangularTentFloor.lean`.

### CCM-EP — dephased Euler--Pick boundary transfer

Finite even real-rooted spectral factors have positive logarithmic-derivative Pick kernels: each
paired zero is exactly sum of two rank-one Gram kernels, and finite PSD cone is closed under
entrywise limits. `CCMEulerPickTransferBoundary.lean` also isolates exact obstruction. Canonical
CCM aperture phase subtracts `2a` times right-half-plane Cauchy kernel; periodic background is
finite-aperture indefinite but exponentially invisible on every strict Euler half-plane. Relative
determinant is Herglotz for nonnegative periodic Fourier coefficients, yet scalar cofinal
Herglotz transport is paper-proved incompatible with Xi growth. Any successful limit must become
signed or operator-valued.

Candidate chain is

```text
actual finite CCM real spectra
  -> source-derived dephased log-derivative convergence across Re(w)=1/2
  -> complete Euler Pick positivity
  -> RH.
```

Missing theorem is not generic PSD closure. It is literal completed-source convergence through
the half-strip boundary, or positive operator-valued background covariance recombining aperture
defect. Current Lean module formalizes paired-zero kernel, PSD-limit transfer, phase/background
laws, and Herglotz sufficiency; it does not instantiate actual cofinal CCM factors or give a Lean
source-to-RH endpoint. Hence CCM-EP is candidate, not live route.
The canonical FU-to-UR fast/slow pair no longer supplies an EP positive-background candidate:
although its scalar boundary pulse is strictly positive, its two-point covariance determinant is
strictly negative at every positive aperture and nonzero separation. Any surviving EP background
must add genuinely operator-valued completed-source structure beyond this rank-two difference.
Dephased determinant convergence and divisor preservation are still absent.
The unit-Riesz coherent increment kernel supplies one canonical positive operator-valued prime
frame, but its exact completed trace subtracts `(2/3)sqrt N` polar energy. Thus it is a lawful EP
input only if boundary transport recombines that polar channel without scalarizing or erasing the
prime off-diagonal Gram. No such dephased divisor-preserving convergence theorem is known here.
Bare-polar strong convergence is now known to be insufficient even on finite source packets: fixed
sampling is unbounded relative to polar response energy. The exact positive survivor is the
first-order graph/source-Gram norm. A lawful EP limit must therefore converge in that graph norm or
preserve an equivalent boundary generator; `L2` polar convergence alone cannot preserve divisor
evaluation.
There is now a canonical finite-packet operator-valued realization of that requirement: complex
graph leak `2g'+i g` has modulus-square equal to graph density and HG boundary slope equal to four
times source Gram. EP may use this as its finite-stage graph topology, but must still prove
dephased divisor-preserving cofinal convergence for the literal completed source; packetwise norm
identification alone does not repair aperture phase defect.
The completed coherent frame additionally has a one-dimensional nondecaying tail charge exactly
`R_1(log N)/2`. Thus any EP dephasing that merely subtracts constant tail erases arithmetic
resolvent. Surviving operator-valued background must retain this charge as explicit boundary block
while dephasing only bulk graph component.
Canonical bulk/boundary block is now available: `Delta_h C_N` is closed and HG-admissible while
its translation series reconstructs exactly `R_1(log N)/2`. EP can therefore dephase bulk without
source erasure. Exact two-mode elimination further expresses boundary block through three bulk
samples with uniform conditioning. What remains is operator-valued Pick/positive-background
control of those finite samples; scalar PSD closure or profile integrability supplies no pointwise
magnitude estimate.
Literal outgoing boundary block is now explicit and positive: it is rank one with scalar profile
`(R_1(log N)/2)exp(-u/2)` and covariance density
`(R_1(log N)^2/4)exp(-u)`. This supplies lawful EP boundary bookkeeping, but scalar pole domination
is exactly `R_1(log N)^2<=16` and hence cannot be used as its own producer. EP must retain
prime/polar operator provenance or couple this block to dephased bulk covariance before taking
trace; otherwise positive-background language merely repackages unresolved arithmetic bound.
This scalar statement is now two-sided: uniform pole domination holds under RH and implies RH.
EP cannot use scalar positivity plus sharper constant as intermediate lemma. Only operator-valued,
divisor-preserving dephasing before scalar trace can remain non-circular.
Poisson--Jensen analysis makes receiver boundary explicit: half-unit seam creates nonnegative outer
defect whose vanishing is shifted RH. Dephased real-spectrum logarithmic graph is identically zero,
whereas Xi transverse graph vanishes exactly under RH; graph-core convergence from real finite
factors to Xi is therefore already RH-equivalent. Lawful producer must preserve transverse charge
at finite stage or use divisor-preserving determinant/floor convergence, not convergence of zero
log graphs.
Using all unused four-unit pole slack cannot supply the missing positive background. For every
positive aperture, every normalized one-channel rank-one repair in the actual fast/slow span needs
at least full slow mass `B_u`, while available slack is only
`S_u=(1-exp(-u/2))B_u<B_u`; a separated two-point compression remains indefinite. Higher-rank,
nonlocal, or additional completed-source covariance remains possible.

### SP-E — prime--Gamma signed-permutation Eulerian limit

This non-CCM candidate is now a concrete determinantal architecture. Scalar specialization through
known Visontai--Williams type-`B` ascent/descent-top signature is dead: words `3142` and `3241`
have same signature but different adjacent edges, forcing every compatible positive edge kernel to
zero four-label multiplicative curvature and hence rank-one separation. Order-blind scaling also
has vanishing normalized quadratic coefficient, incompatible with theta source.

Positive survivor is Pluecker lift. Corpus exhibits nonzero Boolean first-trace insertion curvature
before scalar boundary realization. For edge matrix `K`, rank-two Hermitian pencil has determinant
`det(K)^2 z w`; its normalized Gram determinant
`det(I+u K K^T)=1+S(K)u+det(K)^2u^2` has only negative real zeros, with squared curvature exactly
retained. Lean proves source path discrepancy, scalar annihilation, top-fibre collision/rank-one
no-go, stable curvature pencil, discriminant factorization, and negative-root law. Thus finite
stability can retain completed source curvature, but only matrix-valued before scalarization.

`PrimeGammaUniformBooleanGramQuadraticNoGo.lean` closes literal uniform Boolean Gram metric
negatively. For every finite prime prefix
its normalized quadratic coefficient is at most `13/98`, while completed theta-moment
log-convexity forces Xi square-coordinate ratio to be at least `1/6`. No scalar normalization can
repair mismatch. Any surviving Pluecker carrier must reweight or rotate curvature columns in a
nonuniform completed Gamma/co-Poisson metric before taking Gram determinant.

The first source-derived unit-diagonal nonuniform metric block is exact. Route P's cubic Cauchy/Hellinger
coherence and Route E's balanced two-column load chi-square are related by
`Delta_3=chi(3-3chi+chi^2)`, with `chi<=Delta_3<=3chi`. Iterating Route P's canonical primitive
depth-square map twice gives frequency ratio four, hence `chi=9/25` and unit-diagonal normalized
Gram ratio `11529/62500 > 1/6 > 13/98`. This clears the former local degree-two floor without Xi
coefficients or zeros only after unit normalization.

That normalization cannot be silently imported into source assembly. Coefficient-faithful
fourth-depth transport has partner diagonal `w/64`, so its exact weighted ratio is
`737856/66015625 < 13/98 < 1/6`. Equal-diagonal restoration forces unique nonnegative amplitude
`8` and adds exact trace `63w/64`. Thus raw canonical fourth-depth repetition is now formally
retired. Positive survivor is an exact completion specification: a Gamma/co-Poisson/Stokes
channel must supply squared gain `64` and offset its trace debt within primitive cubic budget.

The physical covariance foundation is now explicit in its own Lean module. Distinct prime/depth
rates make all six minor probabilities positive; their covariance is PSD, vanishes exactly on the
constant direction, and has a nonzero off-diagonal entry. Thus each packet supplies a canonical
rank-three quotient coupling before global sewing. This certifies provenance of the later P-G94/
P-G95 operator; it does not change SP-E's arithmetic identification frontier. Evidence is
`GammaSewnMobiusApertureStokesPhysicalPluckerCovariance.lean`.

This local repair is no longer preferred route. P-G94/P-G95 already supply full source-normalized
six-minor covariance on literal overlapping prime/depth labels, positive Schatten-one assembly,
and global faithfulness. Passing that operator to its canonical coordinate Hilbert--Schmidt kernel
now gives unconditional cofinal SP-E determinant. Every finite principal `det2(I-zT_s)` has only
strictly positive-real zeros; after signed reflection every finite approximant has only strictly
negative-real zeros. Finite sections converge pointwise and locally uniformly on every closed disc
to an entire reflected determinant, whose zeros are also strictly negative real. No amplitude-eight
repair, fitted damping, or new inter-block coefficient enters.

Higher principle is descent before spectralization. Artificial local pairing discards physical
overlap, creates false gauge kernels, and turns Radon--Nikodym mass into apparent normalization
freedom. Literal incidence descent fixes mass and sewing simultaneously; positivity plus global
faithfulness then forces strict stability of all finite compressions. SP-E determinant existence,
finite real-rootedness, source normalization, sewing, trace-class control, and cofinal convergence
are closed in Lean.
Principal capstone is
`GammaSewnMobiusApertureStokesPhysicalPluckerEntireDeterminant.lean`.

Direct `det2` identification with completed Xi is now formally impossible: regularization forces
zero first derivative at origin, while normalized Xi square-coordinate series has strictly positive
linear coefficient. Canonical repair is not fitted amplitude: multiply by
`exp(u*sourceTrace)` to recover ordinary Fredholm determinant without changing zero set. Lean proves
source trace strictly positive, equals summable physical diagonal, and now removes hidden spectral
notation through the literal nuclear source mass

```text
sum_(prime/depth block, Pluecker label)
  blockWeight * physicalProbability * ||centeredVector||^2.
```

Finite determinants are literal `det(I+uT_s)`, and cofinal finite traces/determinants converge.
P-G99 now evaluates first identity negatively without computation. Covariance diagonal is exactly
Bernoulli variance, so source mass is

```text
sum_z blockWeight_z sum_i node_z,i m_z,i(1-m_z,i).
```

Every critical four-node packet has node sum `<2/25`, and `m(1-m)<=1/4` for every real `m`, not
only probabilities. Thus every local trace is `<1/50`, normalized positive sewing gives global
source trace `<=1/50`, and independent prime--archimedean arithmetic gives
`thetaCuspNormalizedEvenMoment 1 / 2>1/50`. Canonical ordinary determinant therefore also has wrong
first jet. Evidence is `GammaSewnMobiusApertureStokesPhysicalPluckerOrdinaryDeterminant.lean` and
`GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo.lean`.

P-G100--P-G102 now classify canonical continuous-zero escape.  On every finite coordinate face,
`T(eps+T)^-1` trace tends to face dimension, so unweighted cofinal trace has no finite scalar
renormalization.  Source block weights applied before boundary limit select exact residue `4`,
cancelled by oriented polar countercurrent `-4`, with exact defect

```text
4-W(eps)=eps R(eps).
```

This escape is rank recovery, not local amplification.  Both bounded channels of resolvent split,
`T(eps+T)^-1` and `eps(eps+T)^-1`, have norm at most/exactly one and cannot realize SP-E's uniquely
required fourth-depth amplitude `8` on any nonzero vector.  P-G102 closes apparent unnormalized
survivor in genuine boundary regime.  Exact inverse gain `c` forces original physical spectral
shell `1/c-eps`; for `c=8` this is `1/8-eps`.  Literal positive rank-one expansion gives
`||T||<=nuclearTraceMass<=1/50`, so amplitude eight is impossible whenever
`0<eps<21/200=1/8-1/50`, in particular along every approach to zero.  Evidence is
`GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryTraceCapacity.lean` and
`GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryAmplificationNoGo.lean` and
`GammaSewnMobiusApertureStokesPhysicalPluckerBoundarySpectralShellNoGo.lean`.

P-G103 classifies smallest operator-changing survivor. Positive parent-pivot Schur shorting can
only reduce depleted energy `w/64`, so it never restores `w`. One negative polar pivot `-w`
reverses correction sign, and exact restoration holds iff cross square is `(63/64)w^2`. Unique
nonnegative cross is `(sqrt 63 / 8)w`; resulting two-channel determinant is `-w^2<0`. Full cross
`w` returns `65w/64`, exactly original coefficient-faithful pair trace, so naive identification of
equal four-unit source/polar residues reproduces debt rather than cancels it. Evidence is
`RouteEPCubicSourceNormalizationKreinShorting.lean`.

P-G104 closes coefficient provenance. Two literal Route-P depth-square steps have squared-energy
factor `1/64`, both on primitive cubic weight and on P-G179 physical Hankel dilation, hence Hilbert
amplitude `c=1/8`. Its canonical minimal Julia defect is
`d=sqrt(1-c^2)=sqrt(63)/8`. For parent amplitude `sqrt w`, parent--defect source pairing is
`sqrt w * (d sqrt w)=d w`, exactly P-G103's unique polar cross; literal fourth-depth energy plus
defect energy is `w`, and negative-pivot shorting restores `w`. Thus coefficient is forced by
source contraction and is not a fitted Gamma/polar overlap. Evidence is
`RouteEPCubicSourceNormalizationJuliaDefectCompletion.lean`.

P-G105 realizes that scalar/physical law on Burnol's actual co-Poisson carrier. The literal map is
`A=(1/8)U_4`, where normalized fourfold dilation `U_4` is unitary. Julia defect
`D=(sqrt 63/8)I` remains in parent aperture while `Af` descends to aperture `b/4`; full
two-channel colligation is isometric and source-compatible. P-G105B then constructs the missing
negative pivot rather than assuming it:

```text
x_f=(cU_4f,0),       p_f=((d/c)U_4f,(1/c)f).
```

In diagonalized source/co-source exchange form, their exact Krein block is
`[[w/64,dw],[dw,-w]]`, determinant is `-w^2`, and shorting restores `w`. Both pivot coordinates
remain in Burnol source ladder. Amplification eight therefore survives only in negative co-graph
coordinate; P-G102 excluded it from positive spectral shell, not from this source-exchange Krein
completion. Evidence is `RoutePFourthDepthCoPoissonJuliaColligation.lean` and
`RoutePFourthDepthCoPoissonJuliaKreinPivot.lean`.

P-G105C closes the former off-diagonal incidence ambiguity. On P-G186's actual Burnol half-line
feature carrier, polarized child/pivot pairings give one universal Julia--Krein block
`B=[[1/64,d],[d,-1]]`. For every finite prime/depth/ordinate packet with Gram `G`, completed matrix
is exactly `B tensor G`, including every off-diagonal entry. Since `det(B)=-1`, its determinant is
`(-1)^N det(G)^2`; completion is nondegenerate exactly when source Gram is. Thus Gamma/Stokes
identification no longer requires `N^2` fitted pairing identities: one label-natural realization of
universal negative channel forces all finite incidences. Evidence is
`RoutePPrimitiveBurnolJuliaKreinMatrixCompletion.lean`.

P-G105D supplies missing Gamma coefficient provenance. For running prime odds `a`, source-derived
thermal ratio `T=(8+a)/7` makes literal co-Poisson Cayley coordinate exactly `1/8`; finite child and
Gamma complement become `a/64` and `63a/64`. The actual archimedean cyclic characteristic squared
at `artanh(1/8)` equals Julia defect `sqrt(63)/8`. Gamma defect operator and both physical/half-line
co-graph pivots are exactly P-G105--P-G105C Julia channels. Evidence is
`RoutePFourthDepthGammaCyclicJuliaIntertwiner.lean`.

P-G105E then falsifies too-strong scalar source weld. Literal joint-depth Xi source and reciprocal
co-source obey `source(p,e)=log(p) coSource(p,e)`; primes `2` and `3` rule out every real or complex
global scalar intertwiner. Exact positive survivor is operator-valued Gamma--Julia multiplier
`(sqrt(63)/8)log(p)`, independent of depth, whose application to actual co-source lands in proved
joint-depth Hilbert source. Therefore P-G105C's universal Kronecker block is a valid carrier
completion but cannot itself be identified with Xi-landing arithmetic polarization. Evidence is
`RoutePPrimitiveJointDepthGammaJuliaScalarIntertwinerNoGo.lean`.

P-G105F carries that survivor through arbitrary finite off-diagonal incidence. With
`L=diag(log p_i)`, exact source Gram in reciprocal-promotion coordinates is `LGL`; its entries are
`log(p_i)G_ij log(p_j)`. Julia--Krein completion is `B tensor (LGL)` and has determinant
`(-1)^N det(L)^4 det(G)^2`, so it is nondegenerate exactly when `G` is. Prime-log correction changes
finite volume but creates no hidden degeneracy. This is matrix algebra, not yet literal Stokes
orientation or Xi carrier identification. Evidence is
`RoutePPrimitiveJointDepthGammaJuliaLogKreinMatrixCompletion.lean`.

P-G105G closes finite stability after retaining channel chirality. Signed row pencil
`I+((diag(z,w)B) tensor LGL)` is exact left action on P-G105F completed matrix, not a diagonal
surrogate. Its determinant factors over nonnegative Gram eigenvalues as
`product_lambda (1+lambda z/64-lambda w-lambda^2 zw)`. A positive-lambda zero would force `w` to be
an orientation-reversing real Möbius image of `z`, hence in lower rather than upper half-plane;
zero eigenvalues contribute one. Thus actual full finite P-G186 pencil is bivariate stable for
every packet without injectivity or nondegeneracy. Physical Stokes provenance of variables remains
open. Evidence is `RoutePPrimitiveGammaJuliaSignedBivariateStability.lean`.

P-G105H then falsifies raw trace-class cofinalization. The two P-G105F prime-log factors cancel
P-G186's `(log p)^-2` diagonal regularizer exactly, leaving promoted density
`(1/4)p^{-(e+1)}(e+1)^-3`. Its depth-zero slice is `1/(4p)`, so actual positive finite traces are
cofinally unbounded by Euler's prime harmonic divergence. Exact positive survivor is coefficient
`1/4`: any completion must cancel this literal Euler pole by source-derived aperture/polar geometry,
not free scalar renormalization. Evidence is
`RoutePPrimitiveGammaJuliaLogCofinalTraceNoGo.lean`.

P-G105I constructs exact surviving renormalization. Strictly positive-depth promoted trace is
summable; singularity is localized to depth zero. Positive aperture diagonal with square
`32d log(p)p^(-2d)` sends literal `1/(4p)` trace density to corpus's oriented Stokes term
`8d log(p)p^{-(1+2d)}` labelwise and on actual finite P-G186 matrices. All-prime transported trace
plus existing higher-valuation/archimedean polar countercurrent equals completed prime--Gamma
current and tends to zero at wall. Thus physical Stokes provenance and polar cancellation are
closed at trace level, not yet operator-determinant level. Evidence is
`RoutePPrimitiveGammaJuliaStokesApertureResidueTransport.lean`.

P-G105J turns trace cancellation into forced stable channel geometry. Ratio
`r(d)=-polarCurrent(d)/primeCurrent(d)` tends `1` and is eventually positive. Physical one-variable
specialization `z=64u`, `w=r(d)u` places both channels in upper half-plane for `Im u>0`; actual
aperture-conjugated P-G186 Gram remains PSD, hence every finite physical pencil is stable near
wall. Its generator trace is `(1-r(d))` times finite child trace, and all-prime value is exactly
completed prime--Gamma current. Evidence is
`RoutePPrimitiveGammaJuliaPhysicalStokesStableSpecialization.lean`.

P-G105K constructs actual cofinal child operator without deleting cross-prime incidence. Its kernel
is literal zero-ordinate aperture/prime-log congruence of P-G186, and every finite pullback equals
P-G105I matrix entrywise. Exact Schur law is
`|K_d(p,q)|^2=w_d(p)w_d(q) 64log(p)^3log(q)^3/(log(p)+log(q))^6`; normalized cubic coherence is at
most one. Summability of transported Stokes weights therefore makes full kernel Hilbert--Schmidt
for every `d>0`. Diagonal sum is literal oriented Stokes current; two-prime PSD pullbacks make
global kernel Hermitian and represented operator self-adjoint. Evidence is
`RoutePPrimitiveGammaJuliaStokesCofinalChildKernel.lean`.

P-G105L exposes P-G105J nonnormality as coordinate artifact. For `r>=0`, physical row-weighted
channel has real-symmetric Hellinger representative
`A_r=[[1,8sqrt(r)delta],[8sqrt(r)delta,-r]]`, with trace `1-r`, determinant `-64r`, and exactly same
characteristic factor on every source eigenvalue. Hence every actual finite P-G186 physical
determinant is retained. Tensoring `A_r` with P-G105K kernel gives full cofinal self-adjoint
Hilbert--Schmidt operator. Its det2 is entire, finite sections converge uniformly on every closed
disc, and every cofinal zero is real. At forced `r(d)`, diagonal sum is exact completed prime--Gamma
current. Evidence is
`RoutePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalDeterminant.lean`.

P-G105M proves every child principal block positive, passes positivity to cofinal operator, and
uses summable exact diagonal to prove Schatten-one. Ordinary child trace is exactly oriented Stokes
current. Evidence is `RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass.lean`.

P-G105N lifts trace class through forced finite Hellinger channel. Full indefinite physical
operator is Schatten-one, its ordinary trace is `(1-r)` times Stokes current, and its ordinary
determinant is trace-restored `exp(z Tr(T))*det2(1+zT)`. Literal finite determinants converge
uniformly on every closed disc for each fixed positive aperture. At forced polar ratio trace is
exact completed prime--Gamma current. At balanced wall `r=1`, finite channel squares to `64I`;
determinant is even, equals regularized determinant, factors through positive child square, and
inherits only real zeros. Evidence is
`RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminant.lean`,
`RoutePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryDeterminantCofinalUniform.lean`, and
`RoutePPrimitiveGammaJuliaPhysicalStokesHellingerBalancedWallSquare.lean`.

This is fixed-node Bernoulli capacity wall. It excludes all probability reweightings and even all
real coordinate-mean changes retaining same positive nodes/quadratic, so direct higher Fredholm
comparison is retired. Local co-Poisson contraction, Julia defect, negative sign, exact pivot, and
shorting, full finite matrix completion, and Gamma cyclic operator provenance are now closed.
Constant source/co-source intertwiner and raw prime-log trace-class cofinalization are closed
negatively. Prime-log-conjugated full finite matrix completion, signed bivariate finite stability,
trace-level source/Stokes polar cancellation, and physical finite stable specialization are closed
positively. Exact cofinal child kernel and its Hilbert--Schmidt/self-adjoint operator are also
closed. Source-equivalent Hellinger channel, actual finite determinant retention, full cofinal
self-adjoint det2, child and full physical Schatten-one membership, ordinary trace-restored
determinant, fixed-aperture local-uniform finite-section convergence, balanced-wall square
factorization, and real-zero law are closed. The normalized wall law, exact energy limit `256/35`,
fixed-carrier cubic-kernel `L2` convergence, nonzero balanced square jet, and every fixed continuum
Fredholm coefficient limit are also closed. Exact physical coefficient transport, one summable
all-order majorant, locally uniform `d -> 0+` wall convergence, and wall real-zero closure are now
closed. But the resulting child is trace class, while a multiplicity-exact Xi landing would require
the nonsummable reciprocal Xi divisor. Thus ordinary/balanced trace-class Xi landing is impossible.
The survivor is now constructed: literal prime-log density produces a self-adjoint Hilbert--Schmidt,
non-Schatten-one balanced channel whose entire `det₂` has exactly the explicit symmetric real
reciprocal source zeros. Burnol
holonomy supplies negative
orientation but has zero-dependent magnitude, so dividing by it would be target fitting. Every
scalar functional-calculus channel of current positive operator, probability reweighting, and free
scalar counterterm is closed. P-G94--P-G105L
positivity, faithfulness, continuous zero spectrum, stable zeros, cofinal convergence, and four-unit
relative residue survive as reference geometry. Local shorting, operator-valued finite completion,
and signed bivariate finite stability exist; raw prime-log trace is impossible. Physical trace,
finite stable Stokes/polar completion, trace-class child/full operators, ordinary physical
determinant, and aperture-wall convergence now exist, but that trace-class divisor cannot be Xi.
Genus-one reconstruction exists, but its forced zero at one excludes Xi, normalized Xi, and every
pointwise scalar weld. SP-E survives only as a spectrum-moving operator-coupling candidate; direct
source-divisor identification is dead. Raw
natural Suzuki Cauchy energy has the wrong linear scaling and its Ward defect tends to
`-infinity`, excluding an unrenormalized natural-wall replacement.

### TC-HS — theta--Cayley half-step reflection transport

Paper-level direct theta-source Cayley orbit has exact eigenline port defect: sign is horizontal Xi
orientation and vanishing is critical-line placement. Functional-equation reflection sends Cayley
time `n` to `-n-1` and gives weighted same-time annihilation with coefficient `|k_q|^(4n+2)`, not
unweighted cancellation. This kills ordinary integer-time Green telescoping and identifies fixed
reflection time `-1/2`.

Surviving candidate is source-native `U^(-1/2)` transport, or equivalent coefficient-neutralizing
density, constructed before divisor scalarization while preserving prime labels, multiplicity, and
both orientations. If it turns forced weighted reflection law into equal-coefficient annihilation,
the port reader closes RH. The defect/reflection theorem is paper-proved but its planned Lean module
and source half-step producer do not yet exist; TC-HS is candidate architecture, not live route.

### UQ-QC — Route U/Q source-pure quadratic concentration

**Candidate endpoint.** A finite cofinal arithmetic quadratic-energy budget, defined before zero
reconstruction, dominates every line-conjugate continued-Cauchy concentration profile and every
strict shifted-Hankel Christoffel boundary layer. Since either false-RH defect has divergent local
quadratic energy, such a budget excludes both and proves RH.

**Established mechanism.** Lean proves exact Q shadow. For `0<y<b`, line-conjugate Poisson
difference has signed integral zero but squared integral
`pi*y^2/(b*(b^2-y^2))`, tending infinity as `y->b-`. This retains mixed incidence erased by first
moments. U independently localizes every false-RH least contact to completed boundary roughness,
the correct place for width-sensitive energy rather than interior sign.

**Open core.** Construct canonical source-side energy from literal prime--Gamma data; prove finite
cofinal bound without RH or divisor-location premise; identify Q and U shadow maps with constants
nondegenerate at their walls. None of these three source statements exists. UQ-QC is a genuinely
new merger mechanism but not yet an independent route because it lacks instantiated source energy
and unconditional chain to endpoint. Evidence is
`PrimeArchConjugatePairQuadraticConcentration.lean` and active
`route-u-q-quadratic-concentration-law.md`.

### HA-SW — height-adaptive cancelled-source socle--Weyl descent

**Candidate endpoint.** On a bounded admissible off-line domain, let `A` be shifted regularized
zeta, `C` literal cancelled sharp-prime source, `Q=O/(A)`, and `L_C` multiplication by `C`.
Exact order loss `ord_p(C)=ord_p(A)-1` makes `im L_C` one-dimensional at every distinct zero, so
its dimension is distinct-zero count `D_Omega`. If source prime clock/shift pair descends to
invertible endomorphisms of this actual socle with dyadic Weyl phase of order `2^k>D_Omega`,
determinants force `2^k|D_Omega`, hence `D_Omega=0`. Cofinal domains then prove RH.

**Established mechanism and obstruction.** Socle-rank/order-loss and height-adaptive determinant
contradiction are paper-proved; existing Lean receivers formalize required divisibility and RH
capstone. New analytic idealizer theorem is Lean-proved for every locally finite symmetric
superlinear sampling set: a finite shift--differential Weyl operator preserving sampling nullspace
collapses to polynomial multiplication, so all descended finite-prime operators commute. Real Xi
divisor is formally locally finite and symmetric; superlinear density uses external Conrey input.
Two multiplicatively independent dilations force any continuous invariant metric to full
translation invariance, and a null completed-theta trace forces spectral measure onto real Xi
divisor. Thus a cofinal finite-prime sampling-quotient descent is impossible.

**Open core.** Construct internal invertible Weyl pair on finite aggregate socle from integral
cutoff boundary incidence before full sampling quotient, or use genuinely nonlocal/cofinally
all-prime operator. It must act on `im L_C` itself, not an added clock tensor, preserve scalar-zeta
socle, and retain Fitting/subresultant incidence rather than raw boundary homotopy. HA-SW is a new
conditional architecture, not live route: source descent does not exist. Evidence is
`PrimeWeylSamplingIdealizerAnalytic.lean`, `XiRealDivisorSampling.lean`,
`SuperlinearSamplingAperiodicity.lean`, `TwoDilationDivisorMetric.lean`, and active
`height-adaptive-cancelled-source-socle-weyl-rh.md`.

### PH-TC — parabolic heat--Turan curvature

**Candidate endpoint.** Parabolic mass blow-up carries the complete centred Xi divisor to
polynomial-filtered Gaussian heat moments. Paper proves RH equivalent to nonnegative Turan
curvature `H_0 H_2-H_1^2` for every real polynomial filter and positive time, equivalently to the
Gamma-averaged shift-one reciprocal-Hankel cone. This is a reflection-positivity mechanism, not
Route T's vertical transport/type mechanism.

**Established mechanism.** Lean proves exact Gaussian moments/Fourier and heat-operator polynomial
laws, eventual positivity under any fixed lower-degree heat-jet correction, the safe degree--time
wedge, and superexponential invisibility of every fixed-degree prime jet before first-prime
horizon. Countable conic compression retains cross-prime covariance. The unfiltered prime--prime
determinant is exactly the mean--variance defect of `Y=(log n)^2`, whose continuous Gaussian saddle
lies on the Lorentz boundary. Exact two-replica expansion and Bohr--Cesàro projection now show an
off-line bottom shell contributes a surviving strictly negative transverse square; corresponding
Xi and finite prime--Gamma contour bottom-shell detectors are formal. Every finite divisor packet
has an explicit real polynomial isolating one nonreal conjugate shell while killing every real and
other point. For any supplied isolated bottom shell and summable majorant, higher-shell determinant
defect decays exponentially and divisor-level parabolic dominated convergence is closed. Missing
is one source-declared positive-root filter/isolation law for full divisor, filtered prime--Gamma
equivalence, and source Schur sign. Massive half-wave is an exact positive Gaussian-heat average;
tilted continuous prime saddle has exact Gaussian moments and zero mean--variance defect. Thus
subordination, tail passage, and saddle evaluation supply no missing arithmetic sign.
For positive channel families, normalized curvature is exactly mean local curvature plus score
variance, while completed curvature is `H(A v_A-P v_P)-AP(m_A-m_P)^2`; cross-prime covariance is
therefore retained and missing sign is isolated to local-curvature/prime--Gamma score mismatch.

**Open core.** Prove the coefficient-exact source-side Schur residual, equivalently the late-time
Fisher--Stein compensation for positive-root prime law against polar--Gamma law; in polynomial form: every monic
real-rooted boundary polynomial `p` orthogonal through degree `n-1` for the literal shifted-Xi
functional has strictly positive next value `L_y(X^n p)`. At the unfiltered face this asks for an
exact completed prime--Gamma Stein identity controlling the tilted von-Mangoldt Gaussian defect;
ordinary relative-error PNT cannot survive the quadratic cancellation. Atomwise positivity, finite
jets, and independent-prime conductors are excluded. PH-TC remains source-isogenous to T, not an
independent live route. Evidence includes `PrimeSquareMeanVarianceDefect.lean`,
`HeatTuranTwoReplica.lean`, and `XiHeatTuranBottomDetection.lean`.

### MC-CS — sub-square-root mass-chirp separation

Mass shell has faithful phase below square-root information horizon. For any fixed finite
conjugation-stable divisor packet and `a(u)=u^theta`, `1/3<theta<1/2`, Lean proves massive trace
tends to zero exactly when packet is critical. Principal-root expansion produces top-growth finite
exponential sum; positive multiplicities and Bohr--Cesàro mean square prevent cross-orbit
cancellation without zero-gap hypothesis.

It is not yet route. Full Xi packet grows with observation scale, and uncontrolled tail can cancel
any selected finite packet. Missing theorem is uniform/cofinal positive chirp projection stable
under growing divisor and accessible from literal prime--Gamma source. This is source-isogenous to
Route T but analytically distinct from its fixed-mass Bessel type-zero lane. Evidence is
`ExponentialSumMeanSquareLower.lean` and `FinitePacketChirpSeparation.lean`.

### Moving-degree reverse-Bessel completed-source opening

Fixed-frequency localization remains dead: normalized reverse-Bessel jets cancel Euler damping at
every fixed prime. That no-go is not uniform in degree. Lean now proves full factorial Gamma-jet
cost is at most `3+(1/2)log N`, normalized coefficients decay geometrically past half degree, and
Euler damping reappears at moving scale `x=6N log(m+2)` with retained exponents `3N` and `2N`.
The former quadratic/parabolic positivity horizon is therefore not forced; a linear-in-degree
completed-source horizon is viable.

This reopens a disproof/positivity mechanism but does not yet instantiate an independent route.
The special-function side is now locally closed: complex Gaussian half-moments, a real-parameter
Schlaefli ray representation, Watson remainder, all-order sectorial `K_1` Poincare expansion,
half-plane complex-binomial control, principal-root factorization, and exact mass-carrier
distortion are formal. Lean further realizes the carrier as a bivariate shell series, computes the
extremal coefficient polynomial at every order, proves a shell-uniform expansion, and bounds the
genuine order-`m` truncation with the correct order-`m` shell power.
Remaining theorem is RH-bearing completed prime--Gamma moving-window/dyadic assembly turning half-log reserve and recovered Euler damping into cofinal pulse capital, or producing one negative completed jet.
Fixed-prime analysis cannot decide it.

### HJ-GR — hard-Jacobi reserve versus boundary controllability Gramian

**Candidate endpoint.** Apply the shifted-Xi reciprocal moment flow to the cofinal Jacobi degree
`n asymp sqrt(y)`. If the far hard reserve dominates the future boundary controllability Gramian,
the centered inverse Jacobi operator cannot acquire a negative hard coordinate. Through Route U's
finite super-apex ancestry and first-contact alternative, this excludes the completed boundary
crossing and proves RH.

**Established mechanism.** In a moving orthonormal frame the connection is skew and
nearest-neighbor. Lean proves that truncating the full nonisospectral Riccati expression loses
exactly one corner,

```text
J_n' = [J_n,A_n] - J_n^2 - 2n a_n^2 e e^T,
```

once the source-derived untruncated Lax identity is supplied. Centering the inverse
`U_n=J_n^(-1)-yI` changes that negative boundary input into a positive rank-one source. Skew
conjugation removes the commutator, so the increment is exactly a positive controllability
Gramian. This explains strict reciprocal Gauss-node motion and Padé-residue leakage as shadows of
one source-controlled port. The nonisospectral Toda coefficient law, finite Riccati boundary
source, inverse derivative, positive conjugated Gramian, boundary visibility of every irreducible
Jacobi node, and strict simple-node motion are now formal for a shifted half-density frame. Positive
forcing still does not control absolute level: initial hard reserve can be smaller than accumulated
Gramian debt.

**Open core.** Instantiate that frame from the literal shifted-Xi moment functional, identify its
Jacobi family with the hard first-contact carrier, and prove the cofinal quantitative
inequality

```text
far hard reserve - future boundary Gramian >= 0,   n asymp sqrt(y).
```

Generic matrix algebra, fixed-degree positivity, and monotone node motion cannot prove this
inequality. HJ-GR is a new candidate mechanism, not a live independent route: its source
instantiation and unconditional chain into Route U's boundary state remain open. Evidence is
`HTGeometry/JacobiRiccatiTruncation.lean`,
`HTGeometry/JacobiTodaRiccatiLaw.lean`,
`HTGeometry/JacobiNodeBoundaryMonotonicity.lean`,
`HTGeometry/SkewConjugatedRiccatiGramian.lean`, `XiShiftedJacobiFrameToda.lean`, and
`mass-shifted-hard-jacobi-leakage-gramian-law.md`.

### CCM causal-Pick and diagonal-Fock receivers

Exact affine conjugacy identifies shifted-Xi quotient with causal quotient; zero shift degenerates
to constant quotient and zero kernel. Separately, safe Cauchy kernel and RH kernel differ by a
positive Schur Cauchy covariance, and diagonal Fock-lift contractivity is equivalent to RH-form
positivity. Euler-ray packets show why scalar pointwise contraction is insufficient: an off-line
model has a negative two-point minor. These are exact RH-equivalent receivers and matrix-level
warnings, not an additional CCM candidate until a literal source proves complete Pick/Fock positivity.
`CCMWeightedSchurSeam.lean` makes missing width exact: unconditional weighted quotient
contractivity reaches only safe width `omega`, while distinguished target is `omega+1/2`.
Target contractivity is RH receiver itself; more scalar Schur estimates cannot manufacture missing
half-width.

New polar-frame, boundary-saturation, diagonal-colligation, and Birman--Schwinger modules sharpen
that warning. They decompose the completed form as positive prime/frame energy minus scalar polar
level, encode passivity once a source colligation is supplied, and give generic norm criteria for
absence of negative spectrum. But the actual source compression, Stieltjes/RKHS realization, and
required lower-frame or norm inequality remain hypotheses. Moreover any fixed boundary profile
with the proved leading asymptotics saturates the polar level at ratio one; only subleading
source-relative sign can decide RH. `CCMPolarEulerFrameLevel.lean`,
`CCMBoundaryLaplaceSaturation.lean`, `CCMDiagonalFockColligation.lean`, and
`CCMNonSchattenBirmanSchwinger.lean` are receiver/guardrail theorems, not another candidate.

### CCM–E floor transport

Literal finite Sonin source carries `mu(n)/n`, but no theorem sends E's fixed Hall/load/flux law
into CCM cofinal floor selector. It becomes new route only after such coefficient-faithful
comparison and unconditional floor handoff exist.

### CCM–P–L two-sheet singular handoff

This is a concrete cross-route mechanism, not independent route. P-G189 tail flux is atomwise a
positive dressing of CCM's first centered cubic clock jet. Two reflected Gamma-six singular graph
sheets now retain this centered direction: finite packets have mass trace zero, orientation trace
one, ambient limit zero, and nonzero graph limit. Every labelled cell has exact CCM third-jet
readout and exact fixed-Sonin transport, with physical vanishing iff neutral horizontal grade.
Active Meyer--Tate bridge now produces each cell from literal ordinary-prime rational-adelic source
before two-sheet lift; arbitrary choice of local horizontal vector is no longer an opening.

What remains is global and RH-bearing: assemble cofinal labelled cells source-faithfully, retain
P-G188 `<2` budget, synthesize adaptive doubled-rate half-density/fundamental-symmetry correction,
and prove distinguished non-universal Stokes annihilation. Fixed primitive secants cannot pay cubic
quantum uniformly, and adaptive rate lies below primitive Euler spectrum near critical line. No
separate source law or endpoint distinguishes this seam from Routes L/P, so Route V remains
uninstantiated.

### Relative formation-completion current (Route-V candidate)

Constitutive and relative-formation modules show source laws may require nonzero mixing before
radical-preserving normalization. No literal Xi-typed formation object currently has both
non-coboundary displacement and coefficient-faithful RH handoff. Therefore Route V is not
instantiated.

### Quenched causal-replica incidence

Circuit heap Boltzmann law and replicated shared-source incidence are exact, with quenched replica
mass realized as event probability. Replica order now has an exact endpoint: accessibility equals
one precisely on empty-heap recurrence sector, off-sector mass decays geometrically, and quenched
replica mass converges to source measure of that recurrence sector. Replicas therefore extract
rather than remove recurrence. No map from this generic probability object to literal
prime--Gamma/Xi source, no RH receiver, and no route-specific recurrence-exclusion theorem exists.
It is infrastructure and sharp obstruction, not a new route.

### Adjacent Artin, Selberg, and Baker programmes

Artin corpus now constructs genuine Frobenius--inertia local Euler polynomials, proves lift
invariance, conjugate and same-base-prime descent, choice-free local factors, direct-sum product at
local and number-field finite places, coefficientwise formal Euler source by stabilization,
virtual Frobenius reciprocity, and injectivity of monomial multiplicity profiles. It also has a
concrete elementary Brauer carrier. Finite-order local-polynomial work proves actual
Frobenius--inertia roots have norm one, reverse local polynomial is nonzero in unit disk, and its
reciprocal has explicit bounds. At number-field finite places Lean constructs locally uniformly
convergent differentiable/analytic reciprocal Euler product on `Re(s)>1` and proves it nonzero
there. Remaining gap is identification with formal stabilized Artin source, Brauer
induction/effectivity, continuation, and global holomorphy.

Selberg corpus now has general positive-line complex Mellin inversion, multiple-twist normal
families and uniform undamping on initial domain, general-line Mellin--Barnes identity, finite
spectral sublevels/right gaps, affine Gamma poles/residues, Barnes two-Gamma vertical tails, and
pole-safe asymmetric functional equation on regular locus with invariant root number. It still
lacks continuation across initial wall, infinite-shift residue sum, pole noncancellation, and
`alpha->0` passage. Finite negative-integer Gamma poles/residues, exact rectangle residue theorem,
horizontal-edge vanishing, two-Gamma vertical-line integrability, and every fixed finite Barnes
vertical shift are now closed. Full carrier is also closed under one, conjugation, and ordinary
product; degree-one common-level character algebra is exact, while degree-two analytic Mertens
prime-harmonic convergence remains open.

Baker programme is now formally closed at its advertised endpoint. Corpus constructs full
integral Siegel matrix/kernel, nonzero auxiliary exponential polynomial, coefficient and conjugate
house bounds, exact multipoint-Schwarz step, parameterized long iteration, and terminal
contradiction. `bakerLinearIndependence_holds` proves Baker linear independence unconditionally.
This is substantive adjacent mathematics, not a Riemann-RH route, and does not change live count.

Friable auxiliary edge coefficients have no finite-degree soft spot: for every finite prime set and
degree bound `d>=T`, the realizable coefficient map is surjective onto all degree-`T` prime-log
monomial forms. Any auxiliary-function successor must control the full form space, not exploit a
hidden realizability subspace. This is adjacent rigidity, not an RH route.

New Dennis--Stein/K₂ Bruhat identities, dominated-series `L²` passage, off-circle unitary
resolvent, sharp rank--energy control, and perturbative endpoint-completeness induction are exact
reusable infrastructure.
None supplies a literal Xi/prime--Gamma source map or RH endpoint, so none creates a route.

Every finite occupation packet with at least two primes is hypertranscendental at every positive
integer temperature, yet cofinal completion at each even temperature is differentially algebraic.
At temperature two it is exactly the sine product, satisfies a second-order ODE, and packet Euler
jets converge to ordinary zeta values. This collapse law is not an Xi selector.

Lie--Cartan normal-form infrastructure proves affine connection for a bracket-closed
pair with a unit member, projective-defect cocycle/quotient identities, and a rank-three coefficient
constraint. It has neither Xi-typed source nor RH endpoint and creates no route.

New differential/algebraic-geometry modules likewise do not change RH frontier. Deep jets of
nonaffine rational observations reconstruct whole free differential field, while affine common-view
case is exact proper tail; expanding torus isogeny's stable tail is logarithmic-current frame and
is birationally invariant; eigen-plurivolume produces canonical log-crepant boundary with
coefficient one on recurrent expanding divisors. Separately, one-point degree loss at Schur
reduction bounds collision support by two and yields monodromy transposition. These are strong
generic reconstruction/rigidity mechanisms but have no Xi-typed source or RH endpoint. Evidence is
`HTGeometry/JetPrincipalSymbolExtraction.lean`,
`HTGeometry/DerivationAlgebraicDescent.lean`,
`HTGeometry/RationalObservationCurveNormalization.lean`,
`HTGeometry/ToricIsogenyTailLaw.lean`, `HTGeometry/EigenPluriVolumeLogCrepant.lean`,
`HTGeometry/CollisionSupportCounting.lean`, and
`HTGeometry/CriticalSchurCollisionDegree.lean`.

### Helson Fredholm wall

Trace-class Helson realization, real self-adjointness, and fixed Fredholm wall are closed. The
`1/w^2` Riesz kernel is sharply integrable, its truncated-log Mellin pair exact, and logarithmic
Riesz sums are positive averages of partial sums. Conditional Tauberian algebra is now closed:
bounded endpoint Riesz means plus uniform short-block increment `epsilon` imply
`||A(N)||<=2B/log(M/N)+epsilon`. Missing source theorem is precisely that analytic increment
control with useful uniform choice of `M/N`, plus coefficient-faithful completed intertwiner and
canonical Xi stream. Coefficientwise tail bounds are too lossy. Steinhaus divergence at
`sigma<=1/2` is no natural-boundary theorem. Helson remains an opening, not a route.

### Post-J principal-relative current

J proves current must be defined before good/bad projection. Existing concrete primitive is Route
R and is terminalized. A genuinely different source object with non-coboundary incidence and
unconditional handoff would be new route.

### Cubic Ward/Hellinger source-trace opening

This opening is an alternate producer for Route P's completed correction/budget problem, not an
independent route. P-G labels identify dependency and receiver blocks. Exact clock-to-radial
transform has not been constructed; P-G204/P-G205 already construct finite target-visible family
and exact augmented balance, so transform matters only if it realizes and controls positive
correction from conserved source budget.

P-G186 and the Burnol-window incidence theorem remove one misleading obstruction. Primitive
source columns and completed-Xi conormal columns both live in the same unweighted
`L2(R_+,dL)`; inverse logarithmic cubes come from
`integral L^2 exp(-2lambda L)dL=1/(4lambda^3)`, not from a `dL/L^3` source measure. The remaining
Riesz gap is absence of a coefficient-faithful completed intertwiner, not Radon--Nikodym loss.

P-G187 identifies a second, sharper universal obstruction. Weighted aperture translation
`T_c f(L)=L/(L+c)f(L+c)` is a contraction semigroup for `c>=0`, diagonalizes every Burnol column,
and turns primitive energy into P-G185 damping by `s=2c`. For every `c<0`, an explicit
finite-energy boundary datum acquires a nonintegrable pole at `L=-c`. Hence completion cannot be
ordinary backward motion in this Hilbert space: polar--Gamma coupling must supply an additional
boundary/dilation defect channel before Gram comparison.

P-G188 resolves the abstract-defect ambiguity. For `c>=0`, the missing energy splits exactly into
the deleted interval `1_(0,c]f` and the surviving-tail cocycle
`1_(c,infinity)sqrt(1-((u-c)/u)^2)f`. Together with `T_c f` these form an exact energy colligation.
On every primitive feature their mass is `(1-exp(-2c lambda))` times P-G186 base mass, and summed
defect plus transported mass is exactly the fixed `<2` source budget. Since primitive features
vanish linearly at the hard edge, the leading small-aperture loss is expected in the distributed
tail channel; a boundary-interval-only Gamma model is therefore too small.

P-G189 proves that last order diagnosis exactly. For every primitive cell the boundary-interval
energy divided by `c` tends to zero, while tail-cocycle energy divided by `c` tends to
`J(p,e)=2 lambda_(p,e) w_(p,e)>0`. The exact arithmetic form is
`J(p,e)=1/[2 p log p] p^(-e)(e+1)^(-2)`, its full primitive sum converges, and dominated convergence
passes the aperture derivative through that sum. Any Hilbert vector carrying this tail energy is
necessarily nondifferentiable at `c=0`; its amplitude is square-root scale. Thus the missing
Gamma--polar producer must match a trace-finite but vector-singular Wold current, not a smooth
boundary block.

Exact bridge identifies this entire first tail flux atomwise with a positive dressing of CCM's
first centered cubic clock jet and differentiates literal P-G188 tail connection to that matrix.
Thus source-side clock outer product is selected before zeros; no scalar-dressing or matrix-
direction ambiguity remains.

W-H185 gives a sharp new no-go and design law. Every primitive Euler column has exponential decay
rate at least `log 2`, whereas every strict-right centered zero column has rate
`0<a<1/2<log 2`. The exact tail is

~~~
T(lambda,R)=exp(-2lambda R)
 [R^2/(2lambda)+R/(2lambda^2)+1/(4lambda^3)].
~~~

Hilbert--Schmidt tail control for P-G186's full primitive synthesis proves that no strict-right
Xi conormal column belongs to its bare synthesis range, for any primitive ordinate clocks:
otherwise `exp(2(log 2-a)R)` would remain bounded. Thus direct Douglas factorization of the
positive primitive Gram is impossible even for one off-line copy.

Completion must therefore act before Gram comparison and create slower modes through signed
polar--Gamma/functional-equation coupling while preserving the global subquantum trace. This does
not exclude arbitrary bounded nonlocal operators; it isolates the exact source-derived completion
property still missing from W-H184. Lean proves exact tail integral and strict-right/log-2 rate
separation in `XiWardCubicPrimitiveTailRateNoGo.lean`.

W-H186/W-H187 close coefficient-faithful pre-divisor incidence. The construction is quadratic and
oriented. Form two completed logarithmic
currents before taking residues, and on the literal signed primitive-depth CCM/Krein family put
the reflected leg at radial coordinate `-r` and the forward leg at `+r`. Successive residues at
the line-reflected and forward Xi poles give

~~~
m_rho m_tau conjugate(F_rho(r)) F_tau(r),
F_rho(r)=r exp[-(rho-1/2)r].
~~~

The negative-radial orientation contributes the sign which cancels `i^2` from the two signed
residues. This removes the formerly nonintegrable `r^2` wall, which arose only when both reflected
columns were polarized on the positive radial leg. Aperture integration recovers every entry of
the raw multiplicity-weighted cubic zero Gram. Finite matrices are PSD and each strict-right copy
costs at least two base units. Lean proves the complete residue, integral, matrix, trace, and
literal-source identification statements in `XiWardCubicCompletedPairResidueIncidence.lean` and
`XiWardCubicKreinOppositeRadialPairIncidence.lean`.

One surviving alternate is clock-moment-to-opposite-radial-moment transform before divisor
residues, retaining P-G188 global subquantum trace while synthesizing and bounding P-G205 positive
fundamental-symmetry correction. Raw finite nonnegativity is itself RH-equivalent. W-H185 forbids
bare positive primitive synthesis; orientation must survive completed shorting. Route P is now
stated by completed correction/budget law, not raw packet passivity.

## Fundamental nature of remaining problems

Live open cores and candidate openings fall into nine mathematical classes.

1. **Source selection and spectral exhaustion.** Determine complete ground/spectrum from explicit
   source sector (C1, G, O, CCM-GS); for U, exclude formally isolated completed-boundary rough
   least-contact state.
2. **Singular boundary orientation.** Use source-derived graph limits or finite boundary packets
   to prove selected annihilation/sign without promoting it to circular universal law (L, P).
3. **Oscillatory arithmetic incidence.** Prove signed all-prime cancellation or transport without
   scalarizing phase/parity (CCM-FU, D2, E, T, U).
4. **Source quantization.** Produce label-sensitive discontinuous or singular selector compatible
   with atomic Xi support (Q, parts of P/U).
5. **Relative coercivity.** Bound entire unwanted complement, not one seed, diagonal, finite
   packet, or generic separating vector (C1, G, O, CCM-GS).
6. **Non-circular annihilation.** Convert already-oriented horizontal charge into zero by an
   independent source law; current vanishing statements themselves are RH-equivalent (L/R/CCM/
   Gauss–Hodge interfaces).
7. **Boundary-layer escape and concentration.** Classify sign carried by vanishing-mass outliers
   and shrinking-width profiles that fixed moments, diagonal energies, or weak limits erase
   (O, Q, U); retain quadratic mixed incidence/source flux before taking limit.
8. **Nonlocal arithmetic descent.** Make prime clock/shift act internally on finite source quotient
   without collapsing in cofinal sampling idealizer or manufacturing external tensor dimension
   (HA-SW and related Weyl openings).
9. **Reserve versus boundary controllability.** Positive boundary forcing determines motion but not
   absolute level. One must compare cofinal far reserve with accumulated rank-one Gramian debt at a
   source-selected growing truncation scale (HJ-GR, with shadows in U/P/O).

These are not mainly missing formal packaging. In most routes source object, receiver, and RH
endpoint already exist. Missing theorem is constitutive: why physical source occupies favorable
ground, crosses singular boundary, cancels all-prime oscillation, or quantizes onto correct atomic
support.

## Research programme

Highest-value research topics are those capable of supplying one of these constitutive theorems:

- canonical-ground Gamma--Slepian head control for restricted-Weil operators: prove literal
  finite-prime compression cannot overcompensate identity plus scalar Gamma and polar terms along
  exact ground's canonical cofinal heads; source alignment, ground-head convergence, prolate
  ground-vector convergence, clocks, ordering, and conditioning escape are closed;
- source-derived untruncated Jacobi Lax law and cofinal reserve-minus-controllability estimates at
  degree `n asymp sqrt(y)`, retaining the shifted-Xi boundary port (HJ-GR);
- literal Suzuki low-source cyclic spectral-mass upper bound above `1/113`, or construction of a
  source family meeting the forced `r/log^2(1/r)` lower mass; screw-kernel/Krein--Langer Morse
  exhaustion; and FE-reflected wall Ward assembly:
  explicit prime/regular-screw imbalance and remaining Robin/Neumann holonomy must pay completed
  negative-light Schur debt cofinally;
- cofinal ground-separating margins coupled to prime-log crowding, generator-energy growth,
  reduced-resolvent gaps, and Mellin evaluation norms;
- source-selected non-covariant Euler--Gamma-to-relative-trace transport proving sharp order at
  four before scalarization; scalar order itself is now RH-equivalent;
- dephased completed log-derivative convergence across exact CCM half-strip boundary, or signed/
  operator-valued positive covariance cancelling periodic aperture background;
- arithmetic Calderón Green intermediate extension with closed Lagrangian boundary relation,
  faithful nuclear harmonic complement, and strict cup-isometric Hodge comparison at the
  half-power prime scale; reciprocal fixed-star/Wold--Jordan descent is closed negatively;
- arithmetic Hall expansion for fixed factorization-generated graphs with simultaneous local load
  and moving-cutoff signed flux;
- half-height Wold residual variation with prime-gap square moment below `3/2`; or identification
  of finite retreated caustic-jet atom core with true-prime quadrature followed by signed type-zero
  Bessel defect control; or growing-packet uniform
  mean-square separation for sub-square-root massive chirp with
  literal prime-side projector; unsigned supply and finite-packet separation are closed;
- pretentious-distance continuation from Euler-convergent line into completed prime–Gamma strip;
- Route-Q arithmetic incidence or multi-observable structure that is not measurable from scalar
  theta rank, since canonical monotone quantile transport is now proved orientation-blind;
- pre-divisor quadratic-concentration conservation with finite arithmetic source budget and
  nondegenerate continued-Cauchy/Christoffel shadow maps (UQ-QC);
- integral boundary-completed or genuinely all-prime/nonlocal descent of prime dyadic Weyl pair to
  cancelled-source aggregate zero socle, beyond finite sampling-idealizer collapse (HA-SW);
- source-specific von-Mangoldt Kelvin/polyphase cross currents rather than scalar explicit-formula
  bounds;
- source-specific no-bounded-super-apex theorems and first-Hausdorff radial-flux monotonicity for
  moving-degree shifted-Xi quadrature;
- odd-sector admission for self-selected even first-contact states and Julia-normalized boundary-
  atom exclusion, rather than ordinary Padé capacity;
- persistence and source-derived sign laws on compactified finite-type Paley–Wiener cones arising
  from hard-edge first contact;
- signed lower laws or provenance-preserving bulk/ground contractivity for literal completed
  current before scalar outgoing projection; uniform scalar outgoing contractivity is now exactly
  RH, and natural-log, Suzuki-Green, Abel, and divisor-tomography handoffs are closed in Lean;
- source-first positive cross-scale synthesis for CCM-RF's fixed-width adjacent critical-Mellin
  block imbalance, preserving prime--polar cancellation inside the zero-mean Haar shell;
- source-scale Loewner budgets retaining both coefficient positivity and pointwise magnitude,
  rather than unrestricted positive-source domination;
- discontinuous source quantization, plateau fibres, and atomic moment realization without fitting
  Xi divisor after fact;
- source-relative intersection/compressed-trace identities controlling Hermitian deviation sector;
- noncommutative or singular mixing mechanisms that preserve reflection-odd horizontal class until
  annihilation, rather than radical-preserving normalization;
- an independent completed-source budget/order law for Route P's now-formal coefficient- and
  multiplicity-faithful Xi copy block; Gamma/polar transport, coupling, nonlocal cancellation, and
  order of operations are closed, but the landed short is kinematic and does not kill its nonzero
  Xi coordinate;
- completed moving-degree reverse-Bessel prime--Gamma window assembly converting half-log reserve
  and recovered Euler damping into cofinal pulse capital;
- source-native theta--Cayley half-step transport neutralizing reflection weight before divisor
  scalarization.

The separate literature-exchange paper records external state of art and proposed imports:
[`rh-route-literature-exchange-august-2026.md`](./rh-route-literature-exchange-august-2026.md).

## Shared analytic infrastructure that does not change route count

Committed results and declaration-level-audited working-tree statements close or isolate several
technical adapters:

- lattice moment transfer, harmonic floor projection, coefficient-faithful Dirichlet smoothing,
  and algebraic floor inversion are closed. Harmonic projection retains diagonal energy, and
  critical square-root stability still has sharp threshold `theta=1/2`; none gives cancellation;
- every finite seam-jet collection is nonselecting. More strongly, first `k` logarithmic-flux jets
  of a genuine `k`-prime nonlinear Euler product form a locally open set; no finite holomorphic
  jet equation can select zeta. The full all-prime jet is faithful and recovers every bounded Euler
  parameter, while full seam-log jet determines the entire carrier up to central scalar. A live
  selector must therefore use all-order prime-ray compatibility plus fixed arithmetic parameters,
  not finite jet shape (`EulerSourceJetOpenness.lean`, `SeamJetFunctionComplete.lean`);
- reciprocal seam, resolvent, shifted-Hankel, and orbifold laws close generic adapters. Exact
  quadratic divisor-front correction `(1-X^2)(1+C)=1-X^3`, jet `(1,-1,1)`, stops before Xi admission;
- Gauss moving spikes have linear total mass, harmonic spike-to-bulk transfer, and a contraction-
  direction power telescope. Remaining local step is invariance of the two-piece bulk-plus-spike
  class under the actual operator; this still does not supply C1 sign (`GaussSpikeMass.lean`);
- for real exponentials, Laguerre zero bounds, convex-cap one-pair separation, compact multi-pair localization, top-Bohr-layer nonnegativity, and unbounded error of per-pair relaxation classify fake-family admissibility, not zeta;
- rational `K_2^M` has exhaustive Tate filtration, Euclidean descent, and two-torsion tame kernel. Real Milnor groups over `Q` vanish from degree two, so Route L higher interaction must survive integrally/torsionally, adelically, by extension, or over a broader field; no Xi specialization or Hodge sign follows;
- compact brick covers, sign-separating maps, and no embedding of an `m`-cube into `R^k` for `k<m` close generic dimension adapters without prime--Gamma source or RH receiver;
- Hilbert-valued multiplier/Plancherel, weak-derivative, compact-Fourier uniqueness, torus
  dominated-convergence, finite-grid compactness, Landau, Bernstein, and coercive-renorming lemmas
  close analytic passage and regularity only; none selects a source or ground;
- Boolean degree-`m` parity needs `2^(m+1)` support points and lifts from `ZMod 2` to `ZMod 8`.
  This prices Route E local randomization but does not construct its fixed physical Hall relation;
- Schur splitting, codimension floors under averaged projections, annealed phase dephasing,
  semidefinite Hankel bootstrap, and finite negative-margin stability show averaging or scalar
  repair cannot erase a missing sector or supply Route U/G ground selection;
- nonnegative Hermitian exponential polynomials need not admit Hermitian sum-of-squares
  factorization; diagonal nonnegativity is strictly weaker than positivity of planar unfolding.
  Positivity routes must prove the operator/kernel lift, not infer it from a scalar diagonal
  (`HermitianSOSCounterexample.lean`, `HermitianSOSUnfolding.lean`,
  `HermitianSOSExtremal.lean`);
- an independent character cube needs at least its frequency rank in continuous chart dimension.
  Low-dimensional continuous coordinates cannot faithfully separate an all-prime independent
  phase cube; adding representation multiplicity without arithmetic source structure is not a
  selector (`IndependentCharacterCube.lean`, `CircleCoordinateCube.lean`,
  `CubeChartDimension.lean`, `HullChartFrequencyRank.lean`);
- sublogarithmic divisor density is now tied to a genus-zero canonical product of quadratic
  subtype/order-zero direction. This sharpens divisor-growth reconstruction but supplies neither
  Xi source admission nor critical-line orientation (`QuadraticSubtypeCanonicalDivisor.lean`);
- differential-matroid, multiple-sine, Big-Witt gcd--lcm, periodic-pencil, polynomial-zero-set,
  and Cauchy--Binet/Pluecker results provide faithful algebraic carriers without Xi admission.
- exact phase-seed collision moments/covariance and regularized spectral-collision functionals;
  capped regularization is continuous in matrix, bounds true collision, and converges to it
  at simple spectrum, while singular return graph remains invisible to subcritical Sobolev control;
- approximate-ground stability and one-dimensional compression under a supplied spectral gap,
  plus whole-line Wronskian integration by parts; neither supplies source-relative gap;
- archimedean Weil pole-plus-Gamma weight is exactly a norm constant plus weighted translation
  Dirichlet energy. Its kernel has one explicit sign change, its constant is positive at small and
  large aperture, and support geometry improves the negative-zone deficit coefficient from `2` to
  sharp pointwise `3/2`. This proves an explicit elementary positive aperture and reduces survival
  past `log 2` to one certificate, but cannot yield all-aperture positivity without nonpointwise
  prolate control (`ArchimedeanWeil{KernelSign,ApertureConstant,Certificate,SupportRefinement}`);
- nonvanishing of real-ray Riemann Xi on every positive input.

These remove interface excuses. None supplies missing Xi-typed source selection, boundary
restriction, arithmetic incidence, or annihilation theorem.

Latest prime-cancellation-budget and Xi-orbit-freeness theorems show no nonzero finite
differential-translation filter erases the all-prime source; fixed-modulus real-rooted carriers,
finite germ jets, Nyman Mellin gauges, and static-local complexity remain nonselecting guardrails.
An everywhere-entire periodic heat orbit with D-finite multiplicative anchor has finite spectrum, so holonomic infinite heat anchoring cannot supply a hidden all-prime selector.

## Final state

Corpus contains genuinely nonclassical architectures, but novelty does not imply completion. Ten lettered routes plus CCM-FU remain live; Route R is terminalized.
No new Lean cluster instantiates an eleventh route; named candidates remain incomplete and moving-degree reverse Bessel remains an unlettered disproof opening.

Latest corpus narrows multiple frontiers. E needs Menon-strength Möbius rate, not bare MR rate, before
its still-harder unit-capacity/flux theorem. G high assistance is forced into quantified
source-cyclic mass above `1/113`. L's completed one-leg singular-graph producer is now fully
classified: exactly constant prime-labelled scalar profiles descend, so every nonconstant
Wold--Jordan/fixed-star reweighting is closed negatively; rational real Milnor amplitude also has
only degrees zero and one, so only carrier-changing critical-scale arithmetic Green/Hodge
construction survives. O now has unconditional signed parity clocks, exact constrained-ground
convergence to two-mode seeds, and canonical finite Gamma--Slepian heads converging to exact
restricted-Weil ground; only arithmetic prime-overcompensation sign on that sequence remains. P's
exact precompression short is now transported coefficient- and multiplicity-faithfully through
completed Gamma/polar Xi residues, but its landed nonzero coordinate still has zero short; only an
independent budget/order law or non-spectral contraction remains. T now identifies all-order
caustic jets with prime atoms and reduces its prime-line receiver to a finite retreated atom core
modulo uniformly bounded exterior; true-prime quadrature identification, signed sub-`3/2`,
interior/type-zero assembly, and growing-Xi chirp remain. Reverse-Bessel shell expansion and genuine
truncation are locally closed; completed moving-window assembly is not. New SOS, dimension,
divisor-growth, and quartet firewalls create no route. No route proves or disproves RH.
