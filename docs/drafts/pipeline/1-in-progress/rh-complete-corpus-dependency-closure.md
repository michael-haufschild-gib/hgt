# RH Complete-Corpus Dependency Closure

- **ID:** rh-complete-corpus-dependency-closure
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** complete current `formal/` tree and every current card under `docs/drafts/pipeline/`
- **Statement:** The current research corpus contains a source-clean finite dependency DAG whose terminal theorem is `RiemannHypothesis`; every missing edge can be stated as an explicit non-circular glue lemma and proved from other corpus nodes.

## Goal

Construct the full backward dependency graph from every formal RH endpoint, match its hypotheses against all Lean declarations and pipeline theorems regardless of status, and close the strongest surviving chain. The proof may use any mathematical detour and any finite chain length. No umbrella import, named route taxonomy, card stage, or literature-shaped decomposition is authoritative over the actual current declarations and proofs.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem `<name>`, touched modules green, formal lint PASS
- [ ] 3 → 4 publication-ready: standalone paper with theorem, proof, Lean certificate, and Door-2

## Constraint

The authoritative corpus is exactly:

1. every Lean file under `formal/`, including files not reachable from `GaloisForLFunctions.lean` or `GaloisForLFunctions.RHTower`;
2. every pipeline card under stages `0` through `5`, read by mathematical content rather than status label.

Prior Route A–D summaries and umbrella-level capstone lists are excluded from the proof search.

## Live-corpus refresh protocol

Other research agents are adding and committing Lean and pipeline work concurrently. Every phase
boundary therefore starts by refreshing the recent commit range, modified and untracked Lean
files, RH-bearing declaration surface, and generated declaration index. A result is consumed as
stable only after it is present in the live tree and typechecks; an untracked or failing in-flight
module is recorded as a candidate dependency but does not close a chain.

## Attack

1. Enumerate every formal theorem concluding `RiemannHypothesis` or an equivalent proposition.
2. Normalize each endpoint into primitive hypotheses and reject hypotheses that merely restate RH or feed the zero divisor into the source.
3. Search all formal declarations and all pipeline claims for producers of each primitive hypothesis, including producers expressed in different coordinates.
4. Generate several competing cross-corpus chains before selecting one.
5. Attack the best chain through boundary, symmetric, degenerate, fake-family, and parent-theory cases.
6. Promote an edge only after its paper proof is complete; promote the terminal chain only after Lean verification.

## Two-ended closure rule

No candidate is rejected because its present gap is remote from RH.  Starting from any corpus
object, the required audit is

```text
unconditional source object
  -> source-defined intermediate objects
  -> exact zero-, multiplicity-, or index-preserving bridge
  -> a formal RH endpoint.
```

The chain may have arbitrarily many middle gaps.  It is retired only when one end cannot be typed,
when the proposed invariant is proved blind to horizontal displacement or multiplicity, or when
the source object is constructed from the Xi divisor it is meant to constrain.

## Current leading chain — rectangular Landau pole jet

The strongest two-ended chain is now closed from a false-RH divisor to an exact one-window RH
criterion:

```text
not RH
  -> nonempty right-half Xi divisor
  -> logarithmic rectangular dominant coefficients
  -> nonnegative-tail Landau transfer left of the transverse supremum
  -> analytic shifted-zeta continuation
  -> Xi-cancelled normal carrier
  -> impossible order comparison m <= m-1
  -> dominant coefficients cofinally unbounded below
  -> full rectangular Weil values cofinally unbounded below
  -> RH iff one fixed-width sampled family is bounded below.
```

Every arrow is formalized without a simple-zero assumption.  The local shifted pole over a zero of
multiplicity `m` retains order exactly `m-1`; the off-support infinite sum has order at least `m`
because local normal convergence preserves a common finite order floor.  Functional-equation
reflection folds the full dominant divisor sum to the right-half coefficient, and the remaining
part of the Weil value is bounded uniformly in aperture.

The exact positive open core is therefore source-side and strictly weaker than positivity:

```text
[OPEN CORE]
For one fixed L>0, prove one finite lower bound for
  Re Q_Xi(F_(log n/2,L))
over all sufficiently large n,
from an unconditional theta--prime--Gamma source identity.
```

This one lower bound proves RH by
`riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow`.  It must not be obtained by assuming
global Weil passivity, a zero-free half-strip, an Xi-divisor-selected domain, or any equivalent RH
criterion.  The prime explicit-formula side is expected to contain a main-term cancellation plus a
cofinal error term; proving the finite floor is the remaining scientific theorem.

The concurrent screw-coordinate formalization compresses the same target further.  With
`Psi=xiScrewDivisor`, Lean now proves

```text
Q_L(a)=2[Psi(2a)+Psi(2a-2L)-2Psi(2a-L)+2Psi(L)].
```

For an integer `m>=2`, taking `L=log m` and `2a=log(m^2 n)` gives the exact multiplicative
midpoint curvature

```text
2[Psi(log(m^2 n))+Psi(log n)-2Psi(log(mn))+2Psi(log m)].
```

This identity is formalized in `CCMMultiplicativeScrewCurvature.lean`.  The live detour is to
parameterize the Landau pole-jet chain by a fixed multiplicative subsequence and then construct an
all-prime Gamma-completed covariance or norm-square law for this multiplicative curvature.  A
finite-prime KMS or projective Born/Fisher metric cannot supply the identification: the formal
corpus proves those data are divisor- and phase-blind.

The earlier source parallelogram work now closes one more coordinate change.  With

```text
R(h)=4sinh(h/2)-sum_(q<=exp(h)) Lambda(q)q^(-1/2),
```

the moving prime--polar part of the rectangular detector is the Stieltjes pairing with one tent
centered at `2a-L`.  Integration by parts turns it into

```text
integral_[2a-L,2a]R(h)dh-integral_[2a-2L,2a-L]R(h)dh.
```

The remaining digamma term is uniformly bounded for fixed `L`.  Therefore RH is equivalent to a
finite lower floor for this single adjacent equal-block imbalance on `2a=log n`.  For `L=log m`
the blocks are exactly `[n/m,n]` and `[n/m^2,n/m]` in logarithmic measure.  This is the positive
dual of the polar--prime main-term cancellation no-go: the required source datum is not separate
control of either main term but a one-sided bound on their completed adjacent-block imbalance.

The natural Möbius-coisometry shortcut has also been tested.  The adjacent-block readout is a
zero-mean translated Haar vector, so it annihilates the common constant boundary mode and
localizes `(I-P_d)1` to one finite shell around the aperture.  However, critical differentiation
through all channels below `X` requires `omega log X ->0`, while the normalized Möbius mass lives
at `log d asymp 1/omega`; the visible mass then tends to zero.  The positive surviving target is a
noncompact cross-scale synthesis which transports the remote Möbius tail into the near-aperture
Haar shell before the critical limit.

This adjacent-block chain does not require the conjectural fixed-multiple Landau extension.  It is
valid at every original sample `2a=log N`; for `L=log m` the real endpoints are
`N/m^2,N/m,N`, whether or not the quotients are integers.  Hence one source floor for the block
imbalance composes immediately with the existing Lean theorem
`riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow`.  The integer-triple
subsequence remains an optional arithmetic refinement, not a middle gap in the leading chain.

## Secondary open core — quadratic scale scattering

[OPEN CORE] Construct, before reading the Xi divisor, a closed self-adjoint source realization
`H_source` of the positive quadratic scale Hamiltonian

```text
H_0 = -D(D+1),                 D = t d/dt,
```

on `L²(R_+, dt)`, together with a source-selected boundary/scattering perturbation whose spectral
determinant is the completed theta--Euler--Gamma function in the quadratic parameter

```text
lambda(s) = -s(s-1) = 1/4 - (s-1/2)^2.
```

The Hilbert geometry is important: the weight-one inversion
`Jf(t)=t^(-1)f(t^(-1))` is unitary for `dt`, not for `dt/t`; there `D*=-D-1` and hence
`H_0=D*D`.  The tree already proves the source identity `h=(D²+D)g_0`, the involutive reflection
`JDJ=-(D+1)`, the commutation with `D(D+1)`, the theta-cusp Fourier identity for Xi, and the
parity/half-shift sector exchange.

The committed Hedenmalm seam makes the intended perturbation concrete. Its source-defined
derivative Bezoutian has Hermitian diagonal

```text
B_X(z,conj z)
  = |XiC(z)|² * oneCauchyDiagonal(continuedPrimeArchSourceRelativeTrace,z),
```

whose nonnegativity is equivalent to anti-Herglotzness and RH. Its Wigner form is a positive
radial weight paired with the theta Wigner current, and the current has an exact
divisor-character/Bessel expansion carrying every prime-log character. This is the current
source-side candidate for the scattering boundary form; it does not yet prove its sign.

The bulk-coercivity no-go now has a formal positive dual rather than only a rejection.
`ThetaWignerEisensteinCrossEnergy.lean` proves the exact completed-square bound

```text
Re(conj(z)w) >= -(p_b(tau) normSq(z)+normSq(w)/p_b(tau))/2.
```

Thus the Wigner branch is reduced to a reciprocal-symbol boundary/scattering energy bound.  Sharp
Garding without that dual channel controls the wrong object, and Maass--Selberg positivity on the
unitary boundary line does not transport across the fixed half-unit continuation seam.

The right end is now closed in Lean:

```text
XiQuadraticSpectralReality
  := every xi zero rho has Im(-rho(rho-1)) = 0

XiQuadraticSpectralReality <-> RiemannHypothesis.
```

Thus a source-built self-adjoint spectral realization would prove RH because its spectral
parameters are real.  The remaining theorem is not abstract self-adjointness and not the algebraic
critical-line calculation.  It is the non-circular determinant/boundary identification:

```text
xi(rho)=0 -> lambda(rho) belongs to spectrum(H_source),
```

with `H_source` and its domain constructed from the theta--prime--Gamma source rather than from the
zeros.  A zero-free entire normalization is allowed; a divisor-selected domain is not.

## Environment-wide audit `[SNAPSHOT; refresh required]`

- The current tree contains 1,672 Lean files.  The root umbrella reaches 1,624 and misses 48.
- Three RH-bearing modules are outside the root closure:
  `CompletedFluxLaguerreReader`, `CompletedSEMContourBoundary`, and `PrimeClockScaleFactor`.
- Importing the root together with those omitted RH-bearing modules yields 133 declarations whose
  types mention `RiemannHypothesis` and no unconditional declaration of `RiemannHypothesis`.
- The omitted criteria are exact readers or selectors.  None supplies an unconditional producer
  for its RH-bearing premise.

Thus that snapshot's umbrella gap concealed criteria but not a completed proof.  Concurrent work
has since added the complete rectangular pole-jet chain outside the earlier snapshot; every future
environment count must be regenerated before use.

## Corpus-wide charge collapse `[PROVED FROM CURRENT CARDS]`

The strongest analytically faithful criteria are not independent missing hypotheses.  They carry
one common integer obstruction:

```text
total right-half off-line Xi multiplicity
  = ind_-(J),
J(x,y) = [Q(x)+Q(y)]/(x+y),
Q(x) = Xi'(1/2+x)/Xi(1/2+x),
  = sup_(a>0) kappa(a)
  = ind_-(I-T_0^*T_0).
```

Here `kappa(a)` is the restricted-Weil aperture Morse charge.  The real Euler-ray kernel uses only
absolutely convergent completed Euler data at `1/2+x>1`; the aperture realization and the diagonal
Fock realization preserve its complete negative index.  Consequently proving any one of these
three carriers nonnegative proves RH, but transporting between them cannot by itself remove the
charge.

## Two-ended detour audit

| Starting point | Source end | Missing middle | RH end | Verdict |
|---|---|---|---|---|
| Rectangular Landau pole jet | fixed-width two-edge divisor family, shifted-zeta continuation, and Xi cancellation are exact and unconditional | prove one source-defined finite lower bound for the sampled rectangular Weil values | `RH <->` this one family is bounded below is formalized | **Leading chain; divisor side closed** |
| Multiplicative screw curvature | the rectangular value is exactly a second difference of the real Xi screw profile; at `L=log m` it is the multiplicative midpoint curvature on `n,mn,m^2n` | construct an all-prime Gamma-completed covariance or norm-square with a uniform boundary term; fixed-multiple subsequence formalization is optional | feeds the same bounded-below rectangular endpoint | **Live detour; source route no longer waits on subsequence Lean** |
| Critical-Mellin adjacent blocks | the rectangular autocorrelation splits into one fixed tent and one moving tent; the Gamma term is uniformly bounded | prove a source lower bound for the difference of the two adjacent equal-scale averages of `R` | exactly equivalent to the sampled rectangular lower floor | **Positive source readout closed; inequality open** |
| Quadratic scale/Hedenmalm scattering | Gaussian theta seed, `D(D+1)`, weight-one inversion, exact source Bezoutian, and Wigner--Eisenstein prime current are source-defined | close the operator on `L²(dt)`; identify the Wigner radial form as its boundary/scattering form; prove a source sign or norm-square law and the determinant identity without divisor-selected data | `XiQuadraticSpectralReality <-> RH` is formalized | **Secondary live detour** |
| Graded order/disorder system | parity grading and half-integer Hurwitz sector are canonical and formalized | realize the signed swap as the boundary involution of the quadratic source operator; prove graded KMS/scattering classification; show a partition zero is a spectral degeneration | feeds the quadratic endpoint | **Live feeder**; Poisson wiring would close the profile-to-sector brick, but its current untracked draft still fails to typecheck |
| Hyperbolic/adelic scattering | prime logarithms and the Gamma ladder can be read as length and cusp data | construct an actual self-adjoint two-dimensional or adelic scattering object; identify its determinant with Xi; exclude nonreal resonances by source geometry | the same real quadratic energy endpoint | **Live geometric variant**, but the determinant realization is wholly open |
| Multivariate stable prime section | finite Euler/simplicial incidence objects and canonical finite orientations exist | build a completed prime--archimedean multiaffine section, prove stability survives the Gamma weld and cofinal limit, and identify the diagonal limit with Xi | locally uniform real-zero transfer to RH is formalized | **Live only with a new completed section**; bare Euler sections are RH-blind and a shifted local orbit already fails PF2 |
| Function-field purity degeneration | fixed-`q` Frobenius purity is a genuine theorem; coefficient FE and degree collapse exist in Lean | construct a single differentiable determinant family linking arithmetic curves to Xi and prove locally uniform zero-preserving convergence | locally uniform closed-locus transfer is formalized | **End presently untyped**: prime powers have no sequence `q -> 1`; formal `q -> 1` language is not an arithmetic family |
| Determinant-line/spectral-flow index | completed source Fredholm and seam families exist | prove a source no-first-crossing law or a null-homotopy retaining the complete defect index | the index equals off-line multiplicity | **Secondary live chain**; orientation counts crossings but does not forbid the first |
| Hurwitz monodromy/hypertranscendence | joint monodromy-character and differential-independence laws are formalized | turn a scalar zeta zero into a functional relation in the Hurwitz shift variable | no typed zero-to-function bridge exists | **Not a closed chain standalone**; usable only as rigidity inside another construction |
| Resurgence/Stokes alignment | explicit-formula trans-series language can be source-defined | identify Borel singularities without first taking `log xi`; prove source Stokes positivity/alignment | alignment is RH | **Target-fed in current form**; using the Xi logarithmic divisor builds the answer into the source |
| Böttcher/Brolin, chromatic sphere, QECC, hyperreal prime | each has a native source object or analogy | no source-defined functor to the completed zeta zero set or quadratic energy is presently typed | absent | **Fringe feeders, not proof chains yet**; retained for new functor construction, not ranked by proximity |

The previous finite Gauss/Sonin contraction remains a legitimate short chain, but its earlier
`[SELECTED]` status is revoked.  It is now one possible construction of the boundary/scattering
perturbation or of the determinant-line no-crossing law, not the search boundary.

## Status Registers

- [CONJECTURE] A long cross-coordinate chain exists and is hidden by the present file and card partitioning.
- [PROVED] The corpus contains no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration according to the current generated gap report.
- [PROVED] No unconditional Lean declaration of `RiemannHypothesis` exists in the combined current RH-bearing environment.
- [PROVED] Reality of the quadratic scale energy at every Xi zero is equivalent to RH in Lean.
- [PROVED] The weight-one inversion uses `L²(dt)`, and the corresponding formal differential expression is `-D(D+1)=D*D`; the earlier `L²(dt/t)` description was incorrect.
- [PROVED] The Hedenmalm source Bezoutian diagonal is the exact prime--Gamma one-Cauchy diagonal times `|XiC|²`, and its orientation is equivalent to RH.
- [PROVED] For every fixed `L>0`, false RH forces the logarithmically sampled rectangular Weil values below every real level cofinally, with exact analytic multiplicity.
- [PROVED] For every fixed `L>0`, RH is equivalent to this one sampled rectangular family being nonnegative, and also equivalent to its being merely bounded below.
- [PROVED] The same rectangular value is the fixed discrete curvature of the real Xi screw profile; for `L=log m` its multiplicative midpoint form on `n,mn,m^2n` is formalized.
- [PROVED] On the source side, the moving rectangular term is one critical-Mellin tent pairing, equivalently the imbalance of two adjacent equal logarithmic blocks; the remaining Gamma term is uniformly bounded at fixed width.
- [PROVED] A constant floor is stronger than necessary: an eventual lower floor `-C n^alpha` forces every zero into `Re rho<=1/2+alpha`; hence any `n^o(1)` or polylogarithmic lower loss already proves RH.  The all-epsilon observable subpower gate is now formalized in `CCMRectangularSubpowerLowerGate.lean`.
- [PROVED] The Wigner cross-energy obstruction has an exact positive dual floor controlled by the primal `p_b` energy and reciprocal-symbol boundary energy.
- [OPEN CORE] Prove one unconditional source-defined subpower lower bound for that rectangular family.  The weaker endpoint permits polynomial losses in aperture and reciprocal powers of a diagonal regulator; the Möbius/Sonin, Wigner--Eisenstein, and quadratic scattering constructions remain competing providers.
- [NOVELTY UNVERIFIED] Any completed glue theorem remains scientifically unclassified until the proof, parent-theory, literature, and rediscovery gates are run.

## Log

- 2026-07-12 — moved directly into progress for complete-corpus dependency reconstruction.
- 2026-07-12 — replaced shortcut ranking by a two-ended detour audit.  Formalized the quadratic
  scale-spectrum RH endpoint, corrected the Hilbert measure of the weight-one inversion, and
  selected the source-defined self-adjoint scattering determinant as the leading long-chain core.
- 2026-07-12 — live-corpus refresh consumed the committed Hedenmalm Bezoutian/orientation and
  Wigner--Eisenstein carrier work. The concurrent Poisson sector wiring was tested but remains an
  untracked failing draft, so it is not yet a closed dependency.
