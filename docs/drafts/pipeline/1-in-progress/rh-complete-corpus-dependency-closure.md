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

## Concurrent mapped chain — rectangular Landau pole jet

This exact chain is being pursued by a concurrent agent and is excluded from the present research
lane.  It remains in the dependency map because its right end is closed from a false-RH divisor to
an exact one-window RH criterion:

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

The concurrently owned positive open core is source-side and strictly weaker than positivity:

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
cofinal error term; proving the finite floor is the remaining scientific theorem on that external
lane.  The present sweep does not develop this estimate, its critical-Mellin reformulations, or its
Hurwitz principal-phase growth equivalent.

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

## Independent interface audit

The following interfaces have been checked against the exact live declarations.  They do not
close RH, but they prevent false cross-corpus compositions and isolate what a genuinely different
provider would have to supply.

1. **Complex versus real negative index.**  The FE seam carrier has complex negative index equal to
   its number of off-line conjugate-pole pairs.  The polarization theorem makes the negative index
   of the realified `J`-invariant form even.  These statements do not combine with the rank-one
   Krein bound to force zero: one complex negative square is already a real two-plane.  Any parity
   argument must prove parity of the complex index itself, not parity after realification.
2. **Complete Gram topology.**  The complete Cayley--Toeplitz Gram tower is continuous and injective
   on real probability measures, and the canonical inverse-Cholesky graph is closed.  Hence measure
   uniqueness and finite-frame graph closure are no longer missing.  They apply only after a real
   positive measure or positive-definite Gram tower has been produced; they do not turn the signed
   Xi reciprocal moments into such a tower.
3. **Hurwitz reflection variables.**  Xi functional-equation reflection conjugates the Hurwitz
   monodromy character, while Xi-zero differential independence concerns functions of the shift
   variable with the exponent frozen.  The exact finite relation is now known: at an actual Xi
   zero, the triple `H_rho,H_(1-rho),H_tau` is dependent exactly for
   `tau in {rho,1-rho}`.  Hence the fixed half-anchor triple is unconditionally independent, while
   the Schwarz-anchor triple `H_rho,H_(1-rho),H_(conj rho)` is dependent exactly when
   `Re(rho)=1/2`.  More sharply, the pair `H_(1-rho),H_(conj rho)` is dependent exactly when
   `Re(rho)=1/2` for every open-strip `rho`, without an Xi-zero hypothesis.  This replaces the
   earlier projective all-order anchor-jet interface by one rank-two differential circuit.  Lean
   now identifies that pair circuit exactly with vanishing of the common first-prime seam charge,
   and globally with zero scalar orientation energy.  Hence there is no independent Hurwitz
   producer to seek: the remaining input is regular-Cauchy source-core nonnegativity;
   finite analytic reflection jets alone still cannot provide it, because the corpus constructs
   arbitrarily delayed reflected-jet defects.
4. **Prime-clock category.**  Shale summability and the reflected clock-scale wall select the
   critical line exactly.  The completed-flux Fitting attachment supplies a nonzero finite
   algebraic seam at every zero, but it is not a bounded normal intertwiner of the infinite prime
   CCR sectors.  A source construction must produce an on-shell normal intertwiner or an equivalent
   representation-theoretic object; finite seam transversality alone cannot discharge Shale
   implementability.
5. **Theta raw moments versus Xi cumulants.**  The positive theta-cusp density gives nonnegative raw
   even moments and closes the constant source-Hankel level.  The higher normalized Xi trace moments
   are logarithmic cumulants.  The first nonconstant minor is already a sixth-moment concentration
   inequality, so raw-density positivity and the all-order recurrence do not close the Hankel cone.
6. **Common first-prime seam versus Hurwitz orientation energy.**  The normalized Hurwitz anchor
   tail and translated von Mangoldt source have one common first-prime charge `C_2(rho)`.  This
   charge is odd under `rho -> 1-conj rho`, and Lean now proves pointwise
   `C_2(rho)=0 <-> xiHurwitzOrientationDefect(rho)=0` and globally
   `XiHurwitzAnchorPrimeTwoSeamsVanish <-> E_Xi=0`.  Hence common-charge vanishing is not an
   additional open input: regular-Cauchy source-core nonnegativity discharges it automatically.
   The same defect is now read directly at the actual Euler point: for every prime `p`, the
   FE--Schwarz difference of `log(p)p^(-s)/(1-p^(-s))^2` is `C_p(rho)` times an explicit invertible
   factor throughout the open strip.  Thus an actual-parameter Hessian reader may use any one
   finite place and requires neither empty-chart coefficient extraction nor an all-prime limit.
   This Hessian is exactly `-1/log(p)` times the spectral derivative of the genuine Euler
   connection, and also the corresponding imaginary-slope trigamma-reflection curvature, so a
   normal-curvature source theorem may stay in its native spectral/Gamma coordinate.
   The only surviving mathematical gap in this splice is that source-core sign itself.
7. **Two-particle Sonin coherence versus common-charge normalization.**  The canonical all-prime
   seam potentials
   `C_p(rho)=log(p)(p^(-conj rho)-p^(-(1-rho)))` tend to zero along cofinal primes throughout the
   open strip.  Therefore any theorem forcing these potentials to be pairwise coherent already
   forces their common value to vanish; no archimedean normalization input remains.  The stage-2
   tensor-square Sonin theorem supplies `uniform Calkin bound -> bounded pair energy` on paper.
   Lean now proves that uniformly bounded finite reciprocal-prime pair energy is equivalent to
   coherence, and on all Xi fibres equivalent to RH.  A cross-corpus value relation factors this
   energy exactly as `2 (sum 1/p)(sum |C_p|^2/p) - 2 |sum C_p/p|^2`, reusing the theta
   square-index weighted-variance theorem.  Thus the arithmetic obstruction is a mass-amplified
   one-particle seam norm modulo one rank-one mean channel.  Lean further proves that the normalized
   pair energy tends to twice the full one-particle seam norm, which is strictly positive off the
   line.  The source hypothesis is therefore weakened from a uniform Calkin bound to sub-root
   reciprocal-mass growth `D_F=o(sqrt(sum_(p in F)1/p))`.  The exact remaining interface is this
   source-pure operator realization and growth estimate, plus formalization of the actual tensor
   lower estimate.  Existing all-prime
   Hilbert--Schmidt results do not supply the bound: they delete the divergent principal prime
   shell and assemble only the compact prime-power residual.  A further exact value relation now
   identifies the one-particle norm with the centered prime-zeta curvature
   `K(1+2 Re(rho))+K(3-2 Re(rho))-2K(2)` and with the squared prime-feature distance between
   `conj(rho)` and `1-rho`.  It is independent of zero height and dominates
   `(Re(rho)-1/2)^2 log(2)^4`, so any quantitative source estimate transfers directly to a
   horizontal zero bound; vertical prime-phase cancellation cannot be the missing mechanism.  On
   the operator side, the complete ordered pair section factors as one exterior tensor
   `A_F(a) tensor B_F-B_F tensor A_F(a)`.  This removes the separate pair-face realization gap:
   the remaining source theorem is asymptotic Calkin collinearity of the seam-weighted and
   unweighted one-particle Euler sections at the sub-root reciprocal-mass scale.  A further
   source-side value relation now closes coefficient discovery: at the horizontal projection,
   `C_p` is exactly the derivative at local parameter zero of the FE-paired finite Euler flux
   `log(p)[a p^(-s)/(1-a p^(-s))-a p^(-(1-s))/(1-a p^(-(1-s)))]`.  This is proved both pointwise
   and in the compact-carrier Banach algebra.  What remains is a bounded transfer of that
   empty-parameter tangent into the Sonin Calkin quotient, comparison with the actual-parameter
   tangent at `a=1`, and the cofinal sub-root exterior estimate; it is no longer an unknown scalar
   value relation.

The continued prime--Gamma Cauchy kernel has a complete value interface with the CCM Mellin
channel:
`XiCriticalMellinSourceFactorization.lean` constructs the canonical continued critical-Mellin
defect, proves agreement with the convergent polar--prime Laplace channel on `Re u>0`, and rewrites
the full continued Xi source kernel as the conjugate divided difference of

```text
explicit polar background - continued critical-Mellin defect - Gamma logarithmic derivative.
```

The apparent background is not an independent positive reserve.  Expanding the archimedean
logarithmic derivative cancels its two rational boundary terms exactly against the displayed polar
terms, leaving

```text
i * (continued critical-Mellin defect + Gamma connection).
```

Consequently the proposed domination theorem is exactly positivity of the full Xi source kernel
in renamed coordinates.  It is retired as a top-down discharge rather than promoted as an open
mechanism.  The distinct determinant-line alternative remains: construct a source-selected
null-homotopy or no-first-crossing theorem for a family retaining the complete negative index.

## Two-ended detour audit

Two previously separate right ends now meet exactly.  On every right-half Xi zero, the principal
argument of the negative Hurwitz monodromy character is its transverse displacement, and its
supremum is the sharp power-growth exponent of the fixed-width rectangular Weil sequence.  The
bounded Hurwitz sine defect is also the coordinate of the canonical orientation vector; that
vector lies unconditionally in the Hilbert closure of pairwise-conjugate-separated continued
Cauchy source packets, whose explicit prime--Gamma energies converge to the negative orientation
energy.  Thus the Hurwitz and rectangular branches do not supply independent orientation
mechanisms:

```text
positive Hurwitz principal phase
  = positive transverse Xi displacement
  = positive rectangular power exponent
  -> an eventually negative separated prime--Gamma source sequence.
```

The remaining choices are genuinely source-side: prove nonnegativity on the separated packet
sequence, prove positivity on the algebraic continued-Cauchy source span, or prove a subpower
bound for the rectangular source values.  The divisor-to-source closure and the phase/growth
identifications are no longer missing interfaces.

| Starting point | Source end | Missing middle | RH end | Verdict |
|---|---|---|---|---|
| Rectangular Landau pole jet | fixed-width two-edge divisor family, shifted-zeta continuation, and Xi cancellation are exact and unconditional | prove one source-defined finite lower bound for the sampled rectangular Weil values | `RH <->` this one family is bounded below is formalized | **Concurrent owned chain; excluded from this lane** |
| Multiplicative screw curvature | the rectangular value is exactly a second difference of the real Xi screw profile; at `L=log m` it is the multiplicative midpoint curvature on `n,mn,m^2n` | construct an all-prime Gamma-completed covariance or norm-square with a uniform boundary term; fixed-multiple subsequence formalization is optional | feeds the same bounded-below rectangular endpoint | **Live detour; source route no longer waits on subsequence Lean** |
| Critical-Mellin adjacent blocks | the rectangular autocorrelation splits into one fixed tent and one moving tent; the Gamma term is uniformly bounded | prove a source lower bound for the difference of the two adjacent equal-scale averages of `R` | exactly equivalent to the sampled rectangular lower floor | **Positive source readout closed; inequality open** |
| Quadratic scale/Hedenmalm scattering | Gaussian theta seed, `D(D+1)`, weight-one inversion, exact source Bezoutian, and Wigner--Eisenstein prime current are source-defined | close the operator on `L²(dt)`; identify the Wigner radial form as its boundary/scattering form; prove a source sign or norm-square law and the determinant identity without divisor-selected data | `XiQuadraticSpectralReality <-> RH` is formalized | **Secondary live detour** |
| Graded order/disorder system | parity grading, half-integer sector, Poisson profile exchange, and graded KMS phase classification are formalized | realize the signed swap as the boundary involution of a source-selected quadratic operator and prove that its determinant zeros are spectral rather than resonant | feeds the quadratic endpoint | **Constraint layer closed, orientation open**; equality of reflected phase labels is itself equivalent to the reflection fixing the zero, so KMS classification alone is not a provider |
| Hyperbolic/adelic scattering | prime logarithms and the Gamma ladder can be read as length and cusp data | construct an actual self-adjoint two-dimensional or adelic scattering object; identify its determinant with Xi; exclude nonreal resonances by source geometry | the same real quadratic energy endpoint | **Live geometric variant**, but the determinant realization is wholly open |
| Multivariate stable prime section | finite Euler/simplicial incidence objects and canonical finite orientations exist | build a completed prime--archimedean multiaffine section, prove stability survives the Gamma weld and cofinal limit, and identify the diagonal limit with Xi | locally uniform real-zero transfer to RH is formalized | **Live only with a new completed section**; bare Euler sections are RH-blind and a shifted local orbit already fails PF2 |
| Two-prime Euler--Gamma reflection constraint | every local Euler factor is exactly a reciprocal imaginary-slope Gamma pair; the FE-symmetric local determinant `B_p(s)=(1-p^(-s))(1-p^(-(1-s)))` is positive on the line, and at nonzero height simultaneous reality for any two distinct primes forces `Re s=1/2` | prove from a source-defined semilocal determinant constraint, before selecting zeros, that `B_2(rho)` and `B_3(rho)` are real on every Xi fibre | the two-prime reality selector forces every Xi zero onto the critical line | **Fringe static value chain with a closed source identity and faithful finite selector**; the remaining fibre-reality premise contains the full orientation unless a natural determinant or Sonin constraint produces it independently |
| Function-field purity degeneration | fixed-`q` Frobenius purity is a genuine theorem; coefficient FE and degree collapse exist in Lean | construct a single differentiable determinant family linking arithmetic curves to Xi and prove locally uniform zero-preserving convergence | locally uniform closed-locus transfer is formalized | **End presently untyped**: prime powers have no sequence `q -> 1`; formal `q -> 1` language is not an arithmetic family |
| Determinant-line/spectral-flow index | completed source Fredholm and seam families exist | prove a source no-first-crossing law or a null-homotopy retaining the complete defect index | the index equals off-line multiplicity | **Secondary live chain**; orientation counts crossings but does not forbid the first |
| Dyadic sharp adjacent parities | the explicit pole-cancelled sharp prime source is holomorphic and loses exactly one vanishing order at every shifted right Xi zero; every shifted pole lies in `1 < Re s < 3/2`; `RHLadder 1` is the independent even-Xi-multiplicity rung | construct an analytic square of the cancelled source, or prove its divisor is even, on the collision band; construct only the first Xi parity rung from a source model | source order and Xi order would be consecutive even integers, hence no right zero and RH | **Independent cross-route collision**; strictly weaker than cancelled-source zero-freeness, uses neither sampled lower bounds nor all-rung divisibility; ordinary coefficient control on `Re s > 3/2` does not cross the required continuation seam |
| Xi--Hedenmalm common Kummer cover | the source-defined `E_Xi=XiC+i XiC'` has exact order `m-1` at every XiC zero of order `m`; functional-equation reflection sends a right-half Xi zero to the centered upper half-plane | construct analytic degree-`d` roots of `XiC` and `E_Xi` on the upper half-plane for one `d>1`; minimally, construct `RHLadder 1` and a square root of `E_Xi` | root divisibility gives `d | m` and `d | (m-1)`, hence no upper-half XiC zero and RH | **Independent source-coordinate collision formalized**; the `E_Xi` root is strictly weaker than Hermite--Biehler zero-freeness because even-multiplicity `E_Xi` zeros are allowed; the earlier raw-derivative version remains a generic corollary, while this is the source-natural target |
| First ladder--Hedenmalm Jordan-normal collision | every positive `RHLadder k` forces every right-half Xi order to be even; the canonical local Hedenmalm divided-chain block is normal exactly when that one Xi divisor point is simple, with no spectral-reality condition | construct one positive ladder rung and prove normality only for the local blocks at existing right-half divisor points; stronger sufficient providers are the first quotient-value constraint, theta-span density, or `continued Cauchy closure <= Hedenmalm theta closure` | right-half local normality makes the same hypothetical zero have order one, while the ladder makes it even, hence no right-half zero and RH | **Weakest independent multiplicity/operator collision formalized**; unlike block Hermiticity, local normality contains no RH orientation, and unlike global simplicity it imposes nothing on critical-line or left-half zeros |
| Hedenmalm local-normality × numerical sector | the local Jordan block is normal exactly at multiplicity one; at a simple fiber the reciprocal-operator numerical value is `Im(alpha^(-1)) * ||theta||^2`, FE reflection replaces `alpha` by `-alpha`, and at a multiple fiber the theta vector and numerical value vanish | prove the upper numerical-sector inequality directly from a prime--Gamma source form and provide right-half local normality; the stronger continued-Cauchy-to-Hedenmalm closure condition is an existing sufficient simplicity provider | reflected one-sided inequalities force every simple centered spectral point real; local normality excludes the multiple fibers invisible to the numerical value; hence no right-half zero and RH | **Exact complementary constraint × orientation product formalized**; local normality allows simple off-line zeros, while the numerical sector is automatically blind at multiple zeros, so neither premise alone contains RH |
| First-divided-source numerical sector | the exact divided-chain recurrence gives `J(M_z Q_rho) = alpha_rho J(Q_rho)` whenever a linear source quotient kills Xi; the fixed two-point quotient at `u=-i,v=-2i` lies in the prime-source half-plane, kills Xi, and has the explicit nonzero value `XiC(u)XiC(v)(v-u)/((u-alpha_rho)(v-alpha_rho))` on every fiber, including multiple zeros | prove the fixed two-point upper-sector inequality from a coefficient-level or cofinal prime--Gamma theorem formulated before divisor insertion; global two-pole CCM energy alone does not localize individual reflected fibers | the numerical-value imaginary part is exactly `Im(alpha_rho) * ||J Q_rho||^2`; FE reflection supplies the opposite sign, so every centered coordinate is real and RH follows | **Multiplicity-robust static value chain formalized with quotient and faithfulness discharged**; removes the global symmetric operator and simplicity/local normality, but the remaining fiberwise sign is exactly the orientation content of RH unless a genuinely stronger source localization theorem supplies it |
| Arakelov algebraic-integrality × conjugate contractivity | the Arakelov coordinate sends the critical line to the unit circle and right-half points to the open unit disk; a nonzero integral minimal polynomial has nonzero integer conjugate product | realize every Xi-zero Arakelov coordinate as an algebraic integer and prove every complex conjugate lies in the closed unit disk, without assuming spectral unitarity or zero location | the integer conjugate product has norm at least one while contractivity makes it at most one; the distinguished coordinate has norm one, hence the zero is critical and RH follows | **Fringe arithmetic collision formalized**; integrality alone has no Archimedean orientation and the contractivity predicate is empty for nonintegral values, but no source producer exists and expected zero transcendence makes integrality a major plausibility risk |
| Arakelov × Hurwitz algebraicity | `w(rho)=1-1/rho` is the FE inversion coordinate and `q(rho)=exp(-2*pi*i*rho)` is the complete Hurwitz differential-dependence character; algebraicity of `w` makes `rho` algebraic, while `q=(-1)^(-2rho)` on the principal branch | construct an arithmetic source model which makes both coordinates algebraic at every hypothetical right-half Xi zero, for example an algebraic Arakelov divisor together with an algebraic monodromy realization | Gelfond--Schneider forces `-2rho` rational, hence `rho` real; Xi is positive on the open real critical strip, so no right-half zero exists and RH follows | **Static cross-coordinate arithmetic collision formalized**; neither algebraicity factor contains orientation alone, but the route is fringe because no algebraicity producer exists and expected zero transcendence makes the Arakelov premise especially implausible |
| Integral Arakelov × relative Hurwitz algebraicity | an integral Arakelov coordinate generates an algebraic field `Q(w(rho))`; a mixed source polynomial or finite module may make `q(rho)` algebraic over that field without separately presenting an absolute polynomial for `q` | construct integral Arakelov coordinates and a source-defined nonzero relation `P_rho(q(rho))=0` over `Q(w(rho))`, uniformly before divisor selection | algebraicity descends through `Q(w(rho))/Q`, after which the Arakelov--Hurwitz Gelfond--Schneider collision forces the hypothetical zero real and excludes it, hence RH | **Relative value-relation chain formalized**; strengthens the pointwise transcendence law to the full Arakelov coordinate field and exposes a mixed algebraic-curve provider, but both source inputs remain unsupported and arithmetically implausible |
| Arakelov × finite Hurwitz differential atlas | for nonintegral exponents, two continued-Hurwitz functions are differentially dependent exactly when their monodromy characters agree; more generally, adjoining one exponent to a finite monodromy-separated anchor family destroys differential independence exactly when its character repeats an anchor character | construct a finite nonintegral Hurwitz anchor family with pairwise distinct algebraic characters and prove every hypothetical right-half Xi-indexed Hurwitz function lies in its differential-matroid closure; independently make the corresponding Arakelov coordinates algebraic | finite capture transfers algebraicity from an anchor character to `q(rho)`; the Arakelov--Hurwitz Gelfond--Schneider collision then forces `rho` real and excludes the zero, hence RH | **Function-value producer chain formalized**; the anchor may vary or be nonreal, so dependence alone has no RH orientation, but unconditional Xi Hurwitz freeness makes finite capture highly restrictive and no source relation currently supplies it |
| Hurwitz FE--Schwarz rank-two circuit | for every open-strip `rho`, without assuming Xi zerohood, `H_(1-rho)` and `H_(conj rho)` are differentially dependent exactly when `Re rho=1/2`; the pair circuit is also exactly `C_2(rho)=0`, and globally exactly zero scalar orientation energy; the exact heat-tail value relation is `log(p)[c_p(1-rho)-c_p(conj rho)]=C_p(rho)`, so the entire reflected prime tail collapses to its `p=2` member; the actual Euler-point tangent difference is likewise `C_p(rho)` times an invertible rational factor, and that tangent is `-1/log(p)` times the genuine spectral connection curvature and an imaginary-slope trigamma-reflection curvature; equality at any one prime therefore suffices in any of these coordinates; separately, the three-node anchor locus at an actual Xi zero is `{rho,1-rho}`, so the fixed half-anchor is always independent | prove nonnegativity of the Weil form on the algebraic regular-Cauchy prime--Gamma source span, or independently produce graded reality of one finite spectral-connection/trigamma curvature from a completed source reader; closure and pair/charge/energy identification are already discharged | either source-core positivity or the one-prime curvature value equality kills one faithful prime seam; this gives zero orientation energy, fixes the reflected heat-tail coefficients, makes every FE--Schwarz pair dependent, and yields RH | **Positive route collapse: differential circuit, any one actual Euler tangent or spectral/Gamma curvature, first-prime seam, reflected heat prime tail, and scalar orientation energy are one defect; the new native-curvature interface removes coefficient extraction, but does not itself produce the source equality** |
| Outer-Euler Xi modulus × first-prime seam | at the same reflected fibre and any fixed shift `h>=1`, both Xi values lie in `Re s>1`; Sondow--Dumitrescu makes their logarithmic modulus defect have sign `Re rho-1/2`, while the demodulated first-prime seam has the opposite sign | prove from a divisor-free completed source constraint that the full prime--Gamma modulus defect and the least-prime inverse defect have nonnegative product | unconditional antialignment and the assumed alignment force both defects to vanish; the common first-prime charge then vanishes, the scalar orientation energy is zero, and RH follows | **Paper-proven cross-scale value interface**; exact equality is weakened to one semidefinite coupling at two absolute-Euler nodes, but functional-equation reflection preserves the product and does not supply the missing alignment |
| Height-adaptive scalar DISC census | the unconditional Jensen/growth theorem gives one fixed envelope `N_Xi(r) <= C(1+r)log(2+r)`; the total right-half upper-box order below integer height `n` is bounded by the global disc mass in `B(2,n+2)` | for each integer `n >= 1`, prove one scalar boundary relation `discCensusH k_n n = 0` with `2^k_n` above that envelope | the box mass is divisible by `2^k_n` and strictly smaller than it, hence zero; integer-height exhaustion gives RH | **Weakest countable finite-depth chain formalized**; no local order divisibility, Kummer root, global branch, or inter-height compatibility is required; regional roots remain an overpowered sufficient provider, while the open core is one completed-source finite-ring census value per height |
| Height-adaptive cancelled-source socle--Weyl contradiction | the cancelled source pair `(A,C)` defines a finite zero algebra and multiplication by `C`; its image has one socle dimension per distinct right-half zero and is bounded by the unconditional Jensen envelope | construct, before enumerating zeros, one internal dyadic Weyl pair on that undoubled image at a depth above the envelope; finite-prime operators on the full real-Xi sampling quotient are formally excluded, so the producer must be integral boundary-completed or genuinely all-prime/nonlocal | if RH is false the socle dimension is positive, while the determinant relation forces divisibility by a larger power of two and hence dimension zero; bounded exhaustion then gives RH | **Nontrivial contradiction chain with both ends closed and one source-realization core**; the direct finite-prime shortcut is dead, but its positive replacement is exact: source the nonzero boundary holonomy and annihilate the top-jet Weyl anomaly without importing the socle dimension |
| Four-unit pole-to-divisor trace-slope contradiction | the finite-prime completion has the unique upper anti-causal Euler-pole profile `2 exp(-t/2)` of squared `L²` energy `4`; a nonempty right-half Xi divisor has a positive Cauchy-Gram residue profile whose energy is strictly greater than `4` per integer divisor unit | construct a pointed, source-defined, nonexpansive all-prime-plus-Gamma continuation from the pole profile to the Xi divisor profile; weak graph-core compactness can transfer a uniform four-unit estimate but cannot create it | false RH gives Xi residue energy `> 4`, while source nonexpansiveness gives energy `<= 4`, a contradiction and hence RH | **Strongest analytic contradiction chain in the paper-proven layer**; both numerical endpoints and the compactness transfer are proved, but the one source transport theorem remains open; canonical real-spectrum stages, theta-cusp screens, and signed-Moebius tails have been tested and merely restate the same horizontal control |
| Burnol co-Poisson quotient Berezin diagonal | normalized dilation and inverse dilation give the exact defect imbalance `||epsilon^-||²-||epsilon^+||²=(r^(2 Re rho-1)-r^(1-2 Re rho))||Z^a_rho||²`; Burnol identifies the closed zero-evaluator span with the orthogonal complement of an explicitly generated co-Poisson source subspace; projecting ordinary evaluation kernels to this complement constructs a canonical faithful Berezin diagonal with exact Fourier-reflection oddness | weakest: prove the scalar Berezin value is nonpositive on every right-half co-Poisson annihilator character; stronger: prove `B_+B_-^*=0`, kill the parity block of the finite holonomy, or construct a contractive Douglas factorization between the forward and inverse quotient channels | the scalar value on a zero fibre is exactly `2 sinh(2 log(r)(Re rho-1/2))`; its sign excludes right-half off-line zeros and FE--Schwarz gives RH; any strong quotient order automatically saturates to flatness by Fourier reflection | **Source-pure short chain proved on paper with the abstract diagonal-functional gap now discharged**; the weakest open input is one scalar co-Poisson source sign, while full quotient decorrelation is a stronger optional provider; neither a Calkin lift nor prime-charge coherence is needed |
| Burnol--Hedenmalm boundary-null graph completion | Burnol's source-defined critical Sonine carrier contains a complete/minimal family `zeta(s)/(s-rho)^k`, while archimedean completion places the corresponding `XiC(z)/(z-alpha)^k` in the maximal real-coordinate domain with exact defect `M_z q_alpha=alpha q_alpha+XiC`; the uncompleted domain failure and completed radical requirement form a proved exchange law | construct a Burnol-specific aperture trace identity which makes `XiC` null, retains every first divided vector, transports the first two divided recurrences, and makes the coordinate operator closed and symmetric; generic critical-aperture limits, de Branges extensions, Green regularizations, ordinary `L²`, and divisor-selected metrics all collapse to the existing real-boundary faithfulness obstruction | a hypothetical nonreal zero becomes a nonzero eigenvector of a symmetric operator with nonreal eigenvalue; a multiple zero becomes a forbidden length-two Jordan chain; hence RH and simplicity | **Conditional endpoint retained; generic graph route retired**. Burnol near-hereditary completeness does not repair the gap: off-line quartets do not construct mixed complements, and the codimension-at-most-one theorem is generic in de Branges spaces. Its positive successor is exact but stronger: an off-line orbit must source two independent mixed complements, or the Sonine aperture must supply a genuinely new null-trace identity before Hilbert completion. |
| Radial-Jensen Schur exact norm gap | the source height and orientation laws put every reciprocal-square atom in the disk `|u|<2/41` and the sector `Im(u)^2<=Re(u)^2/84`; Schwarz--Pick then proves that the fixed prime--Gamma evaluation functional has exact disk-Schur and `L¹/H¹_0` norm `primeArchCentralCurvature`, attained by the constant `1`; the finite Caratheodory--Fejer norms converge geometrically to that curvature | prove a source theorem controlling the trace norm of the reciprocal-square operator, or positively couple its analytic algebra to its adjoint, absolute value, or polar phase; no further holomorphic value relation inside the same disk algebra can enlarge its norm | `2*(trace norm-analytic functional norm)` is exactly `xiGlobalReflectionDefectEnergy`; any reverse norm inequality kills that energy and yields RH | **Exact constraint--orientation decomposition proved on paper**; the former open quotient-norm target is discharged and retired, while the remaining trace/analytic gap is identified exactly rather than hidden in an extremal problem |
| Explicit prime--arch circle state × reflected orientation | the full normalized moment sequence is the Fourier sequence of one source-defined real-analytic probability density `w_Xi/M`, with the uniform bounds `734/819 <= w_Xi/M <= 904/819`; its Caratheodory transform gives an explicit Schur function of norm at most `85/1553`, and multiplication plus circle conjugation gives a canonical unitary/reflection carrier; every polynomial with `85*sum_(n>=1)a_n^2 <= 734*a_0^2` already has nonnegative reflected value | prove radial Poisson disintegration of this one explicit density, equivalently `||S_P||_(L²(mu_Xi)) <= ||C_P||_(L²(mu_Xi))` only for the remaining degree-at-least-two tail-dominant integer-polynomial cone; ordinary density coercivity and strict Schur contractivity cannot supply the unrestricted sign | the reflected orbit Gram is exactly the normalized prime--Gamma Hankel matrix, so the restricted weighted cosine--sine inequality plus the unconditional coefficient cone gives the complete integer Hankel cone and RH | **Carrier, ordinary positivity, and a nontrivial all-degree coefficient region discharged on paper; one transverse tail cone remains**; the family `1-epsilon*cos(2*N*t)` proves that no uniform neighborhood of Haar lies in the reflection-positive cone, so a successful predecessor must use exact source Fourier relations rather than a norm-only estimate |
| Shifted sector circles × residual Sonin comparison | for every `0<=s<=12`, the reciprocal-square sector and radius give a strictly positive analytic circle density with Fourier moments `m_(s+n)/m_s`; after `P=X^v q`, this unconditionally proves the prior cones for `v<=5` and the new valuation-six cone `32*sum_(n>=1)b_n^2<=7b_0^2` | prove the one-sided coupled-Sonin aperture comparison only for the complementary integer-polynomial family; no Sonin value relation is needed on the discharged valuation cones | nonnegative Sonin values exclude a negative residual target, the shifted circles handle the omitted tests, and the complete integer prime--Gamma Hankel cone gives RH | **New cross-route hypothesis reduction proved on paper; thirteenth-mass core formalized**; exact degree-thirteen sector algebra passes the previous cosine cutoff, while valuation at least seven and tail-dominant lower-valuation tests remain open |
| OPUC dyadic logarithmic-phase terminal | every zero of a stable paraorthogonal terminal with unimodular endpoint lies on the unit circle, while `|exp(i log(2)z)|=exp(-log(2)Im(z))`; the interior-root exclusion and the complete RH consumer are formalized | construct from the divisor-free completed theta--prime--Gamma source a stable polynomial family `p_z`, a unimodular endpoint, and the exact evaluation `T_z(exp(i log(2)z))=A(z)XiC(z)` | a hypothetical off-line Xi zero becomes a strict open-disk paraorthogonal root, but root location forces unit modulus and hence `Im(z)=0`, proving RH | **Nontrivial contradiction chain with both ends closed and one exact source-value core**; the phase-adapted Prouhet symbol cannot itself be the OPUC terminal because it has the interior phase root for every strip point.  Its positive successor is a distinct stable source terminal whose evaluation, rather than its coefficients, is selected by Xi. |
| All-prime Sonin value loci and cofinal section | the residual energy `T_a=K_a^*K_a` is positive trace class and its Gram tower collapses exactly to `S_r(a)=Tr(T_a^(r+1))` | weakest: put each fixed prime--Gamma integer-polynomial value in the closure of the corresponding scalar Sonin Gram range; stronger source condition: put every finite prime--Gamma moment block in the corresponding positive Sonin moment-curve closure | finite-block closure is now proved equivalent to one positive aperture sequence converging in every moment coordinate, and either source-value condition transfers positivity to the countable prime--Gamma trace-Hankel cone and RH | **Independent live value-relation chain**; coherence is discharged by diagonal closure selection, but the analytic source-to-source finite-block closure remains open |
| Theta low-degree discharge × prime--Gamma Hankel tail | the two explicit theta-cusp moment-ratio inequalities force every constant and linear real-polynomial prime--Gamma Hankel test to be nonnegative; one strict ratio makes the first nonconstant leading determinant positive; the exact first/higher-atom likelihood order now proves that each first-atom transfer loses only one factor `c=3005/2997`, not `c^2` | prove the sharpened first-atom inequalities `14*c*a_2^2<=9*a_1*a_3` and `16*c*a_0*a_2<=45*a_1^2`, and either the degree-at-least-two integer-polynomial cone or only the scalar leading-determinant tail from size three | the likelihood-ordered transfer gives the complete low block; the degree dichotomy reconstructs the complete countable source cone, or the strict low block plus one determinant per size reconstructs the leading-determinant criterion; either chain implies RH | **Top-down interface strictly weakened on paper**; the polynomial tail starts at degree two and the scalar tail at matrix size three, while the two old `c^2` low-degree premises are superseded by single-loss `c` premises and await a small Lean adapter |
| Hurwitz monodromy/Cauchy source | the Xi-indexed Hurwitz family is differentially free; its character phase is the exact transverse coordinate; the canonical orientation vector is reconstructed by separated continued-Cauchy packets with exact prime--Gamma energies | prove nonnegativity for the explicit separated source packets, or on their algebraic span, without importing a zero-location sign | eventual nonnegativity of one reconstructed source sequence is equivalent to RH; the same phase is the sharp rectangular growth exponent | **Live source-sign chain**; closure, multiplicity, and source-domain interfaces are discharged |
| Euler-safe critical-logderivative Cauchy loss | on every `Re(w)>a>1/2`, horizontal Xi monotonicity makes the shifted Carathéodory kernel `K_a` positive, the normalized Hardy kernel `C_a=2a/(w+conjugate(v))` is a positive Laplace Gram, and the exact identity is `K_0=K_a-K_a circle C_a` | prove the explicit finite Cauchy--Laplace observability inequality for the absolute-Euler density `h_a(t)=Re L(a+it)`, equivalently contract the diagonal map `e_w -> e_w tensor c_w`; a two-node positive-real counterexample proves this is not automatic | `K_a circle C_a<=K_a` gives positivity of the RH-complete critical kernel on an Euler uniqueness half-plane and hence RH | **Complex-node absolute-Euler refinement of the existing half-unit diagonal-Fock bridge**; all input values lie on `Re(s)=1/2+a>1`, the test family is countable for rational `a`, and no divisor, continued anti-Herglotz sign, theta current, or limiting measure enters the premise |
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
- [PROVED] The normalized principal Hurwitz phase is exactly the right-half transverse displacement and its supremum is the sharp rectangular power-growth exponent.
- [PROVED] For every open-strip exponent, the continued-Hurwitz functions at its FE and Schwarz reflections are differentially dependent exactly on the critical line, with no Xi-zero hypothesis.  On the Xi divisor this rank-two circuit law is equivalent to RH.  The larger FE-anchor locus is exactly `{rho,1-rho}`, so the fixed half-anchor triple is always independent.
- [PROVED] The rank-two FE--Schwarz circuit is pointwise equivalent to vanishing of the common first-prime seam charge and to convergence of the normalized Hurwitz anchor seam to zero; globally it is exactly zero scalar orientation energy.
- [PROVED ON PAPER] The FE--Schwarz difference of each heat-tail prime coefficient is exactly the
  corresponding seam divided by `log p`; the whole reflected prime tail therefore collapses to
  its scale-two member.  On the open strip the same seam is the numerator of the actual semilocal
  Euler connection difference, with an explicit invertible Euler denominator.  The Lean source is
  umbrella-wired but targeted verification is deferred under the active no-computation boundary.
- [PROVED] Relative to any actual critical-line Xi anchor, the reciprocal-square weighted sum of squared imaginary anchored two-node Hurwitz Vandermonde determinants is exactly the canonical orientation energy; the HGT separator, one-vector Weil obstruction, and scalar energy are one value relation.
- [PROVED] The full Hurwitz orientation vector belongs to the Hilbert closure of pairwise-conjugate-separated continued Cauchy packets in the analytically continued prime--Gamma source domain; their exact source energies converge to the negative orientation energy.
- [PROVED] The common first-prime Hurwitz-anchor/all-prime seam charge is reflection-odd, and
  vanishing of every Xi-indexed common seam is exactly `E_Xi=0`; it introduces no gap beyond the
  regular-Cauchy source-core sign.
- [PROVED ON PAPER] At every open-strip fibre and every fixed `h>=1`, the logarithmic modulus
  defect between `xi(h+conj(rho))` and `xi(h+1-rho)` is strictly antialigned with the demodulated
  first-prime seam.  Both Xi values lie in absolute Euler convergence.  Therefore any independent
  nonnegative cross-scale alignment forces the common charge to vanish and proves RH; reflection
  alone preserves the product and supplies no such alignment.  See
  `xi-outer-euler-modulus-first-prime-seam-antialignment.md`.
- [PROVED] The canonical seam charge tends to zero along cofinal primes, so all-prime coherence
  forces the common charge to vanish and then forces RH.  Uniform boundedness of its finite
  reciprocal-prime pair energies is now formally equivalent to RH, and false RH produces one
  actual Xi fibre with arbitrarily large finite pair energy.  This removes the extra normalization
  hypothesis from the paper-proven two-particle Sonin route; only its canonical source-side
  uniform Calkin bound and the actual tensor estimate remain open.
- [PROVED ON PAPER] Burnol's cross-aperture evaluator law is a projected identity, not a
  full-vector identity.  Retaining the two orthogonal defects for normalized dilation and inverse
  dilation yields an exact signed energy difference whose sign is `Re(rho)-1/2`.  A same-point
  source contraction on right-half Xi evaluators therefore implies RH directly.  Burnol's
  co-Poisson orthogonal-complement theorem removes the divisor from this premise: it is enough to
  prove vanishing of one parity-mixing block of the explicit finite dilation holonomy compressed
  to the source-defined co-Poisson quotient.  Fourier oddness shows that either semidefinite order
  already forces this exact flatness, and Douglas factorization turns the order into a contractive
  channel-intertwining value relation.  This bypasses the co-Poisson/time-band lift, prime-pair
  coherence, and cofinal charge decay.  No proof of the parity block relation is currently known.
- [PROVED ON PAPER] The closed co-Poisson quotient is point-evaluable, so projecting Burnol's
  ordinary evaluation kernels constructs a canonical faithful Berezin diagonal without choosing
  or biorthogonalizing zeros.  Its value on a zero fibre is the exact bilateral aperture character
  and is odd under Fourier reflection.  This removes the off-diagonal parity-block relation from
  the weakest chain: only the scalar Berezin sign on the co-Poisson annihilator spectrum remains.
- [PROVED] The height-free seam coefficient is the exact empty-parameter first derivative of a
  finite FE-paired Euler flux, pointwise and in the compact-carrier Banach algebra.  Its total
  reciprocal-prime energy equals the Xi seam reflection distance.  The Sonin route now lacks an
  operator-topology transfer and cofinal rate, not a source origin for the coefficients.
- [PROVED] The continued prime--Gamma trace and its RH-bearing Cauchy kernel factor globally through the canonical continued critical-Mellin defect; the defect agrees with the convergent polar--prime Laplace channel on its right-half-plane domain.
- [PROVED] The FE-paired finite Euler connection has an exact upper-half-strip Poisson radial-difference diagonal, and the literal one-sided finite-place contribution to the completed divided difference is exactly half that value.  Their common sign is governed by one explicit cosine threshold, and prime-log Kronecker density puts every finite nonempty packet in both strict sign chambers.  Thus finite-place connection positivity is retired; the positive completion target is phase-locked compensation of this negative chamber by the cofinal prime--Gamma remainder.
- [PROVED] Every finite semilocal Euler multiplier is exactly a product of reciprocal Gamma-reflection pairs with prime-dependent imaginary slopes.  The FE-symmetric one-prime product is a reciprocal Gamma quartet, and simultaneous reality of the quartets for any two distinct primes selects the critical line at every nonzero height.  This supplies a new finite static value chain; no source theorem currently forces those two values real on Xi fibres.
- [PROVED] On the regular continued-source domain, the polar boundary terms cancel exactly against the rational part of the archimedean logarithmic derivative, leaving `i * (critical-Mellin defect + Gamma connection)`; polar--Gamma domination is therefore the original Xi source sign, not an independent discharge.
- [PROVED] Static membership of every finite prime--Gamma moment block in the closure of the positive-aperture all-prime Sonin moment curve implies simultaneous block schedules, the existing per-test positive Gram coupling, and therefore RH; this is a source-value locus premise rather than a sign premise.
- [PROVED] Poisson wiring and graded KMS classification are formalized, but they do not discharge orientation: reflected-label equality at a zero is equivalent to the reflection already fixing that zero.
- [PROVED] Ordinary `L²` theta cyclicity cannot discharge Hedenmalm completeness: every nonzero Hedenmalm form is forced to be singular relative to the ordinary `L²` topology.
- [PROVED] The new square-root vertical zeta bound does not close the Hardy-sign-change endpoint; that endpoint still requires a local completed-carrier second-moment floor dominating its closed first-moment budget and the remaining seam/Jensen transfer data.
- [PROVED] Triviality or null-homotopy of the CCM determinant line over a spectral interval is blind to the Evans zero divisor: a trivial line admits sections with arbitrary finite zero divisors, and zero winding counts only signed crossings.  The positive replacement is a source homotopy through nowhere-zero sections, or boundary nonvanishing plus a source-derived one-sided crossing orientation; see `determinant-line-trivialization-zero-divisor-blindness.md`.
- [EXTERNAL ACTIVE CORE] Prove one unconditional source-defined subpower lower bound for the rectangular family.  This exact `Q_{L,n}` route and its equivalent critical-Mellin, screw-curvature, and principal-phase growth estimates are owned by a concurrent agent and excluded from this lane.
- [OPEN CORE] Independently pursue one of four non-sign producers: construct a source-selected nowhere-zero determinant-section homotopy or one-sided crossing law retaining the complete negative index; prove the canonical two-particle Sonin finite sections uniformly bounded modulo compacts; find genuinely additional structure of the coupled critical-Mellin--Gamma source beyond its Xi-kernel sign; or classify the simultaneous finite-block cluster points of the positive all-prime Sonin trace-moment curve and place the prime--Gamma vector in that closure.  None may be obtained from the Xi divisor, an RH-equivalent limiting measure, or a hidden zero-free assumption.
- [NOVELTY UNVERIFIED] Any completed glue theorem remains scientifically unclassified until the proof, parent-theory, literature, and rediscovery gates are run.

## Log

- 2026-07-12 — moved directly into progress for complete-corpus dependency reconstruction.
- 2026-07-12 — replaced shortcut ranking by a two-ended detour audit.  Formalized the quadratic
  scale-spectrum RH endpoint, corrected the Hilbert measure of the weight-one inversion, and
  selected the source-defined self-adjoint scattering determinant as the leading long-chain core.
- 2026-07-12 — live-corpus refresh consumed the committed Hedenmalm Bezoutian/orientation,
  Wigner--Eisenstein, Hurwitz phase/source reconstruction, Poisson wiring, and graded KMS work.
  The Hurwitz and rectangular right ends now share one exact transverse coordinate; their common
  open content is a source sign or subpower estimate, not another divisor-to-source bridge.

- [PROVED FROM LITERATURE + PAPER ALGEBRA] The degree-one logarithmic source functional is already
  canonical before Sonin compression: it is the finite part of Connes's semilocal cutoff trace,
  equal to the sum of local Weil distributions, and its quantized-differential class is additive
  modulo conjugation coboundaries.  The `p^m` mode has the exact orbital response `log(p^m)`.
  Hence the remaining Sonin interface is an exact Connes-to-Sonin comparison/descent preserving
  this finite part and proving a completed lower floor; it is not construction of an unspecified
  relative trace.  The bounded Hilbert--Schmidt projection-correction scalarization cannot carry
  the full class.

## Semilocal source-connection interface closed before compression

The July top-down audit closes two construction nodes that were previously conflated.  The
Connes--Consani--Moscovici theorem identifies every finite semilocal Sonin space with the classical
space at the same aperture.  The companion paper theorem
`../2-fully-proven/not_new_scientific_knowledge/semilocal-dual-pair-euler-connection-source-law.md`
then differentiates the explicit place multiplier and obtains

```text
theta_S^(-1)D_S theta_S-D_infinity
  =M_(-sum_(p in S_f)L_p'/L_p),                           (DC1)
```

whose Fourier coefficients are the finite von Mangoldt weights.  Together with
`connes-semilocal-finite-part-orbital-source-class.md`, this identifies one degree-one source datum
in three representatives: semilocal cutoff finite part, orbital cyclic class, and Euler connection.
The remaining dependency is strictly the Sonin cutoff/resolvent cyclic descent preserving this
value, plus the completed one-sided floor.  Carrier existence, place comparison, and finite prime
source identification are no longer open nodes.

## 2026-07-15 radial-Jensen Schur exact norm-gap insertion

- [PROVED ON PAPER] The source-derived radius `2/41` and orientation sector `1/84` satisfy a
  general Schwarz--Pick small-sector criterion.  The fixed prime--Gamma moment functional has exact
  complex disk-Schur norm
  `S_Xi=primeArchCentralCurvature`, attained by the constant function `1` unconditionally.
- [PROVED ON PAPER] The reflected boundary symbol therefore has exact `L^1/H^1_0` quotient norm
  `primeArchCentralCurvature`; the former open quotient-norm saturation target is discharged, not
  promoted to an RH producer.
- [PROVED ON PAPER] The exact norm deficit is
  `xiCenteredRadialJensenMass-S_Xi=xiGlobalReflectionDefectEnergy/2`.  In operator language, the
  full orientation datum is precisely the excess of trace norm over the norm visible to the
  analytic functional calculus.
- [PROVED ON PAPER] Caratheodory--Fejer truncations converge geometrically to central curvature,
  with error at most
  `xiCenteredRadialJensenMass*(2/41)^(N+1)/(1-2/41)`; their trace-norm dual certificates cannot
  converge to radial Jensen mass unless RH already holds.
- [OPEN] Produce a source theorem controlling the reciprocal-square trace norm, or coupling the
  analytic source algebra to the adjoint/absolute-value/polar channel.  Additional holomorphic
  identities in the same disk algebra cannot change its already exact norm.

## 2026-07-15 explicit circle-state reflection insertion

- [PROVED ON PAPER] The complete normalized prime--Gamma moment sequence is the Fourier sequence
  of one explicit source-defined real-analytic probability density `w_Xi/M` on the unit circle.
- [PROVED ON PAPER] The exact source estimates give
  `734/819 <= w_Xi/M <= 904/819`; its Caratheodory transform has positive real part and its Schur
  transform has closed-disk norm at most `85/1553`.
- [PROVED ON PAPER] On `L^2(T,mu_Xi)`, multiplication by the circle coordinate and circle
  conjugation construct an unconditional unitary/reflection carrier.  Its ordinary Gram is
  Toeplitz-positive, while its reflected Gram is exactly the normalized prime--Gamma Hankel form.
- [PROVED ON PAPER] Every real polynomial with
  `85*sum_(n>=1)a_n^2 <= 734*a_0^2` has nonnegative reflected value unconditionally.  Therefore the
  countable RH criterion may be restricted to the complementary tail-dominant integer-polynomial
  cone, in addition to the existing degree-at-least-two reduction.
- [PROVED ON PAPER] RH is equivalent to the weighted cosine--sine domination for every integer
  polynomial; the existing theta interface reduces the open family to degree at least two.  It is
  also equivalent to membership of `w_Xi/M` in the closed convex hull of the Poisson kernels
  `{P_r:0<=r<=2/41}`.
- [PROVED ON PAPER] Positive analytic density, equivalence to Haar, and an arbitrarily large
  ordinary Gram gap do not imply reflected positivity: `1-epsilon*cos(2*N*t)` has a negative
  reflected value on `z^N` for every `epsilon>0`.
- [OPEN] Prove the radial Poisson disintegration or the weighted cosine--sine inequality on the
  remaining degree-at-least-two tail-dominant coefficient cone from exact prime--Gamma source
  relations.  Do not reintroduce Xi divisor orientation, a positive real moment measure, or an
  RH-equivalent sign hypothesis.

## 2026-07-15 Euler-safe critical-logderivative Cauchy-loss insertion

- [PROVED ON PAPER] For every `a>1/2`, the completed logarithmic derivative `L(w)` has positive
  real part on `Re(w)>a` by horizontal Xi monotonicity inside absolute Euler convergence.  Hence
  `K_a(w,v)=(L(w)+conjugate(L(v)))/(w+conjugate(v)-2a)` is an unconditional positive
  Carathéodory kernel.
- [PROVED ON PAPER] The positive Laplace kernel `C_a(w,v)=2a/(w+conjugate(v))` gives the exact
  subtraction `K_0=K_a-K_a circle C_a`.  The critical kernel is positive exactly when the
  diagonal RKHS tensor map `e_w -> e_w tensor c_w` is contractive, and that condition is equivalent
  to RH by Nevanlinna--Pick extension from the Euler uniqueness half-plane.
- [PROVED ON PAPER] The domination is the explicit finite observability inequality `(19)` in
  `critical-logderivative-euler-safe-cauchy-loss-law.md`, with positive boundary density
  `h_a(t)=Re L(a+it)` given by an absolutely convergent von-Mangoldt plus Gamma formula.  For
  rational `a`, rational nodes and coefficients form a countable complete test family.
- [PROVED ON PAPER] A two-node determinant for the positive-real atom `1/(w-a)` is strictly
  negative, so neither Euler positivity nor `C_a(w,w)<1` implies the required matrix contraction.
- [OPEN] Prove the Cauchy--Laplace observability inequality from exact value relations of the one
  canonical density `h_a`; do not import continued-strip anti-Herglotzness, Xi zero locations,
  real-rootedness, an RH-equivalent measure, or the active theta-current/subpower route.

## 2026-07-15 outer-Euler modulus/first-prime antialignment insertion

- [PROVED ON PAPER] For `rho=beta+i gamma` in the open strip and any fixed `h>=1`, the points
  `h+conj(rho)` and `h+1-rho` share one horizontal line in `Re s>1`.  Their Xi logarithmic-modulus
  defect has sign `beta-1/2` by strict horizontal monotonicity.
- [PROVED ON PAPER] Demodulating the common first-prime seam gives the real scalar
  `2^(-beta)-2^(beta-1)`, whose sign is the opposite of `beta-1/2`.  Hence the product of the
  full completed defect and the least-prime defect is always nonpositive and vanishes exactly on
  the critical line.
- [PROVED ON PAPER] At `h=1`, the Xi values use the same two absolute-convergence exponents as the
  formal rational-Hurwitz two-fibre response.  The resulting full-source/least-atom relation is
  therefore a genuine same-node value splice, not continuation of an Euler series to a zero.
- [OPEN] Prove a nonnegative cross-scale alignment from a completed source determinant, Gram,
  reflection-positivity, or order constraint defined before divisor insertion.  Antialignment then
  forces equality, common-charge vanishing, zero orientation energy, and RH.  Functional-equation
  reflection changes both factors' signs and leaves their product unchanged, so reflection alone
  cannot close the interface.

## 2026-07-15 shifted sector-circle and residual-Sonin insertion

- [PROVED ON PAPER] For every `0<=s<=11`, the shifted density
  `m_s+2*sum_(n>=1)m_(s+n)cos(nt)` is strictly positive and real analytic.  Its relative deviation
  from its central mass is at most
  `224/(13*(168-(s+1)^2))`, which is strictly less than one on this range.
- [PROVED ON PAPER] If `P=X^v q` with `v<=5`, then the relevant moment shift is `2v`, and
  `224*sum_(n>=1)b_n^2 <= (1960-13*(2v+1)^2)b_0^2` forces `Q(P)>=0` unconditionally.
- [PROVED ON PAPER + LEAN CORE] Exact degree-thirteen sector algebra gives
  `Re(u^13)>|u|^13/8`.  Therefore the `s=12` density has relative deviation at most `32/39`, and
  `P=X^6q` is unconditionally nonnegative whenever `32*sum_(n>=1)b_n^2<=7b_0^2`.  The atomwise
  estimate, summed mass lower bound, endpoint radius, and geometric tail envelope are formalized in
  `PrimeArchShiftThirteenCircleCone.lean`.
- [PROVED ON PAPER] The one-sided coupled-Sonin variational comparison only needs to hold outside
  these valuation cones.  On the residual family its nonnegative aperture value excludes a
  negative prime--Gamma value; the automatic cones fill the omitted tests, and the existing
  integer Hankel capstone gives RH.
- [OPEN] Prove the quotient-free coupled-Sonin Rayleigh upper bound on the residual family only.
  The unresolved tests have either valuation at least seven or a post-valuation coefficient tail
  larger than the explicit sector threshold.

The unshifted circle construction is the positive descendant of the Schur norm-gap law: the
ordinary carrier no longer needs to be built.  Its shifted descendants now remove explicit
valuation cones as well.  The remaining source theorem must select the radial orientation only on
the complementary coefficient family.

## 2026-07-15 critical Möbius beta-wavelet insertion

- [PROVED ON PAPER] The sequential Báez--Duarte coefficient
  `c_k=sum_(j=0)^k(-1)^j binom(k,j)/zeta(2j+2)` is exactly the value of the critical
  logarithmic Möbius boundary vector
  `m_0(t)=sum_(n<=exp(t))mu(n)/n` against one explicit zero-mean beta wavelet
  `K_k(t)=exp(-t)(1-exp(-2t))^(k-1)(1-(2k+1)exp(-2t))`.
- [PROVED ON PAPER] The wavelet has one sign seam at `t=log(2k+1)/2`, and
  `||exp(-alpha t)K_k||_2^2` is an explicit three-term beta-function value asymptotic to
  `Gamma(alpha+1)(alpha^2+alpha+1)/(2(2k)^(alpha+1))`.
- [PROVED ON PAPER] Plancherel cancels the boundary factor `1/(it)` against the wavelet derivative
  and gives the exact safe-line value
  `c_k=(4pi)^(-1) integral_R B((1-it)/2,k+1)/zeta(1+it)dt`.  Moving the beta contour by
  `i alpha` is exactly the reciprocal-zeta continuation from `Re s=1` to `Re s=1-alpha`; the
  kernel has no zeros that can cancel a crossed nontrivial zeta pole.
- [PROVED ON PAPER + EXISTING FORMAL INTERFACE] At the fixed safe exponent `sigma=2`, the same
  coefficient is the coherent signed-source projection value
  `|c_k|=Z_*||Pi_*Y_k||`.  Elementary squarefree counting gives
  `||Y_k||~C k^(-1/4)`, so RH is equivalent to the normalized orientation law
  `||Pi_*Y_k||/||Y_k||=O_epsilon(k^(-1/2+epsilon))`.  The coisometry and projection already exist
  in `RHTower/InfiniteMobiusSignedChannel.lean`; the open input is only the arithmetic angle decay.
- [PROVED ON PAPER] Therefore `exp(alpha t)m_0 in L2` implies
  `c_k=O(k^(-(1+alpha)/2))`.  The unconditional `alpha=0` boundary theorem gives the classical
  exponent `1/2`; the missing half-unit of exponential transport is exactly the missing
  quarter-power needed for the RH-critical exponent `3/4`.
- [PROVED FROM LITERATURE + PAPER VALUE RELATION] Báez--Duarte's theorem converts the terminal
  condition `c_k=O_epsilon(k^(-3/4+epsilon))` into RH.  Hence the full weighted-domain tower may be
  replaced as a proof target by one signed beta-wavelet cancellation coefficient at each
  logarithmic scale.
- [OPEN] Prove these beta-wavelet values have critical decay directly from the Möbius/Euler source,
  without the full weighted `L2` tower, an RH-equivalent Mertens estimate, the explicit zero
  formula, or the active theta-current/rectangular-Weil subpower route.  See
  `../2-fully-proven/not_new_scientific_knowledge/baez-duarte-critical-mobius-beta-wavelet-law.md`.

## 2026-07-15 positive-paired real-boundary Loewner weld

- [PROVED ON PAPER + EXISTING FORMAL INTERFACES] On a zero-free real central source interval,
  write `T=continuedPrimeArchSourceRelativeTrace` and let `G_src` be the seam-log Markov germ.
  The formal normalized-trace identity and the seam-log weld give
  `G_src(x^2)=-T(x)/x`.  For distinct positive real nodes, the one-sided paired source kernel is
  exactly
  `K+(x,y)=4*x*y*(G_src(x^2)-G_src(y^2))/(x^2-y^2)`.
- [PROVED ON PAPER] After inserting the necessary confluent diagonal
  `Khat+(x,x)=2*(-T'(x)+T(x)/x)=4*x^2*G_src'(x^2)`, every finite boundary source matrix is the
  positive diagonal congruence `D*L_G*D`, `D=diag(2*x_i)`, of the seam-log Loewner matrix.  It has
  the same positivity, inertia, rank, and nullity.
- [PROVED ON PAPER] All-order positivity on any one central interval, even only on its rational
  nodes, is equivalent by Loewner--Pick continuation and the exact Xi weld to RH.  Thus the
  real-pole positive-paired source core **is** the seam-log Markov--Loewner core; no separate
  moment-identification or Cauchy-closure bridge remains on this boundary slice.
- [GUARDRAIL] The present Lean expression `ccmPositivePairedReducedKernel x x` at real `x` is not
  the confluent value: totalized division evaluates its `0/0` term as zero.  A formalization must
  define the derivative diagonal rather than rewriting the existing raw value.
- [OPEN] Prove the finite confluent boundary matrices positive from the explicit continued
  prime--Gamma formula without Xi divisor orientation, anti-Herglotzness, real-rootedness, an
  RH-equivalent positive measure, or the active theta-current/subpower route.  See
  `../2-fully-proven/not_new_scientific_knowledge/xi-positive-paired-real-loewner-seam-log-weld.md`.

## 2026-07-15 Euler-safe de-Poissonized Weil stationarity

- [PROVED ON PAPER] For every safe offset `a>1/2`, the Cauchy-loss deficit admits an exact
  tail-Laplace rewrite.  If `f(y)=sum_j c_j exp(-w_j y)` and
  `r_a=(2pi)^(-1) Fourier(h_a)`, then the deficit is the quadratic pairing of `f` with
  `exp(a|u|)r_a(u)`.
- [PROVED ON PAPER] The boundary densities form the Poisson orbit
  `r_b(u)=exp(-(b-a)|u|)r_a(u)`.  Hence the inverse factor in the loss cancels the safe offset:
  all safe-line observability forms are diagonal-congruent presentations of one stationary
  critical form `W_Xi`.
- [PROVED ON PAPER] At each prime-power frequency `u=+-log n`, the cancellation sends the safe
  coefficient `-Lambda(n)n^(-1/2-a)/2` exactly to the critical coefficient
  `-Lambda(n)n^(-1/2)/2`.  Together with the completion terms, the two-channel resolvent identity
  identifies `W_Xi` with the completed Weil distribution on the finite exponential test span.
- [POSITIVE CONSEQUENCE] Moving farther into absolute Euler convergence cannot create a
  perturbative proof: smoothing of the source and amplification by the Cauchy loss cancel exactly.
  The offset is therefore removed as a research parameter; a successful proof must factor the
  stationary critical orientation form itself.
- [GUARDRAIL] Since `h_a` has logarithmic growth, its Fourier transform is a tempered
  distribution.  The exponentially weighted product is defined here only through the convergent
  finite-exponential quadratic pairing; extension to a larger completed source space needs a
  separate continuity theorem.
- [OPEN] Prove the stationary completed form nonnegative by a source-specific orientation theorem,
  without importing divisor orientation, anti-Herglotzness, an RH-equivalent limiting measure, or
  the active theta-current/subpower route.  See
  `../2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`.

## 2026-07-15 absolute-Euler paired Cauchy completeness

- [PROVED ON PAPER] The canonical Xi--Hurwitz orientation vector belongs to the real Hilbert
  closure of Schwarz-paired Cauchy vectors indexed by any fixed open quadrant
  `Re(w)>a>1/2, Im(w)>0`.  Meromorphic Cauchy-transform uniqueness replaces the earlier local
  pole-collision construction and removes the continued-strip domain, the exterior threshold,
  and the low-frequency quartet-band hypothesis.
- [PROVED ON PAPER] The paired Weil energy is the real symmetric absolute-Euler kernel
  `2*Re((L(w)+conj(L(u)))/(w+conj(u))-(L(w)+L(u))/(w+u))`, where
  `L(w)=d/dw log xi(1/2+w)`.  Every value lies in `Re(1/2+w)>1` and therefore has the ordinary
  absolutely convergent prime--Gamma expansion.
- [PROVED ON PAPER] A Gaussian-rational grid in the quadrant and rational real coefficients are
  complete.  Hence RH is equivalent to nonnegativity only on countably many conjugation-odd
  doubled packets.  In the de-Poissonized representation these are precisely rational damped-sine
  packets, a strict subfamily of the arbitrary finite exponentials in the earlier Euler-safe
  Cauchy-loss criterion.
- [OPEN] Prove the paired absolute-Euler matrices, equivalently the restricted Cauchy--Laplace
  observability deficit on damped-sine packets, nonnegative without importing Xi divisor
  orientation, real-rootedness, continued anti-Herglotz positivity, an RH-equivalent limiting
  measure, or the active theta-current/subpower route.  See
  `../2-fully-proven/not_new_scientific_knowledge/xi-orientation-euler-safe-paired-cauchy-completeness.md`.

## 2026-07-15 paired Gauss-resolvent / prime-autocorrelation decomposition

- [PROVED ON PAPER] The paired-Cauchy transform of a real constant is exactly a zero-frequency
  sine mass, the transform of a real Cauchy atom is an explicit boundary square plus a resolvent
  square, and the transform of one negative exponential is exactly a negative half-line lag
  autocorrelation.
- [PROVED ON PAPER] Applying those three identities to the ordinary absolute-Euler formula for
  `L(w)=d/dw log xi(1/2+w)` expands every paired rational packet into two elementary boundary
  resolvents, one compensated Gauss/digamma resolvent-square series, and the explicit
  von-Mangoldt autocorrelations at lags `log n`.  No Xi zero or continued critical-strip value
  enters the expansion.
- [PROVED ON PAPER] Herglotz residue orientation and paired-Cauchy orientation are not the same
  datum.  Reversing a digamma pole adds a positive paired square, while changing the real Gauss
  normalization changes the form by an independent zero-frequency mass.  The finite pole-flip
  palette and the finite-support signed Gauss completion have the same imaginary part but differ
  by an exact positive contact term on every nonzero damped-sine packet.
- [POSITIVE CONSEQUENCE] The new infinite signed-digamma Herglotz theorem cannot by itself supply
  the paired RH sign; its exact usable content is the polar block.  A successful source theorem
  must retain the canonical Gauss contact normalization and prove that the resulting
  archimedean resolvent budget dominates the prime-log autocorrelation budget.
- [OPEN] Prove that explicit domination on the countable rational damped-sine core.  By the
  preceding completeness theorem it implies RH, and it is distinct from the active
  theta-current/subpower route.  See
  `../2-fully-proven/not_new_scientific_knowledge/absolute-euler-paired-gauss-resolvent-autocorrelation-law.md`.

## 2026-07-15 unit Euler-pole affine section and translated value-fibre Bezoutian

- [PROVED ON PAPER] Let `A(s)=s*(s-1)/2*Gamma_R(s)` and, off `s=1`,
  `Z_c(s)=(xi(s)-c)/A(s)`.  The exact punctured source value is
  `lim_(s->1)(s-1)Z_c(s)=1-2c`.  Therefore the canonical unit Euler residue is equivalent to
  `c=0`: it supplies the affine-origin marking erased by every positive-jet horizon field.
- [PROVED ON PAPER] For real `c`, put `X_c(w)=xi(1/2+w)-c`.  The Hermitian Bezoutian
  `B_c(w,v)=(X_c'(w)conj(X_c(v))+X_c(w)conj(X_c'(v)))/(w+conj(v))` is positive semidefinite on
  the right half-plane if and only if every solution of `xi(s)=c` lies on the critical line.
  Genus-zero factorization of the even entire function proves the forward Gram expansion; a
  one-sided approach to any right-half-plane zero makes a diagonal kernel value negative and
  proves the converse.
- [POSITIVE DISCHARGE] The positive-jet horizon no-go is now repaired by a source-defined marked
  section rather than an added arbitrary constant: unit Euler residue selects the zero fibre, and
  translated Bezoutian positivity orients that fibre.
- [OPEN] Prove `B_0` positive from the explicit prime--Gamma/Euler source without Xi divisor
  orientation, real-rootedness, anti-Herglotzness, an RH-equivalent positive measure, or the active
  theta-current/subpower route.  See
  `../2-fully-proven/not_new_scientific_knowledge/xi-unit-euler-pole-affine-section-translated-bezoutian.md`.

## 2026-07-15 BV prime-window Laurent orientation polarization

- [PROVED ON PAPER + FORMAL ANALYTIC PROVIDERS] The moving-prime Dirichlet series attached to a
  compact BV window has the canonical continuation
  `D_W(s)=-M_W(s) zeta'(s-1/2)/zeta(s-1/2)+E_W(s)`, with `E_W` holomorphic on
  `Re(s)>1/2`.  The BV quadrature, holomorphy, Dirichlet identity, polar-renormalized continuation,
  exact residue, Mellin-censorship pole order, and fixed-window RH holomorphy criterion are now
  formalized and wired through `RHTower.lean`.
- [PROVED ON PAPER + FORMAL RESIDUE PROVIDER] At a zero `rho` of multiplicity `m_rho`, the
  canonical polar source has residue `2m_rho M_W(rho+1/2)`.  For reciprocal dilations `W(rx)` and
  `W(x/r)`, the difference of squared residue norms is exactly
  `4m_rho^2 |M_W(rho+1/2)|^2 * 2 sinh(2 log(r)(Re(rho)-1/2))`.
- [PROVED ON PAPER] This normalized residue difference is precisely the Burnol co-Poisson Berezin
  aperture-orientation value.  The reciprocal-conjugate window `W#(x)=conj(W(1/x))` swaps the two
  Laurent channels under functional-equation reflection, so the common horizontal charge is an
  explicit reflection-odd source norm balance.
- [PROVED ON PAPER] Indicators of rational intervals form a fixed countable compact-BV family that
  separates every complex Mellin point and is closed under rational reciprocal dilation and
  reciprocal reflection.  For the right-half RH implication, the single fixed sharp window
  `1_[1,2]` already detects every off-critical zero.
- [OPEN] Prove the forward Laurent residue is contractive relative to the inverse residue on the
  right-half nontrivial pole spectrum directly from the moving-prime source.  This would force the
  common charge to vanish and imply RH.  The value relation is closed; the source contraction is
  not.  See
  `../2-fully-proven/not_new_scientific_knowledge/bv-prime-window-laurent-orientation-polarization.md`.

## 2026-07-15 BV prime-window coefficient decimation and scale-zero boundary contraction

- [PROVED ON PAPER + FORMAL CONTINUATION PROVIDERS] For the integer-dilation ladder
  `W_j(x)=W(r^j*x)` and its canonical polar coefficients `p_j`, square-index decimation is exact:
  `p_j(N)=p_(j-2)(r^2*N)`.  This is termwise finite prime-source algebra, independent of every
  zeta zero.
- [PROVED ON PAPER] On each uncensored zero fibre, the same decimation has Laurent character
  `R_j(rho)/R_(j-2)(rho)=r^(2rho-1)`.  The complementary off-`r^2` coefficient layer has the
  universal residue fraction `1-r^(-2)`, independent of height, multiplicity, and horizontal
  location.
- [PROVED ON PAPER] Ordinary square-summable Dirichlet coefficient space cannot carry any source
  with an uncensored zeta pole: its Dirichlet series would be holomorphic on `Re(s)>1/2`.
  Polynomial coefficient weights yield only the shifted bound `Re(rho)<=1/2+alpha`.  Therefore the
  needed critical completion must be a singular scale-zero graph retaining a principal-part
  coordinate.
- [PROVED CONDITIONAL ENDPOINT] On the source orbit `P_W=span{p_j}`, every right zero defines a
  Laurent functional satisfying `ell_rho D=r^(2rho-1)ell_rho`.  A source-defined positive
  completion which makes `D` contractive and all these functionals continuous would make their
  Riesz vectors eigenvectors of `D^*`; the unit-disk eigenvalue bound forces the common horizontal
  charge to vanish and proves RH.
- [OPEN] Construct the canonical scale-zero Gram renormalization.  Finite cutoffs already satisfy
  an exact positive Stein identity: the difference between the full Gram at cutoff `r^2*X` and the
  shifted Gram at cutoff `X` is the Gram over indices not divisible by `r^2`.  The missing theorem
  is a source-pure boundary limit preserving that positivity while making Laurent evaluation
  continuous.  This is distinct from the active subpower coefficient route.  See
  `../2-fully-proven/not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`
  and `bv-prime-window-decimation-boundary-contraction-rh.md`.

## 2026-07-15 holomorphic Schwarz polarization for OPUC terminals

- [FORMALIZED POSITIVE NO-GO] A nonconstant entire coefficient family cannot have its pointwise
  conjugate holomorphic in the same complex parameter.  Consequently an analytic spectral OPUC
  family cannot form its reversed polynomial by same-variable coefficient conjugation without
  collapsing every coefficient to a constant.
- [FORMALIZED POSITIVE SUCCESSOR] The independent-variable Schwarz partner
  `fSharp(w)=conj(f(conj(w)))` is entire whenever `f` is, and satisfies
  `fSharp(conj(z))=conj(f(z))`.  Thus the admissible analytic terminal is bivariate and is restricted
  to `w=conj(z)` only after its holomorphic source identity has been established.
- [ROUTE FILTER] Finite singular Pick interpolation cannot supply the Xi family: the stage-2
  finite-selector law would make the selected Schur function rational inner, whereas the oriented
  Xi carrier is nonrational and has strictly positive finite Pick defect.  A polarized OPUC object
  may therefore serve as a zero detector, not as a finite-data reconstruction of Xi.
- [OPEN] Construct a source-defined polarized polynomial or colligation from the absolute-Euler
  paired-Cauchy or translated-Bezoutian data, and prove a terminal Xi value identity or zero
  implication before invoking paraorthogonal interior-root exclusion.  See
  `../3-formalized/not_new_scientific_knowledge/holomorphic-schwarz-polarization-opuc-interface.md`.

## 2026-07-15 completed translation-resolvent functional calculus

- [PROVED ON PAPER] On the finite real damped-sine core, every Gauss boundary/resolvent pair
  satisfies the exact integration-by-parts identity
  `Z_c^2+2c||R_c y||^2=2<y,R_c y>`.  The separate scalar squares in the paired source expansion
  are therefore one half-line translation-resolvent value.
- [PROVED ON PAPER] The entire absolute-Euler paired kernel is
  `8<y,(G_Gamma-G_Euler)y>`, where `G_Gamma` is the canonically compensated digamma resolvent
  series and `G_Euler=sum Lambda(m)m^(-1/2)S_(log m)` is the critical prime-power translation
  form.  Compensation is kept termwise, so no divergent identity series is separated.
- [PROVED ON PAPER] For each prime,
  `sum_(k>=1) log(p)p^(-k/2)S_(k log p)=log(p)T_p(I-T_p)^(-1)` with
  `T_p=p^(-1/2)S_(log p)`.  Its Cayley transform is accretive.  Hence the remaining global
  theorem is exactly Gamma contact/resolvent domination of the positive Cayley sectors of the
  Euler-prime family, not an unspecified cancellation among scalar terms.
- [OPEN] Prove `<y,(G_Gamma-G_Euler)y> >= 0` on the countable rational damped-sine core.  Existing
  absolute-Euler paired completeness then gives RH.  Burnol's local conductor positivity covers
  the finite-place cuspidal sector, not this unramified spherical Euler channel; Connes--Consani's
  archimedean Sonin positivity supplies only the archimedean side.  See
  `../2-fully-proven/not_new_scientific_knowledge/absolute-euler-paired-translation-resolvent-functional-calculus.md`.

## 2026-07-15 cumulative critical-error current reduction

- [PROVED ON PAPER + FORMAL FINITE-APERTURE PROVIDER] The formal Stieltjes integration-by-parts
  theorem for `criticalMellinCompletedError` extends from compact aperture vectors to every finite
  damped-sine packet.  Strict damping beyond one half makes the boundary term vanish and gives an
  integrable majorant using only an elementary Chebyshev bound.
- [PROVED ON PAPER] The two polar resolvents and every critical prime-power lag satisfy
  `integral 2cosh(h/2)C_y(h)-sum Lambda(m)m^(-1/2)C_y(log m)
   =-integral E_crit(h)C_y'(h)`.  Thus all separate prime lags collapse to the single cumulative
  arithmetic source `E_crit=criticalMellinCompletedError`.
- [PROVED ON PAPER] The complete paired source value is
  `8*(<y,D_Gauss y>-integral E_crit(h)C_y'(h)dh)`.  The remaining theorem is therefore one exact
  current comparison, not an infinite family of unrelated prime-autocorrelation estimates.
- [OPEN] Prove the compensated digamma form dominates this cumulative critical-error current on
  the rational damped-sine core.  This implies RH by absolute-Euler paired completeness and is
  separate from the active Taylor/theta anisotropic-current route.  See
  `../2-fully-proven/not_new_scientific_knowledge/absolute-euler-paired-cumulative-critical-error-current-law.md`.

## 2026-07-15 normalized screw-current identification

- [PROVED ON PAPER] Every paired damped-sine packet satisfies `y(0)=0` and
  `C_y'(0)=0`.  The logarithmic contact singularity of the completed archimedean kernel is
  therefore classically integrable on this core; no independent finite-part boundary hypothesis
  is needed.
- [PROVED ON PAPER] The tail primitive of the compensated Gamma kernel is
  `A_infinity(h)=atanh(exp(-h/2))+atan(exp(-h/2))`.  With
  `kappa_infinity=(log(8*pi)+EulerGamma)/2+pi/4`, the entire paired source is the single current
  `Q_pair(y)=-8*integral J_Xi_screw(h)C_y'(h)dh`, where
  `J_Xi_screw=E_crit+A_infinity-kappa_infinity`.
- [PROVED ON PAPER + LITERATURE IDENTIFICATION] Distributionally,
  `J_Xi_screw'=K_reg(h)dh-sum Lambda(m)m^(-1/2)delta_(log m)`, with
  `K_reg(h)=exp(h/2)-exp(-5h/2)/(1-exp(-2h))`.  This is exactly the full Suzuki--Weil screw
  kernel.  The cumulative critical-error route and the screw route are therefore one source form,
  not two independent RH attacks.
- [PROVED ON PAPER + FORMAL VALUE PROVIDER] Multiplication by `1-exp(-2h)` removes the contact
  singularity and the infinite Gamma denominator.  The resulting distribution has regular part
  `exp(h/2)-exp(-3h/2)-exp(-5h/2)` and prime atoms weighted by
  `Lambda(m)m^(-1/2)(1-m^(-2))`.  Its Laplace transform is exactly
  `logDeriv(xi)(s)-logDeriv(xi)(s+2)`, with the rational/filtered-prime decomposition already
  formalized in `XiShiftPrimeExposure.lean`.
- [PROVED POSITIVE NECESSITY] The bare filtered distribution is not positive even on the allowed
  one-packet core.  For `y_a(x)=exp(-a*x)sin(a*x)`, its rescaled quadratic tends to `-1/4` as
  `a->infinity`; the prime atoms are exponentially invisible at that contact scale.  Therefore
  a direct positivity-compatible even-shift inversion must add a compensating channel.  In the
  present coordinates the canonical compensator is the contact/boundary normalization.  The
  scalar positive real-axis shift defect in Lean is not a matrix-positivity substitute.
- [POSITIVE INTERFACE DISCHARGE] The separate compensated-Gamma comparison, contact
  renormalization, and current-to-screw identification are closed.  The sole live assertion is
  normalized screw-current dissipation on the explicit rational damped-sine boundary-zero core.
  A new possible subproblem is a contact-augmented positivity-compatible inversion of the regular
  even-shift filter.  Generic screw positivity would be circular, so a proof must use an additional
  value relation or reflection specific to `J_Xi_screw` and that finite exponential core.  See
  `../2-fully-proven/not_new_scientific_knowledge/absolute-euler-paired-normalized-screw-current-identification.md`.

## 2026-07-15 prime-seam damping aperture

- [PROVED ON PAPER] For the reflected amplitude seam and its logarithmic Xi seam, the exact
  summability threshold under weight `p^(-theta)` is
  `theta>|2*Re(rho)-1|`, with the critical-line seam identically zero.  Equivalently, the infimal
  damping exponent is exactly the horizontal FE--Schwarz charge `|2*Re(rho)-1|`.
- [POSITIVE CONSEQUENCE] If the weighted logarithmic seam is summable for every `theta>0` on every
  Xi divisor fibre, then every horizontal charge vanishes, the Xi--Hurwitz orientation energy is
  zero, and RH follows.  This requires neither pairwise prime coherence nor an additional
  common-charge normalization.
- [ROUTE FILTER] The canonical inverse-prime/Gamma damping has `theta=1` and is automatically
  summable throughout `0<Re(rho)<1`.  It repairs the Hilbert domain but carries no critical-line
  orientation.  Any fixed positive power loss proves at most a horizontal band; a viable source
  theorem must remove the loss, make it cofinal as `theta->0+`, or cancel it in a relative trace.
- [OPEN SOURCE INTERFACE] Produce the all-positive-loss estimates from an Euler--Gamma value
  relation without assuming Xi zero locations.  See
  `../2-fully-proven/not_new_scientific_knowledge/prime-seam-damping-aperture-law.md`.

## 2026-07-15 Gamma--Meixner root scale and prime-Laplace value frame

- [PROVED ON PAPER + PRIMARY LITERATURE IDENTITY] Ramanujan's Gamma Fourier transform places the
  actual archimedean cyclic measure in the continuous convolution semigroup
  `phi_theta(t)=cosh(t)^(-theta/2)`.  Its pointed prime diagonal is
  `w_theta(p)=cosh(2log p)^(-theta/2)`, with
  `p^(-theta)<=w_theta(p)<=2^(theta/2)p^(-theta)`.
- [PROVED ON PAPER] The Gamma--Meixner root-domain threshold of an individual Xi seam is exactly
  `theta>|2Re(rho)-1|`, unless the seam is identically zero.  Hence the countable root family
  `theta=1/m` detects the critical line and supplies a source-canonical replacement for arbitrary
  small prime losses.
- [PROVED ON PAPER] The prime-Laplace vectors `e_x(p)=p^(-x)`, `x>1`, lie in every positive root
  domain and have dense span in each.  Pairing the seam with this common frame gives the exact
  value relation
  `M_theta(x+rho)-M_theta(x+1-conj(rho))`, where
  `M_theta=-P_theta'` and `P_theta(s)=sum_p w_theta(p)p^(-s)`.
- [FINITE VALUE INTERFACE] Root-domain membership is equivalent to one Riesz/Gram bound for all
  finite combinations of those explicit reflected values; the countable nodes `x_n=1+1/n`
  suffice.  The ordinary regular-Cauchy source span cannot be interpolated into any root time
  `0<theta<1`: every nonzero finite Cauchy packet has only inverse-logarithmic decay and its root
  norm diverges.  The positive successor is the common exponential value frame or a genuinely
  relative deconvolution.
- [OPEN] Derive the finite value Gram bounds from a completed Euler--Gamma identity or relative
  trace.  See
  `../2-fully-proven/not_new_scientific_knowledge/archimedean-meixner-root-seam-scale.md` and
  `../2-fully-proven/not_new_scientific_knowledge/meixner-root-prime-laplace-value-frame.md`.

## 2026-07-15 one-scalar Gamma-shape Landau continuation

- [PROVED ON PAPER] Weight every Xi divisor fibre by the formalized positive multiplicity divided
  by `|rho-1/2|^2`, and put
  `A_p=sum_rho b(rho)|C_p(rho)|^2`.  The coefficients are finite, nonnegative, and bounded by a
  constant times `(log p)^2`.
- [PROVED ON PAPER] The single general Dirichlet series
  `G_Xi(z)=sum_p A_p exp(-z*log(cosh(2log p))/2)` is holomorphic for `Re z>1`.  Any one off-line
  zero of charge `delta>0` forces its abscissa of convergence to be at least `delta`.
- [TOP-DOWN LANDAU CHAIN] Positive-coefficient Landau theory makes every positive abscissa a real
  singularity.  Therefore RH is equivalent to holomorphic continuation of this one safe
  Gamma-shape trace from `Re z>1` to `Re z>0`.  Meromorphic continuation without a positive-real
  pole-exclusion theorem is insufficient.
- [OPEN SOURCE INTERFACE] Identify the safe trace with a completed prime--Gamma/theta or relative-
  resolvent expression holomorphic in Gamma shape on `Re z>0`.  This replaces separate
  continuation hypotheses on every zero fibre by one scalar value relation.  See
  `../2-fully-proven/not_new_scientific_knowledge/xi-global-meixner-shape-landau-rh.md`.

## 2026-07-15 reciprocal-translation prime-seam norm law

- [PROVED ON PAPER] For the centered reciprocal Cauchy vector
  `v_0(q)=xiSpectralPoint(q)^(-1)`, spectral translation gives
  `v_L(q)=exp(-i*L*xiSpectralPoint(q))*v_0(q)` and the entire norm curve
  `N(L)=sum_q exp(2L*Im(xiSpectralPoint(q)))/|xiSpectralPoint(q)|^2`.
  Functional-equation reflection makes `N` even and gives
  `N(L)-N(0)=sum_q (cosh(2L*Im(alpha_q))-1)/|alpha_q|^2>=0`.
- [EXACT SOURCE VALUE RELATION] The Weil quadratic value of every `v_L` is independent of `L` and
  equals `primeArchCentralCurvature`.  Hence
  `N(L)-primeArchCentralCurvature` is one half of the negative-sector distance
  `||v_L-Jv_L||^2`, and it splits into the translation-growth defect plus one half of the already
  formalized global reflection-defect energy.
- [EXACT PRIME COLLISION] For every rational prime,
  `A_p=2(log p)^2/p*(N(log p)-N(0))`.  Thus the Landau coefficient is not a separate divisor
  statistic: it is the prime sample of one reciprocal-Cauchy norm orbit.
- [STRICTLY SMALLER TOP-DOWN INPUT] Contractivity `N(log 2)<=N(0)` at the single prime `2`, or the
  cofinal estimate `log N(L)=o(L)`, forces every centered spectral point real and proves RH.  This
  requires neither a conservative metric on every theta eigenfunction nor zero simplicity.
- [OPEN SOURCE INTERFACE] Prove the anchored normalized dyadic-residue contraction described
  below, or derive subexponential orbit growth directly from the theta/Mellin source.  Mellin
  unitarity before divisor evaluation does not by itself supply this norm transfer.  See
  `../2-fully-proven/not_new_scientific_knowledge/xi-reciprocal-translation-prime-seam-norm-law.md`.
- [VALUE-RELATION DISCHARGE] The algebraic part of that source-to-divisor map is already the
  formalized dyadic sharp-window tomography.  If
  `B_L(z)=sharpPrimeWindowMellin(L,1+i*z)`, then
  `v_0-v_L=i*B_L(alpha)` on every divisor copy, and the trailing coefficient of the dyadic
  continued source at `rho+1/2`, divided by twice the analytic multiplicity, is exactly
  `B_(log 2)(alpha)`.  Hence the unspecified intertwiner is replaced by the concrete fixed-source
  inequality `||b||^2+2 Im<v_0,b><=0` for the normalized residue vector.  Functional-equation
  reflection supplies every left pole, while critical-line copies contribute zero to this anchored
  current.  The coordinate identity is closed; bounded quadratic transport of the reflected
  right-residue family is the only remaining input in this splice.  This is distinct from the
  active anisotropic rectangular-mesh/subpower route.

## 2026-07-15 theta reflected-budget likelihood splice

- [LEAN-VERIFIED] The Gibbs Ward equation gives the exact Laplace shift
  `2*pi*n^2*B_n(z+2)=b_n(0)+(z+5/2)B_n(z)` and the source transform
  `A_n(z)=2*pi*(b_n(0)+(z-1/2)B_n(z))`.  At the two half-density points these collapse to explicit
  endpoint values.
- [LEAN-VERIFIED] Reflection and `XiC(I/2)=1/2` give the exact first/higher exponential budgets
  `sum a_j/(4^j*(2j)!)=(4*pi-1)exp(-pi)` and
  `H=sum r_j/(4^j*(2j)!)=1/2-(4*pi-1)exp(-pi)`.
- [LEAN-VERIFIED NO-STRONGER THEOREM SURFACE] Retaining the Gaussian cusp damping proves
  `H<=q*a_0<=q*(a_0+a_1/8)` for `q=8/2997`.  Hence the completed theta low block follows from
  `14*(a_0+a_1/8+H)*a_2^2<=9*(a_0+a_1/8)*a_1*a_3` and
  `16*(a_0+H)*a_2<=45*a_1^2`; both left multipliers are no larger than the old single-loss
  multipliers without any evaluated theta value.
- [OPEN] Prove those two finite first-atom inequalities from the exact Ward--Laplace Taylor
  constraints, then close the independent degree-at-least-two polynomial cone or the leading
  determinant tail from size three.  See
  `../3-formalized/not_new_scientific_knowledge/theta-cusp-half-density-ward-laplace-budget-transfer.md`
  and
  `../3-formalized/not_new_scientific_knowledge/theta-cusp-half-density-damped-tail-domination.md`.

## 2026-07-15 theta antisymmetric-reflection Turan splice

- [LEAN-VERIFIED] The reflected half-density difference gives the exact odd first-atom budget
  `sum M_(2*j+1)/(4^j*(2*j+1)!)=exp(-pi)`, complementary to the existing even budget.
- [EXACT HYPOTHESIS COMPRESSION] The upper low-degree gate has no essential tail or zeroth-moment
  input: it follows from
  `8*a_2<=45*a_1^2+2*a_1*a_2+a_2^2/24`.
- [COMMON SOURCE CONSTRAINT] The two low-degree gates are exactly a lower bound on the first Turan
  defect and an upper bound on the second.  The half-line slope-curvature identity splits both into
  a favorable explicit boundary determinant plus one regular functional of
  `E_reg=d/dx((V'(x)-V'(0))/x)`; the first-atom potential satisfies `V''>=19`.  This regular
  curvature changes sign exactly once, and each remainder is its pairing with a positive strictly
  unimodal crossing window having an exact moment-ratio peak.
- [OPEN] Prove the paired one-seam window inequalities for orders one and two.  This closes the
  theta degree-one block, after which the independent degree-at-least-two cone or leading
  determinant tail from size three remains.  See
  `../2-fully-proven/not_new_scientific_knowledge/theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md`
  and `theta-cusp-one-seam-turan-window-balance.md`.

## 2026-07-15 continuous residual half-density chart

- [PROVED ON PAPER] The first theta atom has elementary tilted survival transforms at every cutoff:
  `T_+(a)=2*pi*exp(3*a)*exp(-pi*exp(2*a))` and
  `T_-(a)=(2*pi*exp(2*a)-1)*exp(-pi*exp(2*a))`.
- [VALUE-RELATION STRENGTHENING] Every residual tail therefore has exact even and odd exponential
  moment budgets.  The ordinary survival function lies in an explicit corridor whose exact relative
  width is `1/(2*pi*exp(2*a)-1)`.
- [SEAM DISCHARGE] The unique regular-curvature seam satisfies `0<c<log 2`; hence every nontrivial
  arithmetic translate lies on its positive side.  At the seam, both crossing windows use only total
  moments and residual moments governed by the continuous chart.  The curvature floor further gives
  `tau_1<=tau_2<2/3<log 2`, so the seam and both live peaks lie in the first residual cell.
- [OPEN] Convert these residual budgets into the paired order-one lower/order-two upper window
  balances.  See
  `../2-fully-proven/not_new_scientific_knowledge/theta-cusp-continuous-half-density-residual-tail-chart.md`
  and `theta-cusp-one-seam-turan-window-balance.md`.
