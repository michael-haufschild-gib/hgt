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
   unweighted one-particle Euler sections at the sub-root reciprocal-mass scale.

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
| Hurwitz FE--Schwarz rank-two circuit | for every open-strip `rho`, without assuming Xi zerohood, `H_(1-rho)` and `H_(conj rho)` are differentially dependent exactly when `Re rho=1/2`; the pair circuit is also exactly `C_2(rho)=0`, and globally exactly zero scalar orientation energy; separately, the three-node anchor locus at an actual Xi zero is `{rho,1-rho}`, so the fixed half-anchor is always independent | prove nonnegativity of the Weil form on the algebraic regular-Cauchy prime--Gamma source span; closure and pair/charge/energy identification are already discharged | source-core positivity gives zero orientation energy, hence all first-prime charges vanish and every FE--Schwarz pair is dependent; open-strip rigidity then gives `1-rho=conj rho` and RH | **Positive route collapse: differential circuit, first-prime seam, heat-echo first atom, and scalar orientation energy are one defect; half-anchor/Arakelov route retired, leaving only the existing source-core sign** |
| Height-adaptive scalar DISC census | the unconditional Jensen/growth theorem gives one fixed envelope `N_Xi(r) <= C(1+r)log(2+r)`; the total right-half upper-box order below integer height `n` is bounded by the global disc mass in `B(2,n+2)` | for each integer `n >= 1`, prove one scalar boundary relation `discCensusH k_n n = 0` with `2^k_n` above that envelope | the box mass is divisible by `2^k_n` and strictly smaller than it, hence zero; integer-height exhaustion gives RH | **Weakest countable finite-depth chain formalized**; no local order divisibility, Kummer root, global branch, or inter-height compatibility is required; regional roots remain an overpowered sufficient provider, while the open core is one completed-source finite-ring census value per height |
| Height-adaptive cancelled-source socle--Weyl contradiction | the cancelled source pair `(A,C)` defines a finite zero algebra and multiplication by `C`; its image has one socle dimension per distinct right-half zero and is bounded by the unconditional Jensen envelope | construct, before enumerating zeros, one internal dyadic Weyl pair on that undoubled image at a depth above the envelope; finite-prime operators on the full real-Xi sampling quotient are formally excluded, so the producer must be integral boundary-completed or genuinely all-prime/nonlocal | if RH is false the socle dimension is positive, while the determinant relation forces divisibility by a larger power of two and hence dimension zero; bounded exhaustion then gives RH | **Nontrivial contradiction chain with both ends closed and one source-realization core**; the direct finite-prime shortcut is dead, but its positive replacement is exact: source the nonzero boundary holonomy and annihilate the top-jet Weyl anomaly without importing the socle dimension |
| Four-unit pole-to-divisor trace-slope contradiction | the finite-prime completion has the unique upper anti-causal Euler-pole profile `2 exp(-t/2)` of squared `L²` energy `4`; a nonempty right-half Xi divisor has a positive Cauchy-Gram residue profile whose energy is strictly greater than `4` per integer divisor unit | construct a pointed, source-defined, nonexpansive all-prime-plus-Gamma continuation from the pole profile to the Xi divisor profile; weak graph-core compactness can transfer a uniform four-unit estimate but cannot create it | false RH gives Xi residue energy `> 4`, while source nonexpansiveness gives energy `<= 4`, a contradiction and hence RH | **Strongest analytic contradiction chain in the paper-proven layer**; both numerical endpoints and the compactness transfer are proved, but the one source transport theorem remains open; canonical real-spectrum stages, theta-cusp screens, and signed-Moebius tails have been tested and merely restate the same horizontal control |
| All-prime Sonin value loci and cofinal section | the residual energy `T_a=K_a^*K_a` is positive trace class and its Gram tower collapses exactly to `S_r(a)=Tr(T_a^(r+1))` | weakest: put each fixed prime--Gamma integer-polynomial value in the closure of the corresponding scalar Sonin Gram range; stronger source condition: put every finite prime--Gamma moment block in the corresponding positive Sonin moment-curve closure | finite-block closure is now proved equivalent to one positive aperture sequence converging in every moment coordinate, and either source-value condition transfers positivity to the countable prime--Gamma trace-Hankel cone and RH | **Independent live value-relation chain**; coherence is discharged by diagonal closure selection, but the analytic source-to-source finite-block closure remains open |
| Theta low-degree discharge × prime--Gamma Hankel tail | the two explicit theta-cusp moment-ratio inequalities force every constant and linear real-polynomial prime--Gamma Hankel test to be nonnegative; one strict ratio makes the first nonconstant leading determinant positive | prove the two theta ratios and either the degree-at-least-two integer-polynomial cone or only the scalar leading-determinant tail from size three | the degree dichotomy reconstructs the complete countable source cone; more sharply, the strict low block plus one determinant per size reconstructs the leading-determinant criterion, and either chain implies RH | **Top-down interface reduction formalized**; the polynomial tail starts at degree two and the scalar tail starts at matrix size three, while the active theta atom card owns the separate low-degree producer |
| Hurwitz monodromy/Cauchy source | the Xi-indexed Hurwitz family is differentially free; its character phase is the exact transverse coordinate; the canonical orientation vector is reconstructed by separated continued-Cauchy packets with exact prime--Gamma energies | prove nonnegativity for the explicit separated source packets, or on their algebraic span, without importing a zero-location sign | eventual nonnegativity of one reconstructed source sequence is equivalent to RH; the same phase is the sharp rectangular growth exponent | **Live source-sign chain**; closure, multiplicity, and source-domain interfaces are discharged |
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
- [PROVED] Relative to any actual critical-line Xi anchor, the reciprocal-square weighted sum of squared imaginary anchored two-node Hurwitz Vandermonde determinants is exactly the canonical orientation energy; the HGT separator, one-vector Weil obstruction, and scalar energy are one value relation.
- [PROVED] The full Hurwitz orientation vector belongs to the Hilbert closure of pairwise-conjugate-separated continued Cauchy packets in the analytically continued prime--Gamma source domain; their exact source energies converge to the negative orientation energy.
- [PROVED] The common first-prime Hurwitz-anchor/all-prime seam charge is reflection-odd, and
  vanishing of every Xi-indexed common seam is exactly `E_Xi=0`; it introduces no gap beyond the
  regular-Cauchy source-core sign.
- [PROVED] The canonical seam charge tends to zero along cofinal primes, so all-prime coherence
  forces the common charge to vanish and then forces RH.  Uniform boundedness of its finite
  reciprocal-prime pair energies is now formally equivalent to RH, and false RH produces one
  actual Xi fibre with arbitrarily large finite pair energy.  This removes the extra normalization
  hypothesis from the paper-proven two-particle Sonin route; only its canonical source-side
  uniform Calkin bound and the actual tensor estimate remain open.
- [PROVED] The continued prime--Gamma trace and its RH-bearing Cauchy kernel factor globally through the canonical continued critical-Mellin defect; the defect agrees with the convergent polar--prime Laplace channel on its right-half-plane domain.
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
