# Route T: saddle-polarity facts

- At every literal timelike two-rapidity stationary pair, the first directional curvature is
  positive and the second is negative; their product is strictly negative.  Since the phase is
  separated by rapidity, its stationary cell has zero signature.  Therefore stationary geometry
  cannot supply a one-sided Maslov sign for the Route-T covariance.  The literal damping amplitude
  is real with strictly positive real part everywhere, so it supplies no compensating local phase.
- The Deninger unequal-half cross current is exactly twice the original finite prime-atom cone.
  Its static `h ↦ -h` symmetrization is representation-neutral and cannot create order support or
  signed cancellation.
- Every complex multiplier nonzero on a fixed rapidity-diagonal germ retains an exact anti-ordered
  timelike stationary pair whenever `2k/u` fits in that germ.  Hence no regular fixed diagonal
  cutoff can produce the needed order support; a survivor must vanish through every diagonal germ,
  be discontinuous, or use nonlocal frequency/source data.
- Phase compression at `h,k = o(sqrt(u))` together with saddle polarity forces any surviving
  producer to be a source-faithful, cofinal arithmetic relation between nonlocal prime-frequency
  cells.  No such relation was located by the Route-T deep searches; replacing von Mangoldt
  weights by quadratic-character weights is not an admissible source identity.
- The already-proved adjacent-prime and finite-dilation cancellations are bounded coboundaries.
  Modulo those directions and critical-weight `ℓ¹` errors, their masked source still has exactly
  the scalar valuation-one quotient, whose line bound is RH-equivalent.  They cannot close Route
  T by themselves.
- Finite Abel summation gives an exact remaining source current:
  `Σ_n M_{n+1}(F_n-F_{n+1})`, where `M` is cumulative critical prime mass and `F` the actual
  mass Fourier profile.  Its terminal flux vanishes, but its uniform line bound is exactly RH;
  no absolute uniform summability is available.  This is the sharp source-level survivor after
  all presently known local prime differences are removed.
- Lean status: `XiMassTwoRapiditySaddlePolarity.lean` and
  `XiMassDiagonalGermStationaryNoGo.lean` are compiled and imported by the RHTower umbrella.  Their
  public theorems have only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`
  dependencies.
- Current C5b audit: under critical prime-gap energy, canonical mesh continuation and static
  holonomy are pole-free; the paired residual Hardy continuation is the sole possible carrier of
  an off-line Wold charge.  Any independent strict-subhalf terminal limit, raw-edge convergence,
  or absolute positive-ray Borel interchange is RH-equivalent or incompatible with critical mesh
  energy.  A valid producer must control a terminal-coupled non-uniform source limit.
- Every finite source/order Borel cutoff is pole-free at every continuation point.  This is a
  generic finite-dimensional fact, not a frontier theorem; it rules out finite contour algebra as
  a producer but does not constrain the infinite-source limit and was intentionally not added to
  the Lean corpus.
- Off-axis reduction: a holomorphic residual source on
  `{z | z.im < 1/2 ∧ z.re ≠ 0}` would already force RH.  An off-line zero `rho` rotates to
  `z = -I*(rho-1)` with `z.re = rho.im ≠ 0` (real-strip nonvanishing supplies the inequality),
  and the existing ODE-sector argument remains inside that punctured source domain.  This is a
  sharper target, but not a producer: proving it by generic phase oscillation would itself prove
  RH.  In particular the finite terminal discrepancy has x-independent norm, so horizontal phase
  cannot erase the terminal separately.
- The primitive joint-depth Euler source has an unconditional meromorphic residue at every Xi
  divisor, but its proven landing is the signed CCM/Route-P conormal carrier.  Exhaustive
  Route-T `XiHeatCassiniWold*.lean` source search finds no transport from that carrier or its
  residue to the Wold residual/orbit charge.  Thus this source residue cannot presently supply
  the required T2 tightness: treating it as a Route-T producer would silently add the missing
  source-to-Wold transport theorem.
- The missing safe-chamber transport is now exact: each Route-T Wold Laplace current is the cubic
  four-shift of the Möbius superposition of literal joint-depth off-diagonal Krein coefficients.
  The source argument for dilation `r` and shift `k` is `r*(s+k)-1`, and has positive real part
  for `Re s>0`, `r>=1`, `k>=1`; no divisor label occurs.  The resulting Lean capstone is
  `xiHeatCassiniWoldJointDepthMöbiusTransport_eq_woldLaplaceCurrent` in
  `XiHeatCassiniWoldJointDepthMöbiusSourceTransport.lean`, direct-checked with `lake env lean`.
  The remaining hard step is genuinely local: prove normal meromorphic continuation of the
  dilated tail near a hypothetical off-line Wold pole, then show that only `(r,k)=(1,1)` has a
  residue there.
- Termwise pole isolation is unconditional: at `s=rho-1` for `Re rho>1/2`, every canonical
  Möbius source continuation term with `r>=1`, `k>=1`, other than `(r,k)=(1,1)`, has argument
  `r*(rho-1+k)` in `Re>1` and is holomorphic.  Thus a tail cancellation of the Wold residue, if
  possible at all, must be a failure of normal convergence—not a second termwise divisor pole.
- The apparent normal-convergence escape is now closed for the actual `r>=2`, `k=1` Möbius
  source tail.  For every `a>1/2` and `Re z>=a`, its `r=n+2` term is dominated by
  `C_a * 2^(-n*a)`, where `C_a` is the absolutely convergent von-Mangoldt L-series norm at
  `2a`.  Hence the reindexed tail is absolutely summable pointwise and uniformly convergent on
  the entire closed half-plane.  The proof uses only Euler-half-plane identities and
  `|mu(n)|<=1`; it does not assume RH.
- The tail's natural variable is the source argument `z=s+k`, not the Wold variable `s`.
  Accordingly the literal `k=1` bridge is
  `tailTerm(n,z)=SourceContinuationTerm(n+2,1,z-1)`.  This removes a coordinate-shift error
  that would otherwise attach the normal tail to the wrong meromorphic location.
- The remaining Route-T obstacle is now sharply separated: transport the source-coordinate
  normal continuation through the safe-chamber source-to-Wold identity (or prove the equivalent
  local continuation identity).  It is no longer legitimate to attribute possible residue
  cancellation to a non-normal dilated source tail.
- The same normal family is holomorphic, not merely uniformly convergent: Lean proves the
  reindexed weighted tail differentiable on every open half-plane `Re z>a>1/2` using the complex
  Weierstrass theorem.  Thus its source germ is pole-free.  Scratch axiom audits of the norm,
  summability, uniform-convergence, and holomorphy theorems show only `propext`,
  `Classical.choice`, and `Quot.sound`.
- New safe-chamber conservation identity: for `Re z>1`, the literal prime-boundary source is
  exactly `infinitePrimeFlux z + DilationTail z`; the PNat `r=1` head and `r=n+2` tail are split
  without a rearrangement assumption beyond the tail's already-proved summability.  Hence the
  source continuation candidate has one and only one possible divisor carrier, the undilated
  flux.  Lean theorem: `xiHeatCassiniWoldJointDepthMöbiusSource_decomposition`, direct-checked
  with `lake env lean` on its module.  This does **not** transport the identity to the Wold
  current outside the Euler chamber; that missing germ-conservation law is now the precise
  Route-T producer obstacle.
- Möbius–valuation duality: on `Re z>1/2`, `DilationTail z = -xiPrimeLogHigherValuation z`.
  The equality is first forced in the Euler chamber by the preceding source conservation law,
  the prime-log Euler identity, and its higher-valuation decomposition, then extends by the
  connected half-plane identity theorem.  Thus normal Möbius dilations do not furnish a second
  Route-T singular comparison: they are exactly the already-known prime-power correction.  The
  positive survivor is narrower and non-absolute: any independent comparison must couple
  distinct source frequencies before dilation/absolute-value separation.  Lean theorem:
  `xiHeatCassiniWoldJointDepthMöbiusDilationTail_eq_neg_higherValuation`; direct source check
  and scratch axiom audit use only `propext`, `Classical.choice`, and `Quot.sound`.
- Normal source-germ transport is now closed, not assumed: define the source normal model as
  `infinitePrimeFlux + DilationTail`.  Möbius–valuation duality makes it exactly
  `xiPrimeLogDirichletContinuation` on `Re z>1/2`; its cubic four-shift is therefore exactly
  `xiHeatCassiniWoldLaplaceContinuation` on `Re s>-1/2`, which contains every strict-right Wold
  pole.  Lean theorems:
  `xiHeatCassiniWoldJointDepthMöbiusSourceNormalContinuation_eq_primeLogContinuation` and
  `xiHeatCassiniWoldJointDepthMöbiusNormalTransport_eq_woldLaplaceContinuation`.  This removes
  the former source-to-Wold germ-transport obstacle, but proves that this entire normal Möbius
  source family is the known divisor carrier, not the independent T2 comparison still required.
- The normal-source transport reaches the singular layer faithfully: every strict-right zeta zero
  gives a positive `m` and residue `-m` at `rho-1` for
  `xiHeatCassiniWoldJointDepthMöbiusNormalTransport` itself.  The proof restricts the closed
  normal-source/Wold identity to its punctured half-plane neighbourhood and transfers the known
  residue; it uses no continuation premise.  Lean theorem:
  `xiHeatCassiniWoldJointDepthMöbiusNormalTransport_zero_residue`, source-checked and audited
  with only `propext`, `Classical.choice`, and `Quot.sound`.  Consequence: no reorganization of
  this normal joint-depth Möbius source can be T2's second comparison; it already bears the
  entire forbidden residue.
- The source-to-orbit obstruction is unconditional: a strict-right zero produces one `m≥1` whose
  literal normal-source transport has residue `-m`, and every reflected finite shift-two
  completion of the corresponding head has `R ≠ 0`.  This removes the critical-energy hypothesis
  from the source-level compensator obstruction (not from natural-Abel regularity).  Lean theorem:
  `xiHeatCassiniWoldJointDepthMöbiusNormalTransport_cofinalCompensator`, source-checked and
  axiom-audited with only `propext`, `Classical.choice`, and `Quot.sound`.  The exact remaining
  T2 producer is now a source-derived law excluding this necessarily nonzero noncompact
  compensator; normal Möbius transport cannot supply it.
