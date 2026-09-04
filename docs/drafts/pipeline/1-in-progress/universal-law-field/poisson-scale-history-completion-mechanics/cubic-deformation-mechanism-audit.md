# Cubic deformation: clock power, transport jet, completion

- ID: ULF-CDMA-001
- Stage: 1-in-progress; audit of MCCED/PHCCED, not a new RH theorem.
- Status: `[FALSIFIED]` identification of clock-power defect with transport third jet;
  `[BRIDGE]` positive-clock recovery theorem has a complete paper proof, no Lean certificate.
- Scope: source-faithful cubic deformation of the completion extension. Lean read-only for this
  pass, following the active goal. Existing scratch files and other agents' changes left intact.
- Previous goal turn: progress (new scratch derivative proof and targeted corpus evidence).
- Current plan: verify mechanism against declarations; derive strongest survivor; correct facts;
  attack the surviving completion-level implication without substituting a scalar model.

## Higher-law target and exact RH obligation

The sought law must govern what survives forming an infinite arithmetic completion. Polynomial
operations on a fixed clock and loss of differentiability of an unrelated sequence do not yet
describe that operation. A successful deformation must retain the literal prime/depth coefficients
and change the relative theta completion class itself.

The unchanged RH edge is PHCCED.3--4 / MCCED.3--5: one pre-divisor deformation must yield the
completed Xi escape incidence and, on that same relative representative, the established primitive
Euler sub-unit estimate. Then an off-line copy would require an integer at least one and strictly
below one. Neither the algebra below nor its norm estimate establishes that identity. There is
no new primary conjecture on this card: selecting one before resolving the exposed category error
would recycle an unsupported mechanism.

## Corpus searches and exact evidence

All queries ran with `scripts/formal_tools.py research`; related definitions and proof bodies were
then inspected. Queries:

```text
cubic clock lifting class positive spectrum Sylvester divided difference
theta tanh cubic derivative trace ideal source valuation
cube clock commutator binomial mixed cubic deformation
third orbit derivative anticommutator prime log
prime log Laplace synthesis derivative clock intertwining domain
selfadjoint cube intertwiner clock polynomial reparametrization
nuclear ideal third tangent smooth curve trivial extension
operator monotone cube root divided difference Schur multiplier
cubic clock first obstruction polynomial ramification
Goodwillie cross effect cubic completion excision
derived inverse limit completion obstruction lim1 source
connected third difference Euler formation theta
```

Checked corpus locks and declarations:

- `HTGeometry/CubicClockExtensionLiftingObstruction.lean`: `ambientCubicDefect` is precisely
  `D_E^3 F-F D_X^3`. `quotientLanding_cubic` assumes the analogous quotient identity. This is a
  valid lifting obstruction for the powered clocks. It contains no topology or parameterized flow.
- Same module: `unipotentCompletionLift_cubicDefect` gives `(3z,0)` for every scalar lift;
  `identityClock_cubicCoboundary_zero` kills every correction. Its ordinary first clock defect is
  already `(z,0)`. The example distinguishes vector-space splitting from clock splitting, not
  first-order clock splitting from third-order transport.
- `RHTower/PrimeBurnolThetaModularHolonomy.lean`: `primeBurnolThetaRapidity a p=a log(p)/2`;
  `primeBurnolThetaFrameMatrix pe a` uses only `(pe i).1`. Depth is absent from the frame, while
  the Burnol Gram retains it. The matrix's reflection and modular identities are proved; an
  identification with literal Poisson/theta completion is not supplied by this module.
- `RHTower/PrimeDepthAliasingModularEscape.lean`: the boundedness classification concerns that
  particular prime-only frame. Its proof is valid. Calling it an intrinsic completion theorem
  would add an unproved source-frame identification. Replacing its frame by a valuation-clock
  frame changes the statement; no boundedness conclusion for that replacement has been proved.
- `RHTower/PrimeLogCubicLaplaceGraphFormation.lean`: the actual finite source is
  `2t sum_p c_p(log p)^2 p^(-1/2) exp(-t log p)`. Its canonical graph closure and source-core
  retention are proved. No relative theta extension identification is proved here.
- `RHTower/RoutePPrimeGammaBaseCubicWeight.lean`: exact valuation reindexing and summability of
  the complete base weight. These arithmetic facts do not construct a parameterized extension.
- `HTGeometry/PolarizedTangentGauge.lean`: tangent-normalized odd logarithms already start at
  degree three. `RHTower/SourceHorizontalWoldPrimeClockCubic.lean` already constructs actual
  coefficient-faithful cubic source jets and their cofinal limits. Cubic Taylor order alone is old.
- `RHTower/MobiusGammaXiMarkedClockBoundaryRateDecoupling.lean`:
  `exists_mobiusGammaXiMarkedZeroClockRate_boundaryTransport_debt` gives actual cofinal boundary
  transport and a vanishing pure clock rate while the remaining base debt is RH-equivalent.
  A homogeneous commutator cannot silently replace an affine completion charge.
- STATUS F182, F252--254, FAIL-59, CANNOT-278, MUST-193--198 already exclude ordinary derived
  completion, supplied cubic cocycles, scalar trace matching, and assumed bounded Xi admission.

## Exact killing mechanism

For fixed clocks write `L(F)=AF`, `R(F)=FB`, `delta=L-R`. Since `L R=R L`,

```text
omega_1 = AF-FB,
omega_pow3 = A^3F-FB^3 = A^2 omega_1+A omega_1 B+omega_1 B^2,
J_3 = (d/du)^3 [exp(uA)F exp(-uB)]_(u=0)
    = A^2 omega_1-2A omega_1 B+omega_1 B^2,
omega_pow3-J_3 = 3A omega_1 B.
```

In the corpus's unipotent example, `exp(uD_E)F_h exp(-u)` sends `z` to `((h+u)z,z)`.
Thus `J_3=0` although `omega_pow3=(3z,0)`. Conversely scalar clocks `A=omega`, `B=1`, with
`omega` a nontrivial cube root of one, have `omega_pow3=0` but `J_3=(omega-1)^3 F !=0`.
Even ideal-valuedness of the true third jet does not follow from CCEL's quotient hypothesis.
For an unbounded orbit, these identities require a common invariant core or justified derivatives;
the finite examples need neither qualification.

**Verdict:** `FALSE` as an identification with a third transport jet; `BRIDGE` as an obstruction
for powered clocks. The existing Lean theorems remain correct with their literal statements.

## Strongest positive survivor

[Paper](../../../2-fully-proven/universal-law-field/poisson-scale-history-completion-mechanics/cubic-clock-transport-separation-law.md)
proves the finite algebraic separation and its countable trace-ideal strengthening.
For clocks with labelled values `a_i,b_j>=c>0`, set `m_ij=a_i^2+a_i b_j+b_j^2`.
If the cubic extension coefficient `K_3` is trace class, its ordinary coefficient is recovered
coefficientwise by `K_1(i,j)=K_3(i,j)/m_ij`, with

```text
||K_1||_1 <= ||K_3||_1/(3c^2).
K_3+(a_i^3-b_j^3)H_ij=0  iff  K_1+(a_i-b_j)H_ij=0.
```

The same trace-class correction `H` works, including resonant entries. The countable statement
uses maximal coefficient domains, explicitly not an arbitrary smaller physical domain. Therefore
the remaining distinction must come from the actual completion domains/formation, not positive
clock cubing itself. This is standard divided-difference analysis applied to the proposed model;
no priority or new-field claim. Paper-proof complete; Lean not written under current read-only
instruction. Keep this survivor out of Stage 3.

## The proposed scalar ideal-exit pivot also fails the mechanism test

The carried-over scratch proposes weighting `tanh(a log(n)/2)` by the base Euler mass; its formal
third neutral jet recovers the unsquared Euler coefficient after normalization. This can be a
correct identity without yielding an extension class.

Explicit nonarithmetic control: on `ell2(N_{>=1})`,

```text
V(a)=diag(n^(-4) tanh(an)).
```

`V` is trace-class valued, `C^2` on the real line, smooth off zero, and has no third trace-norm
derivative at zero: any such derivative would have diagonal `-2/n`. First two differentiated
series are uniformly dominated by summable multiples of `n^-3,n^-2`; off zero exponential decay
dominates every differentiated series. Coordinate evaluation gives the divergent third diagonal.
Yet its image in the Calkin algebra is identically zero, and it is a path in a split extension.
It even lies in a uniformly sub-unit trace ball after multiplication by any sufficiently small
fixed constant, with the same third-derivative failure. This disproves inference from that pattern
alone to a nonzero completion/index class. It does not disprove a future theta-specific theorem.

No scalar ideal-exit Lean project is justified as the primary mechanism. The derivative scratch is
retained as scratch, not promoted. A weighted diagonal model cannot establish retention of the
off-diagonal Burnol data or an integral boundary map.

## External audit and next attack

- [Connes--Consani--Moscovici, Zeta Spectral Triples](https://arxiv.org/html/2511.22755v1): finite
  Euler products give self-adjoint spectral models; the required limiting identification remains
  the RH-bearing step. It supplies no automatic Xi admission for our independently defined frame.
- [Chattopadhyay--van Nuland--Pradhan, revised April 2026](https://arxiv.org/html/2404.18422v3):
  higher operator derivatives and spectral-shift formulas require specified relative boundedness
  and Schatten conditions. A third derivative is an operator-integral expression, not a difference
  of clock cubes. These results do not establish the missing arithmetic/domain hypotheses.
- [Le Merdy--Skripka](https://arxiv.org/abs/1901.05586): regularity of scalar symbols is governed
  by operator/Schatten hypotheses; no automatic trace-class third derivative at an unbounded clock.
- [Kaad](https://arxiv.org/abs/1111.6546): modular index pairings use modular admissibility and
  weighted kernel/cokernel traces. Such a pairing cannot be assumed to be our ordinary integer.
- [Chansangiam](https://arxiv.org/html/1305.2471v1), integral representations: parent theory of
  the cube-root divided difference used in the survivor. The survivor is a bridge, not novel math.

The first attempted replacement is already known: the critical Laplace source obeys
`A_* P_u=K_u A_*`, where `P_u c(p)=p^-u c(p)` and `K_u f(t)=t/(t+u)f(t+u)`.
Searches `Laplace synthesis weighted translation t divided t plus shift`,
`primeLogCriticalLaplace semigroup intertwining`, and
`shift semigroup kernel infinite dimensional not Fredholm half line` identified
`RoutePPrimitiveBurnolApertureDampingSemigroup.lean`. It already proves the exact shift,
semigroup law, contraction, primitive eigenfeature action, and backward failure.
**Verdict: REDISCOVERED; no new formalization project.**

The graph implication is also direct: approximate any `c` in `Dom(cl A_*)` by finite source
vectors in graph norm. Boundedness of `P_u,K_u` passes the identity through closure, proving
`P_u c` is in the same domain and `cl A_* P_u c=K_u cl A_* c`. Thus forward source transport is
already compatible with this source completion. Its existence cannot generate the missing
relative theta anomaly. This is a paper corollary, not a new Lean theorem or a selection law.

Next exact attack: determine how literal Poisson completion acts on this *already covariant*
graph, including its domains and affine boundary term. That action must differ in a demonstrable
way from both the existing forward shift and a polynomial reparametrization of its generator.
If those data are supplied only after Xi specialization, PHCCED has no pre-divisor realization.
Ordinary clocks, scalar singular support, and an unspecified derived category do not fill the gap.
