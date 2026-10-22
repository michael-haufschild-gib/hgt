# Prime--Gamma signed-permutation Eulerian limit and RH

- **ID:** `prime-gamma-signed-permutation-eulerian-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [SIGNED-COXETER CHAIN]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/BornSectorExchange.lean`,
  `formal/GaloisForLFunctions/RHTower/BornGradedKMSClassification.lean`,
  `formal/GaloisForLFunctions/RHTower/SignedReflectionParity.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailTelescope.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSource.lean`, with current
  determinant capstones
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerOrdinaryDeterminant.lean`
  and
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo.lean`
- **Statement:** `[CONJECTURE]` Functional-equation reflection upgrades finite ordered prime words
  to signed permutations whose completed descent weights are a nonnegative specialization of a
  stable type-B Eulerian polynomial.  A cofinal locally uniform limit of these negative-rooted
  polynomials is the square-coordinate centered Xi function, implying RH.

## Why this detour is different

The state space is the hyperoctahedral Coxeter group, not a zero divisor, graph, moment measure, or
operator spectrum.  Prime labels provide an order through `log p`; the functional equation provides
the sign/reflection bit; the statistic read by the consumer is descent across adjacent ordered
letters.  Real-rootedness comes from stability-preserving Coxeter insertion recurrences.

## Finite consumer

For a signed permutation `sigma` in the type-B Weyl group `B_N`, let `des_B(sigma)` be its type-B
descent number.  The ordinary type-B Eulerian polynomial

```text
B_N(u)=sum_(sigma in B_N) u^des_B(sigma)
```

has only negative real zeros.  More strongly, Visontai--Williams refine a signed word by its
descent-top set, ascent-top set, and number of negative letters.  The top attached to an adjacent
pair is the maximum absolute label, not its position and not the ordered edge.  Their polynomial
`B_N(x,y;q)` is stable for `q>0`, and nonnegative real specialization followed by diagonalization
remains real-rooted.  Positive coefficients then put its zeros on the nonpositive real axis.

This distinction is essential.  Position-indexed Eulerian refinements can fail stability, and
arbitrary positive weights on signed permutations do not inherit real-rootedness.

## The closed chain

Let `A` again be the normalized square-coordinate function

```text
XiC(z)/XiC(0)=A(-z^2),
A(u)=sum_(n>=0) a_n u^n,
a_n=thetaCuspRawEvenMoment(n)/((2n)! thetaCuspRawEvenMoment(0)).
```

Seek a triangular family of completed signed-permutation packets `E_N`:

```text
ordered prime labels log p_1 < ... < log p_N
  + functional-equation reflection / graded parity
  -> signed prime words in B_N
  -> nonnegative top-label activities, or a new proved stable refinement
  -> stability-preserving specialization E_N(u) of the multivariate type-B Eulerian polynomial
                                                               [OPEN CORE A]
  -> every zero of E_N is negative real                         [KNOWN]
  -> E_N(0)=1 and E_N -> A locally uniformly on compact sets    [OPEN CORE B]
  -> Hurwitz confines every zero of A to the negative real ray
  -> XiC(z)/XiC(0)=A(-z^2) confines every XiC zero to the real axis
  -> RH.
```

Conversely, RH supplies negative-rooted polynomial sections through the paired Xi product, so the
consumer end is exact.  The new science must be the source-derived signed descent specialization,
not a factorization using Xi zeros.

## The raw order-blind Euler model is closed

Raw Euler weights multiply over prime content and are invariant under reordering a fixed set of
letters.  If the reflection sign sector is also weighted independently of descent position, then
after constant normalization every size-`N` packet is just a linearly rescaled universal type-B
Eulerian polynomial

```text
B_N(c_N u).
```

Its first two nonconstant coefficients are

```text
[u] B_N(u)   = 3^N-(N+1),
[u^2]B_N(u)  = 5^N-(N+1)3^N+binom(N+1,2).
```

If `c_N` is chosen so that the linear coefficient tends to `a_1>0`, then

```text
[u^2] B_N(c_N u)
  -> a_1^2 lim_N [u^2]B_N/[u]B_N^2
  = 0,
```

because the ratio is asymptotic to `(5/9)^N`.  But the theta source has

```text
a_2/a_1^2 = 0.46518380969515456525408779214656... > 0.
```

Therefore no order-blind multiplicative Euler weighting, under any scalar activity rescaling, can
converge coefficientwise or locally uniformly to `A`.

## Positive statement from the no-go

The former proposed minimal datum was a genuinely order-sensitive positive local factor

```text
kappa_N(p_i,p_j; sign_i,sign_j)
```

attached when adjacent signed prime letters form a descent.  The four-letter fiber-curvature theorem
in `../../../3-formalized/needs-audit/prime-gamma-descent-top-fiber-curvature-obstruction.md` now shows that direct
specialization of the Visontai--Williams polynomial forces every positive-sector `2 x 2`
multiplicative minor of `kappa` to vanish.  Hence `kappa` is rank-one separable on descending pairs.
Generic order-sensitive Gamma curvature cannot survive as a scalar top activity.

The first tests are now two-tiered.  Extract two- and three-label completed weights to identify the
candidate source law, but also extract four-label weights and compare the fiber-colliding words
`(3,1,4,2)` and `(3,2,4,1)`.  Their weight ratio is the first scalar-stability discriminator.  A
nonunit ratio is the signed insertion curvature and rules out direct top specialization even if the
`B_2 -> B_3` recurrence passes.

## Candidate source mechanism

The corpus already formalizes a completed graded sector swap in the Bost--Connes/KMS picture and
reflection-graded pair signatures.  The proposed bridge is:

```text
KMS integer/half-integer sector exchange
  -> sign change of a reflected prime letter                 [NOT YET CONSTRUCTED]
  -> type-B simple reflection                                [NOT YET CONSTRUCTED]
  -> top-signature support or matrix holonomy
  -> proved stable signed Eulerian or determinantal operator.
```

The bridge must be proved on finite prime words before any thermodynamic/KMS limit.  Current corpus
only proves a global exchange of two completed analytic sectors; it does not act on individual
prime letters.  `SignedReflectionParity.lean` further proves that functional-equation sign controls
fixed-point order parity and explicitly fails away from the fixed point.  Equality of ungraded
partition functions is therefore insufficient to manufacture a letterwise Coxeter action.

## Attacks and positive successors

1. **Order-blindness attack.**  Multiplicative weights constant on signed reorderings reduce to a
   scaled universal Eulerian polynomial and have vanishing normalized quadratic coefficient.
   **Positive successor:** the exact descent-local completion cocycle above.
2. **Arbitrary-weight attack.**  A positive weighted sum of descent monomials need not be stable.
   **Positive successor:** prove that the weights arise by nonnegative specialization of the known
   multivariate stable polynomial or by its stability-preserving insertion operator.
3. **Type-A collapse attack.**  Forgetting reflection loses the sign sector and merely recovers
   ordinary permutations.
   **Positive successor:** identify the functional-equation involution with a type-B simple
   reflection and retain its boundary descent at position zero.
4. **Inverse-descent attack.**  One can solve finite linear systems to fit a desired polynomial by
   weighted permutations.
   **Positive successor:** weights must be local functions of prime/Gamma data and compatible under
   Coxeter insertion; no Xi coefficient may define an individual permutation weight.
5. **Coefficient-only attack.**  Agreement through finitely many descent numbers does not control
   zeros in the limit.
   **Positive successor:** prove compact normality and locally uniform convergence from a common
   insertion recursion and source weight bounds.
6. **Signed-cancellation attack.**  The functional equation naturally carries signs, while the
   stable specialization requires a common nonnegative phase.
   **Positive successor:** realize signs as the signed-permutation state, leaving the numerical
   descent activities nonnegative.  If a negative activity remains, preserve it as a frustration
   cocycle and retire the stable consumer.
7. **Top-fiber attack.**  The known stable polynomial is indexed by ascent/descent tops, not ordered
   adjacent edges.  The words `3142` and `3241` have identical type-B top signatures but descent
   edge products `kappa(3,1)kappa(4,2)` and `kappa(3,2)kappa(4,1)`.
   **Verdict:** `FALSE` for generic scalar edge cocycles.  **Positive survivor:** four-label
   multiplicative curvature; compatibility forces curvature zero and positive kernels become
   rank-one.  **Stronger replacement conjecture:** completion curvature changes allowed signed-word
   support or enters a matrix-stable pencil before scalarization, rather than weighting edges in a
   fixed top-signature fiber.
8. **Global-to-letter reflection attack.**  Corpus functional-equation reflection is one global
   involution and its signed parity theorem reaches only the fixed point.
   **Verdict:** `FALSE` for the claim that reflection alone canonically signs every prime letter.
   **Positive survivor:** any genuine letter sign must be supplied by a source disintegration
   compatible with the global sector exchange; it cannot be inferred from Xi symmetry.

## Gate-1 reset and current conjecture loop (15 August 2026)

- `[LITERATURE]` Visontai--Williams stability tracks `DT_B`, `AT_B`, and negative-letter count; its
  insertion operator is `(q x + y) + (1+q)xy partial`.  It does not accept arbitrary edge weights.
- `[CORPUS]` The four-letter curvature obstruction and positive rank-one classification are
  `[LEAN-PROVED]` at
  `../../../3-formalized/needs-audit/prime-gamma-descent-top-fiber-curvature-obstruction.md` and
  `formal/GaloisForLFunctions/HTGeometry/SignedEulerianTopFiberCurvature.lean`.
- `[CORPUS]` `PrimeWordEnsembleBoundaryTomography.lean` recovers support-cardinality aggregates,
  not word order.  `BornSectorExchange.lean` exchanges completed sectors globally.
  `SignedReflectionParity.lean` proves fixed-point-only parity reach.  None constructs a signed
  prime-word action.
- `[FALSIFIED]` Direct generic adjacent-edge specialization inside the known type-B stable cone.
- `[CONJECTURE]` **Support-curvature transmutation:** the completed prime--Gamma four-letter
  curvature selects or transports signed-word histories, and the resulting support class or
  Hermitian pencil has a proved stability-preserving insertion law whose normalized scalar
  specialization converges locally uniformly to `A`.
- `[PROVED FINITE SURVIVOR]` The first-trace Boolean Euler connection already has nonzero
  support-valued square curvature, while completed-face scalar characters kill it.  A rank-two
  Pluecker/Gram pencil retains any four-label curvature `Delta` as the stable coefficient
  `Delta^2 z w`; see
  `../../../3-formalized/needs-audit/prime-gamma-signed-eulerian-curvature-plucker-lift.md`.
- `[SUPERSEDED OPEN CORE]` Artificial all-prime depth-paired `K_N` construction is no longer
  preferred. P-G94's literal overlapping six-minor covariance already gives canonical finite
  principal matrices and cofinal source operator before Xi divisor reading. Remaining comparison
  is arithmetic, not matrix existence.
- `[FALSIFIED METRIC]` Literal nested first-trace edges in uniform Boolean `L^2` have normalized
  quadratic coefficient at most `13/98`, while theta moment log-convexity forces
  `a_2/a_1^2 >= 1/6`.  No scalar normalization can repair the gap; see
  `../../../3-formalized/needs-audit/prime-gamma-uniform-boolean-gram-quadratic-no-go.md`.
- `[PROVED UNIT-DIAGONAL METRIC PRODUCER]` Route P's normalized cubic Cauchy/Hellinger columns convert balanced
  Route-E load chi-square `chi` into Pluecker defect `chi(3-3chi+chi^2)`, between `chi` and
  `3chi`.  Pairing every primitive cell with its twice-iterated depth-square partner gives
  `chi=9/25` and normalized Gram ratio `11529/62500 > 1/6 > 13/98`, without Xi data; see
  `../../../3-formalized/needs-audit/route-e-p-sp-e-cubic-hellinger-plucker-load-bridge.md`.
- `[FALSIFIED SOURCE-FAITHFUL LIFT]` Two coefficient-faithful depth-square transports contract
  cubic diagonal energy by exactly `1/64`. Actual rate-four pair ratio is
  `737856/66015625 < 13/98 < 1/6`. Equal-diagonal repair uniquely requires extra nonnegative
  amplitude `8` and adds trace `63w/64`; see
  `../../../3-formalized/needs-audit/route-e-p-sp-e-cubic-source-normalization-debt.md`.
- `[PIVOT PROVED]` Full P-G94/P-G95 physical-overlap covariance avoids local rebalancing entirely.
  Its canonical Hilbert--Schmidt coordinate kernel reconstructs source operator exactly. Every
  finite reflected principal `det2(I+uT_s)` has only strictly negative-real zeros, finite sections
  converge locally uniformly on every closed disc, and cofinal entire determinant has same strict
  zero ray; see
  `../../../3-formalized/needs-audit/prime-gamma-physical-plucker-entire-determinant.md`.
- `[FALSIFIED DIRECT DETERMINANT — P-G99]` `det2` has zero first jet. Canonical ordinary Fredholm
  repair restores literal physical trace, but Lean proves exact Bernoulli diagonal formula and
  universal fixed-node ceiling
  `sourceTrace <= 1/50 < thetaCuspNormalizedEvenMoment 1 / 2`.  Bound holds for arbitrary real
  coordinate means, so probability reweighting cannot repair it; see
  `../../../3-formalized/needs-audit/prime-gamma-physical-plucker-first-trace-no-go.md`.
- `[PIVOT PROVED — P-G100]` Canonical continuous-zero transfer recovers one trace unit per finite
  coordinate and is cofinally unbounded before source descent.  Source weights before boundary
  limit select residue `4`; polar countercurrent cancels it; exact remaining defect is
  `eps R(eps)`.  Scalar finite-limit renormalization of unweighted faces is impossible; see
  `../../../3-formalized/needs-audit/prime-gamma-physical-plucker-boundary-trace-capacity.md`.
- `[FALSIFIED BOUNDED AMPLIFICATION — P-G101]` P-G100 escape is rank accumulation, not gain. Both
  bounded resolvent channels have norm one and cannot supply uniquely required fourth-depth
  amplitude `8`; only unnormalized inverse survives, necessarily at `eps<=1/8`; see
  `../../../3-formalized/needs-audit/prime-gamma-physical-plucker-boundary-amplification-no-go.md`.
- `[FALSIFIED CANONICAL INVERSE AMPLIFICATION — P-G102]` Exact inverse gain `c` selects original
  spectral shell `1/c-eps`.  At `c=8`, current positive physical operator has no such nonzero
  vector for `0<eps<21/200`, because literal nuclear expansion gives
  `||T||<=sourceTrace<=1/50<1/8-eps`.  Thus amplitude eight cannot persist toward zero boundary;
  see `../../../3-formalized/needs-audit/prime-gamma-physical-plucker-boundary-spectral-shell-no-go.md`.
- `[PIVOT PROVED — P-G103]` Positive source/source Schur shorting cannot increase fourth-depth
  energy.  One negative polar pivot `-w` restores `w/64` to `w` iff cross square is
  `(63/64)w^2`; unique nonnegative cross is `(sqrt 63 / 8)w` and block determinant is `-w^2`.
  Full cross `w` returns `65w/64`, exactly original coefficient-faithful pair trace; see
  `../../../3-formalized/needs-audit/route-e-p-sp-e-source-normalization-krein-shorting.md`.
- `[COEFFICIENT PROVENANCE CLOSED — P-G104]` Two literal Route-P depth-square steps have
  squared-energy factor `1/64`, so normalized Hilbert amplitude is `c=1/8`. Canonical Julia defect
  is `sqrt(1-c^2)=sqrt(63)/8`; pairing parent amplitude `sqrt w` with defect amplitude
  `(sqrt(63)/8)sqrt w` gives exactly P-G103's cross. This coefficient is source-forced, not fitted;
  see `../../../3-formalized/needs-audit/route-e-p-sp-e-fourth-depth-julia-defect-krein-completion.md`.
- `[LITERAL CO-POISSON COLLIGATION — P-G105]` P-G179's physical two-step map is exactly
  `A=(1/8)U_4` on Burnol's even co-Poisson carrier, with `U_4` unitary. Its Julia defect is
  `D=(sqrt 63/8)I`; child and defect remain at apertures `b/4` and `b`, full two-channel transport
  is isometric, and parent--defect pairing is P-G103's cross.
- `[EXACT KREIN PIVOT REALIZED — P-G105B]` Same Julia data canonically produce co-graph pivot
  `p_f=((d/c)U_4f,(1/c)f)`. In source-exchange signature, child `x_f=(cU_4f,0)` and pivot have
  exact block `[[w/64,dw],[dw,-w]]`, determinant `-w^2`, and Schur short `w`. Both pivot
  coordinates stay in Burnol source ladder. Negative sign is Hadamard diagonalization of
  source/co-source exchange, not fitted scalar orientation; see
  `../../../3-formalized/needs-audit/route-p-fourth-depth-copoisson-julia-krein-pivot.md`.
- `[MATRIX-COMPLETE KREIN LIFT — P-G105C]` Polarized Julia--Krein identities hold for arbitrary
  pairs in P-G186's actual half-line feature carrier. Every finite completed Gram is exactly
  `B tensor G`, where `B=[[1/64,d],[d,-1]]` and `det(B)=-1`; hence its determinant is
  `(-1)^N det(G)^2` and completion is nondegenerate iff original P-G186 Gram is. All off-diagonal
  prime/depth/ordinate incidence survives without orthogonality or fitted coefficients; see
  `../../../3-formalized/needs-audit/route-p-primitive-burnol-julia-krein-matrix-completion.md`.
- `[GAMMA-CYCLIC INTERTWINER — P-G105D]` For running prime odds `a`, unique thermal gauge
  `T=(8+a)/7` forces literal co-Poisson Cayley coordinate `1/8`. Child and Gamma cyclic complement
  are exactly `a/64` and `63a/64`; square of actual archimedean cyclic characteristic at
  `artanh(1/8)` is Julia defect `sqrt(63)/8`. Gamma defect continuous linear map and both physical/
  half-line co-graph pivots equal P-G105/P-G105B/P-G105C Julia objects exactly; see
  `../../../3-formalized/needs-audit/route-p-fourth-depth-gamma-cyclic-julia-intertwiner.md`.
- `[SCALAR SOURCE WELD FALSIFIED; LOG SURVIVOR — P-G105E]` Actual joint-depth Xi source and
  reciprocal-promotion co-source satisfy `source(p,e)=log(p) coSource(p,e)`. Primes `2` and `3`
  exclude every real and complex global scalar intertwiner. Exact Gamma--Julia replacement is
  label-diagonal multiplier `(sqrt(63)/8)log(p)`, independent of depth and defined on literal
  co-source vector. Universal Kronecker completion therefore cannot itself be called Xi landing;
  see `../../../3-formalized/needs-audit/route-p-joint-depth-gamma-julia-scalar-intertwiner-no-go.md`.
- `[PRIME-LOG MATRIX COMPLETION — P-G105F]` For every finite primitive packet,
  `L=diag(log p_i)` retains full incidence as `(LGL)_ij=log(p_i)G_ij log(p_j)`. Completed matrix is
  exactly `B tensor (LGL)` and has determinant `(-1)^N det(L)^4 det(G)^2`; it is nondegenerate iff
  original `G` is. Thus operator-valued arithmetic weld changes finite volume but creates no hidden
  degeneracy; see
  `../../../3-formalized/needs-audit/route-p-joint-depth-gamma-julia-log-krein-matrix-completion.md`.
- `[FINITE SIGNED BIVARIATE STABILITY — P-G105G]` Child/pivot row pencil
  `I+((diag(z,w)B) tensor LGL)` is exact left channel action on P-G105F completion. Its determinant
  factors over nonnegative Gram eigenvalues as
  `product_lambda (1+lambda z/64-lambda w-lambda^2 z w)`. Every positive-lambda zero solver is an
  orientation-reversing real Möbius map from upper to lower half-plane; zero eigenvalues contribute
  `1`. Hence actual full finite P-G186 pencil is bivariate stable for every packet, without
  injectivity or nondegeneracy; see
  `../../../3-formalized/needs-audit/route-p-primitive-gamma-julia-signed-bivariate-stability.md`.
- `[RAW COFINAL TRACE FALSIFIED; EULER-POLE SURVIVOR — P-G105H]` Prime-log congruence cancels
  P-G186's two-log diagonal regularizer exactly. Actual finite trace density becomes
  `(1/4)p^{-(e+1)}(e+1)^-3`, with depth-zero slice `1/(4p)`. Hence raw all-cell trace is
  nonsummable and positive finite sums are unbounded. Exact survivor is Euler-pole coefficient
  `1/4`, which a source-derived polar/Stokes completion must cancel; see
  `../../../3-formalized/needs-audit/route-p-primitive-gamma-julia-log-cofinal-trace-no-go.md`.
- `[SOURCE-TO-STOKES RESIDUE TRANSPORT — P-G105I]` Only depth-zero face is singular; all positive
  depths are summable. Positive diagonal scale squared `32d log(p)p^(-2d)` sends exact P-G105H
  density `1/(4p)` labelwise to literal oriented Stokes term
  `8d log(p)p^{-(1+2d)}`. Congruence acts on actual finite P-G186 matrix. All-prime trace plus
  explicit polar/Gamma countercurrent equals completed prime--Gamma current and tends to zero at
  wall; see
  `../../../3-formalized/needs-audit/route-p-primitive-gamma-julia-stokes-aperture-residue-transport.md`.
- `[PHYSICAL STOKES STABLE SPECIALIZATION — P-G105J]` Forced pivot ratio
  `r(d)=-polarCurrent(d)/primeCurrent(d)` tends `1` and is eventually positive. Physical pencil
  specializes P-G105G by `z=64u`, `w=r(d)u`; actual aperture-conjugated P-G186 Gram stays PSD, so
  every finite physical determinant is upper-half-plane stable near wall. Generator trace is
  `(1-r(d))` times finite child trace and all-prime value is exactly completed prime--Gamma current;
  see
  `../../../3-formalized/needs-audit/route-p-primitive-gamma-julia-physical-stokes-stable-specialization.md`.
- `[REFINED OPEN CORE]` Stop comparing higher coefficients of direct P-G98 determinant and stop
  treating scalar functional calculus of current positive operator as normalization repair.
  Local contraction, defect, sign, pivot, shorting, full finite matrix incidence, and Gamma cyclic
  coefficient/operator provenance are closed. Constant source/co-source weld is now rigorously dead.
  Prime-log operator-valued full finite algebra and signed bivariate finite stability are closed.
  Raw trace-class cofinalization is rigorously dead with exact Euler-pole coefficient `1/4`.
  Trace-level aperture/polar countertransport, forced physical channel ratio, and finite stable
  specialization now exist exactly. Construct cofinal determinant for physical generators with
  trace/determinant-class control and divisor retention, then identify completed divisor with Xi.
  Do not normalize target holonomy.

## Primary parent results

- M. Visontai and N. Williams, *Stable multivariate W-Eulerian polynomials*,
  <https://arxiv.org/abs/1203.0791>;
- P. Brändén and M. Leander, *Multivariate P-Eulerian polynomials*,
  <https://arxiv.org/abs/1604.04140>, for the poset/linear-extension enlargement.

## Kill conditions

Retire the raw order-blind model by the quadratic-coefficient asymptotic above.  Retire the completed
model if the finite signed weights cannot be expressed through a stability-preserving descent
specialization, if the insertion defect is nonzero under every canonical Gamma/KMS grading, or if
the normalized family lacks a nonzero locally uniform limit equal to `A`.  Preserve the insertion
defect, any stable restricted signed-word class, and any exact completion-induced Coxeter action as
positive results.

## Gates

- [x] type-B stable finite consumer identified
- [x] two-ended signed-permutation-to-RH chain closed
- [x] raw order-blind Euler weighting rigorously excluded by coefficient asymptotics
- [x] direct scalar descent-local cocycle generically excluded by four-label curvature
- [x] four-letter curvature invariant and rank-one positive survivor paper-proved
- [x] corrected first decisive finite insertion test from rank three to rank four
- [x] literal support-valued source insertion curvature located
- [x] curvature-preserving stable Pluecker/Gram finite consumer constructed
- [x] uniform Boolean Gram metric excluded by exact rational quadratic gap
- [x] source-native cubic Gamma/Hellinger metric block constructed
- [x] canonical primitive fourth-depth block clears exact `1/6` quadratic floor
- [x] raw fourth-depth source-faithful lift excluded; exact normalization debt classified
- [x] literal physical-overlap cofinal positive trace-class operator constructed
- [x] canonical finite source determinants proved strictly negative-real-rooted after reflection
- [x] finite source determinants proved locally uniformly convergent to stable entire limit
- [x] cofinal source determinant proved strictly negative-real-rooted
- [ ] completed weights of all signed orders on two and three prime labels extracted
- [ ] completed weights on the fiber-colliding four-label pair extracted
- [ ] cubic Gamma/co-Poisson metric assembled on full two-face curvature family
- [ ] source curvature sections identified with completed signed-word columns
- [x] cofinal physical Pluecker determinant family constructed from prime--Gamma source
- [x] direct `det2` and canonical ordinary determinant identification excluded at first jet
- [x] all real coordinate-mean reweightings on fixed physical nodes excluded by trace capacity
- [x] canonical boundary transfer capacity and four-unit relative residue classified
- [x] bounded transfer/normalized-inverse amplitude-eight correction excluded
- [x] unnormalized-inverse amplitude-eight correction excluded near zero by exact spectral shell
- [x] positive-pivot shorting excluded; unique one-negative-index cross target classified
- [x] cross magnitude `(sqrt 63 / 8)w` derived from literal fourth-depth Julia defect pairing
- [x] fourth-depth contraction and Julia defect realized on actual Burnol co-Poisson source spaces
- [x] exact negative pivot, Krein block, determinant, and restored shorting realized locally
- [x] Julia--Krein lift tensorized over full finite P-G186 Gram, including all off-diagonal entries
- [x] Route-P Julia defect identified with literal Gamma cyclic characteristic/operator channel
- [x] constant scalar identification with literal joint-depth Xi co-source excluded
- [x] exact prime-log diagonal Gamma--Julia survivor constructed on joint-depth Hilbert source
- [x] prime-log operator-valued completion constructed over arbitrary full finite source matrix
- [x] signed bivariate finite stable pencil proved for full completed P-G186 incidence
- [x] raw prime-log cofinal trace class excluded; exact depth-zero Euler-pole coefficient proved
- [x] trace-level child source identified with literal source-derived Stokes orientation
- [x] source-derived aperture/polar trace countertransport cancels exact raw Euler pole
- [x] polar countercurrent fixes source-faithful projective pivot ratio near wall
- [x] physical child/pivot specialization proved stable on every finite packet near wall
- [ ] physical specialization proved stable through locally uniform cofinal determinant limit
- [ ] exact `63w/64` fourth-depth trace debt paid by completed countercurrent
- [ ] transferred logarithmic coefficients or divisor identified with completed theta source
- [ ] locally uniform limit identified with `A`
- [ ] RH capstone formalized

## P-G105 first signed Fredholm jet (2026-08-22)

- [LOCAL-RESEARCH] Corpus search established that the all-order local-uniform exponential wall
  limit was already closed; the unstated source invariant was its first signed Fredholm jet.
- [PAPER-PROVED] For the unit-exponential wall kernel
  `K(a,b) = 8 (sqrt a)^3 (sqrt b)^3 / (a+b)^3`, the diagonal is one and the two-label
  determinant is `1 - K(a,b)^2`.  The existing exact source integral
  `∫ K(a,b)^2 d(Exp(1) × Exp(1)) = 16/35` therefore gives
  `c_0 = 1`, `c_1 = 1`, and `c_2 = (1 - 16/35)/2 = 19/70`.
  Hence the quadratic coefficient of the signed product `D(z)D(-z)` is the sharp source value
  `2*c_2 - c_1^2 = -16/35`.
- [LEAN-PROVED] `RoutePPrimitiveGammaJuliaStokesWallFirstJetInvariant.lean` proves the diagonal
  and symmetry identities, all three coefficients, and
  `routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_exp`.  Its two-label proof uses
  `measurePreserving_finTwoArrow` to transport the fixed quantile cube to the existing unit-square
  coherence integral; no numeric approximation or fitted normalization is introduced.
- [OPEN CORE] The remaining SP-E landing problem is now sharpened: a divisor identification with
  the completed theta/Xi source must respect this forced quadratic jet (under a canonical
  normalization), or exhibit a source-derived correction whose own first jet is formalized.  No
  such identification or correction is asserted here.

## P-G105 canonical-scale theta-jet no-go (2026-08-22)

- [CONJECTURE] The fixed canonical SP-E wall scaling might land directly on the central completed
  theta/Xi normalization.
- [FALSIFIED] Direct quadratic-jet matching would require
  `thetaCuspNormalizedEvenMoment 1 = 32/35`, because the normalized theta/Xi jet is
  `-thetaCuspNormalizedEvenMoment 1 / 2` whereas the wall product jet is `-16/35`.
  The independent corpus bound
  `thetaCuspNormalizedEvenMoment 1 < 29/625 < 32/35` rules this out unconditionally.
- [LEAN-PROVED] `RoutePPrimitiveGammaJuliaStokesWallThetaJetSeparation.lean` proves both the
  rational theta bound at the required calibration and the complex jet inequality
  `routePPrimitiveGammaJuliaStokesWallSignedSquareQuadraticJet_ne_thetaCanonical`.
- [POSITIVE SURVIVOR] Any viable SP-E divisor landing must introduce an independently
  source-derived scale law or correction whose quadratic jet is explicit.  An arbitrary target-fit
  rescaling is excluded as a proof strategy; this no-go does not retire source-derived corrections.
