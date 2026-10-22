# RH research through new geometry or topology

- **ID:** RH-NIG-20261006
- **Stage:** 1-in-progress
- **Type:** CANDIDATE SEARCH; no new RH route admitted
- **Source:** `docs/reports/rh-current-frontier-map.md`; `xi-conductor-nearby-cycle-degeneration.md`
- **Statement:** Find a source-derived geometric or topological mechanism that constrains the actual Xi divisor, without positivity, spectral constructions, Fourier transforms, or estimates of bounds.

## Objective and constraints

Ultimate goal remains an unconditional Lean proof or falsification of RH. A research checkpoint is not completion.

User added these restrictions on 2026-10-06:

1. Proof cannot come from positivity.
2. Proof cannot concern energy levels, frequencies, Fourier transforms, or spectral constructions.
3. Proof cannot come from estimating bounds.
4. Proof must concern a new form of geometry or topology; iterated infinite constructions are allowed.

These restrictions also exclude repackaging an eigenvalue argument as a period or monodromy-character argument. No computational experiment was run. No new Lean code was written in this screening cycle.

## Working plan

- [x] Read attached objective and hgtl7 workflow; load project memories and frontier sources.
- [x] Apply the new exclusions to candidate selection.
- [x] Audit prime-face topology, prime-zeta ramification, and existing conductor degeneration.
- [x] Record exact rejection mechanisms and limits of the evidence.
- [ ] Find a source-level global geometric operation not removed by the existing scalar gauges.
- [ ] Freeze an exact, falsifiable conjecture and attack it against both corpus and literature.
- [ ] Complete a dependency-closed paper proof of a surviving significant result.
- [ ] Formalize that exact result, wire its module, audit axioms and run the required targeted checks.

`update_plan` and `multi_tool_use.parallel` were not available in this runtime. This checklist is the durable task record; independent reads used awaited parallel tool calls.

## Corpus evidence and scope

The frontier map states RH remains open. An implication with an unproved RH-strength input is a receiver, not a producer.

Inspected sources:

- `RHTower/PrimeFaceBoundaryGauge.lean`: coefficientwise prime products trivialize the entire admitted boundary-graph family, jointly in the complex parameter. Its header explicitly does **not** assert that the domain forms a chain complex.
- `HTGeometry/TailQuotientSeparationLaw.lean`: finite-support observations cannot distinguish completion classes that erase those same supports.
- `HTGeometry/PrimeProfileInvariantInverseLimitOperationalTorsionUniversalityLaw.lean`: arbitrary intersections and uniform finite annihilators already have a precise corpus treatment.
- `RHTower/DeningerGeneralizedDivisorSupport.lean`: generalized-divisor support comparison is an explicit interface; it is not a source construction selecting Xi zeros.
- `xi-conductor-nearby-cycle-degeneration.md`: the source-first node/Legendre family, terminal multiplicity class, and vertical invariant-cycle comparison already exist. The missing ingredient is a global source-natural comparison, not another pointwise class.
- `rh-incompatible-arithmetic-ends/facts.md` and its card: prime-boundary monodromy, primitive-ray rearrangements, and scalar arithmetic completions were already screened. Merely naming another arithmetic end is not novelty.

Research searches were run directly through `scripts/formal_tools.py research`, including:

```
prime topology inverse limit divisor geometry
prime face iterated boundary square summable
prime zeta monodromy ramification
prime integral lattice inverse limit continuous period
```

Returned searches report no partial search execution, but semantic coverage is not measured and many compiler records are pending or stale. Search results are leads, not proof certificates or exhaustive novelty certification. Exact text searches supplemented them. No fresh compilation is claimed for any inspected corpus theorem.

## Candidate 1: completed prime faces

**Proposed mechanism:** iterating all prime-face boundary admissions might produce a new geometric distinction between parameters.

**Verdict: REDISCOVERED for the parameter distinction.** The existing gauge sends every admitted boundary row and its value to the zero-parameter version. Repeating equivariantly defined domain conditions does not remove this conjugacy.

There is also a separate well-definedness issue. On ordered vertices `v_0,v_1,...`, take the locally finite oriented ray `sum_n [v_n,v_(n+1)]`. Every vertex boundary row is finite. Its boundary is `-v_0`, and augmenting again gives `-1`. Thus rowwise summability and admission of successive boundaries alone do not prove that an augmented completed boundary squares to zero. The issue is the omitted end of the ray, not RH. This is a familiar locally finite homology/Fubini phenomenon; it is not claimed as new science or as an error in `PrimeFaceBoundaryGauge.lean`.

**Second pass:** retaining ends repairs the geometric bookkeeping, but supplies no arithmetic parameter selection. The prime gauge remains. No new positive salvage beyond existing gauge transport and established topology of ends was identified in this candidate.

## Candidate 2: prime-power ramification

**Proposed mechanism:** retain zero multiplicities through the ramification of the complete prime-power continuation tower.

**Verdict: REDISCOVERED at the proposed level.** The formula

`P(s) = sum_(n>=1) mu(n)/n * log(zeta(n*s))`

already describes prime-zeta continuation and its logarithmic branching. The corpus explicitly rejects recutting this as a new RH route (`3-formalized/new-object-candidates.md`), and already contains prime-zeta dilation fields and their limitations. Reconstructing the existing divisor through a new covering description does not constrain its location.

**Second pass:** labelled multiplicity and all dilation levels preserve more information than unlabelled support, but that information is already in the continuation formula. No novel arithmetic vanishing mechanism was obtained. This candidate is not promoted to a theorem or route.

## Candidate 3: infinite lattices with scalar readouts

A possible inverse-limit extension of the finite integral-lattice obstruction was considered. It was not pursued: its intended conclusion still rests on scalar action/eigen-character constraints, contrary to the user's restriction. No theorem or novelty claim was made.

## Candidate 4: double infinite Euler-deletion node geometry

**Question:** can all finite prime deletions, all ramification levels, and reflection together add a source constraint to the existing nodal degeneration?

The following exact calculation screens a natural version of this idea. It is a **BRIDGE**, not new scientific knowledge, and does not retire the general conductor route.

Let `S = {s in C : 0 < Re(s) < 1}` and let `xi(s)` be the completed source in the uncentered coordinate, with `xi(1-s)=xi(s)`. For a finite set of primes `F`, put

```
u_F(s) = product_(p in F) (1-p^(-s)),
N_F(s) = {(x,y) : xy = xi(s) u_F(s) u_F(1-s)}.
```

Each factor is nonvanishing on `S`. The exact change of coordinates

```
(x,y) -> (x/u_F(s), y/u_F(1-s))
```

identifies `N_F` with `N_empty`. Its inverse multiplies the two coordinates by the same factors. It commutes with reflection `(s,x,y) -> (1-s,y,x)` and with complex conjugation. Therefore the marked source parameter and reflection are retained, not discarded.

There is an all-root version. Every individual factor has a holomorphic logarithm `ell_p` on the simply connected strip, chosen by continuation of its real logarithm on the real interval. Define

```
r_(F,n)(s) = exp((sum_(p in F) ell_p(s))/n),  n >= 1.
```

Then `r_(F,n)^n=u_F`, disjoint prime sets multiply, and `r_(F,m)^(m/n)=r_(F,n)` whenever `n` divides `m`. On the root chart

```
(X*Y)^n = xi(s) u_F(s) u_F(1-s),
```

rescaling by `r_(F,n)(s)` and `r_(F,n)(1-s)` identifies it with `(X*Y)^n=xi(s)`. These maps commute with divisibility transitions between root levels. With prime-enlargement maps induced by these same compatible roots, they identify the entire prime-set/root-level diagram with the constant prime-set diagram of the undeleted root tower.

This is a statement about that specified diagram. It does not assert a limit of the numerical Euler products, does not identify a source-selected analytic completion with a categorical limit, and does not classify arbitrary extra gluing or source conditions. Iterated categorical limits preserve an existing diagram isomorphism; they cannot themselves undo it.

**Why this is not a discovery:** the mechanism is invariance of nodal charts under multiplication by units, together with coherent roots of units on a simply connected base. It does not meet the hgtl7 novelty gate. The actual Xi divisor was inserted into the defining equation, and the calculation yields no new law on that divisor. No Lean infrastructure should be added merely to rename this bridge.

**What remains live:** construct source geometry whose global arithmetic gluing is not exhausted by these invertible scalar transitions. Proving another local degeneration normal form, or adding more root/prime indices to this same diagram, does not address that requirement. The existing conductor card remains open and unchanged.

## External audit

Primary sources inspected or located:

- Connes–Consani, *Geometry of the arithmetic site*: <https://arxiv.org/abs/1502.05580>.
- Connes–Consani, *Geometry of the scaling site*: <https://arxiv.org/abs/1603.03191>.
- Connes–Consani, *Hochschild homology, trace map and zeta-cycles*: <https://arxiv.org/abs/2207.10419>, full HTML inspected. Its relevant constructions are spectral and therefore excluded from this research direction.
- Diestel–Spruessel, *On the homology of locally finite graphs*: <https://arxiv.org/abs/0910.5634>; author-hosted extended paper: <https://www.math.uni-hamburg.de/home/diestel/papers/HomologyExtended.pdf>. Established topology of ends is a parent theory, not evidence of a new RH mechanism.
- Hofmann–Morris, *The Structure of Abelian Pro-Lie Groups*: <https://sidneymorris.net/Morris134.pdf>. Adjacent background only; no pro-Lie result was imported as a proof of the proposed lattice claim.

The Fröberg prime-zeta result was located through existing corpus citations and secondary bibliographic leads; direct primary-text verification is still pending if that direction is revisited. A guessed DOI failed and was not used as evidence. Searches cannot establish absence from training data or certify worldwide novelty.

## Audit and next cycle

- **New scientific knowledge:** none certified this cycle. The admissible search space is narrower and several repeated constructions are rejected with exact reasons.
- **Rediscovery:** yes, especially prime faces and prime-zeta branching. Next cycle must start with the existing conductor comparison obstruction and the prior arithmetic-ends attack log.
- **Frontier movement:** no new RH producer or Lean theorem. Do not update the frontier map as though there were one.
- **Hard problem:** global arithmetic gluing that survives scalar trivialization, respects the user exclusions, and constrains the actual divisor. No exact new conjecture survives the present screen.
- **Next action:** examine existing non-scalar, source-level comparison data in the conductor and arithmetic-ends work before choosing a new geometric construction. Freeze the objects, morphisms, topology, and distinguished source before claiming a conjecture.

Lean phases were not begun because every screened candidate failed novelty, scope, or source-selection tests. This is not a completed hgtl7 research result. Goal remains active.

## 2026-10-06: user-supplied KLS paper and geometric suspension

User supplied Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*, [arXiv:2610.05474v1](https://arxiv.org/html/2610.05474v1). Read the introduction, criterion, and suspension proof, including equations (109)–(113). Section 7 encodes an observable in an additional coordinate of a larger object. This suggests a construction pattern; its analytic proof is excluded by the user's restrictions. No independent verification of the full KLS proof is claimed.

The cited Song–Zhang paper is [2610.01447](https://arxiv.org/abs/2610.01447). Its current v2 abstract itself claims a constant bound; the bibliography of the supplied v1 refers to the earlier title. Do not silently conflate these versions.

### Candidate 5: auxiliary coordinates repair the node's lost unit data

Freeze a connected complex domain `S`, a holomorphic function `f` not identically zero, and a holomorphic unit `u`. Two constructions must be distinguished.

**Multiplicative construction.** On any auxiliary-parameter domain where `V(s,w)` is a holomorphic unit, the family `xy=f(s)V(s,w)` is isomorphic over the full marked base `(s,w)` to `xy=f(s)` by `(x,y)->(x/V,y)`. Thus adding independent multiplicative observables does not repair the earlier gauge obstruction, even when those parameters are retained. Verdict: **FALSE** for this proposed repair; the calculation is a standard unit equivalence.

**Additive construction.** Put

```
X_f = {(s,w,x,y) : xy=f(s)+w},
pi_f : X_f -> S x C,  (s,w,x,y) |-> (s,w).
```

The fibre of `pi_f` is singular exactly when `w=-f(s)`. Indeed, for fixed `(s,w)` the derivatives of `xy-f(s)-w` with respect to `x,y` are `y,x`; the fibre contains `(0,0)` exactly at that value of `w`. Consequently an isomorphism of the families `pi_f` and `pi_g` over the identity of the marked base forces the discriminant graphs to agree, hence `f=g`. Conversely `f=g` gives the identity isomorphism. In particular `pi_f` and `pi_(uf)` are isomorphic over that fixed base only if `u=1`: first on the nonempty open set where `f` is nonzero, then everywhere by the identity theorem.

The underlying total space does not retain this distinction. The map

```
(s,x,y) |-> (s, xy-f(s), x, y)
```

is a biholomorphism `S x C^2 -> X_f`, with inverse forgetting `w`. Thus **the marked projection, not the total space, carries the missing data**. No estimate, positivity, or spectral input occurs in this calculation.

Positive survivor: a marked additive pencil recovers the full holomorphic source from its relative discriminant. Paper proof above is complete. Verdict: **BRIDGE**, not a novel RH theorem; this is elementary deformation/discriminant geometry, and inserting `f=xi` into the equation does not explain its zeros. The conductor route remains open, not retired. No routine Lean module added.

### Candidate 6: replace quantitative transfer by exact filtration transfer

The suggested next mechanism is an exact one: transport one *fixed* gluing obstruction into every stage of a separated filtration. For example, in `A[[t]]`, membership in every `t^r A[[t]]` implies zero because each coefficient vanishes. The difficult part is the arithmetic transport law, not this elementary receiver. A change of obstruction from `delta` to `t^r delta` is not such a law.

Two exact attacks delimit the proposed use of infinitely many suspensions.

**Rooting the obstruction can destroy separation.** Let

```
R = union_(n>=0) C[[t^(1/2^n)]],
m = {series in R with zero constant coefficient}.
```

These are nested rings under the usual squaring substitutions. Every nonzero `a` in `m` has the form `t^q b`, with positive dyadic rational `q` and a unit `b` in some stage. In a sufficiently large stage,

```
a = t^(q/2) * (t^(q/2) b),
```

and both factors lie in `m`. Therefore `m^2=m`, hence `m^r=m` for every positive integer `r`, while `t` is nonzero. The `m`-adic completion is exactly `C`; the completion map kills the whole nonzero ideal `m`.

There is an exact noncommutative version. In stable finite-support matrices write `e_ij(a)=1+a E_ij`. For distinct `i,j,k`, direct multiplication gives

```
[e_ik(b), e_kj(c)] = e_ij(bc),
```

where `[g,h]=g h g^(-1) h^(-1)`. Each generator with coefficient in `m` is a commutator of two such generators, by the factorization above. The group generated by these elementary matrices is therefore nontrivial and perfect. Iterating the factorization realizes a nonzero elementary defect through arbitrarily deep commutators. Depth alone does not annihilate it.

**Fixed-divisor survivor.** In the same ring, `intersection_r t^r R = 0`: a nonzero series has a first exponent, and cannot have every integer as a vanishing order. Thus the original divisor ideal `(t)` remains separated. Root factors such as `t^(1/2^n)` do not belong to `(t)` for `n>0`. One cannot replace this fixed ideal by `m` midway through the transfer argument. These are exact divisibility statements, not analytic bounds.

**Rooting a unit is different.** In characteristic zero, the formal substitution

```
T = (1+W)^n - 1
```

has linear coefficient `n`, which is invertible. Its inverse formal series is constructed recursively: the coefficient of degree `k` enters the degree-`k` equation multiplied by `n`, with all other terms already known from lower degrees. It therefore gives an isomorphism of formal power-series rings and preserves the order of the augmentation ideal. Taking a Kummer root of a unit near `1` does not raise that order. Taking a root of its vanishing coordinate is the ramified construction in the preceding example; the two operations cannot be interchanged.

Verdict: the naive inference from arbitrarily deep root/commutator presentations to vanishing is **FALSE**. The surviving fixed-divisor separation and unit-root distinction are **BRIDGES** from standard formal geometry, not certified new science. This does not close the arithmetic suspension construction problem.

### Source test and next proof obligation

Corpus search found the relevant existing source calculation in `RHTower/DeningerSteinbergKummerSuccessorNormalTransgression.lean`: the Steinberg ideal lies in the square of the augmentation ideal, while the normal selector extracts a first-order successor edge. Its source header explicitly warns that the selector lowers augmentation order. Read the header and definitions/lemmas at lines 390–525; do not treat source-index hits as a new compiled audit.

A purely algebraic version exposes the first obstruction without logarithmic size arguments. In `C[Q_(>0)^*]`, let `epsilon([q])=1`, let `I=ker(epsilon)`, and define the complex-linear map `lambda([q])=ord_3(q)`. Prime-exponent additivity gives

```
lambda(ab) = epsilon(a) lambda(b) + lambda(a) epsilon(b).
```

Thus `lambda(I^2)=0`, but `lambda([3/2]-1)=1`. The literal successor edge does not even lie in `I^2`. Multiplying it by auxiliary variables or changing to a nonseparated root ideal cannot establish a transfer theorem for that same edge. This is another standard augmentation calculation, not an RH obstruction theorem.

For this proposed repair, the source construction must retain the marked projection and account for this nonzero first normal class. An all-order identity cannot merely assert that the existing successor edge gains augmentation order. The next task is to construct the comparison object and its distinguished class from source data, then determine an exact suspension identity for that class. **No well-typed source transfer conjecture has yet been admitted:** the needed object/class construction is still being worked on. An unanswered construction is not grounds for abandoning the global gluing problem.

### Audit and execution record for this continuation

- Four corpus queries covered conductor-unit naturality, conjugate-pair residues, marked suspensions, and root/augmentation filtrations. Inspected `candidate_lemmas` and `source_arguments`. Results reported `partial:false`; semantic coverage was not measured, the background indexer was active, and most compiler entries were pending/stale/source-only. No absence or Lean applicability claim follows.
- Existing `PrimeSupportBoundaryJets.lean` already proves all-order support-cardinality recovery from a marked deformation. Existing `PrimeJetFormationTransport.lean` already has exact finite jet transport. Merely requesting more jets is not a new contribution.
- Existing `divisor-augmentation-nonproperness-law.md` records stronger failures of unmarked all-jet source observers. The new pencil test must keep its projection and source mark throughout.
- External parent check: [Stacks Project, valuation rings](https://stacks.math.columbia.edu/tag/00I8), including directed unions and valuations. The dyadic example and matrix identity above were proved directly; they are not attributed to an unread theorem.
- **Anti-theatre:** no new scientific theorem or RH premise discharge certified. Paper supplied a useful construction pattern, but the completed calculations are bridges and counterexamples to naive transfers. Do not promote them into the frontier map.
- **Anti-laziness:** explicit geometric and algebraic attacks were carried out; no numerical experiment was used. The hard task remains construction of source gluing with a faithful exact transfer. Continue there; do not substitute another survey or rename standard formal geometry as a new field.
- **Paper/Lean status:** screening calculations proved on paper above; novelty gate fails for those calculations. Research-level construction remains open, so no new Lean code, build, or claim of a completed hgtl7 result. Goal remains active.

## Continuation 2026-10-06: ramification before global comparison

The previous checkpoint produced screening evidence, not a source producer. Current source
inspection confirms that `XiThetaNodalConductorDegeneration` only maps the terminal jet into a
universal-node coefficient model; it does not identify this model with the pulled-back Legendre
local system. The parent conductor card must retain that distinction.

An exact admission test precedes the proposed global comparison: Legendre monodromy at parameter
zero is the square of the ordinary-node shear, and pullback through a source zero of order `m`
raises it to power `2*m`. Carlson--Müller-Stach--Peters, *Period Mappings and Period Domains*,
§1.1 (author-hosted second edition, p. 20), gives matrices `[[1,2],[0,1]]` and
`[[1,0],[-2,1]]`. This is classical geometry, not a novelty claim.

Working conjecture to test: the same conductor line exhausts the invariants after every
ramified pullback over arbitrary coefficient rings. Its exact coefficient test is
`ker(T^k-1) = {(a,b) : k*b=0}`. Nonzero coefficient torsion should refute unrestricted
exhaustion; the positive replacement should classify the entire additional invariant channel.
This correction concerns geometric admission, not horizontal Xi confinement.

- [x] Revalidate current conductor source and existing coefficient theorem.
- [x] Locate primary literature for the Legendre monodromy normalization.
- [x] Complete corpus collision audit and dependency-closed paper classification.
- [x] Formalize the exact replacement; targeted Lean/axiom checks and wiring pass; global lint fails outside this change.
- [x] Return to global arithmetic comparison with the corrected ramification data; admission test below.

No numerical experiment or new hypothesis is authorized by this test. The full RH goal remains
active. `update_plan` is unavailable; this checklist records the current plan.

### Next global comparison test: specify the transport domain

The universal Legendre family does not have a single globally preserved vanishing line:
its monodromies around zero and one have distinct fixed lines, by the matrices above. This
elementary parent-theory observation is not an assertion about the image of the Xi pullback
fundamental group. In particular, merely knowing that Xi takes the values zero and one would
not identify the two based monodromies in one chosen nearby basis.

An attempted shortcut through Lvovski, *On monodromy in families of elliptic curves over C*,
Corollary 4.5, fails admission: its conventions require an algebraic variety and algebraic
family. The Xi pullback is analytic, with no supplied algebraic realization or finite-component
generic-fibre theorem. Primary text checked:
<https://arxiv.org/html/1705.02129v5>, conventions and §§1,4.

Therefore the next comparison must specify its actual base/path groupoid and a source-defined
marked-cycle transport before invoking a global rank-one local system. The parent card's
pointwise invariant vector is insufficient for this. No irreducibility theorem about the
actual Xi pullback, no new zero restriction, and no global no-go are claimed by this screening.

### Verified checkpoint

The full coefficient classification and actual Xi multiplicity specialization are formalized
in `HTGeometry/RamifiedNodeConductor.lean` and `RHTower/XiThetaRamifiedConductor.lean`.
Both targeted `--old` leaf builds and both final `lake env lean` source checks passed;
all 17 declarations use only standard Lean foundations. Exact statements, global lint failures,
and evidence are in `../../../3-formalized/conductor-ramified-invariant-channel.md`.

This is a correction, not a novel producer or an RH proof. Next action: define and test the
actual source-marked transport domain required by the conductor comparison. No owned build
or search remains pending at this checkpoint. Goal remains active.

## Continuation: the existing oriented regulator and a marked critical-locus test

The previous turn counts as progress: the coefficient replacement is implemented and verified.
The current search found a stronger existing result that changes the next action.
`XiReducedConductorRoosRegulatorClassification.lean` already constructs
`canonicalXiOrientedConductorRoosRegulator` from the actual terminal cut holonomy.
`XiNodalConductorHolonomyNaturalityClassification.lean` proves the arithmetic/geometric
naturality square equivalent to RH. Constructing the two sides again would duplicate work.
An RH-equivalence does **not** refute its premise: the actual-source compatibility law remains
an open theorem to prove, not a falsified assertion.

Working test: can a critical-locus suspension provide an independently natural comparison
using the exact source cut family and canonical ambient geometry? Freeze the literal domain
`S={z in C : |Im z|<1}`, the source `D_x(z)=thetaCuspBoundaryReflectionDefect x z`, and
`W_x(z,t)=t D_x(z)` on `S × C`. Corpus theorem
`thetaCuspBoundaryReflectionDefect_eq` gives `D_x(z)=exp(i z x) XiC(z)` on exactly this domain.
No continuation outside that proved strip is assumed.

- [x] Inspect existing oriented regulator and exact naturality receiver.
- [x] Check source cut identity and its domain in Lean source.
- [x] Freeze complete suspension transport and attack geometric naturality.
- [x] Audit the proposed second comparison against primary vanishing-cycle results.
- [x] Record the exact survivor/open construction; formalize only a warranted new result.

This is a new test of the missing comparison, not an admitted RH route or a claimed new theorem.

### Exact construction and hostile test

Write `f=XiC`, `g_x(z)=exp(i z x)`, and retain the marked projection to `z`.
The globally defined, invertible holomorphic maps on `S × C`

```
H_x(z,t)=(z,g_x(z)^(-1)t),
H_x^(-1)(z,t)=(z,g_x(z)t)
```

satisfy `W_x o H_x=W_0`. This constructs a coherent source-cut comparison before choosing
zeros. Comparing any two cuts by `H_y o H_x^(-1)` obeys the composition law identically.
Its Jacobian determinant is `g_x^(-1)`, not a discrete sign. With the fixed ambient form
`Omega=dz wedge dt`, one has `H_x^*Omega=g_x^(-1)Omega`; using the moving form
`Omega_x=g_x Omega` instead makes `H_x^*Omega_x=Omega`. Moving the form therefore absorbs
the scalar; it does not prove an independent fixed-form conservation law.

This family does not create new critical support. Direct differentiation gives the critical
ideal

```
J_x=(g_x f, t g_x(f' + i x f))=(f,t f')=J_0.
```

Both inclusions use only that `g_x` is a unit: subtract `(i x t)` times the first generator
from the second, then divide by the unit. At a zero of multiplicity `m`, choose local coordinate
`w=z-rho`, write `f=w^m a(w)` with `a(0)!=0`, and use that `m a(w)+w a'(w)` is a unit.
The critical ideal is exactly `(w^m,t w^(m-1))`. For `m=1` it is `(w,t)`; for `m>1` its
reduced support contains the entire multiplier line above the zero. A proof using an isolated
critical point at every Xi zero would silently add simplicity.

**Corpus collision: REDISCOVERED / BRIDGE.** The generic multiplier construction, actual
holomorphic gradient/Hessian, and nonzero-family product already exist in
`LandauGinzburgConstraint.lean`, `LandauGinzburgHolomorphicCore.lean`, and
`LandauGinzburgNodeGerm.lean`. The intrinsic ideal including the source equation and all
derivations is already unit-invariant in
`SquarefreeVeroneseIdeal.derivationalCriticalIdeal_unit_mul`. For this multiplier potential,
the source equation lies in its Jacobian ideal since `W=t partial_t W`, so there is no gap
between that augmented ideal and the displayed critical ideal. No new corpus module is
justified by renaming this calculation.

### Does vanishing-cycle naturality remove the retained scalar?

Tested the proposed implication against Brav--Bussi--Dupont--Joyce--Szendroi,
*Symmetries and stabilization for sheaves of vanishing cycles*,
<https://arxiv.org/html/1211.3259v4>, Theorem 3.1 and §3.4. The theorem compares **two**
function-compatible maps whose restrictions to the critical scheme agree. Its sign controls
their **relative** differential. `H_x` is one compatible map; the identity map is not another
one unless `W_x=W_0`. Equality of the critical ideals does not supply that missing map.

An exact symbolic test separates the two statements. For arbitrary `c in C*`, let
`V_0(z,t)=zt`, `V_c(z,t)=czt`,
`P_c(z,t)=(z,t/c)`, and `Q_c(z,t)=(z/c,t)`.
Both maps identify `V_0` with `V_c`, both agree on the critical point, and both have determinant
`1/c`. Their relative determinant is one for every `c`; their individual determinants are
unrestricted. Thus this theorem cannot justify the proposed absolute-scalar inference.
Theorem 4.2 also retains the function on the third critical thickening; equality of the
underlying critical scheme alone does not meet its hypotheses.

**Verdict:** the absolute-scalar inference is **FALSE** as a general geometric principle;
the exact source-cut suspension is a **BRIDGE**. The positive comparison is the explicit
`H_x` with its retained Jacobian/ambient-form factor. It agrees with the corpus's already
constructed oriented regulator in preserving the obstruction. This does not refute the actual
Xi compatibility conjecture or retire the conductor route.

### Next exact question

An independent source construction must now supply the **second** comparison with the same
function and critical-scheme restriction, and prove its action on the fixed source mark.
Neither the identity map nor an arbitrarily renormalized ambient form supplies it. This is
the concrete construction problem for the next cycle. In particular, the existence of a
comparison or RH-equivalence is no reason to abandon it; what remains missing is the specified
second arithmetic map and its mark-preservation proof.

### The obvious second map: complete cut/reflection groupoid

The functional-equation reflection does provide another function-compatible map, but it moves
the marked zero. More generally, for `epsilon in {1,-1}` define the map from cut `x` to cut `y`

```
K_(x,y,epsilon)(z,t) = (epsilon*z, exp(i*z*(x-epsilon*y))*t).
```

Evenness of `XiC` gives `W_y o K_(x,y,epsilon)=W_x`. The exponent addition identity gives

```
K_(y,q,delta) o K_(x,y,epsilon)=K_(x,q,epsilon*delta).
```

This is a complete, coherent global comparison for the cut/reflection groupoid. It retains the
source multiplier and has no added source premise. Every closed word at the same cut with total
sign `+1` is the identity map. Total sign `-1` sends `z` to `-z`, so it does not fix a marked
nonzero zero. The corpus proves `XiC_zero_ne` in `XiHadamardFactorization.lean`, excluding a zero
at the sole fixed parameter zero.

Thus the source-cut gain is an **open-path comparison of frames**, not automatically monodromy
of a closed geometric loop. Identifying two different cuts while retaining their original
frames is extra gluing data. Taking another word in the same cut/reflection maps cannot provide
the required independent comparison. This is an exact classification of this specified
groupoid, not an impossibility theorem for arbitrary global arithmetic gluing.

**Next pivot:** retain the completed source and its marked projection, but obtain the second
map from genuinely different arithmetic incidence data, rather than the cut/reflection groupoid.
The existing successor/Steinberg first-normal obstruction is the next source-level admission
test. No claim that every source construction reduces to these maps is made.

### Verification and scope of this cycle

`/tmp/rh-source-suspension-audit.lean` verifies the actual strip-domain equivalence `transport`
and the exact source equality `suspension_transport`, using the existing literal theta boundary
identity. Final command `lake env lean /tmp/rh-source-suspension-audit.lean` exited zero;
`/tmp/rh-source-suspension-audit.log` reports only `propext`, `Classical.choice`, and `Quot.sound`
for both declarations. This scratch audit proves the equivalence and source equality. The
holomorphic/Jacobian calculation, critical-ideal classification, and complete cut/reflection
composition law above are paper proofs, not newly formalized Lean theorems.

No formal repository module was added: the multiplier suspension and unit-invariant critical
ideal are already in the corpus. Search coverage was reported non-partial, but compiler
freshness was mixed; source hits were inspected and were not treated as fresh Lean checks.
The new conclusion is a sharper construction obligation, not a new RH restriction: a second
comparison must arise outside the cut/reflection groupoid and must preserve the actual mark.
An RH-equivalent compatibility theorem remains open, not refuted. The goal remains active.

## Next cycle: classify the entire positive Steinberg quotient

The arithmetic-incidence audit found a stronger positive statement than the known individual
first-normal obstruction: all positive Steinberg relations generate exactly the square of
the **positive** augmentation ideal. A complete finite ring proof and collision audit are
recorded in `../../../3-formalized/positive-rational-steinberg-square-classification.md`.
The general rational character theorem and actual-source ideal equality are formalized.

The carrier distinction is essential. The corpus uses `C[Q^*]`, including the negative sign,
so the full augmentation square is strictly larger. The corrected quotient retains two sign
sectors and every prime tangent direction. This is an exact algebraic classification attempt,
not a new source-geometric compatibility proof. No energy, spectral, or estimate argument is
used. Completion cannot be credited with erasing the surviving first-order class by definition.

The targeted `--old` build compiled both new leaves; final `lake env lean` source checks passed
with empty logs. All nine public declarations pass the transitive axiom audit with only standard
Lean foundations. The strict inclusion in the full augmentation square is also proved, via the
explicit negative-scaling sign reader. Full verification and global lint status are on the card.

Assessment: the first cycle rediscovered the suspension machinery; the second proves a stronger
corpus classification. Neither discharges the actual Xi geometric compatibility law. Novelty
relative to literature remains unverified. Next action is the source-defined comparison carrying
the retained prime tangent class and sign sector, not another renaming of the static quotient.

## Next cycle: exact source Hochschild–cyclic comparison

The positive Steinberg ideal classification exposes a distinction between two actual source
readers. The coefficient-of-identity Kummer cyclic trace does not become the augmentation
reader after quotienting. New leaves `RHTower/SquareZeroUnitCyclicBoundary.lean` and
`RHTower/DeningerPositiveSteinbergCyclicComparison.lean` identify the canonical tensor-power
image of the existing multiplier normal K1 cycle in the Steinberg quotient.

That exact image is a cycle and is not a full degree-two Hochschild boundary: the descended
augmentation–Kummer detector reads the original nonzero value `m log(3/2)`. Yet the image lies
in the ordinary cyclic relation space, with an explicit finite boundary plus signed rotation.
No ordinary cyclic functional on this quotient can preserve the source normal period.

The positive survivor and killing boundary are both formalized, with no changed trace hidden
in the comparison. Neither negative cyclic homology nor relative cyclic degree zero is
asserted to vanish. The classical nilpotent Chern-character literature already distinguishes
these targets; scientific novelty remains unverified. Exact card:
`../../../3-formalized/positive-steinberg-hochschild-cyclic-comparison.md`.

Both targeted builds and final direct source checks passed; 37 public declarations have only
standard Lean foundations. Both leaves are wired. Global lint fails on six unrelated unwired
leaves listed on the card. No full or umbrella build, raised heartbeat limit, numerical
experiment, axiom, admission, or commit was used.

Assessment: verified source-interface progress, not a discharge of the Xi geometric comparison.
The surviving mark needs an actual source-defined geometric realization in an appropriate
Hochschild/relative/negative-cyclic object. RH remains open and the full goal stays active.


## Next cycle: two-prime projective real packets

The exact new receiver uses seven preselected marking sections: for each of `p=2,3`, the
four-power packet of `a_p(s)=exp((1/2-s)log p)`, with the shared zeroth section counted once.
Each packet may admit its own nonsingular generalized-circle equation. The complete
classification is `Re s=1/2 OR Im s=0`. Actual Xi zeros exclude the real branch, so the
universal packet condition is exactly equivalent to mathlib's RH statement.

New leaves `HTGeometry/FourPowerGeneralizedCircle.lean` and
`RHTower/XiTwoPrimeProjectiveRealPackets.lean` prove the full classification, including all
collisions and negative-real resonances. A four-node Vandermonde argument handles the
single packet; integer independence of `log 2` and `log 3` handles common resonances.
Every power marking is identified with the existing full Kummer group-ring character.
No descent of that character through the positive Steinberg quotient is claimed.

The paper identifies the circle equation with a projective anti-holomorphic involution
fixing the labelled marks. The graph/blowup construction fixes all sections before any
zero is selected. Nevertheless it does not construct those real forms. The exact polynomial
with roots `rho, conjugate(rho), 1-rho, 1-conjugate(rho)` rejects the shortcut from reflection
and conjugation symmetry alone. This is not a counterexample to Xi.

Hostile verdict: classical BRIDGE, no significant novelty certified and no RH premise
discharged. The existing divisor-gauge Ward identity already exposes an analogous
nonmetric receiver. The deep descent search supplied no applicable source producer; its
fiber-product/vector-bundle ingredient set left the required real structure unproved.
The current proper-family programme has a non-torsion section and exact global two-division
covers on paper, but local formal divisibility and meromorphic-pullback loss of global
non-divisibility remain explicit. The next useful work is the global arithmetic source
comparison, not another equivalent receiver.

Card: `../../../3-formalized/xi-two-prime-projective-real-packets.md`.
Both targeted builds and final direct-source checks passed; both leaves are wired. All 16
public declarations were audited and use only standard Lean foundations. The final source
logs are empty, and the guarded audit exited zero. Five obsolete scratch/check files were
removed. Global lint failed on nine unrelated unwired leaves plus an unrelated in-progress
admission; the exact snapshot is recorded on the card. RH remains open and the full goal
stays active. No source real-descent premise was discharged by this cycle.

## Global Xi Kummer transport — 2026-10-07, active

Selected the explicit gap in the Legendre source-section card: generic non-divisibility
in `C(q)` does not prove non-divisibility after the actual meromorphic Xi pullback.
Paper proof now on `../2-fully-proven/xi-global-kummer-parity-transport.md`.

For the global meromorphic plane field, Xi and all `1-n^(-s)*xi(s)`, integer labels `n>=2`,
have independent square classes. The finite-product proof uses an existing qualitative
real-axis growth theorem and a sign-separated exponential crossing, not numerical work.
New modules `HTGeometry/MeromorphicPlaneSquareRoot.lean` and
`RHTower/XiGlobalKummerSquareClasses.lean` both passed targeted builds and are wired.
Their axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
Final actual-source checks and lint/index remain pending.

Next formal checkpoint is finite/infinite persistence in the joint extension generated
by roots of `xi*(1-n^(-s)*xi)`, then actual source-point non-divisibility. Scratch:
`/tmp/rh-xi-global-kummer-tower.lean` (includes the tower, exponential square unit, and
reusable affine doubling identities under separate namespaces), log of the same stem.
The paper also supplies an explicit nowhere-vanishing unit representing the common
surviving class and a free double cover. None of these statements selects the real part
of a zero; RH remains open. No claim of a new general Kummer or reflection mechanism.

### Verification closure

Six new leaves now implement global square-root normalization, actual Xi square-class
independence, persistence through the infinite algebraic marked union, both affine
sections and their non-two-divisibility, literal Q=P+(0,0), and an explicit nonsquare
unit representative of the common surviving class. All six targeted builds and final
actual-source checks passed. All 112 public declarations have only standard foundations.
Imports and index are updated. Global lint failed only on 16 unrelated unwired leaves;
exact snapshot is on the stage-2 card. Exact degrees, complete halves fields, and
geometric unramification remain paper-proven formalization follow-ups.

Scientific audit: source-divisibility premise discharged, classical mechanism, novelty
not certified; no RH premise discharged. Next conjecture investigates the additional
translated-section class 1+n^(-s)*xi(s). A reflection-square factorization suggests
finite-order rigidity excludes its global square root; corpus and external audit ongoing.

### Exponential-translate rigidity — source implementation

Card: `../2-fully-proven/xi-exponential-translate-square-rigidity.md`.
Paper proof complete: every nonconstant real exponential translate Xi+c*exp(h*s)
is globally nonsquare. Three leaves now pass the targeted build and are wired.
Actual-source and 11-declaration axiom audits are running, followed by the marked
augmentation-class scratch. This addresses the additional lambda class in Q
rather than asserting its full halves field coincides with P. No RH premise discharged.

### Second division class verified in scratch

All three exponential-translate modules passed actual-source checks and their 11
axiom audits. New XiGlobalKummerAugmentation scratch passed empty, now promoted
and wired; its 17-declaration final audit is running. It proves lambda and Xi*lambda
nonsquare on the infinite marked union, with literal sourceLambda identification.
Next card: `xi-signed-factor-divisor-independence.md`. Existing positive Riemann
kernel supplies a candidate sharp boundary bound, which should separate all signed
integer factor divisors. Combining that separation with individual nonsquareness
and existing RootExistence would settle independence among all lambda labels.

### Exponential-translate cycle verification closure

All four targeted builds, actual-source checks, and 28 public-declaration axiom
audits passed. Index regenerated; global lint has 14 unrelated unwired leaves,
recorded exactly on the stage-2 card. Seven obsolete owned scratch files removed.
The actual two independent source classes are settled. Complete division fields
and degrees remain paper-level followups, and RH remains open. No new general
Kummer/Hadamard mechanism or significant novelty is certified.

Active next scratch: `/tmp/rh-xi-boundary-factor-divisors.lean`, sharp boundary
bound and equal-radius exponential-label zero separation. Root existence on C
then turns individual nonsquareness into odd divisors. Next card owns the plan.

### Signed-factor divisor independence: extraction checkpoint

Continued `xi-signed-factor-divisor-independence.md`. The exact boundary
representation and equal-radius exponential-label separation passed Lean.
The generic nonsquare-entire-to-odd-zero theorem and odd-order unit-multiplier
obstruction passed the corrected scratch check. Promoted those generic results
and signed-source zero separation into two new leaf modules; targeted build
pending, followed by the assembled finite signed-packet independence scratch.
No RH zero-location statement or complete halves-field theorem claimed.

### Signed-factor independence verification closure

Completed three leaves: `EntireOddDivisorSquareClass`,
`XiSignedFactorZeroSeparation`, and `XiSignedFactorSquareClasses`.
Targeted builds PASS, final actual-source checks PASS with empty diagnostics,
17/17 public axiom audits standard-only, imports wired, index PASS. Lint fails
only on five unrelated unwired HTGeometry leaves (ApertureConeCalculus,
ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal,
BoundaryCoronaCStarAlgebra); no global lint PASS claimed. Card moved to
`2-fully-proven/xi-signed-factor-divisor-independence.md`.

The exact global criterion is square iff the Xi exponent is even and both signed
label sets are empty; over the actual infinite marked field it is square iff the
Xi exponent is even and the positive-label set is empty. Thus all positive labels
survive independently. No RH zero-location conclusion follows. The completed
13 leaves in this continued chain now have 157 audited public declarations.

Next: `xi-legendre-complete-halving-criterion.md`. Generic sufficient halving
construction and coordinate iff are running in `/tmp/rh-legendre-halving-construction.lean`.
The paper proof handles all denominators and the sign selecting P rather than -P.
Existing quadratic-degree helpers were located for the subsequent field step.

### Complete halving criterion: source equivalences checked

Generic Legendre sufficiency and two-square iff pass scratch and targeted build
(`HTGeometry/LegendreHalvingCriterion`). Generic quadratic square kernel and
independent two-root degree four pass scratch and targeted build
(`HTGeometry/QuadraticAdjoinSquareKernel`). The actual arbitrary-extension
criteria pass scratch and are promoted as `RHTower/XiLegendreHalvingCriterion`:
P_n has a half iff Xi is square; Q_n iff Xi and lambda_n are square. All source
nonvanishing supplied, actual group doubling verified. Imports wired; final
actual-source and axioms still pending for these three new leaves.

Current owned foreground chain checks the finite-family generic degree scratch,
builds XiLegendreHalvingCriterion, then checks `/tmp/rh-xi-halving-fields.lean`
(minimal field objects and source degrees two/four). Card retains exact statuses.
Implementation notes: field maps need `map_div₀`, not group-only `map_div`;
unfold `sourceCurveOver` before rewriting the dependent Point halving iff;
use explicit hP arguments. Root field scalar-tower identity in degree proof is
definitional via `change`, whereas an uninstantiated simp lemma did not rewrite it.

Next scientific audit after the field task: test whether signed factors are units
on the critical strip, potentially trivializing these global division obstructions
on its analytic marked cover. This is an unproved follow-up idea, not a result;
would sharply distinguish global extraneous-divisor data from RH-local data.

### Minimal halving fields checked; joint finite source instantiation pending

Source arbitrary-extension criteria and generic quadratic/finite degree helpers
now pass their targeted builds. `/tmp/rh-xi-halving-fields.lean` passes cleanly:
actual minimal fields admitting original/translated halves have degrees 2/4.
Promoted to `XiLegendreHalvingFields.lean`, import wired, build underway followed
by `/tmp/rh-xi-joint-halving-fields.lean`. The latter defines Option-indexed
Xi/lambda radicals and the actual joint field, with degree 2^(|T|+1) and
minimality for nonempty finite T. No all-four-halves membership theorem is claimed.
Six-module final source/axiom/index/lint closure remains after the joint check.

### Finite joint minimal halving fields pass scratch

`XiLegendreJointHalvingFields.lean` now proves the actual joint field has degree
2^(|T|+1), and for nonempty T is least among intermediate fields admitting halves
of all Q_n for n in T. The corrected scratch is clean; all six new leaves are
promoted and wired. Foreground chain: sixth targeted build, six final actual-source
checks, then 40-public-declaration axiom audit. Logs use `/tmp/rh-...-20261007.log`;
master audit `/tmp/rh-legendre-halving-axioms.{lean,log}` and names `.txt`.
Final index/lint and cleanup remain after the chain. No all-four-halves coordinate
membership or RH zero-location theorem is claimed. Next queued scientific audit
is `0-backlog/xi-critical-strip-kummer-collapse.md` (sharp analytic base-change
classification; only a conjecture so far).

### Complete halving cycle audited; analytic-domain boundary selected

Six leaves, all target builds and final actual-source checks PASS. Public axiom
coverage 40/40, foundations only. Index PASS; lint fails eight unrelated unwired
leaves (listed on the closed halving card). Owned obsolete scratch removed.
Card moved to 2-fully-proven; exact main statements formal, no standalone all-four
coordinate-membership theorem. BRIDGE, not certified novelty or RH discharge.
Next active card xi-critical-strip-kummer-collapse records a complete paper
classification, classical source audit, and exact actual-domain scalar-extension
requirements. First formal step: sharp strip bound and genuine analytic roots.

### Analytic strip source roots and actual domain field pass scratch

Sharp |Xi|<=1/2 closed-strip bound and canonical exp(log(f)/2) roots of both
signed factors pass scratch for every n>=1. Promoted/wired XiCriticalStripFactorRoots;
target build running. Generic all-meromorphic connected-domain field and faithful
restriction from actual MeromorphicPlane pass scratch; promoted/wired
MeromorphicDomainField. Prepared XiCriticalStripField application proving Xi
still nonsquare from its odd-order strip zero, every signed factor square,
and every marked radicand in the same nontrivial class. No tensor splitting
or marked-field embedding/actual halving-on-component claim audited yet.
Next implementation mechanism: embed actual global marked field in the algebraic
closure of StripField using IsAlgClosed.lift; show its image lies in the single
quadratic Xi extension by root membership. This gives an actual analytic
compositum and source-halving instantiation before finite etale product counting.
The finite-tensor deep search completed nonpartial with full inventory; mostly
irrelevant candidates. Direct source found AdjoinRootTensorBaseChange and
mathlib Etale.Field, useful classical alternatives, not already proved target.

### Infinite analytic marked component checked; four-module final audits running

XiCriticalStripMarkedComponent scratch PASS, promoted/wired. Actual K-algebra
embedding of full Marked field into StripField(sqrt(Xi)); analytic compositum
exactly that quadratic field, degree2; all actual original/translated source
sections admit halves. Narrowed classical DecidableEq to component field in
promoted code. Current sole build/check chain session89242: target component,
all4 actual-source checks,53 named public axiom audits. Await result, index/lint,
cleanup owned scratches, update memory. Finite tensor-product splitting remains
unformalised and distinct from compositum result; card still1-in-progress.

### Finite splitting generic algebra advances

Four strip modules final audit closed:53/53 named axioms standard-only,
all4directsourcechecks empty, indexPASS; lint12 unrelated unwired leaves listed
on card. Scratchimplementations cleaned. QuadraticRootFieldEquiv (2theorems/defs)
and CommonQuadraticGenerators (1theorem) pass scratch and targeted builds,
promoted/wired. EtaleCommonQuadratic scratch passes after explicit adjoin
arguments and Nat.cast_id normalization; promoted/wired with unused existential
binder renamed. Session54166 now targetbuild EtaleCommonQuadratic then source
scratch /tmp/rh-xi-strip-finite-tensor.lean. This source defines actual finite
marked field, exact degree, literal tensor algebra, full scaled-root generators,
and targets product-count2^(card-1). No newcycle finalaudit yet.
Prepared next-paper mechanism for two deck actions: quadraticRootFieldEquiv at
r and -r followed by adjoin(-r)=adjoin(r) gives actual conjugation. On strip
component it fixes w_n (base factor-root) and negates v, sends phaseunit toinverse;
on global common-half field it fixes marked u_n but negates v and w_n=u_n/v,
sendsphaseunittoitsnegative. Separate bases must remain explicit.

### Finite tensor algebra and exact deck actions implemented

All three generic finite-splitting helpers, QuadraticRootConjugation, and
XiCriticalStripFiniteTensor pass targeted builds. Literal source tensor algebra
is a product of exactly2^(cardT-1) copies of the actual stripQuadraticField for
every nonemptyT. AlgebraMap elaboration ambiguity was removed by expressing
the defining relation as a tensor and using the canonical scalar-map identity.
XiKummerUnitRoots and XiKummerDeckActions also pass scratch/targeted builds.
Actual global common-half involution negates U_n; actual strip component
involution fixes w_n=image(u_n)/v, flips all marked roots, inverts U_n and its
squared original unit. A local inherited Module instance resolved typeclass
search without resource-limit changes. Final8-leaf audit remains pending.

Current sole Lean job12569 checks /tmp/rh-xi-strip-prime-coefficients.lean:
exact odd part U_n-sigmaU_n=2*i*beta_n*v, extracted coefficient=actual beta_n,
relative odd-part ratio=beta_n/beta_m. No claim that v is a uniformizer at a
multiple zero, nor that the coefficient satisfies an RH real-form condition.
After promotion/build, run all8 actual-source checks, named axioms, index/lint,
cleanup and memory. The first4 strip-module audits remain final; do not repeat.

Next exact descent card created: xi-marked-reflection-descent.md. Competing
conjectures: Xi functional reflection lifts to actual one-sidedMarked, or no
such lift exists because reflected radicands remain nonsquare. Paper mechanism
separates all original/reflected factor divisors using the strip-unit theorem.
Positive survivor: smallest paired completion, exact doubled Kummer ranks,
trivial intersection of the two one-sided fields, and involutive semilinear
root swap. Initial hybrid search partial/no hits; lexical plus direct source
finds fraction-field MeromorphicReflection and actual-carrier
MeromorphicPlaneTranslation (use latter's codiscrete proof pattern).
Prepared next-card-only scratch /tmp/rh-meromorphic-plane-reflection.lean;
not yet checked or promoted. Verdict BRIDGE; no scientific novelty certified.

### Strip cycle final-selected-source closure

All8 new targetbuilds and actual-sourcechecksPASS, all8logs empty.54/54named
axioms standard-only. Togetherwithfirst4leaves:12leaves107namedpublicdeclarations
audited. IndexPASS; final lint7unrelatedunwired leaves listedoncard. No global
lintPASS. Nineobsoleteownedscratchesremoved. Cardmovedto2-fully-proven because
universalpaperwordingforallcompatiblesignchoicesremainsapapercorollarywithout
separateformalwrapper; everyselectedsourceclaimincludingliteralfiniteproduct,
bothdeckactionsandprimecoefficientrecoveryisformal/audited. Nouniformizerclaim,
noveltycertificateorRHpremisedischarge. Memoriesupdated.

Nextcardactualcarrierreflectionpasses scratch/targetbuild; promoted/wired
HTGeometry/MeromorphicPlaneReflection, finalauditpending. Firstsourcefactor
scratchhasonlyalinear_combinationorientationerror(exp equality); corrected
he2-he1. The newsoleLeanchain rerunsreflectedfactorseparationthenpreparedgeneric
EntireOddFactorPackets. No otherownedjobs running. Pairedreflectioncompletion
positiveclosure remainsmandatorybefore anyno-goretirement.

### 2026-10-07 — Actual reflection obstruction and positive completion

`XiReflectedSquareClasses` now passes scratch and targeted build. Its no-lift
theorem excludes every ring homomorphism on the actual infinite original marked
field extending functional-equation reflection. The mixed packet criterion
checks all finite original/reflected twists, not a sampled set of labels.
`IndependentRadicalIntersections` passes scratch and targeted build: arbitrary
disjoint independent radical families intersect exactly in the base, by finite
support extraction and finite linear disjointness.

`XiPairedRadicalDegrees` and `MeromorphicDomainReflection` pass scratch and are
promoted/wired. Their targeted build is running in sole owned chain 9797, followed
by quadratic semilinear, invariant-embedding and exact source intersection
scratches. The final positive involution can be constructed from the actual
quadratic strip component: lift strip reflection while fixing its Xi root,
restrict to the embedded paired field, and transport to the actual global field.
Prepared source completion also proves minimality and unchanged quadratic strip
compositum. It remains unverified. No RH premise has been discharged; this is a
classical descent bridge with a precise source obstruction, not a novelty claim.

The exact paired completion now passes its scratch. All twelve leaves are
promoted/wired. Sole owned Lean chain 35844 builds
`XiPairedReflectionCompletion`, audits all 99 named public declarations, then
runs `lake env lean` on every actual source leaf. No final audit result is claimed
yet. The elaboration bottleneck in invariant-image induction was removed by a
subfield closure proof, with no resource-limit change.

Next candidate is the existing paper survivor
`ternary-fiber-degree-restriction.md`: the necessary power-of-three degree law
for rational parameters with all three correctly labeled integer fibers.
Its paper proof and classical Lucas parent audit are recorded; no Lean code has
yet been written. The exact finite-field converse does not assert rational-map
existence at every allowed degree or anything about the actual transcendental
Xi parameter. The primitive integer-relation corpus search 27197 finished with
partial results and complete file inventory, with compiler pending/stale entries.
The local `Finset.extract_gcd` API supplies the needed primitive normalization;
its exact scratch name verification remains queued behind the existing Lean chain.

The paired completion target build and all 99 public axiom audits have now
passed. The sole remaining owned Lean job is chain 35844 checking the twelve
actual source files. Final source status, index/lint and cleanup are pending.

### Reflection cycle closed — 2026-10-07

Card moved to `../../../5-failed/xi-marked-reflection-descent.md`: only the original
one-sided lift is retired. Its minimal paired completion is fully formalised,
including all nested finite relative degrees, exact infinite intersection,
involutive reflection, normalized root swaps, and quadratic strip compositum.
All twelve target builds and final actual-source checks pass; all 99 public
axiom closures use only standard Lean foundations. Wiring is unique for every
leaf, indexes are refreshed, and twelve obsolete proof scratches are removed.

Authoritative lint reports six unrelated unwired HTGeometry leaves:
ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra, LabeledCosineDescent.
No global lint pass is claimed. No RH premise is discharged and no scientific
novelty is certified. The full goal remains active.

The next active card is `ternary-fiber-degree-restriction.md`. The local API
scratch initially needed explicit universe levels on generic `have := @Name`
checks; those are corrected, and sole Lean chain 87641 is verifying them. No
new ternary proof module exists yet.

### Ternary rational degree cycle closed — 2026-10-07

The exact degree law is fully formalized: actual rational functions with three
complete integer fibers in residues 0,1,-1, positive degree and no fiber at
infinity have degree 3^e. Complex dependence, primitive integer descent and all
root multiplicities are derived. The F_3 converse classifies the complete
coefficient kernel; it does not assert characteristic-zero realizability.

Six HTGeometry leaves build and pass final actual-source checks with empty
logs. All 15 public axiom closures pass; every leaf is wired once. Index refresh
passes. Lint fails seven unrelated unwired leaves (two WeilConeBoundaryMobius
leaves and five Aperture/BoundaryCorona leaves), none owned by this cycle.
No global lint pass, new scientific novelty, or RH premise discharge is claimed.
The card moves to `../../../3-formalized/ternary-fiber-degree-restriction.md`.

The next card was `../../../3-formalized/xi-cubic-lift-strip-decay.md`. An exact paper argument
combines actual order-one growth, superlinear real-ray growth, uniform critical
strip decay, and Hardy odd zeros in both tails to exclude the actual entire
cubic lift. The finite-zero contradiction uses the existing subquadratic
rigidity theorem; no conjugation symmetry of a hypothetical lift is needed.
Use decay threshold 1/2 in the path argument. Corpus/primary parent audits are
recorded, verdict BRIDGE, no novelty certified.

The actual no-lift theorem now passes Lean and targeted build. Five leaves are
promoted and wired: `H:CubicStripSeparation`, `R:XiCubicLiftGrowth`,
`R:XiCubicStripNoLift`, `H:MeromorphicPlaneCubicRoot`, `R:XiCubicMeromorphic`.
The actual meromorphic no-root, irreducibility and dimension-three root algebra
are checked. The positive S3/splitting-degree-six closure is now complete in
three further leaves: `H:CubicGaloisGroup`, `R:XiCubicDiscriminant`,
`R:XiCubicGalois`. All eight targeted builds and final actual-source checks
pass with empty source logs; all 38 public axiom closures use standard
foundations only. All eight imports are unique. Index passes; lint reports six
unrelated unwired leaves, none owned by this cycle. All eight obsolete proof
scratches were removed after exact source comparison. The card moved to
`../../../3-formalized/xi-cubic-lift-strip-decay.md`.

The parent's fixed-cubic subproblem is discharged, with actual S3 as its
positive survivor. C1, joint monodromy and RH remain open. The next candidate
is `xi-joint-cubic-galois.md`: finite joint cubic Galois group S3^S.
Actual signed-factor independence supplies independent discriminant classes;
a sign-isolating conjugation argument gives the paper subgroup mechanism.
Corpus and primary-source checks are recorded on that card. The exact
nonempty discriminant-packet nonsquare theorem now passes Lean; promoted/wired
`R:XiCubicDiscriminantPackets`, targeted build running. Actual quadratic-stage
degree and generic S3 conjugation scratches are prepared but not yet verified.

Joint-cubic update: actual discriminant packets, quadratic stages of degree
2^|S|, S3 odd-conjugation, and the full-product subgroup theorem now pass
scratch checks and targeted builds. Five leaves are promoted/wired, including
the just-verified normal-extension radical-flip transport (its target build
pending). The remaining common-field root-permutation construction is active;
no full joint-S3 or RH conclusion is claimed yet. Evidence and next checks
remain on `xi-joint-cubic-galois.md`.

Joint-cubic cycle CLOSED: `../../../3-formalized/xi-joint-cubic-galois.md`.
Actual unconditional endpoints `RHTower.xiJointCubicGaloisEquiv` and
`xiJointCubic_splittingField_finrank` give S3^S and 6^|S| for every finite
packet, including empty. Ten target builds and final actual-source checks
pass; 59/59 named public axiom closures are standard-only; ten obsolete proof
scratches removed after exact source comparison. Index passes; lint has six
unrelated unwired leaves recorded on the card. BRIDGE, no novelty/RH/C1 claim.
Polynomial-left-factor cycle CLOSED:
`../../../3-formalized/xi-polynomial-left-factors.md`. Actual tilted Xi has only
degree-one polynomial left factors; every nonzero value occurs arbitrarily
far right. Seven target builds and final actual-source checks pass; 19/19
public axiom closures are standard-only. Imports unique, seven obsolete
proof scratches removed, index refreshed. Lint has six unrelated unwired
leaves recorded on card. BRIDGE; novelty unverified, C1 and RH remain open.
The decisive added input was the already formalized unconditional simple Xi
zero, located by corpus audit; it was not supplied as a premise.

Next research card: `../2-fully-proven/xi-finite-cover-monodromy.md`. Single-coordinate
profinite density is the candidate. Primary ancestry confirms the classical
entire-curve polynomial/Laurent reduction. General compact-curve and cover
extension machinery is not yet located in Lean. A dependency-closed Laurent
obstruction is now formalized on `../../../3-formalized/xi-laurent-left-factors.md`.
Two target builds, both actual-source checks, and both public axiom closures
pass. Imports unique, proof scratches removed, index refreshed. Lint remains
unclean only on six unrelated leaves (listed on child card).

The general finite-cover paper proof is closed using puncture completion,
removable extension, and compact-surface uniformization. Primary Beardon--Ng
proofs were inspected to remove a possible cofinite-image hidden assumption.
This also exposes relative algebraic closure of C(d_a) in global meromorphic
functions as the stronger algebraic formulation; general Lean reduction is
still outstanding. Polynomial pole removal is CLOSED in
`../../../3-formalized/xi-meromorphic-polynomial-lifts.md`: two wired leaves, both
targeted builds and actual-source checks passed, all five public axiom
closures standard-only. The entire representative preserves the original
meromorphic field element. Actual tilted Xi admits no nonlinear polynomial
left factor in that field. Lint lists ten unrelated unwired leaves, recorded
on the card. BRIDGE, no novelty or RH claim. Next card:
`../../../3-formalized/xi-rational-left-factors.md`, now CLOSED: five target builds,
five actual-source audits, twelve standard-only public axiom closures,
five unique imports, and five obsolete proof scratches removed. Exact endpoint
forces every coprime rational left factor of actual tilted Xi, all real tilts
and meromorphic inner functions, to have degree one. Verification artifact:
`/tmp/rh-xi-rational-verification.json`. Lint has six unrelated unwired leaves
recorded on card. BRIDGE, no novelty/RH/C1 conclusion.

Next hard candidate: `xi-logarithmic-islands-monodromy.md`. Arbitrarily large
inverse disks of log(d_a) far right would isolate each mark's zero-winding
kernel. In every finite quotient, finite generating packets plus normality
then recover the entire kernel; one actual simple Xi zero supplies diagonal
zero winding. This targets finite-quotient C1 for every finite mark packet.
Paper mechanism recorded, corpus and hostile external audit active, no new
Lean yet. Corpus already has exact digamma vertical minimum, a uniform
Stirling defect bound, opened arithmetic log derivative, and strip decay.
