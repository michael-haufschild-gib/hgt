# Route K prime-cycle trace-class relocation

- **ID:** `route-k-prime-cycle-trace-class-relocation`
- **Stage:** 5-failed / retired as an independent RH route
- **Type:** `RETIRED RH ROUTE` / positive finite-order survivor formalized
- **Source:** `rh-current-frontier-map.md`, Route K; positive survivor of the retired regular
  Clifford/full-source Hilbert subroute
- **Final verdict:** Exact quadratic and quartic incidence, cofinite RVM diagonal, Schatten-1
  source-cycle reserve, and cofinal nonzero holonomy are constructed unconditionally. Complete
  even-trace incidence is not a remaining K-specific mechanism: it factors through source Hankel
  positivity and canonically supplies Route P's compact Markov carrier, hence already proves RH
  before any determinant is formed. Route K is retired as an independent route; all-order carrier
  existence belongs to Route P.

## Original goal and final closure

Original goal was to construct the missing arithmetic part of Route K without enumerating the Xi
divisor and without renaming self-adjointness or a determinant identity as a source theorem.  Exact
finite-order construction is now closed through quartic.  The all-order condition has been proved
to factor through Route P and is retired here rather than relabelled as K progress.

Let `t_n` be the increasing smooth Riemann--von Mangoldt quantiles and let `p_n` be the `n`th
prime.  On the marked prime space `H_+=ell2({p_n})`, put

```text
Q_+ e_(p_n)=t_n^(-1)e_(p_n),
Q=Q_+ directSum (-Q_+).
```

The frozen conjecture is that completed Euler--Gamma data, before zero specialization, constructs
a self-adjoint trace-class `K_+` and `K=K_+ directSum (-K_+)` satisfying all clauses below.

1. **Source construction.** Every finite compression is defined from ordinary-prime/prime-power
   incidence and the archimedean completion, with no `gamma_n`, Xi-zero enumeration, Weil-positive
   metric, or target spectral ordering in its definition.
2. **Cofinal trace-ideal control.** Source finite-packet corrections form one compatible net which
   converges to `K_+` in trace norm.  Diagonal damping chosen after seeing a target kernel is
   excluded.
3. **Forced linear boundary.** The one-prime countercurrent agrees with the unit--double physical
   cancellation.  Its positive inverse-square remainder is treated only as a trace-class
   counterterm, never as the RH mechanism.
4. **Cycle faithfulness.** Nontrivial mixed prime--Gamma information survives in cofinal closed
   cycles of the off-diagonal correction.  Pair magnitudes or forest edges alone do not satisfy
   this clause.  Cycle holonomies must be fixed by the source and compatible under packet growth.
5. **Exact determinant incidence.** For `A=Q+K`,

   ```text
   det_2(I-zA)=XiC(z)/XiC(0)
   ```

   as entire functions, with the genus-one normalization fixed by the same source construction.

Since `A` is compact and self-adjoint, clause 5 forces every centered Xi zero to be real and proves
RH.  The hard problem is clauses 1--5 jointly.  Clause 5 in isolation is an exact RH consumer and
does not count as progress.

## Gates

- [x] 0 → 1 in-progress: unmatched route ownership proved; conjecture source-pure and falsifiable;
  diagonal, forest, gauge, target-fed, and finite-channel attacks recorded
- [x] no-go closure: strongest positive survivor—exact simultaneous quadratic/quartic admission
  with cofinite RVM diagonal and cofinal source holonomy—proved and formalized
- [x] ownership closure: complete even-trace incidence proved to imply source Hankel positivity,
  RH, and Route P's compact Markov representation before determinant formation
- [x] retirement: no unmatched K-specific RH pivot remains; full carrier existence transfers to P
- [ ] publication gate for positive survivor: standalone paper and complete priority audit

## Survivor ownership audit

The former Route K retirement was invalid because it listed survivors without assigning them.
Exact ownership is now:

| Survivor | Exact owner | Reason |
|---|---|---|
| singular/partial Hedenmalm boundary relation retaining every divided-zero mode | Route C1 | C1's open core is exactly a source-defined singular Burnol--Hedenmalm boundary-null completion with faithfulness, second-level retention, symmetry, and graph closure |
| uniform source-domain prime-normal sub-log-square estimate | Route N | N owns this estimate on the closed theta Grushin domain and full Jordan tower |
| restricted-Weil/prolate finite spectra and determinant convergence | Route O | O owns source-locked prolate comparison and finite-to-Xi spectral/determinant convergence |
| cohomological Frobenius determinant with cup/Hodge positivity | Route L | L requires the actual arithmetic complex, Lefschetz comparison, and positive Hodge polarization |
| compact positive moment/Markov carrier | Route P | P owns source construction of the unique positive compact carrier |
| finite-order prime-indexed RVM relocation with marked cycle provenance | **Route K positive survivor** | exact through quartic; retained as a source-incidence theorem, not an open RH route |
| complete reflected trace-energy tower / compact positive carrier | **Route P** | `(K22)` turns every source-Hankel test into an operator square and yields P's compact Markov endpoint before determinants |

This mapping is structural, not verbal.  A prolate-derived `K` becomes Route O; a cohomological `K`
becomes Route L.  Marked-prime RVM/cycle structure remains K's finite-order positive survivor.
Complete moment realization is Route P by the formal all-order factorization, so it no longer
keeps K open.

## Internal state of the art

The corpus already proves the positive normal form:

```text
exact compact Hilbert--Polya realization
  -> Q plus self-adjoint trace-class relocation K,
det_2(I-z(Q+K))=XiC(z)/XiC(0) remains the source incidence.
```

It also proves the attacks which make a more generic statement theatre.

1. Any countable Hermitian kernel can be made trace class by a positive diagonal gauge while
   preserving every finite inertia certificate.  Trace-classness alone has no arithmetic content.
2. The unit--double/physical cancellation is coefficientwise in every real module.  Its positive
   summable remainder is support-blind and cannot encode cross-prime response saturation.
3. A diagonal Hilbert--Carleman response has zero linear term, one-signed quadratic resolvent, and
   no divisor.  It exposes a prime-square correlation but not global orientation.
4. Exact phase-natural source transports on finite prime-power packets are diagonal; a nonidentity
   source-faithful transport must develop an explicit off-diagonal phase-connection defect.
5. Finite-rank theta coupling loses Xi phase through `|XiC|^2`; finite-channel local first-order
   models are pure gauge or finite unions of arithmetic lattices.

Therefore the first honest K object is not “some trace-class `K`.”  It is an infinite-rank,
source-gauged, cycle-bearing correction with a cofinal determinant identity.

## Scalar trace targets are already source-defined

The infinite problem is **not** to guess Xi's regularized-determinant coefficients.  Existing
unconditional corpus theorems define, before any operator construction,

```text
M_m^src = analyticTraceMoments
  (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) m.
```

`xi_completeCenteredReciprocalLaurentParitySourceUniversality` proves for every `m>=0`, with exact
Xi divisor multiplicity,

```text
sum_rho mu_rho^(-(2m+3)) = 0,
sum_rho mu_rho^(-(2m+2)) = M_m^src,                    (S1)
```

where `mu_rho` is the centered Xi spectral coordinate.  The left sides are zero-indexed target
descriptions, but the right side of the even identity is the completed prime--Gamma source germ.
The Route K construction must use the right side, never the divisor sum, to define or tune entries.

Consequently a successful `A=Q+K` must prove the operatorial lift

```text
Tr(A^(2m+3))=0,
Tr(A^(2m+2))=M_m^src                                  (S2)
```

for every `m`.  The final factorization theorem below proves that `(S2)` already makes every
source-Hankel polynomial square a Hilbert--Schmidt squared norm.  It therefore proves RH and
constructs Route P's compact Markov carrier before a determinant is formed.  Thus global
determinant recovery is downstream, not an independent K pivot.  Finite-order marked-prime
incidence remains meaningful positive structure; complete incidence belongs to P.

## New finite-packet boundary theorem `[PROVED HERE] [LEAN]`

For three positive reciprocal skeleton values `q_0,q_1,q_2` and real edge corrections
`x_01,x_12,x_20`, let

```text
A = [q_0  x_01 x_20;
     x_01 q_1  x_12;
     x_20 x_12 q_2].
```

Direct determinant expansion gives

```text
det(wI-A)
= (w-q_0)((w-q_1)(w-q_2)-x_12^2)
  -x_01^2(w-q_2)-x_20^2(w-q_1)
  -2 x_01 x_12 x_20.                                  (K1)
```

Thus every proper forest term depends only on edge squares.  Flipping one edge changes the
characteristic function by exactly `-4 x_01 x_12 x_20`.  The only sign-sensitive term is the
closed-cycle holonomy.

Centered Xi is even, so the positive sector must be paired with its negative.  Put

```text
D_x(w)=det(wI-A_x) det(-wI-A_x).
```

If `x'` flips `x_01`, then

```text
D_x(w)-D_x'(w)
= -8 x_01 x_12 x_20
   (-(q_0+q_1+q_2)w^2-q_0q_1q_2
      +q_0x_12^2+q_1x_20^2+q_2x_01^2).                (K2)
```

If the cycle product vanishes, both unpaired and paired determinants are flip-blind.  If every
`q_i>0` and every edge is nonzero, `(K2)` is nonzero at `w=0` or `w=1`: if the constant bracket is
nonzero, use `w=0`; if it vanishes, `w=1` leaves the nonzero coefficient
`-(q_0+q_1+q_2)`.  Therefore Xi reflection pairing does **not** erase source cycle orientation on a
positive RVM background.

Lean module:
`formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCycleRelocation.lean`.

Headline declarations:

```text
routeKThreePrimeCharacteristic_eq
routeKThreePrimeCharacteristic_sub_edgeFlip
routeKThreePrimePairedCharacteristic_sub_edgeFlip
routeKThreePrimeCharacteristic_edgeFlip_eq_of_cycle_eq_zero
routeKThreePrimePairedCharacteristic_edgeFlip_eq_of_cycle_eq_zero
exists_routeKThreePrimePairedCharacteristic_ne_edgeFlip
```

## General switching and trace-cumulant boundary `[PROVED HERE] [LEAN]`

The triangle computation is not a three-label accident.  Let `G` be any finite connected support
graph, `A` a real matrix with off-diagonal support in `G`, and `c` a symmetric Boolean edge-sign
field.  If every finite closed walk has trivial XOR holonomy, corpus flatness gives a vertex sign
field `epsilon` with

```text
c(i,j)=epsilon(i) XOR epsilon(j).
```

Writing `S=diag((-1)^epsilon(i))`, the edge-twisted packet is exactly `SAS`.  Since `S^2=I`,

```text
det(wI-SAS)=det(wI-A)                                  (K3)
```

for every real `w`; the product at `w` and `-w` is equally blind.  Thus every closed-walk-flat
sign repair, not only a three-vertex forest, is determinant gauge.  Nontrivial cycle holonomy is a
necessary finite orientation coordinate.

The trace cumulants sharpen what survives `det_2` regularization and Xi reflection.  For the
three-prime packet, let `T_m(x)=Tr(A_x^m)` and let

```text
T_m^pair(x)=T_m(q,x)+T_m(-q,-x).
```

Exact expansion gives

```text
T_2(x)=T_2(x'),
T_3(x)-T_3(x')=12 x_01 x_12 x_20,
T_4(x)-T_4(x')=16(q_0+q_1+q_2)x_01x_12x_20,           (K4)

T_3^pair(x)=0,
T_4^pair(x)-T_4^pair(x')
  =32(q_0+q_1+q_2)x_01x_12x_20.                       (K5)
```

Therefore the quadratic `det_2` cumulant is sign-blind; the cubic triangle cumulant is killed by
the required centered reflection; and quartic is the first surviving paired cycle cumulant.  On a
positive RVM diagonal with three nonzero edges, `(K5)` is nonzero unconditionally.  The infinite
source identity must consequently begin by matching reflection-even closed walks at order four,
not by fitting diagonal mass or pair squares.

Lean module:
`formal/GaloisForLFunctions/RHTower/XiPrimeMarkedCycleGauge.lean`.

Formalized theorem card:
`../3-formalized/not_new_scientific_knowledge/route-k-prime-cycle-reflection-paired-determinant-law.md`.

## Completed physical-endpoint RVM relocation `[CONSTRUCTED GLOBALLY] [LEAN]`

Write `S(s)=seamFluxCochain(s)=-xi'(s)/xi(s)`.  Correct physical orientation and the
valuation-resolved endpoint correction give

```text
K_phys(t) = S(1+it)-2S(2+it)+Delta_val(t),
kappa(t)  = Re((K_phys(t)+K_phys(-t))/2),

B(p,q) = (log p/p)(log q/q) kappa(log p-log q).        (K6)
```

This replaces the stale coarse-minus-fine sign formerly printed here.  `Delta_val` is an
absolutely convergent prime-by-valuation Fourier series and defines a self-adjoint Schatten-1
operator.  The primitive ordinary-prime boundary still has divergent absolute nuclear budget
`sum_p log(p)/p`; cancellation must precede trace norm.  Nevertheless the **completed**
source-defined matrix `B` is unconditionally Hilbert--Schmidt: boundary zero-freeness and explicit
zeta/digamma control give a polynomial vertical bound, while the two physical endpoint weights
absorb it in `ell2(primes x primes)`.

Let `t_n` be the unique smooth Riemann--von Mangoldt quantile and put

```text
q(p_n)=t_n^(-1),                 Q e_(p_n)=q(p_n)e_(p_n),
K_RVM=[Q,[Q,B]].                                      (K7)
```

The quantiles are positive and injective and `sum_n t_n^(-2)<infinity`, so `Q` is self-adjoint
Hilbert--Schmidt.  The double commutator is a source-defined self-adjoint Schatten-1 operator with
exact marked-prime entries

```text
<e_p,K_RVM e_q>=(q(p)-q(q))^2 B(p,q).                 (K8)
```

Thus no packet-dependent row balancing or diagonal shell renormalization is needed.  The old
finite row-balanced completion remains a useful obstruction:

```text
C_P(p,q)=R(p,q)                                         if p!=q,
C_P(p,p)=j(p)-sum_(r in P\{p}) R(p,r),                 (K9)
```

where `j(p)` is the fused unit--double current.  Its off-diagonal entries are compression
compatible, but its diagonal is not.  If `r notin P` and `p in P`, then

```text
C_(P union {r})(p,p)-C_P(p,p)=-R(p,r),                 (K10)

sum_(p in P) |C_(P union {r})(p,p)-C_P(p,p)|
  =sum_(p in P)|R(p,r)|.                               (K11)
```

Thus naive finite balancing is not a projective compression system.  Double-commutator relocation
is the exact source-side replacement: it performs cancellation at bounded-operator level and lands
in Schatten-1 before any finite compression.

The remaining nonvanishing problem is also closed.  Positive local stiffness gives
`kappa(0)>0`; continuity makes `kappa` positive on a zero neighborhood.  Euler divergence
`sum_p 1/p=infinity` forces, beyond every prime index, three consecutive primes with both adjacent
log gaps arbitrarily small: otherwise every two-gap block would contain a fixed positive gap,
forcing two-step geometric prime growth and convergence of the reciprocal-prime series.  Hence
cofinally

```text
B(p_n,p_(n+1)) B(p_(n+1),p_(n+2)) B(p_(n+2),p_n) > 0. (K12)
```

Injectivity of `q` preserves these triangles under `(K8)`.  Their centered-reflection quartic
edge-flip signal is nonzero cofinally, so the construction retains determinant-visible source
orientation at the first even order.

Finally, `K_RVM` has exactly zero marked-prime diagonal and is Hilbert--Schmidt-orthogonal to `Q`.
Therefore

```text
||Q+K_RVM||_HS^2 = ||Q||_HS^2 + ||K_RVM||_HS^2
                  > ||Q||_HS^2.                       (K13)
```

This is the sharp quadratic admission constraint for the raw fixed-head candidate.

It is not the sharp constraint for Route K itself.  Put

```text
M_0^src=analyticTraceMoments
  (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0 > 0.
```

Reciprocal-RVM square summability gives a finite source-selected prime set `F` with
`||Q_(F^c)||_HS^2<M_0^src/2`.  There is then a unique positive

```text
c_F^2 =
  (M_0^src/2-||Q_(F^c)||_HS^2) / ||Q_F+K_RVM||_HS^2
```

and the asymptotically locked operator

```text
A_F=c_F(Q_F+K_RVM)+Q_(F^c)                         (K14)
```

satisfies

```text
2||A_F||_HS^2=M_0^src.                              (K15)
```

This is not global spectral rescaling: outside `F`, the diagonal is exactly the original
reciprocal smooth-RVM skeleton.  Every off-diagonal source edge is multiplied by the same positive
`c_F`, so cofinal triangle holonomy and the reflection-even quartic edge-flip signal survive.
Thus degree-two source incidence is closed without changing RVM asymptotics.

The quartic target also passes its first unconditional feasibility audit.  Existing certified
rational bounds imply

```text
0 < M_1^src < 1/5000,
1/25 < M_0^src,
```

and hence

```text
0 < M_1^src < (M_0^src)^2/2.                         (K16)
```

Formula `(K16)` is the strict interior of the universal reflected self-adjoint two-moment purity
cone.  This strict margin supports exact simultaneous admission, not merely a feasibility check.

## Exact quadratic/quartic admission `[PROVED HERE] [LEAN]`

Put

```text
A=M_0^src/2,  B=M_1^src/2,  g=A^2-B>0.
```

Choose an explicit positive control radius `eta` smaller than `A`, with
`2 A eta < g` and `eta^2 < B/2`.  Cofinal square summability selects an arbitrarily late initial
prime cut `N` whose exact RVM tail `D_N` has energy below `eta/4`.  On disjoint source-positive
triangles beyond the same cut, normalize the actual completed-endpoint RVM edges by a geometric
block factor.  Their sum `C_N` is self-adjoint Schatten-1, has exactly zero diagonal, annihilates
the first `N` prime basis vectors, and has nonzero holonomy on every selected block.  A positive
scale `delta` makes `delta C_N` have energy below `eta/4`.  Hence

```text
R_N = D_N + delta C_N,
e   = ||R_N||_HS^2 < eta,
f   = ||R_N^2||_HS^2 <= e^2.                         (K17)
```

The residual pair `E=A-e`, `F=B-f` satisfies the strict finite atomic cone

```text
E>0,   E^2/N < F < E^2.                              (K18)
```

The inequalities are symbolic consequences of `(K16)--(K17)`; no moment or cutoff is evaluated.
One large and `N-1` equal nonnegative atoms then realize exactly

```text
sum a_i^2=E,    sum a_i^4=F.                         (K19)
```

Place their square roots on the first `N` marked-prime basis vectors to obtain a positive
finite-rank diagonal operator `H_N`.  Head and reserve have disjoint invariant supports, so

```text
H_N R_N=R_N H_N=0,
||H_N+R_N||_HS^2=A,
||(H_N+R_N)^2||_HS^2=B.                              (K20)
```

For `T=H_N+R_N`, centered reflection therefore has exact source traces at degrees two and four:

```text
2 Tr(T^2)=M_0^src,
2 Tr(T^4)=M_1^src.                                   (K21)
```

Outside the first `N` primes the diagonal of `T` is exactly the reciprocal smooth-RVM skeleton.
Every selected late triangle edge equals `delta` times its normalized actual source edge, so
cofinal holonomy is nonzero.  This simultaneously closes quartic incidence, RVM-tail fidelity,
trace-ideal control of the correction, and cycle survival.

## All-order factorization and ownership transfer `[PROVED HERE] [LEAN]`

For any self-adjoint Hilbert--Schmidt operator `T`, define

```text
m_n(T)=||T^(n+1)||_HS^2.
```

For every real polynomial `p(X)=sum_i c_i X^i`, form the finite odd-power probe

```text
P_p(T)=sum_i c_i T^(2i+1).
```

Self-adjointness and trace cyclicity give the exact Gram law

```text
<T^(2i+1),T^(2j+1)>_HS
  = ||T^(i+j+1)||_HS^2,
```

hence

```text
sum_(i,j) c_i c_j m_(i+j)(T)=||P_p(T)||_HS^2>=0.     (K22)
```

Therefore any complete reflected incidence

```text
2||T^(n+1)||_HS^2=M_n^src  for every n               (K23)
```

places the entire normalized prime--archimedean source sequence in its trace-Hankel-positive cone.
Existing exact source-Hankel equivalence then proves RH.  Existing compact Markov equivalence
canonically produces `PrimeArchCompactMarkovGermRepresentation`, Route P's endpoint.  No Fredholm
determinant hypothesis is used.

This is the decisive ownership theorem.  Finite-order marked-prime cycle carriers are genuine
positive survivors, with `(K21)` the first nontrivial exact case.  But extending them to all orders
is exactly a producer for Route P's compact positive moment carrier.  The global centered-Xi
determinant is then downstream of RH and moment determinacy, not an unmatched Route K problem.
Route K is therefore retired as an independent RH route.

Lean modules:

```text
XiPrimeMarkedPhysicalEndpointBoundaryNuclearObstruction.lean
XiPrimeMarkedPhysicalEndpointBoundaryGrowth.lean
XiPrimeMarkedPhysicalEndpointHilbertSchmidt.lean
SchattenDoubleCommutatorRelocation.lean
PrimeLogTripleCluster.lean
XiPrimeMarkedPhysicalEndpointCofinalHolonomy.lean
XiPrimeMarkedPhysicalEndpointRVMRelocation.lean
XiPrimeMarkedPhysicalEndpointRVMQuadraticIncidence.lean
XiPrimeMarkedCofinalTriangleNuclearCarrier.lean
FiniteTwoLevelMomentCarrier.lean
XiPrimeMarkedFiniteTwoLevelDiagonalCarrier.lean
XiPrimeMarkedCofiniteRVMQuarticReserve.lean
XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence.lean
XiPrimeMarkedAllOrderIncidenceFactorization.lean
```

## Heavy-conjecture / hostile-attack ledger

### K4.1 — diagonal positive trace-class remainder

**Conjecture.** Put the unit--double inverse-square remainder directly on the RVM diagonal and use
its determinant.

**Attack.** The cancellation is support-blind before any Hilbert structure.  Diagonal `det_2`
regularization is zero-free in the local exponential model and one-signed at quadratic order.  It
does not retain prime phases or produce the Xi divisor.

**Verdict:** `FALSIFIED AS SOURCE PRODUCER`.  Linear counterterm retained as clause 3.

### K4.2 — pairwise off-diagonal lift without cycles

**Conjecture.** Add mixed prime-pair edges whose magnitudes match the true aperture response.

**Attack.** Formula `(K3)` proves the stronger all-packet statement: every symmetric edge-sign
field with trivial closed-walk holonomy is a diagonal switching gauge, so both unpaired and
reflection-paired determinants are identical.  Formula `(K1)` supplies the minimal nonflat witness.

**Verdict:** `FALSIFIED AS PHASE-FAITHFUL DETERMINANT`.  Positive survivor is cycle holonomy.

### K4.3 — reflection pairing kills cycle orientation

**Conjecture.** Evenness of centered Xi makes all odd cycle information irrelevant.

**Attack.** Formula `(K2)` disproves this on the nonzero positive RVM diagonal.  More sharply,
`(K4)--(K5)` show that reflection kills the cubic trace holonomy but moves the same source datum to
the quartic cumulant, weighted by the positive diagonal sum.

**Verdict:** `FALSIFIED`; unconditional positive paired-cycle law formalized.

### K4.4 — abstract realization of the source moment tower

**Conjecture.** Feed the already constructed scalar sequence `M_m^src` into a compact moment or
spectral theorem and call the resulting self-adjoint operator Route K.

**Attack.** A positive compact carrier for the source moments is Route P's exact primitive.
Moreover, the self-adjoint moment positivity needed by an abstract realization is already an
RH-bearing condition, while choosing matrix entries from a target spectral measure violates Route
K's marked-prime source clause.  It supplies neither prime labels nor finite-packet cycle incidence.

**Verdict:** `MAPS TO ROUTE P / TARGET-FED AS A K CONSTRUCTION`.  Scalar target tower retained;
abstract carrier rejected as Route K progress.

### K4.5 — cofinal prime--Gamma cycle relocation

**Conjecture.** The corrected completed endpoint kernel admits an unconditional cofinal
trace-class relocation retaining nonzero cycle holonomy.

**Attack.** Direct nuclear expansion fails sharply at the primitive boundary.  Moving cancellation
before trace norm and applying the canonical second commutator `(K7)` succeeds: `K_RVM` is
self-adjoint Schatten-1, its exact source matrix is `(K8)`, nonzero triangles occur cofinally by
Euler divergence plus local stiffness, and the first reflection-even quartic signal survives.

**Verdict:** `PROVED ON PAPER AND IN LEAN`.

### K4.6 — exact centered-Xi incidence for the constructed relocation

**Frozen conjecture.** Put `A_+=Q+K_RVM`, `A=A_+ directSum (-A_+)`, and prove

```text
det_2(I-zA)=XiC(z)/XiC(0)
```

from completed Euler--Gamma incidence, without using the Xi divisor.

**Attack.** The raw fixed head has the rigid energy `(K13)`, but finite-head/cofinite-tail
orthogonal absorption removes that artifact.  Equations `(K17)--(K21)` construct one operator
matching degrees two and four exactly while preserving the exact cofinite RVM diagonal and
positive cofinal cycle holonomy.

At all orders, `(K22)` proves more: complete reflected trace incidence makes every source-Hankel
test a Hilbert--Schmidt square.  It implies RH and Route P's compact Markov representation before
the determinant is formed.  Thus all-order incidence/global determinant is not a residual
K-specific producer.

**Verdict:** `QUADRATIC/QUARTIC PROVED; ALL-ORDER MAPS EXACTLY TO ROUTE P; ROUTE K RETIRED`.

## External primary-source boundary (1 August 2026)

- Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, constructs the
  theta second-order eigenproblem and pair-self-adjointness framework, not a marked-prime
  trace-class RVM relocation.
- Suzuki, *A canonical system of differential equations arising from the Riemann zeta-function*,
  arXiv:1204.1827, constructs canonical systems unconditionally only away from the critical
  parameter boundary and leaves the all-parameter positive Hamiltonian problem open.
- Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
  arXiv:2206.03682, gives RH-equivalent positivity/moment/string criteria, not this source operator.
- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423, develops
  the semilocal prolate operator and Sonin spaces; its primitive and open finite-to-global limit
  are Route O, not the RVM relocation above.
- Berg--Szwarc, *Self-adjoint operators associated with Hankel moment matrices*, arXiv:2105.07252,
  treats general closed Hankel moment forms; it makes `(K22)` a structural moment-operator
  factorization rather than an independent novelty claim.
- Mädler--Schmüdgen, *On the Truncated Matricial Moment Problem. I*, arXiv:2310.00957, proves
  general finite atomic representation; the two-level moment head is therefore an elementary
  ingredient, not the source-specific contribution.
- Bownik--Jasper, *The Schur-Horn theorem for operators with finite spectrum*, arXiv:1302.4757,
  and *Diagonals of self-adjoint operators I: compact operators*, arXiv:2212.08182, characterize
  self-adjoint diagonals but do not combine a prescribed cofinite RVM diagonal with exact
  prime--archimedean moments and cofinal source holonomy.
- Krein spectral-shift and perturbation-determinant theory supplies the parent trace-class
  language but no ordinary-prime source formula or Xi determinant identity.

No exact-match source was found.  This is noncollision evidence, not a priority claim.

## Lean and infrastructure boundary

The marked-prime Hilbert space, smooth reciprocal RVM skeleton, completed endpoint operator,
Schatten-1 relocation, cofinal nonzero cycle coordinates, first reflection-even quartic signal,
finite-head/cofinite-tail split, exact quadratic/quartic source incidence, zero diagonal of the
cycle carrier, disjoint-support moment additivity, and the all-order Hankel factorization are
dependency-closed and formalized unconditionally.  The positive survivor is exact through quartic.
Complete incidence is recorded under Route P's compact carrier problem.  No unmatched K pivot
remains.

Formalized positive-survivor record:
`../3-formalized/new_scientific_knowledge/route-k-exact-quartic-incidence-all-order-factorization.md`.

## Log

- 2026-08-01 — Route K reopened after survivor-ownership audit invalidated blanket retirement.
- 2026-08-01 — diagonal and forest pivots killed; closed-cycle holonomy isolated as first
  determinant-visible source orientation.
- 2026-08-01 — even paired-cycle law proved on paper and in unconditional Lean; infinite cofinal
  cycle relocation frozen as exact open core.
- 2026-08-01 — generalized forest blindness to every closed-walk-flat finite support graph and
  formalized exact det₂ cumulant boundary: quadratic blind, cubic reflection-cancelled, quartic
  first surviving cycle signal with coefficient `32(q_0+q_1+q_2)x_01x_12x_20`.
- 2026-08-01 — identified existing unconditional all-order source moment tower as the exact scalar
  det₂ target.  Rejected abstract moment realization as Route P/target-fed; active K burden narrowed
  to operatorial prime-cycle realization of those already known source coefficients.
- 2026-08-01 — constructed literal completed unit--double prime-ratio triangle holonomy and
  instantiated determinant/quartic laws.  Formalized exact finite-balancing obstruction: adding one
  prime changes every old diagonal by the negative new pair column, with exact absolute shell mass.
  Active core narrowed to shell renormalization, trace ideal, cofinal holonomy, and moment incidence.
- 2026-08-01 — corrected physical endpoint orientation, separated divergent primitive nuclear
  budget from absolutely nuclear valuation correction, proved polynomial boundary growth, and
  constructed full completed endpoint as a self-adjoint Hilbert--Schmidt marked-prime operator.
- 2026-08-01 — constructed smooth reciprocal RVM Hilbert--Schmidt skeleton and canonical
  double-commutator Schatten-1 relocation.  Proved exact matrix incidence, zero diagonal,
  self-adjointness, and Hilbert--Schmidt Pythagorean quadratic budget.
- 2026-08-01 — derived cofinal three-prime log clusters from Euler divergence alone; combined with
  source local stiffness to prove cofinal positive completed-endpoint triangle holonomy and
  nonzero centered-reflection quartic edge-flip signal.
- 2026-08-01 — disproved the apparent route-level rigidity of the raw quadratic budget: selected a
  finite RVM head by summable-tail control, proved a unique positive source scale, retained the
  exact cofinite RVM diagonal and every cofinal source cycle, and matched the source zeroth moment
  exactly.  Remaining core begins at quartic source incidence, then all moments/global determinant.
- 2026-08-01 — proved the quartic source target lies strictly inside the necessary reflected
  self-adjoint purity cone, using the existing source bounds `M_1^src<1/5000` and
  `M_0^src>1/25`.  Quartic remains live and is narrowed to simultaneous prime-cycle matrix
  incidence, not positivity or scalar moment feasibility.
- 2026-08-01 — constructed a disjoint cofinal Schatten-1 triangle reserve from normalized actual
  completed-endpoint RVM edges, with exact zero diagonal, arbitrary late support, and positive
  holonomy on every selected block.
- 2026-08-01 — proved exact simultaneous quadratic/quartic admission.  A symbolic control radius,
  cofinite RVM tail, positive cycle scale, and exact two-level finite head give one self-adjoint
  Hilbert--Schmidt operator satisfying `(K21)` while preserving exact RVM tail and cofinal holonomy.
- 2026-08-01 — proved the all-order factorization `(K22)`: complete reflected energy incidence
  makes every source-Hankel test an explicit squared Hilbert--Schmidt norm, hence proves RH and
  supplies Route P's compact Markov carrier without determinant input.  Retired Route K as an
  independent RH route; retained exact quartic construction as formalized positive survivor.
