# Route K prime-cycle trace-class relocation

- **ID:** `route-k-prime-cycle-trace-class-relocation`
- **Stage:** 1-in-progress
- **Type:** `CONJECTURE` / `RH ROUTE` / source-built compact Hilbert--Pólya program
- **Source:** `rh-current-frontier-map.md`, Route K; positive survivor of the retired regular
  Clifford/full-source Hilbert subroute
- **Statement:** The completed Euler--Gamma source builds a cofinal, cycle-holonomy-faithful
  self-adjoint trace-class relocation of the prime-indexed Riemann--von Mangoldt reciprocal
  skeleton whose genus-one determinant is centered Xi.

## Goal

Construct the missing arithmetic part of Route K without enumerating the Xi divisor and without
renaming self-adjointness or a determinant identity as a source theorem.

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
- [ ] 1 → 2 fully-proven: construct `K`, prove trace-norm convergence and determinant identity
  without divisor input
- [ ] 2 → 3 formalized: formalize every dependency-closed theorem; no conditional capstone may be
  advertised as an unconditional construction
- [ ] 3 → 4 publication-ready: standalone paper, complete priority audit, Lean certificate

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
| prime-indexed RVM trace-class relocation with marked cycle provenance | **Route K** | no other numbered route constructs a compact self-adjoint correction of the RVM skeleton on the marked prime basis |

This mapping is structural, not verbal.  A prolate-derived `K` would become Route O; a
cohomological `K` would become Route L.  The present conjecture remains K precisely while its
primitive is the marked prime RVM skeleton plus a source-defined trace-class cycle correction.

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

for every `m`, together with the analytic control upgrading the local `det_2` logarithm to the
global entire identity.  Scalar targets `(S1)` are closed.  Missing knowledge is a compatible
ordinary-prime matrix whose closed walks realize them.  Abstract moment realization would move to
Route P and, without source-built entries, would be target-fed theatre.

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

## Literal completed unit--double cycle candidate `[CONSTRUCTED FINITELY] [LEAN]`

The corpus contains one off-diagonal kernel satisfying Route K provenance.  Put

```text
S(s) = seamFluxCochain(s) = -xi'(s)/xi(s),

R(p,q) = (log p/p)(log q/q)
  Re(2S(2+i log(p/q))-S(1+i log(p/q))).                (K6)
```

`R` is defined from completed source response before zero enumeration, is real symmetric, and is
independent of finite packet.  Therefore

```text
H(p,q,r)=R(p,q)R(q,r)R(r,p)                            (K7)
```

is a literal restriction-compatible prime-cycle holonomy.  On three marked primes, the source
edge flip changes the characteristic determinant by `-4H`; after centered reflection its quartic
trace difference is

```text
32(q_0+q_1+q_2)H(p_0,p_1,p_2).                        (K8)
```

This closes the previous “find a source cycle formula” problem.  It does **not** prove `H` is
nonzero on a cofinal family or that the resulting infinite operator is trace class.

The existing finite row-balanced completion is forced:

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

Thus naive finite balancing is not a projective compression system.  Any trace-norm cofinal limit
must prove an actual source cancellation/renormalization theorem for these diagonal shells and a
nuclear estimate for the off-diagonal kernel.  Entrywise convergence or signed row cancellation is
insufficient because trace norm controls absolute diagonal mass.

Lean module:
`formal/GaloisForLFunctions/RHTower/XiPrimeMarkedUnitDoubleCycleCandidate.lean`.

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

**Frozen conjecture.** Use the literal edge kernel `(K6)` and forced finite balancing `(K9)` to
construct the correction in clauses 1--5.  Prove a source renormalization whose finite diagonal
shells satisfy trace-norm Cauchy control, retain the cycle holonomies `(K7)`, realize every source
moment `(S2)`, and give the global centered-Xi determinant.

**Current attack boundary.** Generic trace damping, finite phase naturality, all flat switching,
target-fed ordering, abstract determinant realization, and reflection-blindness do not construct
or refute this object.  Compatible source cycle holonomies are now explicit.  Exact next hard
theorem is the cofinal shell estimate or renormalization forced by `(K10)--(K11)`, followed by the
operatorial all-moment identity.  No current theorem proves nonvanishing of a cofinal holonomy
family, trace-norm convergence, or even the quartic source-moment match for `(K6)`.

**Verdict:** `OPEN — ROUTE K PIVOT`.

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
- Krein spectral-shift and perturbation-determinant theory supplies the parent trace-class
  language but no ordinary-prime source formula or Xi determinant identity.

No exact-match source was found.  This is noncollision evidence, not a priority claim.

## Lean and infrastructure boundary

The finite cycle theorem is dependency-closed and formalized unconditionally.  The infinite
trace-class net, Schatten convergence, global regularized determinant, and exact Xi comparison are
not yet constructed, so Lean must not replace them with a finite wrapper or an assumed proposition.
Missing honest infrastructure is:

1. a marked-prime finite-compression system with compatible inclusions;
2. cofinal nonvanishing and quantitative control of the constructed unit--double cycle
   coordinates `(K7)`;
3. a diagonal shell renormalization satisfying `(K10)--(K11)` and trace-norm Cauchy control for the
   full correction net;
4. operatorial source-moment lift `(S2)` for every order, with the quartic closed-cycle identity
   fixed before the limit (scalar targets `(S1)` already exist; quadratic is orientation-blind and
   odd orders cancel under centered reflection);
5. global genus-one determinant comparison with the completed Euler--Gamma source.

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
