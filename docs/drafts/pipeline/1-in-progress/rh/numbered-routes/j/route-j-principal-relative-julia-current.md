# Route J principal-relative Julia current

- **ID:** `route-j-principal-relative-julia-current`
- **Stage:** superseded by the Stage-5 Route-J closure card; retained here to preserve references
- **Type:** HISTORICAL SOURCE-CONSTRUCTION / NO-GO CLASSIFICATION
- **Scientific status:** `[RETIRED ROUTE J] [POSITIVE SURVIVOR REQUIRES NEW ROUTE] [NO RH INPUT] [NO COMPUTATION]`
- **Parent no-go:** `../../../../5-failed/route-j-julia-unrenormalized-coherent-energy-budget.md`
- **Endpoint:** Route A's literal first-clock source is eventually bounded below

## Mission

This card records the audit that retired the Julia-coherent principal-relative first-clock
capacity mechanism. Statements below that say “Route J remains open” are superseded as route
ownership claims: they identify escape classes for a different pre-projection primitive. The
existing singular joint-depth/Ward carrier belongs to Route R; any other source-defined current
must be opened as a new route rather than used to reopen J.

## 1. Exact endpoint

Write the attenuated completed source at aperture `L` and Julia scale `x` as

```text
C_x(L)=A(L)+G_x(L)-B_x(L),                               (1)
```

where `A` is the continuous archimedean half-wave budget and `G_x,B_x` are the origin
correlations of the nonnegative reduced good and bad prime channels.  The zero-scale finite-window
limit is the literal published first-clock value.

A successful relative current must construct a source-uniform constant `M` and a source-defined
quantity `R_x(L)` such that, along a source-faithful choice of scales,

```text
C_x(L)<0  ->  C_x(L)^2 <= R_x(L),
R_x(L) <= M.                                             (2)
```

Then `C_x(L)>=-sqrt(M)`, and source-faithful de-attenuation gives the eventual lower floor already
proved equivalent to RH.  Both arrows in `(2)` are required.  Defining `R_x(L)` from the negative
part of `C_x(L)` is representation theatre.

## 2. Closed unrenormalized predecessor

The literal bad Julia energy is

```text
E_B(x,L)=sum_(p,q) B_p(L) K_x(log q-log p) B_q(L).       (3)
```

At `L_m=6 log m`, every prime in `(2m^4,5m^4]` is a one-mode pure-bad channel and contributes
at least `(log p)^2/(4p)` on the diagonal.  The Julia kernel is pointwise positive with unit
diagonal, so

```text
E_B(x,L_m) >= log(m)/20                                 (4)
```

for every real `x`.  Thus `(3)` has no source-uniform upper budget.  At zero scale it instead
converges to the square of total bad mass.  Post hoc subtraction of the diagonal destroys the
normalized anchor-capacity inequality on one unit node.

These results retire only the unrenormalized subroute.

## 3. Two-channel linear-current classification `[PROVED HERE]`

Before scalarization, every channel-linear quadratic current on aggregate good/bad masses has the
form

```text
Q_(a,b,c)(g,h)=a g^2+2bgh+c h^2.                        (5)
```

Call it universally nonnegative when `Q(g,h)>=0` for all real `g,h`.

### Theorem A — null pure-bad diagonal kills the mixed coefficient

If `Q` is universally nonnegative and `c=0`, then `b=0`.  Hence

```text
Q_(a,b,0)(g,h)=a g^2.                                   (6)
```

Proof: `Q(1,0)>=0` gives `a>=0`.  Evaluate at
`(g,h)=(b,-(a+1))`.  With `c=0`, nonnegativity gives

```text
0 <= -(a+2)b^2.
```

Since `a+2>0`, this forces `b=0`.  Therefore a positive two-channel current cannot cancel the
bad self-current while retaining good/bad interference.  If both diagonal coefficients vanish,
the entire positive current vanishes.

### Theorem B — negative-excursion dominance retains full bad diagonal

Assume

```text
g-h<0 -> (g-h)^2 <= Q_(a,b,c)(g,h)                      (7)
```

for all real `g,h`.  Taking `(g,h)=(0,1)` gives `1<=c`.  Therefore no current satisfying `(7)`
can cancel pure-bad diagonal (`c=0`).  This conclusion does not assume positivity and is
independent of whether the counterterm was described as occurring before or after projection.

### Arithmetic strengthening

The sixth-power prime block contains an unbounded family of literal source cells with

```text
good_p(L_m)=0,
bad_p(L_m)>0.                                            (8)
```

The first identity follows from prime-power length one: neither the stable length-at-least-three
term nor the exceptional length-two small-square term is present.  The second follows from the
strict negative sine chamber and the existing positive squared lower bound.  Consequently a
packet-hereditary current that cancels every pure-bad singleton cannot orient even these actual
source cells:

```text
(good_p-bad_p)^2>0=Q(good_p,bad_p).                      (9)
```

Thus pre-projection timing does not rescue any channel-linear or finite-restriction-hereditary
counterterm.

### Theorem C — global positive cross-block rescue is impossible

Let `H(i,j)` be the symmetric real kernel of any quadratic relative current, and suppose every
two-node compression is nonnegative.  If exact principal subtraction makes one bad self-current null,
`H(j,j)=0`, then

```text
H(i,j)=H(j,i)=0 for every node i.
```

Indeed the two-node compression on `i,j` is Theorem A with `c=0`; symmetry gives the other
orientation.  Thus this is not merely a singleton-heredity obstruction.  A globally coupled
positive-semidefinite prime--Gamma kernel cannot cancel a bad diagonal and recover its excursion
through cross-prime or archimedean terms.  Any nonzero quadratic cross-block rescue attached to a
null bad diagonal is necessarily indefinite on the ambient coordinate space.

## 4. Anchored Schur-complement candidate `[CLOSED]`

For a normalized positive-definite kernel `K`, the canonical positive relative current is the
anchored covariance

```text
S_ij=K(t_j-t_i)-K(-t_i)K(t_j).                           (10)
```

For one node of mass `u` at `t`,

```text
anchor^2 = u^2 K(t)^2,
Schur residual = u^2 (1-K(t)^2).                         (11)
```

If `u!=0`, asking the residual to dominate the removed anchor correlation is equivalent to

```text
K(t)^2 <= 1/2.                                           (12)
```

Source-faithful de-attenuation has `K(xt)->1` as `x->0`, so `(12)` eventually fails on every
fixed nonzero source cell.  The Schur complement is positive precisely because it removes the
rank-one component containing the desired excursion.  It is a variance certificate, not a
relative orientation provider.

## 5. Diagonal-null off-diagonal Julia candidate `[CLOSED]`

The first genuine Krein repair is not a fake singleton loophole.  Delete every bad diagonal but
retain the positive Julia cross-prime couplings:

```text
E_off(x,m)=sum_(p!=q in P_m) b_p K(x(log q-log p)) b_q,   (13)
P_m={p prime: 2m^4<p<=5m^4}.
```

Because `b_p>=0` and `K>0`, `(13)` is nonnegative on the literal bad cone even though every
nonzero two-node compression has one positive and one negative ambient eigenvalue.  It is exactly
the ambient-indefinite/copositive escape left by Theorem C.

That escape still fails source-uniform boundedness.  Symbolic block estimates give

```text
B_m=sum_(p in P_m) b_p >= m^2/24,
D_m=sum_(p in P_m) b_p^2 <= 65(log m)^2,                 (14)
B_m^2-D_m >= m^4/576-65(log m)^2.                        (15)
```

No prime-gap estimate is used: the first bound comes from Chebyshev theta mass and the one-mode
sine chamber; the second uses only `p>2m^4`, `p<=5m^4`, and the trivial block-cardinality ceiling.
Every two block primes also satisfy

```text
|log q-log p|<=2.                                        (16)
```

Therefore any cofinal source-faithful scale `x_m->0` makes `K(x_m(log q-log p))>=1/2` uniformly on
the moving block, eventually.  The exact off-diagonal kernel-floor identity then yields

```text
E_off(x_m,m) >= (1/2)(m^4/576-65(log m)^2) -> infinity.
```

Thus deleting only the diagonal does not rescue Julia coherence, even after accepting ambient
indefiniteness and restricting positivity to the actual nonnegative source cone.

## 6. Candidate audit

1. **Post-projection diagonal subtraction:** fails on one unit node.
2. **Channel-linear pre-projection subtraction:** Theorems A--B force either retained bad
   diagonal or loss of all mixed orientation.
3. **Packet-hereditary relative current:** actual pure-bad one-mode cells `(8)` give the same
   contradiction inside the arithmetic source.
4. **Anchored covariance/Schur complement:** source fidelity drives its orientation inequality in
   the wrong direction by `(11)--(12)`.
5. **Invariant Sonin principal-relative trace:** existing Fourier-parity law annihilates the odd
   orientation channel; this is not a Julia repair.
6. **Gamma--Julia endpoint Hilbert--Schmidt dressing:** its exact multiplier has
   `chi_(p,e)^2<=1/2`.  On every nonzero pure-bad sixth-power cell, domination of the undressed
   excursion requires squared gain at least one.  Hence the existing compact dressing is a
   phase-faithful endpoint representation, not Route J's relative capacity.  Its separate
   Julia-dressed exterior-intertwiner conjecture has a completed three-node response endpoint.
7. **Definition by desired sign:** `R=(-min(C,0))^2` satisfies the first half of `(2)` tautologically
   and makes its boundedness exactly the Route-A/RH endpoint.  It creates no source knowledge.
8. **Generic positive-Euler/reflection current:** `positiveEulerQuartet_realization` and
   `positiveEulerQuartet_orientedCauchyResponse` realize a genuinely off-line quartet with
   nonnegative generalized-prime density, exact inversion/reflection data, and favorable
   unsquared orientation.  Therefore those generic properties cannot supply the missing sign.
9. **Globally positive cross-block kernel:** Theorem C annihilates the entire row and column of
   every cancelled bad diagonal.  Adding all primes and the Gamma node cannot restore orientation
   inside an ambient positive-semidefinite quadratic current.
10. **Copositive diagonal-null Julia kernel:** `(13)` is a genuine ambient-indefinite current, but
    `(14)--(16)` force its off-diagonal energy to diverge along every zero-scale cofinal law.
11. **Existing calibrated Julia--Euler exterior current:** its kernel is exactly antisymmetric.
    It retains source orientation as a two-form, but every finite-packet scalar quadratic energy
    `sum_(i!=j) H_(ij)m_i m_j` is identically zero.  Thus it is not a nonzero relative capacity.

## 7. The unrestricted residual endpoint is exactly Route A `[PAPER-PROVED]`

Let `S(L)` be the literal published first-clock source.  Strip away all unformalized words such as
“Krein”, “nonlinear”, and “source-defined”, and retain the widest possible residual capacity claim:

```text
CAP_J := there exist R : R -> R and M,A >= 0 with A >= pi/2 such that,
         for every L >= A,
         0 <= R(L) <= M,
         S(L)<0 -> S(L)^2 <= R(L).                      (17)
```

### Theorem D — endpoint completeness

```text
CAP_J
  <-> S is bounded below on some physical aperture tail
  <-> RiemannHypothesis.                                (18)
```

**Forward proof.**  If `(17)` holds and `S(L)<0`, then `S(L)^2<=M`; hence
`-(M+1)<=S(L)`.  The same lower bound is immediate when `S(L)>=0`.  This is exactly Route A's
eventual lower-bound property.

**Reverse proof.**  If `-C<=S(L)` on a tail, with `C>=0`, put

```text
R_-(L) = if S(L)<0 then S(L)^2 else 0,
M = C^2.                                                (19)
```

Then `(17)` holds.  Formula `(19)` is deliberately recorded as the canonical *theatrical*
witness: it proves the reverse logical implication but supplies no source mechanism.  Thus an
unrestricted “some nonlinear capacity exists” placeholder is not independent Route-J content; it
is exactly Route A's endpoint under a new existential wrapper.

## 8. The completed Ward overlap does not close Route J

The corpus now contains the exact non-diagonal completed construction previously described only
schematically:

```text
actual Möbius four-unit Fisher tangent
  -> singular division by its own squarefree source overlap
  -> completed squarefree prime--Gamma current
  -> centered strict-right correction
  -> continued Xi trace column
  -> anchored two-point Julia cross-cell tangent.        (20)
```

`mobiusGammaFourUnitTangent_to_continuedXiTraceColumn` proves `(20)` before positive projection.
Its source tangent has squared norm tending to four.  The required nonzero Hermitian scalar
capacity is the augmented Ward Gram

```text
W_P = [[G_P, r_P], [r_P^*, 4]],                         (21)
```

and the existing endpoint classification proves

```text
W_P is positive semidefinite for every finite packet
  <-> ContinuedXiWardFourUnitBoundaryLiftLaw
  <-> RiemannHypothesis.                                (22)
```

This construction is the strongest named candidate exposed by Route J's no-go, but it does not
close or transfer the card.  Three missing identifications are mathematical, not administrative:

1. no theorem identifies the Ward Schur defect `(21)` with a first-clock relative capacity
   `R_x(L)` satisfying `(2)`;
2. no theorem shows its symmetric completed block cancels the quartic positive-Julia floor `(15)`
   on the sixth-power pure-bad packet while remaining nonnegative on the literal source locus;
3. the equivalence of both endpoints to RH proves only target equivalence.  It supplies neither
   source identity nor estimate and cannot establish mechanism ownership.

Thus the exact surviving class remains a source-constrained symmetric sign-changing completed
prime--Gamma/co-Poisson current, or a genuinely nonlinear Julia source functional, satisfying both
halves of `(2)`.  The candidate must have a nonzero scalar part, survive the pure-bad moving-block
falsifier, and prove its bound without importing the Ward sign, the first-clock lower floor, or RH.
The existing singular Ward transport is a candidate input to attack, not a reason to stop.

## 9. Route disposition

Route J is retired. Concrete natural subclasses are closed and the representation-free
existential is target-equivalent to Route A. The explicit completed-current escape changes the
primitive: it is Route R when it uses the existing singular joint-depth/Ward source, and otherwise
requires a separately owned new route.

## 10. Novelty and theatre audit

- Theorems A and C are standard positive-kernel algebra; no standalone novelty claim.
- Theorem B is elementary but closes the semantic loophole that moving diagonal subtraction
  “before projection” automatically preserves capacity.
- New source-specific content is the weld of Theorems A--B to the exact infinite family of
  pure-bad sixth-power prime cells.
- The off-diagonal identity is standard.  Candidate new content is the unconditional moving-block
  weld `(14)--(16)`, which kills the copositive diagonal-null Julia current for every scale tending
  to zero.  External novelty remains unverified.
- Antisymmetric quadratic cancellation is standard.  Its exact weld to the existing calibrated
  Julia--Euler source seam closes that named seam as a scalar capacity while preserving its valid
  exterior-orientation interpretation.
- Theorem D is elementary endpoint logic, not new mathematics.  Its research value is preventing
  the negative-part witness `(19)` from masquerading as an independent Julia construction.
- The Route-R endpoint equivalence is a bridge only.  Treating it as route closure would be
  mechanism-transfer theatre.

## 11. Lean plan and gates

- [x] unrenormalized bad-energy route refuted unconditionally
- [x] channel-linear positivity classification formalized
- [x] negative-excursion diagonal-retention theorem formalized
- [x] actual pure-bad sixth-power source cells formalized
- [x] anchored Schur-complement failure formalized
- [x] existing Gamma--Julia endpoint Hilbert--Schmidt dressing excluded
- [x] positive global cross-block rescue excluded
- [x] canonical copositive diagonal-null Julia off-diagonal current refuted
- [x] existing calibrated Julia--Euler exterior current proved scalar-zero
- [x] formalize Theorem D and the target-equivalent Route-R endpoint bridge
- [x] prove that endpoint equivalence alone supplies no source-current construction
- [x] retire Route J at its exact coherent-energy/capacity quantifier
- [ ] if pursued, open a separate card for a literal pre-projection symmetric/nonlinear current

## 12. Source-fusion superselection input

The publication-ready source-fusion theorem

```text
../4-publication-ready/riemann-source-modular-superselection/main-universal.tex
```

changes the admissible Route-J class.  The positive high-exponent shells are coefficient-disjoint,
relatively differentially independent over the full zeta differential field, and carry the same
strict-right completed divisor with unit response.  Finite reciprocal label packets obey the exact
orthogonal splitting

```text
2 sum_i x_i y_i
  = (2/N)(sum_i x_i)(sum_i y_i)
    + 2 sum_i (x_i-x_bar)(y_i-y_bar).                   (23)
```

At countable multiplicity, the unit-response codiagonal is nonclosable on the orthogonal `ell2`
label sum, and no Bessel realization has one bounded vector with the same nonzero response on
every label.  Therefore a regular post-fusion Hilbert current is no longer a Route-J survivor.
Any successful current must:

1. act before common-divisor scalar fusion;
2. retain shell, valuation-depth, and reflection-orientation coordinates;
3. be singular in every stable Hilbert realization: relation-valued, rigged, nonclosable, or
   beyond every finite Rees order;
4. still produce one unambiguous scalar capacity satisfying both inequalities in `(2)`.

The corpus already proves that the actual-prime clock and the CCM block--Fock graph have
full-product closure and no closed single-valued extension, even nonlinear.  This kills those two
singular carriers only.  It does not kill a nonclosed source-core correspondence or a different
singular prime--Gamma/co-Poisson carrier.

## 13. The centered fusion current `[PAPER+LEAN-PROVED NO-GO]`

For a nonempty finite bad-label packet `b=(b_i)`, put

```text
B = sum_i b_i,
D = sum_i b_i^2,
b_bar = B/N,
V_fus(b) = sum_i (b_i-b_bar)^2.                         (24)
```

Expanding `(24)` gives the exact identity

```text
V_fus(b) = D - B^2/N,      0 <= V_fus(b) <= D.          (25)
```

Thus `V_fus` is a nonzero symmetric positive-semidefinite current on the transverse fusion fibre.
It annihilates the constant common-response mode and is not the antisymmetric scalar-zero current
closed in Section 6.

On the sixth-power pure-bad block, the proved estimates `(14)` give

```text
0 <= V_fus(b_m) <= 65 (log m)^2,
B_m^2 >= m^4/576.                                      (26)
```

Since `(log m)^2=o(m^4)`, eventually

```text
V_fus(b_m) < B_m^2.                                    (27)
```

Therefore centered fusion cancels the common quartic mode only by discarding the magnitude needed
to dominate the pure-bad excursion.  Multiplying `(24)` by a packet-dependent factor chosen from
the desired excursion would merely move the target into the normalization.  This closes the
plain centered-variance repair.

The genuinely Julia-centered kernel is sharper.  If `K_x` is the finite Julia Gram and
`P_N=I-N^{-1}11^T`, then

```text
E_tr(x,b)=b^T P_N K_x P_N b >= 0.                       (28)
```

Section 20 below proves a moving-packet result stronger than fixed-packet convergence:
`E_tr(x,b)<(sum b)^2` simultaneously on every sixth-power block throughout one zero-scale
neighbourhood.  Thus the bare Julia-centered kernel is closed.  The remaining question is whether
a singular pre-fusion coupling to the completed Gamma/co-Poisson orientation can add a bounded
longitudinal-to-transverse transfer without reinstating the quartic floor.  Neither `(23)` nor
`(28)` supplies that coupling.

## 14. Heavy conjecture ledger

### `J-SF0` — actual arithmetic Julia normal cone `[CONSTRUCTED INPUT, OPEN CAPACITY]`

`arithmeticJuliaNormalConeUniversality` already supplies more than an abstract singular carrier:

```text
finite actual-prime Julia-normal clocks -> literal logarithmic clock,
every bounded Hardy extension has norm -> infinity,
critical completed face -> full strict-right Xi divisor with multiplicity.
```

Its positive two-channel cell lift is unique and minimal.  However the fixed Möbius--Gamma/Ward
source graph has exact base gain `1/(2|epsilon|)` and its normal-cone blow-up has gain
`1/(2|epsilon|^2)`; both are expansive on the physical critical ray.  Thus this constructed
singular input cannot inherit positivity from ambient source-norm contractivity.  The open task is
to find a graph norm and scalar polarization whose singular gains cancel before the Route-J
capacity is read.

### `J-SF1` — singular centered Julia--Wold current `[OPEN]`

There is a source-core relation coupling the centered Julia Gram `(28)` to the two-coordinate
Wold--Poisson conormal before shell fusion, whose Hermitian scalar part:

```text
- is nonnegative on the literal arithmetic source locus;
- dominates every negative first-clock excursion;
- has one source-uniform upper bound;
- is independent of any Xi zero, Ward sign, or target-selected packet.
```

Hostile obligations: prove single-valuedness of the scalar despite multivalued graph closure;
identify its first-clock residual exactly; and survive the sixth-power moving block.

Section 21 closes every version whose depth symbol is the actual Xi successor and whose scalar
capacity is nonnegative, lower-semicontinuous, and two-homogeneous on the reporter topology:
the literal Wold-vacuum truncations then force harmonic-square capacity growth unless the
capacity annihilates the Xi logarithmic connection.  `J-SF1` remains open only for a genuinely
non-lower-semicontinuous/nonhomogeneous preclosure scalar, or for a new source operator whose
depth symbol is not the actual successor.  Either alternative must still meet `(2)` and the
first-clock moving block; neither is supplied by naming the singular graph.

### `J-SF2` — complex polarization of the exterior seam `[CLOSED FOR ALL BOUNDED POLARIZATIONS]`

Multiplication of the real antisymmetric exterior kernel `H` by `i` gives a Hermitian matrix
`iH`.  Real arithmetic weights still give

```text
b^* (iH) b = 0.                                        (29)
```

A nonzero value therefore requires label-dependent complex phases before scalarization.  A common
phase does not help.  Generic prime-log phases are already known not to select the arithmetic
orientation, so the only live version requires a nonuniform source-derived phase retained across
singular transport.  Supplying that phase is part of the theorem, not free input.

### `J-SF3` — nonlinear positive-part repair
`[ACTUAL EXTERIOR POSITIVE PART CLOSED; NEW SINGULAR SOURCE OPERATOR OPEN]`

Taking a Jordan/Krein positive part after forming the completed defect gives a nonnegative
functional, but the spectral projector is computed from the target defect.  Unless its projector
is independently constructed from the prime--Gamma/co-Poisson source before scalarization, this is
the operator analogue of `(19)` and receives no Route-J credit.  Section 23 proves a stronger
quantitative statement for the actual calibrated exterior matrix: even granting its target
spectral projector, the full Jordan positive part is too small by a logarithmic factor.  Thus a
direct positive-part repair of the existing exterior seam is closed.  A genuinely different
singular completed source operator, with its projector constructed before the target sign is
read, remains a Route-J survivor under this label.

### `J-SF4` — stable nonlinear classification `[CLOSED ON THE ACTUAL DEPTH CHANNEL]`

Section 21 proves a stronger no-go without the parallelogram law: every nonnegative,
two-homogeneous, lower-semicontinuous capacity on the actual Xi depth reporter either annihilates
the Xi logarithmic connection or is unbounded on the literal Wold-vacuum truncations.  Thus stable
nonlinearization cannot repair the source budget even when it is not quadratic.  Genuinely
non-lower-semicontinuous or nonhomogeneous preclosure scalars remain part of `J-SF1`; they are not
silently reassigned.

### `J-SF5` — semilocal Hardy compression `[OPEN SINGULAR SURVIVOR]`

Connes--Consani's scaling-Hamiltonian criterion identifies positivity of the direct Hardy
compression with innerness of the local phase.  Finite-prime and archimedean local-factor ratios
are not bounded inner functions, and the direct inequality fails even at the archimedean place.
Their semilocal Poisson/Weil program remains explicitly conjectural.  Hence regular local Hardy
compression is closed, but singular semilocal source coupling remains live and belongs to this
Route-J audit.

### `J-SF6` — Xi Taylor theta-tail oriented current
`[POINTWISE CLASSIFIED; REFLECTION-EQUIVARIANT CONVERGENT TWO-ACTIVE-ATOM SCALAR CLASS CLOSED;
CANONICAL TWO-SIDED THETA COMPLETION CLOSED;
EXPLICIT THREE-ATOM REFLECTION-COHERENT UNIT-CHARGE SURVIVOR CONSTRUCTED;
THREE-ATOM LITERAL SAME-PROFILE CLASS CLOSED;
EXPLICIT FOUR-ATOM LITERAL REFLECTED UNIT-CHARGE SURVIVOR CONSTRUCTED;
FOUR-ATOM LITERAL EQUAL-CHARGE CLASS COMPLETELY CLASSIFIED AND ONE-ORBIT RIGID;
ACTUAL NON-ATOMIC AT-MOST-THREE-PHASE-WEIGHTED-SIGN-CHANGE CLASS CLOSED;
EXPLICIT EXACT-FOUR-CHANGE REGULAR SURVIVOR CONSTRUCTED;
FIXED-SPACING IDENTICAL-FIVE-TRANSLATE REGULAR CLASS COMPLETELY CLASSIFIED AND
ONE-POSITIVE-DAMPING RIGID;
UNCENSORED MULTI-PRIME PRIME-POWER PHASE-NODE SOURCE CLOSED;
SOURCE-LIFT/SINGULAR/RELATION SURVIVOR OPEN]`

The finite theta-tail source has an exact signed current and a fully arithmetic two-term remainder
bridge.  Its remaining joint sublinear bound is equivalent to RH, so it cannot be imported as an
estimate.  It is nevertheless a source-defined odd current before scalar fusion, and the
full-density decomposition proves that all unresolved positive contribution lies in one canonical
finite-truncation transfer current.  Fixed meromorphic transgressions were already classified by
local divisor order.  Section 24 now closes the genuinely moving positive-completion class:
arbitrary nonnegative source densities, phase-lag schedules, and positive theta-packet depth
schedules have zero anisotropic divisor charge, even without a normal-family limit.  They cannot
screen the exact finite-Taylor multiplicity.  The surviving transgression must leave the positive
completion cone through one coherent divisor-independent signed density family, a singular
boundary term, or a relation-valued channel without a scalar logarithmic derivative.  Section 25
proves arbitrary pointwise signed interpolation is universal and hence nonselective.  Merely
calling the coherent survivor a different route would leave a source-current survivor unexamined.
Section 26 proves the first cross-mesh exclusion in the quarter-turn palette: scalar charge
uniquely collapses to two even atoms, its normalized weights determine the Xi fibre radius, and a
common reflection-equivariant nonzero profile at `sigma` and `1-conj(sigma)` forces
`Re sigma=1/2`. Section 28 removes that support choice. Every distinct two-active-atom scalar jet
phase-locks both arbitrary support times to half turns; its limiting value and derivative
fingerprints then force every reflection-projectively coherent nonzero charge profile onto the
critical line. A projective survivor must use at least three asymptotically active atoms. Section
30 proves that one literal coefficient profile with equal reflected charge needs at least four:
three atoms force zero charge, while an explicit four-atom polynomial gives one common exact
unit-charge profile. Section 31 proves every such four-atom equal-charge vector lies on that
canonical ray, and one nonzero vector can serve only one reciprocal transverse orbit. Thus the
minimal survivor is target-informative, not a divisor-independent source law.
Section 32 restores the Fourier phase required by a genuine non-atomic physical-time source. For
an arbitrary atomless reference measure and unbounded positive support, the imaginary-value and
real-derivative rows at both reflected fibres reduce to orthogonality of
`cosh(c t) sin(u t)h(t)` against `1`, `t`, and `tanh(c t)`. Strict concavity kills every source
whose phase-weighted density `sin(u t)h(t)` has at most two sign changes. On one open phase
chamber these are exactly changes of `h`; the finite full-turn survivor sits on sine nodes and is
therefore a singular escape, not an atomless extremizer.
Section 33 uses the fourth, previously discarded derivative-row combination. The resulting
exponential-Hermite system kills every source with at most three phase-weighted sign changes.
Section 34 proves this threshold exact by an explicit five-bump Lebesgue source. Its reciprocal
double-root mask annihilates all four rows and has exactly four changes in one sine chamber.
Section 35 classifies the entire arbitrary-coefficient fixed-spacing identical-five-bump class:
the four physical rows force precisely the reciprocal double-root coefficient ray, and one
nonzero physical mask serves only one positive damping. Thus the sharp extremizer is necessarily
target-informative. Variable support geometry, nonidentical or higher-arity translates, general
atomless densities with at least four phase-weighted changes, phase-node mass, singular
boundaries, broken leading reflection, and relation-valued channels remain live.
Section 36 attacks phase-node mass with literal arithmetic provenance. At every nonzero carrier,
prime-power delays from two distinct prime bases cannot both be sine nodes: the two node equations
would give a nontrivial integer relation between the two prime logarithms. Hence every phase-node
multiplier on the prime-power wall has active prime-base support of cardinality at most one. The
literal Suzuki/von-Mangoldt far-hinge source is positive on every prime-power atom, so it cannot
inhabit the phase-node class. One-prime towers and non-prime-power singular sources remain live.
Section 27 also closes the literal canonical reflected theta pair:
`A(z)+A(-z)` is an analytic unit at every Xi divisor by its exact crossed source identity, so it
preserves rather than screens the full anisotropic multiplicity.
Section 29 proves the two-atom arity bound sharp. Three full-turn atoms carry an explicit nonzero
common reflected value-kernel ray; bounded exact corrections give unit anisotropic
source-connection charge at both off-center fibres, with projectively equal normalized weights.
Section 30 shows why this is not yet one literal source law: the reflected three-atom
representative is rescaled by `r^3`. That stronger same-profile constraint kills three atoms, but
four atoms survive with one coefficient vector at both fibres. The remaining scalar obligation is
now concrete: Section 31 shows its coefficient ray itself encodes the chosen reciprocal orbit.
Route J must exclude this target-informative ray from the canonical theta/prime--Gamma source law,
or derive its unique orbit source-faithfully without divisor data.

## 15. Post-manuscript exact open core

Route J now asks for, or must exclude class-completely, a singular source-pointed correspondence
on the pre-fusion transverse fibre.  It must retain a nonuniform reflection-odd phase, pass through
completed prime--Gamma/co-Poisson transport, and land in a symmetric scalar Julia current meeting
`(2)`.  Common-test Weil reconstruction supplies the terminal form but selects its approximating
packets from the target vector; using that selection is theatre.  Route J remains open until the
source-only section and its sign are constructed or every singular class above is eliminated.

## 16. Updated biaxial source-conservation law

The 1 August 2026 revision of

```text
../4-publication-ready/riemann-source-modular-superselection/main-universal.tex
```

adds two exact gates which must now be carried explicitly in every Route-J construction.
For a partial completion `pi : D -> Q` and target distinction `c`, recovery is equivalent to:

```text
admission:   D = X,
separation:  pi(x)=pi(y) -> c(x)=c(y).
```

Postprocessing only enlarges the kernel relation.  In particular, a reflection-invariant
completion cannot recover a nonzero reflection-odd real target.  The missing orientation must be
present in a transverse channel before invariant scalarization; constructing it after fusion is
set-theoretically impossible.

The revision also identifies one chart-independent modular charge

```text
a_rho = Re(rho)-1/2,
```

simultaneously carried by normalized shell transport, the centered Xi logarithmic residue,
principal Hurwitz phase, and compact-BV dilation.  Reflection sends `a_rho` to `-a_rho`.
Its arithmetic realization has two independent singular axes:

1. **breadth:** unit response on countably many positive exponent shells forces a nonclosable
   codiagonal, even at `a_rho=0`;
2. **depth:** for `0<a_rho<1/2`, the positive Wold Hellinger sector is flat beyond every power of
   the finite Wold boundary volume, while its reflection is half-normal.  Exact reflection sewing
   therefore has norm larger than every finite inverse Rees power.

Thus a Route-J survivor must act on the joint Wold-breadth/exponent-depth incidence grid, promote
the primitive current before scalar fusion, be nonclosable or relation-valued in breadth, and be
beyond every finite Rees grade in reflected depth.  A merely nonclosed shell codiagonal is
insufficient; a merely all-orders-flat valuation map is also insufficient.

The manuscript now includes the explicit centered-fusion estimate `(24)`--`(27)`, including the
threshold `m>=300`.  Its dependency-closed Lean proof is:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockSourceFusionSuperselectionNoGo.lean
```

The module proves the exact centered-energy identity, nonnegativity, logarithmic-square upper
bound, strict failure against squared pure-bad block mass, and combined regular Hilbert fusion
no-go.  It is wired into `RHTower.lean`.

## 17. Source-height polarization of the exterior seam `[PAPER+LEAN-PROVED CURRENT]`

The earlier `J-SF2` audit left one precise obligation: construct a nonuniform phase from source
data before scalarization.  The finite Julia--Gamma transport itself supplies one.  Let

```text
h_x(p,e)
  = (1/2) gammaMidHeight(p,e)
    + (1/4) normalizedJuliaPrimeLog_x(p),
a_u(p,e) = xiGammaEulerBoundaryRealAmplitude(u,p,e) > 0.
```

The calibrated exterior cell has exact rank-two form

```text
H_x(i,j) = a_u(i) a_u(j) (h_x(i)-h_x(j)).
```

For `tau>=0`, phase each source cell before scalarization by

```text
z_i(tau)=exp(i tau h_x(i)).
```

Then the Hermitian scalarization of `i H_x` is real and equals

```text
Q_x,u,tau(P)
  = Re sum_(i,j in P) conj(z_i) i H_x(i,j) z_j
  = sum_(i,j in P)
      a_u(i)a_u(j)(h_x(i)-h_x(j))
      sin(tau(h_x(i)-h_x(j))).                         (30)
```

If every packet phase difference has magnitude at most `pi`, every summand in `(30)` is
nonnegative because `d sin(tau d)>=0`.  If two retained source heights differ and their phase
difference is strictly below `pi`, `(30)` is strictly positive.  This is a genuine nonzero
symmetric scalar current obtained from the previously scalar-zero exterior seam.  It uses only
finite-aperture prime--Gamma--Julia source coordinates; no Xi zero, desired sign, negative part,
Ward conclusion, or target-selected packet occurs in its definition.

The scratch formalization proves the exact complex-to-real identity, nonnegativity, strict
positivity, and calibrated-height factorization unconditionally.  It is being promoted to a
Route-J module.

This construction closes the phase-existence part of `J-SF2`, but not Route J.  Remaining
questions are quantitative:

1. does `(30)` dominate the full first-clock negative excursion, rather than only orient an
   exterior source packet?
2. can `(30)` have one source-uniform upper budget on cofinal moving packets?
3. can its phase carry the chart-independent odd modular charge through both the nonclosable
   breadth axis and beyond-finite-Rees reflected depth, rather than only positive Euler height?

Until those are proved or contradicted, `J-SF2` is a real survivor.

## 18. Safe source-height phase cannot dominate `[PAPER-PROVED NO-GO]`

The positive phase cone in Section 17 admits a quantitative audit.  At the Euler boundary and
valuation depth zero, for `p` in the macroscopic block

```text
P_X = {p prime : 2X < p <= 5X},
```

the source amplitude and height are

```text
a_p = sqrt(log(p)/p),
h_p = (1/2) log(p).
```

Write `D=(1/2)log(5/2)`.  For every `p,q in P_X`,
`|h_p-h_q|<=D`.  In the no-wrap cone,

```text
0 <= d sin(tau d) <= tau d^2,
```

so the phased exterior energy satisfies

```text
0 <= Q_X(tau)
   <= tau D^2 (sum_(p in P_X) a_p)^2.                  (31)
```

Chebyshev's elementary upper bound gives

```text
sum_(p in P_X) log p <= theta(5X) <= 5X log 4.
```

Since every `p>2X`,

```text
sum a_p^2 = sum log(p)/p <= (5/2) log 4,
card(P_X) log(2X) <= sum log p,
```

and Cauchy--Schwarz yields

```text
(sum a_p)^2
  <= card(P_X) sum a_p^2
  <= (25/2)(log 4)^2 X/log(2X).                       (32)
```

No novelty is claimed for the weighted-prime estimate in `(32)` itself.  Hubbard,
[*The S--E route to the Chebyshev bounds for the prime-counting function*]
(https://arxiv.org/abs/2604.21946), independently studies
`sum_(p<=X) sqrt(log p/p)` and proves its square has order `X/log X`.  Route J's new content is
the exact identification of this weight inside the Julia--Gamma exterior current and its
comparison with the certified first-clock pure-bad mass.

The prime number theorem supplies, for all large `X`, one prime in
`(2X,(9/4)X)` and one in `(4X,(9/2)X)`.  Their height separation is at least
`(1/2)log(16/9)`.  Therefore the packet-wide no-wrap condition forces

```text
tau <= 2 pi / log(16/9),                               (33)
```

uniformly in `X`.  Combining `(31)`--`(33)` gives

```text
Q_X(tau) = O(X/log X) = o(X).                          (34)
```

On the certified first-clock block `X=m^4`, the pure-bad mass theorem gives

```text
(sum bad_p)^2 >= X/576.                                (35)
```

Hence every source-height phase staying in the proven positive cone eventually satisfies

```text
Q_X(tau) < (sum bad_p)^2.                              (36)
```

It cannot meet the packet-hereditary domination demanded by `(2)`.

This persists at finite Julia aperture along every moving-block source-faithful scale:

```text
x_m log(5m^4) -> 0.
```

Indeed

```text
normalizedJuliaPrimeLog_x(p)/log p
```

is a continuous function of `x log p` with limit one at zero, by the exact prime-attenuation
profile.  The displayed scale condition makes this convergence uniform on `P_(m^4)`, so calibrated
heights and `(31)`--`(36)` survive with an arbitrarily small multiplicative error.

Consequences:

1. the nonuniform phase constructed in Section 17 is genuine new source orientation, not
   scalar-zero theatre;
2. its entire termwise-positive/no-wrap class is nevertheless too small by a logarithmic factor
   on the hard arithmetic block;
3. any remaining `J-SF2` mechanism must use phase wrapping with a non-termwise global positivity
   theorem, or combine the phase with the manuscript's beyond-finite-Rees depth relation before
   scalarization.

Thus `J-SF2` is narrowed to an oscillatory or genuinely beyond-Rees coupling.  Merely choosing a
different bounded safe phase cannot work.

## 19. Arbitrary bounded polarization cannot dominate `[PAPER-PROVED CLASS NO-GO]`

The no-wrap restriction in Section 18 is unnecessary.  Let `z_p` be arbitrary complex
multipliers on `P_X`, allowed to depend on the whole packet, and assume only

```text
|z_p| <= B.
```

The Hermitian scalarization of the Euler exterior seam is

```text
E_X(z)
  = Re sum_(p,q in P_X)
      conj(z_p) i a_p a_q (h_p-h_q) z_q.
```

Triangle inequality and the fixed multiplicative width of the block give the phase-free estimate

```text
|E_X(z)|
  <= B^2 sum_(p,q in P_X) a_p a_q |h_p-h_q|
  <= B^2 D (sum_(p in P_X) a_p)^2.                    (37)
```

Combining `(32)` and `(37)`,

```text
|E_X(z)|
  <= (25D/2) B^2 (log 4)^2 X/log(2X)
  = O_B(X/log X).                                      (38)
```

This estimate has no sign hypothesis, no phase-flow hypothesis, no no-wrap cone, and no
source-only selection hypothesis.  It remains true for packet-dependent, oscillatory, or even
target-selected phases.  On `X=m^4`, `(35)` therefore implies, for every fixed `B`,

```text
|E_(m^4)(z)| < (sum bad_p)^2
```

for all sufficiently large `m`.  Thus every uniformly bounded diagonal polarization of the
calibrated exterior seam fails the required domination.  In particular, source-height phases
with arbitrary wrapping are closed, not survivors.

The logarithmic loss is sharp at level of available source amplitudes: to compete with the
linear-in-`X` bad-mass square through this rank-two exterior cell, multiplier norms must grow at
least on order `sqrt(log X)`.  Such a family is not a complex polarization; it is an unbounded
amplitude-creating correspondence.  If it is to remain admissible, its closability, uniform
capacity budget, Wold-breadth response, and beyond-finite-Rees reflected-depth action must be
proved as one singular construction.  Calling this amplification a phase would conceal the
missing operator.

Therefore `J-SF2` is class-completely closed for bounded polarizations.  Route J remains open:
the surviving question is whether one source-defined singular correspondence can generate the
required unbounded transverse amplitude while still producing a finite scalar capacity, not
whether a cleverer phase can rescue the exterior seam.

## 20. Moving-block collapse of the centered Julia Gram `[PAPER+LEAN-PROVED NO-GO]`

The fixed-packet limit after `(28)` upgrades uniformly over the moving arithmetic blocks.  Let
`P` be a nonempty finite packet, let `b_i>=0`, put

```text
B=sum_i b_i,
c_i=b_i-B/|P|.
```

Then

```text
sum_i c_i=0,
sum_i |c_i| <= 2B.                                     (39)
```

The second inequality follows termwise from
`|b_i-B/|P||<=b_i+B/|P|`.  For any real kernel satisfying

```text
sup_(i,j in P) |K_ij-1| <= delta,
```

the constant Gram cancels exactly and

```text
E_tr(c)
  =sum_(i,j) c_i (K_ij-1)c_j,
|E_tr(c)|
  <=delta (sum_i |c_i|)^2
  <=4 delta B^2.                                       (40)
```

This is standard centered-kernel algebra; no standalone novelty is claimed.  The Route-J content
is that `(40)` is uniform on its hard moving-prime falsifier.  Every pair in

```text
P_m={p prime:2m^4<p<=5m^4}
```

satisfies `|log q-log p|<=2`.  The normalized Julia kernel is continuous at zero and equals one
there.  Therefore one neighbourhood of `x=0`, independent of `m`, satisfies

```text
sup_(m>=25) sup_(p,q in P_m)
  |K_x(log q-log p)-1| < 1/8.                           (41)
```

Combining `(40)`--`(41)` gives

```text
E_tr(x,b_m) <= |E_tr(x,b_m)|
             <= (1/2) B_m^2
             < B_m^2                                   (42)
```

on every certified nonempty block.  Consequently, for every source-faithful schedule `x_m->0`,
the centered Julia Gram eventually fails pure-bad domination.  No rate for `x_m`, prime gap,
kernel Taylor expansion, or fixed-packet interchange is used.

This closes the bare kernel `(28)`, including the possible slow-scale loophole.  A surviving
`J-SF1` correspondence must add a genuinely new longitudinal-to-transverse source operator; it
cannot be centering, a Julia Gram evaluated on centered masses, or a bounded polarization of the
exterior seam.  Such an added operator must simultaneously cross the nonclosable breadth axis,
cross the beyond-finite-Rees depth fracture, and keep its scalar output within the uniform
capacity budget.

## 21. Wold-vacuum harmonic capacity dichotomy
`[PAPER+LEAN-PROVED CLASS NO-GO] [NEW SOURCE WELD]`

The essential-amplification law can be strengthened from a norm lower bound to a scalar-capacity
obstruction on one canonical source vector.  Let

```text
h_m = H_m(1) ~ 2^(-(m+1)),
||delta_m||^2 = h_m,
delta_m orthogonal,
```

where `delta_m` is the actual Wold maximum-exponent shell.  Fix a compact set `K` avoiding the Xi
divisor, and write in `C(K)`

```text
R_M(u)
  = Xi(u)/Xi((1+1/(M+1))u)-1,
L_Xi(u)
  = -u Xi'(u)/Xi(u).
```

The exact depth-successor derivative gives

```text
y_M := (M+1) R_M  ->  L_Xi                              (43)
```

uniformly on `K`.  Choose `K` with `L_Xi` nonzero.  Suppose one source-global linear
correspondence `T` on the finite Wold shell core realizes the actual successor,

```text
T delta_(M+1) = R_M.                                    (44)
```

### 21.1 Exact vertical graph defect

Put `v_M=(M+1)delta_(M+1)`.  Since

```text
||v_M||^2
  = (M+1)^2 h_(M+1)
  ~ (M+1)^2 2^(-(M+2))
  -> 0,
```

while `(43)`--`(44)` give `T v_M -> L_Xi`, graph closure contains

```text
(0,L_Xi).                                                (45)
```

Thus every exact source-global depth-successor realization is nonclosable whenever `L_Xi` is
nonzero.  This identifies its vertical multivalued direction exactly; the earlier operator-norm
lower bound only proved that bounded realizations fail.

### 21.2 Literal vacuum exhausts every stable scalar budget

No depth-moment reweighting is needed.  Let

```text
Omega_N = sum_(M<N) delta_(M+1),
H_N     = sum_(M<N) 1/(M+1).
```

Wold source masses are summable, so `Omega_N` converges to the literal Wold vacuum.  By linearity
and `(44)`,

```text
T Omega_N = sum_(M<N) R_M
          = sum_(M<N) (1/(M+1)) y_M.
```

Weighted Cesaro convergence applied to `(43)` and `H_N -> infinity` yields

```text
(T Omega_N)/H_N -> L_Xi.                                (46)
```

Let `Q:C(K)->R` satisfy

```text
Q(f)>=0,
Q(rf)=r^2 Q(f)          for real r,
Q lower-semicontinuous at L_Xi.                         (47)
```

Lower semicontinuity and `(46)` imply

```text
Q(L_Xi)
  <= liminf_(N->infinity) Q(T Omega_N/H_N)
   = liminf_(N->infinity) Q(T Omega_N)/H_N^2.            (48)
```

Consequently,

```text
Q(L_Xi)>0
  -> for every 0<eta<Q(L_Xi),
     Q(T Omega_N) >= eta H_N^2 eventually
  -> sup_N Q(T Omega_N)=infinity;                        (49)

sup_N Q(T Omega_N)<infinity
  -> Q(L_Xi)=0.                                          (50)
```

This is the missing scalar-budget dichotomy.  A stable capacity detecting the primitive Xi depth
connection violates the source-uniform upper half of `(2)` already on truncations of one canonical
finite-norm source vector.  A uniformly budgeted stable capacity annihilates that connection and
therefore cannot use the actual depth successor to create the missing Route-J orientation.
Parallelogram compatibility, quadratic representation, closability of `T`, a Xi zero, and RH are
not assumed.

The theorem closes `J-SF4` on the actual depth channel and closes the lower-semicontinuous
two-homogeneous part of `J-SF1`.  It does **not** close a discontinuous/nonhomogeneous preclosure
scalar or a new longitudinal-to-transverse operator with a different depth symbol.  Those
survivors remain Route J work and must still satisfy first-clock domination and uniform budget
in `(2)`.

### 21.3 Novelty and hostile audit

Weighted Cesaro convergence, lower semicontinuity, and the elementary graph criterion are standard
parent facts.  New content is their exact weld to both arithmetic sides:

1. actual Wold source masses make the unweighted vacuum finite;
2. actual Xi quotient successor is harmonic with limit `L_Xi`;
3. their source-global graph has precise vertical direction `(0,L_Xi)`; and
4. same literal vacuum forces harmonic-square blow-up for every stable detecting capacity.

Targeted external searches for nonclosable-operator/Cesaro-capacity results and Xi dilation
quotients found parent ingredients separately, not this Wold-shell/Xi-successor conjunction.
This supports a project-new theorem but does not certify external priority.

Unconditional Lean module:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockWoldXiDepthCapacityNoGo.lean
```

It proves weighted Cesaro convergence, general lower-semicontinuous two-homogeneous budget
dichotomy, exact Xi depth-moment convergence, exact unrenormalized successor recovery, harmonic
divergence, actual prime-two Wold mass envelope, summability of Wold vacuum and depth-moment norm
squares, normalized vacuum-reporter convergence, and final capacity non-domination.  No `sorry`,
`admit`, `axiom`, `opaque`, `unsafe`, computation, or RH input occurs.

## 22. Global Cayley orientation and minimum exterior singularity
`[PAPER+LEAN-PROVED POSITIVE THEOREM AND SHARP NECESSARY RATE]`

The normalized source chart

```text
u_tau(h)=(1+i tau h)/sqrt(1+tau^2 h^2)
```

has unit norm and turns every calibrated Julia--Gamma exterior pair into

```text
tau A_i A_j (h_i-h_j)^2
/ (sqrt(1+tau^2 h_i^2)sqrt(1+tau^2 h_j^2)).
```

Thus exterior orientation is globally nonnegative without phase wrapping.  The same first-clock
prime block gives a class-wide capacity ceiling.  If `|u_p|<=B_m` and the polarized exterior
energy dominates the certified pure-bad mass square, then

```text
log(2 m^4) <= 7200 (log 4)^2 B_m^2.                    (51)
```

Consequently every dominating exterior chart has
`B_m >= sqrt(log(2m^4))/(sqrt(7200) log 4)`.  Bounded charts fail, and any surviving exterior
transport must pay at least square-root-logarithmic multiplier blow-up.  This is a necessary
rate, not a sufficient construction; it neither proves the renormalized upper budget in `(2)`
nor closes Route J.

Formal modules:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockCayleySourcePhaseOrientation.lean
  CCMFirstClockCayleyOrientationCapacityDichotomy.lean
  CCMFirstClockExteriorCapacitySingularity.lean
```

## 23. Rank-two Jordan positive-part ceiling
`[PAPER+LEAN-PROVED NONLINEAR CLASS NO-GO] [NEW SOURCE WELD]`

The target-selected positive spectral projector cannot repair the actual exterior seam even if
one grants it for the audit.  On a finite packet put

```text
alpha_i = A_i,
beta_i  = A_i h_i,
K_ij    = i A_i A_j (h_i-h_j)
        = i (beta_i alpha_j-alpha_i beta_j).
```

The Hermitian matrix `K` has rank at most two.  Its Gram determinant

```text
Delta
  = ||alpha||^2 ||beta||^2 - <alpha,beta>^2
  = (sum A_i^2)(sum A_i^2 h_i^2) - (sum A_i^2 h_i)^2       (52)
```

is nonnegative by Cauchy--Schwarz and invariant under `h_i -> h_i-c`.  On the span of
`alpha,beta`, Gram--Schmidt puts `K` in the exact form

```text
[ 0                 -i sqrt(Delta) ]
[ i sqrt(Delta)      0              ].
```

It vanishes on the orthogonal complement.  Hence its spectrum is
`{-sqrt(Delta),0,sqrt(Delta)}`, its Jordan positive part `K_+` has rank at most one, and

```text
||K_+|| = Tr(K_+) = sqrt(Delta).                           (53)
```

If `|h_i-h_j|<=D`, choose one retained height as center.  Translation invariance of `(52)` gives

```text
Delta <= D^2 (sum A_i^2)^2.
```

Therefore, for every coordinate vector with `|z_i|<=B`,

```text
0 <= <z,K_+ z>
   <= B^2 card(P) sqrt(Delta)
   <= B^2 D card(P) sum A_i^2.                            (54)
```

This is not the diagonal-polarization theorem again: `K_+` mixes the whole packet and its
projector is the terminal spectral projector that `J-SF3` proposed using.

On the actual Euler depth-zero block `P_X={p prime:2X<p<=5X}`,

```text
A_p^2 = log(p)/p,
h_p   = (1/2)log p,
D <= 1,
sum_(p in P_X) A_p^2 <= (5/2)log 4,
card(P_X) <= 5X log 4/log(2X).
```

Thus the complete unit-coordinate Jordan envelope satisfies

```text
sup_(|z_p|<=1) <z,K_+ z>
 <= (25/2)(log 4)^2 X/log(2X).                           (55)
```

At `X=m^4`, beyond the same symbolic threshold `exp(7201)<m`, `(55)` is strictly less than the
certified pure-bad mass square, which is at least `X/576`.  Trace scalarization is smaller still:
`Tr(K_+)=sqrt(Delta)=O(1)`.  Consequently the direct nonlinear positive part of the actual
calibrated exterior matrix cannot satisfy the domination half of `(2)`, even when its
target-selected projector is allowed.  A surviving `J-SF3` object must first construct a
different singular completed source operator; applying functional calculus to the known
rank-two seam is closed.

The determinant identity and rank-two spectral calculation are standard finite-dimensional
linear algebra.  New content is the exact weld of that full nonlinear positive part to the
Julia--Gamma amplitudes and the certified same-block first-clock lower bound.  Targeted arXiv
searches found general Hermitian positivity and bounded-rank spectral results, but no occurrence
of this exterior-matrix/weighted-prime/first-clock conjunction; external priority is not
certified.

Unconditional Lean module:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockExteriorPositivePartNoGo.lean
```

It now constructs the literal complex Hermitian matrix, proves its rank-two outer-product
factorization and exact cubic law `K^3=Delta K`, and uses the matrix C-star norm plus mathlib's
continuous functional calculus to construct the genuine Jordan positive part.  Its quadratic
energy is proved nonnegative and bounded by the variance envelope for every bounded-coordinate
state.  The file also proves the Gram determinant nonnegative, height-translation invariant,
bounded by the squared height diameter, the exact first-clock arithmetic ceiling, and the direct
operator-level strict same-block failure against the bad-mass square.  Thus the Lean theorem no
longer reasons through an unattached scalar surrogate.  No computation, RH input, `sorry`,
`admit`, `axiom`, `opaque`, or `unsafe` declaration occurs.

## 24. Moving positive-completion gauge rigidity
`[PAPER+LEAN-PROVED CLASS NO-GO] [NEW SOURCE-SPECIFIC UNIFORMITY]`

The fixed-meromorphic-gauge theorem does not by itself exclude a theta, Julia, Gamma, or
co-Poisson gauge which changes at every anisotropic mesh point.  This is not reassigned: it is the
moving part of `J-SF6`.

For the centered anisotropic mesh write

```text
z_n = xiCTaylorAnisotropicCenteredPoint sigma n,
x_n = xiTaylorAnisotropicHorizontalStep sigma n.
```

At each `n`, independently, let `h_n>=0` on the positive half-line and define

```text
G_n  = integral h_n(t)(1-exp(i t z_n)) dt,
G'_n = integral h_n(t)(-i t exp(i t z_n)) dt.
```

Suppose only that both integrals exist and that source value/derivative data `F_n,D_n` obey

```text
G_n  = -i z_n F_n,
G'_n = -i(F_n+z_n D_n),
F_n != 0.                                                 (56)
```

The density, total mass, moments, source depth, and phase lag may all vary without bound and need
not converge.  Positivity gives

```text
||G'_n|| <= Re(G_n)/Im(z_n) <= ||G_n||/Im(z_n).
```

Since `||z_n||>=Im(z_n)`, `(56)` and the triangle inequality imply the schedule-uniform bound

```text
|Im(D_n/F_n)| <= ||D_n/F_n|| <= 2/Im(z_n).               (57)
```

For `sigma.re<1/2`, `Im(z_n)` tends to the positive number `1/2-sigma.re`, while `x_n->0`.
Therefore

```text
x_n Im(D_n/F_n) -> 0.                                    (58)
```

Every superaccurate finite Xi Taylor schedule has exact mesh charge

```text
x_n Im(P'_n/P_n) -> m,
m=analyticOrderAt(xi,sigma).toNat.
```

Subtracting `(58)` yields

```text
x_n [Im(P'_n/P_n)-Im(D_n/F_n)] -> m.                     (59)
```

Thus an arbitrary moving positive-completion gauge screens exactly when `m=0`, equivalently
`xi(sigma)!=0`; at every hypothetical Xi zero it preserves the full positive multiplicity.

This applies literally to arbitrary simultaneous schedules

```text
L_n >= 0,  N_n > 0,
F_n = criticalLogPhaseTailPacketValue L_n N_n z_n,
D_n = criticalLogPhaseTailPacketDerivative L_n N_n z_n.
```

The negative derivative of each translated theta profile is positive, the two exact
integration-by-parts identities give `(56)`, and strict right-half-plane completion proves
`F_n!=0`.  Hence increasing positive theta/Prouhet/Haar depth at any rate cannot create the
mesh-scale phase velocity needed to transgress the divisor current.  This closes the
non-normal-moving positive-source escape left by fixed-gauge order quantization.

Classical parent facts are the positive-real derivative contraction and logarithmic-current
algebra.  New project content is their uniform application to arbitrary moving literal theta
packets on the exact Xi anisotropic divisor mesh.  Targeted primary-source searches found no
statement with this conjunction; external priority remains unverified.

Dependency-closed paper certificate:

```text
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
  route-j-moving-positive-completion-gauge-rigidity.md
```

Unconditional Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorMovingPositiveCompletionGaugeNoGo.lean
```

The remaining `J-SF6` object is sharply smaller but still live: it must use an indefinite signed
source density, a singular boundary term invalidating `(56)`, or a relation-valued pre-scalar
channel.  Any scalar moving gauge which succeeds must carry positive mesh charge
`x_n Im(D_n/F_n)->m`; mere growth of a positive source index cannot provide it.

The signed-density escape has a further exact quantitative obstruction.  For real `h`, define its
absolute completion mass

```text
V_h(z)=Re integral_0^infinity |h(t)|(1-exp(i t z))dt.
```

Direct integration of the same half-plane kernel gives

```text
||G'_h(z)|| <= V_h(z)/Im z.
```

For nonzero signed completion define the exact condition number

```text
kappa_h(z)=V_h(z)/||G_h(z)||.
```

Then `(56)` implies

```text
|Im(D/F)| <= (kappa_h(z)+1)/Im z.                        (60)
```

Here `kappa_h(z)` is source-visible cancellation conditioning: it compares total absolute completion
mass with the surviving signed completion before logarithmic division.  Positive densities have
`kappa<=1`; large `kappa` means positive and negative completion vectors nearly cancel.

At a hypothetical Xi zero of multiplicity `m`, exact screening forces gauge charge to tend to
`m`.  Put `eta=1/2-Re(sigma)>0`.  Combining `(60)` with the exact mesh bound
`x_n<2/(n+1)` proves

```text
(m eta/8)(n+1) < kappa_(h_n)(z_n)+1                   eventually.   (61)
```

Thus bounded, sublinear, or merely non-normal signed conditioning cannot screen a divisor.  Every
successful scalar signed-density transgression must be at least linearly ill-conditioned on the
literal `1/n` anisotropic mesh.  This moves the survivor again: it is now a linearly cancelling
signed source, a singular boundary term, or a relation-valued channel.

Unconditional Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorMovingSignedCompletionConditioningNoGo.lean
```

It proves the signed variation inequality, the conditioned logarithmic-current bound, exact
transfer of a screened Taylor charge to the gauge, and the eventual linear lower bound `(61)` for
the intrinsic ratio itself—not an arbitrarily inflated majorant.

## 25. Pointwise signed transgression is jet-universal

The conditioning obstruction is the end of the generic pointwise no-go, not the beginning of an
iteration with larger constants.  Put

```text
z=u+iy,  u>0,  T=pi/(2u),  r=exp(-Ty).
```

For real weights `a_1,...,a_4`, take signed completion atoms at
`T,2T,3T,4T`.  Their completion value `G` and derivative `H` obey

```text
| Re G |   |  1   1+r^2      1    1-r^4 | | a_1 |
| Im G | = | -r      0      r^3      0   | | a_2 |
| Re H |   | Tr      0    -3Tr^3     0   | | a_3 |
| Im H |   |  0    2Tr^2      0   -4Tr^4 | | a_4 |.       (62)
```

The determinant is

```text
4 T^2 r^6 (1+r^2)^2>0.                                  (63)
```

Hence four signed atoms interpolate every `(G,H) in C^2`.  With

```text
F=iG/z,  D=(iH-F)/z,
G=1,     H=i(m/delta+Im(1/z)),   delta>0,
```

the exact source connections hold and

```text
delta Im(D/F)=m.                                         (64)
```

Thus arbitrary pointwise moving signed or singular completions can reproduce any requested
divisor charge exactly.  This does **not** solve Route J: `(64)` places the target multiplicity in
the interpolated jet and is therefore a certified theatrical witness.  Its mathematical force is
classification.  No further theorem using only pointwise integrability, finite support, the two
source connections, or existence of a scalar logarithmic derivative can close the signed class.

Moreover the explicit inverse shows the linear conditioning law is sharp.  On any compact family
of points with `Re z>0`, choosing `delta->0` in `(64)` makes `H=O(1/delta)`, every weight in the
inverse of `(62)` is `O(1/delta)`, and `G=1`.  Hence the intrinsic absolute-mass condition number
is `O(1/delta)`, matching the already proved `Omega(1/delta)` screening lower bound.  No generic
pointwise argument can strengthen the linear obstruction to a superlinear one.

The surviving `J-SF6` hypothesis must now be global and source-bearing: one coherent
divisor-independent Gamma/theta/co-Poisson law must generate all mesh jets without receiving
`sigma`, its zero status, or its multiplicity as coefficient data.  Equivalently, any no-go must
use cross-mesh coherence or source independence; arbitrary per-mesh signed interpolation is
algebraically universal and receives no source-construction credit.

Dependency-closed paper certificate:

```text
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
  route-j-signed-quarter-turn-jet-controllability.md
```

Unconditional Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedAtomicJetControllability.lean
```

## 26. Scalar charge has a unique ray and reflection coherence selects the critical line

The four-atom theorem overstates the arity needed by the scalar charge target.  If `G=1` and
`H=iq`, the odd equations in `(62)` force `a_1=a_3=0`.  The remaining two weights are uniquely

```text
a_4=[1-(1+r^2)q/(2Tr^2)]/(1+r^2)^2,
a_2=q/(2Tr^2)+2r^2a_4.                                 (65)
```

Thus exact horizontal charge uses only atoms at `2T` and `4T`; multiplicity enters one affine
amplitude.  The value equation gives an exact cross-mesh fingerprint:

```text
delta a_2+(1-r^2)delta a_4=delta/(1+r^2).               (66)
```

If `delta_n->0`, `r_n->r_0>0`, and the normalized weights converge to `(b_2,b_4)`, then

```text
b_2+(1-r_0^2)b_4=0.                                    (67)
```

For the exact charge `q_n=m/delta_n+c_n`, with bounded connection correction and convergent
positive geometry,

```text
delta_n a_(4,n)
  -> -m/[2T_0 r_0^2(1+r_0^2)].                         (68)
```

This is nonzero when `m!=0`.  Therefore a common projective source direction at two fibres forces
their radii to agree, even when the normalized representatives differ by mesh scale.

On the Xi anisotropic mesh the radius is

```text
r(sigma)=exp[-pi(1/2-Re sigma)/(2 Im sigma)].           (69)
```

The functional-equation mate `1-conj(sigma)` has the reciprocal radius.  Consequently one
reflection-invariant coherent signed two-atom projective direction, common at both fibres and
carrying a nonzero charge, forces

```text
Re sigma=1/2.                                           (70)
```

This is not an RH proof and not a target-fitted construction.  It is a cross-fibre
superselection theorem: an off-line signed screen must break functional-equation reflection
equivariance in its leading normalized source weights, change support geometry, become singular,
or become relation-valued.  Those survivors remain Route J work; none is reassigned elsewhere.

Dependency-closed certificate:

```text
docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/
  route-j-signed-charge-ray-reflection-rigidity.md
```

The same unconditional Lean module proves scalar-jet uniqueness, `(66)`--`(70)`, the exact limit
`(68)`, and its nonvanishing.

## 27. Literal two-sided theta completion is an analytic unit at every Xi divisor

The canonical signed reflection escape is not generic.  Put

```text
A(z)=thetaCuspTailSecondDensityPhaseValue(z),
B(z)=A(z)+A(-z).
```

The already source-proved two-sided completion identity is

```text
(z^2+1/4)B(z)=1/2+4z^2 XiC(z).                         (71)
```

At an Xi divisor this becomes

```text
(z^2+1/4)B(z)=1/2.                                     (72)
```

Therefore `B(z)!=0`.  The new Lean module proves `B` is analytic throughout the open theta
Fourier--Laplace strip, so its local meromorphic order at every centered critical-strip Xi zero
is exactly zero.  The fixed-gauge charge classification then gives, for every source-selected
superaccurate Taylor schedule,

```text
transferred horizontal charge -> ord_sigma(xi),         (73)
```

not zero.  Hence the literal source-defined two-sided theta density cannot screen any nonzero Xi
divisor.  This is distinct from the positive one-sided no-go: `B` contains the reflected growing
channel, and `(72)`, not positivity, makes it a divisor unit.

Formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-two-sided-theta-completion-unit-no-go.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorThetaTailTwoSidedCompletionNoGo.lean
```

The surviving `J-SF6` signed class must now deform the canonical density/support law enough to
escape `(71)`, introduce a singular boundary term, or become relation-valued.  These are still
Route J survivors.

## 28. Arbitrary two-active-atom scalar screens phase-lock and reflect rigidly

Quarter-turn spacing is not responsible for the Section 26 critical-line selector.  For arbitrary
distinct positive support times `t_1,t_2` and nonzero real weights, write at `z=u+iy`

```text
G=sum_j a_j(1-exp(i t_j z)),
H=sum_j a_j(-i t_j)exp(i t_j z).
```

The scalar jet conditions `G=1`, `H=iq` have imaginary-value and real-derivative equations

```text
a_1 exp(-t_1 y)sin(t_1 u)+a_2 exp(-t_2 y)sin(t_2 u)=0,
a_1 t_1 exp(-t_1 y)sin(t_1 u)
  +a_2 t_2 exp(-t_2 y)sin(t_2 u)=0.                    (74)
```

Their determinant is the nonzero factor
`a_1 a_2 exp(-(t_1+t_2)y)(t_1-t_2)`, so

```text
sin(t_1 u)=sin(t_2 u)=0.                               (75)
```

Thus every genuinely two-active scalar screen, not only the quarter-turn inverse, lies on the
half-turn lattice.

Define the value and imaginary-derivative rows

```text
g_t(u,y)=1-exp(-ty)cos(tu),
d_t(u,y)=-t exp(-ty)cos(tu).                           (76)
```

If `delta a_j -> b_j` and `delta q -> m!=0`, exact mesh equations give

```text
g_(t_1)(u,y)b_1+g_(t_2)(u,y)b_2=0,
d_(t_1)(u,y)b_1+d_(t_2)(u,y)b_2=m.                    (77)
```

The second equation forces `(b_1,b_2)` nonzero.  At a reflected fibre,

```text
g_t(u,-y)=-cos(tu)exp(ty)g_t(u,y).                     (78)
```

Away from `y=0`, both value coefficients are nonzero.  If nonzero normalized rays at `y` and
`-y` are projectively equal, their two value rows are proportional.  Equation `(78)` then gives

```text
cos(t_1u)exp(t_1y)=cos(t_2u)exp(t_2y).
```

Squaring, using `(75)`, and using injectivity of `exp` yields
`(t_1-t_2)y=0`; distinct limiting support times force `y=0`.  On the Xi fibre
`y=1/2-Re sigma`, hence

```text
Re sigma=1/2.                                          (79)
```

This closes the complete convergent, separated, two-active-atom, reflection-projectively coherent
scalar class. It is a genuine support-independent advance over Section 26. It does not close
three-or-more active atoms, coalescing/escaping/nonconvergent support, projective symmetry
breaking, singular boundaries, or relation-valued channels. Those remain Route J work.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-arbitrary-two-atom-reflection-rigidity.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedTwoAtomReflectionRigidity.lean
```

## 29. Three atoms are the sharp reflection-coherent scalar escape

The Section 28 arity threshold is exact.  At

```text
z_+=2*pi/T+iy,     z_-=2*pi/T-iy,     r=exp(-Ty),
```

the three source times `T,2T,3T` have phases `r,r^2,r^3` and their reciprocals. Define

```text
B(r)=(-(1-r^3), 1-r^3, -r(1-r)).                      (80)
```

If `g_j(r)=1-r^j`, direct factorization gives

```text
g(r).B(r)=0,       g(1/r).B(r)=0.                     (81)
```

Unlike the two-atom case, the two reflected value rows have a common line. Its derivative charge
is

```text
M(T,r)=T r(1-r)^2(1-r^2),                             (82)
```

which is nonzero for `T>0`, `r>0`, `r!=1`. Moreover

```text
d(r).B(r)=M(T,r),
d(1/r).(r^3 B(r))=M(T,r).                             (83)
```

Normalize `b=B/M` and `c=r^3B/M`.  Both carry unit leading derivative charge, lie in their
respective value kernels, and are projectively equal.  The first two atom columns have correction
determinant

```text
Delta(T,r)=T r(1-r)^2!=0.
```

Solving those two columns adds bounded corrections which make the completion value exactly one
and its derivative exactly

```text
H_+=i(1/delta+Im(1/z_+)),
H_-=i(1/delta+Im(1/z_-)).
```

The source connections then give, for every `delta>0`,

```text
delta Im(D_+/F_+)=1,
delta Im(D_-/F_-)=1.                                  (84)
```

The normalized exact weights converge to `b` and `c=r^3b`, so all three projective minors vanish
off the centered line.  Thus reflection-projective coherence by itself is not selective once
three atoms are active.

This is an actual positive survivor, not permission to stop.  It does not insert an Xi zero or
target multiplicity, but it is not yet the canonical theta/prime--Gamma density.  Route J must
now prove that `(80)` cannot occur under that source law, or construct its source-faithful lift
and then solve the multiplicity/global-budget gates.  Calling this survivor another route would
leave `J-SF6` open.

Formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-three-atom-reflection-coherence-escape.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedThreeAtomReflectionEscape.lean
```

## 30. Literal reflected source profiles have a sharp four-atom threshold

Projective equality is weaker than one source law. A literal finite signed multiplier has one
coefficient vector at both reflected fibres; it cannot replace that vector by `r^3` times itself.
For weights `a_1,...,a_N`, encode the full-turn rows by

```text
Phi_a(X)=sum_(j=1)^N a_j(1-X^j).                       (85)
```

Then `Phi_a(1)=0`. At reciprocal damping radii `r` and `q=1/r`, equal reflected leading charge
`m` means

```text
Phi_a(r)=Phi_a(q)=0,
T r Phi_a'(r)=T q Phi_a'(q)=m.                         (86)
```

For `N<=2`, the three distinct roots `1,r,q` force `Phi_a=0`. For `N=3`,

```text
Phi_a(X)=C(X-1)(X-r)(X-q).
```

The derivative equality in `(86)` becomes

```text
C(r-1)(r-q)(r-r^(-2))=0.                              (87)
```

When `r>0` and `r!=1`, every displayed factor except `C` is nonzero. Thus `C=0` and `m=0`.
This kills the Section 29 ray under the literal same-profile requirement.

The obstruction is sharp. Define

```text
s(r)=(1-r^5)/[r(1-r^3)]
    =(1+r+r^2+r^3+r^4)/[r(1+r+r^2)],

P_r(X)=(X-1)(X-r)(X-r^(-1))(X-s(r)).                  (88)
```

All four roots are distinct, since

```text
s-r=(1+r)/[r(1+r+r^2)],
s-r^(-1)=r^2(1+r)/(1+r+r^2),
s-1=(1+r^4)/[r(1+r+r^2)].                             (89)
```

The defining formula for `s` is exactly the weighted derivative identity

```text
r P_r'(r)=r^(-1)P_r'(r^(-1)).
```

Its common charge is

```text
M(T,r)=T r P_r'(r)
      =-T(r-1)^2(r+1)^2/[r(1+r+r^2)] != 0.            (90)
```

Writing `P_r=Phi_B` and normalizing `b=B/M` gives one common vector satisfying both value-kernel
conditions and unit derivative charge. A real Hermite interpolant `Q`, uniquely determined by

```text
Q(1)=0,
Q(r)=Q(r^(-1))=1,
T r Q'(r)=eta_+,
T r^(-1)Q'(r^(-1))=eta_-,                             (91)
```

has degree at most four: the homogeneous kernel would have the five roots counted with
multiplicity `1,2,2`. Encoding `Q=Phi_v` and putting

```text
a(delta)=b/delta+v
```

therefore gives one and the same four-vector at both fibres, with exact source-connection data

```text
G_+=G_-=1,
H_+=i(1/delta+Im(1/z_+)),
H_-=i(1/delta+Im(1/z_-)),
delta Im(D_+/F_+)=delta Im(D_-/F_-)=1.                (92)
```

Coordinatewise, `delta a(delta)->b`. Hence the sharp thresholds differ:

```text
projective reflected coherence: three atoms;
one literal equal-charge reflected source profile: four atoms. (93)
```

This is a real survivor, not Route-J closure. `T,y` still choose one full-turn pair, and no
canonical theta/prime--Gamma law or global Julia budget has been proved. The next scalar attack
must use canonical source coefficients across the whole Xi mesh; three-atom projective geometry
is no longer the open core.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-literal-reflection-profile-four-atom-threshold.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedFourAtomLiteralReflectionEscape.lean
```

## 31. The four-atom profile encodes exactly one transverse orbit

`[PAPER+LEAN-PROVED CLASSIFICATION] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

The arity-four survivor is not a free reflection-symmetric source profile. Write

```text
Phi_a(X)=sum_(j=1)^4 a_j(1-X^j),   x=r+r^(-1).
```

For `T!=0`, `r>0`, and `r!=1`, suppose

```text
Phi_a(r)=Phi_a(r^(-1))=0,
T r Phi_a'(r)=T r^(-1) Phi_a'(r^(-1)).
```

Direct symmetric coefficient elimination proves that the complete solution space, including the
zero vector, is the line

```text
a1=-a4 B1(r),   a2=-a4 B2(r),   a3=-a4 B3(r),

B1(r)=x(1+x),   B2(r)=-x(x+2),
B3(r)=x(2x+3)/(1+x),   B4(r)=-1.                       (94)
```

The classification is stronger than the existence theorem: no nonzero-charge hypothesis is
needed to put the vector on the canonical line. Moreover

```text
B3(r)-B3(t)
 = (x-y) (2 + 1/((1+x)(1+y))),   y=t+t^(-1).           (95)
```

For positive radii the second factor is positive. Hence equality of the third canonical
coordinate gives `r+r^(-1)=t+t^(-1)`, equivalently

```text
(r-t)(rt-1)=0.                                         (96)
```

Therefore one literal four-atom vector carrying nonzero equal charge at `r` cannot even satisfy
the zero-value/equal-charge rows at a second positive off-center radius unless
`t=r` or `t=r^(-1)`. The support records `T`, while the coefficient ray records
`{r,r^(-1)}` and therefore `|y|` when `r=exp(-Ty)`.

This is genuine source-provenance progress, not Route-J closure. Minimal finite support now has
transverse information capacity exactly one: a canonical source construction must predict the
orbit rather than fit it from the divisor. The remaining open scalar mechanisms are
larger/unbounded support, non-atomic or singular carriers, broken leading reflection, and
relation-valued channels; all remain Route J until constructed or eliminated class-completely.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-four-atom-transverse-orbit-rigidity.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedFourAtomTransverseOrbitRigidity.lean
```

## 32. Actual continuum phase rows require three phase-weighted sign changes

`[PAPER+LEAN-PROVED NO-GO] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

The full-turn polynomial reduction does not extend directly to a non-atomic physical-time
density: away from the discrete phase lattice, the Fourier carrier `sin(u t)` is nonzero. Let
`mu` be atomless, let `h` be real, and fix `c>0` and a real carrier frequency `u`. Assume
almost every nonzero source point has `t>0` and `sin(u t)!=0`. The actual imaginary-value and
real-derivative rows at the two reflected fibres are

```text
S_q(t)=h(t)exp(q t)sin(u t),
R_q(t)=t h(t)exp(q t)sin(u t),       q=+c,-c.
```

Assume all four are integrable and

```text
integral S_c dmu = integral S_(-c) dmu = 0,
integral R_c dmu = integral R_(-c) dmu = 0.
```

These equations are necessary for a literal scalar leading jet: they are respectively its
imaginary-value and real-derivative components at the two fibres. Put

```text
v(t)=cosh(c t)sin(u t)h(t).
```

Sums of the two value and derivative rows, followed by the value-row difference, prove

```text
integral v dmu = integral t v dmu
               = integral tanh(c t)v(t) dmu = 0.       (97)
```

The last identity uses the exact physical source reduction

```text
tanh(c t)cosh(c t)=sinh(c t).                          (98)
```

Suppose the phase-weighted source has at most two sign changes: for some `0<a<b`, either
`(t-a)(t-b)sin(u t)h(t)>=0` almost everywhere or the reversed inequality holds. The function
`g(t)=tanh(c t)` is strictly concave on the positive half-line. Its chord residual has signs
`-,+,-`, opposite to the first orientation of `sin(u t)h(t)`; the reversed orientation is handled
by `-v`. Equation (97) makes the residual-weighted integral zero while its integrand has one weak
sign. Strict chord separation and atomlessness remove the two endpoints, giving `v=0` almost
everywhere. Positivity of `cosh` and exclusion of sine nodes then give

```text
h=0  mu-almost everywhere.                             (99)
```

Thus this three-row reduction proves that every nonzero actual non-atomic reflected scalar source
needs at least three alternating sign changes in `sin(u t)h(t)`, even with unbounded support. On one open half-turn chamber the
sine has constant sign, so these are changes of `h`. The finite full-turn survivor lies exactly
on sine nodes; it is a phase-node singular escape, not an atomless sharpness witness. Section 33
uses the fourth row to close the three-change regular class. Phase-node/singular measures remain
Route J.

The general Chebyshev-system sign-change principle and strict-concavity chord argument are
classical. Candidate new content is only the exact physical reflected-row reduction to
`span{1,t,tanh(c t)}`, the carrier-weighted invariant, and the phase-node singularity boundary.
Targeted internal and external audits found the general theory but not this source-row
conjunction. An earlier radial draft suppressing `sin(u t)` is explicitly withdrawn as a claim
about non-atomic physical time; its Lean result remains only the analytic core used here.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-continuum-three-sign-change-obstruction.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumSignComplexityNoGo.lean
```

## 33. All four continuum rows require four phase-weighted sign changes

`[PAPER+LEAN-PROVED NO-GO] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

Section 32 discarded one linear combination of the four physical rows and therefore did not
reach the full source constraint. Write

```text
p(t)=sin(u t)h(t).
```

The four reflected imaginary-value and real-derivative equations are exactly

```text
integral exp(c t)p(t) dmu = integral t exp(c t)p(t) dmu = 0,
integral exp(-c t)p(t) dmu = integral t exp(-c t)p(t) dmu = 0.   (100)
```

For arbitrary proposed change points `0<a<b<d`, consider

```text
J(t)=(A+B t)exp(2c t)+C+D t.                            (101)
```

Evaluation at `a,b,d` maps four coefficients to three values, so rank-nullity supplies a nonzero
`J` vanishing at all three points. It cannot have a fourth distinct root. Four roots of `J` would
give three roots of `J'` by Rolle and then two distinct roots of

```text
J''(t)=exp(2c t)
  (4c B+4c^2(A+B t)).                                   (102)
```

The affine factor in `(102)` cannot have two distinct roots unless `A=B=0`; two original roots
then force `C=D=0`, contradiction. A strengthened two-interval Rolle argument also shows
`J'(a),J'(b),J'(d)` are nonzero. Hence these are the complete zero set and `J` alternates at each
root. Globally on `t>0`, either

```text
(t-a)(t-b)(t-d)J(t)>=0                                  (103a)
```

or the reversed inequality `(103b)` holds.

Now set

```text
W(t)=J(t)exp(-c t)p(t).
```

Exact expansion gives

```text
W(t)=A exp(c t)p(t)+B t exp(c t)p(t)
    +C exp(-c t)p(t)+D t exp(-c t)p(t).                 (104)
```

Thus `(100)` makes `W` integrable with zero integral. If `p` has at most three alternating sign
changes at `a,b,d`, its cubic sign certificate combined with `(103)` makes `W` one-signed.
Therefore `W=0` almost everywhere. Atomlessness removes `a,b,d`; the test has no other roots;
the exponential is positive; and source support excludes carrier nodes. Consequently

```text
h=0  mu-almost everywhere.                              (105)
```

Every nonzero regular atomless reflected source must therefore have at least four changes in
`sin(u t)h(t)`. On a single open half-turn chamber it must have at least four changes of `h`.
Support may be unbounded.

This is genuine frontier movement over Section 32: the unused derivative-row difference closes
the entire three-change class. It does not close Route J. Four-or-more phase-weighted changes,
phase-node mass, singular measures, coalescing/escaping/nonconvergent atoms, broken reflection,
and relation-valued carriers remain live and stay on this card.

General exponential-polynomial Chebyshev and sign-change theory is classical. Candidate new
content is only the exact four-row Route-J reduction `(100)--(104)` and its source-specific
four-alternation consequence. Internal corpus search found no such four-row result; targeted
external searches found only general ECT/sign-change theorems. No claim is made that rank-nullity,
Rolle rigidity, or the abstract Chebyshev principle is new.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-continuum-four-phase-variation-obstruction.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumFourVariationNoGo.lean
```

## 34. The four-change regular boundary is attained exactly

`[PAPER+LEAN-PROVED SURVIVOR] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

The Section 33 lower bound is exact, so stronger row-only sign-variation conjectures are false.
For arbitrary `c,u>0`, set

```text
L=pi/(6u),   r=exp(cL),
I_j=(L/4+jL,3L/4+jL],   j=0,...,4.                    (106)
```

All five intervals are disjoint and lie in one open sine chamber because
`u(5L)=5pi/6<pi`. Let `b_j` be their indicator functions and use the reciprocal double-root
polynomial

```text
A(X)=(X-r)^2(X-r^(-1))^2
    =sum_(j=0)^4 a_j X^j,                              (107)
```

with

```text
(a_0,...,a_4)
=(1,-2(r+r^(-1)),r^2+r^(-2)+4,-2(r+r^(-1)),1).        (108)
```

Define

```text
p(t)=sum_(j=0)^4 a_j b_j(t),
h(t)=p(t)/sin(ut) on the chamber, zero at sine nodes.  (109)
```

The source is nonzero on the positive-length interval `I_0`, compactly supported, and carries no
phase-node mass. If

```text
V(q)=integral exp(qt)b_0(t)dt,
T(q)=integral t exp(qt)b_0(t)dt,
```

translation invariance gives

```text
integral exp(qt)p(t)dt
 =V(q)A(exp(qL)),

integral t exp(qt)p(t)dt
 =T(q)A(exp(qL))
  +L V(q)exp(qL)A'(exp(qL)).                           (110)
```

At `q=c,-c`, the argument of `A` is respectively `r,r^(-1)`. Both are double roots, so all four
physical value/derivative rows vanish exactly.

The coefficients in `(108)` alternate `+,-,+,-,+`. The quartic with roots between the bumps has
the same pattern:

```text
(t-L)(t-2L)(t-3L)(t-4L) sin(ut)h(t)>=0
for every real t.                                      (111)
```

Thus the source has at most four phase-weighted changes. It has no cubic certificate: Section 33
would then force `h=0` almost everywhere, contradicting positivity on `I_0`. Hence it has exactly
four.

This survivor creates a hard boundary, not closure. Local reflected rows, atomlessness,
integrability, compact support, exclusion of sine nodes, and sign complexity are now exhausted:
they permit an exact regular source. The next theorem must use cross-mesh source provenance. The
mask `(107)` depends on local `c,u`, so it is not a divisor-independent theta/prime--Gamma law and
receives no RH-construction credit. Route J must either produce this or another exact-four-change
family from one pre-divisor source law, or exclude every such coherent family class-completely.
Phase-node/singular and relation-valued carriers remain live in parallel.

Exponential vanishing-moment translate masks are classical wavelet technology. Candidate new
content is only the exact weld of the reciprocal double roots, both reflected physical fibres,
one Fourier sine chamber, and the already proved Route-J variation lower bound. Internal audit
found no compact atomless extremizer; external audit found general exponential-moment wavelets,
not this source-specific conjunction.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-continuum-four-variation-sharpness.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumFourVariationEscape.lean
```

## 35. The sharp five-translate regular class is one-damping rigid

`[PAPER+LEAN-PROVED NO-GO] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

Section 34 exhibited one five-bump mask fitted to the local radius. This section classifies every
coefficient vector on that fixed support geometry. Let

```text
p_a(t)=sum_(j=0)^4 a_j b(t-jL),
A_a(X)=sum_(j=0)^4 a_j X^j,                            (112)
```

where `L>0` and `b=1_((L/4,3L/4])`. For

```text
V(q)=integral exp(qt)b(t)dt,
T(q)=integral t exp(qt)b(t)dt,
```

translation gives, for arbitrary `a`,

```text
integral exp(qt)p_a(t)dt
  =V(q)A_a(exp(qL)),

integral t exp(qt)p_a(t)dt
  =T(q)A_a(exp(qL))
   +L V(q)exp(qL)A_a'(exp(qL)).                        (113)
```

The base transform is strictly positive for every real `q`. Therefore, with
`r=exp(cL)>1`, the four reflected physical value/first-moment rows vanish if and only if

```text
A_a(r)=A_a'(r)=A_a(r^(-1))=A_a'(r^(-1))=0.            (114)
```

The two radii are distinct and `deg A_a<=4`, so the entire coefficient kernel is the single ray

```text
A_a(X)=a_4 (X-r)^2(X-r^(-1))^2.                       (115)
```

Equivalently,

```text
(a_0,...,a_4)
=a_4(1,-2(r+r^(-1)),r^2+r^(-2)+4,-2(r+r^(-1)),1).     (116)
```

This is not merely a classification of the displayed survivor: `(113)--(116)` begin with an
arbitrary real five-vector and prove there are no other physical masks.

If the same nonzero coefficient vector also serves a second positive noncentral radius `s`,
comparison of `(116)` at `r` and `s` gives

```text
r+r^(-1)=s+s^(-1),
(r-s)(rs-1)=0.                                         (117)
```

Hence `s=r` or `s=r^(-1)`. On the physical branch `r,s>1`, only `s=r` survives. At fixed
positive spacing, if one nonzero five-bump source cancels the rows at positive dampings `c,d`,
then

```text
exp(cL)=exp(dL),  hence c=d.                            (118)
```

Thus the sharp regular extremizer is necessarily target-informative: its support spacing fixes
the carrier scale and its coefficient ray fixes the damping orbit. A catalogue that rebuilds
`(116)` from each divisor is not one pre-divisor source law.

This closes only the fixed-spacing, identical-five-translate class. It does not close Route J.
Variable support geometry, nonidentical bumps, six-or-more translate masks, arbitrary four-change
densities, one-prime phase-node towers, other singular measures, reflection-breaking profiles,
and relation-valued carriers remain researchable and stay on this card.

Exponential finite differences, exponential-spline cancellation operators, and prescribed-root
factorization are classical. Candidate new content is only their exact physical Route-J weld:
both reflected Fourier--Laplace value/first-moment rows, complete minimal-kernel classification,
and the one-positive-damping source-provenance consequence.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-five-translate-source-provenance-rigidity.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedContinuumFiveTranslateRigidity.lean
  XiCTaylorSignedContinuumFiveTranslatePhysicalRigidity.lean
```

## 36. Prime-power phase-node sources have arithmetic rank one

`[PAPER+LEAN-PROVED CLASSIFICATION] [CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`

The full-turn survivor suppresses the sine rows by placing every active delay on a phase node.
Literal prime--Gamma provenance makes this arithmetic. Let `u!=0`, let `p!=q` be primes, and let
`a,b>0` be integers. If

```text
sin(u a log p)=sin(u b log q)=0,
```

then integers `m,n` satisfy

```text
m pi=u a log p,   n pi=u b log q.                      (119)
```

Cross-multiplication gives

```text
u(a n log p-b m log q)=0.                              (120)
```

Since `u!=0`, unique factorization makes the two integer coefficients vanish:

```text
a n=0,   b m=0.
```

Thus `m=n=0`, and `(119)` contradicts `u a log p!=0`. Therefore prime-power delays from distinct
prime bases cannot both be phase nodes at one nonzero carrier.

For an arbitrary real multiplier `A(p,e)` on delays

```text
log(p^(e+1))=(e+1)log p,
```

let

```text
P(A)={p : exists e, A(p,e)!=0}.
```

If every active atom of `A` is a phase node, the two-prime theorem gives the exact classification

```text
P(A) is subsingleton.                                  (121)
```

Equivalently, every phase-node multiplier must censor at least one atom from every pair of
distinct prime bases. The literal Suzuki/von-Mangoldt far-hinge source has weight

```text
w(p,e)=Lambda(p^(e+1))/sqrt(p^(e+1))
      =log(p)/sqrt(p^(e+1))>0                          (122)
```

at every prime power. Its prime-two and prime-three depth-zero atoms are both active, contradicting
`(121)`. Hence the updated manuscript's uncensored far-hinge source cannot realize the Route-J
phase-node singular escape at any nonzero carrier.

This is a real source-provenance no-go, not full singular closure. One-prime towers are sharp
survivors because all their delays are commensurate. Arbitrary singular boundary measures,
non-prime-power singular support, broken reflection, and relation-valued channels remain live.

Prime-log independence and sine-node arithmetic are classical. Candidate new content is only the
exact Route-J rank-one source classification `(121)` and its application `(122)` to the literal
Suzuki/von-Mangoldt far-hinge source. Targeted literature search found semilocal finite-place and
single-prime moment theory, but not this source-specific obstruction.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-prime-power-phase-node-source-rigidity.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedPrimePhaseNodeSourceNoGo.lean
```

## 37. Prime-power phase-node profiles are local Euler data

`[PAPER+LEAN-PROVED CLASS NO-GO] [CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

The source-resolution theorem in

```text
../4-publication-ready/source-horizon-riemann-divisor/main.tex
```

sharpens Section 36. Its global prime-clock carrier is the quotient

```text
Q = {all complex prime-power profiles}
    / {profiles active on finitely many prime rays}.      (123)
```

Section 36 proves that every prime-power phase-node multiplier at `u!=0` has active prime support
of cardinality at most one. Therefore every such profile, including an infinite one-prime tower,
lies in the local subspace in `(123)`:

```text
[A]=0 in Q.                                               (124)
```

For a finite-abscissa positive-prime-power arithmetic profile, the exact source--analytic
correspondence gives the analytic strengthening

```text
L(A) belongs to the coordinate field generated by
the rational coordinate and every finite-prime Euler germ. (125)
```

Thus the formerly surviving scalar one-prime phase-node tower is not a global relative source
direction. This conclusion uses no finite-depth, boundedness, valuation-polynomial, or finite-Rees
hypothesis. The discarded valuation-order calculation would only refine an already excluded
finite-Rees subcase and is not counted as research progress.

The precise surviving boundary is now smaller:

1. non-prime-power singular boundary support;
2. reflection-breaking scalar profiles outside the phase-node class;
3. relation-valued or non-scalar carriers outside the prime-clock quotient;
4. variable/nonidentical/higher-arity regular profiles not eliminated by canonical source
   provenance.

This is not Route-J closure; each item remains owned here.

Dependency-closed formalized certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-phase-node-local-euler-quotient-no-go.md

formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedPrimePhaseNodeLocalEulerNoGo.lean
```

## 38. J-SF5 has a double-root source critical potential

`[PAPER-PROVED ARCHIMEDEAN CLASSIFICATION] [LEAN-PROVED EXACT SOURCE REDUCTION]`

The explicit archimedean prolate parity matrices are in the exceptional Jacobi regime

```text
rho_n asymp 4n^2,   q_n asymp -8n^2,   |q_n|/rho_n -> 2.  (126)
```

Applying the published exceptional power-asymptotic classification to their exact next
coefficients proves a sharp transition:

```text
lambda>0 : each parity block is limit-circle, deficiency (1,1);
lambda=0 : each parity block is limit-point, deficiency (0,0). (127)
```

Thus the transported archimedean control carries two genuine boundary angles at every positive
prolate parameter. Essential self-adjointness cannot be imported into the semilocal source.

More importantly, the new unconditional Lean module

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateCriticalPotential.lean
```

isolates the exact semilocal datum which decides the same double-root transition. For four
consecutive Jacobi radii put

```text
R=x_0x_1-x_1^2-x_2^2+x_2x_3.
```

Then

```text
2R=(x_3^2-x_2^2)-(x_1^2-x_0^2)
   -(x_3-x_2)^2-(x_1-x_0)^2.                            (128)
```

Writing the squared-increment anomaly as

```text
delta_n=a_(n+1)^2-a_n^2-[2(n+1)+1/2],
```

the parity quartet beginning at `2k` satisfies

```text
2R=4+delta_(2k+2)-delta_(2k)
   -(a_(2k+3)-a_(2k+2))^2
   -(a_(2k+1)-a_(2k))^2.                                (129)
```

Diagonal plus the two adjacent parity off-diagonals is exactly the grading contribution plus this
`R`.  Hence the unresolved semilocal limit-point/limit-circle problem is not the already-known
quadratic growth of the off-diagonal.  It is the asymptotic competition in `(129)` between the
metaplectic-anomaly second difference, two increment energies, and the positive linear grading.

This step does not close `J-SF5`.  It replaces a vague “sharper boundary analysis” with one exact
source invariant.  Remaining hard theorem: determine `(129)` for the literal finite-prime Euler
measure, derive the source-selected boundary if limit-circle, and pass its relative resolvent
through the Sonin corner.

Paper proof and honest novelty classification:

```text
docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/
  archimedean-prolate-jacobi-limit-circle-transition.md
```

## 39. J-SF5 one-prime grading has an exact discrete-scale profile

`[PAPER+LEAN-PROVED SOURCE-LOCAL THEOREM]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

The previous one-prime theorem gave only

```text
|C_(k,p)| asymp_p k^(-3/4).
```

It discarded the prime-lattice position of the dominant frequencies. The new exact theorem
recovers it. For

```text
B_(k,p)(M)
 = p^(-M/2) phi(M log p) tanh(M log p)^(2k),
R_(k,p)=sum_(M>=0) B_(k,p)(M),
```

and every positive integer `c`,

```text
sqrt(c p^(2j)) R_(c p^(2j),p) -> F_p(c),                (130)
```

where

```text
F_p(c)
 = sum_(z in Z) sqrt(2c) p^(-z) exp(-4c p^(-2z)) > 0.  (131)
```

Both halves of `(131)` have unconditional geometric majorants. The positive offsets use
`2 sqrt(c) p^(-s)`; negative offset `-D` uses `p^(-D)`. Tannery's theorem therefore yields the
full bilateral limit, not a formal saddle approximation. The literal coefficient satisfies

```text
sqrt(k) |C_(k,p)| / [P_p c_(2k)] -> F_p(c)
along k=c p^(2j),                                        (132)
P_p=2/(1-p^(-1)).
```

The profile has exact discrete-scale invariance

```text
F_p(c p^2)=F_p(c).                                       (133)
```

Lean also proves absolute summability and strict positivity of the profile.

The updated `source-horizon-riemann-divisor/main.tex` prevents overclaiming this theorem. A fixed
one-prime profile is in `A_fin`, is zero in the global source-clock quotient, and has analytic
carrier in `K_loc`. Thus `(130)--(133)` do not construct a global relative current. They identify
the literal label-sensitive local datum which a successful cofinal semilocal boundary must
preserve. Any global `J-SF5` construction must transport these prime-resolved profiles through an
infinite-label cofinal limit or a topology singular relative to canonical source norms.

This moves but does not close `J-SF5`. Remaining hard theorem: propagate `(131)` through
finite-set orthogonalization, evaluate the critical residual `(129)` on a cofinal source family,
and derive or exclude a source-selected extension through the Sonin corner.

Dependency-closed certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-one-prime-geometric-grading-profile.md

formal/GaloisForLFunctions/RHTower/
  SoninSemilocalGradingGeometricProfile.lean
```

## 40. J-SF5 first Euler orthogonalization has a sharp `p^2` boundary

`[PAPER+LEAN-PROVED SOURCE-LOCAL THEOREM]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

The one-prime Lambert moment matrix has literal first source coefficient

```text
[q] c(2k,q)=2(-1)^k(1/2)^(2k).
```

In the archimedean orthonormal polynomial basis this is the signed rank-two tangent formed from

```text
eta_0(m)=2^(-m)sqrt((2m)!)/m!,
eta_0(m)^2=4^(-m)binom(2m,m).
```

Its trace recovers the published normalized determinant jet

```text
Delta'_n(0)=2sqrt(2) sum_(j=0)^n alpha_j,
alpha_j=(-4)^(-j)binom(2j,j).
```

The new theorem propagates that exact determinant tangent through the determinant quotient for
the positive Jacobi radii and then through the four-radius critical residual `(128)`. If `J_k`
denotes the resulting first Euler jet, then

```text
J_(n+1)/sqrt(2(n+1)) -> 4sqrt(2/pi).                   (134)
```

The proof is not based on a freely chosen linear deformation. Lean proves that every genuine
normalized matrix path with the literal source tangent has the same determinant derivative, and
that every determinant family with those jets has the same critical-residual derivative,
independently of all higher Euler coefficients.

The exact factorization is

```text
J_k=sqrt(2)c_(2k)B_(2k),                               (135)
c_m=4^(-m)binom(2m,m),
B_m/m -> (-1)+(-1)+6=4.                                (136)
```

Wallis' law `sqrt(m)c_m->1/sqrt(pi)` gives `(134)`. Thus the first Euler correction is order one
when

```text
q sqrt(n) asymp 1,
n asymp p^2 for q=p^(-1).                              (137)
```

This is a sharp first-jet boundary law, not a claim about uniformity of the full `q`-series. The
`q^2` and higher critical coefficients remain live and must now be determined.

The latest complete shell-field theorem in

```text
../4-publication-ready/source-horizon-riemann-divisor/main.tex
```

adds a second non-negotiable constraint. Arbitrary nonempty field meets and joins reproduce source
intersections and unions exactly, every ordinary field observable has finite shell support, and no
infinitary ghost is created by differential-field completion. Therefore adjoining all fixed-prime
boundary germs cannot construct the global J-SF5 current. A successful global object must be a
genuine pro-limit, relation-valued carrier, or topology singular relative to the direct-sum local
norm. This narrows the survivor but does not close it.

Dependency-closed certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-semilocal-prolate-first-euler-critical-boundary.md

formal/GaloisForLFunctions/RHTower/
  SemilocalProlateFirstEulerCriticalJet.lean
```

Remaining hard theorem: derive the exact higher-Euler critical-residual growth, decide whether
all orders share and resum on `(137)`, propagate the boundary layer through finite-prime
orthogonalization, and realize or eliminate the resulting infinite-label singular carrier through
the Sonin corner.

## 41. J-SF5 second Euler order confirms the `p^2` boundary

`[PAPER+LEAN-PROVED SOURCE-LOCAL THEOREM]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

Write the positive one-prime Jacobi radius as

```text
a_n(q)=r_n+u_nq+v_nq^2+O(q^3)
```

and let `K_k` be the `q^2` coefficient of four-radius critical residual `(128)`. Published
squared-radius coefficient contains

```text
Y_n={}_2F_1(1,n+1/2;n+1;-1).
```

New proof constructs `Y_n` as an actual normalized alternating central-binomial tail and proves

```text
1/2 <= Y_n <= 1/2+1/(4n+4).                            (138)
```

Literal published bracket then cancels to give

```text
[q^2]a_n(q)^2/(n+1) -> 16/pi,
u_n^2/(n+1) -> 8/pi,
v_n -> 4/pi.                                           (139)
```

In four-radius weld, all six terms linear in `v_n` cancel at degree scale. First jets alternate
and have squared normalized amplitude `8/pi`; two cross-products and two squares therefore
contribute four copies of `-8/pi`. Thus

```text
K_(n+1)/(2(n+1)) -> -32/pi.                            (140)
```

Together with `(134)`, both proved Euler orders become order one at same scale:

```text
q sqrt(n) asymp 1,   q^2 n asymp 1,
n asymp p^2 for q=p^(-1).                              (141)
```

This is new critical-residual information, not a restatement of published `q^2` anomaly. It proves
persistence through order two only. It does not justify all-orders law or resummation, and it does
not construct a global carrier. Fixed-prime data remain quotient-zero; complete shell
finite-support rigidity rules out promotion by ordinary differential-field completion.

Dependency-closed certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-semilocal-prolate-second-euler-critical-boundary.md

formal/GaloisForLFunctions/RHTower/
  SemilocalProlateSecondEulerCriticalJet.lean
```

Route J remains open. Immediate hard frontier: extract literal `q^3` squared-radius coefficient,
determine whether critical `q^3` weld has `n^(3/2)` growth, then attack fixed-order induction or
boundary-layer resummation. After that, finite-prime orthogonalization and genuine infinite-label
singular carrier remain unavoidable.

## 42. J-SF5 third Euler order breaks the `p^2` pattern

`[PAPER+LEAN-PROVED SOURCE-LOCAL THEOREM]`
`[CANDIDATE SOURCE-SPECIFIC NEW SCIENTIFIC KNOWLEDGE]`

Published `q^3` determinant-ratio formula contains new `ell=1` trace atom. Its direct relative
squared-radius contribution factors exactly as

```text
(-1)^n T_nD_n,
T_n=2sqrt(2)4^(-n)binom(2n,n),
D_n=16n^2+20n+5+1/(4n+4).                              (142)
```

This polynomial is absent at orders one and two. Products of lower-order parity traces are only
order `sqrt(n)`, while `(142)` is order `n^(3/2)`. Consequently

```text
(-1)^n[q^3]a_n(q)^2/((n+1)^3sqrt(n+1))
  ->32sqrt(2/pi),                                      (143)

(-1)^n[q^3]a_n(q)/((n+1)^2sqrt(n+1))
  ->16sqrt(2/pi).                                      (144)
```

Pointwise `(144)` is not differentiated heuristically. For exact dominant amplitude
`F_n=r_nT_nD_n/2`, source ratios give

```text
(n+1)(r_(n+2)/r_n-1) ->2,
(n+1)(c_(n+2)/c_n-1) ->-1,
(n+1)(D_(n+2)/D_n-1) ->4,                             (145)
```

so

```text
(F_n-F_(n+2))/((n+1)sqrt(n+1))
  ->-80sqrt(2/pi).                                     (146)
```

Two such differences survive in four-radius weld. Radius-curvature terms, exact subleading
`n^(3/2)` remainder stencil, and all mixed first/second-jet terms vanish at critical scale. If
`H_k=[q^3]R_k(q)` and `m_n=2(n+1)`, then

```text
H_(n+1)/((m_n+1)^2sqrt(m_n+1))
  ->-160sqrt(2/pi).                                    (147)
```

Thus third Euler correction becomes order one at

```text
q^3n^(5/2) asymp1,
n asymp p^(6/5),                                       (148)
```

strictly before `p^2`. Order-one/order-two agreement was exceptional. Naive fixed-order law
`[q^r]R_n=O(n^(r/2))` is false at `r=3`.

Dependency-closed certificate:

```text
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/
  route-j-semilocal-prolate-third-euler-critical-boundary.md

formal/GaloisForLFunctions/RHTower/
  SemilocalProlateThirdEulerCriticalJet.lean
```

Route J remains open. New immediate frontier is not “confirm `p^2`”: classify source atoms at
orders `r>=4`, determine lower envelope of interaction exponents, and decide whether complete
one-prime Euler series has any nontrivial uniform degree window. Finite-prime orthogonalization,
source-selected extension, Sonin-corner resolvent transport, and genuine infinite-label singular
carrier remain unresolved.

## 43. Primitive-promoted modular exterior and Gamma-anchor shorting

`[PAPER+LEAN-PROVED SOURCE CONSTRUCTION]`
`[OPEN COFINAL BUDGET]`

The minimum `sqrt(log X)` singularity from Section 22 is now constructed from the arithmetic
source.  For a prime/depth cell `i=(p,e)`, primitive promotion before scalar fusion gives

```text
J_u(i)
  = sqrt(log p) xiGammaEulerBoundaryRealAmplitude(u,i),

J_0(i)
  = (log p)/sqrt(p^(e+1))
  = criticalMellinAtomWeight(p^(e+1)).                 (149)
```

The source modular family

```text
J_a(i)=J_0(i) exp(a r_i),
r_i=2(e+1)log(p^(-1/2))=-2h_i                         (150)
```

has exact reflected geometric mean `J_a(i)J_(-a)(i)=J_0(i)^2` and center derivative

```text
J'_0(i)=-log(p^(e+1))J_0(i).                           (151)
```

Consequently the reflection-odd two-leg center jet is not another copy of the old exterior:

```text
dot O_0(i,j)
 =J_0(i)J_0(j)(r_i+r_j)(h_i-h_j)
 =-2J_0(i)J_0(j)(h_i^2-h_j^2).                        (152)
```

This squared-height transgression supplies the missing modular logarithm from source reflection.
It also exposes an exact division-free Gamma anchor.  For any source height `H`,

```text
O_H(i,j)=dot O_0(i,j)+4H E_0(i,j)
        =-2J_0(i)J_0(j)
           ((h_i-H)^2-(h_j-H)^2).                     (153)
```

At first-clock aperture `L_m=6log m`, the canonical anchor is

```text
H_m=L_m/3=2log m.
```

Every hard-block height `h_p=(1/2)log p`, `2m^4<p<=5m^4`, lies strictly above `H_m`.  Therefore

```text
-(1/2)O_(H_m)(i,j) sin(tau(h_i-h_j)) >= 0              (154)
```

whenever `tau>=0` and the pair is before phase wrap.  Summing `(154)` gives a genuine nonnegative
finite source scalar.  It is primitive-promoted, reflection-odd before fusion, and
Gamma-longitudinally centered.

On every hard depth-zero cell, the promoted source current lands on the actual bad coefficient:

```text
(1/2)(log p)/sqrt p <= bad_p(L_m) <= (log p)/sqrt p,   (155)

log(2m^4)<(sqrt(log p))^2<=log(5m^4).                  (156)
```

Equations `(155)`--`(156)` close the amplitude-provenance part of `J-SF2`: the source itself
realizes the previously proved minimum singular rate and reaches the literal obstruction within
factor two.  Equations `(152)`--`(154)` construct the missing pre-fusion modular/Gamma carrier;
they are not target equivalences or coefficient interpolation.

Full card and Lean certificate:

```text
docs/drafts/pipeline/1-in-progress/
  route-j-primitive-promoted-euler-exterior-source.md

formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedExteriorSource.lean
```

Route J remains open.  Immediate hard frontier is exact two-scale domination for `(154)`, followed
by one aperture-coherent Gamma/co-Poisson relation whose finite restrictions are `(153)` and whose
scalar capacity has a source-uniform cofinal budget.  Ordinary closure, bounded polarization, or
post-fusion positivity cannot supply that theorem.

## 44. Exact two-scale source domination and exposed renormalization core

The finite-domination part of section 43 is now closed unconditionally.  Fix

```text
K=2^32,  tau=1/64,
eta_n(p)=(1/2)log p-(1/2)log n,

Q_n(p,q)=j_p j_q (eta_n(q)^2-eta_n(p)^2)
                    sin((eta_n(q)-eta_n(p))/64),

R_n=2 sum_(p in P_n) sum_(q in P_(Kn)) Q_n(p,q).       (157)
```

The first block has `eta_n(p) in [0,1]`; the dilated block has
`eta_n(q) in [8,17]`.  The squared-height gap and Jordan sine inequality give the pointwise
source bound

```text
3j_pj_q <= Q_n(p,q).                                   (158)
```

Unconditional Chebyshev estimates give

```text
sqrt(n)/12 <= sum_(p in P_n) j_p <= 10sqrt(n),         (159)
100n <= R_n                                             (160)
```

past the explicit source threshold `exp(20)<=n`.  Since the complete hard-block bad mass obeys

```text
(sum_(p in P_(m^4)) bad_p(L_m))^2 <= 100m^4,           (161)
```

equations `(160)`--`(161)` prove

```text
(sum_(p in P_(m^4)) bad_p(L_m))^2 <= R_(m^4).          (162)
```

No target sign, Xi zero, zero multiplicity, numerical certification, or interpolated coefficient
enters `(157)`.  Thus source provenance, primitive landing, and finite obstruction domination are
no longer open parts of Route J.

Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedTwoScaleDomination.lean
```

The exact remaining core is sharper than the previous “find enough energy” formulation:
`R_n` has an unconditional linear floor, so it cannot itself be the uniformly bounded Route J
capacity.  One must construct the completed Gamma/co-Poisson countercurrent before positive
scalarization and prove an aperture-refinement identity that cancels this longitudinal linear
mass while retaining the local lower comparison `(162)`.  Normalizing `(157)` by hand, moving the
survivor to another route, or taking an absolute prime norm would erase the required source
identity and does not close Route J.

## 45. Prime-power-cell Gamma/co-Poisson Green transport

The orientation-transgression source law changes the type of the missing object. A scalar
Gamma/co-Poisson counterterm is too late: every regular boundary-blind scalar consumer factors
through one orientation line, while Route J cross-cell energy lives in exact incidence. Required
transport must therefore act before cup and orientation trace.

For a labelled Euler cell `pe=(p,e)`, define

```text
C_pe(z,w)=-(e+1)^(-1)
  gammaCoPoissonIntervalCell (-(e+1)log(p)) z w.       (163)
```

The following identities are now unconditional Lean theorems:

```text
C_pe(1+a,1+a)=J_a(pe),                                (164)

(z-w)C_pe(z,w)
 =(e+1)^(-1)(
    exp((w-1/2)L_pe)-exp((z-1/2)L_pe)),               (165)

L_pe=-(e+1)log(p),
```

and exact depth sewing

```text
((r+1)+(s+1)) C_(p,r+s+1)
 =(s+1) exp((z-1/2)L_(p,r)) C_(p,s)
  +(r+1) C_(p,r) exp((w-1/2)L_(p,s)).                 (166)
```

Equation `(164)` identifies primitive promotion as canonical depth-normalized confluence of the
ordinary-integer Gamma/co-Poisson Euler jet. It is not a multiplier selected from the target bad
mass.

The source has now been constructed at the correct label resolution:

```text
A1_cell = directSum_(pe : Nat.Primes x Nat) A1_(pe.prime),
A2_cell = directSum_(pe : Nat.Primes x Nat) A2_(pe.prime).       (167)
```

Componentwise Calderón--Witt cup induces a surjective exterior differential

```text
d1_cell : exteriorSquare(A1_cell) -> A2_cell,          (168)
```

with explicit Koszul--Green section and retraction. Distinct cells have zero componentwise cup, so

```text
pe != qe
 -> wedge(lof_pe x, lof_qe y) in ker(d1_cell),         (169)
```

including `pe.prime=qe.prime` with unequal Euler depths. More strongly, the carrier in `(169)` is
its own canonical Green primitive.

For any diagonal coefficient family `c(pe)`, transport only the rational-Witt packet leg in degree
one. Its exterior lift satisfies

```text
d1_cell o T_c = T2_c o d1_cell,                       (170)
T_c o GreenSection = GreenSection o T2_c,             (171)
GreenRetraction o T_c = T_c^I o GreenRetraction.      (172)
```

Taking `c(pe)=C_pe(z,w)` gives the source-pointed Gamma/co-Poisson transport at every finite
support stage. This closes the missing algebraic source construction and shows exactly why scalar
renormalization was theatre: scalar orientation trace kills the carrier in `(169)`.

Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedGammaCoPoissonGreenTransport.lean
  CCMFirstClockPrimitivePromotedPrimePowerCellGreenTransport.lean
```

Route J remains open on one hard theorem, not on source existence. The explicit incidence
endomorphisms `T_c^I` must extend through the beyond-finite-Rees aperture system, preserve its
admitted positive/Hodge sector, and yield a cofinally uniform capacity while retaining finite
lower comparison `(162)`. Orientation-factorization cannot prove that statement; it is singular
sector preservation before trace.

There is now a sharper necessary condition. For every prime `p`, unequal depths `e!=f`, and
nonzero modular displacement `a`, the canonical same-prime depth carrier is exact incidence and
its own Green primitive, but its reflection-odd Gamma coefficient is nonzero. Hence no completion
using only cross-prime countersewing can preserve the reflection-balanced sector. Any successful
countertransport must be depth-nonlocal within every prime and only cancel after cofinal depth
assembly.

## 46. Cofinal source-normal depth countertransport and uniform reflected capacity

`[PAPER+LEAN-PROVED CONSTRUCTION]`
`[OPEN PRETRACE-TO-FIRST-CLOCK COMPARISON]`

The depth-nonlocal survivor from Section 45 is now constructed rather than postulated.  Put

```text
A(p,r)=log(p)/sqrt(p^(r+1)),
D(p,r)=A(p,0)/A(p,r),
K(p)=ceil(log p).                                     (173)
```

The source amplitude law forces

```text
A(p,r)D(p,r)=A(p,0),   D(p,r)^2=p^r.                 (174)
```

Thus equal spreading through the actual Euler depths `0<=r<K(p)` preserves primitive landing and
reduces squared source-normal mass from `log(p)^2/p` to at most `log(p)/p`.  Applied to both legs
of the finite two-scale source, the landed depth rectangle is

```text
U_n(p,q,r,s)=2Q_n(p,q)/(K(p)K(q)).                   (175)
```

Its depth codiagonal recovers `R_n` exactly.  Every shifted cross-prime term is an actual
prime-power-cell Milnor incidence and its own Green primitive, so the finite spread is a
chain-level source carrier rather than a scalar normalization.

Compensated finite-index reflection symmetry is explicit.  Raw exterior reflection exchanges
legs, reverses both finite depth intervals, and contributes one minus sign.  The odd orientation
local system contributes the second.  Their compensated involution squares to one.  Since
`Q_n(q,p)=Q_n(p,q)`, the doubled ordered-pair profile belongs to its fixed sector.  No projection
onto a predeclared kernel is used.  This fixed sector is not the actual Gamma/Hardy admitted
sector, whose defect retains every ordered prime/depth coordinate.

For one reflected fundamental domain,

```text
0<=U_n^orb
 =4 sum_(p,q) Q_n(p,q)^2/(K(p)K(q))
 <=100*289^2.                                         (176)
```

The raw doubled compensated-sector norm counts both ordered orientations and satisfies the exact
identity and uniform bound

```text
U_n^H=2U_n^orb <=200*289^2.                           (177)
```

Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedCofinalDepthCountertransport.lean
```

This closes the countertransport construction, compensated finite-index symmetry theorem, and
uniform capacity theorem.  It does **not** prove actual Hodge admission.  Exact recovery of the
linearly large current
uses a singular codiagonal: any scalar readout gain satisfying

```text
R_n <= gain_n sqrt(U_n^orb)
```

obeys

```text
gain_n >= (10/289)n.                                  (178)
```

The actual-boundary audit below supersedes the former suggestion that a finite source Hodge
polarization could repair this carrier.  The survivor stays in Route J but must be genuinely
completion-relation-valued.

## 47. Actual Gamma/Hardy cell-diagonal rigidity

`[PAPER+LEAN-PROVED CLASSIFICATION]`
`[NO RH INPUT]`

For each prime/depth cell `i`, let `d_i` and `w_i` be normalized defect and packet generators and
put

```text
E_ij=d_i wedge w_j,  i!=j.
```

The actual boundary defect is evaluated before scalar fusion:

```text
(partial_a X)(i,j)=gamma_a(i,j) tau_j(N_ij(X)).
```

Direct-sum component orthogonality gives the exact Kronecker law

```text
(partial_a E_kl)(i,j)
 = if (i,j)=(k,l) then gamma_a(i,j) else 0.           (179)
```

Prime-power half-height is injective on cells.  Hence for `a!=0`,
`gamma_a(i,j)!=0` whenever `i!=j`, and `(179)` yields

```text
ker(partial_a) intersect
  span_finite{E_ij : i!=j} = {0}.                     (180)
```

The existing source-normal spread is exactly a finite `Finsupp` combination of these carriers.
For positive depth counts and nonzero source weight its base coefficient is nonzero, so the whole
spread is outside the actual admitted sector at every nonzero displacement.  Adding the reflected
orientation cannot cancel it: the reversed carrier occupies coordinate `(j,i)`, not `(i,j)`.

Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity.lean
```

Thus changing finite weights, adding finite depths, or symmetrizing finite ordered pairs cannot
repair Section 46.  Any survivor must leave the coordinate-faithful finite carrier span.

## 48. Closed oriented source admission is the exact remaining object

`[CORPUS FRONTIER INCORPORATED]`
`[OPEN PRODUCER]`

The Hellinger--Hodge Green-descent law identifies actual incidence admission with zero modular
displacement.  The oriented source-admission law adds the completed topology.  For fixed distinct
primes `p,q`, the completed Xi Green map

```text
U_pq : H1_c -> IHat_pq
```

is coefficient-faithful and dense, and one completed coordinate decodes to the nonzero canonical
Gamma witness.  If a closed admission set `K_rho` contains `range(U_pq)`, density forces
`K_rho=IHat_pq`.  Therefore one exact unsquared finite trace

```text
e_(r;p,q) in K_rho
  <-> w_(p,q) in actualAdmittedSector(delta_rho)       (181)
```

forces `delta_rho=0`.

This sharpens the Route-J survivor.  An arbitrary source corona is insufficient: if it is closed
and contains the dense completed Green range, it is the whole completion; if it erases finite
coordinates, `(181)` cannot descend; if it keeps the singular codiagonal as a vertical part, it
does not transport an oriented output.  The exact open producer is:

```text
construct K_rho from the arithmetic source,
prove closedness and completed Green landing,
and prove finite trace (181) before scalar orientation.
```

This is not a reassignment or a closure claim.  Existence of such `K_rho` at every divisor point
is formally equivalent to RH.  Route J remains open until this source-derived admission object is
constructed or every remaining source-relation class is exhausted with its strongest positive
survivor.

## 49. Pure-incidence actual admission and bounded-readout no-go

`[PAPER+LEAN-PROVED CONSTRUCTION]`
`[PAPER+LEAN-PROVED CLASS NO-GO]`

Section 47 classifies the mixed canonical span, not all finite incidence.  The exact complementary
survivor is source-defined.  For distinct cells `i,j`, put

```text
D_ij=d_i wedge d_j,
P_ij=w_i wedge w_j.                                  (182)
```

The Calderon--Witt cup and every actual boundary coordinate are defect--packet mixed.  Independent
pure coordinate determinants prove `D_ij,P_ij` nonzero, while

```text
d1_cell(D_ij)=d1_cell(P_ij)=0,
partial_a(D_ij)=partial_a(P_ij)=0                    (183)
```

for every modular displacement `a`.  Thus `D_ij+P_ij` is genuine actual admitted incidence even
off the critical line.  This corrects any inference that actual admission itself is finite-span
rigid.

The pure sector also fixes the missing operation order.  Packet-leg Gamma transport satisfies

```text
T_c(D_ij)=D_ij,
T_c(P_ij)=c_i c_j P_ij.                              (184)
```

Both primitive amplitudes are now produced by the source endomorphism.  With the source height/
phase kernel before amplitudes and the forced critical depth deattenuations, one explicit
prelanding cofinal carrier maps exactly to

```text
A_n(p,q,r,s)
 =U_n(p,q,r,s)(D_(p,r;q,s)+P_(p,r;q,s)).             (185)
```

Both complete finite sums are actually admitted for every `a`; the landed carrier is fixed by
cell Green retraction.  Pure exchange swaps `D` and `P`, hence fixes `(185)`.  Its raw two-component
capacity and one-component codiagonal are

```text
U_n^pure=2U_n<=200*289^2,
sum_(p,q,r,s) U_n(p,q,r,s)=R_n.                      (186)
```

This completes the requested cofinal depth-nonlocal actual-admitted countertransport and its
uniform capacity.  It still does not close Route J.  Hostile testing is decisive: if a scalar
consumer controls exact readout by this capacity, then

```text
R_n <= gain_n sqrt(U_n^pure)
  -> gain_n >= (5/289)n.                             (187)
```

No fixed gain works.  More generally, let `x_n` be any realization in a complex seminormed space
with `||x_n||<=sqrt(U_n^pure)`.  There is no continuous linear functional `L` satisfying

```text
L(x_n)=R_n                                             (188)
```

for all sufficiently large source apertures: `||L||` would be a forbidden fixed gain in `(187)`.
This is class-complete for normed completed scalar descent retaining the uniform capacity and exact
finite codiagonal.  A topology that makes the codiagonal continuous must charge an unbounded
carrier norm; a vertical relation does not give a descended scalar output.

Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedPureHodgeCountertransport.lean
```

Strongest positive survivor is the nonzero actual-admitted two-leg source carrier `(185)`.  Its
bounded scalar-readout program is closed.  Route J remains open on Section 48's unsquared mixed
finite trace: a source-derived `K_rho` must retain the canonical mixed witness that pure incidence
necessarily hides.

## 50. Pure-Hodge modular transgression recovers the unsquared mixed trace

`[PAPER+LEAN-PROVED CONSTRUCTION]`
`[PAPER+LEAN-PROVED TOPOLOGY CLASSIFICATION]`
`[OPEN COMPLETED-XI GRAPH LANDING]`

Section 49's last sentence was too pessimistic: pure incidence hides the mixed trace from its
primary Gamma boundary, but not from the source-relative Hodge transgression required by the
orientation--transgression law.  For a distinct cell pair `i,j`, write

```text
r_ij=rate(i)+rate(j),
B_a(D_ij)=exp(-a r_ij)D_ij,
B_a(P_ij)=exp( a r_ij)P_ij.                         (189)
```

The balanced orbit obeys the exact Hodge covariance

```text
H B_a = B_(-a) H.                                   (190)
```

Therefore its reflection-odd part on the Hodge-fixed pure carrier is

```text
Omega_a(i,j)
 =(B_a-B_(-a))(D_ij+P_ij)/2
 =sinh(a r_ij)(P_ij-D_ij),                          (191)
```

which is Hodge-anti-fixed.  Since both pure summands are exact incidences annihilated by every
primary Gamma/Hardy boundary coordinate, `Omega_a(i,j)` is actual-admitted for every auxiliary
boundary displacement.  This is a vector-valued secondary class, not a mixed carrier inserted
after scalarization.

Pair its packet--packet coordinate against the defect--defect leg with the source weight

```text
W_ij=A_0(i)A_0(j)(height(i)-height(j)).               (192)
```

The definitions of modular current and reflection-odd exterior give, without approximation,

```text
Tr_ij(Omega_a(i,j))
 =W_ij (exp(a r_ij)-exp(-a r_ij))/2
 =gamma_a(i,j)
 =partial_a(E_ij)(i,j).                              (193)
```

Here `E_ij=d_i wedge w_j` is the canonical mixed witness.  Thus `(193)` is the missing exact
unsquared finite trace, reconstructed from a nonzero actual-admitted pure source object through
the Hodge--modular commutator.  Cell-height injectivity and the existing Gamma zero law imply

```text
Tr_ij(Omega_a(i,j))=0  <->  a=0.                    (194)
```

The source-horizon obstruction fixes the completion topology sharply.  At fixed prime clocks
`p,q` and common depth `n`, the two-component coefficient graph capacity is

```text
C_a(p,q,n)
 =exp(-2a r_(p,q,n))+exp(2a r_(p,q,n))
 =S_a(p,q,n)+S_(-a)(p,q,n),                          (195)
```

the sum of reciprocal Gamma sewing costs.  Since
`r_(p,q,n)=-(n+1)(log p+log q)`, one term tends to infinity for every `a!=0`, whereas
`C_0(p,q,n)=2`.  Consequently

```text
exists C, forall n, C_a(p,q,n)<=C  <->  a=0.         (196)
```

More sharply, the graph-capacity excess is exactly the squared oriented curvature:

```text
W_ij^2(C_a(i,j)-2)=4 gamma_a(i,j)^2.                 (197)
```

Equation `(197)` is the source-side purity-defect law.  Positive Hodge capacity sees exactly the
square of the secondary trace, while `(193)` retains its sign before scalar positivity.

This closes the search for an unsquared secondary detector and proves its class-complete
graph-capacity boundary.  It does not assume or prove that completed Xi source vectors satisfy
the bounded side of `(196)`.  Exact remaining Route-J producer is now:

```text
derive, from the prime-power Xi Green source relation, graph-bounded landing
of its balanced pure-Hodge modular transgression.                         (198)
```

Assuming `(198)` would be theatre; deriving it would force `a=0` at every divisor coordinate by
`(196)` and close RH.  Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedPureHodgeModularTransgression.lean
```

## 51. Hellinger--Gamma residue gauge produces the adjacent-grade graph-Cauchy coface

`[PAPER+LEAN-PROVED LOCAL CONSTRUCTION]`
`[PAPER+LEAN-PROVED UNIFORM CAPACITY]`
`[OPEN COMPLETED-XI COEND]`

The updated oriented source-admission law sharpens `(198)`: multiplying a fixed mixed witness by
the full nonzero Hellinger residue cannot change its relative admission class.  A valid producer
must change grade and differential.  The even Gamma residue inside the same Hellinger--Beta column
does exactly that.  Put

```text
g_n=Res_(z=-2n) Gamma(z)=1/(2n)!.                  (199)
```

For fixed distinct primes `p,q`, apply this source-native grade gauge to the PHMT carrier at common
Euler depth `n`:

```text
Q_n(a)=g_n Omega_a((p,n),(q,n)),
E_n(a)=Q_(n+1)(a)-Q_n(a).                          (200)
```

Every `Q_n(a)` is Hodge-anti-fixed in its coefficient plane and actual-admitted for every auxiliary
boundary displacement.  Hence every off-diagonal edge `E_n(a)` is actual-admitted.  Its finite
boundaries telescope before any scalar orientation:

```text
sum_(n<N) E_n(a)=Q_N(a)-Q_0(a).                    (201)
```

This is not full-residue scaling on a fixed incidence line: both cell label and Gamma residue grade
move.  It is the first literal adjacent-grade coface surviving the updated paper's obstruction.

Let `L=log p+log q`, `c=|2aL|`, and let `C_a(p,q,n)` be `(195)`.  Its gauged graph capacity is

```text
K_a(p,q,n)=g_n^2 C_a(p,q,n).
```

Factorial domination gives the unconditional estimate

```text
0<=K_a(p,q,n)
  <=2 exp(c(n+1))/((2n)!)^2
  <=2 exp(c)(exp(c))^n/n!  -> 0.                  (202)
```

In particular, for every real `a`,

```text
K_a(p,q,n)<=2 exp(c) exp(exp(c))                  (203)
```

uniformly in `n`.  Thus the Hellinger--Gamma source grade overcomes the reciprocal exponential
PHMT obstruction without assuming `a=0`.  If `x=e^{-a r_n}` and `y=e^{a r_n}`, the squared norm
of the two opposite odd channels is

```text
g_n^2 (y-x)^2/2 <= g_n^2(x^2+y^2)=K_a(p,q,n),    (204)
```

so `Q_n(a)` is coefficient-graph-null and the partial coface primitives in `(201)` converge to
`-Q_0(a)`.

Graph damping does not erase the finite unsquared charge.  Gradewise Poincare trace gives

```text
Tr_n(Q_n(a))=g_n gamma_a((p,n),(q,n)),             (205)
Tr_n(Q_n(a))=0 <-> a=0.                            (206)
```

The scalar trace differences telescope only after the vector coface has been constructed.  This
closes the local adjacent-grade, telescoping, Hodge-preserving, uniformly graph-Cauchy part of the
producer in the updated paper.

It does not close Route J.  The limit of `(201)` is one depth-zero pure carrier, not the completed
Xi Green primitive.  Exact remaining producer is now the coefficient-faithful coend:

```text
tensor the Hellinger--Gamma coface with the completed Xi Green source;
prove its labelled graph limit equals the completed Xi Green primitive;
prove the induced relative-admission quotient map is injective.          (207)
```

The final clause is forced by relative admission-spectrum conservation: without quotient
injectivity, a pure lift could merely kill the nonzero mixed obstruction class.  Assuming any
part of `(207)` would restate landing.  Lean certificate:

```text
formal/GaloisForLFunctions/RHTower/
  CCMFirstClockPrimitivePromotedHellingerGammaPureHodgeCoface.lean
```

## 52. Adaptive prime-normal horizon intertwiner and forced non-Hilbert provenance

`[PAPER+LEAN-PROVED SOURCE--DIVISOR CONSTRUCTION]`
`[PAPER+LEAN-PROVED HILBERT STABILITY NO-GO]`
`[OPEN SOURCE-FORCED GREEN VANISHING]`

The latest Hellinger--Hodge--Green paper asks to identify the closed adaptive
prime-normal `ell^1` range with the compatible reflected-Gaussian-graded Green quotient and only
then polarize.  Taken literally in the Hilbert quotient norm, this is impossible.  For every
bounded linear map `T:ell^1(I)->H` into a complex inner-product space and every finite label set
`S`, recursive sign selection and the parallelogram law give a signed packet `x_S` with

```text
||x_S||_1=|S|,            ||T x_S||^2<=|S| ||T||^2.                (208)
```

For infinite `I`, `(208)` excludes every positive lower modulus.  In particular, every bounded
Hilbert postcomparison after the adaptive codiagonal destroys its `3/4` lower bound.  Thus the
full stable `ell^1` source range cannot literally be a closed Hilbert subrange.  Compatibility
must quotient source directions before Hilbertization, or unchanged source provenance must remain
in a finer non-Hilbert norm.

The positive replacement is now constructed from the actual arithmetic source.  For each Xi
divisor copy `q`, choose the source-derived adaptive scale `N(q)` in the honest convergence
chamber and let `A_q` be coefficient augmentation after the exact adaptive codiagonal.  For every
prime label `ell`,

```text
A_q(e_ell)
 =R_(ell,d(ell,N(q)))(lambda_q),
3/4<=|A_q(e_ell)|<=5/4.                                      (209)
```

The first equality is the literal complete prime-normal residual multiplier, not an abstract
interpolation coefficient.  Let `h_ref(q)` be the fixed reflected-Gaussian horizon grade.  Column
synthesis gives one unconditional bounded source--divisor operator

```text
T_hor: ell^1(primes) -> ell^2(Div Xi),
(T_hor x)(q)=A_q(x) h_ref(q),
||T_hor x||_2 <= (5/4)||h_ref||_2 ||x||_1.                    (210)
```

Every prime column is nonzero at every divisor copy by `(209)` and `h_ref(q)!=0`.  Applying the
completed Green fracture, actual Calderon--Witt incidence, and split-injective resolved
Hellinger--Gamma quotient produces for every prime label `ell` a completely explicit class
`[G T_hor(e_ell)]_a` satisfying

```text
[G T_hor(e_ell)]_a=0  <->  RH.                               (211)
```

No displacement-zero hypothesis occurs in `(211)`.  The proof uses the stronger generic theorem:
the completed Green fracture of any divisor `ell^2` field nonzero at every actual divisor copy
vanishes exactly under RH.

There is an exact positive range theorem between the full-source no-go and `(211)`.  For each
fixed prime label `ell`, multiplication by `q |-> A_q(e_ell)` defines a bounded automorphism
`M_ell` of the entire completed Xi divisor carrier, with bounded inverse and capacities

```text
(3/4)||v||_2 <= ||M_ell v||_2 <= (5/4)||v||_2,
||M_ell^(-1)v||_2 <= (4/3)||v||_2.                           (211a)
```

In particular `T_hor(e_ell)=M_ell h_ref`.  Thus compatible divisor-range identification is fully
constructed after quotienting the source to any one labelled column.  What is impossible is doing
this bounded-below on the whole infinite `ell^1` source simultaneously.  This separates the exact
survivor from the overstrong target without discarding Route J.

Stability survives only in the source-resolved graph

```text
Gamma_hor(x)=(x,T_hor x) in ell^1(primes) x ell^2(Div Xi).    (212)
```

It is injective, has closed range, obeys `||x||_1<=||Gamma_hor(x)||`, and has uniform upper
capacity `max(1,(5/4)||h_ref||_2)||x||_1`.  Its Hilbert projection is exactly `T_hor` and is not
bounded below.  This is the forced topology change exposed by `(208)`, not a choice of another
ambient completion.

Route J remains open.  The source object, completed divisor landing, resolved quotient class,
fixed-label compatible range equivalence, and RH equivalence are no longer missing.  Exact hard
frontier is now to derive from prime-power
source/Hodge compatibility that one class in `(211)` vanishes, or equivalently to prove the
source-selected closed-graph/quotient relation which forces the completed Green fracture of an
adaptive column to be zero.  Merely assuming that relation would restate RH.  The remaining
theorem must construct it from source differential and compatibility boundaries.

Lean certificates:

```text
formal/GaloisForLFunctions/RHTower/
  MobiusThetaAdaptivePrimeNormalHilbertNoGo.lean
  MobiusThetaAdaptivePrimeNormalHorizonIntertwiner.lean
```

## 53. Reflected adaptive common-test source and exact Green primitive

`[PAPER+LEAN-PROVED FULL SOURCE CONSTRUCTION]`
`[PAPER+LEAN-PROVED REFLECTED GREEN COMPATIBILITY]`
`[OPEN ARITHMETIC CODIAGONAL VANISHING]`

The updated Hellinger--Hodge--Green descent paper identifies the exact local
common-test obligation `(7.17c)`.  The unsymmetrized canonical line map already
closes its landing and faithfulness clauses: for local Green coefficient
`g_(p,q)`, scalar multiplication of the resolved adaptive prime source gives

```text
Phi_(p,q)(g_(p,q)) in S_(N(q),w(q)),
Phi_(p,q)(g_(p,q))=0 -> g_(p,q)=0.                    (213)
```

Its codiagonal is computed rather than postulated:

```text
Sigma_2 Phi_(p,q)(c)=c C_(N(q),w(q))(e_p),
Sigma_2 Phi_(p,q)(c)=0 <-> c=0.                       (214)
```

Thus `(7.17c).1` and `(7.17c).3` are unconditional.  Clause `.2` is exactly
the local critical-line statement, not a hidden range or faithfulness gap.

Direct transport through the divisor-adapted reader still left a genuine
source question: the chosen depths at `q` and functional-equation mate `Rq`
need not agree, so the resulting multiplier need not commute with completed
source Green reflection.  The forced correction is made before scalar
augmentation.  Average the two exact post-prime source tails and retain the
common Möbius head:

```text
T_ref,q=(T_q+T_Rq)/2,
C_ref,q=D+T_ref,q,
R_ref,q(x)=(Dx,T_ref,q x).                            (215)
```

Both literal tails have norm at most `1/4`; consequently

```text
||T_ref,q x||_1 <= (1/4)||x||_1,
||C_ref,q x||_1 >= (3/4)||x||_1.                      (216)
```

The range of `R_ref,q` is closed, and its intersection with the universal
codiagonal kernel is zero.  This is a full source operator and conservative
resolved sector, not divisor-side coefficient interpolation.

After coefficient augmentation on prime basis vector `e_p`, the reflected
reader is

```text
A_ref,p(q)=(A_q(e_p)+A_Rq(e_p))/2,
||A_ref,p(q)+1|| <= 1/4,
3/4 <= |A_ref,p(q)| <= 5/4.                           (217)
```

It is exactly reflection-even.  Hence multiplication by `A_ref,p` is a
bounded automorphism `M_ref,p` of the complete Xi carrier with

```text
(3/4)||v||_2 <= ||M_ref,p v||_2 <= (5/4)||v||_2,
||M_ref,p^(-1)v||_2 <= (4/3)||v||_2,                  (218)
Ghat M_ref,p = M_ref,p Ghat,
W M_ref,p = M_ref,p W.                               (219)
```

Equations `(219)` close the previously missing reflected source-primitive
compatibility.  Applying `M_ref,p` to the literal two-line prime--Gamma
Cauchy boundary gives a Bochner-integrable source whose integral is the
reflected adaptive horizon column.  Applying it to the oriented boundary
gives an integral equal to

```text
e_ref,p=M_ref,p e_ref,
Ghat e_ref,p=M_ref,p h_ref,
e_ref,p=i W(M_ref,p h_ref).                           (220)
```

Every coefficient of `M_ref,p h_ref` is nonzero, so its completed Green
provenance still satisfies

```text
D_G(M_ref,p h_ref)=0 <-> RH.                          (221)
```

This is important negative information as well as positive infrastructure:
exact prime--Gamma landing, harmonic preservation, Green commutation,
invertible capacity, closed resolved source, and line faithfulness do not
force `(221)` to vanish.  For the actual reflected comparison,

```text
Sigma_2 Phi_ref,p,q(g_ref,p,q)=0
  <-> g_ref,p,q=0
  <-> Re(rho_q)=1/2.                                  (222)
```

Therefore Route J remains open.  Exact surviving hard theorem is no longer
construction of source object, completion, reflected primitive, or
Green-compatible transport.  It is the arithmetic differential identity
which forces the already explicit source coordinate in `(222)` to be zero.
Any proof using only Green commutation or primitive existence is now formally
shown insufficient; it must use additional prime--Gamma/co-Poisson incidence
that annihilates this exact coordinate.

Lean certificates:

```text
formal/GaloisForLFunctions/RHTower/
  MobiusThetaAdaptivePrimeNormalGreenResolvedLineComparison.lean
  MobiusThetaAdaptivePrimeNormalReflectedGreenSource.lean
```

## 54. Global square-summable common-test record

`[PAPER+LEAN-PROVED GLOBAL ASSEMBLY]`
`[PAPER+LEAN-PROVED CLOSED GLOBAL SECTOR]`
`[OPEN SOURCE DIFFERENTIAL ANNIHILATION]`

Pointwise construction `(213)--(222)` globalizes without loss.  For fixed
prime `p`, let `v_(p,q)` be the reflected resolved source generated by `e_p`
at divisor copy `q`.  Its head has norm one while reflected tail has norm at
most `1/4`; with product max norm,

```text
||v_(p,q)||=1                                                   (223)
```

at every divisor copy.  Therefore coordinatewise scalar multiplication is
an isometric source comparison

```text
J_p:ell^2(Div Xi) -> ell^2_q(ell^1(N) x ell^1(N)),
(J_p a)(q)=a(q)v_(p,q),
||J_p a||=||a||.                                                (224)
```

Its range is a closed global source sector.  Fiberwise codiagonalization on
that range is represented by a bounded linear map

```text
C_p:ell^2(Div Xi) -> ell^2_q(ell^1(N)),
(C_p a)(q)=a(q) C_ref,q(e_p),
(3/4)||a|| <= ||C_p a|| <= (5/4)||a||.                          (225)
```

Thus `C_p` is injective and global common-test record has no hidden
completion radical.  Applying `(224)` to actual reflected adaptive Green
provenance `g_ref,p` gives one explicit global record in closed sector, with

```text
C_p(g_ref,p)=0 <-> g_ref,p=0 <-> RH.                            (226)
```

This removes possible escape that pointwise comparisons fail to assemble,
lose square summability, or acquire closure kernel.  They assemble
isometrically, and codiagonal retains same quantitative lower modulus after
global completion.  Exact remaining problem is now literally to prove the
left side of `(226)` from arithmetic source differential.  No further range,
topology, or faithfulness construction can affect that gate.

Lean:

```text
formal/GaloisForLFunctions/RHTower/
  MobiusThetaAdaptivePrimeNormalGlobalReflectedComparison.lean
```

## 55. Doubled-window co-Poisson conormal tomography and the quadratic reflection cover

`[PAPER+LEAN-PROVED SOURCE CONSTRUCTION]`
`[PAPER+LEAN-PROVED UNIFORM CAPACITY]`
`[PAPER+LEAN-PROVED QUADRATIC COVER CLASSIFICATION]`
`[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`
`[OPEN ARITHMETIC RAMIFICATION]`

The updated Hellinger--Hodge--Green paper proves a stronger zero-order no-go than the previous
finite-window audit: at every zeta divisor point, completed Mellin evaluation annihilates the
entire infinite-dimensional Burnol co-Poisson source space because every seed carries the same
factor `zeta(w)`.  That statement is exact at value grade, but it does not survive passage to the
first nonzero divisor conormal while source labels remain resolved.

Fix `L>0` and take the two literal reciprocal sub-window seeds

```text
[exp(-L),1],      [exp(-2L),1].
```

Their critical-strip Mellin transforms before the nonzero completion factor are

```text
M_L(w)  =(exp(Lw)-1) zeta(w)/w,
M_2L(w) =(exp(2Lw)-1) zeta(w)/w.                       (227)
```

Let `rho` be a nontrivial zeta zero of analytic order `m>=1`.  All derivatives of `zeta` below
order `m` vanish.  Leibniz therefore gives, with one common nonzero conormal scalar `lambda_rho`
which also absorbs the completed Mellin factor,

```text
D^m M_L(rho)  =(exp(L rho)-1) lambda_rho,
D^m M_2L(rho) =(exp(2L rho)-1) lambda_rho.              (228)
```

Because `0<Re(rho)<1`, the first coefficient in `(228)` is nonzero.  The projective conormal ratio
is consequently defined and satisfies the exact source identity

```text
R_L(rho)
 :=D^m M_2L(rho)/D^m M_L(rho)-1
 =exp(L rho).                                           (229)
```

No zeta derivative, multiplicity normalization, divisor enumeration, or fitted interpolation
survives in `(229)`.  The identity uses the resolved labels of two actual co-Poisson windows and
the first nonvanishing source conormal before the common zeta factor is quotiented away.

Half-density centering produces the source character

```text
U_L(rho)=exp(-L/2) R_L(rho)=exp(L(rho-1/2)).            (230)
```

It has uniform two-sided capacity on the full open strip:

```text
exp(-L/2)<|U_L(rho)|<exp(L/2),
exp(-L/2)<|U_L(rho)^(-1)|<exp(L/2).                    (231)
```

More importantly, its radial coordinate is exactly the missing horizontal displacement:

```text
log|U_L(rho)|/L=Re(rho)-1/2,
delta_tau r_G(rho)=log|U_L(rho)|/(pi L).               (232)
```

Thus the Burnol source is horizontally mute only after zero-order scalar evaluation.  Its
resolved first conormal supplies a literal, uniformly bounded transverse divisor coordinate.
This is not another principal scalar multiple of the Green packet: it is a projective ratio of
two independently labelled source windows after their common divisor factor has been removed.

The hostile reflection audit identifies exactly what this construction still lacks.  For
`tau(rho)=1-conj(rho)`, equation `(230)` gives

```text
U_L(tau(rho))=1/conj(U_L(rho)).                         (233)
```

Put

```text
S_L(rho)=U_L(rho)+U_L(tau(rho)),
P_L(rho)=U_L(rho)U_L(tau(rho)).                        (234)
```

Both `S_L` and `P_L` are reflection-invariant, `|P_L|=1`, and the two reflected source characters
are exactly the roots of

```text
X^2-S_L(rho)X+P_L(rho)=0.                              (235)
```

The discriminant is

```text
Delta_L(rho)=S_L(rho)^2-4P_L(rho)
            =(U_L(rho)-U_L(tau(rho)))^2,               (236)

Delta_L(rho)=0
  <-> U_L(rho)=U_L(tau(rho))
  <-> Re(rho)=1/2.                                     (237)
```

Equations `(234)--(237)` are the exact quadratic reflection cover of the co-Poisson conormal
source.  The invariant observation exists and has uniform capacity; what fails is single-valued
descent of one oriented root.  Fourier unitarity does not repair this: off line it exchanges the
two conormal fibres instead of making either fibre character unitary.  Declaring `|U_L|=1`,
declaring the cover ramified, or choosing the same root on both sheets is precisely the RH
statement in `(237)`.

This materially sharpens the Route-J frontier.  Construction of a transverse co-Poisson source
coordinate is no longer missing, and the paper's common-factor no-go applies only before
conormalization.  Exact remaining producer is an arithmetic differential or off-diagonal
prime--Gamma incidence which forces the explicit quadratic cover `(235)` to ramify at every
actual divisor point.  Equivalently, it must prove `Delta_L=0` from a source relation independent
of `(232)`.  Merely transporting, bounding, or taking the invariant coefficients of the cover is
conservative and cannot supply that ramification.

Novelty audit: Burnol's co-Poisson papers supply the Mellin factorization and Sonine source
spaces; the updated internal paper proves whole-source zero-order annihilation.  Targeted primary
and internal searches located no doubled-window first-conormal ratio `(229)`, uniform centered
character `(231)`, or quadratic reflection-cover classification `(234)--(237)`.  Algebraic
factorization itself is elementary; candidate new content is its exact actual-source conormal
specialization and the resulting correction of the zero-order horizontal-muteness boundary.

Lean realization:

```text
formal/GaloisForLFunctions/RHTower/
  BurnolCoPoissonConormalReflectionCover.lean
```

The formal module binds the construction to the existing literal co-Poisson--Sonin source by
proving the exact uncompleted and completed Mellin evaluations for `[exp(-L),1]`.  At every
multiplicity-exact Xi support point it proves that the zeta jet of exact order is nonzero, applies
the full Leibniz formula, and derives `(228)` with the explicit common factor
`iteratedDeriv(m,zeta,rho)/rho`; hence the actual ratio of the two literal Mellin jets is `(229)`.
It then proves the exact logarithmic horizontal coordinate, two-sided strip capacity for the
character and its inverse, conjugate-inverse reflection law, reflection-invariant orbit
coefficients and discriminant, unit-modulus orbit product, both quadratic-root laws, and the
ramification equivalence `(237)`.  No abstract replacement for the source conormal, universal
ramification premise, zeta-zero classification, or RH axiom enters any theorem.

## 56. Reflection-diagonal phase diagram of the full joint-depth source

`[PAPER+LEAN-PROVED SOURCE CLASSIFICATION]`
`[PAPER+LEAN-PROVED SHARP TWO-WALL NO-GO]`
`[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]`
`[OPEN SINGULAR PRE-CODIAGONAL ARITHMETIC DIFFERENTIAL]`

The latest Hellinger--Hodge--Green revision closes the early-scalarization loophole.  On every
prime-power label `n=p^(e+1)`, the primitive-promoted source and reciprocal co-source remain
distinct,

```text
L_w(p,e)=[log(p)/sqrt(n)] n^(-w),
R_v(p,e)=[1/sqrt(n)] n^(-v),                            (238)
```

and their full labelled pairing is the von Mangoldt Dirichlet channel.  The common Hardy Cauchy
factor was previously known to give the scalar common-test kernel.  To test whether this stronger
source can ramify the Burnol cover `(235)`, retain the common half-line coordinate `t>0` and use
the literal biorthogonal features

```text
L_w(p,e;t)=L_w(p,e) exp(-wt),
R_v(p,e;t)=R_v(p,e) exp(-vt).                           (239)
```

Write the centered divisor displacement as `alpha=rho-1/2`.  Reflection sends it to
`-conj(alpha)`.  At Hardy regularization depth `eps`, the reflected source/co-source parameters
are therefore

```text
w=eps+alpha,                 v=eps-conj(alpha).          (240)
```

The sesquilinear exponent has the exact cancellation

```text
w+conj(v)=2 eps.                                        (241)
```

Consequently horizontal displacement disappears before any integration or summation.  For every
retained `(p,e,t)`,

```text
L_(eps+alpha)(p,e;t) conj(R_(eps-conj(alpha))(p,e;t))
  = Lambda(n) n^(-(1+2 eps)) exp(-2 eps t).              (242)
```

This is stronger than blindness of a scalar Gram: prime label, valuation depth, primitive/co-source
asymmetry, and common Hardy time are all still resolved when `alpha` cancels.  Integrating in `t`
and summing only afterward gives

```text
<R_(eps-conj(alpha)),L_(eps+alpha)>
  = LSeries Lambda (1+2 eps),

K_ref(eps,alpha)
  = [LSeries Lambda (1+2 eps)]/(2 eps),                  (243)
```

whenever the Hilbert pairing is defined.  Both right sides are independent of `alpha`.

The hostile summability audit exposes two different sharp walls.  Individual source and co-source
legs have exact Hilbert chambers

```text
L_w in ell2  <-> Re(w)>0,
R_v in ell2  <-> Re(v)>0.
```

Thus simultaneous reflected Hilbert admission is

```text
L_(eps+alpha), R_(eps-conj(alpha)) in ell2
  <-> eps>|Re(alpha)|
  <-> eps>|Re(rho)-1/2|.                                (244)
```

The direct coefficientwise codiagonal has a strictly larger maximal regular chamber:

```text
sum_(p,e) |L_(eps+alpha)(p,e)
                 conj(R_(eps-conj(alpha))(p,e))| < infinity
  <-> eps>0.                                             (245)
```

The reverse implication in `(245)` is not inferred from a recalled Dirichlet convergence slogan.
Restricting a hypothetical sum at `eps<=0` to the depth-zero prime face gives the exact squared
Gamma boundary coordinate at displacement `2 eps`; its summability is equivalent to `2 eps>0`.
At `eps=0` this is the nonsummable prime mass `log(p)/p`.  Hence the complete phase diagram is

```text
eps>|Re(alpha)| : paired codiagonal + two Hilbert legs;
0<eps<=|Re(alpha)| : paired codiagonal, but no two-leg Hilbert realization;
eps=0 : no absolutely summable reflected codiagonal.     (246)
```

Equations `(242)--(246)` close every regular reflection-diagonal use of the updated source.
Horizontal displacement survives only as the location of the individual-leg chamber wall; that
is another radial detector, already recovered exactly by `(232)`, not an independent arithmetic
annihilator.  Passing from two Hilbert vectors to the larger regular codiagonal does not help: it
erases `alpha` throughout its entire domain.  The singularity at `eps=0` is real, but merely
declaring a renormalized boundary value to vanish would install the missing RH statement.

The Route-J survivor is therefore sharper and remains in Route J.  It must be constructed before
reflection codiagonalization, retain genuinely off-diagonal prime/depth incidence, and either
admit a source-derived singular renormalization at `eps=0` or couple nonseparably to divisor
provenance.  Its arithmetic differential must then prove a zero identity forcing the Burnol
discriminant `(236)` to vanish.  No regular diagonal common-test manipulation can do so.

Internal novelty audit found the newly formalized larger codiagonal chamber and its balanced real
wall, but no complex reflected regularization theorem, pointwise prime-depth-time cancellation,
exact individual-versus-paired two-wall phase diagram, or its Route-J conormal consequence.
Targeted primary searches found Burnol's co-Poisson/Sonine Hilbert constructions and the
Connes--Consani scaling-Hamiltonian discussion of balanced absorption/emission, but not
`(242)--(246)`.  General Cauchy-kernel algebra and prime-series convergence are classical;
candidate new content is their exact source-resolved reflection classification and the resulting
elimination of the full regular diagonal annihilator class.

Lean realization:

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthReflectionDiagonalBlindness.lean
```

The module proves the reciprocal co-source's previously missing sharp Hilbert iff, both complex
coefficient chambers, the literal biorthogonal prime-depth-time feature formula, pointwise
reflection blindness `(242)`, integrated fibre identity, exact maximal codiagonal iff `(245)`,
universal codiagonal value, global Hilbert-pairing blindness `(243)`, the regular-but-non-Hilbert
middle chamber, and the spectral specialization `(244)`.  All statements are unconditional and
contain no divisor-location premise.

## 57. Off-diagonal inverse-clock countertransport and the exact all-depth Hodge wall

`[PAPER+LEAN-PROVED SOURCE CONSTRUCTION]`
`[PAPER+LEAN-PROVED CLASS-COMPLETE FLAT-CYCLE NO-GO]`
`[FORMAL CLASS-CLOSING EXTENSION; FLATNESS ITSELF IS PRIOR INTERNAL KNOWLEDGE]`
`[OPEN NON-COBOUNDARY ARITHMETIC DIFFERENTIAL]`

The survivor left by Section 56 must be tested before reflection codiagonalization.  Let

```text
I = Nat.Primes x Nat,
n_(p,e) = p^(e+1),
lambda_(p,e) = log n_(p,e) = (e+1) log p.                (247)
```

For two independently retained labels `i,j in I`, define the literal reflected source incidence

```text
P_(eps,a)(i,j)
 = L_(eps+a)(i) conj(R_(eps-conj(a))(j)).                (248)
```

This is not an abstract edge field: both factors are the primitive-promoted source and reciprocal
co-source from `(238)`.  Direct complex-power algebra, using positivity of every `n_i`, gives

```text
P_(eps,a)(i,j)
 = P_(eps,0)(i,j) H_a(i,j),

H_a(i,j) = exp(a (lambda_j-lambda_i))
          = n_j^a n_i^(-a).                              (249)
```

Every source and co-source coefficient is nonzero, so normalization by `P_(eps,0)` is legitimate
and source-defined:

```text
P_(eps,a)(i,j) / P_(eps,0)(i,j) = H_a(i,j).              (250)
```

Thus the first literal off-diagonal survivor is completely computable.  Its computation exposes
a full-class obstruction, not one failed loop.  For all labels `i,j,k`,

```text
H_a(i,j) H_a(j,k) = H_a(i,k),
H_a(i,j) H_a(j,k) H_a(k,i) = 1.                          (251)
```

Hence every multiplicative cycle word in the normalized joint-depth incidence is identically
flat for every horizontal displacement.  No choice of finite prime/depth graph, longer cycle, or
cofinal union of such cycle identities can create an RH equation from this separable character.

The reflection and Hodge laws are nevertheless exact.  Complex conjugation gives

```text
H_(-conj(a))(i,j) = conj(H_a(i,j))^(-1).                 (252)
```

Since the log clock is injective on prime powers, every distinct pair obeys

```text
H_a(i,j) = H_(-conj(a))(i,j)  <->  Re(a)=0,
H_a(j,i) = conj(H_a(i,j))     <->  Re(a)=0.              (253)
```

Thus edgewise reflected-Hodge compatibility is exactly the critical-line condition, while closed
cycle holonomy is blind to it.  There is also an exact cross-construction identification with the
doubled-window Burnol cover of Section 55:

```text
H_(rho-1/2)(i,j)
 = burnolCoPoissonCenteredConormalCharacter
     (lambda_j-lambda_i, rho).                            (254)
```

The Burnol window length is therefore not an analogy or inserted calibration: it is precisely the
log-clock separation of two literal Euler source labels.

The requested countertransport now has a canonical finite form.  For an injective packet
`q : Fin N -> I`, let `D_q=diag(lambda_(q_i))` and let `P_q` be `(248)`.  Put

```text
K^P_q(i,j) = 0                                      if i=j,
             P_(eps,a)(q_i,q_j)/(lambda_(q_i)-lambda_(q_j)) otherwise.
```

Every denominator is nonzero by injectivity of the prime-power clock, and entrywise multiplication
proves the exact commutator identity

```text
[D_q,K^P_q]
 = P_q - diag_i(P_(eps,a)(q_i,q_i)).                    (255)
```

This constructs the depth-nonlocal countertransport of the actual source incidence.  Its only
unrecovered part is the diagonal residual already classified in Section 56 as displacement-blind.
For the normalized source character define similarly

```text
K^H_q(i,j) = 0                                      if i=j,
             H_a(q_i,q_j)/(lambda_(q_i)-lambda_(q_j)) otherwise.
```

Then

```text
[D_q,K^H_q] = H_q - I.                                  (256)
```

If `Re(a)=0`, equation `(253)` and antisymmetry of the clock denominator give

```text
(K^H_q)^* = -K^H_q,
[D_q,K^H_q]^* = [D_q,K^H_q].                            (257)
```

Thus the countertransport preserves the reflected Hodge sector at operator level, not merely at
the level of a scalar cycle.

Its cofinal capacity has a sharp unconditional classification.  Let

```text
UB(a) := exists C, forall i j in I, ||H_a(i,j)|| <= C.
```

Because

```text
||H_a(i,j)|| = exp(Re(a) (lambda_j-lambda_i)),
```

one has

```text
UB(a) <-> Re(a)=0.                                       (258)
```

The reverse direction has bound `C=1`.  For `Re(a)>0`, keep prime `2`, orient depth `0` toward
depth `e`, and obtain `exp(Re(a) e log 2) -> infinity`.  For `Re(a)<0`, reverse the orientation.
This uses arbitrarily separated valuation depths at one fixed prime; it requires no prime-gap
input and no numerical experiment.

Specializing to actual Xi divisor supports produces the unconditional capstone

```text
exists C, forall rho in XiDivisorSupport, forall i j in I,
  ||H_(rho-1/2)(i,j)|| <= C
  <-> RiemannHypothesis.                                  (259)
```

Equation `(259)` is an equivalence, not a proof of its left side.  It prevents capacity language
from laundering the missing theorem: uniform all-depth reflected capacity is exactly RH.

There is a stronger finite spectral no-go.  On a packet `q`, define the diagonal vertex gauge

```text
G_a(q)=diag_i(exp(a lambda_(q_i))),
G_a(q)^(-1)=diag_i(exp(-a lambda_(q_i))).                (260)
```

Equations `(249)--(250)` give the full matrix identity

```text
P_(eps,a)[q] = G_a(q)^(-1) P_(eps,0)[q] G_a(q).          (261)
```

This is stronger than triangle flatness.  For every finite packet and every `m>=0`,

```text
charpoly(P_(eps,a)[q]) = charpoly(P_(eps,0)[q]),
det(P_(eps,a)[q])      = det(P_(eps,0)[q]),
trace(P_(eps,a)[q]^m)  = trace(P_(eps,0)[q]^m).          (262)
```

Therefore every finite similarity-invariant Julia/spectral consumer of the complete actual
off-diagonal incidence is horizontally blind.  Changing graph, packet size, determinant degree,
or trace moment cannot help; a successful finite consumer must break this vertex gauge by adding
nonseparable arithmetic incidence before taking spectral invariants.

The hostile prior-research audit changes the novelty verdict.  The failed
`orbitwise-source-divisor-seam-obstruction` card already proved the first-prime character to be a
coboundary and explicitly predicted coordinatewise flatness for the full prime-power grading.
General divided-difference commutators are also classical.  Therefore `(251)` alone is not new
knowledge.  The strict extension established here is the exact factorization of the literal
joint-depth primitive/co-source incidence, its Burnol conormal identification `(254)`, the source
countertransport identities `(255)--(257)`, the all-oriented-depth phase boundary `(258)`, and the
complete finite gauge-similarity/spectral blindness law `(260)--(262)`.  These close the separable
normalized-incidence/similarity-invariant spectral class without claiming novelty for its known
flat mechanism.

Route J remains open.  The constructed source object shows exactly why it is insufficient: its
normalized edge field is a vertex-potential quotient.  The remaining object must be a genuinely
nonseparable, non-coboundary prime/depth--divisor incidence whose arithmetic differential is not a
function only of `lambda_j-lambda_i`.  It must carry an independently proved source law forcing a
nontrivial reflected edge—or equivalently the Burnol discriminant—to vanish.  Uniform capacity,
Hodge compatibility, or loop closure cannot be assumed; the first two are RH-equivalent and the
third is identically true.

Lean realization:

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthOffDiagonalCountertransport.lean
```

The module proves `(247)--(262)` unconditionally, including both actual and normalized finite
countertransports, skew-Hermitian Hodge preservation, same-prime cofinal escape in both
orientations, the Xi-support/RH equivalence, explicit finite diagonal similarity, characteristic
polynomial invariance, determinant invariance, and invariance of all trace powers.  No
divisor-location hypothesis is used in any source construction or local capacity theorem.
