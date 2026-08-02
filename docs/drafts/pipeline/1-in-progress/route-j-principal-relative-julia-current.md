# Route J principal-relative Julia current

- **ID:** `route-j-principal-relative-julia-current`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / SOURCE CONSTRUCTION / NO-GO CLASSIFICATION
- **Scientific status:** `[OPEN] [ROUTE J OWNER] [NO RH INPUT] [NO COMPUTATION]`
- **Parent no-go:** `../5-failed/route-j-julia-unrenormalized-coherent-energy-budget.md`
- **Endpoint:** Route A's literal first-clock source is eventually bounded below

## Mission

Classify every Julia-coherent implementation of a principal-relative completed first-clock
capacity and construct one unconditionally or prove a class-complete no-go.  Target equivalence and
overlap with another route do not discharge this card while a source-defined current remains
researchable.

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

Route J remains open.  Concrete natural subclasses are closed and the representation-free
existential is target-equivalent to Route A, but neither fact eliminates the explicit completed
current problem above.  As long as that construction or a class-complete no-go remains
researchable, this card stays in Stage 1.

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
- [ ] construct a completed symmetric/nonlinear current satisfying `(2)`, or prove the surviving
      class impossible
- [ ] close Route J only when no researchable unowned survivor remains

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
