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

### `J-SF6` — Xi Taylor theta-tail oriented current `[OPEN INPUT]`

The finite theta-tail source has an exact signed current and a fully arithmetic two-term remainder
bridge.  Its remaining joint sublinear bound is equivalent to RH, so it cannot be imported as an
estimate.  It is nevertheless a source-defined odd current before scalar fusion, and the
full-density decomposition proves that all unresolved positive contribution lies in one canonical
finite-truncation transfer current.  Route J must test an exact transgression from that transfer
current to `(2)`, or prove that no Julia/Gamma/co-Poisson transgression preserves its sign.  Merely
calling the Taylor current a different route would leave a source-current survivor unexamined.

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
