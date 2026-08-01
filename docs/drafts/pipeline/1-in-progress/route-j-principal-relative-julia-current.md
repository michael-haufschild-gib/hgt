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
