# Dyadic weld--Weyl multiplicity route

- **ID:** `dyadic-weld-weyl-multiplicity-route`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / exact RH chain with one open source-realization core
- **Source:** `bottcher-exact-pruefer-monodromy.md`, `weld-class-table.md`,
  `sem-integral-fitting-charge.md`, `multiplicity-parity-ladder-route.md`

## Claim and chain

The corpus contains two structures that have not previously been collided:

1. disconnected quadratic Böttcher continuation supplies the coherent primitive phases
   `zeta_k = exp(2 pi i / 2^k)` of exact order `2^k`;
2. the founding derivative--difference weld supplies a rank-two generator lattice and a
   Heisenberg-type 2-cocycle.

The source phase gap is now closed more directly.  `PrimeDyadicWeyl.lean` exponentiates the actual
prime--derivative commutator: spectral translation by
`-2*pi*i/(2^k log p)` and multiplication by the `p`-Euler exponential obey the exact projective
relation with multiplier `Bottcher.dyadicRoot k`.  Böttcher monodromy therefore names the same
coherent phase, but is no longer required to manufacture it.

The proposed long chain is

```text
exact prime dyadic translation--Euler Weyl relation
  -> nonlocal descent to a projective action (U_k,V_k) on each actual finite SEM hole space
  -> U_k V_k = zeta_k V_k U_k, with U_k,V_k invertible
  -> 2^k divides the hole-space dimension
  -> RHLadder k
  -> all k, or cofinally many k
  -> RH.
```

The determinant step is unconditional algebra.  If `U,V` are invertible endomorphisms of a
finite-dimensional complex space of dimension `d` and

```text
U V = zeta V U
```

with `zeta` primitive of order `n`, then taking determinants gives

```text
det(U)det(V) = zeta^d det(V)det(U).
```

Cancellation gives `zeta^d=1`, hence `n | d`.  At `n=2^k`, one Weyl pair therefore forces the
whole rung `k`.  This is strictly leaner than the Clifford presentation: it replaces `2k`
anticommuting complex structures by one projective rank-two action.

## Two-ended closure audit

### Source end

- `[PROVED]` The Böttcher multiplier `zeta_k` exists at every depth and has exact order `2^k`.
- `[PROVED]` The actual prime translation and Euler multiplication operators satisfy the exact
  level-`k` Weyl relation with this phase.
- `[PROVED]` Actual finite SEM hole spaces exist unconditionally and their dimension is the central
  `xi` order.

These facts do **not** yet give an action on the same object.  The global translation has no fixed
spectral point at a nontrivial dyadic step, while the SEM hole space is pinned at one centre.

### RH end

- `[PROVED]` A dyadic Weyl relation on the actual hole space forces `2^k`-divisibility of its
  dimension.
- `[PROVED]` Divisibility for every right-half zero is `RHLadder k`.
- `[PROVED]` All rungs, or a cofinal set of rungs, imply RH.

Thus the chain reaches RH exactly and does not stop at parity, a spectral analogy, or a restatement
without a source object.

## No-go attack and positive residue

### Rank-one Prüfer monodromy alone is insufficient

The Prüfer group is abelian and divisible.  Every homomorphism from it to a finite group is trivial,
and a single cyclic projective representation over `C` supplies no nondegenerate alternating
commutator pairing.  Pontryagin duality changes it to the procyclic group `Z_2`; this exposes finite
quotients but still only one generator.  Therefore the direct chain

```text
Prüfer monodromy -> finite charge -> RH
```

is dead.

**Positive statement:** dyadic depth becomes multiplicity-forcing only after a second independent
generator and a nontrivial projective commutator are retained.  The missing datum is not another
root tower; it is a rank-two incidence law.

### External Weyl modules are vacuous

Tensoring every hole space with the standard `2^k`-dimensional clock--shift module manufactures the
desired relation but also multiplies the dimension by `2^k`; it says nothing about the original
hole count.  Likewise, a projective action on an auxiliary Böttcher or weld carrier does not constrain
the SEM root space.

**Positive statement:** `U_k,V_k` must act internally on the actual finite SEM hole space, commute
with its local multiplication/operator model, and preserve the source-selected integral lattice
before scalar extension.  No external tensor factor is admissible.

### Real additive weld charges are insufficient

The existing weld-charge faithfulness dichotomy kills finite additive charges after passage through
the divisible real coefficient group.  Exponentiating a real cocycle after an arbitrary level-dependent
rescaling can manufacture `zeta_k`, but that phase is normalization-selected rather than source-selected.

**Positive statement:** the required projective multiplier must be read from the integral/dyadic
continuation lattice before real scalar extension, or from a non-additive determinant/monodromy
boundary.  The exact Böttcher Prüfer multiplier is a candidate source-selected phase.

### Finite prime--Weyl operators are excluded on the full real-divisor quotient

`prime-modulated-weyl-idealizer-collapse-on-xi-sampling.md` proves that every finite
shift--differential prime-Weyl operator preserving the full real-Xi sampling nullspace collapses to
a polynomial multiplier; all descended operators commute.  Such a carrier cannot realize a
nontrivial Weyl phase.

This does not kill the present route because the desired action is on a hypothetical off-line local
SEM hole algebra, not the full real-divisor sampling quotient.  It does kill the obvious finite-prime
implementation.

**Positive statement:** a viable internal Weyl action must be an all-prime/nonlocal incidence,
an infinite-prime closed operator, or an integral continuation action before descent to the real
sampling quotient.  Finite prime decoration is structurally too small.

### Born super-KMS covariance is a noninvertible shadow

`BornSuperKMSCovariance.lean` proves the diagonal covariance of the graded Gibbs weights under the
dilation isometries `mu_k`.  Odd dilations preserve parity; `mu_2` kills parity on its image.  These
are semigroup isometries, not two invertible operators on a finite SEM hole space, so they do not
inhabit `SEMDyadicWeylModel`.

**Positive statement:** the Born/Bost--Connes feeder must first pass to a source-defined unitary
dilation or crossed product (the dyadic solenoid/torsion sector), then prove that its clock and shift
descend internally to the SEM local algebra.  Scalar KMS covariance is not enough.

`FiniteIsometryBoundaryNoGo.lean` now rules out literal preservation of the proper-isometry defect
on the finite target.  Every finite matrix satisfying `U*U=1` automatically satisfies `UU*=1` and
has nonzero determinant.  Thus the Bost--Connes/Toeplitz range projection is intrinsically
infinite-dimensional: a unitary dilation enlarges the carrier, while a finite descent must replace
the defect by a cyclic boundary arrow.  The positive successor is therefore the same source
holonomy closure `h(1-zeta_k^d)=0`, not a separate KMS or Toeplitz mechanism.

### Hurwitz torsion sectors mix away the scalar zeta component

Rational Hurwitz shifts at denominator `2^k` carry the expected finite Fourier character table, so
translation of the residue class and multiplication by its character form a canonical external Weyl
pair.  But the Fourier decomposition mixes the trivial character (`zeta`) with nontrivial Dirichlet
characters.  Any determinant/multiplicity law applies to the full character packet; zeros of the
other `L`-functions can compensate the zeta multiplicity.  Projecting to the trivial character breaks
the irreducible Weyl action.

The publication-ready joint Hurwitz monodromy-character theorem does not repair this: its hypothesis
is monomial-character injectivity, the infinite/Zariski-dense regime, whereas rational torsion phases
deliberately fail that hypothesis.

**Positive statement:** a Hurwitz feeder would need a source-built projection whose complement has
independently controlled divisor modulo `2^k`, while retaining a nontrivial projective action on the
trivial sector.  Without that arithmetic isolation theorem, finite Fourier symmetry reads only total
packet multiplicity.

The character-line failure is now formal rather than heuristic.  `WeylCommonEigenspaceNoGo.lean`
proves that a nontrivial Weyl pair has no common nonzero eigendirection with nonzero eigenvalues.
Therefore a projector onto the scalar-zeta character line must break at least one generator.  The
positive replacement is a full `2^k`-orbit isolation or an independent modulo-`2^k` divisor theorem
for the complementary packet; one-dimensional character extraction cannot carry the action.

### QECC and chromatic moonshots reduce to the same open core

Prime qubits carry Pauli/Weyl operators, but their tensor-product dimension is external padding.  A
QECC route becomes substantive only after the actual SEM hole space is identified as the protected
logical space and the induced logical Pauli pair is proved source-built.  The chromatic sphere route
supplies cofinal torsion depth only in the additive `log zeta`/fracture-square register; exponentiation
and an internal action on the divisor are separate.

**Positive statement:** these moonshots do not add independent gaps.  They propose possible source
categories for the same precise object: a nonlocal crossed-product Weyl action on the undoubled SEM
hole algebra.

## Open core

`[OPEN CORE]` Descend the global prime dyadic translation--Euler Weyl pair, for every `k` and every
actual SEM split at a hypothetical right-half zero, to invertible endomorphisms `U_k,V_k` of the
undoubled finite hole space such that

```text
U_k V_k = Bottcher.dyadicRoot(k) V_k U_k,
```

with the following non-circularity conditions:

1. the action is functorially built from the global prime translation--Euler pair;
2. it acts on the actual SEM local algebra, not an external tensor enlargement;
3. its construction does not use the hole count, an assumed divisibility, a root of `xi`, or RH;
4. level coherence comes from the Prüfer squaring law;
5. the action is semilinearly compatible with the local coordinate: one generator may be local
   multiplication, while the other must twist `X` by `X -> zeta_k X`; requiring both generators
   to be linear over the complete local divisor-jet algebra is impossible.

The first concrete attack is a cutoff/incidence descent: compress the global translation--Euler
square around the SEM isolating annulus, retain its cross-boundary cochain, and test whether a
presentation-invariant boundary correction makes the induced finite operators invertible while
preserving the projective multiplier.  Literal pinned translation is excluded by
`primeDyadicClockStep_no_fixedPoint`; an external clock--shift tensor is excluded by the model type.

The algebraic descent defect is now closed by `CutoffWeylBoundary.lean`.  For a global pair
`UV=zeta VU` and idempotent cutoff `e`, the compressed defect is exactly

```text
(eUe)(eVe)-zeta(eVe)(eUe)
  = zeta[eV(1-e)][(1-e)Ue] - [eU(1-e)][(1-e)Ve].
```

Hence the remaining source theorem has three sharply separated clauses:

1. construct the SEM annulus cutoff and finite reduced operators from the global prime pair;
2. prove the two directed corner products satisfy the projective boundary-balance law;
3. prove the reduced operators are invertible on the undoubled hole space.

Clauses 2 and 3 together inhabit `SEMDyadicWeylModel`, after which the formal RH capstone applies.

For the concrete one-sided aperture used by the earlier compressed-prime-shift parallelogram card,
Euler multiplication commutes with the cutoff.  The new commuting-cutoff corollary therefore closes
clause 2 automatically: the compressed pair still obeys the exact dyadic Weyl relation.  What the
parallelogram work did not supply is clause 3.  A positive compressed translation has a boundary
kernel and is not invertible.  The live refinement is now:

> construct a source-defined wrap-around or boundary-completed translation on the SEM finite
> reduction, prove it invertible, and prove that its wrap holonomy preserves the dyadic Weyl phase.

The old parallelogram theorem supplies a faithful arithmetic carrier and Krein decomposition, but
its remaining contraction condition does not construct this boundary completion.

The truncated-local-jet test now excludes a generic cyclic completion more decisively.
`TruncatedJetWeylBoundary.lean` puts the clock `diag(1,zeta,...,zeta^(d-1))` on the canonical
coefficient basis and completes the one-sided shift by a top-to-bottom holonomy `h`.  The exact
wrap-entry Weyl defect is

```text
h (1-zeta^d).
```

For `h != 0`, the completed shift obeys the Weyl law if and only if `zeta^d=1`; at the depth-`k`
primitive phase this is already `2^k | d`.  Therefore neither a Sz.-Nagy/unitary dilation nor a
hand-chosen cyclic wrap can be treated as free completion machinery: preserving the internal phase
at the top boundary is precisely the multiplicity ladder being sought.

**Positive residue:** the source theorem must do more than produce an invertible wrap.  It must
construct a nonzero Euler--Gamma--SEM boundary holonomy and prove directly from source incidence
that it annihilates the canonical scalar top-jet anomaly `h(1-zeta^d)`, without assuming its second
factor vanishes.  This is now the smallest algebraic form of the open core.

A second local-algebra no-go corrects the category of that source theorem.
`LocalDivisorJetWeylNoGo.lean` proves that all endomorphisms of `C[X]/(X^m)` that are linear over the
whole local algebra commute; invertible ones can satisfy a projective relation only with phase one.
Thus a nontrivial dyadic pair cannot consist of two ordinary local-module automorphisms.

**Positive successor:** the action must live in the skew local algebra generated by multiplication
and a coordinate automorphism `sigma_k(X)=zeta_k X`, where

```text
sigma_k M_X = zeta_k M_X sigma_k.
```

This semilinear replacement is source-compatible with the global translation--Euler relation and
does not demand that both generators centralize the Jordan multiplication operator.  The sharpened
open core is to construct this coordinate twist from the actual SEM annulus/presentation, show that
it preserves the undoubled root space, and prove that its top-boundary holonomy closes.

The interior part of this semilinear successor is now unconditional and formalized:
`truncatedJetClock_oneSidedShift_weyl` gives the exact clock--one-sided-shift relation for every
dimension and every phase.  The clock is invertible, but the shift has zero determinant.  The gap
has therefore collapsed to a single boundary arrow: source the nonzero top-to-bottom incidence and
prove that adding it does not break the Weyl law.  Its failure is exactly `h(1-zeta_k^d)`.

The apparent Fitting/contour detour is now proven to be the same obstruction, not a second route.
`SEMTruncatedJetWeylCharge.lean` proves for every actual SEM split and every nonzero `h` that

```text
integralCharge_(2^k)(completed SEM contour) = 0
  iff zeta_k^d = 1
  iff h(1-zeta_k^d) = 0
  iff the top wrap entry of the truncated Weyl defect vanishes.
```

Thus “annihilate the source contour class” and “close the semilinear Weyl boundary” are literally
one open core.  The next detours must attack its source annihilation, not move between equivalent
charge readers.

The target end is now closed in the same coordinates:
`riemannHypothesis_iff_all_dyadicSEMPhaseHolonomies_close` proves that RH is equivalent to
`zeta_k^d=1` for every dyadic depth and every actual right-half SEM hole count.  The complete chain
is therefore typed from the source contour to RH.  Its sole unproved arrow is the source theorem
forcing these phase holonomies to close.

### Moving-fiber parallelogram: fixed-point escape but not charge annihilation

The large-prime limit makes the dyadic translation step arbitrarily small, so one can try to move
an isolating annulus around a four-edge prime translation--Euler commutator square rather than pin
translation at one zero.  This avoids `primeDyadicClockStep_no_fixedPoint`.

It also removes the determinant argument.  The edges act between different fibers, so the closed
square is a groupoid holonomy; it may have arbitrary scalar determinant even in rank one.  On the
unframed local divisor, scalar rescaling of the defining function is a unit gauge.  A framed
determinant line retains the phase, but source triviality of its loop holonomy is an extra theorem.

**Positive residue:** the moving square geometrizes the shared contour/Weyl class.  To turn it into
an RH proof one must construct a source-canonical determinant-line trivialization around the square.
By `SEMTruncatedJetWeylCharge.lean`, its failure is again exactly the completed-SEM dyadic contour
charge.  See `moving-fiber-prime-weyl-parallelogram.md`.

## Gates

- [x] 0 -> 1: exact source and RH endpoints identified; circular shortcuts killed
- [ ] 1 -> 2: construct the internal source-built Weyl action
- [ ] 2 -> 3: formalize the source action and connect it to the SEM hole model
- [ ] 3 -> 4: only after the complete RH chain is closed
