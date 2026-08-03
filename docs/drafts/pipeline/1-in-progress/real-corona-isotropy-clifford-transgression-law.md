# Real-corona isotropy--Clifford transgression law

- **ID:** `real-corona-isotropy-clifford-transgression-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed algebraic bridge
- **Parent:** `../4-publication-ready/real-corona-quaternionic-cyclic/CARD.md`
- **Lean targets:** `GaloisForLFunctions.RHTower.RealCoronaUniversalTransgression`,
  `GaloisForLFunctions.RHTower.RealCoronaLocalDetectabilityFracture`, and
  `GaloisForLFunctions.RHTower.RealCoronaCompleteDivisorDetectability`
- **Statement:** exchanged sectors create bounded quaternionic orientation and graded cyclic
  charge, fixed sectors create the complete Tate defect, but a nonzero unbounded odd Dirac
  operator cannot contain its own exchanged projector in the Lipschitz algebra.

## Public sentence

Symmetry can turn paired spectral sectors into quaternionic orientation, but the same exchange
prevents that orientation from being a smooth local coordinate; fixed spectral points are the
exact residue left by this fracture.

## Frozen universal conjecture

`[CONJECTURE] [ISOTROPY_CLIFFORD_TRANSGRESSION]`

Let a complete bornological Real algebra carry a smooth involution and a complete central orbit
decomposition

```text
1 = e_plus + e_fixed + e_minus,
sigma(e_plus) = e_minus,
sigma(e_fixed) = e_fixed.
```

Put `m = e_plus - e_minus`. The Real equivariant Chern character admits a canonical and exhaustive
two-channel factorization:

```text
free C2 orbits   -> Clifford/Morita parity transgression of m,
fixed C2 orbits  -> fixed-locus Tate class of e_fixed.
```

After crossed-product descent, the free orientation is an ordinary cyclic boundary but its
Clifford-transgressed class is the graded survivor. The fixed channel is not transgressed: it is
the complete obstruction to quaternionification. No third channel exists. For every regular
unbounded realization, the JLO/bivariant character of these two channels agrees with the
corresponding Lefschetz fixed-orbit decomposition.

The final sentence is frozen without a proof route. It is the hard P1--P2 core and is not admitted
to a paper until unconditional.

## Dependency-closed bridge

`[BRIDGE] [BOUNDED_TO_LOCAL_FRACTURE]`

Let `V` be a normed complex vector space, let `e,m,D : End_C(V)`, and assume

```text
m = 2 e - 1,
m^2 = 1,
D m = -m D,
||m x|| = ||x||.
```

Then, pointwise,

```text
[D,e] = D m,
||[D,e] x|| = ||D x||.                                    (F)
```

Consequently `[D,e]` is bounded on a common invariant domain exactly when `D` is bounded there.
In particular, if `D` is genuinely unbounded, `e` cannot belong to the Lipschitz algebra of a
graded spectral triple whose oddness is implemented by the same orientation `m`.

### Proof

From `m=2e-1` and `Dm=-mD`,

```text
2(De-eD) = D(2e-1) - (2e-1)D = Dm-mD = 2Dm.
```

Scalar cancellation gives `[D,e]=Dm`. Oddness gives `Dm x=-mD x`; isometry of `m` gives `(F)`.
The boundedness equivalence is immediate from equality of pointwise norms on the common domain.

This bridge is not the primary conjecture: its proof route is visible and it supplies a hostile
constraint on possible realizations.

## Proven universal law: smoothness--detectability conservation

`[THEOREM] [C2_SMOOTHNESS_DETECTABILITY_CONSERVATION]`

For every domain-preserving isometric involution `m` and partially defined complex-linear
operator `D`, define

```text
D_even = (D + m D m)/2,      D_odd = (D - m D m)/2.
```

On the exact common domain,

```text
D = D_even + D_odd,
D_even m = m D_even,
D_odd m = -m D_odd,
[D,m] = 2 D_odd m,
||[D,m]x|| = 2 ||D_odd x||.                            (U)
```

Thus `m` is Lipschitz exactly when the detecting component `D_odd` is bounded.  If `D` is
genuinely unbounded and `m` is Lipschitz, every unbounded direction is forced into `D_even`, where
the first local commutator cannot see it.  Exact commutation promotes a bounded operator to an
all-orders smooth element whose positive iterated commutators are all zero; a genuinely unbounded
first commutator excludes every all-orders smooth representative.

For the actual multiplicity-exact Xi divisor this yields both extremal realizations:

```text
absolute energy |rho-1/2|:
    reflection is all-orders smooth, but orientation is erased;

signed energy eps(rho)|rho-1/2|:
    reflection detects the sign and is genuinely non-Lipschitz,
    diagonal Real-corona orientation remains all-orders smooth but locally blind.
```

Functional-equation reflection conjugates the diagonal orientation to its negative.  Therefore
the crossed-product generator carrying cyclic transgression is precisely the generator excluded
from the signed local smooth algebra.  P1 trace blindness, P2 need for a nonlocal bivariant
transgression, and P3 smoothness failure are three consequences of `(U)`.  Fixed orbits form the
collateral channel through `m^2=1-e_fixed`; ordinary `K_0` records its support while cyclic pairing
records multiplicity, with exact difference equal to multiplicity excess.

## Existing findings as shadows

| Existing finding | Universal shadow map |
|---|---|
| `e#=1-e`, `m^2=1`, `m#=-m` | free `C2` orbit orientation |
| `J=m#`, `J^2=-1` | Clifford parity transgression on free orbit |
| `m_0^2=1-e_fixed`, `J_0^2=-(1-e_fixed)` | fixed-isotropy defect channel |
| anti-Real `K_0` class | free-orbit orientation before descent |
| `m=[eu,ue]` and ordinary trace blindness | crossed-product boundary of free channel |
| nonzero supertrace | graded Morita image of free channel |
| real-zero obstruction | fixed-locus Tate support |
| corona theorem | analytic existence theorem for universal orbit idempotents |
| Mellin--Hardy globalization | one bounded realization of universal decomposition |

## P1--P4 obligations

### P1: local index formula

Every domain-preserving involutive orientation has the exact decomposition

```text
D_even = (D + mDm)/2,        D_odd = (D - mDm)/2,
[D,m] = 2 D_odd m.
```

Hence boundedness of `[D,m]` is equivalent to boundedness of `D_odd`; if `D` is genuinely
unbounded while `[D,m]` is bounded, every unbounded direction lies in the commuting, locally
invisible even sector.  On the actual multiplicity-exact Xi divisor, take the unconditional
self-adjoint maximal diagonal with energy `|rho-1/2|`.  Its spectrum escapes every bound, but the
canonical functional-equation orientation commutes with it exactly.  Thus `[D,m]=0`, `D_odd=0`,
and `D_even=D`.  A local cocycle generated only by grading commutators is therefore identically
blind on this complete-divisor realization.  Remaining P1 obligation is chain-level: construct the
universal commutator-generated local cyclic/JLO subcomplex and prove its realized pairing with
`[m]` vanishes in every positive local degree, including the degree-zero normalization boundary.

### P2: adelic lift

Construct a chain-level idempotent on the CCM cokernel cyclic module, not merely an idempotent on
its Hardy realization. Prove that its bivariant Chern character maps under realization to the
orientation-weighted Lefschetz character. A homology-level spectral projector does not suffice.

### P3: smoothness classification

Smoothness is now defined in Lean at all orders: every iterated commutator must have an
everywhere-defined bounded extension preserving the exact Dirac domain.  On the actual Xi divisor,
absolute energy makes reflection all-orders smooth; signed detecting energy makes any smooth
reflection representative impossible already at first derivative; diagonal orientation is
all-orders smooth but has identically zero positive derivatives.  Remaining classification task
is automorphic uniformity: construct the complete multiplicity divisor for the stated completed
automorphic class and prove its signed energies are bounded exactly in the exceptional finite-
divisor cases.

### P4: fixed sector and analytic rank

For each self-dual family member, decompose the fixed idempotent into central and off-central real
fibres. Prove

```text
rank(e_fixed) = analytic_rank + 2 * upper_off_central_real_multiplicity,
```

and hence equality with analytic rank exactly when no off-central real zero occurs. The theorem
must be multiplicity-exact and compatible with specialization in the family.

## Closest parent theories and unoccupied residue

- Green--Julg descent and equivariant Chern characters already relate equivariant `K`-theory to
  crossed products.
- Karoubi/Atiyah--Bott--Shapiro theory already identifies Clifford modules with parity shifts.
- Periodic cyclic homology of finite-group crossed products already localizes at fixed strata.
- Reflection Tate cohomology of permutation lattices already leaves mod-two charge at fixed
  labels; this is formalized in `HTGeometry.ReflectionTateAnomaly`.

Therefore orbit splitting alone is rediscovery. Unoccupied residue is simultaneous theorem that
identifies the same concrete corona orientation across Real Morita descent, crossed-product cyclic
transgression, unbounded smoothness obstruction, and fixed-sector analytic rank, with exact chain
maps and no external doubling.

## Falsifiers

1. A regular non-doubled complete-divisor triple with unbounded `D`, grading `m`, and bounded
   `[D,e]` falsifies the fracture law.
2. An additional independent cyclic channel not generated by free or fixed orbit strata falsifies
   exhaustiveness.
3. A CCM chain lift whose realized Chern character differs from the oriented Lefschetz character
   falsifies P2 compatibility.
4. A self-dual family member with no off-central real zeros but fixed-defect rank different from
   central vanishing order falsifies P4.

## Risky consequence

For every infinite complete divisor, the canonical non-doubled quaternionic orientation is a
bounded/entire cyclic phenomenon but not a local Lipschitz idempotent for an unbounded odd operator
implementing that same exchange. Thus P1 and P3 cannot both have affirmative intrinsic answers;
any affirmative local index formula must exhibit and account for an additional Clifford
stabilization or a different Dirac parity.

## Gates

- [x] internal corpus and failed-route collision search
- [x] primary-literature parent audit
- [x] frozen universal conjecture
- [x] dependency-closed proof of bounded-to-local fracture bridge
- [x] unconditional Lean proof of fracture bridge
- [ ] exact chain-level P2 lift
- [ ] P1 chain-level local-index no-go (operator theorem proved)
- [ ] P3 smoothness classification
- [ ] P4 family analytic-rank theorem
- [ ] full universal Chern-character factorization
- [ ] all-paper-claims Lean coverage

## Log

- 2026-08-03 — created in `1-in-progress`; orbit-only formulation rejected as parent
  Green--Julg/Karoubi/fixed-stratum theory; bounded-to-local fracture isolated as new hard residue.
- 2026-08-03 — `RealCoronaUniversalTransgression.lean` upgraded bridge from an everywhere-defined
  endomorphism surrogate to an exact `LinearPMap` on the invariant dense domain. Lean proves
  `[D,e]=Dm`, `‖[D,e]x‖=‖Dx‖`, `[D,m]=2Dm`, and `‖[D,m]x‖=2‖Dx‖`; both bounded-commutator
  conditions are equivalent to boundedness of `D`. A self-adjoint intrinsic odd datum therefore
  has dense closed domain but admits neither first-order local-index regularity for `m` nor
  first-order smoothness for `e`.
- 2026-08-03 — P4 sharpened by self-dual reflection. For every finite real-zero multiplicity
  function invariant under `x ↦ 2c-x`, Lean proves
  `defectRank = analyticRank + 2 * upperOffCentralMultiplicity` and the parity congruence
  `defectRank ≡ analyticRank (mod 2)`. Application to analytic families and identification with
  the actual `K₀` rank remain required before closing P4.
- 2026-08-03 — `SelfDualAnalyticRealZeros.lean` removes the supplied-multiplicity abstraction:
  compact-window real-zero support is derived from isolated zeros of a nontrivial entire completed
  function, coefficients are its exact `analyticOrderAt`, and the functional equation proves
  reflection symmetry. Lean also proves `ε² = 1`, `ε ∈ {±1}`, and
  `(-1)^analyticRank = ε`. `SelfDualDirichletRealZeros.lean` instantiates this construction on the
  actual family of nontrivial primitive self-dual Dirichlet characters, proving the multiplicity-
  exact defect formula and root-number parity for completed automorphic GL(1) L-functions.
  Remaining P4 gate is identification of this defect rank with the rank map of the paper's concrete
  Real-corona `K₀` idempotent; no abstract declaration is accepted as that identification.
- 2026-08-03 — Hostile K-theory audit found that literal identification is false for multiple
  zeros. `RealCoronaKZeroMultiplicityFracture.lean` constructs the finite-coordinate fixed
  idempotent, its genuine Grothendieck `K₀` class, total rank and evaluation rank. Lean proves
  `cyclicDefect = KZeroSupportRank + multiplicityExcess`; central `K₀` evaluation equals analytic
  rank iff central multiplicity is at most one. Thus ordinary `K₀` detects occupied real-zero
  support, while the cyclic pairing detects analytic multiplicity. For self-dual families both
  sides obey the same central-plus-twice-upper orbit law with respectively support and multiplicity
  weights. This support--multiplicity fracture is the correct P4 comparison and a new fixed-channel
  shadow of the universal transgression law. All selected theorems pass `#print axioms` with only
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-03 — `RealCoronaLocalDetectabilityFracture.lean` proves the exact orientation
  even/odd decomposition for arbitrary densely defined `LinearPMap`s on invariant domains:
  `[D,m]=2 D_odd m`, pointwise norm equality, bounded-commutator iff bounded odd part, and forced
  concentration of all compatible unboundedness in `D_even`.  No self-adjointness or spectral
  hypothesis is used. `RealCoronaCompleteDivisorDetectability.lean` then constructs the actual
  maximal self-adjoint diagonal on all multiplicity copies of the Xi divisor with energy
  `|rho-1/2|`; cofinite escape of Xi spectral norms proves genuine unboundedness.  The canonical
  functional-equation orientation is a norm-preserving involution preserving the maximal domain,
  commutes exactly with this operator, and has zero odd part and zero first commutator.  Selected
  theorems pass `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.  This is
  an actual complete-divisor P1 obstruction, not an everywhere-defined operator surrogate.
- 2026-08-03 — `RealCoronaSpectralSmoothness.lean` adds the missing all-orders notion rather than
  treating first commutation as a synonym for smoothness: a witness stores every bounded iterated
  commutator extension and exact domain invariance. Exact commutation constructs such a witness;
  a genuinely unbounded first commutator excludes all witnesses.  In
  `RealCoronaCrossedProductSmoothnessFracture.lean`, functional-equation reflection, absolute and
  signed self-adjoint complete-divisor Dirac operators, their maximal domains, and the signed
  energy reversal are all constructed on the actual Xi-zero Hilbert carrier. Lean proves the
  absolute reflection is all-orders smooth, the signed reflection has genuinely unbounded first
  commutator and no smooth representative, diagonal orientation is all-orders smooth but
  commutator-blind, and reflection conjugates orientation to its negative.  This establishes the
  smoothness--detectability conservation law on the genuine complete divisor. Selected axioms are
  again only `propext`, `Classical.choice`, and `Quot.sound`.
