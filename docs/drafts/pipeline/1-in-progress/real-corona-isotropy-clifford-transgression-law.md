# Real-corona isotropy--Clifford transgression law

- **ID:** `real-corona-isotropy-clifford-transgression-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed algebraic bridge
- **Parent:** `../4-publication-ready/real-corona-quaternionic-cyclic/CARD.md`
- **Lean target:** `GaloisForLFunctions.RHTower.RealCoronaUniversalTransgression`
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

First falsifier: any proposed non-doubled triple with grading `m`, unbounded `D`, and `e` in its
Lipschitz algebra contradicts `(F)`. A solution must either prove no such local formula exists or
identify a genuinely different unbounded representative and prove its JLO/local residue formula.

### P2: adelic lift

Construct a chain-level idempotent on the CCM cokernel cyclic module, not merely an idempotent on
its Hardy realization. Prove that its bivariant Chern character maps under realization to the
orientation-weighted Lefschetz character. A homology-level spectral projector does not suffice.

### P3: smoothness classification

Classify smoothness relative to the actual derivation used by the unbounded realization. Equation
`(F)` predicts emptiness for the intrinsic non-doubled graded realization with infinite divisor;
boundedness of the corona representative alone cannot imply spectral smoothness.

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
- [ ] P1 local-index theorem or unconditional no-go
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
