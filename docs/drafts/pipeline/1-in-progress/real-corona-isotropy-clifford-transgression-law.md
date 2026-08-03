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
  and `D_even=D`.  Lean now encodes every finite positive local formula as a linear combination of
  words in bounded iterated commutator extensions; every such word vanishes.  Its degree-zero
  completion is any absolutely summable reflection-invariant spectral weight, and its oriented
  trace cancels orbitwise.  The same cancellation holds exactly on every finite reflection-stable
  truncation.  Hence no complete-divisor-compatible local formula can reproduce the nonzero graded
  cyclic charge `2`.  P1 has a negative answer for the canonical non-doubled complete-divisor
  triple: `[m]` is a nonlocal graded cyclic class, not a local index class.

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
- [x] P1 complete-divisor local-index no-go
- [ ] P3 smoothness classification
- [x] P4 family analytic-rank theorem
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
- 2026-08-03 — `RealCoronaLocalCyclicNoGo.lean` closes P1 rather than stopping at first-order
  obstruction. An all-orders smooth commutator jet defines local words; every positive word for an
  exactly commuting orientation is the zero operator. Finite linear combinations evaluated by
  arbitrary additive residue/trace functionals therefore vanish. In degree zero, every summable
  reflection-invariant spectral weight has zero oriented `tsum`, and every finite reflection-stable
  truncation has zero oriented sum without a limit argument. A complete local formula is the sum
  of these degree-zero and positive pieces. Lean proves its value is always zero and therefore can
  never equal the graded cyclic charge `2`. Selected theorems are axiom-clean modulo `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-03 — P2 no longer uses a cyclic-module placeholder. Lean now contains the exact
  generator-and-relation simplex presentation, genuine cyclic-bar tensor powers of arbitrary
  unital noncommutative algebras, all face/degeneracy/rotation identities, and the resulting cyclic
  module (`PresentedSimplicialObject.lean`, `CyclicBarTensorOperators.lean`,
  `CyclicBarSimplicialTupleRelations.lean`, `CyclicBarSimplicialLinearRelations.lean`,
  `CyclicBarPresentedSimplicial.lean`, `CyclicBarCyclicTupleRelations.lean`,
  `CyclicBarCyclicLinearRelations.lean`, `CyclicBarCyclicModule.lean`). The actual rational CCM
  coefficient algebra and finite-support twisted crossed product are also present, followed by its
  minimal unitization; no all-functions algebra, free-word object, or degree-zero truncation remains.
- 2026-08-03 — `CCMRationalAdelicEpsilonZero.lean` constructs the exact first CCM endpoint on that
  source: zero-adele evaluation is proved multiplicative and rational-scaling invariant; the
  identity coefficient is proved a trace for twisted convolution; and its normalized unitized
  extension is proved a trace. `CyclicBarTraceAugmentation.lean` and
  `CyclicBarTraceMorphism.lean` prove universally that every linear trace induces a morphism from
  the genuine tensor cyclic bar to the constant scalar cyclic module, natural for every morphism
  of the presented simplex category and for Connes rotation. `CCMRationalAdelicEpsilonZeroCyclic.lean`
  instantiates the result as the literal all-degree morphism `ε₀ⁿ`.
- 2026-08-03 — `CyclicModuleDoubleKernel.lean` constructs the exact categorical operation needed
  for CCM's reduced source: for any two cyclic morphisms, the degreewise intersection of their
  kernels inherits every face, degeneracy, and cyclic rotation, with a canonical cyclic inclusion.
  This will instantiate `ker ε₀ⁿ ∩ ker ε₁ⁿ` once the second endpoint is built.
- 2026-08-03 — Honest `ε₁` audit exposed a concrete upstream formalization gap rather than a
  mathematical ambiguity: mathlib's `IsDedekindDomain.FiniteAdeleRing ℤ ℚ` currently has its
  restricted-product topology and topological-ring structure, but no measurable-space,
  locally-compact-space, or Haar-measure instance. Consequently the genuine finite-adelic Haar
  integral cannot yet be typed. The required route is frozen: import/prove compactness of every
  rational adic integer ring using the finite-place DVR and finite-residue-field theorems, apply
  restricted-product local compactness, install Borel and additive Haar measure, prove the
  rational diagonal product formula for Haar scaling, then define `ε₁`, its trace law, and `ε₁ⁿ`.
  Replacing this with zero, evaluation at zero, or an assumed functional is explicitly forbidden.
- 2026-08-03 — Frozen `ε₁` infrastructure gap is now closed exactly. Lean constructs local and
  restricted-product `T2` instances, proves the exact local quotient
  `ℤ_p / nℤ_p ≃+ ZMod (p^v_p(n))`, assembles the global integral-finite-adele index `n`, and derives
  normalized Haar mass `μ(nẐ)=n⁻¹`. `CCMRationalFiniteAdeleHaarCharacter.lean` then proves from
  numerator/denominator arithmetic—not an assumed product formula—that finite-adelic scaling has
  modulus `|q|_∞⁻¹`. `CCMRationalAdelicEpsilonOne.lean` tensors this Haar integral with Lebesgue
  integration, proves exact rational-scaling cancellation, constructs the genuine identity-
  coefficient trace and normalized unitized `ε₁`. `CCMRationalAdelicEpsilonOneCyclic.lean`
  promotes it to every cyclic degree and instantiates the exact reduced source
  `ker ε₀ⁿ ∩ ker ε₁ⁿ`. All modules compile without `sorry`, `axiom`, `opaque`, or `unsafe`.
- 2026-08-03 — Exact CCM Morita restriction infrastructure is no longer a placeholder.
  `CCMRationalAdelicMoritaMonomial.lean` proves orbit evaluation is multiplicative, inverse adelic
  scaling is inverse rational-orbit translation, twisted monomial multiplication is weighted-
  shift composition, and operator trace is supported exactly on the identity scaling sector.
  `CCMRationalAdelicMoritaRepresentation.lean` extends this to the full finite-support crossed
  product as a multiplicative linear representation and proves every image trace class.
  `CCMRationalMoritaTraceClassAlgebra.lean` constructs the actual nonunital trace-class operator
  algebra, its minimal unitization, normalized trace, unitized source homomorphism, and all-degree
  fixed-base cyclic trace morphism; the infinite-dimensional identity is never falsely declared
  trace class. `CCMRationalAdelicMoritaTraceFormula.lean` proves on every full source element that
  operator trace equals the rational-orbit sum of the identity-scaling coefficient.
- 2026-08-03 — Higher independent-variable CCM formula is now formal rather than aspirational.
  Scaling labels were corrected from a transported `Group` to their canonical `CommGroup`,
  retaining the actual commutativity of `ℚˣ`. `CCMRationalAdelicCyclicRestrictionFormula.lean`
  defines the primary-source formula
  `1_{∏k_j=1} Σ_{q∈ℚˣ} ∏_j t_j((∏_{i<j}k_i)⁻¹ q b_j)` on independent nonzero adelic Morita bases
  and proves absolute convergence using one `ℓ¹` orbit factor and exact uniform bounds on every
  tail factor. `CCMRationalAdelicCyclicRestrictionLinear.lean` proves multilinearity and uses
  mathlib's tensor-of-Finsupp equivalence to extend the formula canonically to the full algebraic
  nonunital cyclic-chain degree. Remaining P2 gate is the normalized unitized mixed-sector
  extension, proof of all face/degeneracy/rotation naturality identities, strong-Schwartz target
  completion and closed-range cokernel, then the concrete `κ`/bivariant-Chern/Lefschetz comparison.
- 2026-08-03 — `CCMRationalAdelicUnitizationDFinsupp.lean` adds the next non-negotiable mixed-
  sector layer. It proves an exact linear equivalence between the actual minimal unitization
  `ℂ ⊕ (𝒮(𝔸_ℚ)⋊ℚˣ)` and a dependent finitely supported family with one scalar label and one
  Bruhat-core fiber over every `k∈ℚˣ`. This makes the scalar unit algebraic and separate from the
  trace-class sectors while enabling mathlib's dependent tensor/Finsupp distribution theorem in
  every cyclic degree. The module compiles unconditionally; next construction is the normalized
  mixed-label generalized trace (all-scalar branch plus convergent non-scalar branches).
- 2026-08-03 — The normalized mixed-label gate is now dependency-closed.
  `CCMRationalAdelicUnitizedCyclicRestrictionFormula.lean` separates the finite all-scalar
  normalized trace from the orbit sum and reduces the all-crossed sector to the primary CCM
  formula. `CCMRationalAdelicUnitizedCyclicSummability.lean` proves absolute convergence of every
  non-all-scalar sector: an arbitrary crossed position supplies the translated `ℓ¹` head and every
  remaining scalar or crossed position has a uniform bound. No trace of an infinite-dimensional
  identity is used. `CCMRationalAdelicUnitizedCyclicRestrictionLinear.lean` proves dependent
  multilinearity, passes sums and scalar multiples through the absolutely convergent series, and
  distributes the result through dependent `DFinsupp`, tensor powers, and the exact source
  unitization equivalence.
- 2026-08-03 — Missing cyclic functoriality and the genuine class-space target are now present.
  `CyclicBarAlgHomMorphism.lean` proves that every algebra homomorphism induces a morphism of the
  full presented cyclic-bar modules, including every face, degeneracy, arbitrary simplex morphism,
  and Connes rotation. `CCMRationalAdelicClassSpaceCyclicModule.lean` assembles the fixed-base
  Morita representations into the pointwise algebra homomorphism from the actual unitized adelic
  crossed product to trace-class Morita sections over all nonzero adelic bases. It then constructs
  the literal all-degree cyclic restriction, its composition with `ker ε₀ ∩ ker ε₁`, and the exact
  algebraic cyclic cokernel. This replaces the earlier independent-base scalar formula as the
  target object: that formula is pairing data on the genuine class-space cyclic module, not a
  surrogate cyclic module. Remaining P2 gates are the strong-Schwartz locally convex target and
  closed-range cokernel, followed by the concrete `κ`/bivariant-Chern/CCM-Lefschetz comparison.
- 2026-08-03 — `SelfDualFixedSectorVariation.lean` closes P4 at family level. For arbitrary
  parameters it proves that cyclic fixed-sector defect variation is analytic-rank variation plus
  twice upper off-central multiplicity variation. The central Real-corona `K₀` evaluation varies
  only with the support indicator, and analytic-rank variation is exactly this `K₀` variation plus
  variation of central multiplicity excess. Thus `[e_R]` and analytic rank agree only in the
  multiplicity-free central sector; their general discrepancy is computed, not suppressed.
- 2026-08-03 — Coefficientwise projective topology and closed relative cyclic quotient are now
  formalized on the genuine CCM class-space target. `CyclicBarProjectiveContinuity.lean` proves
  norm bounds and continuity for every face, degeneracy, and cyclic rotation on projective tensor
  powers. `CCMRationalAdelicClassSpaceCyclicContinuity.lean` proves that all class-space evaluation
  maps intertwine these operators and makes the induced section-chain topology cyclic.
  `CCMRationalAdelicClosedRelativeCyclicModule.lean` proves continuity for every presented simplex
  morphism and constructs the quotient by the closure of the actual reduced restriction range.
  `CCMRationalMoritaTraceClassAlgebra.lean` now supplies the exact norm-one unit required for
  degeneracy continuity. This is a dependency-closed coefficientwise-projective model, not yet the
  primary-source strong target: CCM requires continuous trace-class-valued chains whose scalar trace
  on the main diagonal lies in `S(C_Q) = intersection_beta mu^beta S(C_Q)`. P2 remains open until
  that exact diagonal-condition cyclic submodule, its closed cokernel, and the concrete
  `kappa`/bivariant-Chern/Lefschetz comparison are formalized.
- 2026-08-03 — The primary-source strong target itself is now exact and formal.
  `CCMRationalStrongCyclicTarget.lean` defines the degree-`n` main-diagonal functional by ordered
  multiplication of continuous trace-norm field factors followed by normalized operator trace,
  takes the inverse image of the literal strong class-space scalar space, and proves that every
  face, degeneracy, arbitrary presented simplex morphism, and Connes rotation preserves this
  condition. `CCMRationalStrongCyclicReal.lean` proves the diagonal Real law
  `Tr^natural(sigma x)(b) = conjugate(Tr^natural(x)(b))` and restricts the even Real structure to
  the full strong cyclic module. `CCMRationalStrongCyclicClassSpaceAction.lean` constructs the
  exact `C_Q` right action and proves diagonal covariance; `CCMRationalStrongCyclicLefschetz.lean`
  proves identity/product laws in every degree and packages each translation as a Real-equivariant
  cyclic endomorphism. These modules compile unconditionally and supply the genuine target-side
  CCM Lefschetz architecture. P2 is still open at the analytic landing gate: the adelic source
  representation must be proved continuous in the Schatten-1 norm over the literal section, the
  reduced diagonal trace must land in the strong target in all degrees, and only then may the
  closed cokernel action and `kappa`/bivariant-Chern comparison be claimed.
- 2026-08-03 — Exact Schatten-`1` source continuity and all-degree reduction are now closed.
  `CCMRationalWeightedShiftTraceNormBound.lean` proves the sharp identities
  `‖W_{a,k}‖₁=∑_q‖a(q)‖` and `‖W_{a,k}-W_{d,k}‖₁=∑_q‖a(q)-d(q)‖`; the associated
  linear isometry packages weighted shifts as a genuine `ℓ¹` model. Uniform Schwartz-lattice
  envelopes, one profinite denominator, and dominated convergence then prove joint class-section
  continuity for pure tensors, algebraic Bruhat tensors, the full finite-support crossed product,
  and finally the exact unitized source algebra in
  `CCMRationalAdelicSourceContinuousTraceNormField.lean`. No operator-norm proxy occurs.
  `CCMRationalAdelicStrongCyclicDegreeReduction.lean` proves the exact unitized rational-orbit trace
  formula and the universal reduction law
  `Trⁿ(ρⁿ(x)) = Tr⁰(ρ⁰(∏ x_j))`; both cyclic endpoint augmentations are likewise the
  endpoint traces of `∏ x_j`. Hence every cyclic degree of reduced strong landing follows from one
  and only one analytic theorem: if `ε₀(y)=ε₁(y)=0`, the full finite-adelic degree-zero orbit
  trace of `y` lies in the locally constant, all-derivative, all-exponential-weight class-space
  target. Remaining P2 gate is precisely that finite-adelic Poisson theorem, followed by closed
  strong cokernel descent and concrete `κ`/bivariant-Chern/CCM-Lefschetz comparison.
