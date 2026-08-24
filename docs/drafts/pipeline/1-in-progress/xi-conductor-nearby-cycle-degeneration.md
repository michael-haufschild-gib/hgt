# Xi conductor nearby-cycle degeneration

- **ID:** RH-XCNC-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `s6.pdf`, Appendix B and Lemma 10.3; local Xi source/monodromy corpus
- **Statement:** Construct from fixed completed prime--Gamma/theta data, before Xi-zero selection, a proper arithmetic degeneration with reduced non-normal-crossing fibres over the Xi divisor and a nonzero conductor-supported source class whose specialization is the existing terminal multiplicity jet; prove the specialization image is exactly the corresponding monodromy-invariant submodule.

## Goal

Supply a non-circular producer for Xi thinning coherence: special-fibre admission, rather than an RH-equivalent classifier, must force the terminal source jet into monodromy invariants.

## Gates

- [x] 0 → 1 in-progress: exact source-purity and circularity obligations stated; internal/external audit opened
- [ ] 1 → 2 fully-proven: complete construction and dependency-closed specialization proof
- [ ] 2 → 3 formalized: exact unconditional Lean theorem, targeted build, axiom audit, lint pass
- [ ] 3 → 4 publication-ready: standalone paper and independent mathematical audit

## Approach

Audit three layers separately: (i) conductor Mayer--Vietoris and hidden torsion on a reduced non-normal fibre; (ii) proper nearby-cycle specialization and integral saturation; (iii) a literal pre-divisor prime--Gamma/theta construction identifying the conductor class with the nonzero terminal Xi jet. Reject any formulation in which layer (iii) assumes extension, invariance, physical admission, or critical-line placement.

## No-go closure

- **Exact killing theorem/mechanism:** pending hostile audit.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`.

## Log

- 2026-08-24 — Card opened. Paper mechanisms isolated: conductor-supported classes can disappear under normalization; in one explicit proper degeneration, special-fibre cohomology specializes isomorphically onto monodromy invariants. Exact unresolved burden is source-first Xi realization, not the abstract invariant classifier.

## 2026-08-24 corpus-first collision audit

### Existing results which this route may use but may not rename

- `FrankensteinGammaCompositionScaleZeroDescent.lean` constructs the literal theta terminal
  multiplicity jet and proves it nonzero at every Xi divisor point.  Its prime-cut isometric
  descent is already equivalent to critical-line placement.
- `MobiusThetaInternalJetCofinalComplexLanding.lean` constructs, before any fixed finite cutoff,
  the all-order theta source landing whose specialization at the analytic multiplicity is the
  first nonzero Xi jet.
- `NormalCrossingMinimalizationDescent.lean`,
  `NormalCrossingCriticalBaseChange.lean`, and
  `NormalCrossingFaceMatrixFactorization.lean` formalize normal-crossing derived base-change
  excess.  They do not construct a proper analytic degeneration or a nearby-cycle regulator.
- `RouteRDerivedScalarCartierBaseChangeWall.lean` proves that ordinary scalar Cartier derived
  specialization is contractible off neutral character; coefficient-faithful survival is already
  equivalent to `Re rho = 1/2`.  Thus ordinary derived base change cannot be inserted as the
  missing producer.
- `PairGroupoidBidescentLaw.lean` proves that exact vertical gluing preserves an arbitrary
  horizontal defect.  A one-parameter degeneration cannot force horizontal theta neutrality.
- `LocalDivisorJetAdamsMonodromy.lean` already proves quasi-unipotent Adams rigidity.  The missing
  input there is the same completed prime--Gamma geometric monodromy realization, not its scalar
  consequence.
- `CyclicParacyclicBoundaryDefectLaw.lean` already proves that one retained cyclic class under a
  coefficient-faithful equivariant landing forces target scalar monodromy one.  The missing input
  is construction of the landing.

### Paper mechanisms, exact scope

`s6.pdf`, Lemma 10.3, proves a conductor Mayer--Vietoris gluing law.  For a reduced normal-crossing
fibre `S`, a line bundle trivial on the normalization, and the conormal differential `dg`, the pair
`(eta* dg tensor e, 0)` glues uniquely.  It is nonzero, while its image in Kahler differentials is
torsion supported on the conductor and vanishes in the torsion-free quotient.  This is a mechanism
for a hidden coherent class, not a theorem that the class survives topological nearby cycles.

Appendix B, Theorem B.1, proves for one explicit proper torus degeneration that

```text
sp_q : H^q(W; Z) -> H^q(F; Z)
```

is injective and has image exactly `ker(T_q - 1)`.  Load-bearing ingredients are the local models
`t=z0`, `t=z0 z1`, `t=z0 z1 z2`, the complete nearby-cycle `E2` page, a degree-three Gysin class,
and integral saturation.  Inclusion in invariants plus equal rational rank is insufficient over
`Z`; saturation is essential.

The paper's global complex-threefold claim is not imported.  Only the dependency-closed local
conductor lemma, Appendix-B specialization mechanism, and explicit integral linear algebra are
treated as usable bridges.

### External collision and scope audit

- General local invariant-cycle theorems give surjectivity to monodromy invariants under properness
  and purity/regularity hypotheses; they do not identify a theta terminal jet with a conductor
  class and do not generally give integral injectivity.
- Unipotent nearby-cycle Grothendieck classes can depend only on the reduced zero fibre.  Therefore
  a reduced fibre or its `K_0` class cannot retain Xi multiplicity; marked-function, Cartier,
  filtration, or extension data are mandatory.
- Geometric regular-singular monodromy is quasi-unipotent, but applying this to the actual
  prime-dilation weight requires the unconstructed geometric-origin comparison already isolated
  in the corpus.

## Concrete pre-divisor degeneration

Let `t` be a universal disc coordinate and consider the Legendre cubic

```text
E_t : Y^2 Z = X (X-Z) (X-t Z)  in P^2.
```

Pull it back along the globally defined, theta-completed source map `t = XiC(s)`:

```text
E_Xi -> U,
U = {s : XiC(s) != 1},
Y^2 Z = X (X-Z) (X-XiC(s) Z).
```

This construction precedes zero selection.  It is proper because it is a closed analytic
subspace of `P^2 x U` over `U`.  At every Xi divisor point its reduced fibre is

```text
Y^2 Z = X^2 (X-Z).
```

On the affine chart `Z=1`, the equation is `y^2 - x^2(x-1)=0`.  Its only singular point is
`(0,0)`; its quadratic tangent cone is `y^2+x^2`, two distinct complex lines, so it is an ordinary
node.  The point at infinity is smooth.  Hence the fibre is reduced and non-normal with one
normal-crossing node.  Product with a fixed smooth projective curve gives surface fibres if the
threefold form of Lemma 10.3 is required.

The reduced nodal fibre is identical at every Xi zero and is therefore blind to horizontal
location and analytic multiplicity.  Multiplicity is instead retained by the scheme-theoretic
Cartier conormal

```text
I_Xi / I_Xi^2,  I_Xi = (XiC).
```

At a zero of order `m`, the generator `[XiC]` maps to its first nonzero valuation-graded term in
`m_rho^m/m_rho^(m+1)`; in the analytic coordinate this coefficient is the existing terminal jet,
up to the fixed factorial convention.  Thus the correct carrier is:

```text
reduced nodal fibre + nonreduced Cartier/conormal ramification channel.
```

Using `d XiC` alone is false for repeated zeros because every derivative below order `m` vanishes.

## New framework: bivariant conductor--ramification phase topology

The proposed higher object has two transverse specialization axes:

```text
vertical geometric axis:
  universal semistable node t -> 0
  -> conductor class
  -> proper nearby cycles
  -> Picard--Lefschetz monodromy invariants;

horizontal arithmetic axis:
  completed prime--Gamma/theta source
  -> Cartier ramification [XiC]
  -> all-order terminal jet
  -> prime-log/paracyclic phase monodromy.
```

Neither axis generates zeros.  Xi zeros are ramification defects of the global source map.  The
new law is a constraint: one conductor transgression must be simultaneously the vertical
invariant class and the horizontal coefficient-faithful theta class.  The required mathematical
language is not a spectral flow but a bivariant regulator/interchange theory joining coherent
conductor torsion, Cartier ramification, integral nearby cycles, and prime--Gamma phase monodromy.

### Frozen conjecture

`[CONJECTURE -- XI_CONDUCTOR_RAMIFICATION_REGULATOR_INTERCHANGE]`

Construct on the pulled-back Legendre family, before choosing any Xi zero, a functorial regulator
from the conductor-supported Cartier/conormal Bockstein to integral (or canonically oriented
real) nearby cycles such that:

1. its valuation-graded specialization at every Xi divisor point is the existing nonzero terminal
   multiplicity jet;
2. its image is saturated and equals vertical monodromy invariants;
3. it commutes with the horizontal prime--Gamma/theta rotation on the same retained class;
4. source cyclic/Real orientation fixes that class before divisor specialization; and
5. the regulator is compatible with prime enlargement and Gamma completion.

Clauses 1--2 are conductor/nearby-cycle conservativity.  Clauses 3--4 are the genuinely RH-bearing
interchange: by the already-proved cyclic--paracyclic retained-class rigidity, the horizontal
monodromy scalar must be one, hence the divisor point is critical.  Clause 5 prevents a fitted
finite-prime or zero-indexed gauge.

## No-go closure

- `[PROVED NO-GO]` Reduced nodal geometry alone is identical at all Xi divisor points; it cannot
  detect `Re rho` or multiplicity.
- `[PROVED NO-GO]` The coherent conductor class vanishes in the torsion-free differential quotient;
  existence of Lemma 10.3's class does not imply nonzero nearby-cycle specialization.
- `[PROVED NO-GO]` Vertical exactness alone conserves an arbitrary horizontal defect.
- `[PROVED NO-GO]` Ordinary scalar derived Cartier specialization is contractible off the neutral
  locus, and its non-erasure is already RH-equivalent.
- `[PROVED NO-GO]` Equal integral ranks without saturation do not identify specialization image
  with invariants (`2 Z` inside `Z` is the minimal countermodel).
- `[PROVED NO-GO]` Reduced-fibre `K_0` data cannot retain terminal multiplicity.
- `[PROVED NO-GO]` Quasi-unipotence is a consumer unless geometric origin of the actual theta/Adams
  action on this same class is constructed.
- **Strongest positive survivor:** Xi multiplicity is naturally ramification of a global source
  map and belongs in the Cartier conormal/derived conductor channel, while critical-line placement
  is a two-axis phase-interchange constraint on the resulting nonzero defect class.
- **Exact open core:** construct the conductor--ramification regulator and prove horizontal
  prime--Gamma equivariance from source data.  Assuming either nonzero topological survival or
  horizontal invariance at each Xi zero would be circular.

## Dependency-closed formalization targets

1. Conductor pullback gluing: a normalized section whose conductor restriction is zero has a
   unique glued section with zero conductor component, and nonzero normalization implies nonzero
   glued class.
2. Integral invariant-cycle saturation: specialization lands in monodromy invariants; saturated
   image plus rational cofinality inside invariants implies equality.
3. Saturation firewall: the explicit doubling specialization into identity monodromy has full
   rational rank but proper image `2 Z`, proving why rank bookkeeping alone is invalid.
4. Xi nodal local model: the pre-divisor equation `x*y=XiC(s)` has, at every support point, exactly
   the union of the two coordinate axes and is support-independent.  This formalizes the raw
   degeneration and its blindness without pretending to formalize proper analytic geometry.

Targets 1--4 are dependency-closed.  The frozen regulator-interchange conjecture remains Stage 1
and must not be represented in Lean as a proved existence theorem.

## 2026-08-24 formalization result: node specialization closes, RH constraint does not

The ordinary node has a more suitable conductor class than Lemma 10.3's torsion differential.
For the normalization of an irreducible nodal cubic, the conductor preimage has two branches and

```text
C_D = coker(Z -> Z^{ {p_+,p_-} }) = Z.
```

After choosing branch orientation, its generator is the normalization Mayer--Vietoris connecting
class.  In an oriented nearby-cycle basis, Picard--Lefschetz monodromy and conductor specialization
are

```text
T(a,b) = (a+b,b),       sp_D(c) = (c,0).
```

The formalization proves over every commutative coefficient ring `A` that `sp_D` is injective and

```text
range(sp_D) = ker(T-1).
```

It then places the already-proved nonzero complex terminal multiplicity jet on the conductor
coefficient line.  Its specialization is exactly `(j_rho(x),0)`, is nonzero, and is fixed by
Picard--Lefschetz monodromy.  This is the exact cellular coefficient calculation requested by the
paper mechanism; no rank-only inference is used.

This closes an important local question and simultaneously proves a stronger no-go:

- `[PROVED NO-GO]` Nonzero conductor specialization with image equal to monodromy invariants holds
  for every coefficient and hence for every Xi divisor point.  It cannot distinguish on-line from
  off-line support.
- `[PROVED NO-GO]` The invariant line is canonical, but a generator is only canonical up to branch
  orientation.  Pointwise multiplication by the terminal jet does not construct a source-natural
  orientation or horizontal equivariance.
- `[CORPUS COLLISION]` The existing `XiNodalDefectSuperselection` condition makes the mixed
  grade--phase product vanish and is already equivalent to RH.  It cannot be imported as the
  missing source law.
- `[POSITIVE SURVIVOR]` The vertical map is no longer mysterious: it is the normalization
  connecting line mapped to the vanishing-cycle line.  Missing object is a comparison of local
  systems/actions, not another pointwise class or another invariant-cycle theorem.

The exact unresolved arrow is therefore a pre-divisor, source-natural comparison

```text
Reg_Xi : (terminal Cartier valuation line) tensor C_D,C
           -> (oriented vanishing-cycle local system of E_Xi),
```

not merely a fibrewise linear map.  It must intertwine the horizontal prime--Gamma/theta deck
character with geometric transport of the oriented vanishing-cycle line.  Vertical
Picard--Lefschetz monodromy fixes that line for every `rho`; only this independent two-action
interchange can force the horizontal character to be isometric/trivial and hence constrain
`Re(rho)`.  Constructing that source-level equivariant comparison, including branch orientation
and compatibility under prime enlargement, is the remaining RH-bearing core.

### Lean status

- `HTGeometry/ConductorNearbyCycleSpecialization.lean`: conductor gluing, integral saturation
  criterion and countermodel, universal-node Picard--Lefschetz lattice, injectivity, and exact
  specialization-image theorem.
- `RHTower/XiThetaNodalConductorDegeneration.lean`: source-first Xi node and Legendre equations,
  identical reduced nodal fibres, terminal-jet conductor coefficient, nonzero nearby invariant
  class, and instantiated image-equals-invariants theorem.
- All new declarations elaborate without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Remaining regulator-interchange statement stays a conjecture; no Lean declaration assumes it.
