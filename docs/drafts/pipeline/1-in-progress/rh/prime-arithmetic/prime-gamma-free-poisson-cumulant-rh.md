# Prime--Gamma free-Poisson cumulant assembly and RH

- **ID:** `prime-gamma-free-poisson-cumulant-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [FREE-PROBABILITY ASSEMBLY]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/EulerSquarefreeWickDefect.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeArchMomentMeasureRH.lean`
- **Statement:** `[CONJECTURE]` The canonical completed seam-log tower is the free-cumulant tower of
  one source-defined positive compound free-Poisson variable.  Positivity of its jump operator makes
  every shifted seam Hankel form a Gram form, and the existing seam-log consumer then proves RH.

## Why free cumulants are a plausible detour

The Euler product is multiplicative while its logarithm is additive over prime powers.  Free
cumulants linearize free additive convolution.  This does not prove that the two logarithms agree,
but it suggests a source assembly in which local prime packets are combined additively at the
cumulant level while mixed squarefree support is retained by noncrossing partitions rather than
discarded by a Gaussian/Wick closure.

The corpus now proves a concrete positive clue.  The raw four-prime squarefree Euler packet is not a
Gaussian matching packet: its Wick defect is

```text
-2 a_0 a_1 a_2 a_3.
```

But Lean also proves that every even squarefree moment of that packet is exactly the moment of one
shared Rademacher spin `X_i=a_i epsilon`.  The defect is therefore its genuine fourth joint cumulant.
The failed dimer shortcut has positively selected a higher-cumulant spin object.

## Exact free-Poisson consumer

Let `T_n^src`, `n>=1`, be the canonical shifted seam-log tower.  Suppose a positive compound
free-Poisson variable `Y` has jump measure `mu` on `R_+` and free cumulants

```text
kappa_n(Y)=integral x^n dmu(x)=T_n^src.                  (1)
```

Then for every real polynomial `p(x)=sum_i c_i x^i`,

```text
sum_(i,j) c_i c_j T_(i+j+1)^src
  =integral x p(x)^2 dmu(x)>=0.                         (2)
```

The paper theorem `seam-log-hankel-rh-equivalence.md` identifies all-order positivity in `(2)` with
RH.  Thus `(1)` for one positive source-built jump law closes the consumer end exactly.
The common infinite-support moment-measure-to-RH capstone is also formalized in Lean; the remaining
formal bridge is the coefficient identification between this jump law and
`normalizedPrimeArchMoment`.

This is formally the same positive cone as the Stieltjes/Thorin route but proposes a different
source mechanism.  Instead of first recovering a one-variable transform, it asks whether prime-word
connected interactions can be assembled as free cumulants of a positive operator.

## The large two-ended chain

```text
finite prime-word support strata and all boundary jets          [PROVED LEAN]
  + exact shared-Rademacher four-interaction                     [PROVED LEAN]
  + theta-cusp all-order cumulant recurrence                     [PROVED LEAN]
  -> noncrossing connected prime-word cumulants C_(N,n)
       [OPEN CORE A: finite combinatorial assembly]
  -> positive completed jump operator J_N>=0
       [OPEN CORE B: Gamma/polar sign repair]
  -> compound free-Poisson variable Y_N with
       kappa_n(Y_N)=Tr(J_N^n)=T_(N,n)^src
       [OPEN CORE C: exact finite comparison]
  -> compatible positive spectral laws mu_N -> mu
       [OPEN CORE D: tight cofinal limit]
  -> kappa_n(Y)=T_n^src for every n
  -> shifted Hankel Gram identity (2)
  -> RH.                                                         [PROVED PAPER CONSUMER]
```

The construction is static: the finite matrix or positive element `J_N` is a certificate built
from source incidence.  No free-convolution time evolution is needed.

## Candidate finite construction

At aperture `N`, retain every prime-word support label exposed by
`PrimeWordEnsembleBoundaryTomography.lean`.  Introduce one shared sign for each connected support
block.  Define block cumulants by Möbius inversion on the lattice of noncrossing partitions, but do
not evaluate them as target seam coefficients.  Instead:

1. local prime powers provide diagonal block entries;
2. squarefree shared-spin interactions provide off-diagonal hyperedges;
3. theta integer atoms provide positive archimedean termination blocks;
4. the polar counterterm is coupled by a Schur complement before scalar compression;
5. the resulting completed block matrix `J_N` must be proved positive from its entries;
6. only afterward compare `Tr(J_N^n)` with the completed finite seam cumulant.

The trace normalization may be projective: one positive scalar shared by the whole finite moment
block is harmless only if it is removed by the existing scale-free Hankel criterion.  Independent
degree-by-degree rescaling is forbidden.

## Hard attacks and positive residues

1. **The raw shared spin is not already the positive jump variable.**  For positive real `a_i`, its
   fourth Gaussian cumulant is `-2a_0a_1a_2a_3`.  Lean now proves the sharper noncrossing statement:
   its ordered fourth free cumulant is exactly `-a_0a_1a_2a_3`; the missing factor is the excluded
   crossing pair partition.
   **Positive residue:** the shared Rademacher law is the correct interaction carrier, not the final
   scalar jump law.  Positivity must appear only after Gamma/polar completion and block compression.
2. **Prime-by-prime scalar free convolution cannot work.**  A single positive FE-even frequency has
   alternating seam moments and fails the first shifted Hankel gate.  Free additivity does not
   change those scalar signs.
   **Positive residue:** use operator-valued or amalgamated cumulants retaining cross-prime support;
   scalarize only after the completed interaction is assembled.
3. **Arbitrary free-cumulant realization is circular.**  Declaring the canonical `T_n^src` to be free
   cumulants and invoking a realization theorem assumes the positivity wall.
   **Positive residue:** define `J_N` entrywise from prime powers, theta atoms, shared signs, and the
   polar block, then prove the moment comparison.
4. **Noncrossing partitions can be only a recoding.**  The moment/free-cumulant transform is
   triangular and all-order function-complete.
   **Positive residue:** the transform contributes only if the source incidence proves `J_N>=0`
   before its traces are identified with the seam tower.
5. **Finite-free convolution is a different, partly retired handle.**  The corpus's finite-free
   cocycle reducibility threshold is RH-blind and its live remnant is single-orbit hyperbolicity.
   **Positive residue:** this card uses no coboundary or finite-free flow; it seeks one positive jump
   operator whose full cumulant tower directly supplies the shifted square tests.
6. **Finite moment matching is insufficient.**  For each `N`, a separately chosen positive matrix can
   fit a finite prefix while later moments fail.
   **Positive residue:** require one source rule, compression compatibility, tight spectral laws, and
   convergence of every fixed trace moment along the same cofinal schedule.
7. **Operator-valued positivity may disappear under cumulants.**  A positive conditional expectation
   preserves positive elements, but operator-valued cumulants themselves need not be positive.
   **Positive residue:** certify the scalar moments as traces of powers of an actually positive
   `J_N`; use cumulants only for the source comparison, never as the positivity theorem.

## Low-aperture tests

The rank-four packet is the first compulsory test.

1. Reconstruct its six two-support and one four-support coefficients from the shared-spin law.
2. The noncrossing moment--cumulant inversion is now exact in Lean and gives the negative scalar
   fourth free cumulant `-a_0a_1a_2a_3`.  Therefore the uncompleted scalar jump ansatz is retired.
3. Add the finite Gamma/polar block in the same normalization as the seam recurrence.
4. Solve for the smallest Hermitian `J_4` whose first four traces match the completed packet.
5. Test positivity by exact principal minors.  If it fails, record the negative eigendirection as a
   named completion defect and enlarge the block once; do not alter moments independently.

Failure of the scalar or rank-one ansatz is expected and is not a route death.  Failure of every
source-prescribed positive block at a fixed finite packet, after the permitted completion channels
are exhausted, retires the free-Poisson construction and leaves the exact minimal negative
cumulant as a reusable no-go theorem.

## Exact open cores

- `[OPEN CORE A]` Define the finite noncrossing prime-word cumulants directly from support strata and
  prove their compatibility under aperture enlargement.
- `[OPEN CORE B]` Construct a positive completed jump block `J_N` without using seam moments, Xi
  zeros, or a target spectral measure.
- `[OPEN CORE C]` Prove the all-degree finite comparison between `Tr(J_N^n)` and the completed seam
  cumulant packet in one shared normalization.
- `[OPEN CORE D]` Prove tightness and moment convergence of the spectral laws, including determinacy
  sufficient to pass `(2)` to the limit.

## Kill conditions

Retire the route if the jump operator is reconstructed from `T_n^src`; if only scalar prime-by-prime
free convolution is used; if the Gamma/polar completion is added after positivity rather than inside
the block; if the finite matrices are incompatible; if cumulant positivity is asserted without an
actual positive jump operator; or if the construction matches a finite prefix only.

## Parent boundary

The free compound-Poisson cumulant formula, noncrossing moment--cumulant inversion, and the fact that
free cumulants linearize free convolution are parent theory.  The finite-free cocycle already in the
pipeline is a different construction.  The proposed new assembly is the completed source-first
positive jump operator; it is valuable only if that operator is built without the seam positivity
it is meant to prove.

## Gates

- [x] free-Poisson-to-shifted-Hankel-to-RH consumer chain closed
- [x] raw Wick no-go upgraded in Lean to a positive shared-Rademacher cumulant identity
- [x] scalar primewise, triangular-recoding, and finite-prefix shortcuts attacked
- [x] infinite-support representing-measure-to-RH capstone formalized in Lean
- [x] raw rank-four scalar free-Poisson jump ansatz retired by the exact negative fourth free
      cumulant; completion-sensitive block successor isolated
- [ ] rank-four noncrossing completed block constructed and tested exactly
- [ ] all-aperture source rule for `J_N` defined
- [ ] positivity and trace comparison proved
- [ ] cofinal positive jump law constructed
- [ ] free-cumulant coefficient dictionary composed with the formal RH capstone
