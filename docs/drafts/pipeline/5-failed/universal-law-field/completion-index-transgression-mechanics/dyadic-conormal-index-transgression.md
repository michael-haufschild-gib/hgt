# Dyadic conormal index transgression

- **ID:** `ULF-DCIT-1`
- **Stage:** 5-failed
- **Type:** higher-mechanism construction programme
- **Status:** retired. It conflated analytic torsion/character value with an ordinary Euler index.
  Positive survivor is `ULF-DRRLC-1`: the same scalar is legitimately an integer when realized as
  determinant of a relative-reflection differential in a finite integral lattice frame.

> Failure learned: proper pushforward produces an integer index, while Laurent evaluation is a
> varying analytic torsion. Equating them without an integral endomorphism is an unmotivated type
> jump. Replace “character-to-index” by “relative monodromy acquires integral coordinates.”

## 1. Big-picture higher law

Corpus does not need another reader of horizontal grade. It already has an unconditional integral
Laurent producer

`R = Z[T,T^-1]`, `kappa=(T-1)(T^-1-1)`,

whose physical character at one prime sends `T` to `p^a` and therefore sends `kappa` to

`Q_p(a)=(p^a-1)(p^-a-1)=-2(cosh(a log p)-1)`.

Missing operation is **character-to-index transgression**: completion must turn this equivariant
Laurent character into an ordinary integer Euler index on every canonical one-dimensional
conormal layer of the Xi divisor. Horizontal holonomy then becomes vertical intersection count.
This is not positivity, ghost erasure, or a new scalar reporter.

At `p=2`, open-strip geometry gives `-1<Q_2(a)<=0`. Hence a genuine integer index with analytic
value `Q_2(a)` is forced to be zero and therefore `a=0`. Prime two is selected by aperture, not by
fitting: its entire critical-strip image lies strictly between adjacent integers.

## 2. Corpus audit before conjecture

Searches:

- `dyadic quadratic ghost integral subunit index`
- `hermitian square quadratic ghost properness integer index multiplicity`
- `integral supertrace Adams Frobenius ghosts`
- `source endomorphism analytic realization`
- `proper Laurent completion`

Facts found:

1. `FrankensteinXiFullIntegralGammaEvaluationProducer` already constructs `R`, strict inversion,
   the one-copy quadratic ghost, full evaluation, and exact forward+inverse+ghost conservation.
2. `SourceHorizontalGammaSixPositiveStarUntwisting` proves `kappa` is the literal integral
   Hermitian square and its evaluation is `-2(cosh a-1)`. Nonnegativity or erasure is exactly the
   RH receiver and cannot be assumed.
3. `FrankensteinXiGreenStokesQuadraticGhostNormalForm` proves the same coefficient is nonpositive,
   nonzero off line, killed by the adjoint boundary, and admitted to the derivative range for all
   zeros iff RH. Boundary killing is therefore not index production.
4. `HedenmalmThetaSourceShellReplicaWardDoubleProperness` replicates the ghost coefficient
   faithfully, but closability/properness is itself equivalent to line placement. Its operator
   cannot supply unconditional properness.
5. `WittFormationMechanics` and `DeningerBigWittFrobeniusPrimeSeamTransgression` already provide
   integral ghosts, Adams transport, finite reconstruction, and Frobenius ghost shifting. A new
   Witt class with prescribed physical ghost would only reinsert the selector.
6. `GradedTraceDeterminantRigidity` shows finite signed traces determine a determinant but do not
   move its divisor. `PrimeDeterminantTwoSuperghostRigidity` shows two odd integral ghosts would
   suffice, but source/Gamma trace naturality is missing.
7. `XiArakelovKroneckerChamber` and localization no-gos show algebraic-unit or `S`-unit language
   alone does not force neutrality. Evaluation of an integral Laurent polynomial is not generally
   an integer.
8. Xi multiplicity is retained in the full producer. Total multiplicity is fatal here:
   `m Q_2(a)` can be integral for nonzero strip grades when `m>=3`. The construction must descend
   to canonical local-length quotients, not divide a total index by multiplicity.

No searched declaration proves dyadic subunit integrality rigidity or produces the required
ordinary index.

## 3. Proposed mechanism

Let `D` be the Xi divisor with local ideal `m_rho` and length `m(rho)`. The one-variable local
divisor algebra has canonical layers

`gr_j(rho)=m_rho^j/m_rho^(j+1)`, `0<=j<m(rho)`,

each of residue-field dimension one. This removes multiplicity without choosing a zero-dependent
projector: the filtration is intrinsic to the divisor scheme.

Construct one global compactified formation correspondence over `D` with:

1. the involution `T <-> T^-1` induced by the functional equation;
2. a perfect integral complex on every `gr_j`;
3. a proper pushforward to a point, giving an ordinary integer Euler index `Ind_2(rho,j)`;
4. an analytic fixed-point formula

   `Ind_2(rho,j)=Q_2(2 Re(rho)-1)`.

The decisive operation is item 4: completion converts an equivariant character value into an
ordinary local intersection index. Ordinary equivariant `K`-theory does not do this; it merely
retains `kappa in Z[T,T^-1]`. A continuous Fredholm family cannot do it either, because its integer
index is locally constant while `Q_2(a)` varies. The correspondence must be relative to the
spectral divisor and proper there, with the analytic identity obtained from a global source trace
formula rather than imposed fibrewise.

Functional equation fixes `kappa` but reverses the two linear factors. Thus mixed inertia is the
orientation of the local intersection, positivity is the phase-forgetting quotient, recurrence is
the finite shadow of the completed correspondence, and nonclosability/hypertranscendence are
failures of naive nonproper pushforward. These are consequences if the transgression exists, not
inputs to its construction.

## 4. Exact RH closure

For every Xi divisor copy `rho`, standard zero-free regions give

`|a(rho)|=|2 Re(rho)-1|<1`.

Proper integral pushforward makes each `Ind_2(rho,j)` an integer. The analytic index identity makes
it `Q_2(a(rho))`. `ULF-DQIR-1` proves an integral value in the open strip occurs iff `a(rho)=0`.
Hence every Xi zero has real part `1/2`, proving RH.

This closes RH from one prime, one quadratic ghost, and one canonical conormal layer. No positivity,
all-scale integrality, common lattice across primes, ghost erasure, or vanishing of the completion
defect is required.

## 5. What must be built

1. Global, pre-fibre compactification of the existing integral Laurent formation correspondence.
2. Relative local-length filtration whose fibres are the intrinsic `gr_j`, with no chosen root
   projector.
3. Perfect integral fixed-point complex after dyadic completion.
4. Source-derived Lefschetz/index theorem identifying its ordinary Euler index with the already
   proved Laurent evaluation of `kappa`.

Construction order matters: properness and integrality must exist before evaluating at an Xi
divisor. Defining a complex from `a(rho)`, declaring its trace to be `Q_2(a)`, or assuming shell
closability is circular.

## 6. Immediate falsifiers

1. Pushforward remains only equivariant, valued in `Z[T,T^-1]`, with no ordinary index.
2. Analytic comparison yields total multiplicity `m(rho)Q_2(a)` and cannot split the canonical
   local-length filtration.
3. Required properness is equivalent to the existing shell-replica closability/RH condition.
4. Index identity is proved only after choosing `rho` or inserting `a(rho)` into the source map.
5. Completed correspondence forms a continuous Fredholm family across the strip; then the proposed
   varying analytic index is impossible.

## 7. Current boundary

`ULF-DQIR-1` proves and Lean-certifies the scalar aperture law and pointwise Xi equivalence. It does
not discharge items 1--4 above. Next work is geometric: find the global formation correspondence
whose fixed-point pushforward de-equivariantizes `kappa` one conormal layer at a time.
