# Hypertranscendental source constraints have unbounded augmentation height

- **ID:** `unbounded-hypertranscendental-source-constraint-height`
- **Stage:** 3-formalized
- **Type:** GENERAL HT HEIGHT THEOREM / FINITE-TRUNCATION NO-GO / HIGHER-COHERENCE LAW
- **Scientific status:** `[PAPER THEOREM CONDITIONAL ON THE AUDITED ANALYTIC PARENT]`
  `[ALGEBRAIC CORE LEAN-FORMALIZED]` `[NOVELTY PROVISIONAL]` `[NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SourceConstraintHeight.lean`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/all-order-multiple-elliptic-gamma-structural-differential-matroid.md`
  - `normal-crossing-derived-critical-excess-phase-law.md`
  - `../1-in-progress/hypertranscendental-source-descent-duality.md`

## The invariant

Let `A` be an augmented source-operator algebra, let `m` be its augmentation ideal, and let `q`
be the class of a constrained analytic observable modulo differentially algebraic gauges.  Put

```text
J_q=Ann_A(q).
```

When `J_q` is nonzero, define its **source-constraint height** by its augmentation-adic onset

```text
ht_src(q)=max{h:J_q subset m^h}
         =min{total augmentation degree of 0 != P in J_q}.       (1)
```

This is not the number of chosen equations and not the length of a free resolution.  It records
the least source-composition depth at which any genuine relation appears.  An augmented source
algebra automorphism preserves every `m^h`, so `(1)` is basis-independent.  Morita invariance for
general source groupoids remains part of the successor conjecture.

## Exact height in a natural HT hierarchy `[PROVED FROM THE ANALYTIC PARENT]`

For the generic order-`r` multiple elliptic gamma logarithmic derivative, let

```text
A_r=C[delta,t_0^(+-1),...,t_r^(+-1)],
x_i=t_i-1,
q_r=[Psi_r] modulo DA.
```

The all-order structural-matroid theorem proves the exact annihilator

```text
J_(q_r)=I_r=(product_(i in S)x_i:|S|=r).                  (2)
```

Squarefree-Veronese membership says that a polynomial belongs to `I_r` exactly when every
monomial in it uses at least `r` distinct augmentation variables.  Consequently

```text
ht_src(q_r)=r.                                            (3)
```

The hierarchy therefore realizes every positive finite source height.  Differential
transcendence degree does not see this stratification: every `q_r` is hypertranscendental, while
the least source degree of its first DA relation tends to infinity.

## Fixed-depth theories are nonconservative `[PROVED + LEAN]`

For every cutoff `H`, choose `r=H+1`.  Then

```text
0 != P and totalDegree_m(P)<=H  =>  P notin I_r,           (4)
there exists P with totalDegree_m(P)=H+1 and P in I_r.     (5)
```

Thus the entire source-operator truncation through degree `H` is relation-free even though the
full object is constrained one degree later.  No theory restricted to a fixed source-composition
depth can be conservative on natural constrained HT functions.

This is a stronger conclusion than saying that one needs more equations.  Increasing a fixed
finite list does not solve the problem: for every proposed terminal depth, a natural HT source
first becomes visible beyond it.

> **Positive successor.** A universal HT theory must admit an unbounded augmentation filtration.
> Finite-dimensional realization functors may remain useful local charts, but no invariant that
> factors through one uniform finite source-operator jet can be universal.  Identifying this
> filtration with a source Postnikov tower is the stronger conjecture below.

The unconditional algebraic theorem `(4)`--`(5)` is Lean-formalized as
`boundedSourceDepth_misses_next_normalCrossingConstraint`.  The special-function interpretation
uses the paper-level exact-annihilator parent `(2)` and inherits its audit boundary.

## Immediate faces reconstruct every higher-height structural class `[PROVED + LEAN]`

The unbounded-height theorem has a nontrivial positive converse.  For every `r>=2` and every source
operator polynomial `P`,

```text
P in I_r  <=>  x_i P in I_r for every i.                  (6)
```

Equivalently, the joint immediate-face observation

```text
A_r/I_r -> product_i A_r/I_r,
[P]     |-> ([x_i P])_i                                  (7)
```

is injective.  Thus high source height is not hidden from all lower faces.  No one uniform finite
augmentation truncation is conservative across the hierarchy, but for each object its complete
family of immediate cofaces reconstructs the entire structural quotient.

The proof is exact monomial geometry.  If a nonzero monomial of `P` uses a variable already in its
support, multiplication by that variable does not increase support width; membership of `x_i P`
in `I_r` therefore forces the original monomial to have width at least `r`.  A constant monomial
is excluded by multiplying with any variable and using `r>=2`.

Lean formalizes `(6)` as `mem_veroneseIdeal_iff_all_X_mul_mem`.

The threshold is sharp.  At `r=1`, `I_1` contains every `x_i`, so all immediate-face
multiplications kill the nonzero constant class.  Height one therefore needs a pointed residue or
affine calibration; from height two onward the entire coface family is already jointly
conservative.  Lean certifies this failure as `heightOne_all_X_mul_not_conservative`.

> **Positive reconstruction law.** The universal HT object must be unbounded in height, but its
> normal-crossing structural strata satisfy one-step descent: global classes are separated by
> their complete immediate boundary family.

## Source height and derived-critical amplitude `[PROVED + LEAN]`

The normal-crossing source law in `r+1` variables has critical ideal `I_r`.  Its full critical
Koszul object has exact homological amplitude `r-1`.  Therefore this hierarchy satisfies

```text
ht_src(q_r)=derivedAmplitude(dCrit(f_r))+1.                (8)
```

Lean formalizes the exact conjunction as
`normalCrossing_constraintHeight_eq_derivedAmplitude_succ`.

Equation `(8)` is not asserted for arbitrary ideals.  Initial augmentation degree, grade, and
Koszul excess are independent in general commutative algebra.  Here the equality is a substantive
normal-crossing purity law joining the analytic source annihilator to its independently defined
derived-critical lift.

## Scalar flatness collapses when source rank rises `[PAPER PROOF; FINITE CORE IN LEAN]`

There is a second reason higher source degree is forced.  Let `F` be a `1`-periodic meromorphic
function on `C`, and let `omega_1,...,omega_s` be shifts such that each group

```text
Z + Z omega_i + Z omega_j
```

is nondiscrete for `i!=j`.  Suppose that for some `1<=k<s`, every `k`-fold mixed difference

```text
Delta_(omega_i1)...Delta_(omega_ik) F
```

is constant.  Then `F` is constant.

**Proof.**  Assume all `m`-fold mixed differences are constant, with `m<s`.  Fix an
`(m-1)`-fold difference `g`.  At least two unused shifts remain.  The derivative `g'` is periodic
under `1` and both unused shifts.  A meromorphic function with a nondiscrete period group is
constant.  Since `g` is `1`-periodic, this constant derivative is zero, so `g` is constant.
Descending from `m=k` to `m=0` proves the claim. `QED`

At the first nontrivial boundary level the finite endpoint algebra has a sharp transition:

```text
two directions:   the two mixed-orthant equations force equal boundary jumps;
three directions: adjacent mixed-orthant equations force every boundary jump to vanish.   (9)
```

Lean formalizes `(9)` as `rankTwo_mixedOrthant_reciprocity` and
`rankThree_mixedOrthant_boundaryCollapse`.

The general mixed-difference collapse is a `[BRIDGE]`, not a novelty claim.  Montel-type theorems
for mixed differences and the classical discreteness of the period group of a nonconstant
meromorphic function are direct parents.  Its positive HT consequence is architectural:

> a nonconstant high-rank HT source cannot be a scalar lower-degree cocycle whose every face is
> flat.  It must retain a nonconstant higher coherence defect, a higher cocycle/gerbe class, or
> genuinely non-scalar boundary data.

The rank-three elliptic-gamma gerbe and Morain's higher-rank cocycles exhibit exactly the kind of
positive successor predicted here; their existence is established parent theory.

## First positive reconstruction stratum `[PROVED ON PAPER]`

The height-one triptic class is already complete.  Its two labelled orbital-residue maps are
defined on two noncommensurable elliptic boundary curves, but the triptic reciprocity theorem
proves that they agree and induce an isomorphism

```text
Q/(Q intersect Mer_DA) ~= C[delta][C/(Z+Z tau+Z sigma)].
```

Hence the unbounded-height result is not only a sequence of no-gos.  At its first positive stratum
there is an actual source-native boundary object, two genuinely different analytic realization
functors, reciprocity between them, and complete reconstruction modulo DA.  The precise theorem
and its analytic audit boundary are in
`../2-fully-proven/new_scientific_knowledge/triptic-orbit-residue-reciprocity.md`.

This does not reconstruct the full analytic germ and does not settle height two.  It provides the
base case for the higher orbit-residue descent conjecture in
`../1-in-progress/hypertranscendental-constraint-hodge-duality.md`.

## Unbounded-height correspondence `[CONJECTURE — FIELDS-SCALE CORE]`

> **[CONJECTURE — HT SOURCE-HEIGHT CORRESPONDENCE]** For regular source-minimal constrained HT
> germs, the augmentation filtration on the exact admissible source annihilator is the lowest
> associated-graded shadow of the minimal positive-degree source-descent object.  The assignment
> is Morita invariant, its finite-height strata are characterized by intrinsic effectivity and
> polarization conditions, and its unbounded completion reconstructs the analytic source germ.
>
> Every admissible analytic obstruction realization preserves this filtration.  Continuation,
> monodromy, boundary, spectral, and positivity failures are conservative realization defects of
> the same unbounded object, not separately chosen invariants.

This strengthens the current constraint-Hodge proposal in one essential way: unbounded
augmentation height is no longer aesthetic or optional.  Equations `(3)`--`(5)` force it on a
natural HT hierarchy.  The further claim that augmentation height is categorical or Postnikov
height remains an explicit, falsifiable part of the correspondence rather than a proved synonym.

## Novelty gate

Established parent theory includes:

1. augmentation filtrations, associated graded algebras, and squarefree monomial ideals;
2. the colon identity behind immediate-face injectivity for positive-depth Stanley--Reisner rings;
3. grade sensitivity of Koszul homology and normal-crossing derived critical loci;
4. Montel-type theorems for mixed differences;
5. elliptic-gamma gerbes and modular cocycles;
6. higher multiple-elliptic-gamma families and their increasing cocycle degrees.

Primary checks:

- J. M. Almira, *A Montel-type theorem for mixed differences*,
  https://arxiv.org/abs/1612.03754;
- G. Felder, A. Henriques, C. A. Rossi, C. Zhu, *A gerbe for the elliptic gamma function*,
  https://arxiv.org/abs/math/0601337;
- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, https://arxiv.org/abs/math/0306164;
- P. Morain, *Geometric families of multiple elliptic Gamma functions and arithmetic
  applications, I*, https://arxiv.org/abs/2510.16515;
- P. Morain, *Geometric families of multiple elliptic Gamma functions and arithmetic
  applications, II*, https://arxiv.org/abs/2602.06561.

Morain explicitly constructs rank-dependent higher cocycles, so “higher rank has higher
cocycles” is not new.  Almira removes the general mixed-difference collapse from the novelty
claim.  The coface injectivity `(6)` is elementary Stanley--Reisner commutative algebra, not a new
general algebra theorem.  The candidate-new residue is instead its source-native HT consequence
and conjunction:

```text
exact all-order DA source annihilator
  => intrinsic unbounded augmentation onset
  => rigorous nonconservativity of every fixed source-depth truncation
  + joint immediate-face reconstruction
  + exact normal-crossing height/amplitude relation.       (10)
```

Targeted searches located no external theorem stating `(10)` for hypertranscendental functions or
using it as a lower bound on any universal HT classification theory.  This is provisional
negative evidence, not a priority certificate.

## Anti-theatre and significance gate

- **No-go survived:** a third ad hoc Hodge grading was rejected because minimal presentation
  length is not an independent intrinsic degree.
- **Positive theorem survived:** source-annihilator onset is intrinsic to the augmented operator
  algebra and is unbounded on a natural HT hierarchy.
- **Not vocabulary:** deleting `(4)`--`(7)` leaves only the slogan “retain unbounded structure.”
  The theorems supply explicit witnesses defeating every finite cutoff and an exact positive
  reconstruction map.
- **Not a universal equality claim:** `(8)` is restricted to the normal-crossing purity class.
- **Paper verdict:** the unbounded-height theorem is a significant foundational consequence of
  the all-order exact-annihilator theorem and warrants a paper section or short companion paper
  after independent audit of that analytic parent.
- **Medal-scale verdict:** the lower bound alone is not medal-scale.  The Source-Height
  Correspondence—Morita invariance, essential image, analytic reconstruction, and conservative
  realizations—is the medal-scale theorem.

## Lean certificate

`SourceConstraintHeight.lean` proves:

- `veroneseIdeal_hasExactSquarefreeConstraintHeight`;
- `totalDegree_lt_constraintHeight_not_mem_veroneseIdeal`;
- `boundedSourceDepth_misses_next_normalCrossingConstraint`;
- `normalCrossing_constraintHeight_eq_derivedAmplitude_succ`;
- `mem_veroneseIdeal_iff_all_X_mul_mem`;
- `heightOne_all_X_mul_not_conservative`;
- `rankTwo_mixedOrthant_reciprocity`;
- `rankThree_mixedOrthant_boundaryCollapse`.

No special-function axiom is introduced.  Lean certifies the unconditional squarefree,
finite-truncation, amplitude-comparison, and endpoint algebra.  The exact analytic annihilator of
the multiple elliptic gamma observable remains the explicitly named paper-level input.

## Gates

- [x] intrinsic source-height invariant isolated
- [x] exact height `r` proved for the squarefree coface ideal
- [x] every fixed total-degree truncation proved nonconservative on the hierarchy
- [x] exact source-height/derived-amplitude relation proved in the normal-crossing class
- [x] rank-two reciprocity/rank-three scalar collapse formalized
- [x] mixed-difference and higher-cocycle parent theories separated from novelty
- [ ] independent audit of the all-order multiple-elliptic-gamma annihilator theorem
- [ ] Morita invariance of source height for source groupoids
- [ ] identify the associated graded height with the minimal source-descent Postnikov layer
- [ ] prove reconstruction in one nonlinear analytic class
- [ ] prove two genuinely different obstruction realizations conservative
- [ ] independent specialist novelty and significance verdict
