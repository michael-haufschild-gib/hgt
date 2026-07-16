# Finite differential circuits conserve hypertranscendental source complexity

- **ID:** finite-differential-circuit-hypertranscendental-source-extraction
- **Stage:** 3-formalized
- **Type:** `[PROVED ELSEWHERE]` / `[BRIDGE]` / corpus-strengthening formalization
- **Parent theory:** differential fields and closure of differential-algebraic elements
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/FiniteDifferentialCircuitBoundary.lean`
- **Arithmetic consumer:** `formal/GaloisForLFunctions/RHTower/PrimeSourceFiniteDifferentialCircuit.lean`

## Statement

Let `F ⊆ E` be differential fields of characteristic zero. For a predicate `Atom : E → Prop`,
let `FiniteDifferentialCircuit Atom x` mean that `x` is represented by a finite expression tree
whose leaves satisfy `Atom` and whose internal operations are addition, multiplication, additive
inverse, multiplicative inverse, and the ambient derivation.

The closure theorem is

```text
FiniteDifferentialCircuit Atom x
and (for every a, Atom a -> DifferentialAlgebraicOver F a)
  -> DifferentialAlgebraicOver F x.                                      (1)
```

Its positive source form is

```text
HypertranscendentalOver F x
and FiniteDifferentialCircuit Atom x
  -> exists a, Atom a and HypertranscendentalOver F a.                    (2)
```

The scalar-aware strengthening admits every embedded base-field coefficient as a free leaf:

```text
HypertranscendentalOver F x
and FiniteDifferentialCircuit (Atom or base scalar) x
  -> exists a, Atom a and HypertranscendentalOver F a.                   (2s)
```

Thus learned weights, regression coefficients, and affine offsets are discharged automatically
and can never be returned as the alleged HT source.

For every signed-prime orientation `epsilon`, the arithmetic specialization is

```text
FiniteDifferentialCircuit Atom (signedPrimeSource epsilon)
  -> exists a, Atom a and HypertranscendentalOver C a.                    (3)
```

The canonical all-positive source is an immediate specialization.

Thus a finite differential circuit can transport an HT source but cannot manufacture one from
DA primitives.

## Proof

The new base-monotonicity lemma proves that differential algebraicity over `F` remains true after
enlarging the coefficient field. For a DA element `x`, its singleton differential adjunction
`F⟨x⟩_D` is derivation closed and has finite transcendence degree over `F`; therefore every member
of that field is DA over `F` by finite-transcendence descent.

For two DA elements `x` and `y`, first adjoin `x`, enlarge the coefficient field for `y`, and then
adjoin `y`. Differential-algebraic transitivity descends every element of the resulting field back
to `F`. This proves closure under addition and multiplication. Singleton adjunction proves closure
under inverse, negation, and derivation. Structural induction on the finite expression tree gives
`(1)`.

For `(2)`, if no atom were HT then classical double-negation would make every atom DA, and `(1)`
would contradict the HT output. For `(3)`, restrict the existing differential independence of each
complete signed-prime shift palette to its unshifted source, then apply `(2)`.

For `(2s)`, apply `(2)` to the enlarged leaf predicate. A leaf returned from the scalar branch is
an embedded coefficient and is DA over the base field, contradicting its asserted HT status.
Therefore the returned leaf belongs to the genuine model-atom branch.

## Exact scope

The circuit is a finite syntactic observation architecture. It may share no state, linearity,
normality, or time-evolution law. The theorem covers rational formulae, derivative features, finite
symbolic-regression trees, equation-learning networks whose admitted primitives are DA, and
finite mechanistic input/output formulae in genetics or systems biology.

The theorem does not cover:

- an atom that is already hypertranscendental;
- an infinite-depth or unbounded-width limiting architecture;
- a primitive such as arbitrary functional composition unless that primitive is separately
  proved to preserve differential algebraicity;
- approximation of an HT target by DA circuits.

This is intentionally an exact-representation theorem. Approximation power is irrelevant to its
conclusion.

## Clock-observability interpretation

No temporal flow occurs in the definition or proof. The derivative operator labels which
observations of each atom the architecture can expose. Equation `(2)` says that finite algebraic
recombination of those observations cannot create the infinite differential observation structure
of an HT clock. The HT complexity must already be visible at a leaf. This directly realizes the
motif that hypertranscendence concerns the observability structure of a clock, not its temporal
evolution.

## Genomics, genetics, ML, and AI transfer

Differential-algebra elimination in rational biological ODE models produces exact input/output
differential formulae. Finite gene-regulatory or biochemical formulae assembled from DA measured
signals remain DA by `(1)`. If an exact genomic clock output is HT, `(2)` gives the positive
conclusion that some measured or latent primitive in the formula is itself HT; the architecture
does not create that complexity.

Classical methylation clocks are finite affine combinations of CpG measurements, and learned
symbolic or multilayer clocks contain fixed weights and offsets. Equation `(2s)` removes those
coefficients from the source hypothesis: an HT clock value forces an HT biological/model feature,
not an HT learned weight.

Equation-learning and symbolic-regression systems search finite compositional formulae. When their
primitive vocabulary is DA and their algebraic core is generated by the operations formalized
here, they are certified incapable of exactly producing an HT target. Conversely, an exact learned
HT formula is a source detector: at least one admitted primitive must carry HT complexity. This is
stronger than saying one chosen network architecture fails.

## Physics transfer

Finite formulae assembled from DA scalar-field observables, rational Hamiltonian reductions,
finite effective-field observables, or exact algebraic response functions fall under `(1)`.
Consequently a physical construction claimed to generate an HT clock must exhibit either an HT
primitive or a genuinely infinite operation. Generic finite QFT, cosmology, holography, or quantum
clock vocabulary does not evade the boundary merely by being reinterpreted as a new dynamics.

## Literature gate

- J. F. Ritt, *Differential Algebra*, AMS Colloquium Publications 33 (1950), for the parent
  differential-field closure theory.
- G. Martius and C. H. Lampert, *Extrapolation and learning equations*, arXiv:1610.02995. The EQL
  architecture learns finite analytical expressions in an end-to-end differentiable network.
- S.-M. Udrescu and M. Tegmark, *AI Feynman: a Physics-Inspired Method for Symbolic Regression*,
  arXiv:1905.11481. Its recursive formula search explicitly uses compositional operations such as
  sums, products, differences, and ratios.
- H. A. Harrington, K. L. Ho, and N. Meshkat, *Differential Algebra for Model Comparison*,
  arXiv:1603.09730. Biological hidden-state ODE models are eliminated to differential invariants
  in measurable variables.
- A. Ovchinnikov, G. Pogudin, and P. Thompson, *Parameter identifiability and input-output
  equations*, arXiv:2007.14787. Rational state/output systems and the generated differential
  input-output fields are the precise systems-biology model class relevant here.

The mathematical closure principle is established parent theory. No novelty claim is made. The
value is the reusable Lean closure API, the finite-circuit induction theorem, and the unconditional
specialization to every signed-prime orientation.

The API is already consumed by `HTGeometry/SourceLogarithmicBoundary.lean`: its former manual
singleton-adjoin proof that `x'/x` is DA has been replaced by the derived closure chain
`DA(x) -> DA(x')`, `DA(x) -> DA(x⁻¹)`, and multiplication. This is a direct hypothesis-discharge
and proof simplification in the existing corpus, not merely a prospective application.

## RH impact

This does not prove RH and does not orient the remaining prime--Gamma Fisher/curvature incidence
seam. It does strengthen the proof search in a directly usable way:

1. generic finite physical, genomic, symbolic-AI, or learned circuits are now formally excluded as
   independent producers of every oriented signed-prime HT source;
2. any such exact construction must identify an HT atom, so renaming a hidden arithmetic oracle as
   a quantum clock, field, latent state, or learned primitive cannot discharge a source hypothesis;
3. a viable external bridge must contribute either a source-specific HT primitive with new
   arithmetic orientation or an intrinsically infinite construction whose convergence preserves
   that orientation.

The positive research route is therefore sharper: search physics and AI for exact infinite-limit
or source-incidence identities, not finite compositional redressings. If a proposed construction is
finite, theorem `(2)` turns it into an audit that locates where the unproved HT source was inserted.

## Verification

Both new modules passed targeted module builds when their artifacts were absent and direct
`lake env lean` checks. The late scalar-aware strengthening passes the direct source-file check
without forcing a redundant rebuild of the existing artifact. The formal lint gate passes. The
capstone theorems use only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`,
`admit`, new axiom, `opaque`, or `unsafe` declaration.
