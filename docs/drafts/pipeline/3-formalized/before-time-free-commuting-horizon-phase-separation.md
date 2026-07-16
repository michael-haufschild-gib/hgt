# Before There Was Time: a free/commuting phase boundary at the holographic horizon

## Status

`[LEAN-PROVEN]` for the complete algebraic-dependence horizon of one actual differential
observable in every cyclic commuting annihilator model, with no homogeneity, reducedness, or
finite-generation assumption, and for the explicit nonlinear separation from the free
noncommuting model.  Classification of genuinely nonlinear, interacting, gauge, or prolonged
commuting systems remains `[CONJECTURE]`.

## Statement

Let `A` be any commutative `K`-algebra, `V` a law vector space, and `L:V -> A` a linear law map.
Write

```text
A_alg = {a in A : a is algebraic over K}.
```

Over a field, algebraic elements are exactly integral elements, so `A_alg` is the integral closure
of `K` in `A` and is a `K`-subalgebra.  Lean proves the general principal theorem

```text
{v : the observable jet iota(1),iota(L(v)),iota(L(v)^2),... is algebraically dependent}
  = L^(-1)(A_alg).                                         (A)
```

The right side is a vector subspace of law space.  This uses no grading, presentation, or finiteness
assumption on `A`.

Apply `(A)` to `A=S/I`, where `S=K[X_i | i in ι]` is the commutative law algebra and `I` is an
arbitrary annihilator ideal.  Let `ell_c=sum_i c_i X_i` and let `bar(ell_c)` be its class in `S/I`.
The unconditional cyclic horizon is

```text
H_I = {c : bar(ell_c) is algebraic over K}.                (B)
```

It is a vector subspace even when `I` is nonhomogeneous or nonreduced.

If `I` is homogeneous, the algebraic element `bar(ell_c)` must in fact be nilpotent.  Homogeneous
components isolate different powers, and `(B)` reduces to

```text
H_I = ell^(-1)(rad(I)).                                   (C)
```

Thus the earlier radical theorem is the graded special case of the algebraic-direction principle.

The classification is realized by a genuine differential orbit.  Let `M=S/I`, let multiplication
by `X_i` act on `M`, and extend these commuting linear actions to commuting derivations `delta_i`
of the commutative domain `Sym_K(M)`.  For the single root observable `z=iota([1])`, Lean proves

```text
(sum_i c_i delta_i)^n z = iota([ell_c^n])
```

for every `n`.  The canonical degree-one family in a symmetric algebra is algebraically independent
exactly when its state vectors are linearly independent, while the powers of an element are linearly
independent exactly when that element is transcendental.  Therefore the entire actual iterated jet
of `z` is algebraically dependent exactly on `(B)`.

This restriction is sharp.  In two law directions the crossing cone

```text
c_0 c_1 = 0
```

contains both coordinate axes but not their generic sum, so it is not a vector subspace and cannot
equal `H_I` for any commutative cyclic annihilator ideal.  Nevertheless there is an explicitly
constructed rational differential field with free noncommuting word derivations and one observable
whose complete directional jet is algebraically dependent exactly on this crossing cone; off the
cone its entire jet tower is algebraically independent.

Thus noncommuting free law space and commuting cyclic law space are separated by a theorem, not a
metaphor:

```text
free noncommuting: arbitrary projective horizon topology exists;
cyclic commuting differential domain: every complete horizon is linear.
```

The separation is not limited to the crossing example.  For every finite homogeneous family whose
affine zero cone is not the carrier of a vector subspace, Lean proves simultaneously that the cone
is an exact complete horizon of one free noncommuting observable and is not the complete horizon of
any cyclic commuting annihilator model.  Thus nonlinear projective topology itself is a rigorous
witness that the cyclic commuting description has failed.

## What the external object must be

The external constraint cannot be any ideal acting on one cyclic linear state through
linear-induced commuting derivations if the horizon is nonlinear.  Nonhomogeneous mass or scale
terms do not escape the theorem.  At least one of the following must be present:

1. derivations whose action on observable generators is genuinely nonlinear;
2. interacting internal degrees of freedom not reducible to one cyclic law element;
3. gauge identifications and syzygies coupling several observables;
4. a formally integrable prolonged complex rather than one annihilator module.

These are necessary directions for enlargement, not yet an exhaustive classification theorem.

## Physical interpretation `[CONJECTURE]`

The linear commuting cyclic phase is the algebraic analogue of a free abelian field sector: even
complete algebraic-dependence directions superpose.  A nonlinear horizon therefore cannot be
explained by any more complicated annihilator of one cyclic state, including a nonhomogeneous one;
it signals nonlinear action, interacting sectors, gauge structure, or prolongation.  A QFT realization
should encode that additional object as a local constraint complex, plausibly with Koszul/BRST-type
syzygies.  No theorem here identifies the formal law algebra with a physical QFT, a black-hole
horizon, or cosmology.

The phrase “before there was time” refers to law space before a nonzero propagation direction has
been chosen.  The theorem says that nonlinear selection at that pre-directional horizon already
requires structure beyond one commuting cyclic state.

## Novelty and anti-theatre gate

Integral closure, algebraic elements, cyclic modules, symmetric algebras, induced derivations, and
the failure of a union of two axes to be a subspace are classical.  The free projective-realization
mechanism also has universality parent theories.  None of these ingredients is claimed as new.
Locally algebraic operators and locally finite derivations are an active parent theory; in
particular Chitayat--Daigle--Regeta (2026), *Locally finite sets of derivations*, studies when sets
of derivations share finite-dimensional invariant sectors, but does not formulate a varying-law
complete hypertranscendence horizon or compare it with free projective universality.

Exact searches have not located the combined one-observable classification saying that the
complete algebraic-dependence horizon of an actual cyclic commuting differential orbit is always
linear for every annihilator ideal, while a free noncommuting orbit realizes the nonlinear crossing
and, more generally, arbitrary projective zero loci.  This is an absence-of-hit verdict, not a
priority claim.

The result is scientifically useful because it identifies a real phase boundary and names the
missing carrier.  It is not yet Fields-scale: that requires classifying the nonlinear
commuting/prolonged side or deriving a major consequence that survives its parent-theory audit.

## RH impact

If a proposed zeta or completed-`L` law model reduces to commuting derivations induced linearly from
one cyclic state, its entire differential-algebraic horizon must be projectively linear, regardless
of the annihilator ideal.  Any genuinely nonlinear arithmetic horizon therefore forces an interacting,
gauge, or prolonged source.  This is a stronger route filter; it does not prove RH or supply the
required arithmetic source.

## Lean surface

- `CommutingCyclicHorizonLinearity.lean`
  - `lawLinearForm_injective`
  - `lawLinearForm_isHomogeneous`
  - `mem_commutingCyclicNilpotenceHorizon_iff`
  - `homogeneous_finiteCyclicRelation_iff_radical`
  - `lawLinearForm_hasFiniteCyclicLinearRelation_iff`
  - `commutingCyclicNilpotenceHorizon_add_mem`
  - `crossingCone_not_submodule`
  - `crossingCone_not_commutingCyclicNilpotenceHorizon`
  - `exists_completeJet_crossingHorizon`
  - `crossingHorizon_free_realizable_commutingCyclic_impossible`
- `SymmetricAlgebraAlgebraicIndependence.lean`
  - `symmetricAlgebra_ι_algebraicIndependent_of_linearIndependent`
  - `symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent`
- `CommutingCyclicObservableHorizon.lean`
  - `homogeneous_cyclicPowerState_linearIndependent_iff`
  - `homogeneous_cyclicSymmetricObservableJet_algebraicIndependent_iff`
  - `not_algebraicIndependent_commutingCyclicObservableJet_iff`
- `SymmetricAlgebraDerivation.lean`
  - `symmetricAlgebraDerivation_ι`
  - `symmetricAlgebraDerivation_commute`
- `CommutingCyclicDifferentialObservable.lean`
  - `cyclicLawDerivation_commute`
  - `cyclicDirectionalDerivation_ι`
  - `cyclicDirectionalJet_eq_observableJet`
  - `not_algebraicIndependent_cyclicDirectionalJet_iff`
  - `cyclicDifferentialDependenceHorizon_eq_radicalSubspace`
  - `crossingCone_not_cyclicDifferentialDependenceHorizon`
- `AlgebraicDirectionHorizon.lean`
  - `linearIndependent_powers_iff_transcendental`
  - `symmetricPowerObservable_algebraicIndependent_iff_transcendental`
  - `mem_algebraicDirectionHorizon_iff`
  - `symmetricPowerObservable_dependenceHorizon_eq`
- `CommutingCyclicAlgebraicHorizon.lean`
  - `commutingCyclicObservableJet_algebraicIndependent_iff_transcendental`
  - `not_algebraicIndependent_cyclicDirectionalJet_iff_algebraicHorizon`
  - `cyclicDifferentialDependenceHorizon_eq_algebraicSubspace`
  - `commutingCyclicAlgebraicHorizon_eq_nilpotenceHorizon`
  - `crossingCone_not_cyclicAlgebraicDifferentialHorizon`
  - `crossingHorizon_free_realizable_cyclicAlgebraic_impossible`
- `FreeCommutingHorizonPhaseBoundary.lean`
  - `nonlinearProjectiveHorizon_free_realizable_cyclicCommuting_impossible`

Every declaration is theorem-valued and unconditional.  Direct module elaboration and the isolated
target build pass.  The axiom print reports only `propext`, `Classical.choice`, and `Quot.sound`.
