# Generalized Clifford shift-suspension horizon

- **ID:** `generalized-clifford-shift-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM / DIFFERENTIAL FIELD / GENERALIZED CLIFFORD PRINCIPAL SYMBOL
- **Scientific status:** `[LEAN-PROVEN] [UNCONDITIONAL GIVEN EXPLICIT POWER-RELATION DATA]`
- **Lean modules:**
  - `formal/GaloisForLFunctions/HTGeometry/GeneralizedCliffordShiftHorizon.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GeneralizedCliffordShiftFieldHorizon.lean`
  - `formal/GaloisForLFunctions/HTGeometry/SymmetricAlgebraDerivationLinear.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GeneralizedCliffordPrincipalSymbolLaw.lean`

## Theorem

Let `K` be a field, `V` a linear law space, `M` a nonzero internal state space, and

```text
symbol : V ->_K End_K(M)
```

a linear pencil.  Fix `d>0`, a scalar function `F:V->K`, and assume the pointwise power relation

```text
symbol(c)^d = F(c) I_M                                                (1)
```

for every `c`.

Put one copy of `M` at every nonnegative grade.  Suspend `symbol(c)` by the unilateral shift and
extend the resulting linear state action to a derivation of the symmetric observable algebra.
Extend that derivation by the quotient rule to the fraction field

```text
L = Frac(Sym_K(N -> M)).                                              (2)
```

For a nonzero root state `m`, let `y` be its grade-zero observable.  Then the complete ordinary
differential jet satisfies

```text
{delta_c^n(y) : n>=0} algebraically independent over K
                    <-> F(c) != 0.                                   (3)
```

Equivalently, the exact differential-dependence horizon is

```text
{c : V | the complete jet is algebraically dependent} = {c | F(c)=0}. (4)
```

The construction `c |-> delta_c` is a linear map into field derivations.  If `v,w` lie on the
horizon and one linear combination `a v+b w` lies off it, then

```text
[delta_v,delta_w] != 0.                                               (5)
```

## Proof mechanism

The suspended state orbit has the exact form

```text
T(c)^n(e_0 tensor m) = e_n tensor symbol(c)^n m.                      (6)
```

If `F(c)=0`, equation `(1)` kills the orbit at order `d`.  If `F(c)!=0`, equation `(1)` makes
`symbol(c)` injective, so every state in `(6)` is nonzero.  Distinct iterates occupy distinct
grades and are linearly independent.  Canonical degree-one observables in a symmetric algebra are
algebraically independent exactly when their state vectors are linearly independent.  The
injective fraction-field embedding preserves that independence.

Linearity is proved for the state suspension, the symmetric-algebra derivation, and its
fraction-field extension.  Equation `(5)` then follows from the already formalized commuting-chord
principal-symbol theorem.

## Lean theorem surface

- `generalizedCliffordShiftOperator_orbit`
- `generalizedCliffordPowerRelation_injective`
- `generalizedCliffordShiftOperator_orbit_linearIndependent`
- `generalizedCliffordShiftJet_algebraicIndependent_iff`
- `generalizedCliffordShift_dependenceHorizon_eq_zeroLocus`
- `generalizedCliffordShiftFieldJet_algebraicIndependent_iff`
- `generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus`
- `symmetricAlgebraDerivationLinearMap`
- `generalizedCliffordShiftFieldDerivationLinearMap`
- `generalizedCliffordField_linearDependenceHorizon_eq_zeroLocus`
- `generalizedCliffordField_escapingChord_forces_noncommute`

## Verification

Direct checks and narrow cached builds passed for the new modules.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound` for the exact field horizon and escaping-chord
theorems.  There are no `sorry`, `admit`, project axioms, opaque declarations, or unsafe
declarations in this theorem surface.

## Scope boundary

The Lean theorem assumes the explicit power relation `(1)`.  It does not yet formalize:

- the universal Roby generalized Clifford algebra;
- the equivalence between its finite-dimensional modules and pencils satisfying `(1)`;
- the Van den Bergh correspondence with Ulrich bundles;
- existence of Ulrich bundles on smooth hypersurfaces;
- the positive-Hilbert obstruction;
- Ulrich separation of Clifford bivectors.

Accordingly, the all-smooth-hypersurfaces existence claim remains paper-level and dependent on
external parent theorems.  The shift-suspension implication itself is unconditional in Lean.

## RH impact

The theorem supplies an exact finite-width source architecture for an arithmetic form once a
power-relation pencil is constructed.  No such pencil is currently proved for Xi or a completed
L-function, so this is a source criterion rather than an RH implication.
