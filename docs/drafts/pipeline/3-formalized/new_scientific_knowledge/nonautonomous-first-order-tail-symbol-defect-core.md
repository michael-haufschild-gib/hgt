# First-order tail tensor-symbol and defect-budget core

- **ID:** nonautonomous-first-order-tail-symbol-defect-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[FORMALIZED CORE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Paper theorem:** `../../2-fully-proven/new_scientific_knowledge/nonautonomous-first-order-tail-symbol-defect-law.md`
- **Lean module:** `formal/GaloisForLFunctions/HTGeometry/NonautonomousFirstOrderTailSymbol.lean`

## Certified theorem surface

Lean defines the integer-weight tensor evaluation

```text
tensorJetObservable q k y dy = q(y) dy^k
```

and proves exact transport under a rational first-jet constraint and exact composition through two
layers:

```text
tensorJetObservable_transport
tensorSymbol_transport_comp
```

The local ramification mechanism is certified by

```text
pullbackZeroMultiplicity_fiber
```

which proves that a terminal zero of multiplicity `m` contributes at least `D*m` total
multiplicity over any degree-`D` pullback fiber.

The finite transient law is certified by

```text
futureTensorDefect_eq_zero_of_degree_gt
tensorDefect_eq_zero_after_log
tensorDefect_eventually_zero
```

If `D_n Z_n <= Z_0` and `2^n <= D_n`, Lean proves `Z_n=0` after the exact binary-logarithmic
budget and proves eventual vanishing at `Filter.atTop`.

The integral-holonomy step is certified by

```text
tensorFiber_subset_exceptional_of_not_dvd
tensorFiber_degree_le_exceptionalBudget
terminalTensorAngle_dvd_of_exceptionalBudget_lt_degree
```

Lean proves that a terminal angle not dividing the regular tensor angle forces its full fiber into
the finite exceptional divisor.  If the covering degree exceeds the entire exceptional angle
budget, this is impossible; hence every positive terminal angle divides the tensor order.  This is
the exact combinatorial quantization mechanism behind the eventual integral orbifold weights.

## Formalization boundary

The module certifies the tensor evaluation, composition, local multiplicity amplification, exact
budget cutoff, eventual defect collapse, and exceptional-support angle quantization.  The
paper-level extraction of the first nonzero
vertical Laurent symbol from an arbitrary transported order-one rational observable is not hidden
as an axiom; it remains outside the current rational-function valuation API.

## Verification

- Targeted direct compilation: PASS.
- Targeted `.olean` generation: PASS.
- Scratch `#print axioms`: only standard `propext`, `Classical.choice`, and `Quot.sound` where
  present; `futureTensorDefect_eq_zero_of_degree_gt` is axiom-free.
- No full project build was run.

## RH impact audit

The formal law is a structural obstruction for any future zeta-related rational protocol: a
first-order persistent tensor defect cannot recur beyond its degree-amplified finite budget.  No
source-pure zeta protocol or RH-sensitive tensor is constructed here, so there is no direct RH
implication.
