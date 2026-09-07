# CCM-FU: exact transport outside the negative support

- **Stage:** 3-formalized
- **Type:** [BRIDGE], complete mixed-field transport constraint
- **Parent:** [defect-supported extension](../1-in-progress/ccm-fu-defect-supported-extension.md).
- **Boundary:** Complete certificate extension, signed Abel bound and RH remain open.

## Closed source statement

For the actual oriented retained field A_P, let N(P) be the union of all
negative nonempty labels. Its members are active primes. Then an active
prime q belongs to N(P) exactly when some surviving q-free coordinate
strictly increases under its merger.

Indeed `A_(P+q)(R)=A_P(R)-A_P(R+q)`. A negative partner makes this increase
strict. Conversely every negative q-containing label has the form R+q
with R q-free, supplying that increase. Every label is retained in the
argument; there is no restriction on cardinality or head sign.

If q lies outside N(P), every q-containing coordinate is nonnegative.
All q-free coordinates decrease under subtraction. Their positive parts
therefore decrease and their negative parts increase. The deleted
q-containing coordinates have zero negative parts. Summing squares gives

`G_(P+q)<=G_P`, `D_P<=D_(P+q)`.

Consequently every strict total defect decrease must select q in N(P).
This is a necessary support condition, not a sufficient certificate bound:
a prime in N(P) may create new negative coordinates while absorbing others.
Even outside N(P), decreased good energy may pay increased defect energy.

## Lean declarations

`formal/GaloisForLFunctions/RHTower/MobiusDivisorNegativeSupport.lean`,
namespace `RHTower`:

- `mobiusDivisorNegativeSupport` defines the actual finite support.
- `mobiusDivisorNegativeSupport_iff_coordinate_increase` gives the exact
  support classification.
- `mobiusDivisorParityEnergy_insert_outside_negativeSupport` gives both
  complete energy inequalities for arbitrary mixed fields.
- `mobiusDivisor_mem_negativeSupport_of_defect_drop` gives the necessary
  condition for a strict defect decrease.

The proof uses the literal merger identity and monotonicity of squared
positive parts. It is independent of the numerical path experiment.

## Validation

Scratch and exact leaf checks passed with `lake env lean`; only the new
leaf olean was emitted. One audit of all four new public declarations found
only `propext`, `Classical.choice` and `Quot.sound`. The module is wired into
`RHTower`, the research index is refreshed, and formal lint passed. No
dependency, full or umbrella build ran; the previously encountered Lake
stale-dependency audit was not repeated. Owned scratch files were removed
and every owned Lean process terminated.
