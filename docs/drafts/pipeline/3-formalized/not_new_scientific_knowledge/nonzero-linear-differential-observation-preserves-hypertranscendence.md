# Nonzero linear differential observations preserve hypertranscendence

- **ID:** `nonzero-linear-differential-observation-preserves-hypertranscendence`
- **Stage:** 3-formalized
- **Type:** `[PROVED ELSEWHERE]` / `[BRIDGE]` / reusable corpus strengthening
- **Register:** `[CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`
- **Formal files:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialOperatorToeplitzRank.lean` and
  `formal/GaloisForLFunctions/RHTower/PrimeSourceFiniteDifferentialCircuit.lean`

## Statement

Let `C` be a coefficient field embedded as constants in a differential field `K`.  For a
polynomial `P in C[D]`, write `P(D)x` for its constant-coefficient differential observation of
`x`.  Lean proves

```text
P != 0 and HypertranscendentalOver C x
  -> HypertranscendentalOver C (P(D)x).                 (1)
```

The arithmetic specialization is unconditional for every orientation `epsilon`:

```text
P != 0
  -> HypertranscendentalOver C
       (P(D)(signedPrimeNaturalShiftPalette epsilon 0)). (2)
```

Thus a nonzero finite linear differential filter changes the clock reading but cannot hide or
collapse its infinite differential observation structure.

## Proof

Hypertranscendence of `x` is differential independence of its singleton family.  Regard `P` as a
one-row, one-column matrix over `C[D]`.  Its row is linearly independent exactly when `P != 0`.
The existing differential-operator Toeplitz-rank theorem then says that the output singleton
`P(D)x` is differentially independent.  This is exactly `(1)`.

For `(2)`, the existing signed-prime palette theorem supplies differential independence of all
natural shifts.  Restriction to shift zero gives a named source theorem, and `(1)` applies because
the complex constants have zero derivative in the arithmetic-function field.

The same source theorem also removes the duplicated inline differential-independence argument from
the existing finite-circuit source-extraction proof.

## Functional-identifiability transfer

Differential-equation identifiability eliminates hidden states to finite input--output differential
relations.  In genetics, systems biology, and neural ODE model discovery, the observed signal is
often filtered by a nonzero polynomial in the derivative before an unknown constitutive function
or parameter combination becomes visible.  Equation `(1)` gives the positive HT conclusion:
linear differential observation does not merely fail to generate an HT clock; it produces another
HT observable whenever the input clock is HT.

This differs from the earlier finite-circuit boundary.  That theorem says a finite DA circuit
cannot manufacture hypertranscendence and must contain an HT atom.  Equation `(1)` says a broad
and important class of finite observation circuits preserves HT at its output.  It is therefore a
source-producing closure law, not only a no-go.

The immediate literature prompt is T. E. Loman--A. P. Browning--R. E. Baker, *Structural
functional identifiability and model discovery in differential equation models*, arXiv:2606.30289.
The paper derives differential input--output equations for unknown functional components and shows
that identifiability depends on model structure and the chosen observable.  A. F. Villaverde,
*Observability and Structural Identifiability of Nonlinear Biological Systems*, arXiv:1812.04525,
is the biological-systems parent for the observability/identifiability distinction.  The algebraic
proof of `(1)` is a direct singleton specialization of the already formalized Toeplitz-rank law;
no scientific novelty is claimed.

## ML, AI, genomics, genetics, and physics value

- A learned finite derivative filter cannot turn an exact HT latent signal into a DA output unless
  the filter is zero.
- A genomic or biochemical reporter defined by a nonzero constant-coefficient differential readout
  preserves HT of the underlying exact clock signal.
- In equation learning, applying a nonzero linear differential preconditioner does not lower the
  target from HT to DA; symbolic recovery cannot evade the finite-circuit boundary by such a
  preprocessing step.
- In physics, nonzero constant-coefficient response, susceptibility, and linearized field operators
  preserve HT of an exact observable.  A finite filter can reorganize the source but cannot be
  credited with removing its infinite differential rank.

These statements concern exact representations.  They make no claim about approximation by finite
models, noisy finite samples, or variable-coefficient operators.

## RH impact

Equation `(2)` applies the new finding directly to the arithmetic source used by the RH corpus.
Every nonzero polynomial differential reading of every signed-prime orientation is now a certified
HT source.  Consequently:

1. a proposed physics/AI/genomics bridge cannot make the signed-prime source DA by finite linear
   differential filtering;
2. downstream arguments may select a useful nonzero differential observation without reproving
   hypertranscendence;
3. any route claiming collapse after such a filter must prove that its operator symbol is actually
   zero, which is an exact algebraic obstruction.

This does not orient zeros or prove a missing positivity estimate.  Its positive use is to enlarge
the certified source class and remove an avoidable source hypothesis from every future nonzero
constant-coefficient differential observation of the prime carrier.

## Formalized declarations

- `HTGeometry.hypertranscendentalOver_differentialOperatorApply`
- `RHTower.signedPrimeSource_hypertranscendentalOver`
- `RHTower.signedPrimeSource_differentialOperator_hypertranscendentalOver`

## Verification

- both touched Lean source files pass direct `lake env lean` checks;
- no numerical computation or full build was used;
- the theorem is a specialization of the existing exact differential-operator matroid law, not a
  new axiom or an assumed identifiability principle.

## Gates

- [x] parent-theory and current-literature audit
- [x] general HTGeometry preservation theorem
- [x] direct signed-prime arithmetic consumer
- [x] existing finite-circuit proof simplified through the named source theorem
- [x] extend from constants to coefficients in a finite-trdeg derivation-closed reservoir
      (`finite-reservoir-variable-differential-observation-preserves-hypertranscendence`)
- [ ] use a selected preserved observation to discharge a sign/value hypothesis
- [ ] RH
