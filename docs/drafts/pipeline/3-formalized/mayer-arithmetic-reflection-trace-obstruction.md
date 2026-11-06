# Arithmetic reflection fails for the full Mayer spectral family

- **ID:** mayer-arithmetic-reflection-trace-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Γ25.
- **Target:** The actual first Fredholm trace is not invariant under `w↦1−w` on any nonempty open subset of the critical strip. The full spectral determinant cannot have that reflection symmetry even up to a scalar factor independent of the spectral parameter.

## Proof

The corpus identifies the actual trace as `T(w)=ζ(w)+R(w)`, where the
fixed-point correction `R` is holomorphic on `Re w>−1`. Thus `T` is
holomorphic at zero and has residue one at one. Reflection therefore gives

`w[T(1−w)−T(w)]→−1` as `w→0`.

More precisely, put `U(w)=ζ_reg(w)+R(w)` and
`H(w)=U(1−w)−U(w)`. On `−1<Re w<2`, the function

`G(w)=w(w−1)H(w)+1−2w`

is holomorphic, with `G(0)=1`, `G(1)=−1`, and `G(1−w)=−G(w)`.
Away from the endpoints it equals `w(w−1)[T(1−w)−T(w)]`.
Holomorphic uniqueness therefore excludes trace reflection invariance even
on a nonempty open subset of the strip. The derivative at spectral
parameter zero is `−T(w)`, transferring the obstruction to the actual
Fredholm determinant.
Since `D(w,0)=1`, an identity `D(1−w,λ)=c(w)D(w,λ)` for every `λ`
forces `c(w)=1`. Thus the same obstruction excludes such scalar factors.

The fixed-point summands have positive real bases, so conjugation commutes
with their complex powers and with the normally convergent correction.
Together with zeta conjugation this gives `T(conj w)=conj T(w)`.
Consequently `T(1−conj w)≠conj T(w)` somewhere in every such open subset.
An identity `D(1−conj w,conj λ)=c(w)conj D(w,λ)` again forces `c(w)=1`;
differentiating after replacing `λ` by `conj λ` gives the excluded trace
identity. The obstruction therefore includes conjugated arithmetic reflection.

## Positive survivor and scope

The invariant is the reflected trace defect's residue: `−1` at zero
and `−1` at one. Its pole-free remainder is holomorphic across the closed
critical strip. The exact decomposition separates these polar terms from
the holomorphic reflection remainder.

This concerns preservation of the full spectral family. It does not exclude
arithmetic reflection of the selected scattering divisor, or the existing
closed Cauchy reflection between different parameter spaces.

## Lean declarations

`RenormalizedIntersectionTheory/GaussMayerArithmeticReflectionTraceObstruction.lean`,
namespace `MayerArithmeticReflection`:

- `traceReflectionRemainder_eq` and
  `differentiableOn_traceReflectionRemainder`: exact pole-free remainder.
- `clearedTraceReflectionDefect_zero`, `clearedTraceReflectionDefect_one`,
  `clearedTraceReflectionDefect_reflect`: endpoint charges and odd reflection.
- `traceReflectionDefect_residue_zero`, `traceReflectionDefect_residue_one`:
  both residues equal `−1`.
- `exists_trace_ne_reflect_in_open`: local trace obstruction.
- `sourceDeterminant_deriv_zero`: actual determinant-to-trace bridge.
- `exists_spectralDeterminant_no_scalar_reflection_in_open`: every nonempty
  open strip subset contains a parameter where no scalar factor works for
  the full spectral family.
- `continuedTrace_conj`, `exists_trace_ne_arithmetic_reflect_in_open`, and
  `exists_spectralDeterminant_no_scalar_arithmetic_reflection_in_open`:
  the corresponding conjugated arithmetic reflection obstruction.

No operator-similarity claim is made without proving its determinant invariance.

The direct production `lake --old env lean` check passes. Transitive axioms
are only `propext`, `Classical.choice`, and `Quot.sound`. The RIT umbrella
import is wired. Γ25 is partially solved; physical descent remains open.
