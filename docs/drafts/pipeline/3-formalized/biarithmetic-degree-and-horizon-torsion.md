# Arithmetic degree and exact horizon torsion

- **ID:** biarithmetic-degree-and-horizon-torsion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Biarithmetic Geometry foundations](../1-in-progress/biarithmetic-geometry-foundations.md); report `docs/reports/review-2410/opus.md`, B1.
- **Statement:** The real box defect cannot be an ordinary cohomological Euler characteristic. On every nonnegative aperture it has an exact decomposition into integer degree, logarithmic finite-group order, and continuous polar evolution.

## Gates

- [x] Precise source invariant and proposed dimension identity identified.
- [x] Dependency-closed paper proof, including the positive replacement on every aperture.
- [x] Direct Lean leaf check passed.
- [x] Transitive axiom audit passed: only `propext`, `Classical.choice`, `Quot.sound`.

## Theorem and proof

[PROVED HERE] Write `E(s)=exp(s)+s-1-ψ(exp(s))`. At `s=log(3/2)`, the von Mangoldt sum is
zero, because there is no prime power below 2. Hence

`E(log(3/2))=1/2+log(3/2)`.

The strict inequalities `0<log(3/2)<1/2` put this value strictly between zero and one. It is
not an integer. Therefore there are no natural-valued functions `h0,h1` on all apertures
with `(h0(s):R)-(h1(s):R)=E(s)`. In particular ordinary finite-dimensional cohomology cannot
satisfy the proposed literal B1 identity.

[PROVED HERE] For `N≥1`, set `L_N=lcm(1,...,N)` and `Q_N=L_N/N`. The inclusion of `N` in
the least-common-multiple range proves `N|L_N`. Thus `Q_N` is a positive integer and
`Q_N N=L_N`. The classical identity `ψ(N)=log L_N` gives

`E(log N)=(N-1)-log Q_N=(N-1)-log #(Z/Q_N Z)`.

For a nonnegative aperture `s`, put `N=floor(exp s)≥1`. Then
`log N≤s<log(N+1)` and `ψ(exp s)=ψ(N)`, so subtraction of the integer-horizon formula gives

`E(s)=(N-1)-log #(Z/Q_N Z)+(exp s-N)+(s-log N)`.

This covers every nonnegative aperture and retains the exact continuous remainder. No
positivity, admission, or zero-location assumption enters the proof.

## Exact Lean statements

Module: `GaloisForLFunctions/BiarithmeticGeometry/ArithmeticEulerCharacteristic.lean`.
Lean indexes the group by `N-1`:

- `no_dimension_model_for_boxDefect`.
- `horizonTorsionOrder_pos`, `horizonTorsionOrder_mul_horizon`.
- `boxDefect_eq_degree_sub_log_card`.
- `arithmeticHorizon_bounds`, `boxDefect_all_apertures`.

Direct command passed: `lake --old env lean GaloisForLFunctions/BiarithmeticGeometry/ArithmeticEulerCharacteristic.lean`.
The classical dependency is Mathlib `Chebyshev.psi_eq_log_lcmUpto`.

## No-go closure

- **Killing theorem:** `no_dimension_model_for_boxDefect` refutes the literal ordinary-dimension identity, not arithmetic cohomology with real degree terms.
- **Strongest positive survivor:** a canonical finite cyclic torsion datum and the exact degree/torsion/continuous decomposition at every nonnegative aperture.
- **New insight:** integer obstruction indices and real arithmetic masses must be separate invariants. Logarithmic torsion supplies a type-correct arithmetic term; it is not a dimension.
- **Limits:** no payment complex, restriction map, Mayer–Vietoris sequence, duality, or vanishing theorem is supplied by this identity.
- **Novelty:** the least-common-multiple identity is classical. The contribution is the precise correction of B1 in the corpus's source coordinates; no general novelty claim is made for arithmetic degree.
- **Selectivity:** exact actual-integer calibration; no source-selective cancellation or orientation estimate.
- **Status:** dependency-closed paper proof, direct leaf check, and transitive axiom audit complete.
