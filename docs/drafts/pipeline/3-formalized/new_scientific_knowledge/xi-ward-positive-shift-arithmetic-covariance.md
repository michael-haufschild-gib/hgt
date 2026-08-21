# Xi Ward positive-shift arithmetic covariance

- **ID:** `xi-ward-positive-shift-arithmetic-covariance`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** internal W-H190/W-H191 reflection--Loewner chain
- **Statement:** Opposite-Euler specialization of the reflection--Loewner kernel is exactly a
  positive-real-shift quotient of the completed pole--Gamma--von-Mangoldt current, with derivative
  as its punctured diagonal finite part.  Its meromorphic continuation has local residue equal to
  the normalized discrete derivative of Xi multiplicity.

## Goal

Supply missing pre-divisor covariance behind submicroscopic reflection separation.  Both source
arguments remain in absolute-Euler chambers; no Xi zero, divisor copy, critical-line projector,
or RH premise enters the covariance.

## Gates

- [x] 0 → 1 in-progress: source-pure specialization and diagonal limit identified.
- [x] 1 → 2 fully-proven: algebraic chamber proof and general derivative finite-part proof.
- [x] 2 → 3 formalized: direct module build, formal lint, and axiom audit pass.
- [ ] 3 → 4 publication-ready: requires height-local trace theorem and novelty audit.

## Theorem

Let

```text
A(z) = z⁻¹ + (z-1)⁻¹ + Gamma_R'(z)/Gamma_R(z)
       - sum_n Lambda(n)n^(-z).
```

For `Re z>1` and real `eps>0`, put the opposite-chamber source nodes

```text
s = 1-z,       t = conjugate(z+eps).
```

Then `Re s<0`, `Re t>1`, and the W-H190 reflection--Loewner kernel satisfies

```text
K(s,t) = [A(z+eps)-A(z)]/eps.
```

The quotient splits exactly into pole--Gamma increment plus sign-oriented von Mangoldt increment

```text
[L_Lambda(z)-L_Lambda(z+eps)]/eps.
```

For complex punctured `eps→0`, any derivative certificate `HasDerivAt A d z` gives convergence of
the covariance to `d`.  Thus diagonal finite part is fixed before divisor expansion.

There is also an exact source-to-divisor transgression.  Write `F=-xi'/xi`.  On the source chamber,

```text
[A(z)-A(z-eps)]/eps = -[F(z)-F(z-eps)]/eps.             (PS2)
```

Continue the right side only after forming the left side.  Its removable local residue germ at
`rho` has center value

```text
[ord_xi(rho)-ord_xi(rho-eps)]/eps.                      (PS3)
```

At a left translation boundary the predecessor is regular, so `(PS3)` is exactly
`ord_xi(rho)/eps>0`.  Positive shift is therefore source-defined before scalarization, while
diagonal multiplicity is recovered only as the post-scalarization residue.

## Reach and open core

This repairs provenance defect in Abel/exterior-Cesàro candidates: reflection covariance can be
formed using only absolute-Euler values.  It does **not** prove

```text
B_corrected(K_T) <= B_tilde_T + o(N(T)),
B_tilde_T <= (4/25) N(T) + o(N(T)).
```

Remaining non-circular theorem must localize trace of this positive-shift covariance in height,
retain W-H190 cubic bichamber feature through coalescence, and prove pole--Gamma--von-Mangoldt
upper constant `4/25`.  Direct scalar trace-capacity comparison is excluded by P-G176 because it
is RH-equivalent.

## Formal artifact

Module:

```text
formal/GaloisForLFunctions/RHTower/
  XiWardCubicPositiveShiftArithmeticCovariance.lean
```

Principal declarations:

- `xiWardCubicReflectionLoewnerKernel_eq_positiveRealShiftArithmeticCovariance`;
- `xiWardCubicShiftArithmeticCovariance_eq_poleGamma_add_vonMangoldt`;
- `tendsto_xiWardCubicShiftArithmeticCovariance`;
- `xiWardCubicPositiveShiftDivisorTransgression_eq_arithmeticCovariance`;
- `xiWardCubicPositiveShiftDivisorTransgressionGerm_zero`;
- `xiWardCubicPositiveShiftDivisorTransgressionGerm_zero_re_pos_of_leftBoundary`.

Target build passed. `scripts/formal_tools.py lint` passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-21 — conjectured from moving reflection-hyperplane residue, numerically checked at two
  complex Euler points and three decreasing shifts, then proved and formalized.
- 2026-08-21 — welded source covariance to Hedenmalm translated-divisor transgression; proved
  exact multiplicity-difference residue and strict positivity on every positive left boundary.
