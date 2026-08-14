# Route U Nyquist null-form rigidity and two-ended current

- **ID:** `route-u-nyquist-null-form-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md`, Route U; successor to `U-DYC-global`
- **Statement:** Every quadratic two-channel observable annihilating Route U's parabolic
  `(1,-1)` shell mode factors through exact fine-channel reconstruction; a nonnegative one is only
  a multiple of fine-channel square, while the unique nontrivial class modulo that square is the
  signed Nyquist current `E^2-O^2`, which vanishes at both fixed-divisor infrared and parabolic
  ultraviolet ends.

## Status labels

`[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`

The positive-semidefinite classification is a Route-U specialization of the corpus theorem
`twoChannelLinearCurrent_eq_goodDiagonal_of_nonnegative_of_badWeight_eq_zero` and is therefore
`[REDISCOVERED]`, not new science.  The new Route-U delta is its composition with the formally
proved parabolic parity flip and the resulting identification of the signed two-ended current as
the sole nontrivial ultraviolet-safe quadratic class modulo reconstructed fine energy.

## Conjecture--failure--pivot loop

### U-PN-PSD — nontrivial positive ultraviolet-safe covariance

`[FALSIFIED]` Conjecture: a constant positive-semidefinite quadratic form in even/odd samples can
annihilate the ultraviolet `(1,-1)` mode while retaining a genuinely cross-scale mixed channel.

Killing mechanism: in reconstructed/detail coordinates

```text
S = E + O,       D = E - O,
```

the parabolic mode is pure detail: `(S,D) -> (0,2h)`, where
`h=F_n(-4/u)/2`.  Ultraviolet cancellation forces the pure-`D` coefficient to vanish.  Positivity
then kills the `S D` coefficient by `TwoChannelRelativeCapacityNoGo`; only `lambda S^2` remains.
Because `S` is exactly the full fine sample, this is single-scale energy and retains no independent
dyadic information.

### U-PN-NULL — signed null-form successor

`[PAPER-PROVED]` The killing theorem does not kill signed forms.  Every ultraviolet-safe quadratic
form is a linear combination of `S^2` and `S D`; modulo the scale-trivial `S^2` ray, `S D` is the
unique surviving direction.  In even/odd coordinates it is

```text
J = S D = (E+O)(E-O) = E^2-O^2.                         (U-PN-NULL)
```

The current is two-ended: it tends to zero for every fixed Xi divisor copy and for every positive
quadratic-shell coordinate.  Hostile verdict: `SURVIVES PRELIMINARY ATTACK`.  This is not yet a
global divisor-sum theorem; pointwise two-ended vanishing alone does not provide a summable
majorant.

## Complete paper proof

Let

```text
Q(E,O)=a E^2+2b E O+c O^2.
```

On a positive parabolic shell, the already proved Route-U law gives `(E,O)->(h,-h)`.  Polynomial
continuity therefore gives

```text
Q(E,O) -> (a-2b+c) h^2.                                 (1)
```

Thus the coefficient condition for profile-independent ultraviolet cancellation is
`a-2b+c=0`.  Under this condition `2b=a+c`, and direct expansion gives

```text
Q(E,O)
 = (E+O)(a E+c O)
 = S ((a+c)S/2+(a-c)D/2).                               (2)
```

Conversely every expression on the right has zero pure-`D` coefficient and hence annihilates the
parabolic mode.  Equation (2) proves that safe quadratic forms are spanned by `S^2,S D`, and that
the quotient by the reconstructed square is one-dimensional with representative `S D=E^2-O^2`.

Now assume the real quadratic form is nonnegative on all real channel values.  In `(S,D)`
coordinates write it as

```text
A S^2+2B S D+C D^2.
```

Ultraviolet safety is `C=0`.  The corpus theorem
`twoChannelLinearCurrent_eq_goodDiagonal_of_nonnegative_of_badWeight_eq_zero` gives `B=0` and exact
collapse to `A S^2`; evaluating at `(S,D)=(1,0)` gives `A>=0`.  This proves the PSD classification.

For the two-ended law, exact dyadic recombination gives `S=E+O=full` at every scale.  At each fixed
Xi divisor copy, existing pointwise coherence gives

```text
full -> F,       E-O -> F/2-F/2=0,
```

so `J=full*(E-O)->0`.  On every positive parabolic shell, the new ultraviolet theorem gives

```text
full -> 0,       E-O -> h-(-h)=2h,
```

and again `J->0`.  All limits follow from continuity of subtraction and multiplication.  No zero
count, RH premise, numerical computation, or exchange of limit and divisor sum occurs.  QED.

## Internal and external audit

- `[CORPUS]` `XiShiftedHardEdgeDyadicSampleCoherence.lean`: fixed-divisor even/odd half limits and
  exact reconstruction.
- `[CORPUS]` `XiShiftedHardEdgeParabolicNyquistParity.lean`: parabolic `(1,-1)` parity law.
- `[CORPUS]` `HTGeometry/TwoChannelRelativeCapacityNoGo.lean`: PSD null-diagonal classification.
- `[LITERATURE]` P. P. Vaidyanathan, *Quadrature mirror filter banks, M-band extensions and
  perfect-reconstruction techniques* (1987),
  <https://authors.library.caltech.edu/records/j1cr6-qe046>, supplies classical two-channel
  alias-cancellation/perfect-reconstruction parent theory.
- `[LITERATURE]` S. Narang and A. Ortega, *Perfect Reconstruction Two-Channel Wavelet Filter-Banks
  for Graph Structured Data*, <https://arxiv.org/abs/1106.3693>, gives necessary and sufficient
  spectral-folding alias-cancellation conditions in another two-channel setting.

No audited source states the Xi hard-edge quadratic-shell two-ended current.  The underlying
difference-of-squares and PSD linear algebra are classical and receive no novelty credit.

## Exact open core

Prove a weighted complete-Xi divisor theorem for `J` with completed resolvent weight: absolute
summability or a source-exact signed summation law, uniform across the infrared/parabolic transition.
Only then test whether the sum equals the nonlinear node-transport plus prime--Gamma covariance
appearing in `U-DYADIC-SOURCE`.  Pointwise vanishing at both ends is insufficient.

## Gates

- [x] 0 → 1: exact falsifiable quadratic classification and hostile attack
- [x] 1 → 2: dependency-closed proof above
- [ ] 2 → 3: exact Lean theorem and axiom audit
- [ ] 3 → 4: independent novelty/significance audit and standalone exposition

## Log

- 2026-08-14 — Nontrivial PSD survivor conjecture falsified by existing two-channel null-diagonal
  theorem after rotating to reconstruction/detail coordinates.
- 2026-08-14 — Strongest positive survivor `U-PN-NULL` paper-proved: unique signed quotient current
  and its fixed-divisor/parabolic two-ended vanishing law.
