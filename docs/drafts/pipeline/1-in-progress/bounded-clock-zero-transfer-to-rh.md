# Bounded-clock zero transfer to RH

- **ID:** `bounded-clock-zero-transfer-to-rh`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / TOP-DOWN RH TRANSFER
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Statement:** Locally uniform approximants whose off-real zero fibres ride positive vertical
  arithmetic progressions with a uniform upper bound on their periods force the limit divisor to
  have the same periodicity.  Applied vertically in the centered `XiC` coordinate, the positive
  limiting period is ruled out by the elementary zero-free half-plane for `xi`, and the shrinking
  period is ruled out by analyticity.  Therefore the approximation law forces RH.

## The missed compactness alternative

Let `F_n -> F` locally uniformly on a vertically shift-closed domain, let `z_n -> z`, and suppose

```text
F_n(z_n+k T_n i)=0        for every k in Z,
0<T_n<=B.
```

Compactness of `[0,B]` gives a subsequence `T_n -> T`.

1. If `T>0`, locally uniform convergence gives

   ```text
   F(z+k T i)=0           for every k in Z.
   ```

2. If `T=0`, for each real `t` choose `k_n=floor(t/T_n)`.  Then

   ```text
   k_n T_n -> t,
   F_n(z_n+k_n T_n i)=0,
   F(z+t i)=0.
   ```

   Thus `F` vanishes on the whole vertical line through `z`.  If `F` is analytic and nonzero,
   this branch is impossible.

The existing `ClockEscape.lean` theorem only handles a fixed finite inventory of periods.  The new
argument handles continuously varying clocks and periods tending to zero.  Shrinking a clock does
not evade zero-locus closure: it produces a dense vertical mesh and collapses the analytic limit.

Coordinate warning: a vertical clock in the centered variable `z` is a horizontal clock in the
original variable `s`, because `s=1/2+iz`.  Ordinary Euler-column clocks are vertical in `s` and
therefore real in `z`; they do not instantiate this theorem.

## Top-down RH chain

For `XiC(z)=xi(1/2+iz)`, assume `F_n -> XiC` locally uniformly, the `F_n` are eventually entire,
and for one finite `B` the following finite-stage source predicate holds eventually:

```text
BoundedVerticalClockDichotomy B F_n:
  F_n(w)=0
  -> Im(w)=0 or
     exists T, 0<T<=B and F_n(w+kTi)=0 for every k in Z.
```

Hurwitz selection of zeros converging to each `XiC` zero is proved internally.  Then

```text
bounded-clock approximant zero fibres
  -> positive limiting clock or vertical zero continuum
  -> off-real XiC zero lies on a vertical arithmetic progression
  -> horizontal xi-zero progression entering Re(s)>=1, impossible
  -> every XiC zero is real
  -> RH.
```

This is not a restatement of RH through positivity, a Hermitian determinant, or a zero-side norm.
Its antecedent is an approximation-stable source constraint on the divisor-generating clocks.

The theorem `xiC_no_vertical_zero_progression` discharges the positive limiting-period branch
unconditionally: a negative integer step eventually maps to `Re(s)>=1`, where `xi` is nonzero.
The theorem `riemannHypothesis_of_bounded_vertical_clock_dichotomy_approximants` carries the full
source-level composition with no no-arithmetic-progression or limiting-zero-sequence premise.  The
older `riemannHypothesis_of_bounded_clock_zero_approximants` remains as the lower-level sequence
interface.  The vertical-continuum branch is discharged internally.

## Lean status

`formal/GaloisForLFunctions/RHTower/BoundedClockZeroTransfer.lean` proves:

- `tendsto_intFloor_mul_of_pos_of_tendsto_zero`;
- `periodic_zero_limit_of_period_tendsto`;
- `shrinking_periodic_zero_limit_vertical`;
- `bounded_periodic_zero_limit`;
- `xiC_no_vertical_zero_progression`;
- `riemannHypothesis_of_bounded_clock_zero_approximants`;
- `exists_XiC_zero_approximating_subsequence`;
- `BoundedVerticalClockDichotomy`;
- `riemannHypothesis_of_bounded_vertical_clock_dichotomy_approximants`.

The file compiles with the project toolchain and is imported by the RHTower umbrella.

## Exact open source obligation

The sole remaining theorem is now the finite-stage predicate itself: construct a completed
approximant family `F_n` converging locally uniformly to `XiC` and prove

```text
eventually BoundedVerticalClockDichotomy B F_n
```

for some finite `B`.  These are bounded vertical clocks in the `XiC` variable, equivalently
bounded horizontal clocks in the original `s` variable.  Unscreened finite-prime Euler columns do
not supply this orientation: their clocks are vertical in `s`.  The known theta cusp screen couples
the columns and supplies no horizontal zero-fibre clock law either.

The next top-down question is therefore exact:

> Is there a source-pure completion whose off-real zeros carry a bounded transverse
> (horizontal-`s`) clock, while its remaining zeros are forced onto the real `XiC` axis?

No finite-prime resolvent, theta derivative, or screen-convergence lemma is requested unless it
proves that zero-fibre dichotomy.
