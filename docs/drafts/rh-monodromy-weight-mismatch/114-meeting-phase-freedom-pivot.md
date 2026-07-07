# 114 — Meeting phase freedom: reachability closes the budget side, not the orientation side

[PROVED HERE, Lean: `AnchorTilt.lean`, `WindowBudget.lean`] — doc 113's first
follow-up is now closed, and the meeting argument has a sharper open core.

## New formal facts

**Negative reachability is closed.**  `WindowBudget.lean` now contains:

- `anchorMirrorDefect_reachable_nonpos_magnitude`: for
  `0 < Im s < π/(2 log 2)`, every magnitude `T ≥ 0` and tolerance `ε > 0` has a
  finite prime set `P` with

  ```
  -T - ε ≤ anchorMirrorDefect P s ≤ -T.
  ```

- `anchorMirrorDefect_reachable_nonpos`: equivalently, every nonpositive target
  `T ≤ 0` is hit from below:

  ```
  T - ε ≤ anchorMirrorDefect P s ≤ T.
  ```

The proof is the mirror of doc 113's positive window proof at phase offset `5π/4`.
The new reusable increment lemmas are:

- `mirrorTiltIncrement_conj`: the single-prime mirror increment is Schwarz-odd;
- `neg_mirrorTiltIncrement_ge`: a negative sine window gives the same quantitative
  arctangent floor for `-mirrorTiltIncrement`.

Thus below the Chebyshev threshold height the finite Euler head can steer the defect
to both sides, to arbitrary precision.

## The meeting equation is not a one-coordinate sweep

The anchored incidence mirror law is already formalized:

```
Im ι_P(1-s̄)
  = positive scale · Im(e^{-i·D_P(s)} · conjugate(ι_P(s))),
```

where `D_P(s) = anchorMirrorDefect P s`.

Reachability controls `D_P(s)`.  It does not by itself control `ι_P(s)`, because the
source incidence value also depends on the same prime set `P`.  This is now banked
formally as:

```
rotatedConj_im_can_be_assigned :
  ∀ d y, ∃ z ≠ 0,
    Im(e^{-i d} · conjugate(z)) = y.
```

So the defect angle alone cannot force a mirror endpoint orientation.  For any fixed
reachable angle, an unconstrained co-moving source value can realize either sign, zero,
or any prescribed imaginary coordinate.

## Pivot

The reachable-angle problem is solved in the Chebyshev height range, on both signs.
The remaining open core is not prime supply; it is **source phase control**.

A proof of endpoint agreement must provide one of the following stronger inputs:

1. a cone/half-plane theorem for `ι_P(s)` at the source endpoint, uniform over the
   prime sets used by the defect walk;
2. a coupled-variation theorem showing that the change of `ι_P(s)` cannot cancel the
   steered angle `D_P(s)`;
3. a quotient or normalized meeting functional in which the source phase cancels while
   the defect term survives.

Without one of these, "defect reaches every angle" does not imply "endpoint
orientations agree."  The route therefore moves from budget reachability to a
controlled-source-value theorem.
