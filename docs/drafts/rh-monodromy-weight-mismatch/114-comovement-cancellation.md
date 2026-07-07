# 114 — The co-movement pivot resolved: the mirror orientation is ONE angle

[PROVED HERE, Lean: `RelativePhase.lean`; builds on the co-movement no-go
`rotatedConj_im_can_be_assigned` and the mirrored reachability
`anchorMirrorDefect_reachable_nonpos` (both verified, axiom-clean, gate 9224 exit 0).]

## The pivot (the no-go, verified)

`rotatedConj_im_can_be_assigned`: for ANY defect angle `d` and ANY target `y` there is
a source value `z ≠ 0` with `Im(e^{−id}·conj z) = y`. So defect reachability ALONE
cannot force the mirror orientation — the source incidence `ι_P(s)` co-moves with the
same prime set P. Correct, and it forced the right question: what is the JOINT motion?

## The resolution: the co-movement cancels exactly

`incidence Λ₁ Λ₂ = −Λ₂/Λ₁`, so the source incidence divides by the anchor, whose
canonical phase IS `anchorTilt P s` (the polar identity). The defect is
`tilt_P(1−s̄) + tilt_P(s)`. In the mirror-orientation formula the `tilt_P(s)` from the
defect rotation and the `−tilt_P(s)` inside `arg ι_P(s)` CANCEL:

**`im_incidence_anchored_mirror_tilt_only`** (and the SEM version):

```
Im ι_P(1−s̄) = ‖A_P(1−s̄)‖⁻¹ · Im( e^{−i·anchorTilt P (1−s̄)} · conj(−G(s)) )
```

The P-dependence of the mirror orientation is exactly ONE angle — the anchor tilt at
the MIRROR point — acting on a P-FREE member phase `conj(−G(s))` (the member carries no
primes), scaled by a positive modulus that cannot change any sign. The joint
(defect, source) problem the no-go demanded collapses back to a single-angle steering
problem — strictly simpler than the defect itself (one tilt instead of a two-point sum).

## The steering engine carries over verbatim

- `anchorTilt_mirror_eq_sum` — the mirror tilt is the prime-indexed walk
  `∑_q primeTilt q (1−s̄)`;
- `primeTilt_mirror_pos_iff` / `_neg_iff` — its per-prime steps have the sign of
  `sin(Im s·log q)`, the same sine law as the defect (the mirror point has the same
  height);
- the arctan floors, budget ceilings, window counts, and greedy accumulation of docs
  112–113 apply unchanged: the ORIENTATION-STEERING ANGLE is reachable by the same
  Chebyshev-window machinery that reached the defect.

## Route state

The meeting functional now reads, with everything machine-checked:

```
sign( Im ι_P at mirror edge ) = sign( Im[ e^{−i·θ_P} · conj(−G(s)) ] ),
θ_P := anchorTilt P (1−s̄) — steerable, sign-lawed, window-suppliable
conj(−G(s)) — FIXED once the annulus datum is fixed (no P)
```

As θ_P sweeps (reachable to any nonnegative value within any ε at Chebyshev heights,
and mod-2π sweeping is all the sign needs), `Im(e^{−iθ}·conj(−G s))` crosses EVERY sign
unless `G(s) = 0`. The remaining question of the weld is therefore no longer whether
the orientation datum CAN be moved — it provably can, through the full circle — but
what the parity criterion's two-point AGREEMENT demands as BOTH basepoint orientations
move under the same P: the two steering angles `anchorTilt P (1−s̄)` at the two
basepoints share their prime walk. Next object: the two-point joint sweep — the pair
`(θ_P(P₊), θ_P(P₋))` as a walk in the torus, its per-prime increments, and what the
even/odd positions of `split_deckClass_one_iff_even` look like in those coordinates.
