# HB symmetry-only affine-collision exclusion no-go

- **ID:** HB-SS-SYM-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · HB self-source/nonvanishing edge
- **Statement:** Functional-equation reflection, conjugation symmetry, strip confinement, real-axis nonvanishing, and isolated zeros alone do not exclude a strict-right zero `q` with a simultaneous zero at `q / 2`.

## Goal

Retire the attempted proof of HB strict-right self-source nonvanishing that uses only generic zero symmetries and elementary zero geometry. This does not decide the arithmetic collision question for the actual Xi function.

## Gates

- [x] 0 → 1 in-progress: source-pure candidate and falsification target stated.
- [x] 1 → 2 fully-proven: complete finite-polynomial countermodel below.
- [x] 2 → 3 formalized: `RHTower.XiAffineCollisionSymmetryModelNoGo.collisionModel_reflect`, `collisionModel_conj`, `collisionModel_root`, and `collisionModel_half_root`; isolated module audit green.
- [ ] 3 → 4 publication-ready: not a standalone RH result.

## Approach

For `R_b(s) = (s-b)(s-(1-b))`, set
`P_a(s) = R_a(s) R_(conj a)(s) R_(a/2)(s) R_(conj a/2)(s)`.

## Proof

`R_b(1-s)=R_b(s)`, so `P_a(1-s)=P_a(s)`. Conjugation exchanges the factors indexed by `b` and `conj b`, hence `P_a(conj s)=conj(P_a(s))`. Direct factors give `P_a(a)=P_a(a/2)=0`.

Take `a = 3/4 + i`. Its eight roots have real parts `1/4`, `3/8`, `5/8`, or `3/4`, and nonzero imaginary parts. Thus `P_a` is entire, reflection- and conjugation-symmetric, has no real zero, has no zero outside the open critical strip, and has only isolated zeros, while retaining the strict-right half-affine collision `a` and `a/2`. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** no deduction from only those generic properties can exclude the half-affine collision needed for `physicalSelfSourceCoefficient q = 0`.
- **Strongest positive survivor:** any proof of HB-SS-NV must use a genuinely Xi-specific arithmetic/analytic invariant; `RHTower.D4BMJointSource.physicalSelfSourceCoefficient_zero_iff_xi` identifies the exact three affine inputs such an invariant must control.
- **New insight:** zero symmetry is compatible with the source-killing collision. The correct HB fork is therefore an arithmetic collision invariant or a new literal vector-to-radial receiver, not further symmetry manipulations or scalar normalization.
- **Status:** paper proof dependency-closed. The exact algebraic countermodel is formalized in `GaloisForLFunctions/RHTower/XiAffineCollisionSymmetryModelNoGo.lean`; its module build and axiom audit are recorded in the fact log.

## Log

- 2026-09-15 — symmetry-only route retired; positive survivor is Xi-specific collision control.
