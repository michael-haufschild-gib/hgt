# Discriminant Bulk Cross Sign Needs Scale Separation

- **ID:** discriminant-bulk-cross-sign-needs-scale-separation
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / route correction
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`;
  `y-plane-quartet-minor-imaginary-defect.md`;
  `fe-offline-quartet-shifted-minor-obstruction.md`
- **Statement:** In the Gram-Heine/discriminant expansion, a non-real atom with
  positive real part does not have positive cross term with every positive real
  bulk atom. Termwise bulk domination requires an additional scale-separation
  estimate.

## Setup

Let

`y=u+iv`, with `u>0` and `v!=0`,

be a non-real reciprocal atom, and let `x>0` be a positive real bulk atom.
The degree-one discriminant cross term between `y` and `x` contains

`R_x(y)=Re(y(y-x)^2)`.

The informal shortcut under audit is:

`u>0 => R_x(y)>0 for every x>0`.

## Theorem

The shortcut is false. In fact,

`R_x(u+iv)=x^2u-2xu^2+2xv^2+u^3-3uv^2`,

and at `x=u`,

`R_u(u+iv)=-uv^2<0`.

Thus positive real part of the off-axis atom does not imply positive
discriminant cross terms against all positive real atoms.

## Proof

Expand:

```text
(u+iv)(u-x+iv)^2
 = (u+iv)((u-x)^2-v^2+2i(u-x)v).
```

Taking the real part gives

```text
R_x(u+iv)
 = u((u-x)^2-v^2)-2(u-x)v^2
 = x^2u-2xu^2+2xv^2+u^3-3uv^2.
```

Substitute `x=u`:

```text
R_u(u+iv)=u(0-v^2)-0=-uv^2<0.
```

For a concrete instance, `y=1+i` and `x=1` gives

`Re((1+i)((1+i)-1)^2)=-1`.

This proves the claim.

## Consequence For The RH Route

The degree-one shifted determinant still has a useful discriminant expansion,
and isolated off-axis conjugate pairs still contribute the negative local term
recorded in `y-plane-quartet-minor-imaginary-defect.md`. However, the bridge
argument cannot promote

`det H_1=T_1T_3-T_2^2>0`

from the statement "`Re y>0`" plus termwise cross positivity. A valid proof of
degree-one positivity must supply one of:

1. a full summed inequality over the actual divisor;
2. a scale-separation theorem showing all relevant positive bulk atoms lie in a
   cross-positive range for every possible off-line atom;
3. a different source identity proving the determinant directly.

The verification-height heuristic may still be a useful finite-scale audit:
for a hypothetical off-line zero far above the verified range, its reciprocal
atom is much closer to `0` than the verified low zeros, and cross terms with
that low verified bulk are positive by scale separation. But that is not the
same as a global termwise proof.

## Source Boundary

This theorem does not disprove the degree-one shifted determinant positivity
claim for zeta. It removes an invalid termwise sign step from the claimed proof.
The route must either prove the missing summed domination estimate or downgrade
the degree-one statement to a checked/conditional mechanism.

## Gates

- [x] 0 -> 1 in-progress: discriminant cross-term sign assertion isolated.
- [x] 1 -> 2 fully-proven: exact algebraic counterexample written.
- [x] 2 -> 3 formalized: unconditional exact expansion
  `RHTower.discriminantCross_eq`, negative self-scale theorem
  `RHTower.discriminantCross_self_neg`, and explicit unit counterexample
  `RHTower.discriminantCross_one_one` in
  `formal/GaloisForLFunctions/RHTower/ReciprocalDiscriminantGuardrails.lean`;
  exact target build passed and the capstone audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Log

- 2026-06-24 -- Codex: created after auditing the embedded bridge-theorem claim
  that positive bulk cross terms make `det H_1` unconditionally positive. The
  local cross-term sign needs scale separation; `Re y>0` alone is insufficient.

## 2026-06-24 Exact Interval Follow-Up

`discriminant-cross-positive-interval.md` gives the exact replacement for the
invalid sign shortcut. For `y=u+iv`, `a=|v|`, `r=|y|`, the cross term is
positive for every positive real bulk atom `x>x_+(y)`, where

`x_+(y)=(u^2-a^2+ar)/u`,

and the sufficient uniform condition `x>=1.18|y|` implies positivity.

This narrows the repair obligation: a determinant proof may use termwise bulk
positivity only after proving that the relevant atoms lie outside the explicit
bad intervals, otherwise it must prove a summed domination estimate.

## 2026-06-24 Degree-One Summed Replacement

`degree-one-discriminant-tail-stability.md` records the summed version of the
repair. For a bulk/tail split `T_k=L_k+E_k`, the determinant perturbation is

`Delta-Delta_B=L_1E_3+L_3E_1-2L_2E_2+E_1E_3-E_2^2`.

Thus `det H_1>0` can be proved from a verified positive bulk only by bounding
this whole expression, not by citing pointwise cross positivity alone.
