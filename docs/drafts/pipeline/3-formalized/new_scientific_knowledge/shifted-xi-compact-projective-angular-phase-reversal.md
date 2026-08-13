# Shifted-Xi compact projective angular phase reversal

- **ID:** `shifted-xi-compact-projective-angular-phase-reversal`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM + NO-GO + POSITIVE SURVIVOR
- **Status:** `[LEAN-FORMALIZED] [UMBRELLA-WIRED] [CORPUS-NOVEL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** characteristic-apex projective Wronskian law, adjacent-degree no-common-root,
  positive finite Jacobi edges, and fixed-degree projective recession.

## Exact claim

For `A_n(y)=P_n(y,1/y)`, define the compact projective angular velocity

```text
Omega_n(y) = (A_(n+1) A_n' - A_n A_(n+1)') / (A_n^2 + A_(n+1)^2).
```

On every positive shifted-Xi block through degree `n+2`, `n>0`, `y>0`:

1. `A_n^2+A_(n+1)^2>0`, so `Omega_n` is pole-free.
2. At a numerator-axis contact `A_n=0`, `Omega_n=-2n<0`.
3. At a denominator-axis contact `A_(n+1)=0`,

   ```text
   Omega_n=-2(n+1) beta_(n+1)<0.
   ```

4. In a chart with `A_(n+1) != 0`,

   ```text
   Omega_n = R_n'/(1+R_n^2),  R_n=A_n/A_(n+1).
   ```

5. For fixed `n>0` on the square-mass ray,

   ```text
   w^4 Omega_n(w^2) -> 1/4 > 0.
   ```

Thus compactifying adjacent-degree poles does not produce a monotone projective phase: both chart
axes point backward while the far-right chamber points forward. Any successful Route-U invariant
must measure signed sector transitions, not only unwrap poles.

## Paper proof

Finite positive-block no-common-root excludes simultaneous vanishing of `A_n` and `A_(n+1)`.
Their squared norm is nonnegative and can be zero only under simultaneous vanishing, proving (1).

The pole-free Wronskian law is

```text
W_n = -2n A_(n+1)^2
      + ((2n+1)/y-(2n-1)alpha_n) A_n A_(n+1)
      - 2(n+1)beta_(n+1) A_n^2.
```

At `A_n=0`, no-common-root gives `A_(n+1)!=0`; division by its square yields (2). At
`A_(n+1)=0`, no-common-root gives `A_n!=0`; division by its square yields the identity in (3).
Finite Jacobi positivity gives `beta_(n+1)>0`, hence strict negativity.

Where `A_(n+1)!=0`, quotient differentiation gives

```text
R_n' = W_n/A_(n+1)^2,
1+R_n^2 = (A_(n+1)^2+A_n^2)/A_(n+1)^2,
```

which proves (4). Put `r_n(w)=R_n(w^2)/w^2` and `d_n(w)=R_n'(w^2)`. Previously formalized
source recession gives `r_n -> 4` and `d_n -> 4`. Therefore

```text
w^4 Omega_n(w^2)
 = d_n(w) / (w^(-4)+r_n(w)^2)
 -> 4/(0+16)=1/4,
```

proving (5).

## Hostile audit and survivor

- **Conjecture:** pole compactification absorbs chart resets and makes the lifted phase monotone.
- **Verdict:** `[FALSIFIED]` for the literal shifted-Xi trajectory. Compact angular velocity has
  opposite signs at infinity and at both coordinate axes.
- **Positive survivor:** `[LEAN-FORMALIZED]` exact pole-free angular velocity and its three-sector sign classification.
  It supplies the local density for a signed transition action and identifies what that action must
  charge.

## Revised open core

Construct a continuous projective phase lift or signed variation whose derivative is `Omega_n`,
count its forward/backward sector transitions on the cofinal parabolic frontier, and bound that
variation by the existing source-specific hyperbolic-reset/arithmetic surplus. Local monotonicity
is impossible; cancellation or a quantized winding deficit is required.

## Lean formalization

Module:

```text
formal/GaloisForLFunctions/RHTower/
XiShiftedCanonicalAdmissionCharacteristicApexCompactAngularPhaseReversal.lean
```

Lean formalizes all five items in the exact claim, including strict finite-block denominator
positivity, exact negative values at both projective coordinate axes, chart identification with
`R_n'/(1+R_n^2)`, the scaled limit `1/4`, and eventual strict positivity of the literal angular
velocity.

The module is imported by `GaloisForLFunctions.RHTower`. Direct `lake env lean` passes cleanly.
Targeted
`lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexCompactAngularPhaseReversal`
passes `12014/12014`. All eight public theorem audits depend only on
`[propext, Classical.choice, Quot.sound]`; forbidden-declaration scan is clean. Authoritative lint
reaches this module and reports only unrelated unwired modules elsewhere in the dirty worktree.

