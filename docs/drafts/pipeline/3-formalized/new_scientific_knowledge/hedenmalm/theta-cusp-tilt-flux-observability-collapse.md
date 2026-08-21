# TTF and Euler-safe observability are the same source order law

Status: Lean-formalized, unconditional route compression. `[CORPUS-NEW SYNTHESIS]`. Does not
prove RH.

## Exact coefficient weld

Let `a > 1/2`, let all packet nodes satisfy `Re(w_j) > a`, and define the diagonal coefficient
change

```text
d_j = c_j * xiCent(w_j).
```

The safe zero-free theorem makes this change invertible. Lean proves the exact identity

```text
eulerSafeDeficit(a,d,w)
  = π * sum_{j,k} c_j * conj(c_k)
      * sourceBezoutian(thetaCuspTiltSource,w_j,w_k).
```

For any claimed neutral derivative `D` of the literal theta tilt correlation, uniqueness of the
already-formalized derivative gives

```text
Re(eulerSafeDeficit(a,d,w)) = π * D.
```

Consequently, on every safe half-plane, Lean proves a coefficient-bijective equivalence between

```text
universal nonnegativity of all literal theta-source flux packets
```

and

```text
universal nonnegativity of all Euler-safe observability deficits.
```

## New route information

Tilt-flux and Cauchy-loss observability are not independent final producers. They are two exact
coordinate realizations of the same multi-node quadratic law. Combined with the existing
Hedenmalm rank-one collapse, this has three consequences:

1. the one-node sector is already unconditionally nonnegative;
2. local source shape and scalar Carathéodory positivity cannot supply the missing implication;
3. all RH-bearing content is the source-specific cross-node incidence needed to dominate the
   unshifted Cauchy loss.

This also explains the earlier stalls at a higher level: safe half-plane arguments prove a shifted
positive kernel, but passing to the critical kernel subtracts a positive Cauchy Gram term. Scalar
subunit bounds do not control the off-diagonal subtraction. The required theorem must retain the
literal theta/Euler correlation between different nodes.

## Positive survivor and next conjecture

The survivor is an explicit source inequality, not another abstract positive-kernel argument:

```text
0 <= Re(eulerSafeDeficit(a,d,w))
```

for every finite safe packet, proved from the literal theta/Euler source while retaining cross-node
incidence. Through the exact coefficient weld, this is simultaneously the missing TTF packet-flux
theorem. Generic diagonal contraction and generic two-node positive-real models are already ruled
out by the corpus; the next attack must exploit a theta-specific cross-node factorization,
sum-of-squares law, or cancellation invariant.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxObservabilityWeld.lean`

Closed declarations:

```text
sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel
eulerSafeDeficit_rescaledXi_eq_pi_mul_thetaCuspTiltSource_flux
eulerSafeDeficit_rescaledXi_re_eq_pi_mul_tiltCorrelation_deriv
thetaCuspTiltSource_flux_nonneg_iff_eulerSafeDeficit_nonneg
```

Verification:

- direct source check passed with `lake env lean`;
- exact target build passed with
  `lake build GaloisForLFunctions.RHTower.ThetaCuspTiltFluxObservabilityWeld`;
- no umbrella/full build was run;
- all four `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`;
- module is wired into `RHTower.lean`.

## Log

- 2026-08-21 — exact TTF/CLG coefficient equivalence formalized; route pivoted to the common
  source-specific cross-node observability inequality.
