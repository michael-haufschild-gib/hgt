# Xi horizontal collision: Gauss--Hodge prime current

Status: in progress. RH not proved.

## Problem

Horizontal collision charge is quantized:

```text
O(T) = sum_gamma H_gamma^2 - sum_rho m_rho^2,
RH <-> forall T, O(T) < 2.
```

The density estimate `O(T)=o(N(T))` is insufficient: it permits one permanent reflected off-line
pair of charge two. Required input is absolute, not density-normalized.

## Heavy-conjecture loop

1. **Finite multiplicity-faithful Gauss--Hodge current.** Proved. Expanding each finite Xi packet
   into analytic-multiplicity copies gives a nonnegative prime current. Prime summability is
   equivalent to zero horizontal collision charge in that window.
2. **One full-divisor resolvent trace.** Proved. A positive resolvent-weighted Gauss--Hodge trace is
   prime-summable iff RH.
3. **Literal Gamma-six source identification.** Proved. The same trace is the Euler response of
   the two-orientation Gamma-six suspension determinant.
4. **Remove Euler differentiation.** Proved. Raw determinant curvature itself has a harmonic-prime
   lower quantum off line, is bounded above by Gauss--Hodge virial mass, and its positive
   full-divisor resolvent trace is prime-summable iff RH.
5. **Wold--Gauss virial producer.** Failed. Exact coefficient gauge grows at least linearly in the
   prime label, so Wold summability cannot pay the trace.
6. **Finite unit-double Euler negativity.** Failed. Completed kernel has positive zero-frequency
   local stiffness; finite negative type does not survive completion.
7. **Generating-parameter moment identity.** Failed. Existing prime--Archimedean source moments
   are unweighted Taylor moments; nonlinear horizontal coefficient requires critical boundary
   continuation.
8. **Gamma-six/Bockstein completion weld.** Proved at scalar scratch level and ported. At every
   prime and horizontal rate, raw even Gamma-six determinant curvature times the explicit positive
   two-orientation completion gauge equals the square of the odd fixed-first-trace Gamma
   Bockstein, with exact Gauss coefficient. On an actual retained Xi multiplicity copy, one
   vanishes iff the other does. Prime labels and both reflection orientations survive.

## Formal files

- `formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionGaussHodgePrimeCurrent.lean`
- wired by `formal/GaloisForLFunctions/RHTower.lean`
- scalar audit: `/tmp/hgt_bockstein_gamma_bridge.lean`

The scalar identity and its zero-equivalence pass `lake env lean` in scratch. Earlier dedicated
scratch for the derivative-free determinant endpoint passed before port. Direct target checking
subsequently encountered unrelated missing `.olean` artifacts from concurrent corpus changes; per
instruction no more dependency or project builds were run. One actual proof-body issue exposed
before that boundary (`tsum 0 = 0`) was fixed with explicit `tsum_zero`.

## Exact open producer

Prove unconditionally that the positive derivative-free Gamma-six suspension-determinant source
resolvent trace is prime-summable. By the new completion weld, an equivalent source-side target is
loss-zero landing of the same two orientations in one fixed trace-one ideal. Generic Frechet
nuclearity, shifted ideals, damping, `q>1` Schatten admission, determinant regularization, or
`o(N(T))` estimates cannot supply this endpoint.

