# Every fixed theta-shell prefix has infinitely many nonreal zeros

- **Scope:** fixed canonical shell prefixes as real-zero foundations; not the full theta route.
- **Status:** complete scratch Lean proof; named leaf and axiom audit pending.
- **Provenance:** formalization of the existing paper argument in
  `../1-in-progress/k-rvm-finite-sixth-moment-bracket.md`, paragraph “Every fixed
  theta-shell prefix”. No new discovery or novelty claim.

## Exact statement

For any integer `N ≥ 1`, let

`P_N(x) = sum_(n=1)^N thetaCuspSourceTerm(x,n)` and
`F_N(z) = integral_(x>0) P_N(x) cos(z*x) dx`.

Then `F_N` is entire, has only finitely many real zeros, and has infinitely many
nonreal zeros. The statement uses the literal canonical source and holds for
every nonempty fixed cutoff. No numerical premise is used.

## Dependency-closed proof

1. The existing atom domination bound and first-atom envelope imply
   `0 ≤ P_N(x) ≤ K_N exp(-x³-x)` for `x>0`, with finite `K_N≥0`.
   The cubic bound follows from the first four terms of `exp(2x)` and `pi>3`.
2. For `t,x≥0`, `t*x-x³ ≤ (1+t)^(3/2)`: split at `x=sqrt(1+t)`.
   Thus all exponential source weights are integrable. The half-line Fourier
   transform and its reflected average are entire, and the average is exactly
   `F_N`. Integrating the envelope gives
   `|F_N(z)| ≤ exp(C_N (1+|z|)^(3/2))` for some `C_N≥0`.
3. Riemann–Lebesgue gives decay to zero on both real rays. The corpus's
   `zeroSet_infinite_of_subquadratic_twoRayDecay` therefore gives infinitely many
   complex zeros: finite-zero Hadamard factorization would leave a finite divisor
   times an exponential character, whose norms cannot decay on opposite rays.
4. The exact boundary identity gives `t² F_N(t) → -P_N'(0)<0`.
   Hence `F_N` has no real zeros outside a compact interval. It is nonzero, and
   holomorphic isolation gives only finitely many zeros in that interval.
   Removing these from the infinite zero set leaves infinitely many nonreal zeros.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/ThetaFiniteShellNonrealZeros.lean`:

- `thetaFiniteShellEntire_eq_integral`: exact source identification.
- `differentiable_thetaFiniteShellEntire`: entire transform.
- `thetaFiniteShellEntire_subquadratic`: source-derived growth envelope.
- `thetaFiniteShellEntire_zeroSet_infinite`: infinitely many complex zeros.
- `thetaFiniteShellEntire_real_zeroSet_finite`: finitely many real zeros.
- `thetaFiniteShellEntire_nonreal_zeroSet_infinite`: unconditional conclusion for `N+1` shells.

## Whole-route consequence and positive survivor

No fixed finite shell prefix can be an all-order real-zero foundation. Increasing
from one fixed cutoff to another cannot repair this mechanism. This strengthens
the verified scope beyond the previously numerical one- and two-shell failures.
It does not produce a particular negative Hankel polynomial or settle the
full-source Hankel sign.

**Positive survivor [Lean]:** the complete omitted tail restores exactly the
opposite leading Fourier boundary term at every cutoff:
`t² C_(Phi-P_N)(t) → P_N'(0)` while `t² C_Phi(t) → 0`.
See `ThetaFiniteShellFourierBoundary` and
`../3-formalized/theta-finite-shell-fourier-boundary.md`.
This survivor is already formalized. It identifies an essential infinite-source
cancellation; it supplies no sign for the remaining full-source transform.

The live producer must retain the complete arithmetic source or prove joint
cutoff/degree control. RH remains unresolved.
