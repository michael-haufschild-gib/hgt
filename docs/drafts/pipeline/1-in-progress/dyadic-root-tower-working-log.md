# Dyadic root tower: working log

- **Scope:** facts and no-gos established or verified during this investigation
- **Status:** in progress; no RH proof
- **Updated:** 2026-09-12

## Facts

- `RHTower.nonvanishing_of_exists_roots_all_two_powers_preconnected` needs global analytic roots of every order `2^k` on one open preconnected region plus one nonzero anchor. Successive-root coherence is not used.
- `RHTower.rh_iff_exists_roots_all_two_powers` identifies the required global dyadic-root family on `rightHalf` as RH-equivalent. It is a receiver, not a root producer.
- `ZetaBinomialHalfKaramataLaw` proves the positive zeta-half Dirichlet mass has Gamma-half scaling after logarithmic rescaling and exponential compactification.
- `HTGeometry.WeightedPortmanteau` proves bounded continuous exponential tilting preserves weak convergence and transfers null-frontier set integrals.
- `ZetaBinomialHalfKaramataUntilt` proves unconditionally, for `0 ≤ x`,
  `√t * ∑' n, if t * log n ≤ x then b(n)/n else 0 → 2√x/√π` as `t → 0+`, where `b = zetaBinomialHalfReal`.
- Deep corpus search found `HTGeometry.sum_mul_weight_eq` as a reusable exact finite partial-summation identity. No searched declaration directly converts the new harmonic-window limit into the ordinary Kato summatory asymptotic.
- Kato, Theorem 3.1 (`arXiv:1406.0427`), assumes more than a real pole limit: `L^m` must continue meromorphically to an open neighborhood of the closed boundary half-plane and be holomorphic there except for the pole. For fractional order below one, the proof obtains a locally bounded-variation boundary remainder and Fourier decay.
- `ZetaBinomialHalfBoundaryGerm.exists_local_analytic_zetaBinomialHalf_extension_at_oneLine` proves unconditionally that at every `1 + iy`, `y ≠ 0`, the actual positive Dirichlet square root of zeta extends holomorphically across `Re(s)=1` on a zero-free disk and squares to zeta there. The sign is fixed by agreement at one point of the connected right-half-disk.
- `ZetaBinomialHalfBoundaryGerm.exists_local_normalized_analytic_sqrt_zetaPoleUnit` proves unconditionally that the entire pole unit `(s-1)·zeta(s)`, patched to value `1` at `s=1`, has an analytic square root `P` on a disk about `1`, normalized by `P(1)=1`.
- `ZetaBinomialHalfBoundaryGerm.normalized_analytic_sqrt_zetaPoleUnit_eq_cpow_mul_LSeries` identifies that normalized root with the actual positive Dirichlet branch: `P(s) = (s-1)^(1/2)·LSeries zetaBinomialHalf s` on the right-half overlap. The real-axis normalization excludes the negative square-root branch.
- `ZetaBinomialHalfBoundaryGerm.exists_local_zetaBinomialHalf_kato_remainder_factorization` proves the exact local identity `LSeries zetaBinomialHalf s / s - (s-1)^(-1/2) = (s-1)^(1/2)·H(s)` with `H` analytic near `s=1`.

## No-gos

- All-power divisibility is only the selection endpoint. Replacing roots by covering lifts or divisibility data does not construct the required global objects.
- Positive coefficient roots and Gamma-half/Karamata laws live in the Euler convergence chamber. By themselves they do not analytically continue a square root across `Re(s)=1` or control monodromy.
- Previously tested diagonal, dense, and transport-controlled Laplace heat regularizations cannot supply the first root rung; their local-boundedness premise contradicts the zeta pole.
- Proving Kato's ordinary coefficient asymptotic would strengthen the arithmetic description of the positive half, but would still not imply a global analytic root without a separate continuation/monodromy theorem.
- The harmonic-window asymptotic does not, by finite partial summation alone, imply `ZetaBinomialHalfKatoInversion`: its `o(√(log N))` error is larger than the endpoint cancellation scale `N/√(log N)`. Nonnegative mass may be redistributed inside bounded-width logarithmic shells without changing the harmonic asymptotic while changing endpoint-dominated ordinary sums.
- Local square-root germs along the zero-free line do not supply the required global square root: continuation can stop at zeros to the left of the line, and gluing around loops still requires trivial monodromy.

## Open boundary

- Prove from the pole factorization that the boundary remainder is a one-cusp profile with integrable one-sided derivatives, hence locally BV and square-root-weighted Fourier-decaying.
- Any claimed RH advance after that bridge must exhibit a source-derived mechanism that crosses `Re(s)=1` and trivializes root monodromy.
