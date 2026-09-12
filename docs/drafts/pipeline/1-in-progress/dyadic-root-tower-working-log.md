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
- `HTGeometry.intervalIntegrable_verticalCpow_negHalf` proves `(it)^(-1/2)` is interval-integrable on every finite real interval. `HTGeometry.tendsto_sqrt_mul_norm_intervalIntegral_verticalCpowCusp` upgrades any analytic-factor cusp `(it)^(1/2)H(1+it)` to square-root-weighted localized Fourier decay.
- `ZetaBinomialHalfBoundaryGerm.exists_zetaBinomialHalf_kato_boundary_fourier_decay` instantiates that cusp theorem with the actual zeta half-Dirichlet remainder. Thus the pole boundary germ at `s=1` has the local Fourier decay required by the fractional Kato mechanism.
- `WeldTowerLimit.xi_coherentTower_iff_zeroFree_halfPlane` proves for every real `σ` that a coherent dyadic tower for `xi` on `Re(s)>σ` is equivalent to zero-freeness there. At `σ=1/2` this is exactly RH; at `σ=1` the tower exists unconditionally.
- Corpus constructors `exists_analyticOnNhd_pow_eq` and `exists_analyticOnNhd_pow_eq_of_lift` give global analytic roots from, respectively, simple connectivity plus nonvanishing or connectedness plus divisible loop winding.
- `HTGeometry.circleBoundaryModulus_blind_to_monomial_zero_order` proves that the entire functions `z ↦ z^m` have identical unit-circle modulus for all `m`, while their zero orders at the origin are exactly the arbitrary values `m`. The existential corollary gives two entire functions with the same full boundary modulus and different zero orders.
- `ThetaTiltXiInfiniteDivisibilityNoGo.not_exists_probability_convPow_two_thetaTiltProb_zero` proves unconditionally that the central theta probability `thetaTiltProb 0` is not a convolution square of any probability measure. Its characteristic function is normalized `XiC`; endpoint exponential moments would make a hypothetical root transform analytic on `|Im z|<1`, where the identity theorem and Hardy's odd-order Xi zero contradict the even order of an analytic square.
- `ThetaTiltXiInfiniteDivisibilityNoGo.not_infinitelyDivisible_thetaTiltProb_zero` strengthens this to failure of probability infinite divisibility.

## No-gos

- All-power divisibility is only the selection endpoint. Replacing roots by covering lifts or divisibility data does not construct the required global objects.
- Positive coefficient roots and Gamma-half/Karamata laws live in the Euler convergence chamber. By themselves they do not analytically continue a square root across `Re(s)=1` or control monodromy.
- Previously tested diagonal, dense, and transport-controlled Laplace heat regularizations cannot supply the first root rung; their local-boundedness premise contradicts the zeta pole.
- Proving Kato's ordinary coefficient asymptotic would strengthen the arithmetic description of the positive half, but would still not imply a global analytic root without a separate continuation/monodromy theorem.
- The harmonic-window asymptotic does not, by finite partial summation alone, imply `ZetaBinomialHalfKatoInversion`: its `o(√(log N))` error is larger than the endpoint cancellation scale `N/√(log N)`. Nonnegative mass may be redistributed inside bounded-width logarithmic shells without changing the harmonic asymptotic while changing endpoint-dominated ordinary sums.
- Local square-root germs along the zero-free line do not supply the required global square root: continuation can stop at zeros to the left of the line, and gluing around loops still requires trivial monodromy.
- Restricting to a simply connected zero-free subregion makes root construction automatic but removes hypothetical zeros from the receiver. On `rightHalf`, using nonvanishing or divisible winding as the root-construction premise restates the unresolved zero/multiplicity obstruction.
- Full boundary modulus, and therefore outer-factor data alone, cannot determine zero multiplicity or dyadic divisibility. The missing information is the inner factor, equivalently phase/winding/divisor data.
- Probability convolution and infinite-divisibility constructions cannot produce even the first analytic square root of normalized `XiC`. The obstruction is the actual odd-order Xi divisor, not lack of exponential moments or transform analyticity.

## Open boundary

- Determine whether the pole and nonpole analytic germs extend through a connected zero-exclusion region with trivial square-root monodromy; otherwise isolate the exact zero or loop obstruction.
- Any claimed RH advance after that bridge must exhibit a source-derived mechanism that crosses `Re(s)=1` and trivializes root monodromy.
- Burnol/Sonin completeness can turn divisibility of a source Mellin transform by zeta into source vanishing, but the searched theorems do not construct a fractional zeta divisor or force zeta multiplicities to be even.
- Any transform-side dyadic-root producer must leave probability characteristic transforms; signed or complex measures remain possible only if they also supply global analytic continuation and trivial monodromy.
