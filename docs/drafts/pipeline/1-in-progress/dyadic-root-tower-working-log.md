# Dyadic root tower: working log

- **Scope:** facts and no-gos established or verified during this investigation
- **Status:** in progress; no RH proof
- **Updated:** 2026-09-13

## Facts

- `ZetaPoleHalfArithmeticLaplace` verifies the literal damped
  floor-cutoff source as the infinite sum of all arithmetic translates, including
  exact endpoint agreement. It proves whole-line integrability, the full transform
  `L(H)(s)=B(s+3)*L(D)(s)`, and square `zeta(s+3)*(s+2)/(s+3)^2` for `Re(s)>=0`.
  The transform is analytic on `Re(s)>0`. These are original-variable `Re(z)>=3`
  statements, not a larger root domain or a baseline bound. Targeted production
  build passed; all 18 public theorems have only `propext`, `Classical.choice`, and
  `Quot.sound` as axiom dependencies. Umbrella wired; default heartbeats.
- The same module proves `LSeriesSummable zetaBinomialHalf z iff 1<Re(z)` directly
  from the actual coefficient convolution square and zeta's convergence criterion.
  The complete weighted atom norm factors exactly into a Dirichlet coefficient norm
  and the weighted kernel norm. Both statements retain the full arithmetic family.

- Complete Gamma-source scratch constructs a real causal `g`, proves
  `g*g=exp(-t)*t*((1-t)^2+t^2/3)` almost everywhere on the positive ray,
  and proves that this square is strictly positive there, integrable, and tends to zero.
  It proves `exp(-2*t)*g` integrable but `exp(-3*t/4)*g` not integrable.
  The source is an explicit convolution of two conjugate Gamma-half filters;
  Fourier uniqueness verifies the square identity. The contradiction at the stronger
  weight uses a simple transform zero, not an assumed zero of zeta.
  Therefore positivity and decay of a full convolution square cannot alone establish
  the required source bound. The actual arithmetic coefficients remain outside this
  generic counterexample. See the [complete construction](../5-failed/positive-convolution-square-growth-bootstrap.md).
  The three production leaves passed targeted builds; every one of their 55 public
  theorems has only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies.
  Umbrellas wired; default heartbeats. Final lint has unrelated unreachable
  `RHTower.Sieve.KloostermanGlobalCollisionCoprime` and
  `RHTower.ThetaCuspHawkingBMOriginalHorizonRegularity`.

- `CausalGammaHalfLaplace` proves the normalized complex-rate Gamma-half integral,
  filter integrability, and the square-transform identity `(s+w)/(s+3)^2` for
  `Re(s)>=0`, `Re(w)>0`. Its targeted build passed. A separate scratch identifies
  the `w=2` filter with `exp(-3*t)*poleClearedHalfKernel(t)/Gamma(1/2)` and proves
  integrability and its Laplace square. This is the existing kernel, including the
  full primitive subtraction; the infinite arithmetic delayed sum is not yet identified.

- Direct inspection found `exists_zetaBinomialHalf_summatory_bound` assumes
  `ZetaBinomialHalfKatoInversion`. It does not supply an unconditional baseline bound.

- The complete cell-upper scratch proves
  `sum_(1<=N<M) N^(-sigma)*integral_cell abs(G-C_N)
   <=16*sum_(1<=N<M) b(N)*N^(-sigma-1/2)` for `sigma>=0`.
  It proves the weighted remainder-mass sequence summable for every `sigma>1/2`,
  bounded by `16*sum N^(-sigma-1/2)`. The proof uses positive increments,
  exact triangular finite-sum interchange, telescoping, and `0<=b(n)<=1`.
  No bound for the retained baseline, no root continuation, and no RH proof follows yet.
  `PoleHalfKernelCellOscillation` and `ZetaPoleHalfCellRemainder` passed both targeted
  builds; all 24 public theorems have only `propext`, `Classical.choice`, and `Quot.sound`
  as axiom dependencies. Umbrellas wired; default heartbeats. Lint still has the unrelated
  unreachable `RHTower.Sieve.KloostermanGlobalCollisionCoprime`.

- The cell-upper scratch verifies the exact decomposition of the literal causal source into
  its old-atom right-endpoint baseline and remainder. It proves the remainder's cell mass
  is at most `12*b(N)*sqrt(d_N)+2*sum_(n<N) b(n)/n * (q(log(N/n))-q(log((N+1)/n)))`,
  with `q(t)=t^(-1/2)`. Each old-atom difference is nonnegative and its later-cell sum
  telescopes. This is an upper bound for the remainder, not the complete source.

- `PoleClearedHalfKernel` verifies local integrability and exact derivatives of `r(t)=exp(t)*t^(-1/2)-integral_0^t exp(v)*v^(-1/2) dv`. Both `r` and `r(t)-t^(-1/2)` are strictly decreasing on the positive ray. The latter gives a reflected-cell absolute-mass bound for every nonnegative finite packet of delayed kernels, without a sign assumption on the packet values.
- `ZetaPoleHalfCausalSource` instantiates that law with the literal zeta-half coefficients and the full floor-cutoff causal source. On every prime cell of width `d=log(p+1)-log(p)`, its unnormalized absolute mass is at least `sqrt(d)/4`. The normalization to the Gamma-half kernel divides this bound by `sqrt(pi)`. The [causal-kernel card](dyadic-root-causal-kernel.md) distinguishes this checked lower bound from the still-unproved weighted upper bound needed for analytic roots. Both targeted builds passed; all 19 public theorems have only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies. Default heartbeats; no root domain gain.

- `PairedEtaRootContinuationBoundary` verifies the exact entire-factor identity `etaPair=C*zetaPoleUnit` on `Re(s)>0`, including `etaPair(1)=C(1)=log(2)`. Here `C=dslope (1-2^(1-s)) 1`; auxiliary zeros are retained, not silently cancelled inside separate roots.
- Its entire comparison `J_h(s)=dslope exp 0 (-h*(s-1))` satisfies `J_h->1` locally uniformly on all of `Complex`, and `J_h*zetaPoleUnit->zetaPoleUnit` locally uniformly. At `h=log(2)` the latter equals `etaPair/log(2)`. The comparison uses the already continued pole unit; it supplies no new root of that unit. Complete scratch proof passed with default heartbeats.

- `SquarefreeConvolutionHalfSourceMass` proves `norm(c(n)) <= norm(b(n))` for the actual Möbius and positive zeta halves, strictly at `n=4`, and proves the complete square-supported correction tail at `s=2/3` has absolute mass `A<1`.
- `SquarefreeConvolutionHalfHeatMass` proves for every `t>0` that the actual signed heat sum satisfies `norm(F(t)-B(t)) <= A*B(t)`, hence `Re F(t) >= (1-A)*B(t) -> +infinity` as `t->0+`. The proof retains the full correction, proves absolute summability before rearranging, and uses prime-coefficient divergence rather than Kato asymptotics or heat-gap interpolation.
- `PoleFactorTwoThirdsLowerBound` proves `norm(poleFactorSqrtApprox N (2/3)) >= 1/2` for every `N>=4`, from monotonicity of the binomial partial sums in their separate parity classes.

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
- `XiSymmetricZeroFreeCuspDyadicRoots.isOpen_firstTraceSymmetricZeroFreeCusp` and `isPreconnected_firstTraceSymmetricZeroFreeCusp` prove that the Euler chamber joined to the upper and lower classical zero-free cusps is one open preconnected region.
- `XiSymmetricZeroFreeCuspDyadicRoots.exists_xi_symmetricZeroFreeCusp_extension_of_farHalf_root_all_levels` proves unconditionally that every chosen Euler-side `2^k`-th root of actual completed `xi` extends, at every level `k`, to that same symmetric cusp and agrees with the Euler germ on all of `farHalf`.
- `XiSymmetricZeroFreeCuspDyadicRoots.exists_xi_symmetricZeroFreeCusp_arithmetic_extensions_all_levels` selects those extensions simultaneously level-by-level from the unconditional Euler roots. No coherence premise is used.
- `XiSymmetricLittlewoodZeroFreeCuspDyadicRoots` proves that a single unconditional constant `c > 0` supports actual analytic `2^k`-th roots of `xi`, for every `k`, on the same open preconnected conjugation-symmetric region with high left edge `max(1/2, 1 - c log log |t| / log |t|)`; each root agrees with its chosen Euler-side root on `farHalf`.
- `firstTraceZeroFreeCusp_strictlyContainedIn_littlewoodZeroFreeCusp` proves a genuine domain gain: above the explicit height `max(9, exp(exp(1/(10000c)+1)))`, the classical `1/(10000 log t)` cusp is properly contained in the Littlewood cusp.
- `DeckChargeCalculus.wCharge_eq_zero_iff` identifies the obstruction to a global analytic `n`-th root with the additive zero-order class in `ZMod n`; `exists_root_iff_wCharge_zero` identifies its vanishing with existence of the glued root. For `n = 2^k`, covering-lift monodromy is exactly zero multiplicity modulo `2^k`.
- `ArithmeticFiniteSourceContour.exists_lt_eventually_finiteCutoffZeta_displaced_zero_and_winding` proves that every sufficiently long literal finite head has, on an isolating circle around an actual zeta zero, logarithmic-derivative integral equal to that zero's full analytic multiplicity times `2*pi*I`. The nearby finite-head zero is displaced from the original zero.
- `ArithmeticFiniteZeroDisplacement.exists_finite_zero_displacement_coefficient` retains that same arbitrary multiplicity `m` as the exponent in the exact nonzero finite-zero displacement limit. `ArithmeticPrimeEnergyTransport.exists_cofinal_finite_zero_primeEnergy_transport` further proves that cofinal finite-head zeros converging to `rho` have normalized critical-line prime-energy floor `(rho.re - 1/2)^2`.
- `HedenmalmThetaSource.thetaSourceEntireDet2_eq_XiC_normalized` identifies a source-derived regularized determinant with normalized actual `XiC`; `analyticOrderAt_thetaSourceEntireDet2_eq_algebraicMultiplicity` identifies each local Xi order with the corresponding generalized-eigenspace dimension.
- `thetaQuantileReflection_anticommutes` gives `R B R = -B`. It pairs the nonzero source spectral points `mu` and `-mu` and preserves their algebraic multiplicities, but the points are distinct away from zero.
- `thetaKernelOperator_adjoint_ne_thetaKernelOperator` proves the actual source operator is not ordinarily self-adjoint. Its coordinate expectation has strictly negative imaginary part.
- `pinnedBoundaryCLM_exact_inertia` proves the Green boundary form has exact inertia `(1, 1)`, with explicit quadratic values `1/6` and `-1/6`. `thetaFredholmEigenmodesPinnedGreenIsotropic_iff_riemannHypothesis` proves that annihilating this form on every nonzero source eigenmode is exactly RH.
- `PolyaFrequencyIsTheHypothesis` explicitly corrects the Pólya-frequency shortcut: Schoenberg's characterization concerns the reciprocal bilateral Laplace transform of an integrable Pólya-frequency density, not real-rootedness of that density's Fourier transform. `xi_laguerrePolya_of_rh` constructs the Xi Laguerre--Pólya approximation only after assuming RH.
- `PrimeLogBlockCompression` retains prime count and first logarithmic moment in each `[k^4,(k+1)^4)` block. Its complete Euler-log discrepancy has bound `(240*norm(s)^2*exp(2*norm(s))+30)*k^(1-4*Re(s))`; the literal finite quotients converge to the holomorphic nonzero multiplier `quarticPrimeCompressionUnit` on `Re(s)>1/2`. This compares sources but supplies no continuation theorem for a root of either infinite Euler product.
- `XiPoleClearedFirstTraceRootReduction` removes the archimedean and higher-prime-power analytic units. Its remaining actual Euler half-germ is `exp((log(s-1)+coronaPrimeZeta(s))/2)`; extending it to `rightHalf` is exactly `RHLadder 1`, not an unconditional construction.
- **Earlier source audit, not a resumed route:** `SuzukiTaCovarianceSource.suzukiTaCovarianceDeficiency_shiftEquation` uses the literal shift `r=norm(B)+1>=1`. The paper's [Theorem AE](../3-formalized/new_scientific_knowledge/suzuki/suzuki-coalescing-anchor-parity-locking-reduction.md#1422-every-negative-shift-bounded-away-from-zero-is-asymptotically-free) states, under RH, defect convergence to zero for `inf r_j>0`; the actual Xi target is unconditionally in `(77/85,1)` by `SuzukiXiFirstDefectJet`. The cited `SuzukiExpandingFrameAnnihilation` and `SuzukiNegativeRecessionJensen` modules contain abstract ingredients, not the instantiated literal-covariance limit. The resulting source-identification obstruction remains paper-level, not a verified closed Lean no-go.

## No-gos

- Termwise absolute integration of the literal pole-cleared atom family cannot cross
  original `Re(z)=1`: integrability of every atom plus summability of their norm
  integrals forces `Re(z)>1`. The closed instance at `z=2/3` passes the production audit.
  The proof establishes nonzero kernel mass under integrability and does not infer
  convergence from a default zero integral. This rejects an absolute-value step;
  the [positive survivor](dyadic-root-causal-kernel.md#full-arithmetic-transform-and-absolute-integration-boundary)
  is the exact full-source transform, not retirement of the dyadic-root route.

- Taking a global analytic square root of the actual paired eta series on `rightHalf` is impossible: at `1+2*pi*i/log(2)` the series vanishes with derivative `log(2)*zeta(rho)!=0`, hence exact analytic order one. This zero is introduced by pairing, not by zeta. `not_exists_analytic_etaPair_squareRoot_rightHalf` and the [positive cancellation and dilation survivor](../5-failed/dyadic-root-paired-source-test.md) passed the complete scratch check and targeted production build; all 27 public theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The module is umbrella-wired; no heartbeat increases. This rejects separate factor-root extraction, not the actual dyadic-root route.

- `SquarefreeConvolutionHalfLaplaceAllClocksNoGo.not_exists_locallyBounded_squarefreeHalfLaplace_cofinal_twoClocks` closes the sparse-clock loophole for the **literal** normalized heat family: no positive heat clock tending to zero and no cofinal pole-degree clock yield local boundedness on `rightHalf`. No monotonicity, gap, or rate condition is imposed on heat time. The [complete source-mass card](../5-failed/dyadic-root-laplace-source-mass.md) retains the positive reserve theorem; this rejects the producer, not the analytic-root route. Four direct checks and four targeted builds passed with default heartbeats; all 20 public theorems have only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies.

- All-power divisibility is only the selection endpoint. Replacing roots by covering lifts or divisibility data does not construct the required global objects.
- Positive coefficient roots and Gamma-half/Karamata laws live in the Euler convergence chamber. By themselves they do not analytically continue a square root across `Re(s)=1` or control monodromy.
- Previously tested diagonal, dense, and transport-controlled Laplace heat regularizations cannot supply the first root rung; their local-boundedness premise contradicts the zeta pole.
- Proving Kato's ordinary coefficient asymptotic would strengthen the arithmetic description of the positive half, but would still not imply a global analytic root without a separate continuation/monodromy theorem.
- The harmonic-window asymptotic does not, by finite partial summation alone, imply `ZetaBinomialHalfKatoInversion`: its `o(√(log N))` error is larger than the endpoint cancellation scale `N/√(log N)`. Nonnegative mass may be redistributed inside bounded-width logarithmic shells without changing the harmonic asymptotic while changing endpoint-dominated ordinary sums.
- Local square-root germs along the zero-free line do not supply the required global square root: continuation can stop at zeros to the left of the line, and gluing around loops still requires trivial monodromy.
- Restricting to a simply connected zero-free subregion makes root construction automatic but removes hypothetical zeros from the receiver. On `rightHalf`, using nonvanishing or divisible winding as the root-construction premise restates the unresolved zero/multiplicity obstruction.
- Full boundary modulus, and therefore outer-factor data alone, cannot determine zero multiplicity or dyadic divisibility. The missing information is the inner factor, equivalently phase/winding/divisor data.
- Probability convolution and infinite-divisibility constructions cannot produce even the first analytic square root of normalized `XiC`. The obstruction is the actual odd-order Xi divisor, not lack of exponential moments or transform analyticity.
- The classical cusp tower does not imply RH: its left edge is `1 - 1/(10000 log |Im s|)` and retreats to `Re(s)=1`, so it omits the fixed-width region between the critical line and that edge. Root construction there succeeds precisely because prior zero-freeness removes all divisor monodromy.
- The strictly wider Littlewood cusp tower still does not imply RH: `c log log |t| / log |t| → 0`, so its left edge also retreats to `Re(s)=1`. Removing one logarithmic factor enlarges the actual-root domain but does not reach any fixed half-plane `Re(s)>σ` with `σ<1`.
- Ordinary exponentiated holonomy discards integer divisor charge: `exp (2*pi*I*m)=1` for every integer `m`. Passing to a `2^k`-root covering retains precisely `m mod 2^k`, so it repackages rather than proves dyadic divisibility.
- Literal finite-head convergence cannot supply dyadic parity: its isolating contour transports the actual zero multiplicity unchanged, and its displacement law is valid for every positive multiplicity. A parity conclusion requires an independent arithmetic restriction on finite-head winding or zero clusters.
- Generic determinant, Pfaffian, fermionic, and tau-function declarations found by corpus search do not identify an unconditional power with actual completed `xi`; proxy or modulus-square determinants cannot produce the required analytic roots.
- The actual source determinant does not gain local parity from functional-equation reflection: anticommutation pairs the distinct zeros `z` and `-z` with equal order, while a generic off-diagonal determinant `det(I + zB)` can have simple zeros. Fixed-point-free pairing constrains the global divisor but not either local order.
- Ordinary or weighted dissipativity cannot be inferred from the available theta Green identity. The ordinary operator has a proved nonzero adjoint defect, and the weighted boundary form is one hyperbolic plane rather than semidefinite. Reflected eigenmodes carry opposite boundary currents, so aggregate cancellation does not imply modewise neutrality.
- Positive theta-source density or a proposed Pólya-frequency property does not by itself locate the zeros of its Fourier transform. The relevant Schoenberg theorem applies to a reciprocal Laplace transform, and the corpus's actual Xi Laguerre--Pólya construction has RH as an input.
- Integer exponents in finite Euler products do not supply meromorphic continuation of their infinite root limit. An uncompleted meromorphic square root of zeta near `s=1` would require `2*ord(g)=-1`. Pole-clearing is a genuine survivor: `exists_local_normalized_analytic_sqrt_zetaPoleUnit` already constructs the normalized analytic square root near `1`; this local repair does not settle interior Xi monodromy. Both statements passed `lake env lean /tmp/rh-root-source-audit.XnUgKV/PoleCheck.lean`; both axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. This is a diagnostic using existing order lemmas, not a new production module or an RH advance.
- The geometric removability theorem found by the broad search does not remove a complex root's branch obstruction: [Antonelli–Székelyhidi, arXiv:2609.01464, Theorem 1.1](https://arxiv.org/html/2609.01464v1) assumes metric comparability and singular-set codimension strictly greater than `3-1/(n-1)`. At real dimension two that is strictly greater than two, so an isolated complex branch point is outside its hypotheses. No branch-descent conclusion is supplied.
- The recent iterated-extension theorem does not force an unramified root tower: [Barcau–Paşol, arXiv:2606.29310, Theorem 1.1 and Proposition 5.2](https://arxiv.org/html/2606.29310v1) allow deep ramification; collapse in the Frobenius-type case requires unramifiedness at every level. Substituting that premise for trivial complex root monodromy does not prove it.

## Open boundary

- Determine whether the pole and nonpole analytic germs extend through a connected zero-exclusion region with trivial square-root monodromy; otherwise isolate the exact zero or loop obstruction.
- Any claimed RH advance after that bridge must exhibit a source-derived mechanism that crosses `Re(s)=1` and trivializes root monodromy.
- Burnol/Sonin completeness can turn divisibility of a source Mellin transform by zeta into source vanishing, but the searched theorems do not construct a fractional zeta divisor or force zeta multiplicities to be even.
- Any transform-side dyadic-root producer must leave probability characteristic transforms; signed or complex measures remain possible only if they also supply global analytic continuation and trivial monodromy.
- A finite-source location attack must prove a source-derived `o(log^2 N)` upper bound for critical-line prime energy along cofinal finite-head zeros. The proved lower floor would then force `rho.re = 1/2`; without that independent upper bound, finite approximation only transports the unknown zero location.
- An operator-source attack must prove modewise vanishing of the single rank-two Green boundary current from arithmetic/source structure. Self-adjointness, semidefinite boundary form, and reflected-pair cancellation are all unavailable; universal modewise vanishing would force real source spectrum and hence RH.
