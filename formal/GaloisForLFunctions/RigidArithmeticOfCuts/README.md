# Rigid Arithmetic of Cuts (RAC)

Namespace `GaloisForLFunctions.RigidArithmeticOfCuts`; umbrella `RigidArithmeticOfCuts.lean`; 28 modules.
Every theorem is unconditional. RH and zero-free regions appear only inside implications and equivalences.

## 1. Motivation

Suppose positivity, Weil positivity and spectral methods are all excluded. Inner-function theory loses its core, since a Blaschke
mass is a positive quantity and a passive medium is a positive form. Stepanov over `ℤ`, as a linear stencil theory, has closed:
the rate of a producer is the Mertens level. What remains has to be nonlinear in the primes.

RAC asks how an exact statement about one object, `N(x) = ⌊x⌋`, constrains its zeros by operations that have no sign and are not
linear floor identities. Three facts set the scene.

- All multiplicity of a stencil lives in fractional parts: `g(r) = −Σ c(k) {r/k}`.
- Every integer is a cut. Over `𝔽_q[T]` norms are quantized and a stencil is cut only at a degree boundary.
- The object is single. Within FE defect `1/6400` there is nothing else, so no deformation theory exists near it.

So the theorems of the field concern one function, and the exact system of relations it satisfies. The field succeeds in one of two
ways: a contradiction between an off-line zero and `⌊x⌋`, or a proof that a stated class of arithmetic information cannot give one.
The modules here do the second for every class they name, and isolate what is left.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Sawtooth, cut identity | `sum_Icc_mul_mod` | `Σ_{r ≤ kJ} U(r) (r mod k) = Σ_{r ≤ kJ} T(r) − k Σ_{j ≤ J} T(kj)` for `U(r) = T(r) − T(r+1)` |
| Fake prime measure | `IsFakePrimeMeasure` | `u ≥ 0` with `Σ_j u(j) ((j+1) mod k) = log k` for `k ≤ K` |
| Tail | `cutTail` | `T(r) = Σ_{j ≥ r} u(j)`, the scaling image of `ψ(n/r)/n` |
| Cut defect, kernel | `cutDefect`, `IsCutKernel`, `cutDefectC` | tails invisible to every balanced stencil |
| Zero mode | `sawStencil`, `abelStep` | the tail `r^{-s}` read by the sawtooth |
| Hecke action | `IsCutKernel.dilate`, `heckeOp` | `T ↦ T(j ·)` on the kernel |
| Curve kernel | `tailPairing`, `IsCurveKernel`, `curveKernel` | tails annihilating the ideal of the numerator `P` |
| Pure kernel | `traceNumerator`, `IsPureKernel` | genus one: every power-law kernel vector has decay `q^{-r/2}` |
| Carry | `floor_mul_sub_mul_floor`, `HasFrobenius` | the Frobenius defect `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋` |
| Ledger | `ledger`, `conv`, `selbergWeight` | `Σ_d a(d) g(⌊x/d⌋)` and its convolution readings |
| Symbol hierarchy | `vonMangoldtSymbol`, `ledgerSymbol` | `A = −ζ′/ζ`, `ζ A^k` |
| Twin and filters | `twinWeight`, `filteredTwin`, `IsEvenFilter`, `levelFilter` | `−λΛ = Λ − 2Λ1_{Ω even}`; `Λ − 2b`, `0 ≤ b ≤ Λ1_{Ω even}` |
| Harmonic mass | `harmonicMass`, `primeSquareMass`, `levelConstant` | `Σ_{e≤N} b(e)/e`; `κ = −ζ′/ζ(2)`; the mass above a level |
| Parity ledger | `liouvilleR`, `parityLedger`, `squareMertens`, `twistPoly` | `L(x)`, `Σ c(k) λ(k) L(⌊x/k⌋)`, `Σ_{d ≤ √x} M(x/d²)`, `D_{cλ}` |
| Return sets | `primeReturnSet`, `zetaReturnSet`, `exponentBox`, `boxDensity` | Bohr sets of finite prime families; returns of `ζ` on a compact set |
| Gauge torus | `IsGaugePoint` | unitary completely multiplicative `ω` |
| Beurling distances | `HasEventuallyExactCount`, `exchangeCount`, `exchangeFactor`, `numerator`, `stencilDefect` | count, Hamming, FE defect |
| Maximal-angle zero | `squaredXi`, `zeroSq`, `zeroSlope`, `sqFactor` | `Q(z²) = Ξ(z)`; zeros `w = α²` in the sector `|arg w| ≤ π/3`, positive iff RH |

## 3. Language

- **Cut.** A point where a floor jumps. **Multiplicity against size.** The count of a cut against the size of the integer it builds.
- **Carry.** The failure of `⌊·⌋` to be self-similar.
- **Blind.** A functional is blind at `ρ` when its generating function has no pole at `ρ`.
- **Exact.** A functional is exact when its value is determined by `⌊x⌋` alone.
- **Fake.** A measure consistent with the cut system at some level. **Tight.** Dominated by one summable sequence.
- **Kernel vector.** A tail invisible to every balanced stencil. **Pure kernel.** All modes at the critical decay.
- **Filter.** A twin that changes only chosen even prime powers. **Harmonic mass.** What a quadratic reading sees of a filter.
- **Oscillation, annihilator.** A finite oscillation `x^β T(log x)` in `ψ − x`, and a dilation combination that kills it.
- **Head and tail.** A finite Dirichlet part and its remainder.
- **Transport.** Copying a zero to a new height by a return, through minimum modulus.
- **Isolation.** A positive lower bound for the distance from `ζ` to every other system.
- **Extremal position.** A statement at the zero of maximal angle, used in place of a sign.

## 4. Mechanisms

1. **Exact identities.** The cut identity; Liouville's `Σ_k L(x/k) = ⌊√x⌋` (`floorSum_liouvilleR`); Selberg's
   `(Λ log + Λ∗Λ) ∗ 1 = log²` (`sum_divisors_selbergWeight`).
2. **No uniform measure on `ℕ`.** A finite measure with `W(kℕ) = S/k` for all `k` vanishes, by the Euler product at the edge
   (`eq_zero_of_uniform_multiples`). This one fact drives uniqueness of the fake.
3. **Rigidity as uniqueness.** One fake at infinite level (`eq_pronic_of_forall_isFakePrimeMeasure`); one system with an exact
   count (`nonempty_label_equiv_primes`); one system of small FE defect (`beurlingSystem_rigidity_of_small_critical_line_defect`).
4. **Extremal-factor modulus.** With `u = w₀/w`, `‖1 − tu‖² − ‖1 − t̄u‖² = 4 Im t Im u` (`rotated_factor_norm_sq_sub`). At the
   maximal-angle zero every Hadamard factor points the same way (`norm_squaredXi_conj_lt`), and the first order at the boundary
   zero is a Stieltjes sign (`im_stieltjes_nonpos`).
5. **Transport by minimum modulus.** A holomorphic function smaller at a centre than on a circle has a zero in the disc
   (`exists_zero_of_norm_center_lt`). It moves zeros of Dirichlet polynomials in every window (`exists_zero_in_every_window`).
6. **Gamma speed as dominance.** The Gamma speed `½ log(|τ|/2π)` beats a finite Euler speed above a horizon, so finite carriers are
   real there (`re_carrier_speed_ge`, in ZeroConfigurationGeometry).
7. **Nonlinear ledgers.** `ζ A^k` has order `m − k` at a zero of order `m` (`meromorphicOrderAt_ledgerSymbol`), so nonlinear pieces see
   zeros. Convolution moves the twin gap from `√N` to `N`, with the exact constant (`tendsto_selberg_twin_gap`).
8. **Effective Kronecker.** Integrality gives `|log a − log b| ≥ 1/Q` (`one_div_le_abs_log_sub_log`). On the divisors of `R^D` a
   nonnegative separated trigonometric density gives a return at explicit height (`exists_height_phase_return`).
9. **Exchange.** The count law `|Σ w_i ⌊x/m_i⌋ − x Σ w_i/m_i| ≤ x^σ Σ |w_i| m_i^{-σ}` (`abs_tsum_mul_floor_sub_le`) and the Hamming law: an
   exchange of summable exponent `σ` is a holomorphic zero-free factor on `Re s > σ` (`zeta_mul_exchangeFactor_eq_exp`).
10. **Bohr coefficients on the line.** `T⁻¹ ∫_0^T ζ(½+it) n^{it} dt → n^{-½}`, by Cauchy from `¾` with the convexity bound on the
    horizontal sides (`tendsto_critical_average_log`).

## 5. Questions and their answers

**Q1. What replaces Frobenius?** Nothing removes the sawtooth over `ℤ`, and this is a theorem. The Frobenius defect of `⌊·⌋` is the carry
`⌊k{x}⌋`, which is never constant for `k ≥ 2` (`not_exists_constant_carry`) and is the sum of the shifts `⌊x + j/k⌋ − ⌊x⌋`
(`carry_eq_sum_shifts`). A count with `N(kx) = kN(x) + C` has support in finitely many geometric progressions, with `a(kn) = k a(n)`
(`exists_pow_mul_of_ne_zero`, `card_support_le`), so bounded multiplicities admit no Frobenius (`not_hasFrobenius_of_bounded`). A
stencil cuts a proportion at least `φ(L)/L` of the integers (`totient_le_card_cuts`). Over a curve the kernel is one linear recurrence, of
rank `deg P` (`isCurveKernel_iff_isSolution`, `rank_curveKernel`), and `P = 1` leaves no kernel (`eq_zero_of_isCurveKernel_one`). Over `ℤ`, the
kernel carries a Hecke action instead of a recurrence, and a finite invariant subspace contains a completely multiplicative vector
(`exists_mul_of_hecke_invariant`).

**Q2. What nonlinear functional of `Λ` sees a zero mode and survives the twin?** `ζ A^k` has order `m − k` at a zero of order `m`: only `k = 1` is
blind (`blind_of_linear`, `sees_of_lt`), and at a simple zero `(s − ρ)^k ζ A^{k+1} → (−1)^{k+1} ζ′(ρ)` (`tendsto_mul_ledgerSymbol`). No piece of
this kind is exact: the exact combination `ζ(A² − A′) = ζ″` is blind again (`riemannZeta_mul_selberg`). For the twin, the Selberg ledger is exact on `Λ`
(`ledger_selbergWeight`), and uniformly over filters

`ledger(Selberg Λ, N) − ledger(Selberg (Λ − 2b), N) = 4 L N Σ_{e ≤ N} b(e)/e + O(N^{3/4})` (`exists_abs_selberg_gap_sub_le`).

So the ledger survives the twin, with exact rate `4 L (−ζ′/ζ(2))` (`tendsto_selberg_twin_gap`). A twin agreeing with `Λ` up to any level is still
seen at scale `N` (`tendsto_selberg_level_gap`, `levelConstant_pos`), against a linear ledger bound `2 w ψ(√N)` (`IsProducer.abs_ledger_twin_le`). The
constant dies with the level (`tendsto_levelConstant`). What the separation reads is a value at `s = 2`, so it passes the twin and does not break parity.

**Q3. Why do primes recur at a zero, if they do?** The primes always recur: every finite family returns on a set of positive lower density
(`exists_density_primeReturnSet`), at explicit height and in every window (`exists_height_phase_return_window`). Above the abscissa that is
enough, since a return of the primes up to a length is a return of `ζ` on the whole half-plane (`primeReturnSet_subset_zetaReturnSet`). At a zero
it is never enough. At a positive proportion of heights all primes of any finite family return and `ζ` does not
(`exists_primeReturn_not_zetaReturn`). A Dirichlet polynomial has no tail and its zeros recur in every window
(`exists_zero_in_every_window`). A bounded return must be a return of every prime (`tendsto_phaseDefect_zero`). So the tail is exactly what fails, and
this holds for every length. The limit map itself is onto the gauge torus (`exists_tendsto_translate`), and the twin `ζ(2s)/ζ(s)` is a limit of
translates of `ζ` on `Re s > 1` (`exists_tendsto_translate_twin`), so recurrence cannot see parity.

**Q4. Is a single off-line zero a contradiction with `N(x) = ⌊x⌋`?** Not by anything below. The zeros are the power-law kernel of the cut system on
`Re s > 0` (`forall_hasSum_abelStep_mod_zero_iff`), and a finite combination of modes in the kernel consists of zeros
(`riemannZeta_eq_zero_of_finite_kernel`).

| Class of information | What it gives | Theorem |
|---|---|---|
| Exact linear ledgers | blind at every zero | `hasSum_ledgerMode_eq_zero` |
| Exact nonlinear ledgers | blind again | `riemannZeta_mul_selberg` |
| Order in the cut system | reaches the edge only: `ζ ≠ 0` on `Re s ≥ 1` and on the real segment | `riemannZeta_ne_zero_of_one_le_re_of_cut`, `riemannZeta_ne_zero_of_real` |
| Finite prime recurrence | never controls the tail at a zero | `exists_primeReturn_not_zetaReturn` |
| Limits of translates | contain the twin | `exists_tendsto_translate_twin` |
| Adding generators | adds no zero right of the count exponent | `numerator_eq_zero_iff` |
| Exchange of summable exponent `σ` | a holomorphic zero-free factor on `Re s > σ`, so no new zero there | `differentiableOn_exchangeLog`, `exchange_eq_zero_iff` |
| A power bound on the parity ledger | confines zeros to zeros of a twist; for `L` itself, a zero-free strip | `twistPoly_eq_zero_of_parity_bound`, `riemannZeta_ne_zero_of_liouville_bound` |

The last row is the arithmetic input the question asks for. A bound on `L` is a statement of the depth of the conclusion, and it has no source.

**Q5. What is the fake prime measure closest to the true one, for each `K`?** At infinite level there is one fake, the pronic measure
`1/((j+1)(j+2))` (`eq_pronic_of_forall_isFakePrimeMeasure`, `forall_isFakePrimeMeasure_iff`). Tight fakes of levels tending to infinity converge to it
pointwise (`tendsto_pronic_of_tight`). So no extremal family has a limit other than `dy/y²` read on integer cells. At finite level, translating
an atom by a common period keeps all moments (`isFakePrimeMeasure_translate`), so there is no lower radius without a condition at infinity. The upper radius
is the rate (`TheDualOfTheRateIsAFakePrimeMeasure`).

**Q6. Is there an arithmetic rotated identity with balanced coefficients nonzero at the zeros of `ξ`?** Not with polynomial coefficients
(`squaredXi_no_polynomial_rotation`), by the Turán log-concavity of the Taylor coefficients. A rotated relation with balanced coefficients nonzero at
the zeros implies RH (`riemannHypothesis_of_balanced_relation`), and equal rotated modulus at all zeros is RH (`riemannHypothesis_iff_forall_norm_eq`).
Unrestricted coefficients are vacuous, even normalized at the origin (`exists_normalized_entire_vacuous_rotated_relation`).

## 6. Tools

| Tool | State | Lean |
|---|---|---|
| Ledgers that are not blind | built: orders, residues, exact twin gap, filter law | `TheHierarchyOfLedgers`, `TheSelbergLedgerSeparatesTheTwin`, `TheQuadraticGapIsTheHarmonicMass` |
| Parity input | built: the exact identity, its bound by the Mertens level, the confinement theorem; no source for the bound | `TheLiouvilleChebyshevIdentity`, `AParityBoundConfinesTheZeros` |
| Effective Kronecker | built: explicit threshold `4(D+1) R^{2D+1}`, every window, positive density | `EffectiveKroneckerAtArithmeticScale`, `ZerosOfADirichletPolynomialRecurEffectively`, `TheTailFailsAtAZero` |
| Pointwise bounds below VK | left endpoint built: no cancellation for `p ≤ y` at some height `T ≥ 4(D+1) 4^{(2D+1)y}`; the range up to VK is open | `TheShortSumBarrierHasALeftEndpoint` |
| Metric geometry of Beurling systems | built: exact count rigidity, count law, Hamming law, generators add no zeros, stencils at infinite FE distance | `AnExactCountForcesTheRationalPrimes`, `TheExchangeLaw`, `AddingGeneratorsAddsNoZeros`, `StencilSystemsHaveInfiniteDefect` |
| Extremal calculus | built: max angle attained, Hermite–Biehler modulus, Stieltjes sign, no polynomial rotation | `TheZeroOfMaximalAngle`, `TheStieltjesSignOfTheExtremalZero`, `TheSquaredXiHasNoPolynomialRotation` |
| Kernel calculus | built: `ℤ` and curves, in one language | `ZerosAreTheKernelOfTheCutSystem`, `ACutVectorWithAMonotoneTailVanishes`, `TheCutSystemOverACurve` |

Still to build: a source for a power bound on the parity ledger; a functional that separates a twin at a level growing with `N`; pointwise bounds in the
range `log T ≲ y ≲ exp((log T)^{2/3})`.

## 7. Test cases

| Test | Outcome | Theorem |
|---|---|---|
| `𝔽_q[T]` | zero kernel: `P = 1` | `eq_zero_of_isCurveKernel_one` |
| Weil for split hyperelliptic curves | kernel modes of exact decay `q^{-r/2}`, by Stepanov | `isCurveKernel_lRoots_of_stepanov` |
| Genus one | kernel pure iff `t² ≤ 4q` | `isPureKernel_iff` |
| Kloosterman data | pure, with Weil's `2√p` as input; the stencil window `|K| ≤ p + 1` does not reach it | `isPureKernel_kloosterman`, `traceNumerator_kloosterman` |
| Carlitz stencil | a stencil is cut only at a degree boundary, rate `0` | `carlitzOrder_sub` |
| Golden fake | exact transport, impure kernel, fails the count | `golden_battery`, `golden_deep_mode` |
| Continuous Beurling systems | no multiplicity, no carry | `continuous_multiplicity_eq_zero` |
| Liouville twin | linear ledgers within `2 w ψ(√N)`; Selberg gap of exact order `N` | `IsProducer.abs_ledger_twin_le`, `tendsto_selberg_twin_gap` |
| Level filters | seen at scale `N`, constant tending to `0` | `tendsto_selberg_level_gap`, `tendsto_levelConstant` |

## 8. Traps

| Trap | Fact |
|---|---|
| A stencil identity sees a zero | Every exact ledger is holomorphic at every zero |
| A functional that sees a zero is a new input | The pieces `ζ A^k` have no exact value, and their exact combination is blind |
| Selberg's identity excludes a zero | It holds for every analytic function in the form `f(A² − A′) = f″` |
| The Selberg twin gap breaks parity | The gap is `4 L (−ζ′/ζ(2)) N`: a value at `s = 2`, read from prime squares |
| A filter of `Λ` is the parity problem | `−λΛ` differs from `Λ` only on even prime powers, so a ledger of `Λ` reads only those. Sieve parity concerns `λ` on all integers |
| A return of the primes is a return of `ζ` | True above the abscissa, false at a zero, at every length |
| The Dirichlet model is `ζ` with a small error | Its zeros recur in every window; returns at a zero of `ζ` are rare |
| Transport proves purity | The golden fake returns exactly and is impure |
| Mean values see off-line zeros | The Bohr mean of `ζ` against `n^{it}` is `n^{-σ}` on every line `½ ≤ σ < 1`, with no term from any zero |
| Integer norms exclude fakes | Integer systems with count `x + O(x^σ)` exist for every `σ > 0` (`exists_abs_exchangeCount_sub_le`). Only an exact count forces the primes |
| Count distance and FE distance agree | A nonconstant stencil has bounded count error and `T⁻¹ ∫_0^T |D| ↛ 0` (`eq_zero_of_defect_sublinear`) |
| Adding primes can create a zero | Right of the count exponent it never does (`numerator_eq_zero_iff`). Only deletion can |
| A fake of level `K` has mass in a window | Translation by a period empties every window |
| Order in the cut system reaches into the strip | The homogeneous bound `v ≥ −1/(r(r+1))` is the edge, and nothing passes it (`eq_zero_of_homogeneous_of_ge`) |
| Balanced rotated coefficients force equal moduli | Only when nonzero: `a = b = F` is an identity for every entire `F` |
| The extremal law is a contradiction | It is a necessary law of a counterexample, vacuous under RH. Nothing proved here contradicts it |
| The twin is a fake for zero location | `ζ(s)/ζ(2s)` has the zeros of `ζ` right of `½` |

## 9. Open research topics

1. **A parity source.** A power bound on some `Σ c(k) λ(k) L(⌊x/k⌋)` with `D_{cλ}` not vanishing at a prospective zero. Any such bound moves zeros.
2. **Growing levels.** What reads `Λ − 2b` when `b` is supported above a level growing with `N`? The harmonic mass tends to `0` there, and it is the entire signal of the Selberg ledger.
3. **Higher degree.** Do polynomial ledgers of degree `k ≥ 3` read anything of the twin beyond values of `ζ′/ζ` at integers `≥ 2`?
4. **Kernel beyond power laws.** Finite combinations are zeros and monotone kernel vectors vanish. Which infinite combinations lie in the kernel, and in which norm?
5. **Finite-level radius.** Quantify `tendsto_pronic_of_tight`: how far from pronic is a fake of level `K` with a tail bound `C/r`?
6. **Integer-norm one-offs.** Does an integer system with count `x + O(x^θ)`, `θ < β`, have a new zero at `β`? New zeros need deletion, and exchange exponent `≥ β`.
7. **Defect of a one-off.** Stencils are at infinite FE distance. What is the smallest FE defect carrying a one-off, outside the stencil class?
8. **Coefficient classes.** For which class of entire coefficients is a balanced rotated relation neither vacuous nor refuted?
9. **The extremal law.** Combine the Stieltjes sign with the structure of `Q` (log-concavity, real coefficients, order `½`). Is it violated, at second order or for multiple zeros?
10. **Pointwise bounds.** Close the range between `y ≍ log T` and the VK length, or show an obstruction there.

## 10. Pillar theorems

| Theorem | Statement | Lean |
|---|---|---|
| Uniqueness of the fake | A fake at every level is the pronic measure | `eq_pronic_of_forall_isFakePrimeMeasure` |
| Tight fakes | Tight fakes of growing level converge to the pronic measure | `tendsto_pronic_of_tight` |
| Zeros are the kernel | `r^{-s}` lies in the kernel on `Re s > 0`, `s ≠ 1`, iff `ζ(s) = 0` | `forall_hasSum_abelStep_mod_zero_iff` |
| Monotone kernel vanishes | A kernel vector with a monotone tail is zero | `eq_zero_of_cut_kernel` |
| Curve kernel | Kernel = recurrence, rank `deg P`, power tails = zeros | `isCurveKernel_iff_isSolution`, `rank_curveKernel`, `isCurveKernel_pow_iff` |
| Purity is the trace bound | `1 − tu + qu²` has pure kernel iff `t² ≤ 4q` | `isPureKernel_iff` |
| Carry | `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋`, never constant; bounded multiplicities have no Frobenius | `floor_mul_sub_mul_floor`, `not_exists_constant_carry`, `not_hasFrobenius_of_bounded` |
| Ledger hierarchy | `ζ A^k` has order `m − k`; only `k = 1` is blind | `meromorphicOrderAt_ledgerSymbol`, `blind_of_linear`, `sees_of_lt` |
| Filter law | Selberg gap `= 4 L N Σ b(e)/e + O(N^{3/4})`, uniformly in `b` | `exists_abs_selberg_gap_sub_le` |
| Twin constant | Gap per `N` tends to `4 L (−ζ′/ζ(2))` | `tendsto_selberg_twin_gap`, `ofReal_primeSquareMass` |
| Liouville ledger | `Σ_k L(x/k) = ⌊√x⌋`; `L(x) = Σ_{d ≤ √x} M(x/d²)` | `floorSum_liouvilleR`, `liouvilleR_eq_squareMertens` |
| Parity confinement | A power bound on the parity ledger confines zeros to zeros of the twist | `twistPoly_eq_zero_of_parity_bound` |
| Effective Kronecker | A return at height `≤ 4(D+1) R^{2D+1}`, in every window | `exists_height_phase_return`, `threshold_le`, `exists_height_phase_return_window` |
| Effective recurrence of a model | Zeros of a Dirichlet polynomial recur in every window of a fixed length | `exists_zero_in_every_window` |
| The tail fails | At a zero, positive density of prime returns are not returns of `ζ` | `exists_primeReturn_not_zetaReturn` |
| Short-sum barrier | No cancellation for primes `≤ y` at some height below `4(D+1) 4^{(2D+1)y}` | `exists_height_no_cancellation` |
| Limit map | Limits of translates fill the gauge torus and contain the twin | `exists_tendsto_translate`, `exists_tendsto_translate_twin` |
| Exact count | Integer norms with eventually exact count are the rational primes | `nonempty_label_equiv_primes` |
| Hamming law | Exchange of summable exponent `σ` is a zero-free holomorphic factor on `Re s > σ` | `differentiableOn_exchangeLog`, `exchange_eq_zero_iff`, `zeta_mul_exchangeFactor_eq_exp` |
| Generators add no zeros | Additive systems vanish exactly with `ζ` right of the count exponent | `exists_numerator_eq_mul`, `numerator_eq_zero_iff` |
| Infinite defect | A sublinear FE defect forces a stencil to be constant | `eq_zero_of_defect_sublinear`, `eq_zero_of_integrable_stencilDefect` |
| Bohr on the line | `T⁻¹ ∫_0^T ζ(½+it) n^{it} dt → n^{-½}`, and `→ 0` off the spectrum | `tendsto_critical_average_log`, `tendsto_critical_average_of_forall_ne` |
| Extremal modulus | At the maximal-angle zero, `‖Q(t̄ w₀)‖ < ‖Q(t w₀)‖` for `Im t > 0` | `exists_zero_of_maximal_angle`, `norm_squaredXi_conj_lt` |
| Equal modulus | RH iff `‖Q(tw)‖ = ‖Q(t̄w)‖` at all zeros, for one `t` off the axis | `riemannHypothesis_iff_forall_norm_eq` |
| Stieltjes sign | At a simple extremal zero, `Im(w₀ Q″(w₀)/Q′(w₀)) ≤ 0` | `im_stieltjes_nonpos` |
| No polynomial rotation | `Q` satisfies no polynomial rotated relation | `squaredXi_no_polynomial_rotation` |

## 11. Place in the research

RAC starts where the linear theory closes. It takes its objects from three programmes, and its verdicts feed the frontier as boundaries of the sign-free route.

| Neighbour | Relation |
|---|---|
| ArithmeticAuxiliaryDynamics | supplies stencils, producers, fake measures, ledgers, rate and battery (`hasRate_vk`, `exists_bracket_bestRate`, `IsProducer.abs_ledger_twin_le`, `goldenL_shift`). Its open questions on parity through the primes and on the extremal measure are answered here for filters and for tight limits |
| ZeroConfigurationGeometry | finite oscillations and annihilators (`primeErrorFiniteOscillation_unique_abscissa_and_profile`, `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`), Gamma dominance (`re_carrier_speed_ge`). Also sign-free. ZCG works with the zero configuration, RAC with the cut system |
| ArithmeticPositiveDuality | Beurling isolation and countermodels (`beurlingSystem_rigidity_of_small_critical_line_defect`, `critical_line_defect_gt_of_not_prime_equiv`, `not_weakRecurrence_overRegularZeta`). RAC adds the infinite defect of the stencil class |
| RHTower, integer Beurling | the additive factorization and the half-dimension floors (`abscissaOfAbsConv_logCoeff_le`, `not_isBigO_count_of_leading_chebyshev`, `not_isBigO_count_of_frequently_abs_mass`) |
| RHTower, zeta returns | `zetaReturnSet`, the strong recurrence receiver, Bohr coefficients on lines above `½` |
| ArithmeticOfSquareRootPrecision | the twin and its torsion identities (`liouvilleWeight`, `sum_evenVonMangoldt`), the count at precision |
| ArithmeticKreinLangerTheory, RHTower.Hyperelliptic | Stepanov's order, stencil integers and their logarithms, Hasse–Weil for split curves |
| ArithmeticLorentzianGeometry | realness of Kloosterman sums, the same local factor read as a trickle-down inequality |
| ArithmeticInnerFunctionTheory, prime torus theory | the complement: they keep the positivity that RAC excludes |
| ArithmeticScatteringHolography | a parallel test: it asks for a universal law from wave dynamics, RAC from exact arithmetic |

## 12. Success criteria and contributions

Status of the criteria for the field:

| Criterion | Status |
|---|---|
| No quadratic form with a sign, no self-adjoint operator | Met. Order enters as nonnegativity of measures and of step weights, and as a nonnegative density on the height line in effective Kronecker. No form on arithmetic data is used |
| Hasse–Weil over `𝔽_q` in the same language | Met as a reading: purity of the kernel is the statement for split hyperelliptic curves and Kloosterman data, with Stepanov and Weil as inputs. The cut system gives no new proof of them |
| Distinguishes rational primes from continuous and discrete Beurling systems | Met: exact count, carry, continuous multiplicity, exchange |
| Breaks parity | Not met. The twin and all its filters are passed at scale `N`, and the signal is a value at `s = 2`. No source gives a parity bound at any power saving |
| Not blind to zero modes | Met for the nonlinear pieces, and proved impossible for exact readings |

The field has no named mechanism above VK. Nothing shows that the exclusion of positivity is forced: over `𝔽_q` both Hodge index and Stepanov prove the theorem.

A contribution to this field must

- use no form with a sign and no self-adjoint operator;
- state which arithmetic of `⌊x⌋` it uses, and fail for a general meromorphic function with the same functional equation;
- pass the battery: fail for the golden fake or continuous systems when it claims purity, and separate the twin when it claims parity;
- have a reading over `𝔽_q`;
- give, when it is negative, the strongest positive statement the obstruction exposes.
