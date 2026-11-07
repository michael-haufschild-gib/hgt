# Rigid Arithmetic of Cuts (RAC)

Namespace `GaloisForLFunctions.RigidArithmeticOfCuts`; umbrella `RigidArithmeticOfCuts.lean`; 41 modules.
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
The modules here do the second for every class they name. Where a class can decide, they prove that its deciding statement is
equivalent to a zero-free region, so that the remaining input is identified exactly.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Sawtooth, cut identity | `sum_Icc_mul_mod` | `Σ_{r ≤ kJ} U(r) (r mod k) = Σ_{r ≤ kJ} T(r) − k Σ_{j ≤ J} T(kj)` for `U(r) = T(r) − T(r+1)` |
| Fake prime measure | `IsFakePrimeMeasure` | `u ≥ 0` with `Σ_j u(j) ((j+1) mod k) = log k` for `k ≤ K` |
| Tail, deviation | `cutTail`, `cutDeviation` | `T(r) = Σ_{j ≥ r} u(j)`; `W = 1/r − T` |
| Cut defect, kernel | `cutDefect`, `IsCutKernel`, `cutDefectC` | tails invisible to every balanced stencil |
| Zero mode, superposition | `abelStep`, `IsStripSuperposition` | the tail `r^{-s}`; absolutely convergent sums of modes in a strip |
| Hecke action | `IsCutKernel.dilate`, `heckeOp` | `T ↦ T(j ·)` on the kernel |
| Curve kernel | `tailPairing`, `IsCurveKernel`, `curveKernel` | tails annihilating the ideal of the numerator `P` |
| Pure kernel | `traceNumerator`, `IsPureKernel` | genus one: every power-law kernel vector has decay `q^{-r/2}` |
| Carry | `floor_mul_sub_mul_floor`, `HasFrobenius` | the Frobenius defect `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋` |
| Ledger | `ledger`, `conv`, `selbergWeight` | `Σ_d a(d) g(⌊x/d⌋)` and its convolution readings |
| Symbols | `vonMangoldtSymbol`, `ledgerSymbol`, `twinSymbol` | `A = −ζ′/ζ`, `ζ A^k`, `T(s) = A(s) − 2A(2s)` |
| Twin and filters | `twinWeight`, `filteredTwin`, `IsEvenFilter`, `levelFilter` | `−λΛ = Λ − 2Λ1_{Ω even}`; `Λ − 2b`, `0 ≤ b ≤ Λ1_{Ω even}` |
| Harmonic mass | `harmonicMass`, `primeSquareMass`, `levelConstant` | `Σ_{e≤N} b(e)/e`; `κ = −ζ′/ζ(2)`; the mass above a level |
| Parity ledger | `liouvilleR`, `parityLedger`, `squareMertens`, `twistPoly` | `L(x)`; `Σ c(k) λ(k) L(⌊x/k⌋) = Σ_{n≤x} λ(n) h(n)`; `Σ_{d ≤ √x} M(x/d²)`; `D_{cλ}` |
| Return sets | `primeReturnSet`, `zetaReturnSet`, `windowSum` | Bohr sets of finite prime families; returns of `ζ`; dyadic prime sums |
| Gauge torus | `IsGaugePoint` | unitary completely multiplicative `ω` |
| Beurling distances | `HasEventuallyExactCount`, `exchangeCount`, `exchangeFactor`, `numerator`, `stencilDefect` | count, Hamming, FE defect |
| Models | `cubicMass`, `cubicFactor`, `goldenL` | bounded count with a new zero; the golden fake |
| Maximal-angle zero | `squaredXi`, `zeroSq`, `zeroSlope`, `sqFactor` | `Q(z²) = Ξ(z)`; zeros `w = α²` in the sector `|arg w| ≤ π/3`, positive iff RH |
| Coefficient class | `HasSqrtGrowth` | entire `f` with `‖f(w)‖ ≤ C exp(C √‖w‖)` |

## 3. Language

- **Cut.** A point where a floor jumps. **Multiplicity against size.** The count of a cut against the size of the integer it builds.
- **Carry.** The failure of `⌊·⌋` to be self-similar.
- **Blind.** A functional is blind at `ρ` when its generating function has no pole at `ρ`.
- **Exact.** A functional is exact when its value is determined by `⌊x⌋` alone.
- **Fake.** A measure consistent with the cut system at some level. **Tight.** Dominated by one summable sequence.
- **Kernel vector.** A tail invisible to every balanced stencil. **Pure kernel.** All modes at the critical decay.
- **Filter.** A twin that changes only chosen even prime powers. **Harmonic mass.** What a quadratic reading sees of a filter.
- **Parity exponent.** The infimum of `a` with `L(x) ≪ x^a`.
- **Oscillation, annihilator.** A finite oscillation `x^β T(log x)` in `ψ − x`, and a dilation combination that kills it.
- **Head and tail.** A finite Dirichlet part and its remainder.
- **Transport.** Copying a zero to a new height by a return, through minimum modulus.
- **Isolation.** A positive lower bound for the distance from `ζ` to every other system.
- **Extremal position.** A statement at the zero of maximal angle, used in place of a sign.
- **Dominance.** One function exceeding its rotations by more than every exponential, through its Gamma factor.

## 4. Mechanisms

1. **Exact identities.** The cut identity; Liouville's `Σ_k L(x/k) = ⌊√x⌋` (`floorSum_liouvilleR`); Selberg's
   `(Λ log + Λ∗Λ) ∗ 1 = log²` (`sum_divisors_selbergWeight`).
2. **No uniform measure on `ℕ`.** A finite measure with `W(kℕ) = S/k` for all `k` vanishes, by the Euler product at the edge
   (`eq_zero_of_uniform_multiples`). At finite level the same sieve gives a radius (`abs_le_of_uniform_multiples_level`).
3. **Rigidity as uniqueness.** One fake at infinite level (`eq_pronic_of_forall_isFakePrimeMeasure`); one system with an exact
   count (`nonempty_label_equiv_primes`); one system of small FE defect (`beurlingSystem_rigidity_of_small_critical_line_defect`).
4. **Extremal-factor modulus.** With `u = w₀/w`, `‖1 − tu‖² − ‖1 − t̄u‖² = 4 Im t Im u` (`rotated_factor_norm_sq_sub`). At the
   maximal-angle zero every Hadamard factor points the same way (`norm_squaredXi_conj_lt`), and the first order at the boundary
   zero is a Stieltjes sign (`im_stieltjes_nonpos`).
5. **Transport by minimum modulus.** A holomorphic function smaller at a centre than on a circle has a zero in the disc
   (`exists_zero_of_norm_center_lt`). It moves zeros of Dirichlet polynomials in every window (`exists_zero_in_every_window`).
6. **Gamma speed as dominance.** On the negative axis `Q(−r²) = ξ(½ + r)` exceeds every rotation `Q(ϑ(−r²)) = ξ(½ + rω)` by more than every
   exponential in `r`, since `Γ(a)/Γ(b) ≤ 4/⌊b − a⌋!` (`exists_norm_squaredXi_rot_le`). On the critical line the same speed beats a finite Euler
   speed above a horizon (`re_carrier_speed_ge`, ZeroConfigurationGeometry).
7. **Phragmén–Lindelöf on a ray.** An even entire function of exponential type that decays faster than every exponential on a ray vanishes
   (`eq_zero_of_decaysOnRay`).
8. **Nonlinear ledgers.** `ζ A^k` has order `m − k` at a zero of order `m` (`meromorphicOrderAt_ledgerSymbol`). Convolution moves the twin gap
   from `√N` to `N`, and the gap is the harmonic mass (`exists_abs_selberg_gap_sub_le_sharp`).
9. **Effective Kronecker.** Integrality gives `|log a − log b| ≥ 1/Q` (`one_div_le_abs_log_sub_log`). On the divisors of `R^D` a
   nonnegative separated trigonometric density gives a return at explicit height (`exists_height_phase_return`).
10. **Exchange.** The count law `|Σ w_i ⌊x/m_i⌋ − x Σ w_i/m_i| ≤ x^σ Σ |w_i| m_i^{-σ}` (`abs_tsum_mul_floor_sub_le`) and the Hamming law: an
    exchange of summable exponent `σ` is a holomorphic zero-free factor on `Re s > σ` (`differentiableOn_exchangeLog`, `exchange_eq_zero_iff`).
11. **Bohr coefficients on the line.** `T⁻¹ ∫_0^T ζ(½+it) n^{it} dt → n^{-½}`, by Cauchy from `¾` with the convexity bound on the
    horizontal sides (`tendsto_critical_average_log`).
12. **Dirichlet means.** `ε ζ(1 + ε + b) → 1_{b = 0}` for `Re b ≥ 0` separates the exponents of a relation `Σ d_i k^{w_i} = D` at the top
    abscissa (`eq_zero_of_sum_cpow_eq_const`).

## 5. Questions and their answers

**Q1. What replaces Frobenius?** Nothing removes the sawtooth over `ℤ`, and this is a theorem. The Frobenius defect of `⌊·⌋` is the carry
`⌊k{x}⌋`, which is never constant for `k ≥ 2` (`not_exists_constant_carry`) and is the sum of the shifts `⌊x + j/k⌋ − ⌊x⌋`
(`carry_eq_sum_shifts`). A count with `N(kx) = kN(x) + C` has support in finitely many geometric progressions
(`exists_pow_mul_of_ne_zero`, `card_support_le`), so bounded multiplicities admit no Frobenius (`not_hasFrobenius_of_bounded`). A
stencil cuts a proportion at least `φ(L)/L` of the integers (`totient_le_card_cuts`). Over a curve the kernel is one linear recurrence, of
rank `deg P` (`isCurveKernel_iff_isSolution`, `rank_curveKernel`), and `P = 1` leaves no kernel (`eq_zero_of_isCurveKernel_one`). Over `ℤ` the
kernel carries a Hecke action instead of a recurrence, and a finite invariant subspace contains a completely multiplicative vector
(`exists_mul_of_hecke_invariant`).

**Q2. What nonlinear functional of `Λ` sees a zero mode and survives the twin?** `ζ A^k` has order `m − k` at a zero of order `m`. Only `k = 1` is
blind (`blind_of_linear`, `sees_of_lt`), and at a simple zero `(s − ρ)^k ζ A^{k+1} → (−1)^{k+1} ζ′(ρ)` (`tendsto_mul_ledgerSymbol`). No piece of
this kind is exact: the exact combination `ζ(A² − A′) = ζ″` is blind again (`riemannZeta_mul_selberg`). For the twin, the Selberg ledger is exact on `Λ`
(`ledger_selbergWeight`), and uniformly over filters

`ledger(Selberg Λ, N) − ledger(Selberg (Λ − 2b), N) = 4 L N Σ_{e ≤ N} b(e)/e + O(√N log N)` (`exists_abs_selberg_gap_sub_le_sharp`).

The Liouville twin has the exact rate `4 L (−ζ′/ζ(2))` (`tendsto_selberg_twin_gap`). A twin agreeing with `Λ` up to a level `y` is seen with gap of exact
order `N/√y` for every `y ≤ N/(K log² N)` (`exists_level_gap_order`), against `2 w ψ(√N)` for a linear ledger (`abs_ledger_sub_filteredTwin_le`). The
reading passes the twin, Type I and Type II data (`exists_le_of_typeI_represents_gap`, `not_isBilinearStatement_selberg`). At every degree its symbol separates
the twin only at `s = 1`, through jets of `ζ′/ζ` at `s = 2`; at every zero right of `½` the twin and `Λ` have the same leading singular part
(`tendsto_sub_pow_twinSymbol_at_one`, `tendsto_sub_pow_twinSymbol_at_zero`).

**Q3. Why do primes recur at a zero, if they do?** The primes always recur. Every finite family returns on a set of positive lower density
(`exists_density_primeReturnSet`), at explicit height and in every window (`exists_height_phase_return_window`). No nontrivial return lies below the
length: a return of all `n ≤ N` has `τ < 2/log N` or `τ > N − 1` (`exists_phase_far`, `no_prime_return`). Above the abscissa recurrence of the primes
is enough, since a return of the primes up to a length is a return of `ζ` on the whole half-plane (`primeReturnSet_subset_zetaReturnSet`). At a zero
it is never enough. At a positive proportion of heights all primes of any finite family return and `ζ` does not
(`exists_primeReturn_not_zetaReturn`). A Dirichlet polynomial has no tail and its zeros recur in every window (`exists_zero_in_every_window`). A
bounded return must be a return of every prime (`tendsto_phaseDefect_zero`). So the tail is exactly what fails, at every length. The limit map is onto
the gauge torus (`exists_tendsto_translate`), and the twin `ζ(2s)/ζ(s)` is a limit of translates of `ζ` on `Re s > 1`
(`exists_tendsto_translate_twin`), so recurrence cannot see parity.

**Q4. Is a single off-line zero a contradiction with `N(x) = ⌊x⌋`?** Not by anything below. The zeros are the power-law kernel of the cut system on
`Re s > 0` (`forall_hasSum_abelStep_mod_zero_iff`). Absolutely convergent superpositions of modes in a strip lie in the kernel exactly when
they are carried by zeros (`superposition_kernel_iff`).

| Class of information | What it gives | Theorem |
|---|---|---|
| Exact linear ledgers | blind at every zero | `hasSum_ledgerMode_eq_zero` |
| Exact nonlinear ledgers | blind again | `riemannZeta_mul_selberg` |
| Nonlinear ledgers of any degree on the twin | the same singular part at every zero | `tendsto_sub_pow_twinSymbol_at_zero` |
| Order in the cut system | reaches the edge only: `ζ ≠ 0` on `Re s ≥ 1` and on the real segment | `riemannZeta_ne_zero_of_one_le_re_of_cut`, `riemannZeta_ne_zero_of_real` |
| Finite prime recurrence | never controls the tail at a zero | `exists_primeReturn_not_zetaReturn` |
| Limits of translates | contain the twin | `exists_tendsto_translate_twin` |
| Adding generators | no new zero right of the count exponent | `numerator_eq_zero_iff` |
| Exchange of summable exponent `σ` | a holomorphic zero-free factor on `Re s > σ` | `differentiableOn_exchangeLog`, `exchange_eq_zero_iff` |
| A count within `O(1)` of `x`, nonnegative and multiplicative | consistent with zeros at `Re s ≈ 0.80` | `cubicCount_sub_mem`, `exists_cubicFactor_eq_zero` |
| The exact cut identity of `λ` | determines `λ` on every integer | `eq_liouville_of_floorSum` |
| A power bound on the parity ledger | equivalent to a zero-free strip, up to zeros a twist absorbs | `zeroFree_iff_liouville_power`, `twistPoly_eq_zero_of_parity_bound` |
| The extremal modulus inequality at every order | satisfied by a real quadratic with an off-axis zero | `norm_model_conj_lt` |
| Energy-space kernel of mass zero | implies RH | `riemannHypothesis_of_energy_kernel` |

The arithmetic input the question asks for is a parity bound. Parity is not missing information: the exact identity
`Σ_{k ≤ x} L(x/k) = ⌊√x⌋` determines `λ` on every integer (`eq_liouville_of_floorSum`). What is missing is the size of `L`. At log powers it is known
(`exists_abs_parityLedger_le_log`). At a power saving it is the zero-free strip itself (`zeroFree_iff_liouville_power`,
`riemannHypothesis_iff_liouville_power`).

**Q5. What is the fake prime measure closest to the true one, for each `K`?** At infinite level there is one fake, the pronic measure
`1/((j+1)(j+2))` (`eq_pronic_of_forall_isFakePrimeMeasure`). Tight fakes of levels tending to infinity converge to it (`tendsto_pronic_of_tight`). At
finite level, translating an atom by a common period keeps all moments (`isFakePrimeMeasure_translate`), so there is no radius without a condition at
infinity. With a summable deviation the radius is explicit: `|W(n)| ≤ (|S|/n) ∏_{p<X}(1 − 1/p) + Σ_{t≥X} |W(nt)|` whenever `n 4^X ≤ K`
(`abs_cutDeviation_le_of_level`), of order `1/log log K` by Mertens. The upper radius of the window mass is the rate (`TheDualOfTheRateIsAFakePrimeMeasure`).

**Q6. Is there an arithmetic rotated identity with balanced coefficients nonzero at the zeros of `ξ`?** Not with coefficients of growth `exp(C √|w|)`:
such a relation is trivial (`rotated_relation_trivial`), and this covers polynomials (`squaredXi_no_polynomial_rotation`). Unrestricted
coefficients are vacuous already at the size of `Q` (`self_coefficient_rotated_relation`, `exists_normalized_entire_vacuous_rotated_relation`). A relation
with balanced coefficients nonzero at the zeros implies RH (`riemannHypothesis_of_balanced_relation`), and equal rotated modulus at all zeros is RH
(`riemannHypothesis_iff_forall_norm_eq`).

## 6. Tools

| Tool | State | Lean |
|---|---|---|
| Ledgers that are not blind | built: orders, residues, sharp filter law, every degree | `TheHierarchyOfLedgers`, `TheQuadraticGapIsTheHarmonicMass`, `EveryLevelIsSeen`, `TheTwinAtEveryDegree` |
| Parity input | built: the exact identity and its rigidity, the Type I form, the VK-level source, the equivalence with zero-free strips at power savings | `TheLiouvilleChebyshevIdentity`, `TheExactIdentityDeterminesTheParity`, `AParityBoundConfinesTheZeros`, `TheParityExponentIsTheZeroAbscissa` |
| Passing the filters | built: twin, Type I, Type II | `TheSelbergReadingPassesTheFilters` |
| Effective Kronecker | built: explicit threshold `4(D+1) R^{2D+1}`, every window, positive density, no return below the length | `EffectiveKroneckerAtArithmeticScale`, `ZerosOfADirichletPolynomialRecurEffectively`, `TheTailFailsAtAZero`, `TheFirstReturnIsAboveTheLength` |
| Pointwise bounds below VK | built at both ends: no cancellation at some height up to `y ≍ log T`; square-root cancellation at all dyadic lengths up to `T/log T` off a set of measure `≪ T Y^{-2ε}` | `TheShortSumBarrierHasALeftEndpoint`, `CancellationAtAlmostEveryHeight` |
| Metric geometry of Beurling systems | built: exact count rigidity, count law, Hamming law, added generators, stencil defect, bounded-count model | `AnExactCountForcesTheRationalPrimes`, `TheExchangeLaw`, `AddingGeneratorsAddsNoZeros`, `StencilSystemsHaveInfiniteDefect`, `ABoundedCountWithANewZero` |
| Extremal calculus | built: max angle, Hermite–Biehler modulus, Stieltjes sign, the model, dominance, coefficient boundary | `TheZeroOfMaximalAngle`, `TheStieltjesSignOfTheExtremalZero`, `TheExtremalLawHasAModel`, `RotatedRelationsNeedCoefficientsOfTheSizeOfQ` |
| Kernel calculus | built: `ℤ` and curves, superpositions, energy space | `ZerosAreTheKernelOfTheCutSystem`, `ACutVectorWithAMonotoneTailVanishes`, `TheCutSystemOverACurve`, `TheKernelBeyondPowerLaws` |
| Fake calculus | built: uniqueness, tight limits, finite-level radius | `TheFakePrimeMeasureIsUnique`, `TightFakesConvergeToThePronicMeasure`, `TheFiniteLevelRadius` |

## 7. Test cases

| Test | Outcome | Theorem |
|---|---|---|
| `𝔽_q[T]` | zero kernel: `P = 1` | `eq_zero_of_isCurveKernel_one` |
| Weil for split hyperelliptic curves | kernel modes of exact decay `q^{-r/2}`, by Stepanov | `isCurveKernel_lRoots_of_stepanov` |
| Genus one | kernel pure iff `t² ≤ 4q` | `isPureKernel_iff` |
| Kloosterman data | pure, with Weil's `2√p` as input; the stencil window `|K| ≤ p + 1` does not reach it | `isPureKernel_kloosterman`, `traceNumerator_kloosterman` |
| Carlitz stencil | a stencil is cut only at a degree boundary | `carlitzOrder_sub` |
| Golden fake | exact transport, impure kernel, fails the count | `golden_battery`, `golden_deep_mode` |
| Continuous Beurling systems | no multiplicity, no carry | `continuous_multiplicity_eq_zero` |
| Liouville twin | linear ledgers within `2 w ψ(√N)`; Selberg gap of exact rate `4 L κ` | `IsProducer.abs_ledger_twin_le`, `tendsto_selberg_twin_gap` |
| Level filters | gap of exact order `N/√y` up to `y ≍ N/log² N` | `exists_level_gap_order` |
| Type I, Type II data | do not compute the Selberg gap | `exists_le_of_typeI_represents_gap`, `not_isBilinearStatement_selberg` |
| Bounded-count model | count within `3` of `x`, zeros at `Re s ≈ 0.80`, infinite FE defect | `cubicCount_sub_mem`, `exists_cubicFactor_eq_zero`, `not_tendsto_cubic_defect` |

## 8. Traps

| Trap | Fact |
|---|---|
| A stencil identity sees a zero | Every exact ledger is holomorphic at every zero |
| A functional that sees a zero is a new input | The pieces `ζ A^k` have no exact value, and their exact combination is blind |
| Selberg's identity excludes a zero | It holds for every analytic function in the form `f(A² − A′) = f″` |
| The Selberg twin gap breaks parity | The gap is the harmonic mass of even prime powers, a value at `s = 2` |
| Higher-degree ledgers break parity | At every degree the twin has the singular part of `Λ` at every zero |
| A filter of `Λ` is the parity problem | `−λΛ` differs from `Λ` only on even prime powers. Sieve parity concerns `λ` on all integers |
| A parity bound is a new input | At a power saving it is a zero-free strip, exactly |
| A return of the primes is a return of `ζ` | True above the abscissa, false at a zero, at every length |
| Returns come early | A return of all `n ≤ N` lies above height `N − 1` |
| The Dirichlet model is `ζ` with a small error | Its zeros recur in every window; returns at a zero of `ζ` are rare |
| Transport proves purity | The golden fake returns exactly and is impure |
| Mean values see off-line zeros | The Bohr mean of `ζ` against `n^{it}` is `n^{-σ}` on every line `½ ≤ σ < 1`, with no term from any zero |
| Pointwise cancellation fails only for short sums | It holds off a small set at every length, and fails somewhere up to `log T` |
| Integer norms exclude fakes | Integer systems with count `x + O(x^σ)` exist for every `σ > 0` (`exists_abs_exchangeCount_sub_le`). Only an exact count forces the primes |
| A bounded count error puts the zeros on the line | `−3 ≤ N(x) − x ≤ 0` with zeros at `Re s ≈ 0.80` (`ABoundedCountWithANewZero`) |
| Count distance and FE distance agree | A nonconstant stencil has bounded count error and a defect that is not sublinear (`eq_zero_of_defect_sublinear`) |
| Adding primes can create a zero | Right of the count exponent it never does (`numerator_eq_zero_iff`). Only deletion can |
| A fake of level `K` has mass in a window | Translation by a period empties every window |
| Order in the cut system reaches into the strip | The homogeneous bound `v ≥ −1/(r(r+1))` is the edge, and nothing passes it (`eq_zero_of_homogeneous_of_ge`) |
| Balanced rotated coefficients force equal moduli | Only when nonzero: `a = b = F` is an identity for every entire `F` |
| Small coefficients might carry a rotated relation | Coefficients of growth `exp(C √|w|)` carry none |
| The extremal law is a contradiction | It is a necessary law of a counterexample, and the real quadratic `w² − 2w + 2` with zeros `1 ± i` satisfies the whole inequality (`norm_model_conj_lt`) |
| Parity is missing information | The exact cut identity determines `λ` on every integer; only the size of `L` is missing |
| The twin is a fake for zero location | `ζ(s)/ζ(2s)` has the zeros of `ζ` right of `½` |

## 9. Open research topics

1. **The size of `L` beyond VK.** The exact identity determines `λ` (`eq_liouville_of_floorSum`), and a power saving for `L` is a zero-free strip
   (`zeroFree_iff_liouville_power`). The open question is the size of `L` between the VK saving and a power, through the cut system. For a stencil whose twist `D_{cλ}` vanishes at a
   prospective zero, a parity bound is weaker than a zero-free strip: which stencils have twists with zeros where they are needed?
2. **Parity through stencils, not through `Λ`.** Every reading of `Λ` sees the twin only through even prime powers (`tendsto_sub_pow_twinSymbol_at_zero`). Long integer
   polynomials see `λ` away from the pole (`eventually_not_uniform_liouville`, ArithmeticProduction). Is there a cut-system reading of that kind?
3. **Genuine Beurling one-offs.** The bounded-count model has negative generators at powers of `2`. Does a system with nonnegative integer generators, count
   `x + O(x^θ)`, have a new zero at `β > θ`? It must delete primes, with exchange exponent `≥ β`.
4. **Kernel beyond well-ordered superpositions.** Is every kernel vector of finite energy a limit of zero modes? The converse of
   `riemannHypothesis_of_energy_kernel` is the Báez-Duarte–Bagchi direction of Nyman–Beurling.
5. **Coefficient classes between `exp(C√|w|)` and `Q`.** Coefficients of order `½` with `log` in the exponent: is a non-vacuous rotated relation possible there?
6. **The extremal law with more structure.** The inequality alone has a model (`norm_model_conj_lt`). Which further property of `Q`, its order `½`, the log-concavity
   of its coefficients, or its functional equation, contradicts it together with the extremal position?
7. **Pointwise bounds at all heights.** Between `y ≍ log T` and the VK length, how large is the exceptional set of `CancellationAtAlmostEveryHeight` allowed to be?
8. **The smallest FE defect of a one-off.** Stencils are excluded (`eq_zero_of_defect_sublinear`), and a prime mismatch at `N` costs `1/(400 N²)`
   (`critical_line_defect_gt_of_not_prime_equiv`). Which classes outside stencils carry a one-off at finite defect?

## 10. Pillar theorems

| Theorem | Statement | Lean |
|---|---|---|
| Uniqueness of the fake | A fake at every level is the pronic measure | `eq_pronic_of_forall_isFakePrimeMeasure` |
| Tight fakes | Tight fakes of growing level converge to the pronic measure | `tendsto_pronic_of_tight` |
| Finite-level radius | `|W(n)| ≤ (|S|/n) ∏_{p<X}(1 − 1/p) + Σ_{t≥X}|W(nt)|` for `n 4^X ≤ K` | `abs_cutDeviation_le_of_level` |
| Zeros are the kernel | `r^{-s}` lies in the kernel on `Re s > 0`, `s ≠ 1`, iff `ζ(s) = 0` | `forall_hasSum_abelStep_mod_zero_iff` |
| Superpositions | An absolutely convergent strip superposition lies in the kernel iff it is carried by zeros | `superposition_kernel_iff` |
| Energy kernel | Mass zero for all finite-energy kernel vectors implies RH | `riemannHypothesis_of_energy_kernel` |
| Monotone kernel vanishes | A kernel vector with a monotone tail is zero | `eq_zero_of_cut_kernel` |
| Curve kernel | Kernel = recurrence, rank `deg P`, power tails = zeros | `isCurveKernel_iff_isSolution`, `rank_curveKernel`, `isCurveKernel_pow_iff` |
| Purity is the trace bound | `1 − tu + qu²` has pure kernel iff `t² ≤ 4q` | `isPureKernel_iff` |
| Carry | `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋`, never constant; bounded multiplicities have no Frobenius | `floor_mul_sub_mul_floor`, `not_exists_constant_carry`, `not_hasFrobenius_of_bounded` |
| Ledger hierarchy | `ζ A^k` has order `m − k`; only `k = 1` is blind | `meromorphicOrderAt_ledgerSymbol`, `blind_of_linear`, `sees_of_lt` |
| Sharp filter law | Selberg gap `= 4 L N Σ b(e)/e + O(√N log N)`, uniformly in `b` | `exists_abs_selberg_gap_sub_le_sharp` |
| Every level is seen | Gap of exact order `N/√y` for `y ≤ N/(K log² N)` | `exists_level_gap_order` |
| Twin constant | Gap per `N` tends to `4 L (−ζ′/ζ(2))` | `tendsto_selberg_twin_gap`, `ofReal_primeSquareMass` |
| Every degree | Twin symbol `A(s) − 2A(2s)`; same singular part at zeros; `−2kκ` at the pole | `LSeries_twinWeight`, `tendsto_sub_pow_twinSymbol_at_zero`, `tendsto_sub_pow_twinSymbol_at_one` |
| Filters | Type I tests computing the gap have size `≥ δ√N`; the reading is not a Type II statement | `exists_le_of_typeI_represents_gap`, `not_isBilinearStatement_selberg` |
| Liouville ledger | `Σ_k L(x/k) = ⌊√x⌋`; `L(x) = Σ_{d ≤ √x} M(x/d²)` | `floorSum_liouvilleR`, `liouvilleR_eq_squareMertens` |
| Parity exponent | `L ≪ x^a` for all `a > Θ` iff no zero right of `Θ`; RH iff `L ≪ x^{½+ε}` | `zeroFree_iff_liouville_power`, `riemannHypothesis_iff_liouville_power` |
| Parity source | `P_c(x) ≪ x/log^k x` unconditionally | `exists_abs_parityLedger_le_log` |
| Parity confinement | A power bound on the parity ledger confines zeros to zeros of the twist | `twistPoly_eq_zero_of_parity_bound` |
| Effective Kronecker | A return at height `≤ 4(D+1) R^{2D+1}`, in every window | `exists_height_phase_return`, `threshold_le`, `exists_height_phase_return_window` |
| First return | No return of all `n ≤ N` in `[2/log N, N − 1]` | `exists_phase_far`, `no_prime_return` |
| Effective recurrence of a model | Zeros of a Dirichlet polynomial recur in every window of a fixed length | `exists_zero_in_every_window` |
| The tail fails | At a zero, a positive proportion of prime returns are not returns of `ζ` | `exists_primeReturn_not_zetaReturn` |
| Short-sum barrier | No cancellation for primes `≤ y` at some height below `4(D+1) 4^{(2D+1)y}` | `exists_height_no_cancellation`, `exists_height_window_no_cancellation` |
| Cancellation off a small set | Square-root cancellation at all dyadic lengths off measure `≪ T Y^{-2ε}` | `exists_cancellation_off_small_set` |
| Limit map | Limits of translates fill the gauge torus and contain the twin | `exists_tendsto_translate`, `exists_tendsto_translate_twin` |
| Exact count | Integer norms with eventually exact count are the rational primes | `nonempty_label_equiv_primes` |
| Bounded count | A nonnegative multiplicative count within `3` of `x` with zeros at `Re s ≈ 0.80` | `cubicCount_sub_mem`, `cubicMass_mul`, `exists_cubicFactor_eq_zero` |
| Hamming law | Exchange of summable exponent `σ` is a zero-free holomorphic factor on `Re s > σ` | `differentiableOn_exchangeLog`, `exchange_eq_zero_iff`, `zeta_mul_exchangeFactor_eq_exp` |
| Generators add no zeros | Additive systems vanish exactly with `ζ` right of the count exponent | `exists_numerator_eq_mul`, `numerator_eq_zero_iff` |
| Infinite defect | A sublinear FE defect forces a stencil to be constant | `eq_zero_of_defect_sublinear`, `eq_zero_of_integrable_stencilDefect` |
| Bohr on the line | `T⁻¹ ∫_0^T ζ(½+it) n^{it} dt → n^{-½}`, and `→ 0` off the spectrum | `tendsto_critical_average_log`, `tendsto_critical_average_of_forall_ne` |
| Extremal modulus | At the maximal-angle zero, `‖Q(t̄ w₀)‖ < ‖Q(t w₀)‖` for `Im t > 0` | `exists_zero_of_maximal_angle`, `norm_squaredXi_conj_lt` |
| Equal modulus | RH iff `‖Q(tw)‖ = ‖Q(t̄w)‖` at all zeros, for one `t` off the axis | `riemannHypothesis_iff_forall_norm_eq` |
| Stieltjes sign | At a simple extremal zero, `Im(w₀ Q″(w₀)/Q′(w₀)) ≤ 0` | `im_stieltjes_nonpos` |
| Extremal model | A real quadratic with an off-axis extremal zero satisfies the whole inequality | `norm_model_conj_lt` |
| Exact parity identity | The cut identity of `L` determines `λ` | `eq_liouville_of_floorSum` |
| Dominance | `‖Q(ϑ(−r²))‖ ≤ e^{−Kr} ‖Q(−r²)‖` for every `K`, `ϑ ≠ 1` | `exists_norm_squaredXi_rot_le` |
| Coefficient boundary | Rotated relations with coefficients of growth `exp(C√|w|)` are trivial | `rotated_relation_trivial` |

## 11. Place in the research

RAC starts where the linear theory closes. It takes its objects from several programmes, and its verdicts feed the frontier as boundaries of the
sign-free route.

| Neighbour | Relation |
|---|---|
| ArithmeticAuxiliaryDynamics | supplies stencils, producers, fake measures, ledgers, rate and battery (`hasRate_vk`, `exists_bracket_bestRate`, `IsProducer.abs_ledger_twin_le`, `goldenL_shift`). Its questions on parity through the primes, on the extremal measure and on returns are answered here for filters, finite levels and first returns |
| ArithmeticProduction | the Type I parity barrier (`typeI_parity_barrier`), the Type II twist invariance (`bilinearConstants_liouvilleTwist`), finite systems of linear laws, and long integer polynomials that see parity away from the pole. RAC adds the quadratic reading that passes the filters, and the Type I identity of the parity ledger |
| ZeroConfigurationGeometry | finite oscillations and annihilators (`primeErrorFiniteOscillation_unique_abscissa_and_profile`, `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`), Gamma dominance on the line (`re_carrier_speed_ge`). Also sign-free: ZCG works with the zero configuration, RAC with the cut system |
| ArithmeticPositiveDuality | Beurling isolation and countermodels (`beurlingSystem_rigidity_of_small_critical_line_defect`, `critical_line_defect_gt_of_not_prime_equiv`, `not_weakRecurrence_overRegularZeta`). RAC adds the infinite defect of the stencil class and the bounded-count model |
| RHTower | integer Beurling factorizations and floors, zeta returns and strong recurrence, Bohr coefficients, Nyman–Beurling (`bdTarget_notMem_closedSpan_family_of_zero`), Mertens power bounds from zero-free strips, the mean value theorem for Dirichlet polynomials |
| ArithmeticOfSquareRootPrecision | the twin and its torsion identities (`liouvilleWeight`, `sum_evenVonMangoldt`), the deciding-input theorem, the count at precision |
| ArithmeticKreinLangerTheory, RHTower.Hyperelliptic | Stepanov's order, stencil integers and their logarithms, Hasse–Weil for split curves |
| ArithmeticLorentzianGeometry | realness of Kloosterman sums, the same local factor read as a trickle-down inequality |
| ArithmeticInnerFunctionTheory, prime torus theory | the complement: they keep the positivity that RAC excludes |
| ArithmeticScatteringHolography | a parallel test: it asks for a universal law from wave dynamics, RAC from exact arithmetic |

## 12. Success criteria and contributions

Status of the criteria for the field:

| Criterion | Status |
|---|---|
| No quadratic form with a sign, no self-adjoint operator | Met. Order enters as nonnegativity of measures and of step weights, as a nonnegative density on the height line in effective Kronecker, and as the mean value theorem for the exceptional set. No form on arithmetic data is used |
| Hasse–Weil over `𝔽_q` in the same language | Met as a reading: purity of the kernel is the statement for split hyperelliptic curves and Kloosterman data, with Stepanov and Weil as inputs. The cut system gives no new proof of them |
| Distinguishes rational primes from continuous and discrete Beurling systems | Met: exact count, carry, continuous multiplicity, exchange, bounded-count model |
| Breaks parity: passes the Liouville twin and the filters on Type I and II data | Met in this sense by the Selberg reading. It does not reach `λ` on all integers: its signal is the harmonic mass of even prime powers, and at every degree it has the singular part of `Λ` at every zero |
| Not blind to zero modes | Met for the nonlinear pieces, and proved impossible for exact readings |

The field has no named mechanism above VK. Nothing shows that excluding positivity is forced: over `𝔽_q` both Hodge index and Stepanov prove the theorem.

A contribution to this field must

- use no form with a sign and no self-adjoint operator;
- state which arithmetic of `⌊x⌋` it uses, and fail for a general meromorphic function with the same functional equation;
- pass the battery: fail for the golden fake or continuous systems when it claims purity, separate the twin when it claims parity, and survive the
  bounded-count model when it claims to read zeros from the count;
- have a reading over `𝔽_q`;
- give, when it is negative, the strongest positive statement the obstruction exposes.
