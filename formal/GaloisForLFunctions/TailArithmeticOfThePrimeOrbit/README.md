# Tail Arithmetic of the Prime Orbit (TAPO)

Namespace `GaloisForLFunctions.TailArithmeticOfThePrimeOrbit`; umbrella `TailArithmeticOfThePrimeOrbit.lean`.

Throughout, `t` is a height, `L = log t`, `ω_t = (p^{−it})_p` is the point of the prime orbit at time `t`, and `y` is a
*cut*: the primes up to `y` are the **head**, the primes above `y` the **tail**. `E_y = Π_{p≤y}(1 − p^{−s})^{−1}` is the
head of `ζ`, `M_y = 1/E_y` the Euler mollifier, `ζM_y` the tail.

## 1. Motivation

Every wall of the research stops at one range of primes at one height. Below the Kronecker scale `y ≍ log t` the phases
`t log p` can be prescribed: every window of length `exp(c y log y)` enters every box of the torus on the primes up to
`y`. Above the Vinogradov length `y = exp(L^{2/3+ε})` the column `Σ_{p≤y} p^{−it}` loses a proportion of its size. In
between nothing is known, and every route needs something there: the all-height sign past `a ≈ log log X`, the width
axis, proportional savings (B46), the first-return time, a bounded return at a right zero (B89). This range is the
**dark range**.

A zero of `ζ` is an event of this range. The head never vanishes on `Re s > 0` and cannot resolve the strip below the
scale `1/log y`; the zero is carried by the tail at every cut. Prime torus theory (PTT) studies the pair `(t, ω_t)` at
finite time and proves absolute savings with proved ceilings. TAPO studies **the law of the tail**: the phases of the
primes past the head, at a single height and on Bohr sets, conditionally on what the head does. Its objects are the time
the orbit needs to return, the conditional law of the tail, the fade of the alignment past the head, and what a return at
a zero forces on the tail.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Return, anti-return | `IsReturn s ℓ η t`, `IsAntiReturn` | `1 − cos(tℓ_i) ≤ η` for `i ∈ s`; the same near the corner `−1` |
| First return | `firstReturn s ℓ η`, `returnSet` | least `t ≥ 1` of a return; for primes `ℓ = logStep = log` |
| Harmonic defect, weak return | `harmonicDefect N t`, `IsWeakReturn N C t` | `A_t(N) = Σ_{p≤N}(1 − cos(t log p))/p ≤ C` |
| Spike point | `spikePoint N t` | `1 + 1/log N + it` |
| Fade length | `fadeLength τ` | `|ζ(1 + iτ)|` |
| Weighted defect | `weightedDefect`, `weightedSize`, `returnedSteps` | `D(t) = Σ a_i(1 − cos tℓ_i)`, `S = Σ a_i`, the returned steps |
| Head and tail polynomials | `headPoly A r`, `IsRough y n` | `Σ_{m∈A} r_m m^{it}`; `n` with all prime factors `≥ y` |
| Powers of the tail | `powSupport`, `powCoeff`, `powNorm` | support, coefficients and `ℓ²` norm of `B^k` |
| Head, mollifier, tail of `ζ` | `RHTower.eulerHead`, `eulerMollifier`, `eulerTail` | `E_y`, `M_y = 1/E_y`, `ζM_y` |
| Tail-bad heights | `RHTower.eulerDiscTailBadSet y c r ε` | `|ζ − E_y| ≥ ε` somewhere on the translated disc |
| Resolution sum | `resolutionSum y σ` | `Σ_{p≤y} log p · p^{−σ}/(1 − p^{−σ})` |
| Jet of the logarithm | `logDiffMass j x` | `|Δ^{j+1} log x|`, the block coefficient of `t log` |
| Euler factor of the scattering function | `scatteringFactor p s` | `E_p(s) = (1 − p^{−2s})/(1 − p^{1−2s})` |
| Head–tail coordinates | `headTailCoordinates`, `tailCoordinate` | head coordinates and `S/(z_0⋯z_{n−1})` |
| Phase, comb | `phaseOf t n`, `PrimeTorusTheory.dist01` | `t log n/2π` and its distance to `ℤ` |

## 3. Language

- **Head, tail, cut.** The primes up to `y`, above `y`, and `y`.
- **Return; weak return.** All head phases within `η` of `1` in `1 − cos`; the head close to `1` in the harmonic metric.
- **First return** `R(y, η)`. The least height `t ≥ 1` of a return on the primes up to `y`.
- **Heavy return.** A return on a subset carrying all but `κ` of the weight.
- **Dark range.** `log t ≲ y ≲ exp(L^{2/3})`.
- **Resolution.** `1/log y` on `Re s ≥ 1`, `y^{σ−1}` at `Re s = σ`: the scale below which the head does not move.
- **Tail event; tail-good, tail-bad height.** An event visible only through the tail at every cut; a height where
  `ζ(· + iτ)` is within `ε` of `E_y(· + iτ)` on a disc, or not.
- **Fade.** The growth of `A_τ(x)` past the head. Its length is `|ζ(1 + iτ)|`.
- **Atypical member of a Bohr set.** A head-aligned height whose tail is far from `1`.
- **Exotic block.** A block where the coefficient of the phase sits on a lattice `c + ℤ` (binomial denominators).
- **Comb.** The level set `{n : dist(t log n/2π, ℤ) ≤ δ}`, a multiplicative Bohr set.
- **Head–tail certificate.** A decomposition of `1 − S(x)S̄(y)` with finitely many Euler coordinates and one tail
  coordinate.

## 4. Mechanisms

1. **The first return is an extreme value.** Mertens' second theorem and the Euler comparison give
   `log|ζ(1 + 1/log N + it)| = log log N − A_t(N) + O(1)`. A weak return up to `N` at height `t` is a spike
   `|ζ(1 + 1/log N + it)| ≍ log N`, and conversely.
2. **Precision buys length.** At a return to precision `η` the critical defect `Σ_{p<y}(1 − cos)/√p` is at most `12η√y`.
   Every absolute saving of PTT then excludes returns at small precision, and the escape of the first return to infinity
   excludes small heights.
3. **Unique factorization decouples the tail.** A `y`-smooth integer times a `y`-rough one determines both factors. The
   product of a head weight and a tail polynomial is a Dirichlet polynomial with tensor-product coefficients, and the
   mean value theorem factorizes. Powers of a tail polynomial are tail polynomials, so every conditional moment factorizes.
4. **Products of `k` primes have at most `k` prime factors.** So `‖B^k‖² ≤ k!‖b‖^{2k}`: the tail is Gaussian through order
   `k`, conditionally on the head.
5. **The head is frozen at its resolution.** Each factor moves by `p^{−σ}|v| log p` under `s ↦ s + iv`.
6. **The tail carries the zero.** On `Re s > 0` the zeros of `ζ` are those of `ζM_y` at every cut. Along a bounded
   return the tail converges to `ζM_y`. At a tail-good height the head is zero-free and large on the circle, hence, by
   the maximum principle for `M_y`, inside; so no return at a zero is tail-good.
7. **The fade is forced.** `ζ(1 + iτ)` is finite and nonzero, so `A_τ(x) − log log x → −log|ζ(1 + iτ)| + O(1)`.
8. **The jet moves.** `Δ_h^j log(x) = Δ_1^j log(x/h)`, and consecutive blocks change the coefficient by at least
   `(j+1)!/(x+j+2)^{j+2}`. A sequence that moves meets a lattice rarely.
9. **Depth is exact, height approximate.** `(1 + q₁u)(1 + q₁v) ≡ 1 + q₁(u + v) mod q₁q₂` when `q₂ ∣ q₁`; at the height
   the same identity holds up to `t h h'/x²`.
10. **Euler coordinates stop at the abscissa.** `|E_p(s) − 1| ≥ p^{1−2σ}/4` and `Σ_p p^{1−2σ} = ∞` for `σ ≤ 1`.
11. **A factorization is a certificate.** `1 − Π a_i = Σ_i (1 − a_i) Π_{m<i} a_m`, with rank-one kernels.
12. **A return is a comb.** At a return every `P`-smooth integer with `k` prime factors has phase within `k√(η/8)`;
    past `X ≍ t` the phase moves by at least `t/(2π(X+H+1))` per step, so the comb is thin.

## 5. The questions and their answers

| Question | Answer | Lean |
|---|---|---|
| **1.** What is `R(y, δ)`? | Above: `R(y, η) ≤ Q^{π(y)}` when `2π² ≤ ηQ²`. Below: `log(M + log R) ≥ (1 − η) log log y − O(1)`, i.e. `R ≥ exp(c(log y)^{1−η})`; `R > exp(√(y/(48 log y)))` at precision `12η√y·y⁴ < 4·48⁴/10^{10}` (the bound RH gives at constant precision, here at precision `≍ y^{−9/2}`); `R > exp(y^{1/A})` at precision `12η√y < exp(−δy^{1/A})`; `R → ∞` at every `η < 1`. At the weights `1/p` the first weak return is the inverse of the extreme-value function of `ζ(1 + 1/log N + it)`, and Dirichlet gives a spike `|ζ(1+1/log N+it)| ≥ e^{−1−K} log N` before `t ≤ Q^{π(N)}`, `Q ≍ √(log log N)` (Littlewood). At rank one `R` is bounded uniformly in the set. At constant precision the exponent `log log R/log log y` is known only in `[1 − η, ∞)` here; Vinogradov–Korobov would give `3/2`; `log R ≤ C y/log y`. | `question_one`, `firstReturn_le_pow`, `firstReturn_lower`, `the_precision_law`, `eventually_exp_sqrt_lt_firstReturn`, `eventually_exp_rpow_lt_firstReturn`, `abs_harmonicDefect_sub_le`, `exists_spike_le_pow`, `tendsto_firstReturn_primes`, `firstReturn_le_of_rankOne` |
| **2.** What does the tail look like conditionally on alignment below it, at resolution finer than `1/log y`? | Below the Kronecker scale it is the Steinhaus tail: second moment `‖b‖²` up to `16N log N‖r‖²‖b‖²`, mean `O(N(Σ|r|)²Σ|b|)`, moments at most `k!‖b‖^{2k}` and Gaussian large deviations `k!(‖b‖²/V²)^k`, valid while `log max A + k log Z ≪ log T`. Finer than the resolution the head does not move (`2|v|(log y + log 4)` on `Re s ≥ 1`), so all finer structure of `|ζ| = |E_y||ζM_y|` is the tail's. Typical heights are tail-good (RHTower Euler tail law). | `question_two`, `abs_conditional_second_moment_sub_le`, `norm_integral_head_sq_mul_tail_le`, `integral_head_mul_tail_pow_le`, `setIntegral_head_on_large_tail_le`, `abs_log_norm_eulerHead_sub_le_of_one_le`, `norm_zeta_eq_head_mul_tail` |
| **3.** Why is `t log n` not a generic phase past Vinogradov's degree? | Its block coefficients lie on one curve `u ↦ (tΔ_1^j log u/2π)_j`, `u = x/h`, and they move monotonically, by at least `(j+1)!/(x+j+2)^{j+2}` per block. Blocks on a lattice `c + ℤ` number at most `(tj!/(2πX^{j+1}) + 2)(2η·2π(X+H+j+2)^{j+2}/(t(j+1)!) + 1)` on `[X, X+H]`: proportion `O(η)`. The binomial ceiling `2/(k+1)` bounds one block, not a family. | `question_three`, `fwdDiff_iter_log_dilate`, `logDiffMass_sub_succ`, `card_exotic_le`, `card_near_lattice_le` |
| **4.** What replaces `q`-factorization at the archimedean place? | The real scale `x/√|t|`. In depth, `u ↦ 1 + q₁u` is an exact homomorphism for `q₂ ∣ q₁` (so `q₁ ≥ √q`) and `q`-differencing is exact; at the height `h ↦ t log(1 + h/x)` is additive up to `|t|hh'/x²` and equals `th/x` up to `|t|h²/x²`. Both factor at the square root of the conductor; the height pays the quadratic Taylor term that vanishes `p`-adically. | `question_four`, `one_add_mul_mul_one_add_mul`, `mulChar_add_mul`, `log_one_add_defect_le`, `abs_log_one_add_sub_le` |
| **5.** Is an atypical bounded return possible at a right zero, and what does its tail look like? | Its tail is forced: along a bounded return the tail tends to `ζM_y`, which vanishes at the zero, while the head tends to `E_y(ρ) ≠ 0`, and `|ζ − E_y|` at the transported zero tends to `|E_y(ρ)|`. Every return at a zero is tail-bad at every cut with tolerance `m/4` independent of the cut, and such returns have density zero. On the universal disc about each point, nonvanishing targets are approached at positive density, targets with a zero only at heights tail-bad at every cut. Existence is open: it is B89, the exact input of AAL. | `question_five`, `eulerTail_eq_zero_iff`, `tendsto_zero_tail_of_phaseReturn`, `zetaReturnSet_subset_eulerDiscTailBadSet`, `exists_returns_tailBad_and_rare`, `tail_recurrence_dichotomy` |
| **6.** Which certificates in non-returning coordinates survive past `Re s = 1`? | Not Euler coordinates: on `Re s > ½`, `Σ_p|1 − E_p(s)| < ∞ ⟺ Re s > 1`, and no family within summable distance of the Euler factors does better. What survives is the head–tail certificate: any factorization is a decomposition with rank-one kernels, and the tail coordinate is Schur exactly where `|S|` is at most the head. Past the abscissa the certificate question is the size of the tail. | `question_six`, `summable_one_sub_scatteringFactor_iff`, `not_summable_of_summable_sub`, `certificate_of_factorization`, `headTail_certificate`, `norm_tailCoordinate_le_one_iff` |

## 6. Pillar theorems

All are unconditional; the answer theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

| Theorem | Lean | Module |
|---|---|---|
| Dirichlet bound, group laws, corners, rank one | `firstReturn_le_pow`, `IsReturn.add`, `IsReturn.nat_mul`, `IsAntiReturn.two_mul`, `firstReturn_le_of_rankOne` | `TheFirstReturn` |
| The first return is an extreme value | `abs_harmonicDefect_sub_le`, `log_norm_zeta_ge_of_isReturn`, `exists_spike_le_pow`, `firstReturn_lower`, `tendsto_firstReturn_primes` | `TheFirstReturnIsAnExtremeValue` |
| The precision law | `criticalDefect_le_of_isReturn`, `eventually_exp_rpow_lt_firstReturn`, `eventually_exp_sqrt_lt_firstReturn`, `the_precision_law` | `ThePrecisionLawOfTheFirstReturn` |
| Proportional saving is a heavy first return | `exists_heavy_return_of_defect_lt`, `defect_le_of_heavy_return`, `saving_of_no_heavy_return`, `no_heavy_return_of_saving`, `lt_firstReturn_of_saving` | `ProportionalSavingIsAHeavyFirstReturn` |
| The fade is forced | `eventually_abs_harmonicDefect_sub_le`, `tendsto_harmonicDefect`, `logLog_le_of_isWeakReturn` | `TheFadeOfAReturn` |
| Head–tail decoupling | `smooth_mul_rough_injective`, `indexed_meanValue`, `integral_head_mul_tail`, `abs_conditional_second_moment_sub_le`, `norm_integral_head_sq_mul_tail_le` | `TheTailDecouplesFromTheHead` |
| Gaussian conditional moments | `headPoly_pow`, `powNorm_le`, `integral_head_mul_tail_pow_le`, `setIntegral_head_on_large_tail_le` | `TheConditionalMomentsOfTheTail` |
| Arithmetic smooth–prime second moment | `integral_balancedHead_primeTail_sq_le`, `setIntegral_balancedHead_on_large_primeTail_le` | `TheSmoothPrimeMeanSquareHasAnArithmeticCost` |
| Rectangular arithmetic moments | `integral_rectangular_head_tail_le`, `integral_rectangular_head_prime_tail_pow_le`, `setIntegral_rectangular_head_on_large_prime_tail_le`, `integral_rectangular_full_prime_tail_pow_le` | `TheRectangularMomentsHaveAnArithmeticCost` |
| Unrestricted smooth-head moments | `integral_smooth_head_prime_tail_pow_le_primitive`, `primitiveHeadCost_le_first_moment`, `integral_full_smooth_head_prime_tail_pow_le`, `setIntegral_smooth_head_on_large_prime_tail_le` | `TheSmoothHeadNeedsNoDyadicRestriction` |
| Normalized arithmetic moments | `integral_head_sq_ge_primitiveSupportHeight`, `normalized_prime_tail_moment_le_primitive`, `normalized_large_prime_tail_mass_le`, `normalized_full_smooth_prime_tail_moment_le` | `TheNormalizedMomentsRetainTheArithmeticCost` |
| The head is frozen | `abs_log_norm_eulerMollifier_sub_le`, `abs_log_norm_eulerHead_sub_le_of_one_le`, `norm_zeta_eq_head_mul_tail` | `TheHeadIsFrozenAtItsResolution` |
| The tail carries the zero | `eulerTail_eq_zero_iff`, `tendsto_eulerTail_of_phaseReturn`, `tendsto_zero_tail_of_phaseReturn`, `zetaReturnSet_subset_eulerDiscTailBadSet`, `exists_returns_tailBad_and_rare` | `TheTailOfAReturnCarriesTheZero` |
| The recurrence dichotomy of the tail | `exists_tailBad_of_zero`, `zetaTargetReturnSet_subset_eulerDiscTailBadSet`, `tail_recurrence_dichotomy` | `TheRecurrenceDichotomyOfTheTail` |
| The jet moves | `fwdDiff_iter_log_dilate`, `logDiffMass_sub_succ`, `card_near_lattice_le`, `card_exotic_le` | `TheJetOfTheLogarithm` |
| Depth exact, height approximate | `one_add_mul_mul_one_add_mul`, `mulChar_one_add_mul_add`, `mulChar_add_mul`, `log_one_add_defect_le` | `TheDepthAspect` |
| The abscissa wall; head–tail certificates | `summable_one_sub_scatteringFactor_iff`, `not_summable_of_summable_sub`, `headTail_certificate` | `EulerCoordinatesStopAtTheAbscissa` |
| The comb | `dist01_mul_le`, `dist01_le_of_isReturn`, `card_comb_le`, `comb_inequality` | `TheCombOfAReturn` |
| The questions and the tools | `question_one` … `question_six`, `the_tools` | `TheQuestionsOfTheField` |

For arbitrary smooth rows `A` and prime columns `B>y` in `(X,2X]`, coefficients of modulus at most one,
all centers `U` and `T>0`, the actual product polynomial satisfies
`∫_[−T,T]|R(U+t)|²|B(U+t)|²≤(5π/2)(T #A #B+8X² #A²)`.
Summing compatible integer differences cancels the gcd cost; a triangular Fourier majorant transfers
the count without a harmonic logarithm. Restricting head mass to `|B|≥V` costs `V⁻²`.
This gives a sparse-head arithmetic error, without a prime-density saving or control of infinite exceptional tails.

For smooth rows in `(X,2X]` and rough columns at most `Z`, write `R_j=Σ|r|^j`,
`B₂=Σ|b|²`, and assume `|b|≤K`. Every centered mean square is at most
`(5π/2)(T R₂ B₂+4Z(X+Z)R₁²K²)`. For a prime tail below `Y` with `|b|≤1`,
its `k`th power has coefficient supremum `≤k!` and squared coefficient sum
`≤k!B₂^k`. Thus its head-weighted `2k`th moment is at most
`(5π/2)(T R₂ k!B₂^k+4Y^k(X+Y^k)R₁²(k!)²)`.
The literal smooth interval and prime tail satisfy this bound; restriction to
`|tail|≥V` divides it by `V^(2k)`. Sparse heads can improve the finite-moment
range through this arithmetic error. Exceptional infinite tails remain open.

For an arbitrary finite smooth head, the dyadic restriction disappears. Its intrinsic
cost is `C(A,r,Z)=Σ_{m,n∈A}|r_m r_n|Z(2Z+m/gcd(m,n)+n/gcd(m,n))`.
Every centered rough-tail mean square is at most `(5π/2)(T R₂ B₂+C K²)`.
With `M₁=Σm|r_m|`, the simpler envelope is `C≤2Z²R₁²+2ZR₁M₁`.
Prime-tail powers substitute `Z=Y^k`, `K=k!` and diagonal `k!B₂^k`;
large-tail head mass divides by `V^(2k)`. The generic logarithmic-energy
transfer is public and applies to arbitrary positive integer supports.

Reduced ratio height `H(A)=max(1,max_{m,n∈A}m/gcd(m,n))` controls actual
head mass: `∫_[−T,T]|R(U+t)|²≥(2T−52H(A))R₂`. It is unchanged by a
common positive integer dilation. At `T≥52H(A)` and `R₂>0`, division by
actual head mass gives normalized `2k`th moment at most
`(5π/2)(k!B₂^k+C(A,r,Y^k)(k!)²/(T R₂))`, with
`C(A,r,Z)≤2Z(Z+H(A))R₁²`. Normalized large-tail mass pays `V^(−2k)`.
For the unit full smooth head below `M≥1`, the error inside parentheses
is at most `2Y^k(Y^k+M)#A(k!)²/T` when `T≥52M`.

## 7. Tools

| Tool | Reaches | Stops at |
|---|---|---|
| Proportional non-alignment past Kronecker | B46 is exactly the absence of heavy returns of weight `1 − c/η` (and excludes heavy returns with `ηS + 2κ < cS`); proportional saving on a window bounds the first return of the column; the precision law converts every absolute saving into a first-return bound | constant precision in the dark range: the heavy first return there is the open problem |
| A moment past the last diagonal scale that sees smooth-number density | the comb: at a return the smooth integers lie on `exp((2π/t)ℤ)` with teeth `k√(η/8)`, and past `X ≍ t` the comb has density `O(δ)` | below `X ≍ t` the comb is not an interval structure; seeing it there is a count of smooth numbers in intervals of length `X/t` with polylogarithmic smoothness |
| Conditional mean values on Bohr sets | exact head–tail factorization of all conditional moments, Gaussian moments and large deviations of the tail | the Kronecker scale: the head resonator must be shorter than the height, `log max A + k log Z ≪ log T` |
| Arithmetic second moments for sparse smooth heads | every centered interval; error `8X² #A²` for balanced smooth–prime supports and bounded coefficients | prime-density savings, growing heads and infinite exceptional tails |
| Rectangular conditional moments | exact coefficient diagonal and error `4Y^k(X+Y^k)R₁²(k!)²` for bounded prime tails, uniformly in interval center | the displayed arithmetic error must be small relative to `T R₂ k!B₂^k`; infinite exceptional tails remain uncontrolled |
| A lower bound for atypical members of a Bohr set | nonvanishing tail shapes occur at positive density (universality); shapes with a zero only at tail-bad heights of density zero | a lower bound for tail-bad heights *at a zero*: that is B89 |
| A sum–product theorem for the height orbit | the comb is a multiplicative approximate group and, past `X ≍ t`, locally an interval structure; the comb inequality gives polynomial first returns at precision `≲ 1/k` | the comb has both structures, so sum–product inequalities do not exclude it; below `X ≍ t` it is the dark range |
| Agler-type certificates past the abscissa | head–tail certificates wherever the tail coordinate is Schur | Euler coordinates, prime by prime or perturbed summably, diverge on `½ < Re s ≤ 1` |

## 8. Test systems

| System | Behaviour | Lean |
|---|---|---|
| Curves, Golden, commensurable steps | rank one: the first return is bounded uniformly in the set and the precision; no dark range | `firstReturn_le_of_rankOne` |
| Rational primes | the first return tends to infinity with the length at every `η < 1` | `tendsto_firstReturn_primes` |
| Liouville twin | a visit of `−1` at `t` is a return at `2t`: the twin corner is reached no earlier than half the first return | `IsAntiReturn.two_mul`, `firstReturn_le_two_mul_of_antiReturn` |
| Rounded primes (PTT) | same weights, same diagonal moments and early orbit, exact return at `T` | `PrimeTorusTheory.diagonal_data_cannot_exclude_return` |
| Continuous Beurling systems (PTT) | no torus, no returns: non-alignment alone decides nothing | `PrimeTorusTheory.tendsto_continuousColumn` |
| Depth aspect, smooth moduli | exact `q`-differencing at half depth | `mulChar_add_mul` |
| Dirichlet polynomials (RAC) | no tail: zeros recur in every window | `RigidArithmeticOfCuts` |

## 9. Traps

| Trap | Truth |
|---|---|
| A return at a zero is a return of the primes | the primes return at positive density (RAC); at a zero `ζ` returns only at tail-bad heights, at every cut, on density zero |
| Typical aligned shifts see the zero | they are tail-good: `ζ ≈ E_y`, which is zero-free |
| Strong returns at constant precision are weak returns | the harmonic defect of a return at precision `η` is up to `η log log y`: the spike has exponent `1 − η` |
| A single binomial phase bounds what `t log` can save | it bounds one block; the jet moves along blocks and exotic blocks are isolated |
| Diagonal moments decide the tail | the rounded orbit has the same diagonal moments and early orbit and returns exactly (PTT) |
| The conditional law holds at every scale | the decoupling needs the head resonator shorter than the height: the Kronecker scale |
| Euler products certify past the abscissa, prime by prime or with perturbations | `Σ_p|1 − z_p| = ∞` on `½ < Re s ≤ 1` for every family within summable distance of the Euler factors |
| Head–tail certificates are free | they exist exactly where the tail coordinate is Schur: the tail-size question |
| Sum–product theorems exclude alignment | the comb has both structures |
| The head sees features of `ζ` at every scale | it is frozen below `1/log y` on `Re s ≥ 1` |
| Proportional saving is a statement about the whole column | it is the absence of heavy returns: a heavy subset can return early while the column's first return is late |

## 10. Open research topics

1. **The constant-precision exponent.** `κ(η) = liminf log log R(y, η)/log log y` and the dark-range exponent of
   `log log R/log y`. A Lean form of `|ζ(1 + it)| ≪ (log t)^{2/3}(log log t)^{1/3}` gives `κ ≥ 3/2` through the dictionary.
2. **The tail past the Kronecker scale.** Conditional moments when the head weight is longer than the height: tilted
   resonators, which should realize a product tilt `f_p` on the head with budget `Σ f_p² log p ≲ log T`, and their tail
   laws.
3. **The Bohr mean of `|ζ|²`.** With the sharp mean value theorem: `∫|R|²|ζ(σ + it)|²` with the gcd-twisted diagonal
   and its reading as a torus mean of `|R E_y|²` times the tail factor `Π_{p>y}(1 − p^{−2σ})^{−1}`.
4. **A bounded return at a right zero (B89).** Every such return is tail-bad at every cut with amplitude `|E_y(ρ)|`; at
   the Kronecker scale its conditional cost is a Gaussian large deviation; past it nothing is known.
5. **From isolated exotic blocks to a saving.** An inverse theorem for near-full Weyl sums at degree `k` and precision
   `1/k`, applied along the moving jet, would turn isolation into an averaged saving past Vinogradov's degree.
6. **An exact archimedean half depth.** A substitute for `1 + q₁ℤ` that avoids the defect `t h²/x²` along a tower of
   real scales.
7. **Certificates at typical heights.** Show the tail coordinate of `ζ(2s − 1)/ζ(2s)` is Schur on tail-good heights past
   the abscissa; block certificates on the `1`-line from the prime number theorem.
8. **Smooth numbers on the comb below `X ≍ t`.** The moment past the last diagonal scale: counts of `y`-smooth integers
   with `k` factors in intervals of length `X/t`.
9. **Heavy returns at the size curve.** The heavy first return at `y = L^{2K}`, weights `p^{−½}`: this is B46.

## 11. Criteria

**A contribution must:**
- reduce to the periodic flow at rank one, or state why it does not;
- see the start of the orbit, or state the blindness it proves;
- use integrality (unique factorization, the integer gap), since transfer alone is empty past Kronecker;
- pass the ceilings: not diagonal moments, not one word, not one polynomial phase, not the rounded orbit;
- be false on impure columns, Golden and heated kernels if it claims a sign, and fail on integer-norm systems through
  the amplitude;
- state its scale against the Kronecker scale, the resolution `1/log y` and the Vinogradov length, and say whether it is
  conditional on the head.

**The field has succeeded when** one of these holds: the constant-precision first-return exponent is determined; a
conditional tail law is proved at one moment past the Kronecker scale; a bounded return at a right zero is excluded in a
stated class or exhibited; or the heavy first return at the size curve (B46) is decided.

## 12. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | RHTower 9 (Sieve mean value and Mertens, Euler tail law, universality, strong recurrence, vertical bounds), PrimeTorusTheory 5 (chord, iterated differences, savings, misalignment), HTGeometry 3 (simultaneous Dirichlet, log separation), ArithmeticAuxiliaryDynamics 1 (phase returns), SignedSuccessorArithmetic 1 (cosine sums against `ζ`) |

| Neighbour | Interface |
|---|---|
| PrimeTorusTheory | the orbit at finite time, absolute savings, words, rounded orbit, energies; TAPO adds the head–tail split, the first return and the conditional law |
| ArithmeticAuxiliaryDynamics | phase returns and bounded translates; TAPO says what the tail of such a return is |
| RigidArithmeticOfCuts | the tail fails at a zero; returns of the primes at positive density |
| RHTower (universality, Carlson tail, recurrence) | Euler tail law and Voronin on discs; TAPO reads the zero-target half as a tail-bad law at every cut |
| ArithmeticPositivityTheory | single-height escape: under RH coherent peaks at aperture `a` lie above `exp(c e^a)`; TAPO's precision law gives this bracket unconditionally at polynomial precision |
| SquareRootThreshold | Kronecker realization, isolated-zero visibility |
| ArithmeticInnerFunctionTheory | the one-dimensional causal theory of the half-plane; TAPO is its many-prime, single-height complement |
| twin-prime, SignedSuccessorArithmetic | the harmonic comparison `Σ_p cos(t log p)/p ≈ log|ζ(1 + 1/log N + it)|` |

## 13. Big picture

The dark range is where the head can no longer be prescribed and the tail is not yet controlled. TAPO separates what is
forced there from what is not.

Forced: the first return is an extreme value of `ζ` next to the `1`-line, and precision buys length; at polynomial
precision the bound RH gives at constant precision is a theorem. Unique factorization decouples the tail from the head,
so below the Kronecker scale the tail is Gaussian conditionally on any head, moment by moment. The head is frozen below
its resolution and never vanishes, so a zero is carried by the tail at every cut: along a bounded return the tail
converges to `ζM_y`, and every return at a zero is tail-bad at every cut. The jet of `t log` moves, so the binomial
obstruction is isolated along blocks; depth factors exactly where the height factors approximately; Euler coordinates
stop at the abscissa and certificates past it are head–tail certificates.

Not forced: the constant-precision first return in the dark range, the tail law past the Kronecker scale, and whether a
bounded return at a right zero exists. Each is located precisely. The first is the extreme-value problem of `ζ(1 + it)`
at the weights `1/p` and the heavy first return (B46) at the weights `p^{−½}`; the second needs a head weight longer than
the height; the third is B89, and its tail is known: tail-bad at every cut, by the amplitude `|E_y(ρ)|`.
