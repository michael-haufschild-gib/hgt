# Exact exponential rate of the recovery gaps

**Status:** Lean-complete (Stage 3-formalized). Every proven statement below — the angle, `0<ρ<1/16`, `lim δ_k^(1/k)=ρ`, `E_(2m)(w)=4^m t_m`, the root-sum bounds, the log-convexity and moment-measure consequences, the explicit equilibrium measure (probability, potential conditions, derivative, energy minimality and uniqueness), `∫t²dμ`, `A`, and `S_m/m→A` — is proved in Lean; axioms `propext`, `Classical.choice`, `Quot.sound` only. The Lean route replaces the cited Balogh–Bertola asymptotic by a self-contained argument (Jensen lower bound against the arcsine law, block products of scaled Chebyshev polynomials for the upper bound, Jensen against `(1+δcos2θ)/π` for `S_m/m`). Originally: paper proof using classical weighted potential theory. This attacks the actual unknown sequence rather than adding operator infrastructure. It does not settle log-convexity or existence of a moment measure. Priority of this specific application is unestablished.

Let δ_k be the actual physical recovery gap at weight k+1. There is a unique θ∈(0,π/2) satisfying

`2(π−θ)=3π sin θ`.

Put b=cos θ and

`ρ = (b²/16) exp((2/π) ∫₀^(π/2) log(1−b cos s) ds)`.

Then `0<ρ<1/16` and

`lim_(k→∞) δ_k^(1/k)=ρ`.

If the gaps are log-convex, their successive ratios increase to ρ. If γ_k=(δ_k/δ_0)² has a compactly supported probability representing measure, the largest point in its support is exactly ρ². These are necessary consequences; existence and log-convexity remain open.

## Proof of the rate

For m≥1 let T_m be the monic degree-m minimizer of max_(r∈[0,1/4]) W(r)^m|T_m(r)|, where W(r)=1−√(1−4r), and let its norm be t_m. The weighted alternation/interpolation argument in [coefficient duality](chronological-weighted-coefficient-duality.md) gives distinct roots r_i∈(0,1/4) and

`δ_(m−1)=t_m/S_m`, where `S_m=Σ_i r_i`.

Change variables r=(1−t²)/4. The even monic polynomial

`P_(2m)(t)=(-4)^m T_m((1−t²)/4)`

has weighted norm 4^m t_m on [−1,1] for the fixed weight w(t)=√(1−|t|), raised to degree 2m. Conversely every even monic polynomial of degree 2m has this form. Averaging any monic polynomial with its reflection preserves monicity and cannot increase this even weighted norm. Consequently

`E_(2m)(w)=4^m t_m`,

where E_n(w) is the unrestricted monic weighted Chebyshev norm with weight w^n.

The potential on (−1,1) is Q(t)=−½log(1−|t|). The endpoint singularity must be handled before applying the whole-line support formula. The following extension supplies that step.

Define I(b)=∫₀^(π/2) (1−b cos s)^(-1) ds. It is continuous and strictly increasing for 0<b<1, with endpoints π/2 and +∞. Hence I(b)=3π/2 has exactly one solution. Substitution y=tan(s/2) gives

`I(b)=(π/2+arcsin b)/√(1−b²)`.

Writing b=cos θ gives the stated equation for θ. Alternatively its left side minus right side has strictly negative derivative on (0,π/2), with opposite endpoint signs.

Choose a with b<a<1. On [0,a] keep q(t)=−½log(1−t); beyond a extend by its quadratic Taylor polynomial at a. Call the resulting function q̃. It is C² on [0,∞), nonnegative, and has q̃(0)=0. Its derivative is positive, its second derivative is positive, and t q̃'(t) is strictly increasing. It grows quadratically. Since q'''(t)>0, Taylor's integral remainder gives q̃≤q on [a,1). On [0,a] they agree.

The classical support theorem for the whole-line weight exp(−q̃(|t|)) gives support [−b,b]: its endpoint equation is

`(2/π)∫₀^(π/2) b cos s q̃'(b cos s) ds=1`,

which reduces to `(I(b)−π/2)/π=1`. Its equilibrium measure μ is therefore supported where q̃=q. For every probability measure ν on [−1,1], the weighted energies satisfy

`I_Q(ν)≥I_q̃(ν)≥I_q̃(μ)=I_Q(μ)`.

Thus μ also minimizes the original compact-interval problem, and its modified Robin constant is unchanged. The interval F-functional now gives

`C=exp(−F_Q)=(b/2) exp((1/π)∫₀^(π/2) log(1−b cos s) ds)`.

The support equation and F-functional formulas used here are stated in [Révész–Sarantopoulos, §2, equations (2.10), (2.14)–(2.17)](https://www.renyi.hu/~revesz/harrisfinal.pdf). The extension above verifies their whole-line hypotheses instead of silently applying them at the singular endpoints.

For the continuous admissible compact weight w, the classical weighted Chebyshev limit is E_n(w)^(1/n)→exp(−F_Q). See [Balogh–Bertola, §1.1 and §3, Proposition 3.1/Theorem 3.1, p=∞](https://arxiv.org/pdf/0910.4223). The twice differentiable hypothesis in their finite-p comparison lemma is not needed for this p=∞ statement. Hence t_m^(1/m)→C²/4=ρ. The displayed integral is negative, giving 0<ρ<b²/16<1/16.

It remains to show the penultimate-coefficient normalization does not change this rate. No root-distribution theorem is needed. Always S_m<m/4. If S_m≤1/8, then positivity of the roots and the elementary product inequality ∏(1−x_i)≥1−Σx_i for x_i∈[0,1] give

`t_m ≥ |T_m(1/4)| = 4^(−m)∏(1−4r_i) ≥ ½·4^(−m)`.

This contradicts t_m^(1/m)→ρ<1/16 for all sufficiently large m. Thus eventually 1/8<S_m<m/4; consequently log(S_m)/m→0. Taking logarithms in δ_(m−1)=t_m/S_m proves the rate, including the harmless index shift.

## Consequences for the hard problem

The equilibrium measure also has an explicit positive construction, giving a second check of the selected support. Set

`H(a)=(I(a)−π/2)/π`, for 0≤a≤b.

Then H(0)=0, H(b)=1, and H'>0. Let ν_a be the arcsine probability measure on [−a,a]. The equilibrium measure is

`μ=∫₀^b ν_a H'(a) da`.

Here is a direct verification. If J_n=∫₀^(π/2)cos^n s ds, expansion of I gives H'(a)=π^(-1)Σ_(n≥0)(n+1)J_(n+1)a^n. The Wallis recurrence implies (n+1)J_nJ_(n+1)=π/2. Termwise integration, justified on compact subintervals of [0,1), therefore yields the Abel identity

`∫₀^x H'(a)/√(x²−a²) da=1/(2(1−x))=Q'(x)`.

The arcsine potential is constant inside its interval and has derivative −1/√(x²−a²) for x>a>0. Thus U^μ+Q has derivative zero on (0,b) and strictly positive derivative on (b,1); symmetry handles the negative half. Its potential is continuous: the displayed mixture has density O(1+|log|x||) near zero and bounded density away from zero, hence an L² density; convolution with the locally L² logarithmic kernel is continuous. The weighted potential conditions characterize the equilibrium measure. This verifies support and positivity without identifying μ with the recovery moment measure.

Since the second moment of ν_a is a²/2, integration by parts gives

`∫t² dμ(t)=b²/2−∫₀^b aH(a) da=1−b/π−3b²/4`.

For the last equality, substitute a=sin u in ∫aI(a)da and use I(b)=3π/2. Consequently the mean root location in the original r-coordinate is

`A=b/(4π)+3b²/16`.

More precisely, `S_m/m→A`. To justify this additional asymptotic, the monic even weighted minimizers have real roots in (−1,1), so their normalized root-counting measures are compactly supported. Every subsequential limit has the same harmonic polynomial moments as μ by [Balogh–Bertola, Corollary 2.1, p=∞](https://arxiv.org/pdf/0910.4223). Apply this to Re(z²), then use r=(1−t²)/4. No stronger asymptotic for E_(2m)(w)/C^(2m) follows from this argument; in particular a constant-prefactor formula for δ is still open.

If w_k=δ_(k+1)/δ_k is nondecreasing, its proved bound w_k≤1/4 gives a positive limit L. Cesàro averaging log w_k in log δ_n shows L=ρ. In particular every w_k must be at most ρ; any exact violation disproves global log-convexity.

For a compact probability moment sequence, the nth root of the nth moment tends to the largest support point: the upper bound is immediate, and positive mass in every neighborhood below that point gives the lower bound. Applied to γ_n, this forces that point to be ρ². Therefore the scaled sequence γ_n/ρ^(2n) must satisfy every Hausdorff finite-difference inequality if a measure exists. This is a stronger concrete test than unspecified compact moment positivity.

**Open:** prove all these inequalities or find an exact violation; obtain an actual representing measure; derive stronger than exponential asymptotics. The equilibrium measure μ in the proof is a distribution of approximation-polynomial zeros. It is not the sought representing measure for the recovery gaps.

## Lean formalization

Modules in `formal/GaloisForLFunctions/HTGeometry/` (`ArcsineLogIntegral`, `GaussianFrullaniLogKernel`)
and `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/` (the rest), wired into `HTGeometry.lean`.

| Card statement | Lean declaration | Module |
|-|-|-|
| Unique `θ ∈ (0,π/2)` with `2(π−θ)=3π sin θ`; `b = cos θ ∈ (0,1)`; `I(b)=3π/2` | `existsUnique_recoveryAngle`, `recoveryAngle_eq`, `recoveryEdge_mem`, `recoveryI_edge` | `CubicRecoveryRateConstants` |
| `I(b)=(π/2+arcsin b)/√(1−b²)` (and `(π−θ)/sin θ`) | `recoveryI_eq_arcsin`, `recoveryI_cos` | `CubicRecoveryEquilibriumMeasure`, `CubicRecoveryRateConstants` |
| `0<ρ<b²/16<1/16` | `recoveryRateFun_bounds`, `recoveryRate_bounds` | `CubicRecoveryRateConstants` |
| Lower bound `t_m ≥ ρ(b)^m` for every `b∈(0,1)` (Jensen against the arcsine law) | `recoveryRateFun_pow_le`, `recoveryRate_pow_le`, `ae_jensenIntegrand_le` | `CubicRecoveryRateLower` |
| Upper bound `t_m ≤ 2^K 4^(⌊m/K⌋+1) ρ^m` (block Chebyshev products at equal-`H`-mass nodes) | `cubicChebyshev_norm_le`, `sum_log_arcsineGauge_le`, `abs_eval_chebyshevBlock_le` | `CubicRecoveryRateUpper` |
| Equilibrium inequality `∫_0^b log g(a,t)H'(a)da ≤ log C − ½log(1−t)`, equality for `t ≤ b`, strict for `t > b`; `C²/4=ρ` | `recoveryMixturePotential_le/_eq/_lt`, `recoveryCapacity_sq_div_four` | `ArcsineMixturePotential` |
| `t_m^(1/m) → ρ` | `tendsto_cubicChebyshev_norm_rate` | `CubicRecoveryExponentialRate` |
| `E_(2m)(w)=4^m t_m` (even monic reduction, attained by `(−4)^m T_m((1−t²)/4)`) | `isLeast_evenWeightedNorm`, `four_pow_mul_le_evenWeightedNorm`, `evenWeightedNorm_evenChebyshevLift` | `CubicRecoveryEvenReduction` |
| `S_m<m/4`; `4^m t_m ≥ 1−4S_m`; eventually `1/8<S_m` | `one_sub_four_rootSum_le`, `eventually_rootSum_gt` | `CubicRecoveryExponentialRate` |
| **`lim δ_k^(1/k) = ρ`** | `tendsto_cubicGradedRecoveryGap_rate`, `tendsto_log_cubicGradedRecoveryGap` | same |
| Log-convex gaps: every `w_k ≤ ρ` and `w_k → ρ` | `cubicGradedRecoveryGap_ratio_of_monotone` | same |
| Representing measure of `γ_n`: largest support point `ρ²` | `cubicRecoveryMoment_support_max` | same |
| Hausdorff inequalities for `γ_n/ρ^(2n)` (measure on `[0,∞)`) | `cubicRecoveryMoment_hausdorff` | same |
| `H(0)=0`, `H(b)=1`, `H'=h>0`, `H'(a)=π⁻¹Σ(n+1)J_(n+1)a^n`, `(n+1)J_nJ_(n+1)=π/2` | `recoveryMass_zero`, `recoveryMass_edge`, `hasDerivAt_recoveryMass`, `recoveryDensity_pos`, `recoveryDensity`, `wallisJ_mul` | `CubicRecoveryRateUpper`, `CubicRecoveryEquilibriumMeasure`, `RecoveryDensitySeries` |
| Abel identity `∫_0^x H'(a)/√(x²−a²)da = 1/(2(1−x))` | `integral_recoveryDensity_div_sqrt` (integrated form `integral_arcsineExcess_mul_recoveryDensity`) | `CubicRecoveryEquilibriumMeasure`, `RecoveryDensitySeries` |
| `μ=∫_0^b ν_a H'(a)da` is a probability measure, atomless, supported on `[−b,b]` | `recoveryEquilibriumMeasure`, instance `IsProbabilityMeasure recoveryEquilibriumMeasure`, `recoveryEquilibriumMeasure_singleton`, `ae_recoveryEquilibriumMeasure_abs_le` | `CubicRecoveryEquilibriumMeasure`, `CubicRecoveryEnergyMinimizer` |
| Arcsine potential on/off support; `cos 2θ` moment | `integral_log_mul_cos_sub_of_abs_le`, `integral_log_mul_cos_sub_of_lt_abs`, `integral_log_mul_cos_sub_mul_cos_two` | `ArcsineLogIntegral` |
| `U^μ+Q` constant on `[−b,b]`, `>` and strictly increasing on `[b,1)`; derivative `0` on `(0,b)` and `1/(2(1−t))−∫_0^b h/√(t²−a²) > 0` on `(b,1)`; potential continuous | `recoveryEquilibrium_potential_eq/_lt`, `recoveryWeightedPotential_strictMonoOn`, `hasDerivAt_recoveryWeightedPotential_of_lt`, `hasDerivAt_recoveryWeightedPotential`, `deriv_recoveryWeightedPotential_pos`, `continuousOn_potential_recoveryEquilibriumMeasure` | `CubicRecoveryEquilibriumMeasure` |
| The potential conditions characterize the equilibrium measure: `μ` minimizes `I_Q(ν)=∫∫log(2/|x−y|)dνdν+2∫Qdν` over probability measures on `[−1,1]`, `I_Q(μ)<∞`, and the minimizer is unique | `recoveryWeightedEnergy_le`, `recoveryWeightedEnergy_lt_top`, `eq_recoveryEquilibriumMeasure_of_weightedEnergy_le` | `CubicRecoveryEnergyMinimizer` |
| Positive-definiteness of the log kernel (Frullani/Gaussian), equality case, moment determinacy | `frullaniLogKernel_eq`, `frullaniLogKernel_self`, `two_mul_frullaniEnergy_le`, `exists_gaussianMoment_eq_of_energy_le`, `eq_of_gaussianMoment_eq` | `GaussianFrullaniLogKernel` |
| `∫t²dμ = 1−b/π−3b²/4`; `A = b/(4π)+3b²/16` | `integral_sq_recoveryEquilibriumMeasure`, `recoveryRootMean_eq` | `CubicRecoveryEquilibriumMeasure` |
| **`S_m/m → A`** | `tendsto_rootSum_div`, `abs_rootMoment_sub_le` | `CubicRecoveryRootMean` |

The Lean proof does not use the card's extension `q̃` or the Balogh–Bertola citations; those
were steps of the original route through the classical whole-line theory.

**Verification.** `lake env lean` on each module: clean. `lake build` of the top modules: passed.
`#print axioms` for 28 capstones: `[propext, Classical.choice, Quot.sound]`.

