# ArithmeticKreinLangerTheory (AKL)

Namespace `GaloisForLFunctions.ArithmeticKreinLangerTheory`; umbrella `ArithmeticKreinLangerTheory.lean`; 21 modules. Every theorem is unconditional. RH appears only inside equivalences, and finite off-line support (`FiniteOffLine`, `negIndex zetaKernel < ⊤`) only as a stated hypothesis. 12 modules end with `#print axioms` lines.

## 1. Motivation

HeckeKreinToeplitz (HKT) made RH the statement `κ(K_ζ) = 0` for one Hermitian kernel on `Γ = ℚ_{>0}`. Over `𝔽_q` the corresponding index is computed from local data in two steps. Riemann–Roch bounds it by the genus, and a count (Stepanov's auxiliary polynomial) brings it to zero. AKL studies the local-to-global map in between. It asks which restrictions to towers decide the index, what tower-supported constituents can carry, what form the one global law must take, what produces such a law, and where the parity twins enter. Each theorem either computes the index from local data or proves that a class of local data cannot decide it.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Tower restriction | `k ∘ zpowersHom G u` | the kernel on the cyclic subgroup `⟨u⟩` |
| Quotient character, torsion aliasing | `quotChar`, `IsTorsionAliased` | `χ/ψ`; `χ = ψ` on a finite-index subgroup |
| Nodes, weights, outer node | `node`, `nodeWeight`, `outer`, `outerNode` | `χ_j, χ_j†` with `ω_j, ω̄_j`; the node of modulus `> 1` at `u` |
| Tower-faithful spectrum | `IsTowerFaithful χ u` | each character non-unitary at cofinitely many towers; distinct nodes agree at finitely many |
| Axis-supported kernel | `IsAxisSupported` | kernel on `ℤ^S` vanishing off the coordinate axes |
| Local constituent | `poissonKernel`, `eulerKernel p`, `primeConstituent p`, `localAssembly` | `r^{|n|}`; `L_p(n) = log p·p^{−|n|/2}`; `log p·δ₀ − L_p`; `Σ_s a_s(δ₀ − r_s^{|n_s|})` |
| Waves | `card_le_of_bounded_sub_waves` | terms `Σ a_i v_i^n` subtracted from a count `k(u^n)` |
| Twin | `twistChar`, `shiftChar τ`, `flipChar E` | `ω·χ`; vertical shift `u ↦ u^{iτ}`; sign flip at a prime set `E` |
| Quadratic twist, base change | `quadTwist`, `baseChange`, `twistCount` | `β ↦ −β`; `β ↦ β^n`; count of the twist of the base change |
| Parity classes | `parityCount`, `oddClassSum`, `harmonicExp` | Liouville classes `{λ = ±1}`; `O(t) = Σ_{λ=−1} e^{−nt}/n`; `H(t) = Σ e^{−nt}/n` |
| Consecutive tower | `consecutiveRatio n` | `(n+2)/(n+1)`, scale `→ 0` |
| Blind primes of `ζ` | `zetaBlindPrimes` | primes where two right-zero characters agree |
| Hyperelliptic trace kernel | `hypTraceKernel f` | `n ↦ Σ_ω (ω/√q)^n` for `y² = f(x)` |
| Function-field prime kernel | `primeKernelFq N`, `poleVec`, `divVec Q` | Weil prime kernel on monic polynomials of degree `≤ N`; `|f|^{−1/2}`; its restriction to multiples of `Q` |
| Chebyshev ratio | `logChebRatio`, `chebWeight` | `log((30n)! n!/((15n)!(10n)!(6n)!))`; `g(a) ∈ {0, 1}` |
| Pole of the Weyl sum | `poleParameter D i` | `Re = −½ + log|β_i|/log q` |

External: `negIndex`, `pairKernel`, `reflectChar`, `logChar`, `zeroChar`, `zetaKernel`, `orbitKernel`, `traceKernel`, `compress`, `hat` (HeckeKreinToeplitz); `CurveDatum`, `goldenDatum`, `rightZeros` (ArithmeticCastelnuovoSeveri); `HeckeLattice`, `primeElt`, `scale`, `heckeLogScale`, `primeTorus_kronecker_dense` (HTGeometry); `collisionMassAfter`, `FiniteOffLine`, `riemannHypothesis_splitHyperelliptic`, `PolarConfinement` (RHTower).

## 3. Language

- Cyclic locality: positivity on every cyclic subgroup implies positivity. Tower locality: positivity on infinitely many towers of one fixed family implies positivity.
- Count: a bound on `k(u^n)` along a tower. Wave number: the least number of exponentials whose subtraction makes a count bounded.
- Ceiling: an inequality `κ ≤ F(local data, one law)`.
- Producer: a construction that yields a one-sided count without assuming it. Receiver: a statement equivalent to a count.
- Ledger: a vanishing auxiliary has size at least the counted mass times its multiplicity.
- Discriminant: Krein–Langer data with a node on the unit circle, two colliding nodes, or a zero weight.
- Geometric twin: a twin realized by a vertical shift of the zeta function.
- Fine tower: a cyclic subgroup whose generator has small log-scale.

## 4. Mechanisms

**A. Locality**
1. Neumann avoidance plus Dedekind: in a coset of the finite-index subgroup where one aliasing class is trivial, choose `u` outside every infinite-index coincidence subgroup. Then every node is off the circle, nodes merge only within aliasing classes, and a nonzero class weight is a negative square on `⟨u⟩`.
2. Tower faithfulness: if all but finitely many towers separate the pairs, each carries the whole index. Logarithmic spectra with incommensurable scales (`log p/log q ∉ ℚ`) are faithful: a pair aliases at ≤ 1 tower and is never unitary there.
3. Fine grids: a kernel continuous in `log` is decided by cyclic subgroups `⟨e^{s_n}⟩`, `s_n → 0`, by rounding points to the grid. Orbit kernels are continuous because zeros lie in the strip and the weights are summable. So consecutive-integer towers decide every orbit kernel, and two primes suffice because `p^a q^b` reaches arbitrarily small scales.
4. Nyquist at scale `t`: characters with `t|s_j − s_k| < 2π` are distinct at `u`, so fine towers resolve every finite family.
5. Attained depth: normalize a bounded tower by `R^n`, `R = e^{D·scale}`, and take Cesàro means against `w̄^n` with Tannery. The weight of the top nodes must cancel. A zero aliases with a given zero at ≤ 1 prime, and summable mass allows only finitely many disjoint cancelling sets.

**B. Local constituents**
6. Euler factors are Poisson kernels: `r^{|n|}` has form `(1−r²)Σ|h(k)|² + |h(N)|²`. Local positivity is twin-invariant.
7. Zero-or-infinity: on `ℤ^S`, `|S| ≥ 2`, diagonal translates of a negative family by large steps are orthogonal for an axis-supported kernel, so `κ ∈ {0, ∞}`. Tower-supported constituents vanish at the identity and are negative on `{0, e_p}`, so their assembly has `κ = ∞`. Finite nonzero index needs the archimedean factor.

**C. Counts and waves**
8. A bounded exponential sum has zero merged coefficient at every frequency of modulus `> 1`. So each outer node must be a subtracted wave, `κ ≤ m`, and the outer nodes attain it. A minimal count fixes the hyperbolic spectrum and the weights.
9. Continuity off the discriminant: a semicontinuous floor (attained on one family) meets the structural ceiling `κ`. Weights vanishing, nodes colliding with opposite weights, and coalescence onto the line each lower the index.

**D. Producers and parity**
10. Twist tower over `𝔽_q`: write `k = 2^j m` with `m` odd. The twist count at `(2^j, m)` is the curve's lower count at `k`, so upper counts on all twisted 2-power base changes give RH. One twist is not enough (split datum `±2, ±½`).
11. Parity form over `ℤ`: `J = H − 2O`, and the one-sided Liouville law becomes an upper count for the odd class alone. Over `ℤ` the blind spot of upper counts would be a real zero in `(½, 1)`, of which there is none.
12. Ledger: `Σ_{x∈T} m_x ≤ deg P` over `𝔽_q[X]`; `Σ_{p∈S} m_p log p ≤ log A` over `ℤ`. Stepanov gets multiplicity `≈ √q` from `x^q = x`. Binomials have multiplicity ≤ 1 above `√N`.
13. Divisibility is parity-blind: `θ(x) ≤ log lcm(odd class) ≤ ψ(x)`, a window of width `≤ 2√x log x`.
14. Geometric twins: one vertical shift is `−1` at ≤ 1 prime (unique factorization). By Kronecker, shifts converge to any unimodular completely multiplicative twist, so pointwise-closed shift-invariant statements contain every flip.
15. Compressions: the Frobenius characteristic polynomial annihilates the trace kernel and certifies nothing. Euler compressors `δ₁ − cδ_p` with `|c| ≤ p^{−½}` never vanish on the strip, so they are index-neutral.
16. Function-field ceiling: `P_N v = N v` exactly for the pole vector. With Schur's test, `D·1 − P_N ⪰ 0 ⇔ D ≥ N log q`. Multiples of `Q` give the second rung `N − deg Q`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Cyclic Hasse principle on every group | `exists_one_le_negIndex_zpowers`, `negIndex_eq_zero_of_forall_zpowers` | proved |
| No torsion aliasing ⇒ one cyclic subgroup carries `κ` | `negIndex_zpowers_eq_of_not_aliased` | proved |
| Coordinate towers fail inside KL; cyclic subgroups fail outside KL | `coordinate_locality_fails`, `cyclic_locality_fails_off_class` | proved |
| Tower Hasse principle; sharpness of both faithfulness clauses | `finite_towers_negIndex_ne`, `negIndex_eq_zero_of_posDef_on_infinitely_many`, `unitary_tower_defeat`, `aliased_tower_defeat` | proved |
| Logarithmic spectra are tower-faithful; arithmetic tower Hasse on primes | `isTowerFaithful_logChar`, `negIndex_eq_zero_of_posDef_on_infinitely_many_primes` | proved |
| Euler factors positive definite; zero-or-infinity; local assemblies have `κ = ∞` | `isPosDefKernel_eulerKernel`, `negIndex_eq_zero_or_top_of_isAxisSupported`, `negIndex_localAssembly_eq_top`, `rankOne_axis_pair` | proved |
| Riemann–Roch ceiling `2κ ≤ #β`; golden attains it | `two_mul_negIndex_traceKernel_le`, `golden_attains_ceiling` | proved |
| Quadratic twist keeps `κ`; one twist does not complete; twist tower ⇔ RH for curve data | `negIndex_traceKernel_quadTwist`, `one_twist_does_not_complete`, `unitary_iff_twistTower_upper`, `unitary_iff_twistedBaseChanges_upper`, `golden_battery` | proved |
| Continuity off the discriminant; three degenerations | `eventually_negIndex_eq_of_tendsto`, `vanishing_weight_drops_index`, `collision_drops_index` | proved |
| RH ⇔ both parity classes upper; ⇔ odd class upper; ⇔ `κ(K_ζ) = 0` | `riemannHypothesis_iff_parityClasses_upper`, `riemannHypothesis_iff_oddClass_upper`, `negIndex_zetaKernel_eq_zero_iff_oddClass_upper` | proved (equivalence) |
| `κ` = least number of exceptional waves; minimal count = outer nodes | `negIndex_eq_card_waves`, `minimal_waves_eq_outerNodes` | proved |
| Frobenius char poly annihilates trace kernel; Euler compressions index-neutral | `compress_traceKernel_charPoly`, `hat_euler_eq_zero_iff`, `negIndex_compress_euler` | proved |
| Fine towers decide and carry every orbit kernel; RH ⇔ consecutive towers positive; two-prime fine towers | `negIndex_orbitKernel_eq_iSup_fine`, `eventually_negIndex_fine_eq`, `riemannHypothesis_iff_zetaKernel_consecutive`, `negIndex_orbitKernel_eq_iSup_twoPrime_towers` | proved |
| Twin-invariance of tower faithfulness and the Hasse principle | `isTowerFaithful_twist`, `twin_finite_towers_negIndex_ne` | proved |
| Finite stratum: wave number, collision mass `2(κ + E)`, amplitudes `m_ρ|ĝ(γ)||ĝ(γ̄)|` | `waveNumber_collision_law`, `minimal_count_reads_multiplicities`, `collision_mass_from_minimal_count` | proved (on finite stratum) |
| Collision mass diverges ⇔ consecutive tower indices unbounded | `tendsto_collisionMass_iff_consecutive`, `bounded_heat_iff_consecutive_bounded` | proved |
| Finite stratum: ≤ `C(κ,2)` blind primes; non-blind tower carries `κ`; RH ⇔ one non-blind / infinitely many prime towers positive | `zetaBlindPrimes_finite_card_le`, `negIndex_zetaKernel_prime_eq`, `riemannHypothesis_iff_zetaKernel_prime_posDef`, `riemannHypothesis_iff_infinitely_many_zetaKernel_prime_posDef` | proved (on finite stratum) |
| Attained least real part ⇒ positive on finitely many prime towers; RH ⇔ infinitely many positive prime towers when attained | `finite_primes_posDef_of_attained_depth`, `riemannHypothesis_iff_infinite_primes_posDef_of_attained` | proved; non-attained infimum open |
| Stepanov bounds both Legendre parity classes; Chebyshev `Σ_{(n,2n]} log p ≤ n log 4` | `stepanov_parity_classes_upper`, `sum_log_prime_Ioc_le` | proved |
| Ledgers over `𝔽_q[X]` and `ℤ`; binomial caps; short-interval weakness | `sum_le_natDegree_of_vanishing`, `sum_mul_log_le_log_of_dvd`, `pow_le_of_dvd_choose`, `le_one_of_dvd_choose`, `log_choose_ge` | proved |
| Divisibility parity-blind at `√x` precision | `theta_le_log_lcm_oddPoints`, `abs_log_lcm_oddPoints_sub_theta_le` | proved |
| Weil in Stepanov's order for split hyperelliptic curves | `stepanov_order_hyperelliptic` | proved |
| Twin geometric on one tower, not on two, yes in the Bohr closure | `shiftChar_primeElt_zpow`, `shiftChar_eq_neg_one_subsingleton`, `exists_shiftChar_near_neg_one` | proved |
| Pointwise-closed shift-invariant sets contain the Liouville twin and every flip | `liouvilleTwin_mem_of_isClosed`, `unitaryTwist_mem_of_isClosed`, `flip_mem_of_isClosed` | proved |
| Function-field ceiling exact; second rung; window `≤ (|Q|/(|Q|−1)) log|Q|` | `atomFq_nonneg_iff`, `atomFq_two_negative_squares` | proved |
| Fine towers resolve every finite family | `exists_scale_injective_logChar` | proved |
| `ψ(x) ≥ 0.89x − O(log x)` by Chebyshev's ratio | `log_chebRatio_le_psi`, `psi_ge_of_chebyshev` | proved |
| `κ(traceKernel)` = #pole classes right of `Re s = −½`; confinement ⇔ twist tower | `negIndex_traceKernel_eq_card_rightPoles`, `polarConfinement_iff_twistTower_upper` | proved |

## 6. Tools

**Developed**
- Neumann avoidance `exists_mul_not_mem` and torsion-aliasing calculus.
- Tower faithfulness and its twin-invariance.
- Fine-grid rounding (`exists_tendsto_gram_grid`, `hermQuad_nonneg_of_fine_zpowers`, `eventually_le_negIndex_fine`); continuity of orbit kernels (`continuous_realOrbitKernel`).
- Wave calculus (`sum_coeff_eq_zero_of_norm_le`, `exists_waves_bounded`).
- Bohr–Cesàro coefficient extraction (`tendsto_cesaro_pow`, `tsum_weight_node_eq_zero_of_bounded`, `finite_of_disjoint_mass`).
- Poisson-kernel positivity identity `poisson_pair`.
- Schur's test with a positive eigenvector (`sum_mul_le_of_pos_eigenvector`, `atom_nonneg_iff`); exact Mertens over `𝔽_q[T]` (`powerSumW_one_eq`, `sum_primePower_weight_eq`).
- Ledgers over `𝔽_q[X]` and `ℤ`; Chebyshev weight identity (`log_chebRatio_eq`).
- Kronecker approximation of twins by vertical shifts (`exists_shifts_tendsto_unitaryTwist`).

**To build**
- A producer over `ℤ`: an auxiliary integer of controlled size whose multiplicity on the odd Liouville class grows like Frobenius multiplicity, giving the odd-class upper count at precision `x^{½+ε}`.
- A vanishing notion finer than divisibility that separates the odd class from the primes and prime powers at `√x` precision.
- A geometric parity twin over `ℤ` in the Bohr compactification of vertical shifts.
- An extension of the attained-depth law to a non-attained infimum of real parts.
- A finite ceiling for `ζ` from local data: since finite index is LH-deep, such a ceiling must contain an LH proof.

## 7. Open questions

1. What produces the odd-class upper count `O(t) ≤ (H(t) + Ct^{½−ε})/2`?
2. Is there a notion of vanishing at integers that sees Liouville parity and still yields a ledger inequality?
3. Does positivity on infinitely many prime towers imply RH without the attained-infimum hypothesis?
4. Does the second rung over `ℤ` correspond to the exact function-field rung, with `γ` as the archimedean defect?
5. Is there a selective statement that is neither pointwise-closed nor shift-invariant, carried by the pole and Gamma factor?
6. Can a count with finitely many exceptional waves be produced along one fine tower without zero information?

## 8. Traps

| Trap | Fact |
|---|---|
| Positivity on coordinate towers decides the index | Only for tower-faithful spectra; the `ℤ²` coordinate kernel has `κ = 2` and vanishes on both axes |
| Cyclic subgroups decide every kernel | Only inside the Krein–Langer class; the star kernel is positive on every cyclic subgroup and not on `ℤ²` |
| Assembling local constituents gives a finite index | Tower-supported assemblies on ≥ 2 towers have `κ ∈ {0, ∞}`; the archimedean factor is needed |
| Local positivity of Euler factors is selective | Every unitary twin of `L_p` is positive definite |
| Upper counts for a curve and its twist give RH | Split datum `±2, ±½`; the whole twist tower is needed |
| An over-`ℤ` producer must bound both parity classes | One class (the odd class, containing the primes) carries the whole law |
| Vanishing at the primes selects parity | Divisibility sees only `lcm`; primes, prime powers and the odd class are indistinguishable at `√x` precision |
| Binomial/Chebyshev producers can be sharpened to `√x` | Multiplicity ≤ 1 above `√N`; short intervals gain only `log(x/y)/log x` |
| The Liouville twin is a vertical shift | Only on one prime tower; in the Bohr closure, never exactly |
| Weil positivity selects through the prime weights | It is pointwise-closed, so shift-invariant data cannot select; the pole and Gamma terms carry the selectivity |
| Local Euler compressors can annihilate off-line pairs | For `|c| ≤ p^{−½}` they never vanish on the strip |
| Prime towers are as good as fine towers | Prime towers alias (coarse grids); fine towers carry the index for every orbit kernel |

## 9. Context

**Uses**

| Programme | Imports | What |
|---|---|---|
| HeckeKreinToeplitz | 26 | kernels, pairs, index formula, aliasing, compression, trace kernels, `K_ζ`, heat collisions, global law |
| RHTower | 9 | Stepanov counts, hyperelliptic RH, Liouville laws, Gelfond–Schneider, `ξ` orders, Weil–Kloosterman, infinite symmetry |
| HTGeometry | 2 | Kronecker density of prime phases |
| ArithmeticCastelnuovoSeveri | 2 | upper Lefschetz bounds, Riemann–Roch for `ℤ` |
| ArithmeticOfSquareRootPrecision | 1 | `log n!` bounds, Chebyshev transform |

**Used by**: AdelicKreinGeometry (`StableConformalSuccessors`), ArithmeticGaugeTheory (`FactorialRatiosHaveChebyshevPrecision`), umbrella.

| Neighbour | Relation |
|---|---|
| HeckeKreinToeplitz | foundation; AKL adds locality, local constituents, waves, producers |
| ArithmeticCastelnuovoSeveri | curve data and the golden datum; AKL adds the genus ceiling and the twist tower |
| ArithmeticEffectivityTheory | integrality lower counts for primes; AKL places them on the ledger and shows parity-blindness |
| SelectiveMultiscaleArithmeticPositivity, ArithmeticCountingPositivity | selection and flip battery; AKL shows pointwise-closed statements cannot select against flips |
| AdelicKreinGeometry | adelic continuation of the local-to-global index theory |

## 10. Big picture

AKL establishes that the local structure of the Weil kernel is fully understood and completely uninformative about its index. Restrictions to towers decide the index when the spectrum is faithful, and the logarithmic spectrum of `ζ` is faithful. Fine towers and two primes carry everything. Euler factors are positive. Yet tower-supported data alone have index `0` or `∞`, every local statement is blind to twins, and every pointwise-closed statement that survives vertical shifts also survives the Liouville twin. The index is a global invariant, and its value is set by one global law: an upper count for one parity class at square-root precision.

The function-field comparison is exact and shows where `ℤ` differs. Over `𝔽_q` the parity twin is geometric, Frobenius gives multiplicity `√q`, and the atomic ceiling has no error term. Over `ℤ` the twin is geometric only in the Bohr closure, integrality gives multiplicity one, and Euler's constant is the archimedean defect of the ceiling. What RH needs is a producer: an auxiliary object that vanishes on the odd Liouville class to growing order, in a sense finer than divisibility. None of the known constructions is of that kind.
