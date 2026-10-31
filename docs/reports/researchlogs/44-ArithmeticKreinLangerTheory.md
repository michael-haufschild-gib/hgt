# ArithmeticKreinLangerTheory: mathematical facts

Namespace `GaloisForLFunctions.ArithmeticKreinLangerTheory`. 21 modules. Continues HeckeKreinToeplitz.

## CyclicSubgroupsDecideTheKreinLangerClass (uses HKT LocalityFails…, StepanovCompressions…, WeilsIndex…; Mathlib CosetCover)
- Neumann avoidance: every coset of a finite-index subgroup contains an element outside finitely many infinite-index subgroups (coset-cover lemma).
- quotChar χ/ψ; torsion-aliased: χ, ψ agree on a finite-index subgroup (equivalence relation, reflection-invariant). Torsion-aliased ⇒ |χ| = |ψ| pointwise; χ torsion-aliased with χ† ⇒ χ unitary.
- Nodes χ_j, χ_j†, weights ω_j, ω̄_j; outward node at u = the one of modulus > 1.
- Cyclic Hasse principle (any group): p ⪰ 0 plus ≥ 1 pair (non-unitary χ, distinct nodes, nonzero weights) has a negative square on some cyclic subgroup ⟨u⟩. Proof: fix the aliasing class T of one node; Dedekind independence gives g with F(g) = Σ_T c_ν η_ν(g) ≠ 0; Neumann gives u ∈ gH avoiding all infinite-index coincidence subgroups; orient outward; a vanishing class weight would force F(u) = 0. Hence KL kernels positive on every cyclic subgroup are positive definite (negIndex_eq_zero_of_forall_zpowers).
- Separation: no torsion aliasing ⇒ one element u separates all 2κ nodes and ⟨u⟩ carries the whole index κ.
- Coordinate towers do not decide: on ℤ², h_{(2,1),i} + h_{(2,−1),−i} = 2i sinh(a log 2)(1 − (−1)^b) has index 2, vanishes on both axes and on b ∈ 2ℤ (torsion-aliased along axis 1 with cancelling weights, unitary on axis 2).
- Off the KL class even cyclic subgroups fail: star kernel δ₀ − ½Σ_{±e₁,±e₂,±(e₁+e₂)} is positive on every cyclic subgroup (restriction = 1, δ, or Laplacian) but has a negative square on {0, e₁, e₂, e₁+e₂} (form −1).

## TowerFaithfulSpectraAreDecidedByAlmostEveryTower (uses RHTower GelfondSchneider)
- Tower-faithful spectrum for towers u_t: each character non-unitary at all but finitely many towers; distinct nodes agree at finitely many towers.
- Tower Hasse principle: tower-faithful KL kernel ⇒ all but finitely many towers carry the whole index κ; with infinitely many towers κ(k) = κ exactly; positive on infinitely many towers ⇒ κ = 0.
- Sharpness: a non-unitary χ unitary on a tower set S gives h_{χ,i} of index 1 invisible on S (vanishes there); two characters agreeing on S give h_{χa,1} + h_{χb,−1}, invisible on S, with a negative square on some cyclic subgroup.
- Logarithmic spectra u ↦ e^{sℓ(u)}, Re s ≠ 0, are tower-faithful for towers with nonzero pairwise incommensurable scales: never unitary, two distinct nodes agree at ≤ 1 tower.
- log p/log q irrational ⇒ prime towers incommensurable. Arithmetic tower Hasse: on ℚ_{>0}, p ⪰ 0 plus pairs of logarithmic characters with Re s_j ≠ 0, positive on infinitely many prime towers ⇒ κ = 0.

## LocalConstituentsMeetOnlyAtTheIdentity (uses HKT Rotation…, TheMargin…)
- Poisson kernel r^{|n|} (0 ≤ r ≤ 1) positive definite on ℤ: form = (1 − r²)Σ_{k<N}|h(k)|² + |h(N)|² (geometric identity per pair).
- Euler-factor kernel L_p(n) = log p · p^{−|n|/2} positive definite; unitary twins positive definite (local positivity is twin-invariant). Prime constituent on ⟨p⟩: log p δ₀ − L_p (vanishes at identity).
- Zero-or-infinity law: on ℤ^S, |S| ≥ 2, an axis-supported kernel has κ ∈ {0, ∞} (diagonal translates by large steps are mutually orthogonal).
- No finite set of places has finite index: Σ_{p∈S} a_p(δ₀ − r_p^{|n|}) on ℤ^S (|S| ≥ 2, a, r > 0) has κ = ∞ (negative on {0, e_p}). Finite nonzero index needs a constituent off the towers: the archimedean factor.
- One tower (ℤ): every kernel is axis-supported and a single pair has index 1 (as over 𝔽_q, one Frobenius tower).

## TheTwistTowerCompletesTheUpperCount (uses ACS UpperLefschetzBoundsAreBlindOnlyToRealZeros)
- Riemann–Roch ceiling: 2κ(traceKernel) ≤ #eigenvalues (= 2g); reflection maps outer eigenvalues injectively to inner. Golden datum attains it (genus 1, κ = 1).
- Quadratic twist β ↦ −β: trace kernel twisted by (−1)^n, same index; N_k + N_k' = 2(q^k + 1) for odd k; N_k' = N_k for even k.
- One twist does not complete: split datum ±2, ±½ over q = 5 satisfies N_k ≤ q^k + 1 for itself and its twist, and is not unitary.
- Twist tower: twistCount(n, m) = count over 𝔽_{q^{nm}} of the quadratic twist of the base change to 𝔽_{q^n}. Unitary ⇔ ∃C: upper counts for all twists of 2-power base changes (k = 2^j m, m odd: the twist count is the lower count at k). The twist count is the point count of an actual datum.
- golden_battery: golden attains the ceiling, satisfies the upper count with C = 0, fails the twist tower for every C.
- Moral: an upper-count producer reaches the global law only with a parity symmetry on every base change; over ℤ the Liouville twist acts on prime constituents but not on the archimedean factor.

## TheIndexIsContinuousOffTheDiscriminant
- Lower semicontinuity attained: k_n → k₀ pointwise, κ(k₀) < ∞ ⇒ eventually κ(k₀) ≤ κ(k_n).
- Continuity off the discriminant: converging KL data (p_n → p₀, characters pointwise, weights → nonzero limits, limit separated at one element) ⇒ eventually κ = κ exactly.
- Three degenerations: vanishing weight (index 1 → 0), collision of two logarithmic pairs with opposite weights (s, s + 1/(n+1): index 2 → 0), coalescence onto the line (HKT).
- HKT receivers (height truncations, integer windows, shrinking atoms) add pairs monotonically and never cross the discriminant.

## TheParityFormOfTheGlobalLaw (uses RHTower LiouvilleExponentialSumOneSidedPower)
- Parity classes {λ = ±1} in [1, N]: sum N, difference L(N). RH ⇔ ∀δ both classes have upper count N/2 + C(N+1)^{½+δ}.
- J(t) = Σλ(n)e^{−nt}/n = H(t) − 2O(t), O = odd-class harmonic–exponential mass. RH ⇔ κ(K_ζ) = 0 ⇔ upper count for the odd class alone: O(t) ≤ (H(t) + Ct^{½−ε})/2 for small t.
- Contrast with 𝔽_q: there upper counts are blind to real outer eigenvalues (need the twist tower); over ℤ the blind spot is a real zero in (½, 1), which does not exist, so one class carries the law. Missing over ℤ: a producer for that class.

## TheIndexIsTheNumberOfExceptionalWaves (uses HKT GrowthReadsTheDepth…)
- Bounded finite exponential sum ⇒ merged coefficient zero at every frequency of modulus > 1.
- Wave ceiling: p ⪰ 0 + κ pairs separated at u; if ‖k(u^n) − Σ_{i<m} a_i v_i^n‖ ≤ M for n ≥ 0 then κ ≤ m (each outer node must be a wave).
- Attainment: subtracting the κ outer nodes with weights leaves a bounded count. Rigidity: a count bounded after exactly κ waves uses the outer nodes, one each, with the pair weights.
- negIndex_eq_card_waves: κ = least number of exceptional waves of a bounded count along a separating tower. For ζ on the finite stratum: ψ(x) − x minus finitely many x^ρ/ρ bounded by √x log²x; every finite count ceiling proves LH.

## CompressionsAreReceivers
- Over 𝔽_q the Frobenius characteristic polynomial Π(X − β_i) (coefficients from finitely many counts via Newton) annihilates the trace kernel outright (order-2g recurrence): spectral compression certifies nothing about |β|. Stepanov's polynomial vanishes on rational points (point side) and yields a count.
- Over ℤ the Euler compressor δ₁ − cδ_p has transform 1 − c p^{ρ−½}; it vanishes exactly on one vertical Nyquist progression (ρ − ½)log p ∈ log c⁻¹ + 2πiℤ.
- For |c| ≤ p^{−½} the transform is nonzero at every ρ in the open strip and its reflection, so Euler compressions keep the index κ exactly. Local Euler data cannot annihilate a pair: a producer must vanish at the primes, not at the zeros.

## FineTowersDecideEveryOrbitKernel (uses HKT ArchimedeanCompletion…, LindelofDeep…, BoundedIndexClosed…, FiniteIndexIsPositiveMinusFiniteRank)
- Fine grids decide continuous kernels on ℝ_{>0}: if t ↦ k(e^t) is continuous and forms on ⟨e^{s_n}⟩ (s_n → 0, s_n ≠ 0) are ≥ 0, all forms are ≥ 0 (round points to grids); every finite family's index is eventually attained on the fine grids.
- Orbit kernel t ↦ Σ_ρ e^{−t(ρ−½)}W_ρ is continuous (zeros in the strip, summable weights).
- Fine towers decide and carry the index of every orbit kernel on a tempered configuration (finite or infinite index); on the finite stratum every fine enough tower carries exactly κ.
- Consecutive-integer towers ⟨(n+2)/(n+1)⟩: κ(K_ζ) = sup of tower indices; RH ⇔ K_ζ positive definite on every consecutive-integer tower. Prime towers are coarse (spacing ≥ log 2) and alias; fine towers do not. Cyclic locality holds for arithmetic kernels with any number of pairs, via the archimedean place.
- Two primes contain fine towers p^a q^b with scales → 0; the two-prime law is the fine-tower law.

## LocalityIsTwinBlind
- Twin = unitary character ω acting by k ↦ ωk (Liouville, finite sign flips, vertical shifts u^{iγ}). Reflection commutes with unitary twists; ω·h_{χ,a} = h_{ωχ,a}; ω·p ⪰ 0.
- Tower faithfulness is twin-invariant; the tower Hasse principle holds verbatim for every twin. Locality cannot separate a kernel from its twins: selectivity must enter through a count or a carrier.

## TheCollisionMassIsTheWaveNumber (uses HKT HeatCollisions…, WeilKernelIsKreinLanger…; RHTower XiZeroCountingFunction, CompletedPrimeFluxFittingAttachment, WeilPhiDoobPrimeAtoms)
- K_ζ(u) = explicit-formula functional of the spline against its translate (pole − Λ-sum + Gamma): the count is prime-side.
- Cubic spline sees every right zero (nonzero weight); on the finite stratum K_ζ = on-line orbit kernel + one pair per right zero (Fin κ presentation).
- waveNumber_collision_law: finite index ⇒ ∃ tower ⟨u⟩: K_ζ(u^n) bounded after subtracting κ waves, only if ≥ κ waves; collision mass after small t = 2(κ + E).
- Minimal count reads multiplicities: amplitudes of a κ-wave count are m_ρ|ĝ(γ_ρ)||ĝ(γ̄_ρ)|; ξ-order = ζ-multiplicity in the strip; collision mass 2(κ + Σ(m_j − 1)) read from one minimal count.
- Off the finite stratum: collision mass → ∞ ⇔ consecutive-integer tower indices unbounded; bounded heat counts ⇔ bounded tower indices.

## FiniteSupportMakesAlmostEveryPrimeDecideZeta (uses HKT AllButFinitelyManyPrimes…)
- zetaBlindPrimes: primes where two right-zero characters agree on the generator. Finite stratum ⇒ #blind ≤ C(κ, 2).
- Non-blind prime tower carries the full index of K_ζ. On FiniteOffLine: RH ⇔ K_ζ positive on one non-blind prime tower ⇔ positive on infinitely many prime towers.

## AttainedDepthIsSeenByAlmostEveryPrime (uses ACS RiemannRochForZAndTheReflectedPrimePolarLedger; Mathlib Tannery)
- Cesàro means of c^n (|c| ≤ 1) → [c = 1]; disjoint pieces of a summable mass: only finitely many carry mass ≥ c > 0.
- Bohr coefficients along one tower: if the orbit kernel is bounded on u^n (scale u > 0) and D = max depth > 0, the total weight of zeros with node v (|v| = e^{D scale u}) vanishes (normalize by R^n, Cesàro against w̄^n, Tannery).
- A zero ρ₀ of maximal depth with nonzero weight: orbit kernel positive on only finitely many prime towers (alias sets of ρ₀ at different primes are disjoint; each positive tower must cancel W_{ρ₀}).
- For ζ: if the least real part is attained and < ½, K_ζ is positive on only finitely many prime towers. RH ⇔ positive on infinitely many prime towers, whenever the least real part is attained (contains the finite stratum). Open: non-attained infimum.

## IntegralityProducesLinearCounts (uses RHTower StepanovCharacterSum)
- Producer = construction giving a one-sided count without assuming it.
- Over 𝔽_q (q = s² odd, h squarefree, deg h + 5 ≤ s): Stepanov bounds both Legendre parity classes {h(x)^{(q−1)/2} = ±1} by q/2 + (deg h + 1)√q (curve and quadratic twist).
- Over ℤ: primes in (n, 2n] divide C(2n, n) ≤ 4^n ⇒ Σ log p ≤ n log 4 (linear precision); integer polynomials give the matching lower count. Global law needs precision x^{½+ε} for the odd class.
- One ledger: over 𝔽_q[X], Σ_{x∈T} m_x ≤ deg P; over ℤ, Σ_{p∈S} m_p log p ≤ log A. Stepanov: size ≈ ℓq/2, multiplicity ℓ ≈ √q via x^q = x ⇒ q/2 + O(√q). Chebyshev: size n log 4, multiplicity one.
- Binomial caps: p^m | C(N, k) ⇒ p^m ≤ N; above √N multiplicity ≤ 1. Short interval (x, x + y]: Σ log p ≤ log C(x + y, y) and log C(x + y, y) ≥ y log((x + 1)/y): no better than trivial up to log(x/y)/log x; the sieve constant 2 on x^ε intervals is out of reach.
- Producer problem over ℤ: auxiliary integer of controlled size with growing multiplicity on the counted primes.
- Divisibility sees prime powers not parity: vanishing on S ⊂ [1, x] ⇔ lcm S | A, log lcm S ≤ ψ(x). θ(x) ≤ log lcm(odd class ∩ [1, x]) ≤ ψ(x), difference ≤ 2√x log x: at square-root precision vanishing at primes, prime powers and the odd class are the same divisibility condition.

## StepanovsOrderOverTheFiniteField (uses RHTower HyperellipticRiemannHypothesis)
- hypTraceKernel K_f(n) = Σ_ω (ω/√q)^n for split squarefree odd-degree f, odd characteristic. √|E|·K_f([E:F]) = |E| − #{y² = f(x)}(E): the kernel is the normalized count error on the extension tower.
- Stepanov bounds both parity classes over even-degree extensions ⇒ character sums two-sided ⇒ |ω| ≤ √q; Gauss-sum product |Πω| = √q^{m−1} forces equality ⇒ K_f a sum of unitary characters ⇒ κ = 0 (Weil in Stepanov's order).
- Over 𝔽_q the producer acts on both parity classes because the twin is a curve; over ℤ one class suffices but the auxiliary must vanish finer than divisibility.

## TheParityTwinIsGeometricOnlyInTheBohrClosure (uses HKT OneGrid…; HTGeometry PrimeTorusKroneckerDensity)
- shiftChar τ: u ↦ u^{iτ} (moves zeros by iτ). Over 𝔽_q: (q^d)^{iπ/log q} = (−1)^d (degree parity, −1 at every odd-degree place).
- On one prime tower the Liouville twin is geometric: shift π/log p gives (−1)^n on p^n.
- On two primes it is not: a vertical shift equals −1 at ≤ 1 prime (p^{odd} = q^{odd} impossible). Two-prime lattices carry the whole index, so no vertical shift realizes the twin where the index lives.
- Bohr closure: by Kronecker (log p independent over ℚ) for every N, ε some shift is within ε of −1 at all p ≤ N. The twin is a limit of shifts on every finite prime set, equal to none.

## PointwiseClosedStatementsAreTwinBlind
- ∃ τ_m: n^{iτ_m} → λ(n) for all n ≥ 1 (Kronecker at primes, complete multiplicativity).
- A pointwise-closed set of weight sequences containing all vertical shifts a(n)n^{iτ} contains the Liouville twin λa; a selective closed statement fails for some vertical shift.
- Every completely multiplicative χ with |χ(p)| = 1 is a pointwise limit of shifts; flips at any prime set E (single ω_p, cofinite, Liouville) lie in every such closed set.
- Weil positivity is pointwise-closed (finitely many weights per compact test): its selectivity lives in terms that do not move under a shift, the pole and Gamma factor, where the index-one window carries its square.

## TheFunctionFieldCeilingIsExact (uses RHTower WeilKloostermanLFunction)
- Schur's test: symmetric P ≥ 0 with positive eigenvector Pv = μv ⇒ form ≤ μ|x|²; hence D·1 − P ⪰ 0 ⇔ μ ≤ D.
- Prime polynomial theorem: Σ_{d|j} d·#{monic irreducible of degree d} = q^j (Newton identity with weight 1). Mertens exact over 𝔽_q[T]: Σ_{1 ≤ deg h ≤ M} Λ(h)/|h| = M log q.
- primeKernelFq on monic polys of degree ≤ N (units of log q): the pole vector |f|^{−1/2} is an exact eigenvector, P_N v = N v (forward prime powers N − deg m, divisors deg m).
- Exact ceiling: D·1 − P_N ⪰ 0 ⇔ D ≥ N log q, no error term. Over ℤ the ceiling is log N − γ: Euler's constant is the archimedean defect of Mertens.
- Second rung: u_Q = pole vector on multiples of monic Q: P_N u_Q = (N − deg Q)u_Q there; |v|² = N + 1, |u_Q|² = (N + 1 − e)q^{−e}. Form negative definite on span(v, u_Q) for D < N − e(N + 1)/(N + 1 − (N + 1 − e)q^{−e}); as N → ∞ threshold N − e q^e/(q^e − 1): window width ≤ (|Q|/(|Q| − 1)) log|Q|; at |Q| = 2 this is 2 log 2 (ℤ margin).

## FineTowersHaveUnboundedNyquistWindows
- Nyquist at scale t: distinct exponents with t|s_j − s_k| < 2π give distinct characters at any u of scale t.
- For finitely many distinct exponents ∃δ > 0: every element of scale in (0, δ) separates them; groups with arbitrarily small scales (ℚ_{>0}, two-prime lattices) see every finite family on fine towers.

## ChebyshevsProducerPassesTheIntegerChebyshevCap (uses ArithmeticOfSquareRootPrecision WherePrecisionIsLost)
- Integer polynomials on [0, 1] give ψ lower counts capped by the integer Chebyshev constant (c ≤ −log t_ℤ ≤ 0.8644, classical) when smallness is certified by sup norm.
- Chebyshev's A_n = (30n)! n!/((15n)!(10n)!(6n)!): log A_n = Σ_{d ≤ 30n} Λ(d) g(⌊30n/d⌋), g(a) = a − ⌊a/2⌋ − ⌊a/3⌋ − ⌊a/5⌋ + ⌊a/30⌋ ∈ {0, 1} (30-periodic) ⇒ log A_n ≤ ψ(30n).
- Stirling: log A_n ≥ (14 log 2 + 9 log 3 + 5 log 5)n − 3 − log 30 − (3/2) log n; constant > 0.89·30.
- ψ(x) ≥ 0.89x − O(log x): passes the Nair floor log 2 and the integer Chebyshev cap. Still linear precision, lower count for primes; global law needs square-root upper count for the odd class.

## ThePolarDivisorCountsTheIndex (uses RHTower InfiniteSymmetry ConfinementIsTheSquareRootCount)
- Pole of the continued affine A₁ Weyl sum attached to β_i: Re s_i = −½ + log|β_i|/log q; right of the critical hyperplane ⇔ outer eigenvalue. Distinct eigenvalues ⇔ distinct pole parameters.
- Polar index formula: κ(traceKernel) = #distinct pole parameters right of Re s = −½. Confinement ⇔ κ = 0 ⇔ twist-tower upper counts. Golden datum: one pole class off the hyperplane (genus ceiling).
