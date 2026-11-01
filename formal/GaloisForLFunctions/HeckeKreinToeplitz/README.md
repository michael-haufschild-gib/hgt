# HeckeKreinToeplitz (HKT)

Namespace `GaloisForLFunctions.HeckeKreinToeplitz`; umbrella `HeckeKreinToeplitz.lean`; generic index theory lives in `Index/`. Every theorem is unconditional; RH appears only inside equivalences (`RiemannHypothesis ↔ …`) or as the conclusion of a stated finite-stratum hypothesis such as `(rightZeros zetaZeroConfig).Finite`. `#print axioms` lines exist only in `Index/`.

## 1. Motivation

The explicit-formula pairing of a test with its Hecke translates is a Hermitian kernel on `Γ = ℚ_{>0} ≅ ⊕_p ℤ`. RH says this kernel has no negative squares. Krein–Langer, Pontryagin-space and Toeplitz theory describe Hermitian kernels with finitely many negative squares on `ℤ` and `ℝ`. HKT builds that theory on `Γ`: a structure theorem, an index formula, a closed topology, a local-to-global law by prime towers, and a test of which statements separate `Λ` from its twins. The guide is Weil over `𝔽_q`. There the trace sequence is a kernel on `ℤ`, its index is the number of outer Frobenius eigenvalues, and a count (Stepanov) or Castelnuovo–Severi sets it to zero.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Hermitian kernel | `IsHermKernel k` | `k(u⁻¹) = conj k(u)` on a group |
| Gram matrix | `gram k x` | `(k(x_a⁻¹x_b))_{a,b}` for a finite family |
| Negative index | `negIndex k : ℕ∞` | sup over finite families of negative squares of the Gram matrix |
| Index on a subspace | `negIndexOn H V` | largest negative-definite subspace inside `V` |
| Positive-definite kernel | `IsPosDefKernel` | `κ = 0` |
| Hyperbolic pair | `pairKernel χ ω` | `ωχ + ω̄χ^†`, `χ^†(u) = conj(χ(u))⁻¹` |
| Krein–Langer class | `IsKreinLanger` | positive-definite + finitely many pairs with nonzero weights |
| Pontryagin decomposition | `exists_pontryagin_decomposition` | `k + Σ_{i≤κ} φ̄_i ⊗ φ_i ⪰ 0`, `φ_i` in the span of translates of `k` |
| Column space | `kernelColumnSpan`, `kernelColumnPairing` | span of columns `k(g⁻¹·)`, nondegenerate invariant Hermitian form (Pontryagin space) |
| Logarithmic character | `logChar`, `zeroChar ρ` | `u ↦ u^{ρ−1/2}` on `ℚ_{>0}` |
| Hecke orbit kernel | `orbitKernel Z f` | `u ↦ W_Z(f, τ_{log u} f)` for a zero configuration `Z` |
| Weil kernel of `ζ` | `zetaKernel` | orbit kernel of the zeros of `ζ`, cubic-spline test |
| Weight kernel | `weightKernel λ f` | explicit-formula functional with `ζ`'s pole and Gamma and prime weights `λ` |
| Tower kernel | `towerKernel`, `towerPole`, `towerPrime`, `towerArch` | restriction to `⟨p⟩ ≅ ℤ`, split as pole − prime + arch |
| Trace kernel | `traceKernel D` | `m ↦ Σ β_i^m` of a curve datum |
| Atomic kernel | `atomKernel D`, `primeKernel` | `Dδ₁ − P` on `ℚ_{>0}`, `P(r^{±1}) = Λ(r)r^{−1/2}` |
| Pole index | `poleNegIndex` | index on the pole hyperplane `Σ c_n n^{−1/2} = 0` |
| Dirichlet block | `dirichletBlock L x` | `Σ_{l<L} e^{ilx}` |
| Flip jump | `flipJump p f d` | `2 log p ‖f‖² p^{−|d|/2}` at odd `d` |

External: `zetaZeroConfig`, `rightZeros`, `CurveDatum`, `realTests`, `cx` (ArithmeticCastelnuovoSeveri); `TemperedConfig` (SquareRootThreshold); `hermNegIndex`, `HeckeLattice`, `primeElt`, `scale`, `heckeLogScale` (HTGeometry); `weilFullFunctional`, `crossCorr` (RHTower); `primeFlipWeight` (ArithmeticCountingPositivity); `finiteFlip`, `finiteFlipWeight`, `twistedCompleteWeilMatrix` (RenormalizedArithmeticPotentialTheory); `atomicTest` (ArithmeticElectrostatics); `atomDilate`, `weilQuadTw` (SpacingScaleHarmonicAnalysis); `cubicSpline` (BiScaleUncertainty).

## 3. Language

- Index `κ`: number of negative squares; RH for a weight = its kernel has `κ = 0`.
- Right zero: zero with `Re ρ > ½`; each one contributes one hyperbolic pair `u^{ρ̄−1/2}`.
- Finite stratum: finitely many right zeros of `ζ`, equivalently `κ(K_ζ) < ∞`.
- Separation at `u`: the `2|J|` values `χ_j(u), χ_j^†(u)` are distinct and off the unit circle.
- Aliasing on `H`: two pairs with equal restrictions to `H`, or a pair unitary on `H`.
- Seen zero: a right zero at which the test's Fourier weight is nonzero.
- Receiver: Weil Gram matrix of finitely many real shifts of one `C²` compactly supported test.
- Compression: the kernel pulled back to a product family by an auxiliary `P = Σ p_α δ_{y_α}`.
- Twin: the weight `ωΛ`, `|ω| = 1`. Battery: Liouville twin, single-prime flips, `Λ + εn^{−η}`, golden curve.
- Carrier: the vector that carries a negative square (pole direction or not).
- Rung: an eigenvalue `log N − E_m + o(1)` of the prime Gram on `{1..N}` at the adjunction energy `E_m = γ + log m + τ(m)`.

## 4. Mechanisms

**A. Structure**
1. Hyperbolic plane: the form of `h_{χ,ω}` is `2 Re(ω A(c) conj B(c))`, with `A = Σ c_a χ(a)` and `B = Σ c_a χ^†(a)`. Unitary `χ` gives `2 Re ω |A|²`; otherwise exactly one negative square.
2. Sum-of-squares upper bound: `2 Re(ωAB̄) ≥ −|ω|(|A|² + |B|²)`. Adding `m` squares that make every form nonnegative gives `κ ≤ m` (`negIndex_le_card_of_nonneg_on_ker`, `negIndex_le_of_hyperbolic_features`).
3. Growth lower bound: on `⟨u⟩` a pair is `ωw^n + ω̄w̄^{−n}` with `|w| ≠ 1`, while a positive-definite part is bounded by `p(1)`. Test vectors `X^N E − F` with Vandermonde-interpolated windows are negative definite on a `|J|`-dimensional space for large `N`.
4. Pontryagin decomposition: the index is attained on one family `x₀`. Haynsworth splits the index of `x₀ ⊔ x` into the negative block plus its Schur complement, and the Schur complement is ⪰ 0.
5. Column space: columns `k(g⁻¹·)` with pairing `k(g⁻¹h)` give a nondegenerate, translation-invariant Hermitian space. Nonpositive and isotropic column subspaces have dimension ≤ `κ`.
6. Null rigidity: if `k(1) = 0` and `κ ≤ 1`, the zero set is a subgroup. Vanishing on normal `H` and on `D` with `G = HD` gives column rank ≤ `κ²`.
7. Spectral matrix: every Gram matrix of `Σ a_χ χ` is `MᴴAM`. Dedekind–Artin makes some `M` surjective, so `κ = κ(A)` with no separation hypothesis.
8. Bohr means: box averages of `conj ψ_i ψ_j` tend to `δ_ij`, so a Bohr series is eventually negative definite on its negative characters.

Index one on any abelian group: completing the positive column complement gives a common nonpositive line for commuting isometries. Its reflected eigencharacter defines a positive mass hyperplane; conversely, positivity on such a hyperplane bounds the index by one. No growth or countability assumption is needed. The kernel either has a positive unitary-character mass hyperplane or splits as a positive-definite kernel plus one nonzero nonunitary hyperbolic pair. The off-circle unitary resolvent constructs the reflected companion line. The unitary-hyperplane case is exactly cyclic subexponential growth, equivalently cyclic quadratic growth. A positive unitary-character hyperplane forces the quadratic bound even on a nonabelian group, through the polar-index/second-difference identity.

Bounded kernels: finite translate corrections give uniformly bounded Fejér measure pairs. Compactness produces a signed torus spectrum; L² density extends the repaired form to indicators. A positive mass floor forces finite negative support, and correction-map injectivity gives exactly `κ` negative atoms.

Finite index and cyclic growth: on any group, a Hermitian kernel with `κ≤r` and cyclic subexponential growth has cyclic growth at most degree `2r`. Complete the positive column factor, obtain a nonpositive eigenvector from a weakly compact invariant graph, and force its eigenvalue onto the unit circle using orbit growth. Its unitary second-difference filter lowers the index; two discrete integrations per negative square give the degree bound.

**B. Topology and deformation**
9. Closedness: pointwise kernel convergence gives entrywise Gram convergence, and negative-definite subspaces persist, so `{κ ≤ m}` is closed.
10. Restriction and compression never raise `κ`. A compression multiplies the weight of a pair by `P̂(χ) conj P̂(χ^†)`.
11. Unitary twist is a diagonal unitary congruence, so `κ` is unchanged. Damping by `r` unitary characters multiplies `κ` by at most `r` (attained: `1 + (−1)^n` doubles a pair).
12. Coalescence: `u^{t+iγ}` has one square for `t ≠ 0` and none in the limit iff `Re ω ≥ 0`.
13. Rescaling: if positive rescalings of pullbacks recover `k`, a bounded positive-definite addition keeps `κ`.

**C. Arithmetic**
14. `|χ_ρ(p)| = p^{β−1/2}`. On `⟨p⟩` two right zeros alias iff they have equal real parts and ordinates in `2πℤ/log p`. On `⟨p, q⟩` they alias iff equal (`log p/log q ∉ ℚ`). A right zero never aliases with a reflection.
15. Blind primes: a pair of distinct right exponents aliases at ≤ 1 prime, so ≤ `κ(κ−1)/2` primes are blind.
16. Nyquist: the tower of `p` samples ordinates at spacing `2π/log p`. It hides at most a factor `⌊H log p/2π⌋ + 1` in a window of length `H`, and nothing below `2π/log p`.
17. Dense scales: `ℝ_{>0}`, `ℚ_{>0}` and every subgroup with dense log-scales carry the same orbit-kernel index.
18. Pole principle: on a tower the pole is one pair `h_{w,(A+B̄)/2}`, `w = e^{ℓ/2}`, vanishing on a hyperplane. Forms equal on a hyperplane differ in index by ≤ 1.
19. Integer windows: the Gram matrices on `{1..N}` exhaust `κ` of any kernel on `ℚ_{>0}`.
20. Index ladder: the atomic Gram matrix is `D·1 − P_N`. Each rung below `log N − D` adds a square, and sign gauges act by congruence (twin-blind index). Orthogonal prime translates of one negative window give `κ = ∞` at every fixed `D`.
21. Precision rigidity: two weights with the same pole and Gamma differ on a tower by the prime pairing of the difference. A one-signed difference with unbounded mass makes both positive impossible.
22. Flip on its tower: for `supp f ⊂ [−a, a]`, `2a ≤ log p`, the `p`-flip twin equals `K_ζ + flipJump` on `⟨p⟩`. `flipJump` has Toeplitz symbol `sign(cos θ)` (odd Poisson), negative `≍ −L` on blocks modulated near `θ = π`.
23. Thin pure-point spectrum: the grid identity `Σ_{m<M}|D_L(x − 2πm/M)|² = ML` plus Markov shows that a pure-point positive kernel has Toeplitz energy `≤ εL` at some frequency in every arc. An absolutely continuous spectrum would give `≍ L`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| `κ(p + Σ_J h_j) ≤ |J|`, `= |J|` under separation | `negIndex_add_sum_pairKernel_le`, `negIndex_add_sum_pairKernel_eq` | proved |
| One pair: index 0 if unitary, 1 otherwise, for any positive-definite addition | `negIndex_pairKernel_of_unitary`, `negIndex_add_pairKernel_eq_one` | proved |
| `{κ ≤ m}` closed under pointwise limits | `negIndex_le_of_tendsto`, `isPosDefKernel_of_tendsto` | proved |
| Index attained; `κ ≤ m` ⇔ ⪰ 0 after `m` squares; subadditive | `exists_hermNegIndex_gram_eq_negIndex`, `exists_pontryagin_decomposition`, `negIndex_le_iff_exists_rank`, `negIndex_add_le` | proved |
| Nonpositive column subspaces have dim ≤ `κ` | `finite_nonpositive_column_subspace`, `finite_isotropic_column_subspace` | proved |
| `κ ≤ 1`, `k(1) = 0`: zero set is a subgroup; two zero subgroups covering `G` force `k = 0` | `inv_mul_eq_zero_of_negIndex_le_one`, `eq_zero_of_subgroup_readings` | proved |
| Zero readings on normal `H` and `D`, `G = HD`: Gram rank ≤ `κ²` | `rank_gram_le_square_of_zero_subgroups` | proved |
| Finite exponential sum: `κ` = #negative unitary weights + #nonzero reflected pairs | `negIndex_expSum_eq`, `negIndex_expSum` | proved |
| Absolutely convergent Bohr series: `κ` = #negative coefficients | `negIndex_bohrSum`, `negIndex_bohrSum_lt_top_iff` | proved |
| Twist keeps `κ`; damping multiplies by ≤ `r`; coalescence law | `negIndex_twist`, `negIndex_mul_sum_le`, `negIndex_damped_pair_eq_two`, `coalescence_law` | proved |
| Bounded growth along a separating `u` ⇒ positive definite | `isPosDefKernel_of_bounded`, `not_norm_le_of_lt_depth` | proved |
| `(tr H^k)² ≤ κ_± tr H^{2k}` (odd `k`) | `sq_trace_pow_le_negIndex_mul`, `le_negIndex_of_trace_pow_neg` | proved |
| Compression: `κ` counts pairs with `P̂` nonzero at both characters; positive definite iff one character of every pair is killed | `negIndex_compress_eq`, `negIndex_compress_eq_zero_iff` | proved |
| Arithmetic index formula: `κ` distinct right points with nonzero weights give exactly `κ` | `negIndex_hecke_pairs_eq`, `negIndex_logChar_pairs_eq` | proved |
| Aliasing: index on a cyclic subgroup = #value classes of nonzero weight; two primes decide; ≤ `κ(κ−1)/2` blind primes | `negIndex_zpowers_eq_card_classes`, `negIndex_twoPrime_eq`, `ncard_blindPrimes_le`, `negIndex_prime_eq_of_not_blind` | proved |
| Locality fails on `ℤ²`; positivity on infinitely many prime towers gives `κ = 0` for arithmetic kernels | `locality_fails`, `negIndex_eq_zero_of_posDef_on_infinitely_many_towers` | proved |
| `𝔽_q`: `κ(traceKernel)` = #distinct outer eigenvalues; `κ = 0` ⇔ count ⇔ trickle-down | `negIndex_traceKernel`, `negIndex_traceKernel_eq_zero_iff_count`, `negIndex_traceKernel_eq_zero_iff_trickleDown` | proved |
| Golden datum: `κ = 1` on its tower, `∞` on the lattice (two primes) | `negIndex_golden_traceKernel`, `negIndex_orbitKernel_golden_twoPrime`, `golden_tower_vs_lattice` | proved |
| Orbit kernel: Gram = Weil Gram of translates; `κ` = #seen right zeros | `gram_orbitKernel`, `negIndex_orbitKernel` | proved |
| `κ(K_ζ)` = #right zeros, even; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | `negIndex_zetaKernel`, `negIndex_zetaKernel_eq_two_mul`, `riemannHypothesis_tfae_zetaKernel` | proved |
| Krein–Langer ⇔ finite index, for orbit kernels and `ζ` | `isKreinLanger_orbitKernel_iff_negIndex_lt_top`, `isKreinLanger_zetaKernel_iff_negIndex_lt_top` | proved; general unbounded converse on `Γ` open |
| Bounded free-lattice kernels: finite index iff PD minus finitely many distinct unitary characters with positive weights; least count = index | `bounded_free_lattice_krein_langer`, `bounded_free_lattice_finite_index_iff`, `bounded_hecke_krein_langer` | proved |
| On the finite stratum, boundedness iff an index-sized unitary decomposition | `finite_index_bounded_iff_unitary_decomposition`, `negative_index_le_unitary_decomposition_size` | proved |
| Same index on `ℝ_{>0}`, `ℚ_{>0}`, two primes; finite-index TFAE | `negIndex_realOrbitKernel`, `negIndex_zetaKernel_twoPrime`, `zetaKernel_finiteIndex_tfae` | proved |
| Finite index ⇒ LH and a zero-free strip | `lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top` | proved |
| Height truncations converge, `κ` = sup; RH ⇔ every truncation positive definite | `negIndex_orbitKernel_eq_iSup_height`, `riemannHypothesis_iff_height_truncations_posDef` | proved |
| Integer windows carry `κ`; RH ⇔ integer-atom positivity | `negIndex_eq_iSup_intWindow`, `riemannHypothesis_iff_integerAtoms` | proved |
| Every receiver at every width has ≤ `κ(K_ζ)` squares; `κ(K_ζ)` = sup over receivers | `hermNegIndex_weilGram_le_negIndex_zetaKernel`, `negIndex_zetaKernel_eq_iSup_receivers` | proved |
| Shrinking atoms reach `κ` along some schedule | `exists_shrinking_schedule`, `negIndex_zetaKernel_eq_iSup_shrinkGram` | proved; explicit schedule open |
| Gevrey `s ≤ 1` compact profiles vanish; width `(log log N)^α/N`, `α > 1`, decides RH | `eq_zero_of_gevrey_le_one`, `exists_compactSupport_gevrey_iff`, `atomicReceivers_quasiAnalytic_boundary` | proved |
| Index is energy: `κ(K_ζ)² ≤ 2E_crit/97` | `negIndex_zetaKernel_le_of_energy`, `riemannHypothesis_tfae_energy` | proved |
| Heat collisions: mass `2(κ + E)` on the finite stratum; charge ≤ 1 ⇒ RH | `eventually_collisionMassAfter_eq_index`, `riemannHypothesis_of_horizontalCollisionCharge_le_one` | proved |
| Global law: `κ = 0` ⇔ one-sided count, over `𝔽_q` and over `ℤ` (`ψ(x) − x ≤ C√x log²x`) | `global_law_count`, `negIndex_zetaKernel_eq_zero_iff_count` | proved (equivalence) |
| Selectivity: `Λ` vs Liouville, `λ` vs `λ + εn^{−η}` never both tower-positive; index zero on a tower selects `Λ` | `not_negIndex_towerKernel_liouville_and_vonMangoldt`, `not_negIndex_towerKernel_and_perturbed`, `forall_negIndex_towerKernel_eq_zero_iff` | proved |
| Pole costs ≤ 1: tower index = `κ(Arch − Prime)` ± 1 | `negIndex_towerKernel_le_archPrime_add_one`, `negIndex_archPrime_le_towerKernel_add_one` | proved |
| Nyquist: one prime hides ≤ `⌊H log p/2π⌋ + 1` | `card_le_mul_card_image_frobEig`, `card_le_iSup_negIndex_towerKernel_of_window` | proved |
| Index-one window: `κ_atom = 0` above `L = log N − γ`, `= 1` on `[L − 2 log 2, L)` (pole-carried), `≥ 2` below; `κ = ∞` on `Γ` at fixed `D` | `eventually_hermNegIndex_atom_eq_one`, `eventually_two_le_hermNegIndex_atom`, `negIndex_atomKernel_eq_top` | proved |
| Twin-blind ladder, selective carrier | `hermNegIndex_gaugeAtom_eq`, `eventually_exists_neg_on_pole_gauge`, `eventually_exists_neg_on_pole_liouville` | proved |
| Selective index is one square: pole indices of two gauges differ by ≤ 1; in the window `ζ` 0, Liouville 1 | `abs_poleNegIndex_gauge_sub_zeta_le_one`, `eventually_poleNegIndex_window` | proved |
| Pure point spectrum thin at most frequencies | `exists_frequency_thin`, `sum_grid_normSq_dirichletBlock` | proved |
| `ζ` and any single-prime flip never both have finite index | `negIndex_flip_eq_top_of_finite`, `negIndex_zetaKernel_eq_top_or_flip` | proved |
| Every nonempty finite flip set: `sup_g κ = ∞`; for `ζ` the sup is `κ(K_ζ)` | `iSup_negIndex_weightKernel_finiteFlip_eq_top`, `iSup_negIndex_weightKernel_vonMangoldt` | proved |

## 6. Tools

**Developed**
- Kernel index calculus on any group: Gram inertia, restriction, closedness, attainment, subadditivity, Pontryagin decomposition, column Pontryagin space, null-subgroup rigidity.
- Exact index of finite exponential sums (spectral matrix) and of Bohr series (box means).
- Logarithmic characters on `ℚ_{>0}` and the arithmetic index formula; aliasing and Nyquist counting on prime towers.
- Stepanov compressions as kernel pullbacks; Dirichlet-polynomial transforms `hat_logChar`.
- Hecke orbit kernel of a tempered zero configuration, its on-line/pair split on the finite stratum, height truncations, the archimedean completion.
- Receivers: integer windows, uniform receiver bound, shrinking schedules, Denjoy–Carleman profiles.
- Tower decomposition pole − prime + arch; pole hyperplane lemma `hermNegIndex_le_add_one_of_eq_on_ker`.
- Atomic kernel on `{1..N}`: rung lemma `le_hermNegIndex_atom_of_eigen`, gauge congruence, `negIndexOn`.
- Toeplitz block technology: Dirichlet blocks, the grid identity, odd-Poisson blocks, separated block families (`re_blockSum_pp_le`, `re_blockSum_flip_le`).
- Realness of the explicit-formula functional on real tests (`im_weilFullFunctional_ofReal`).

**To build**
- Covariant converse for unbounded kernels on `Γ`. The bounded case has finite negative spectral support and an exact unitary-character decomposition.
- An arithmetic Krein–Langer bound: `κ(K_ζ)` from local constituents and one global count, reproducing index zero over `𝔽_q`.
- A Stepanov certificate over `ℤ`: Dirichlet polynomials vanishing off the line without presupposing the zeros.
- A bound on `E_crit`, or any prime-side bound on `κ`.
- The explicit receiver schedule `(log log N)^α/N` reaching `κ`.
- Transfer of the pole carrier from atomic windows to the complete form at overlapping widths.

## 7. Open questions

1. What structure theorem holds for unbounded finite-index Hermitian kernels on `Γ`? The bounded case is positive definite minus exactly `κ` distinct unitary characters with positive weights.
2. Which prime-side quantity bounds `κ(K_ζ)`? Any such bound proves LH.
3. Can the one-sided count `ψ(x) − x ≤ C√x log²x` be proved from local constituents, as Stepanov does over `𝔽_q`?
4. Is there a prime that certifies all zeros of height `≤ T`, uniformly in `T` (Diophantine relation between `log p` and the ordinates)?
5. Are the adjunction energies all the rungs of the atomic ladder?
6. Does the selective pole carrier survive at overlapping widths (the separated regime)?
7. Is there a deformation of Krein–Langer data that follows the heat flow pair by pair?
8. Does a direct kernel-side argument give finite index ⇒ LH without zeros?
9. Does the conductor-2 rung (`E_2 − E_1 = 2 log 2`) coincide with the dyadic multiresolution of the complete source?

## 8. Traps

| Trap | Fact |
|---|---|
| Finite index is a smallness condition | It is structure: positive + finitely many pairs; weight sizes do not matter |
| A large positive part pays a pair | Never: growth beats boundedness |
| Positivity on coordinate circles gives positivity on `Γ` | False on `ℤ²` (`locality_fails`); true for arithmetic kernels on infinitely many towers |
| One prime sees every pair | Aliasing classes with cancelling weights hide; ≤ `κ(κ−1)/2` primes are blind |
| `L²` limits of positive tests stay positive | Weil's form is not `L²`-continuous; `{κ ≤ m}` is closed only in the kernel topology |
| Index is additive | Only subadditive |
| Positive damping keeps the index | It can multiply it by the number of characters |
| The atomic index separates `ζ` from twins | Sign gauges act by congruence; only the carrier (pole or not) is selective, and only by one square |
| A large fixed counterterm pays the prime kernel | `κ(atomKernel D) = ∞` on `Γ` for every fixed `D`; the counterterm must grow like `log N` |
| The gap `2 log 2` is an index ceiling | It is the width of the index-one window; single-prime flips share it |
| Short-interval prime statistics bound `κ` | `Λ + εn^{−η}` shares them and fails on every nonnegative tower |
| Finite index is below Lindelöf | Finite index ⇒ LH |
| Narrower atoms escape the receiver bound | Every receiver at every width is ≤ `κ(K_ζ)`; below Gevrey 1 no compact profile exists |
| Local constituents are positive | Prime terms enter with a minus sign, the pole is hyperbolic; positivity belongs to the assembly |
| A finite-index ceiling for `ζ` might also hold for a flip | `ζ` and any single-prime flip never both have finite index; every finite flip has `sup_g κ = ∞` |

## 9. Context

**Uses**

| Programme | Imports | What |
|---|---|---|
| HTGeometry | 8 | Hermitian inertia, Hecke lattice, logarithmic scales |
| RHTower | 7 | explicit formula, `weilFullFunctional`, Lindelöf/depth strata, heat collisions |
| ArithmeticCastelnuovoSeveri | 6 | zero configurations, `Wsummand`, curve data, one-prime tower law |
| ArithmeticOrientationGeometry | 5 | spline orbits, rational Hecke orbit index |
| RenormalizedArithmeticPotentialTheory | 3 | finite flips, twisted complete Weil matrix, overlap flip index |
| SelectiveMultiscaleArithmeticPositivity | 2 | margin `2 log 2`, tower selection |
| SpacingScaleHarmonicAnalysis, ArithmeticLorentzianGeometry, ArithmeticIndexDescent, ArithmeticCountingPositivity | 1 each | atomic dilates, trickle-down, index descent, `primeFlipWeight` |

**Used by**

| Programme | Imports |
|---|---|
| ArithmeticKreinLangerTheory | 14 |
| AdelicKreinGeometry | 12 |
| EffectiveArithmeticHodgeTheory | 3 |
| ArithmeticOfSquareRootPrecision, TransMetzlerWeilPositivity, BiarithmeticGeometry | 1 each |

| Neighbour | Relation |
|---|---|
| ArithmeticPositiveDuality | positive (Bochner) theory on `ℚ_{>0}`; HKT is its finite-index extension |
| ArithmeticCastelnuovoSeveri | Pontryagin law for finite configurations; HKT reads it as restriction to cyclic sublattices |
| SelectiveMultiscaleArithmeticPositivity, ArithmeticCountingPositivity | selection theorems and the flip battery that HKT tests |
| ArithmeticKreinLangerTheory | continues HKT: exceptional waves, fine towers, Nyquist windows, parity form of the global law |
| AdelicKreinGeometry | adelic/Haar completion of the HKT kernel theory |
| SignedArithmeticHodgeTheory, ArithmeticIndexDescent | finite stratum and Gram index under source presentations |

## 10. Big picture

HKT turns the RH problem into an invariant of one object: a Hermitian kernel on the positive rationals whose negative squares are exactly the zeros right of the line. Everything structural is now known about this invariant. It is closed in the right topology. It is carried by two primes, by integer windows and by every receiver. It is priced by energy and by heat collisions. It equals a one-sided square-root prime count. Over finite fields it reproduces Weil. None of this decides its value. Each equivalence relocates the problem without shrinking it, and finite index alone already sits at Lindelöf depth.

The programme also shows where a proof cannot come from. Twin-blind structure (aliasing, closedness, decompositions, index ladders) cannot decide, because sign gauges act by congruence. The selective content at atomic resolution is a single square, carried by the pole. Every arithmetic perturbation of `Λ` (a flipped prime, a Liouville twist, an `n^{−η}` error) has infinite index, so `ζ` sits at an isolated point. A proof has to supply a global law that is exact rather than approximate: a count or a Riemann–Roch-type identity, with the Euler product and functional equation entering as identities. Positivity is then the last step, after the index has been computed.
