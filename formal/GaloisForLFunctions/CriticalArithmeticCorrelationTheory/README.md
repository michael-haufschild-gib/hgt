# Critical Arithmetic Correlation Theory

Namespace `GaloisForLFunctions.CriticalArithmeticCorrelationTheory`; umbrella `CriticalArithmeticCorrelationTheory.lean`; 105 modules. Every theorem is unconditional (no RH, no correlation model, no zero hypothesis); modules end with `#print axioms`.

## 1. Motivation

Weil positivity on a family that exhausts the test space is RH. This programme proves positivity of the literal complete Weil form (von Mangoldt source with every prime power, Gamma factor, both pole moments) on atomic test families: `N` dilated copies of one profile at logarithmic positions `log n`, width `c/N`, `n ≤ N`. The ratio `c` measures overlap: `c ≤ 1` keeps supports essentially disjoint (touching at `c = 1`); `c > 1` makes atoms overlap and lets non-ratio prime pairs `km ≠ n` interact. The programme carries positivity from strict separation, through touching, to every fixed overlap, to bounded overlap with one horizon, and to slowly growing overlap on fixed conductor packets. Each step names the exact arithmetic object that pays the error.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Complete Weil matrix | `completeWeilMatrix φ c N` (RAPT) | normalized complete Weil form on atoms `atomDilate φ (c/N)` at `log n`, `n ≤ N` |
| Complete energy / spectrum | `completeWeilEnergy`, `completeWeilEigenvalue` | quadratic form `⟨A x, x⟩`, Hermitian eigenvalues |
| Atomic test | `atomicTest N x g` (SSHA) | `Σ x_n g(u − log n)` |
| Prime-edge defect | `poleDefect N x` | Dirichlet energy of `x` along prime edges; the reserve that pays errors |
| Ramanujan pole profile | `ramanujanPoleProfile m n`, `normalizedRamanujanHorizonVector m N` | `c_m(n)/√(φ(m) n)`, normalized by `√log N`; approximate eigenvectors |
| Completed conductor energy | `completedConductorEnergy φ c m` | `completeWeilAdjunctionEnergy − shellCorrection`; quasimode eigenvalue of conductor `m` |
| Non-ratio prime source | `nonRatioForm g N x`, `fullWeilNonRatioMatrix` | prime pairs `k·m ≠ n` inside the atom window |
| Upward / downward rows | `upwardPrimeRow`, `downwardPrimeRow` (RAPT) | non-ratio action split by direction `n ↦ kn` vs `n ↦ n/k` |
| Affine prime shell | `affineRamanujanPrimeShell`, `affinePrimeShellCorrectionOfShift` | `Σ Λ(k)/k·c_q(kn+b)·autocorr(hX/(ck))`; literal source of the shell correction |
| Residue prime window | `residuePrimeWindow`, `residuePrimeReading`, `primeClassKappa` | Mangoldt reading of a residue pattern; unit-class mean |
| Primitive prefix energy | `primitiveRootPrefixEnergy m k`, `primitivePrefixGram` | `Σ_{ζ primitive} |Σ_{j<k} ζ^j|²` and its Gram form |
| Arithmetic overlap curvature | `arithmeticOverlapCurvature m t`, `arithmeticOverlapGram` | `Σ_{d|m} μ(m/d)d²{t/d}(1−{t/d})` |
| Divisor jet | `ramanujanLogDivisorJet m n` | `Σ_{d|(m,n)} μ(m/d) d log d` |
| Profiles | `tiltedUnitSpline` (SSHA), `liouvilleSelector`, `tiltedBoxPlateau` | explicit `C²` profiles on `[0,1]` with no real Fourier zeros |
| Source work | `xiDampedSourceWork R` (ArithmeticElectrostatics) | rational-damped completed source work |

External: `atomDilate`, `archForm`, `weilQuad` (RHTower/SSHA), `robinEulerThreshold` (TMWP), `shellSpectrum` (RAPT `CompletedShell`).

## 3. Language

- Overlap `c`: atom width `c/N`. Touching `c = 1`. Distinct integers `≤ N` have log gap `> 1/N`, so at `c ≤ 1` atom supports are disjoint; the only non-ratio pair is the boundary star `(N, N+1)`.
- Reserve + quasimodes + floor: a positive fraction of `poleDefect`, norm quasimodes `‖A v_m − E_m v_m‖ → 0`, and `E_m ≥ e > 0` together exclude every eigenvalue below `e`.
- Shell: integer offset `h` between `kn` and a neighbour index; shells `1 ≤ h < c` are active at overlap `c`.
- Horizon types: eventual (`∀ᶠ N`), uniform in `c` on an interval (one horizon), explicit (stated inequalities on `N`).
- Harmonic norm: errors measured in `Σ_n err(N/n)²/n`, normalized by `log N`.

## 4. Mechanisms

**A. Exact decomposition of the complete matrix**
1. Complete matrix = prime energy + self finite part + center (charge) + cross error + both pole errors − non-ratio matrix (`completeWeilMatrix_eq_decomposition_at_touching`); the sign of the non-ratio term is retained.
2. The complete residual on `v_m` is an exact sum of eight source terms; each is estimated separately with its own rate.

**B. Through touching (`0 < c ≤ 1`)**
1. Boundary star: at width `≤ 1/N` the only non-ratio pair is `N, N+1` (`small_integer_log_gap_forces_boundary`); its source is `2G(d_N)x_N Σ_{km=N+1} Λ(k)/√k·x_m`, paid by the divisor identity at cost `O(log N/N)`.
2. Cross error: endpoint decay `|G(z)| ≤ (L²w/4)(w−|z|)²` or overlap length `|G(z)| ≤ B²(w−|z|)` pays the inverse-square kernel without gap loss; one budget `4C c²‖x‖²` for all `c ≤ 1`.
3. Charge deficit: `(∫φ)²/∫φ² < 1` for every nonzero continuous interval profile; keeps a uniform defect fraction `(1−q)/4`.
4. Plateau limits: smooth plateaus have Robin, mass, charge `→ 1`, completed shape `→ 2 > log 2π`; endpoint energy `B/M − log 2πc + cI²/M ≥` its value at `c = 1`.

**C. Spectral assembly**
1. Reserve ⇒ bounded-energy unit vectors have coordinate mass `≥ 1/18` on a finite Ramanujan family (arithmetic compactness).
2. Coordinate on eigenvector below `e`: `⟨x_i, v_m⟩² ≤ ‖A v_m − E v_m‖²/(E − e)²`; finitely many conductors ⇒ contradiction (`eventually_completeWeil_eigenvalues_ge_of_reserve_quasimodes`).
3. Shifted matrix (subtract half the prime energy) keeps confinement and gives a logarithmic defect reserve.

**D. Fixed overlap (`c > 1`)**
1. Integer separation: log gap `> 1/(N+1)` leaves overlap length `max(0, w − 1/(N+1))`; first overlap costs `C(c − 1 + 1/N)` defect.
2. Directed Young: outgoing rows have bounded mass (Chebyshev), incoming rows carry `log m` paid by the top-row defect; non-ratio form is infinitesimally bounded by `poleDefect`.
3. Gamma reserve at fixed overlap: macroscopic cutoff `M = N/L`; separated prefix keeps unit self-energy, tail gets a Fourier-band reserve, ordered prefix/tail interaction costs only mass.
4. Downward cancellation: `Σ_{a|n} Λ(a)c_m(n/a) = log n·c_m(n) − jet` cancels the near-Gamma `log(N/c)` coefficient; exterior products live in a strip of width `⌈ce^c⌉`.
5. Upward realization: offset reindexing, log-kernel linearization `O(1/N)`, cutoff moves paid by `primeIndexBoundaryMass → 0`, reflected shifts `c_q(T − h) = c_q(T + qh − h)`; the remainder is the affine shell source.
6. Affine shells: unit averages diagonalize `c_q(rn + h)` with eigenvalue `c_q(h)/φ(q)`; residue Mertens windows; Abel summation with flat reciprocal weights gives the signed mean `c_q(n)c_q(b)/φ(q)·∫_{h/c}^1 autocorr/u`.
7. Conductor floor: first coprime term of the shell repayment series gives `E_m ≥ (2/M)(m/φ(m))∫_{t>c/m} shellSpectrum > 0` when the profile FT has no real zeros.

**E. Uniformity and growth**
1. Bounded overlap: every constant monotone in `c` on `[1, K]`; one Fourier floor on `[1, 101K]`.
2. Polynomial costs: residual `‖·‖² ≤ K(c⁵/log N + c¹⁰(log N/N)²)`, energies `≤ Cc²`, defect reserve `a/c⁷` at mass cost `Cc⁹`, conductor floor `c⁻⁷`.
3. Quantitative arithmetic: fixed-modulus and conductor-uniform PNT (`q ≤ (log X)^A`) give every inverse-log rate for residue readings and Mertens remainders; total variation (not sup) of reciprocal weights makes the affine source linear in `c`.

**F. Cyclotomic curvature**
1. `P_m(k) = Σ_{d|m} μ(m/d)(k mod d)(d − k mod d) ≥ φ(m)` when `m ∤ k` (cyclotomic norm ≥ 1 + AM–GM); `A_m(k+u)` interpolates `P_m(k), P_m(k+1)`.
2. Curvature is a squared Hilbert distance; centered Gram positive, raw kernel conditionally negative; radical = cyclotomic divisibility; all divisor conductors give the discrete bridge = prime-block jump energy.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Completed source work `0 ≤ W(R) ≤ 64R L_R(L_R+1)`, tapered `|W_N(R)| ≤ 128R L_R(L_R+1)` | `xiDampedSourceWork_le_logarithmic_ceiling`, `abs_xiTaperedSourceWork_le_logarithmic_ceiling` | proved |
| One horizon, all `c ∈ (0,1]`, every eigenvalue `≥ b` for any `b < 2 − log 2π` (near-unit plateau) | `exists_near_unit_plateau_uniform_completeWeilMatrix_posDef` | proved |
| Explicit horizon through touching: `Q⁴ ≤ N`, `log N ≥ max(1, 36B/floor²)` ⇒ PosDef for all `c ∈ (0,1]` | `exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_through_touching` | proved |
| Reserve + quasimodes + floor ⇒ spectral floor | `eventually_completeWeil_eigenvalues_ge_of_reserve_quasimodes` | proved |
| Completed conductor energies are actual quasimode energies at every fixed `c > 0` | `tendsto_completeWeilMatrix_completedConductor_residual_norm` | proved |
| Positive complete Weil matrix at every fixed `c > 0` (tilted spline) | `eventually_tiltedUnitSpline_completeWeilMatrix_posDef`, `eventually_tiltedUnitSpline_weilQuad_atomicTest_nonneg` | proved |
| Same for every `C²` profile on `[0,1]` with no real Fourier zeros; low spectral counts; bottom → completed shell energy | `eventually_noRealZero_completeWeilMatrix_posDef`, `noRealZero_spectral_count_eq`, `noRealZero_spectrum_bottom` | proved |
| Ground state is the pole: one eigenvalue below `E(1) + gap/2`, it tends to `E(1)`, its line captures `v_1` | `eventually_tiltedUnitSpline_completeWeil_ground_count_one`, `tendsto_tiltedUnitSpline_groundProjection_error_sq` | proved |
| One horizon and one floor for all `0 < c ≤ K` | `exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor`, `eventually_tiltedUnitSpline_weilQuad_nonneg_uniform_boundedOverlap` | proved |
| Explicit horizon at `c ≥ 1`: `Q ≤ exp(D(Cc¹⁶+1)) + 2`, `N ≥ Q⁴, Hc⁸`, `log N ≳ c¹⁰` | `exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_horizon` | proved |
| Fixed conductor packets positive for `1 ≤ c ≤ (log N)^A`, `A < 1/48`, and for `c ≤ (log log N)^A` any `A` | `eventually_tiltedUnitSpline_finite_packet_energy_pos_growing_overlap`, `eventually_tiltedUnitSpline_finite_packet_energy_pos_iterated_log_overlap` | proved; full matrix at growing overlap open |
| Selectivity: ζ positive, every pole-free sign gauge (Liouville, every cofinite flip) negative at the same `c ≥ 1` | `liouvilleSelector_selective_of_one_le`, `liouvilleSelector_selective_of_cofiniteFlip` | proved |
| Growing Ramanujan families: `(log(N+1) − log(K+1))Σa² ≤ Σ F_a²`, `K = Q(Q−1)`; annular frames `¼, 5/4` | `ramanujanPoleProfile_family_logarithmic_lower`, `ramanujanPoleProfile_dyadic_twoSided_frame` | proved |
| Cyclotomic floor `P_m(k) ≥ φ(m)`, `A_m(t)/φ(m) ≥ {t}(1−{t})` | `totient_le_primitiveRootPrefixEnergy`, `fract_quadratic_le_normalized_arithmeticOverlapCurvature` | proved |
| Gamma reserve at growing overlap: `archForm ≥ (κc⁻⁷ log N − bc)(c/N)M Σx²` | `archForm_atomicTest_ge_growing` | proved |
| Defect reserve `(a/c⁷)D − Cc⁹Σx²` at `N ≥ Hc⁸` | `exists_tiltedUnitSpline_complete_defect_reserve_polynomial` | proved |

## 6. Tools

**Developed**
- Spectral assembly lemma for complete Weil matrices (`MacroscopicOverlapSpectralAssembly`, `FiniteRamanujanCoordinatesTransferSpectralFloors`).
- Explicit coordinate mass `1/18` from `Q⁴ ≤ N` (`normalizedRamanujan_coordinate_mass_ge_of_raw_approximation`).
- Directed Schur/Young split of non-ratio rows (`abs_nonRatioForm_le_relative_defect`).
- Cancelled Robin calculus: polarized mixed expansion with overlap, Lipschitz stability of `bumpRobin`, dilation differences (`abs_mixed_levy_sub_robin_le`, `abs_bumpRobin_sub_le_lipschitz_difference`).
- Exact successor-shell thresholds `N log(1 + k/N) ∈ [k − k²/N, k)` (`exists_successor_gap_iff`).
- Residue-window machinery with uniform horizons over all patterns and Gram packets (`eventually_residuePrimeWindow_uniform`, `eventually_primeWindow_dominates_all_complex_Gram_packets`).
- Weighted Abel transfer with flat weights; variation version (`weightedResiduePrimeReading_sub_mean_eq`, `eventually_weightedResiduePrimeReading_variation_log_bound`).
- Harmonic-quotient square budgets (HTGeometry) applied to row errors at `N/n`.
- Conductor-uniform residue PNT and Mertens rates (`eventually_conductor_uniform_residuePrimeRealError_log_bound`).
- Explicit profiles: `tiltedUnitSpline`, `tiltedBoxPlateau` (FT `= 2L·Û_L·Û_w⁴` shifted by `iτ`), `liouvilleSelector` (threshold `< 1`).

**To build**
- Full-matrix positivity at growing overlap `c_N → ∞`: needs a conductor cutoff whose cost does not grow like `exp(c¹⁶)` and residuals with sub-`c¹⁰` cost.
- Uniform low-energy confinement with conductor count growing with `N` (current certificates fix a finite family before the horizon).
- An exhausting overlapping family (holes below the horizon top persist at `c ≤ 1`).
- Annular upper bound on `W(2R) − W(R)` from the completed arithmetic expression (needed `39/50`).

## 7. Open questions

1. Positivity of the full complete matrix along a prescribed schedule `c_N → ∞`. Which loss dominates: the `exp(c¹⁶)` conductor cutoff, the `c⁻⁷` floor, or the `c¹⁰` residual?
2. Is the `c⁻⁷` Fourier-tail floor sharp for smooth compact profiles, or can a profile family keep a `c`-independent floor?
3. Can the defect reserve `a/c⁷` be improved to a fixed fraction at growing overlap?
4. Do the polynomial packet results extend from `A < 1/48` to larger powers of `log N` (SuccessorShellArithmetic reaches `1/19`)?
5. Which overlapping atomic families exhaust compact tests, and what is their low spectrum?
6. Does the cyclotomic curvature `A_m` coincide with the overlapping spectral symbol of the complete form?
7. Signed short-difference correlations for the critical-line census (exchange-rate input, bandwidth-`4/3` surplus).

## 8. Traps

| Trap | Fact |
|---|---|
| "Touching ⇒ overlap" | At `c = 1` supports are disjoint; non-ratio interaction is one boundary star. Real overlap starts at `c > 1`. |
| "Positivity on these families ⇒ RH" | Families are not exhausting; local coverage at index `n` is about `n/N`. |
| "Fixed `c` positivity is uniform" | Horizons depend on `c` unless stated; bounded-overlap uniformity needs the separate `[1, K]` theorems. |
| "Absolute estimates suffice" | The prime main term cancels a polar term; near-Gamma cancels the downward row only through the exact divisor jet. |
| "Large positive conductor energies give positivity" | Without a defect reserve, low-energy vectors can escape to large conductors. |
| "Individual prefix positivity ⇒ coercive Gram" | The overlap Gram has a radical: packets divisible by the cyclotomic polynomial. |
| "Dyadic annuli carry prime transport" | The prime kernel vanishes on `(A, 2A]`; transport crosses annulus boundaries. |
| "Source work ceiling excludes zeros" | `O(R log² R)` includes critical zeros; it is not selective. |
| Plateau limit | The charge reserve tends to zero as plateaus approach the indicator. |
| Duplicate name | `eventually_tiltedUnitSpline_completeWeilMatrix_posDef` is declared in both `MacroscopicOverlapPositivityAtEveryOverlap` and `TheCompleteWeilFormIsPositiveAtEveryFixedOverlap` (same namespace). |

## 9. Context

**Uses**

| Programme | Imports | Role |
|---|---|---|
| RenormalizedArithmeticPotentialTheory | 30 | complete Weil matrix, completed shells, Ramanujan quasimodes, arithmetic compactness |
| SpacingScaleHarmonicAnalysis | 19 | atoms, tilted spline, Gamma reserves, row bounds |
| HTGeometry | 11 | harmonic-quotient budgets, Hermitian projections, finite Gram certificates |
| RHTower | 9 | Mertens, PNT in progressions, conductor-uniform sums |
| BezoutValuationIncidence | 5 | large sieve, divisor rows, Brownian bridge |
| SignedArithmeticHodgeTheory | 3 | horizon-uniform residual and Gram budgets |
| BiScaleUncertainty, ArithmeticLorentzianGeometry, ArithmeticEffectivityTheory | 3 each | Ramanujan bounds, one-sided cross energy, torsion Fourier coefficients |
| TransMetzlerWeilPositivity | 2 | Liouville twin and sign-gauge breaking |
| TransHorizonIncidenceMechanics, ArithmeticIntersectionTheory, ArithmeticIncidencePositivity, ArithmeticElectrostatics, ArithmeticCriticalityTheory | 1 each | single lemmas |

**Used by**: RenormalizedArithmeticPotentialTheory (14 modules), TransMetzlerWeilPositivity (9), CompletedArithmeticForms (7), SuccessorShellArithmetic (2), MainTheorems.

| Neighbour | Relation |
|---|---|
| RenormalizedArithmeticPotentialTheory | supplies the complete matrix and shell theory; imports CACT back for quasimodes, ground state, flip thresholds |
| TransMetzlerWeilPositivity | first-overlap positivity and Robin–Euler twin breaking; CACT supplies selectivity against all sign gauges |
| SuccessorShellArithmetic | sharpens the growing-overlap packet exponent |
| CompletedArithmeticForms | packages the growing-overlap and residual bounds |
| SignedArithmeticHodgeTheory | prime residual budget uniform in the horizon |

## 10. Big picture

The programme shows that the literal Weil form, with nothing modelled away, is positive on every atomic family whose overlap stays bounded, and that it separates ζ from Liouville and from every cofinite sign flip at the same overlap. Positivity is not an accident of one profile: any smooth profile whose Fourier transform has no real zeros works, and the ground state is always the pole. The mechanism is always the same triangle: a prime-defect reserve confines low energy to finitely many conductors, actual prime sums realize each conductor's energy as an approximate eigenvalue, and a Fourier tail gives every conductor a positive floor.

What this says about the RH proof: positivity through the arithmetic of finitely many conductors is now routine, so the difficulty sits entirely in growth. As overlap grows, the floor decays polynomially, the residual costs grow polynomially, and the conductor cutoff grows exponentially. Fixed packets survive to `(log N)^{1/48}`; the full matrix does not yet survive any growing schedule. An RH proof along this route needs either a conductor-count bound that grows slowly with overlap or a family that exhausts the test space without paying conductor confinement.
