# Spacing-Scale Harmonic Analysis (SSHA)

Namespace `GaloisForLFunctions.SpacingScaleHarmonicAnalysis` (sub-namespace `LengthHeight` for coordinates);
umbrella `SpacingScaleHarmonicAnalysis.lean`; 38 modules. Everything is unconditional; every `riemannHypothesis_iff_*` is
an equivalence, not a proof of RH. Several modules end with `#print axioms` lines.

## 1. Motivation

Weil's form on tests built from narrow atoms at log n, n ≤ N, is a competition between two divergent self-energies: the
archimedean place charges log(1/w) per atom of width w, the prime place pays at most log N. They meet at the atom
spacing δ_N = log(1 + 1/N) ≍ 1/N, which is also the Nyquist scale: zeros up to height ≍ 1/w sample the Dirichlet
polynomials of length N at density log N/2π. SSHA measures everything in the overlap ratio wN: how far the
archimedean place pays the prime place (a fixed fraction of the spacing, for every twist), where positivity becomes
the Riemann hypothesis (any unbounded overlap growing faster than (log log N)^{1+ε}), where the arithmetic gauge
becomes visible (non-ratio lags), and that the pole is the only correction RH allows.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Atomic test | `atomicTest` (ArithmeticElectrostatics) | f_x = Σ_{n≤N} x_n g(· − log n) |
| Lévy density, energy | `archLevyDensity` (RHTower), `levyEnergy` | ω(y) = e^{−y/2}/(1 − e^{−2y}) ~ 1/(2y); ∫ω‖f − f(·+y)‖² |
| Archimedean, Markov, Weil forms | `archForm`, `levyMarkovForm`, `markovQuad`, `weilQuad` | 2θ'(0)‖f‖² + Lévy; arch − primeSum; Q = M + 2m₋m₊ |
| Pole moments | `poleMomentNeg`, `poleMomentPos` | m_∓ = ∫ g e^{∓u/2} |
| Robin constants | `archRobinConstant`, `bumpRobin`, `profileRobin`, `selfEnergyConstant` | 2c_∞ = 2log2 + π/2; β(g) = ∫_0^w‖g − g(·+y)‖²/(2y) |
| Dilations | `atomDilate`, `dilate` | φ(·/w); kφ(k·) (unit mass) |
| Autocorrelation, cross term | `bumpCorr`, `bumpAutocorr`, `atomCrossTerm`, `crossBound` | G(t) = ∫g g(·+t); two-atom Lévy coupling |
| Spacing constants | `spacingRatio`, `spacingConstant`, `spacingWidthRatio` | c₁ = 1/(32e^{5/2}); C = 2(log4+4)+1; c₀ = c₁e^{−(C+2|θ'(0)|)} |
| Tilt | `tilt` | r(n) = 1 + n/N |
| Lag forms | `lagForm`, `ratioLag`, `nonRatioLag`, `nonRatioForm`, `nonRatioRow` | prime sum split by k = n/m exact or not |
| Dirichlet polynomial | `dirichletPoly`, `mellinPolynomial` | D_x(z) = Σ x_n e^{iz log n} |
| Twisted form | `weilQuadTw`, `twistCoeff`, `pairing`, `alignedTwist` | Λ replaced by λ, |λ| ≤ Λ |
| Synthesis | `cellSum`, `trapSum`, `emWeights`, `logNode`, `blockSize`, `synthErr`, `synthErrTwo`, `emErr`, `gevErr` | atoms reproducing a fixed test |
| Overlap growth | `OverlapGrowth`, `OverlapGrowthTwo`, `OverlapGrowthPow`, `OverlapGrowthGevrey` | N/κ_N beats √log, (log)^{1/4}, (log)^{1/q}, (log log)^s |
| Stable form | `StableForm` | translation invariant, continuous under small Lipschitz perturbations |
| Profiles | `plateau`, `gevreyProfile`, `dcProfile`, `tiltedUnitSpline` | plateau; Gevrey 2; Gevrey 1+1/r; boosted cubic spline without real Fourier zeros |
| Coordinates | `LengthHeight.height`, `overlap`, `bandwidth`, `aperture` | X/c, X/T, log X/log T, log X/2 |

## 3. Language

- *Width* w, *spacing* δ_N, *overlap ratio* wN (or N/κ_N); *separated* (w < δ_N) vs *overlapping*.
- *Ratio lag*: n = km (exact Hecke pairing); *non-ratio lag*: log k within w of log(n/m), n ≠ km.
- *Universal* law: holds for every twist |λ| ≤ Λ; *selective*: distinguishes ζ.
- *Synthesis*: weights on the log-lattice making the atomic test approximate a fixed test; order = error exponent.
- *Pole correction rank*: number of negative squares of the Markov form that RH tolerates (the pole: one).

## 4. Mechanisms

**A. Constant one on both sides**
1. 1/(2y) ≤ ω(y) ≤ e^{y/2}/(2y) on (0,1] ⇒ atom self-energy log(1/w) + 2c_∞ + β/‖g‖² + O(w), constant one; prime Schur rows A(⌊N/m⌋) + log m ≤ log N + O(1).
2. Two separated atoms at distance s couple through ω(s)(∫g)² + O(w); ω has inverse-square increments (ω(a) − ω(b) ≤ 19(b−a)/a²).

**B. Stability at the spacing**
3. Cross-kernel row at atom m ≤ 4e^{5/2}wm(1 + log(N+1)): relative width × log N, largest on the top dyadic block.
4. Tilted Schur weight 1 + n/N: down tower loses (m/4N)log m (proper divisors ≤ m/2), up tower costs log4 + 4 (Chebyshev). At w ≤ c₁/N this pays the cross kernel scale by scale ⇒ M ≥ (2θ'(0) + log(1/(wN)) − C)‖f‖² and M ≥ 0 at w ≤ c₀δ_N, all N.
5. Universality: below the spacing every prime pairing is an exact Hecke pairing; twisted prime sum ≤ ‖g‖²P_N(|x|). Diamagnetic: Lévy energy is a Dirichlet form, so arch − twisted ≥ Markov(|f|): ζ is the ground state of its gauge orbit.

**C. Overlap calculus**
6. primeSum f_x = ‖g‖²P_N(x) + NR_w(x) at every width; gauge factor ω(k) − ω(m)ω(n) vanishes on ratio lags, so twins differ only on non-ratio lags (none below spacing, present within 4δ_N above).
7. Non-ratio rows at ratio K: O(K) + 2e^{3/2}K(m/N)(log m + 1): three rows of shape (m/N)log N compete (tilt ¼, cross kernel ≍ K, non-ratio ≍ 2e^{3/2}K).
8. Gram rows bounded at fixed overlap: ‖f_x‖² ≤ ‖g‖²(1 + 2ce^c)‖x‖².

**D. Synthesis ⇒ RH equivalences**
9. Weil's form is continuous in the Lévy norm: perturbation of size ε, Lipschitz K moves Q by O(ε√log(K/ε)).
10. Log-lattice gaps ≤ 1/n₀. Cell weights: error O(k/n₀ + 1/k); trapezoid: O((k/n₀)² + 1/k); Euler–Maclaurin weights F(log n − c)/n: O((k/n₀)^p + 1/k) for every p for smooth profiles (log tower T_{j+1} = T_j' − (j+1)T_j); Gevrey profiles with p ≍ log log k: O(1/log²k + 1/k). The tilted cubic spline has fourth-order error O((k/n₀)^4 + 1/k), via smooth regularizations with bounded fourth-derivative L¹ norms.
11. Hence for each order: if Q < 0 on some test, Q < 0 on atomic families eventually ⇒ RH ⇔ eventual positivity; the same transfer holds for every stable form (twists, Markov form, pole hyperplane after a vanishing bump correction).

**E. The pole and the zeros**
12. M(u + iv) = M(u) + M(v) and M is not PSD ⇒ under any overlap growth M < 0 on atomic families unconditionally; on the pole vector at width cδ_N, M < 0 once c > e^{β/‖φ‖²}/(2π) (finite part log(1/c) + β/‖φ‖² − log 2π, γ cancels), every c ∈ (e/2π, 1) via plateaus.
13. h_{f_x} = h_g·D_x; one zero weighs ≤ m_ρ e^{2|σ|/k}(‖φ‖₁²/‖φ‖₂²)((N+1)/k)/(2√(β(1−β))) of the diagonal energy.
14. Gamma reserve: a profile with no real Fourier zeros has a Fourier floor on [c,101c]; Montgomery–Vaughan gives band mass 48N‖x‖² ⇒ archForm ≥ (a log N − b)‖x‖² at every fixed overlap.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Self-energy constant one; exact Robin constant | `levyEnergy_atom_ge`, `abs_levyEnergy_atom_sub_le`, `archRobinConstant_eq` | proved |
| Cross-kernel law; tilted prime rows | `levyEnergy_atomicTest_ge`, `atomicWeilForm_le_tilted` | proved |
| Stability at the spacing (Markov ≥ 0, Re W + 2S² ≥ 0) | `markovEnergy_atomicTest_nonneg_spacing`, `re_W_add_sinh_sq_nonneg_spacing` | proved |
| Universal over every twist; diamagnetic inequality | `twistedMarkov_atomicTest_nonneg_spacing_of_abs_le`, `diamagnetic_inequality` | proved |
| Fixed width (unbounded overlap) ⇔ RH; neg. index = # right zeros | `riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width`, `zeta_splineAtomic_negIndex_law` | proved |
| Critical exponent 1; overlap (log N)^{½+ε} | `riemannHypothesis_iff_atomicFamilies_nonneg`, `riemannHypothesis_iff_atomicFamilies_nonneg_log` | proved |
| Fourth root; every root (log N)^ε | `riemannHypothesis_iff_atomicFamilies_nonneg_log_quarter`, `riemannHypothesis_iff_atomicFamilies_nonneg_log_pos` | proved |
| Tilted spline: every K(log N)^{1/8} ⇔ RH, full space and pole hyperplane | `riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_every_eighthRoot_multiple`, `riemannHypothesis_iff_tiltedSpline_pole_nonneg_every_eighthRoot_multiple` | proved |
| (log log N)^{1+ε} window (Denjoy–Carleman) | `riemannHypothesis_iff_gevreyProfile_nonneg_loglog`, `exists_dcProfile_loglog` | proved |
| Gauge: twist seen ⇔ not Weil positive | `atomicFamilies_negative_iff_of_growthPow`, `liouville_atomicFamilies_negative_of_growthPow` | proved |
| Markov fails under overlap; pole hyperplane ⇔ RH | `markov_atomicFamilies_negative_of_growthPow`, `riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow` | proved |
| Markov fails inside separated regime (c > e/2π) | `markov_poleVector_negative_inside_separated` | proved |
| Universal threshold finite | `universalThreshold_bracket` | proved |
| Gauge lives on non-ratio lags | `twistedPrimeSum_sub_primeSum_gauge_eq_of_supp`, `exists_nonRatio_pair` | proved |
| Non-ratio rows at bounded overlap | `abs_nonRatioForm_le`, `nonRatioRow_le_of_ratio` | proved |
| Weight of one zero | `norm_Wsummand_atomicTest_dilate_le` | proved |
| Gamma reserve at every fixed overlap | `exists_tiltedUnitSpline_archForm_reserve`, `exists_noRealZero_archForm_reserve` | proved |

## 6. Tools

**Developed**
- Sharp Lévy density bounds; exact atom self-energy with Robin constant; two-atom pairing; inverse-square density increments.
- Tilted Schur test; Chebyshev and Mertens rows; non-ratio row counting (log windows, divisor reindexing).
- Lévy-norm continuity of Weil, twisted and Markov forms (`StableForm`); mollification; pole-hyperplane correction.
- Cell, trapezoid, Euler–Maclaurin and Gevrey syntheses on the log-lattice; Gevrey and Denjoy–Carleman explicit profiles.
- Montgomery–Vaughan band mass for atomic families; Fourier floor of profiles without real zeros.
- Length/height/overlap/aperture coordinate identities.

**To build**
- The critical constant of the Markov form in [c₀, e/2π] and of Re W + 2S² (where the pole decides).
- A positivity mechanism at bounded overlap that reads the signs of non-ratio lags.
- A large sieve over the zeros (frame constants for length-N Dirichlet polynomials vs wN, T/N).
- The alias fraction of the best synthesis below (log log N)^{1+ε}; whether any unbounded growth suffices.

## 7. Open questions

1. Is positivity at every bounded overlap K (all N) a theorem, and what is the largest such K for ζ (between c₀ and the RH regime)?
2. Does any growth κ_N → ∞ of the overlap already make positivity equivalent to RH, or is there a sub-(log log N) window where positivity is unconditional?
3. Can a signed test separate ζ from every twin flipping a prime ≤ p_N at bounded overlap with margin bounded below?
4. Is there a Hecke-covariant tilt that survives overlap?
5. Exact value of the universal threshold K_univ and of the Markov threshold c_M*.

## 8. Traps

| Trap | Fact |
|---|---|
| The self-energy constant does not matter | Constant e^{−1/2} stops at N^{−O(1)}; constant one reaches the spacing |
| The cross kernel is lower order at the spacing | Its row ≍ c(m/N)log N, as large as the bounded margin |
| Uniform or power Schur weights suffice | Only a tilt separating m from m/2 pays the down tower |
| Stability at the spacing is RH | It is a theorem, universal over twists |
| A fixed-width family is "near the spacing" | Its overlap is unbounded; positivity there is RH |
| RH-strength needs polynomial overlap | Any (log log N)^{1+ε} suffices |
| Gauge selectivity can come from arch − prime on |·|-closed families | ζ is the ground state; only the pole or non-ratio lags/signed families can separate |
| Twins differ from ζ on every lag | Only on non-ratio lags |
| The pole correction is a method artifact | Markov alone fails at c > e/2π, and under any overlap growth unconditionally |
| Universal (twist-blind) methods reach every bounded overlap | K_univ < ∞ (dipole at N = 2) |
| Width w and support cutoff are the same coordinate | Aperture includes profile width: cutoff N e^{(b−a)w} |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 16 (Weil–Markov, Lévy forms, CHMD, DQPT Euler–Maclaurin, Weil spectral criteria) |
| ArithmeticElectrostatics | 3 (atomic tests, Weil form at atomic resolution, gauge invisibility) |
| RenormalizedArithmeticPotentialTheory | 2 (covariant counterterm, Markov finite part) |
| HTGeometry, ArithmeticOrientationGeometry, ArithmeticCastelnuovoSeveri | 2 each (Kronecker/inertia, spline orbit, Weil Grams of translates) |
| TransMetzlerWeilPositivity, SelectivePositivityAndThresholdLaws, BiScaleUncertainty, ArithmeticIndexDescent, arithmetic-positivity-theory | 1 each |

| Used by | Modules |
|---|---|
| CriticalArithmeticCorrelationTheory | 16 |
| RenormalizedArithmeticPotentialTheory | 11 |
| TransMetzlerWeilPositivity | 8 |
| ArithmeticLorentzianGeometry | 6 |
| ArithmeticCastelnuovoSeveri | 5 |
| SignedArithmeticHodgeTheory, SelectiveMultiscaleArithmeticPositivity, ArithmeticIndexDescent | 3 each |
| SuccessorShellArithmetic, SquareRootThreshold, RHTower, HeckeKreinToeplitz, EffectiveArithmeticHodgeTheory, CompletedArithmeticForms, MainTheorems | 1 each |

| Neighbour | Relation |
|---|---|
| ArithmeticElectrostatics | atomic tests and stability at N^{−O(1)}; SSHA pushes it to a fixed fraction of the spacing |
| RenormalizedArithmeticPotentialTheory | supplies log N − γ counterterm; consumes the overlap law (RH ⇔ PSD at c = 2(log N)^α) and Gamma reserve |
| CriticalArithmeticCorrelationTheory | consumes overlap law, reserves, Robin constants for completed spectra |
| TransMetzlerWeilPositivity | supplies Montgomery–Vaughan band mass; consumes cross-kernel and spacing laws |
| ArithmeticOrientationGeometry | spline orbit law that SSHA restricts to atoms log n |

## 10. Big picture

SSHA pins down where the difficulty of RH sits on the scale axis. At widths below a fixed fraction of the atom spacing
positivity is a theorem — and it is universal: it holds for every twist of the primes, Liouville included, so it
contains no arithmetic. At any overlap growing faster than (log log N)^{1+ε}, narrow atoms reproduce every fixed test,
so positivity there is exactly RH, and every non-positive twin is detected. Between them lies bounded overlap, where
the prime form begins to read signs through non-ratio lags and where twist-blind methods provably stop.

For the RH programme this means two things. First, the archimedean place can pay the prime place only up to the
Nyquist scale; beyond it, positivity must come from the pole (the one negative square RH permits) together with a
selective, sign-reading input from non-ratio lags. Second, the gap between theorem and RH is not polynomial in N but
iterated-logarithmic in the overlap: any argument that controls positivity at slowly growing overlap with constants
uniform in N would be a proof, and any argument blind to the signs of the primes cannot do it.
