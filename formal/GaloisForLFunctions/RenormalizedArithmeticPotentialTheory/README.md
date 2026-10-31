# Renormalized Arithmetic Potential Theory (RAPT)

Namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory` (sub-namespace `CompletedShell` for the shell energy);
umbrella `RenormalizedArithmeticPotentialTheory.lean`; 189 modules (subfolders `Conductor/`, `Signature/`).
Everything is unconditional. Two exceptions in form, not in content: the general-overlap spectral counts in
`TheBoundedCompleteWeilSpectrumIsTheCompletedShellSpectrum` / `TheLowCompleteWeilSpectrumLivesOnTheLowConductors` take a
prime-defect reserve and quasimode convergence as binders (discharged for the tilted unit spline through
CriticalArithmeticCorrelationTheory); `LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis` is an equivalence.

## 1. Motivation

Over 𝔽_q Weil uses one pairing that is positive, Frobenius-equivariant and finite on the diagonal. Over ℤ the diagonal
diverges at both places: torsion orbits at the prime place (Abel self-energy log 1/(1−r)), atoms at log n at the
archimedean place (width-w self-energy log 1/w), and both meet at the arithmetic point (the pole). Every pairing of the
explicit formula is a regularized self-energy. RAPT is the theory of the renormalization data — regulator, counterterm
(rank, survival cone), Hecke anomaly, paying place — then of the finite parts left after subtraction, and finally of the
renormalized spectrum: of Weil's prime matrix P_N and of the literal complete Weil matrix on atoms of width c/N.
It locates RH exactly: positivity at every fixed overlap c is proved; positivity at overlap c_N = 2(log N)^α is RH.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Weil prime kernel / form | `weilPrimeKernel` (ArithmeticEffectivityTheory), `atomicWeilForm` (ArithmeticElectrostatics), `primeBilinear` | P(m,n) = Λ(n/m)(n/m)^{−1/2}; P_N(x) on orders ≤ N |
| Pole vector; polar functional | `poleVector`, `polarFunctional` | u_n = n^{−1/2}; ℓ(x) = Σ x_n n^{−1/2} |
| Step / class profiles | `truncPole`, `stepProfile`, `classPole`, `classDensity` | u^{(M)} = u·1_{n≤M}; valuation classes v_p(n) = j, density δ_j = (1−1/p)p^{−j} |
| Tensor counterterm | `tensorCounterterm`, `sieveTensorCounterterm` | Σ_j δ_j^{−1} ℓ_j(x)² |
| Hecke shift | `heckeShift` | (T_t x)(n) = x(n/t) |
| Coupled counterterm, joint germ | `jointGram`, `jointGerm` | prime block ⊕ archimedean block |
| Mertens sum | `mertensSum` (RHTower) | A(y) = Σ_{t≤y} Λ(t)/t = log y − γ + o(1) |
| Pole defect | `poleDefect` | D_N(x) = Σ_{mt≤N} Λ(t)(x_{mt} − x_m/√t)² |
| Renormalized prime energy | `renormalizedPrimeEnergy` | log N·|x|² − ⟨P_N x, x⟩ |
| Ramanujan profiles / energy | `ramanujanPoleProfile`, `normalizedRamanujanMode`, `ramanujanAdjunctionEnergy` | c_m(n)/√(φ(m)n); E(m) = γ + log m + τ(m), τ = tame different |
| Valuation step | `valuationStep` | 1_{j≥k} − (p−1)^{−1}1_{j=k−1}: eigenvector of the p-tower |
| Tower finite part / deficit | `towerFinitePart`, `towerDeficit`, `localEuler` | F_p(b) = 2γ_p|b|² + log p(|b|² − K_{p^{−1/2}}(b)); d_p = √p log p/(p−1) − γ |
| Finite sieve | `sieveEuler`, `sievedHarmonic`, `sieveClassPole`, `sieveAdjunctionOperator`, `sieveAdjunctionBasis` | γ_Q = γ + Σ_{p∈Q} log p/(p−1); A_Q = diag(log n) + γ_Q − P on ℓ²(Q-supported) |
| Sign gauge | `IsSignGauge`, `liouvilleSign`, `primeSignGauge`, `charGauge` | completely multiplicative ±1 twist of P |
| Harmonic measure tools | `harmonicVar`, `glauberForm`, `shellTau`, `roughInterval` | variance under 1/n; prime-ladder Dirichlet form |
| Markov form | `markovEnergy`, `levyEnergy` | archimedean form minus prime sum on atomic tests |
| Complete Weil matrix | `completeWeilMatrix`, `fullWeilHorizonMatrix` | literal Weil form (both poles) on atoms φ((u − log n)/w), w = c/N, / atom mass |
| Center kernel | `archimedeanCenterKernel` | Lévy density at log-gaps; in pole gauge ½(1/|n−j| + 1/(n+j)) |
| Completed energies | `completedShellEnergy`, `completedConductorEnergy` | E(c) = (2/M)Σ_k k^{−1}∫_{kc}^∞|φ̂(2πt)|²; E_m(c) by Möbius inversion |
| Resolution data | `resolutionBottom`, `resolutionThreshold`, `twistBound`, `packetEnergy`, `flipCoupling` | sign of a twisted Weil matrix at overlap c |
| Horizon boundary | `horizonBoundary` | B_N(s) = ζ(s) − Σ_{n≤N} n^{−s} (Euler–Maclaurin) |

## 3. Language

- Counterterm: *scalar / polar / orbital / tensor*; *survival cone* = its kernel; a coupling *pays* a direction.
- Regulator: *Abel radius*, *spacing radius*, *horizon* (orders ≤ N). Rank of the counterterm belongs to the regulator.
- *Matching coefficient* κ (divergence κℓ²) vs *finite part* 2α (from A_ε(y) = κ log y + α + o(1)).
- *Overlap* c = wN: c < 1 separated atoms; c fixed > 1 bounded overlap; c → ∞ growing overlap.
- *Conductor* m labels Ramanujan modes; *flip* = sign twist at a prime; *threshold* = least overlap that resolves it.

## 4. Mechanisms

**A. Counterterm algebra**
1. Coupled survival: positive [[A,C],[Cᵀ,D]] ⇒ ker D ⊆ ker C; prime survival ≤ rank D. Rank-one archimedean germ pays exactly the arithmetic point e₁ (`jointGram`).
2. Gårding = finite-rank survival: A ≥ 0 on the common kernel of k functionals ⇔ survival cone of a rank-k PSD counterterm. RH ⇔ Weil's counterterm can be zero.

**B. Horizon regulator**
3. Polar law: ⟨u^{(M)}, P u^{(M')}⟩ = H_M H_{M'} + O(H_min); step profiles P_N = ℓ² + O(mass); extends to every BV profile g(log n/log N).
4. Tensor law: class-wise P_N = Σ_j δ_j^{−1}ℓ_j² + O(H_N); rank unbounded on p-adic classes; [p] maps class j → j+1 with δ/p and ℓ/√p, so the finite part is exactly Hecke covariant (no anomaly). Exact factorization: P(dk, el) = [d=e]P(k,l) + [k=l]P(d,e) over a finite sieve.
5. Residues: unit classes mod q have rank-one divergence (weight q/φ(q)); a class function f is seen only through its mean; Re χ, Im χ profiles have no (log N)² term.

**C. Finite parts are Mertens constants**
6. If A_ε(y) − κ log y → α then P_N(εx) = κℓ² + 2α|x|² + o(mass); necessary and sufficient: harmonic mean of the Mertens error. ζ: κ = 1, α = −γ.
7. p-adic classes: finite part −2γ_p + log p(K_{p^{−1/2}} − 1) (tower form). Sign: F_p ≥ 0 ⇔ d_p ≤ 0 ⇔ p ≥ 47; valuation potential j log p left by the archimedean matching pays the deficit for every p.
8. Finite sieve: one Euler constant γ_Q shared by harmonic and Mertens sums; profile finite part −2γ_Q|b|² + Σ_p tower forms; sieved log sum has no linear log N term.
9. Characters: α_χ = −L'/L(1,χ); residue finite part diagonalized by characters with eigenvalues 2 Re(−L'/L(1,χ)). Gauge rigidity: among κ = 1 gauges α ≤ −γ with equality iff ε ≡ 1; each flipped prime lowers α by ≥ 2 log p/p; Liouville separates by 2(2γ + τ).

**D. Ground state of the prime form**
10. Exact ground-state identity P_N(x) + D_N(x) = Σ_n (A(⌊N/n⌋) + log n) x_n²; pole is the top: P_N ≤ (log N − γ + ε)|x|², sharp.
11. Harmonic measure 1/n on [1,X] tensorizes over primes (approximate Efron–Stein, thin rough shells by Selberg sieve) ⇒ Poincaré constant of the multiplicative walk = 2 log 2; the 2-adic step attains it. Top of P_N on the pole hyperplane = log N − γ − 2 log 2 + o(1).
12. Box/ladder chains are exactly solvable (valuation steps, eigenvalues k log p + log p/(p−1)); the top spectrum of P_N is exhausted by integers m with energy log m + τ(m).
13. Fixed-point law: spectrum of α diag(log n) + P_N fills [κ₋, κ₊]·log N, κ² = ακ + 1; torsion pairing (α = 1) costs φ_golden·log N, extremal charges φ^{ω(n)}/√n.

**E. Ramanujan spectral exhaustion**
14. Ramanujan correction identity: Σ_t (c_m(nt) − c_m(n))Λ(t)/t = −(log m + τ(m))c_m(n) − downward jets ⇒ r_m is a quasimode of P_N at log N − E(m).
15. Bounded defect ⇒ uniform finite Ramanujan approximation (valuation boxes, smooth–rough fibres); conductor cutoff exp(C(K+1)) suffices and is necessary (E(2^k) = γ + (k+1)log 2).
16. Coordinate certificate + residuals ⇒ exact counts: #{eigenvalues of log N − P_N below T} = #{m : E(m) < T}; simple eigenlines converge to Ramanujan lines. Finite-sieve version: A_Q has the density-weighted Ramanujan basis as eigenbasis, compact resolvent.

**F. Archimedean place at atomic width**
17. Lévy self-energy has constant one; Markov form ≥ 0 down to width e^{−C}/(N(1+log N)) (archimedean pays the prime place up to a logarithm).
18. Finite part at the spacing: ground energy log(1/(2πwN)) + β(φ)/‖φ‖² (Gamma factor, self-energy and pole combine to −log 2π). Arithmetic modes at width K/N: energy log(K_m/K), K_m = m e^{τ(m)} e^{β/‖φ‖²}/(2π).

**G. Complete Weil matrix**
19. Exact decomposition at every c: W = (log N + self(c) − γ + err)I − P + Center − CrossErr + PoleErr + Overlap − NonRatio. Center row cancels the restored poles up to a boundary layer paid by top atoms.
20. c < 1: Ramanujan quasimodes at E_m = log(1/(2πc)) + β/M + log m + τ(m) + [m=1]c(∫φ)²/M; coercivity a|x|² + ((1−c)/4)D ≤ W; spectrum = these energies with multiplicity.
21. Every c > 0: residual = −(Up − κ_m(c)) + o(1), Up the upward prime window; affine prime shells give the shell correction κ_m(c). Completed energies E_m(c) = (2/(Mφ(m)))Σ_{(a,m)=1}(m/a)∫_{ac/m}^∞|φ̂|² ≥ 0 (Möbius signs collapse to coprimality); conductor one minimizes; E(c) → 0 as c → ∞ (Stirling).
22. Overlap ↔ RH: SSHA second-order overlap law transfers ⇒ for c_N⁴/log N → ∞, c_N = o(N): RH ⇔ W eventually PSD.

**H. Selectivity**
23. Twists enter only through defect × multiplicative correlations of packet profiles; sign at fixed c = sign of an explicit quadratic form on finitely many Ramanujan coordinates.
24. Every finite flip set is resolved at an exact positive threshold (profiles without real Fourier zeros); index of the twin grows unboundedly with c; c_0(ω_p) is between (κp/log p)^{1/7} and (Kp)^{1/7}: no bounded overlap sees all flips.

**I. Zero side**
25. Pole mode: Q(f_pole) = Re Σ_ρ m_ρ ĝĝ B_N(1−ρ)B_N(ρ): zeros see the pole only through the Euler–Maclaurin horizon boundary; general x through Möbius horizons of a = (√n x)*μ. Horizon charge is blind to Re ρ; theta source carries the same boundary; windowed aperture modes are exponential box tests.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Archimedean place pays exactly the arithmetic point | `TheArchimedeanPlacePaysTheArithmeticPoint` | proved |
| Gårding ⇔ finite-rank survival | `garding_iff_survival`, `garding_iff_regularized` | proved |
| Covariant counterterm log N − γ + o(1), pole extremal | `covariantCounterterm_sandwich`, `covariantCounterterm_sharp` | proved |
| Torsion counterterm φ_golden log N + O(1) | `torsionCounterterm_golden` | proved |
| Horizon counterterm: unbounded rank, tensor law, Hecke covariant | `horizonCounterterm_rank_unbounded`, `TheHorizonCountertermIsHeckeCovariant` | proved |
| Finite part = 2× Mertens limit; −2γ for ζ | `TheFinitePartIsTwiceTheMertensLimit`, `TheFinitePartIsEulersConstant` | proved |
| Tower deficit sign change 43/47; valuation potential pays | `TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven`, `towerFinitePart_add_valuation_ge` | proved |
| ζ maximizes the finite part among κ = 1 gauges | `finitePartLimit_le_and_eq_iff`, `liouvilleLimit_le_and_eq_iff` | proved |
| Character Mertens limit = −L'/L(1,χ); character diagonalization | `charMertensLimit_eq_neg_logDeriv`, `sum_residueFinitePart_mul_char` | proved (PNT for characters) |
| Ground-state identity and pole top | `eventually_atomicWeilForm_add_poleDefect_le` | proved |
| Spectral gap 2 log 2 below the pole, 2-adic step first excitation | `eventually_atomicWeilForm_le_two_log_two`, `eventually_atomicWeilForm_below_pole_two_log_two` | proved |
| Matched prime Gram hyperbolic (one positive direction) | `Signature/TheMatchedPrimeFormHasOnePositiveDirection` | proved |
| Matched sieve operator: Ramanujan eigenbasis, compact resolvent | `TheSieveOperatorHasTheAdjunctionEigenbasis`, `TheAdjunctionResolventIsCompact` | proved |
| Bounded prime spectrum = adjunction spectrum; eigenlines | `eventually_fullPrime_spectral_count_eq`, `exists_simple_fullPrime_eigenline` | proved |
| Exponential conductor cutoff, necessary and sufficient | `exists_exponential_conductor_cutoff_of_poleDefect_le`, `PrimeDefectConfinementMustRetainLowEnergyConductors` | proved |
| Markov finite part −log 2π at the spacing | `eventually_markovEnergy_atomicTest_ge`, `TheArchimedeanFinitePartIsMinusLogTwoPi` | proved |
| Complete Weil spectrum for c < 1 | `TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum` | proved |
| Upward defect = shell correction at every c | `tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm`, `tendsto_sum_sq_upwardPrimeRow_sub_shellCorrection` | proved |
| Completed shell energy positive Fourier integral; conductor repayment | `TheCompletedShellEnergyIsAPositiveFourierIntegral`, `TheShellsRepayEveryConductor` | proved |
| Spectrum bottom → E(c) > 0 at every fixed c; RH ⇔ PSD at c = 2(log N)^α | `tiltedUnitSpline_overlap_window` | proved (tilted unit spline) |
| Flip thresholds exact and polynomial in p | `primeFlip_resolutionThreshold_spec`, `tiltedUnitSpline_primeFlip_resolutionThreshold_sharp_lower`, `tiltedUnitSpline_flip_threshold_polynomial` | proved |
| Zeros see the pole mode only at the horizon | `weilQuad_poleMode_eq_tsum`, `weilQuad_atomicTest_eq_tsum_mobiusHorizon` | proved |
| Capstone (26 laws) | `renormalized_arithmetic_potential_theory_laws` | proved |

## 6. Tools

**Developed**
- Weighted Schur test with tilted pole; ground-state transform by n^{−1/2}; ground-state identity P + D = row potential.
- Harmonic-measure tensorization over primes (rough intervals, thin shells, `shellTau`), smooth–rough fibration, box Poincaré.
- Exactly solvable towers and box chains (valuation steps); Ramanujan sums as products of valuation steps.
- Mertens toolkit: gauged, sieved, residue-class and character Mertens sums with constants; harmonic-convolution transfer.
- Finite Ramanujan approximation with explicit conductor cutoffs; min–max / Davis–Kahan packet machinery.
- Complete Weil error decomposition; center kernel; Riemann-sum shells; completed energies via Poisson, Stirling and Möbius.
- Twisted packet calculus; resolution bottom and threshold; flip coupling bound.
- Euler–Maclaurin horizon boundary and Möbius horizons for the zero-side expansion.

**To build**
- A lower bound for the complete Weil matrix with margin surviving c_N = 2(log N)^α (the RH step).
- Reserve and quasimodes at general overlap for profiles other than the tilted spline.
- Mertens constants for Artin/Hecke L-functions (finite parts of Chebotarev patterns).
- Torsion-pairing O(1) term; finite parts of twisted torsion pairings.

## 7. Open questions

1. Rate of E(c) → 0 versus the error terms as c grows with N: where exactly does positivity become RH?
2. Does any regulator give finite Hecke-covariant self-intersection with a nonzero survival cone (beyond the horizon tensor one)?
3. Uniform-in-p flip resolution at overlap c: what overlap profile sees every prime at once (c*(p) → ∞ forbids bounded c)?
4. Finite part of all primes at once in class profiles (growing sieves); joint Hodge index on all valuation classes.
5. Can the zero-side horizon boundary B_N(1−ρ)B_N(ρ) be controlled independently of Re ρ for non-pole modes?

## 8. Traps

| Trap | Fact |
|---|---|
| Counterterm rank is intrinsic | It belongs to the regulator (Abel: full rank; horizon: polar/tensor) |
| Coupling lowers prime counterterm rank | Never; archimedean pays one direction |
| Renormalization is anomalous | At the horizon [p] acts by density 1/p, polar p^{−1/2}: exact covariance |
| Continuum model gives the torsion constant e/(e−1) | Extremal charges are multiplicative: golden ratio |
| Raw prime kernel has local Hodge index | Ladder 1..p⁵ has two positive squares; only the matched form is hyperbolic |
| Gauges are distinguished by divergence | Finite flips have identical κ; only finite parts separate them |
| Residue classes are seen by the horizon | Divergence is rank one on units; residues live in the finite part |
| Fixed-overlap positivity is evidence for RH | Holds unconditionally at every fixed c and on an unbounded schedule; RH is growth (log N)^α |
| Margin at overlap c is uniform | E(c) → 0; flip thresholds c_0(ω_p) → ∞ |
| General-overlap counts are unconditional | They take reserve + quasimode binders; unconditional only for c < 1 and the tilted spline |
| Overlap Gram smoothing keeps the pole defect | Needs the ¼ correction (exact threshold) |
| Several modules end with `#print axioms` lines | Diagnostic only; no logical content |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 30 (Mertens, Lévy density, Euler–Maclaurin, PNT for characters) |
| HTGeometry | 27 (harmonic finite parts, atomic tests, Weil quadratic form) |
| CriticalArithmeticCorrelationTheory | 16 (affine prime shells, reserve, quasimodes, polynomial floor) |
| SpacingScaleHarmonicAnalysis | 15 (atomic stability, overlap growth law) |
| ArithmeticIntersectionTheory | 10 (tame different, tower form, transverse towers) |
| ArithmeticLorentzianGeometry | 8 (Metzler dichotomy, Hardy–Blaschke bases) |
| BiScaleUncertainty, SelectiveMultiscaleArithmeticPositivity, BezoutValuationIncidence, ArithmeticElectrostatics | 4–5 each |
| TransMetzlerWeilPositivity, RenormalizedBiarithmeticGeometry, ArithmeticIncidencePositivity, others | 1–2 each |

| Used by | Modules |
|---|---|
| CriticalArithmeticCorrelationTheory | 27 (Ramanujan certificates, completed spectrum, conductor cutoffs) |
| TransMetzlerWeilPositivity | 9 (complete Weil errors, arithmetic finite part, spectrum) |
| ArithmeticCountingPositivity | 9 (adjunction spectrum, matching density, BV horizon laws) |
| SuccessorShellArithmetic | 7 (completed shells, flip thresholds, pole collapse) |
| SelectiveMultiscaleArithmeticPositivity | 5 (gap 2 log 2, Liouville separation, spectral points) |
| ArithmeticLorentzianGeometry, SignedArithmeticHodgeTheory, HeckeKreinToeplitz, SpacingScaleHarmonicAnalysis | 2–4 each |
| ArithmeticElectrostatics, ArithmeticIntersectionTheory, ArithmeticCastelnuovoSeveri, AdelicKreinGeometry, HeckeLFunctions, CompletedArithmeticForms, ArithmeticIncidencePositivity | 1 each |

| Neighbour | Relation |
|---|---|
| RenormalizedBiarithmeticGeometry | supplies survival cones and germs; RAPT computes them for the explicit formula |
| ArithmeticIntersectionTheory | supplies intersection numbers and towers; RAPT renormalizes their diagonal and computes finite parts |
| ArithmeticElectrostatics | atomic Weil form and stability; RAPT sharpens constants to one and to the spacing |
| SpacingScaleHarmonicAnalysis | overlap growth law; RAPT turns it into RH ⇔ PSD at logarithmic overlap |
| CriticalArithmeticCorrelationTheory | mutually dependent: affine prime shells and reserves in, completed spectrum and certificates out |
| ArithmeticCountingPositivity, SuccessorShellArithmetic | consume the adjunction spectrum and completed shells |

## 10. Big picture

Every divergence of the explicit formula is understood: its rank is set by the regulator, Weil's own horizon regulator is
Hecke covariant with a polar (tensor) counterterm, and what remains is a computed finite part built from Euler's constant,
local tower forms and logarithmic derivatives of L-functions at 1. The renormalized prime form has a clean spectrum — the
integers, with energies log m + tame different, attained by Ramanujan sums — and the archimedean place pays it down to
the atom spacing. Positivity of the literal complete Weil matrix is therefore proved at every fixed overlap, with an
explicit completed spectrum whose bottom is a positive Fourier integral.

What it tells us about RH: the obstruction is not hidden in any single prime, character or finite sieve — all of these are
computed and positive. It is a rate problem. The positivity margin E(c) decays to zero as the overlap grows, flips of
larger primes need larger overlaps, and RH is exactly positivity at overlap (log N)^α. A proof must control the shrinking
margin against all primes simultaneously; finite-dimensional arithmetic (sieves, gauges, packets) is fully understood
and cannot supply it on its own.
