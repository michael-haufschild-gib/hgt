# Arithmetic Lorentzian Geometry (programme card)

- **ID:** ALG
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/fable2.md §4
- **Statement:** Develop the combinatorial Hodge theory of the affine monoid of ℤ: positivity of Weil's form by closure.

## Goal
Folder `formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/`, umbrella
`ArithmeticLorentzianGeometry.lean`, README = foundational doc. Answer Q1–Q5 of fable2 §4, build
the tools listed there, record no-go survivors.

## Status
All modules compile cleanly (`lake --old env lean`), are wired into the umbrella, and their main
theorems depend on standard axioms only. Co-editor modules: PolarGluingAndDispersion,
TheHalfDefectIsTheOptimalHodgeRepair; the README's extended scope is theirs — keep their text.

- Calculus and theorems: LorentzianFormsAtDegreeTwo, TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity,
  TheHodgeIndexTricklesDown, TheMetzlerDichotomy, LorentzianPolynomialsAndTheTuranLayer.
- Gauge and sign: TheSignIsAGaugeFixing, TheSuccessorConnectionIsTheArchimedeanGaugeField,
  LocalFactorsAndTheEulerProductClosure, FrobeniusIsConformalHeckeIsABoost.
- 𝔽_q calibration: TheFrobeniusLadderIsMetzler; TheTrickleDownInequalityIsTheSquareRootCount (TD_π on
  all ladders ⇔ square-root count; hyperelliptic curves trickle down via Stepanov);
  TheLocalFactorTricklesDownByRamanujan (depth 2g−1 decides; genus one: depth one ⇔ |a| ≤ 2√q,
  depth zero never decides; Kloosterman factor trickles down by Weil's bound).
- Atomic family of ζ: TheAtomicFormIsMetzlerBelowTheSpacing; TheOverlapFrustratesTheMetzlerGauge;
  TheMetzlerThresholdOfTheOverlapRatioIsOne (overlap law; threshold exactly K = 1);
  TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing (tilted margin μ_m ≥ 1 + (m/8N) log m pays the pole:
  signed Weil positivity, Hodge index, TD_π, links at K ≤ c★, uniformly in N; twist-blind);
  TheUniformMarginPaysThePoleOnlyUpToARootLogarithm (uniform margins fail at fixed K);
  TheTiltedMarginPaysThePolarDispersion (Gram = tilted model + NSD residual; dispersion ≤ reserves);
  TheAtomicMetzlerPropertyIsSelective; HyperbolicityIsBlindTheSignIsNot (every sign twin hyperbolic
  at K ≤ c★; Liouville twin hyperbolic, not Metzler); TheTowerDeficitIsARowSum.
- Lorentzian polynomials (closure toolkit): TheHessianOfALorentzianPolynomialTricklesDown (∂_i f
  Lorentzian; ∇²f(x) hyperbolic for x ≥ 0 by weighted TD, Euler = link condition);
  TheMixedHessiansOfALorentzianPolynomialAreHyperbolic (all mixed quadratic derivatives along
  nonneg directions hyperbolic; Alexandrov–Fenchel; Khovanskii–Teissier);
  TheLorentzianClassIsClosedUnderNonnegativeSubstitution (mixed class: Lorentzian ⇒ mixed; closed
  under ∂_v, v ≥ 0, and p ↦ p(Ay), A ≥ 0; Hessian at x ≥ 0 hyperbolic; d p ∂_v²p ≤ (d−1)(∂_v p)²);
  TheEulerProductOfLorentzianLocalFactorsIsLorentzian (disjoint-variable products Lorentzian,
  renaming, ∏ f_p and (∏ f_p)∘A mixed-Lorentzian; Euler Hessian Lorentzian at all y ≥ 0).
- TheClosureProducesExactlyTheLorentzianForms (Q1: Hessians of the closure at x ≥ 0 = Lorentzian
  forms exactly). TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine (topic 8: d J J'' ≤ (d−1)J'²
  on s ≥ 0 for every Jensen polynomial of ξ; RH = same on s < 0). TheOverlapRatioIsTheCoveredMeasure
  (exhaustion: atomic tests of ratio K live on measure ≤ K; exhaustive families need K ≳ log N).
- TheStabilityRegimeEndsAtTheRobinEulerThreshold (via RAPT finite part 2θ′(0)+log(1/(wN))+κ_L+γ,
  attained by the pole vector): beyond exp(2θ′(0)+κ_L+γ) the atom block −M has a positive square
  (pole vector); no π > 0 with (−M)π ≤ 0. Window = TD regime proper; constants cannot close it.
- AnIsometricLadderCarriesNoPositiveSquare (Q4): decaying Metzler Toeplitz ladders are hyperbolic at
  all depths iff NSD at all depths. Survivor: the positive square needs growing couplings; the
  fixed-width prime pairing along p-ladders grows like w p^{k/2} (PNT main term = pole weight).
  Conformal ladders G_ij = λ^{min} a_|i−j| ≅ Toeplitz(λ^{−k/2} a_k): same dichotomy; Frobenius
  escapes since normalized couplings grow like q^{k/2}.
- ThePoleDefectControlsTheVRow (multiplicative Hardy: (Σ√n x_n)² ≤ C_H N²/log N (D_N + |x|²)),
  ThePoleDefectPaysThePole: eventually in N, Weil positivity / Hodge index of the atomic Gram at
  K★(φ,ε) = min(overlap bounds, 1/(A+2c_P√e), e^{2θ′(0)+κ_L+γ−ε−2}) ∈ [1e-4, 6e-4] for κ_L ≥ −2,
  ε ≤ 1/8 (vs c★ ≈ 1e-11).
  Mechanism: pole defect pays the pole (no tilt). Gap to Robin–Euler threshold = Chebyshev A.
- WeilsFormIsPositiveOnEveryTestNearTheLogarithms: window tests Σ G_n(· − log n), arbitrary C²
  profiles in [0, w]; orthogonality, prime sum = Weil kernel × window Gram ≤ P_N(y), y_n = ‖G_n‖;
  Lévy diag with pair windows; self-energy ≥ (log(1/w) + 2c_∞ − O(w))‖G‖²; eventually in N, Weil
  form ≥ 0 on every C² test supported in ⋃[log n, log n + w], w ≤ K★_∞(ε) δ_N (κ_L → 2c_∞).
- TheSupportOfAMixedLorentzianPolynomialIsMConvex: exchange in Lorentzian forms (Q_ai, Q_jk > 0 ⇒
  Q_aj or Q_ak > 0); mixed-Lorentzian supports are M-convex (induction: common variable → ∂_k;
  coprime → ∂_{e_a+e_k} then common-variable exchange); mixed = coefficient class; products,
  substitutions, derivatives, Euler product ∘ scale map Lorentzian in coefficient form.
- RHIsReflectionPositivityOfTheCayleyLadder (topic 10 / Q4): Cayley ladder (ℓ(|i−j|)),
  ℓ(n) = Re Σ m(2 − w^n − w^{−n}); reflection formula Q[c] = −2 Re Σ m p_c(w)p_c(w⁻¹) on Σc = 0;
  shift = multiplication by w (reflected pairing invariant, evaluation conformal |w|²). ζ: RH ⇔
  ladders NSD on primitive ⇔ ladders entrywise ≥ 0 (via corpus Li criterion); under RH Lorentzian;
  2λ_n never → 0 (ladder dichotomy + subexp Li). 𝔽_q: ℓ(n) = 2(2g − Σβ^n), sign = sharp Weil bound,
  reflection positivity ⇔ unitary; golden fails.
- APeriodicSuccessorHolonomyIsFlat: nonvanishing completely multiplicative f with periodic successor
  ratio ≡ 1; torus: periodic succConn ⇔ Euler point; periodic CM f ≠ 1 vanishes somewhere
  (Dirichlet characters leave the torus). Plus IsLorentzianPoly.quadDeriv_minor (2×2 minors ≤ 0).
- Topic 9 answered: RamanujanAndLorentzianMeetOnlyAtTheWeilBound (Lorentzian ⇒ a_1 ≥ d√q,
  Ramanujan ⇒ a_1 ≤ d√q; equality only for (1+√qT)^d; never at a prime; elliptic: Lorentzian ⇔
  a² ≥ 4p).

## Open
- Window c★ < K < 1: TD_π for the Metzler Gram; the Markov form loses positivity along the pole
  vector n^{−1/2} (top of P_N, RAPT), paid by the pole term only in the Euler gauge; needed: a gap on
  its complement (cf. card selective-positivity-on-separated-atoms, gate C4).
- K > 1: primitive gap, or a non-atomic Metzler basis.
- Conformal correspondence with λ ≠ 1.
- Adapted (local-spacing) atomic families: widths c·log(1+1/n) cover fraction c of [0, log(N+1)];
  ratio 1 is their Nyquist rate; adapted Gram Metzler for c < 1 (Lean). Hodge index / TD_π at
  c < 1 open.
- Topic 10, dynamical part: a reflection-positive functional built from the source (prime +
  archimedean data) whose Cayley ladder is the Li ladder; candidate: KMS states of the Toeplitz
  algebra of ℕ ⋊ ℕ^× (Laca–Raeburn window 1 ≤ β ≤ 2 ↔ critical strip of ζ(β−1)), reflection β ↦ 3 − β.

## Findings so far
- Degree 2: Lorentzian = Hodge index (no gain); nef shift makes any finite Gram nonneg (trap).
- Gauge: ε(n/m)P(m,n) = ε(n) conj ε(m) P(m,n) ⇒ every twin's prime kernel is gauge-equivalent to
  Euler's; sign hypothesis needs a second, gauge-rigid kernel (archimedean).
- OQ2 as stated is false: n^{iτ} is a non-periodic torus point with prime form unitarily equivalent
  to Euler's; correct locus modulo archimedean characters.
- Beurling systems: nonneg coefficients + Euler product, can violate RH ⇒ multiplicative-only closure blind.
- Canonical atomic intersection form has negative diagonal ⇒ not a Hessian of a nonneg polynomial;
  only domination available.

- Metzler Hodge index (Lean): connected Metzler Q, D=Q1>0: hyperbolic ⇔ Q[v] ≤ Σ(Qv)_i²/D_i ⇔ hyperbolic links;
  diagonal unrestricted. Converts one-positive-square (not sum-closed) into NSD of Q − QD⁻¹Q (sum-closed).
  Euler-point intersection Gram is Metzler in canonical coords (P+J ≥ 0, pole row ≥ 0); twins are not in any gauge.
