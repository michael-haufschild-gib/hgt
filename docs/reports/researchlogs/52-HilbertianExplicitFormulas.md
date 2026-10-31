# 52 HilbertianExplicitFormulas — facts log

## TheExplicitImageIsTheWeilForm (uses RHTower XiWeilLineConjHilbert)
- Spectral coordinate z = −i(ρ − ½); line reflection z ↦ z̄. Entire function vanishing on ℝ (or iℝ) is 0.
- Calibration rigidity: entire h with h(x) = |F(x)|² on ℝ ⇒ h = F·F# (weilWeight, F#(z) = conj F(z̄)).
- Pair identity: |a|² + |b|² − (ab̄ + bā) = |a − b|²; at pair {z, z̄} same-point sum − explicit sum = |F(z) − F(z̄)|². Correct at one pair ⇒ F(z) = F(z̄); correct at all pairs ⇒ F constant.
- Finite reflection-closed configurations: samePointForm − explicitStatistic = lineReflectionDefect = ½Σm|F(z) − F(z̄)|²; equality (positive weights) ⇔ every pair blind.
- Xi divisor (multiplicity exact): every line-calibrated explicit statistic = xiWeilPolarization(F, F); ‖evaluation vector‖² − explicit = ½‖v − LineConj v‖²; equality ⇔ evaluation vector fixed by line conjugation. Explicit formulas cannot reach past Weil's form.

## TheSamePointQuantumOfAReflectionConfiguration (uses RHTower WindowRelation)
- ReflectionConfiguration: finite divisor closed under s ↦ 1 − s̄ and conjugation with invariant multiplicities. Collision charge O = Σ m_ρ(H_ρ − m_ρ), H_ρ = multiplicity on horizontal line through ρ.
- O = 0 on critical configurations; off-line point ⇒ O ≥ 2 (point and its reflection see each other); TFAE: critical, O = 0, O < 2. O even (swap involution on ordered pairs). Census: offLineMass ≤ O, total ≤ lineMass + O; O ≤ cN ⇒ (1 − c)N ≤ N₀.

## HolomorphicClocksCarryNoQuantum (uses RHTower XiHolomorphicTwoPrimePencilGrowthDichotomy, GaussHodgeVerticalExtraction)
- Cesàro mean square of pencil Σ m_i c_i^n: clocks |c| ≤ 1 ⇒ bounded; bounded ⇒ |P(n)|² ≤ C(n+1); one clock of modulus > 1 (positive multiplicities) ⇒ unbounded (dominant fibre).
- Holomorphic clock e^{λ(s−½)}, modulus exp(Re λ(Re s − ½) − Im λ Im s). On reflection configurations: bounded ⇔ Re λ(Re ρ − ½) = 0 and Im λ·Im ρ = 0 ∀ρ (four-fold symmetry gives every sign). Real λ ≠ 0: bounded ⇔ O < 2 (excess 0 or ∞, never the finite quantum). Non-real λ grows on any configuration with a non-real point.
- Ordinate clock e^{2it Im s} = holomorphic clock at s × at its reflection (same-point quantity), unimodular. Cesàro mean square → Σm² + O + A_t (aliasing A_t ≥ 0, = 0 at non-resonant t); non-resonant excess → O. The quantum lives on the same-point side.

## TheResolventHilbertianExplicitFormula
- Pair identity |s − ρ*|² − |s − ρ|² = (2σ − 1)(2β − 1), ρ* = 1 − ρ̄; (β−½)/|s−ρ|² + (β*−½)/|s−ρ*|² = 4(σ−½)(β−½)²/(|s−ρ|²|s−ρ*|²).
- On every reflection configuration (s ∉ support): (σ − ½)S(s) = E(s) + D(s), S = Σm/|s−ρ|² (same-point), E = Σm Re 1/(s−ρ) (explicit), D = Σm·2(σ−½)(β−½)²/(|s−ρ|²|s−ρ*|²) ≥ 0 for σ > ½; D = 0 ⇔ critical. E ≤ (σ−½)S; if all Re ρ ≤ ½ + w then (σ − ½ − w)S ≤ E (sandwich); E = (σ−½)S ⇔ critical.
- Vertical integral: ∫dt/((a²+t²)(b²+t²)) = π/(ab(a+b)); ∫D(σ+it)dt = πΣm d²/(u² − d²) (u = σ−½, d = β−½, |d| < u) = π Σ_{k≥1} M_{2k}u^{−2k}, M_{2k} = Σm d^{2k} (even depth moments).

## TheXiResolventDepthIdentity (uses ArithmeticElectrostatics TheExternalFieldIsAPrimeSum; RHTower XiLogDerivRePositiveRightOfStrip)
- On the multiplicity-exact Xi divisor, Re s > 1: same-point resolvent Σ1/|s−ρ|² summable (dominated by real reciprocal field); depth series summable. (σ−½)S(s) − Re(ξ'/ξ)(s) = D(s) ≥ 0.
- Opened: D(s) = (σ−½)S(s) − Re(Γ-factor log-derivative)(s) + Σ Λ(n)n^{−σ}cos(t log n).

## TheResolventDepthHasAThetaPrimeExpression (uses ConjugateDiagonalGeometry FiniteThetaReadingsRecoverCompactCurrents; RHTower CCM CCMZetaWeilSmoothIdentity, VonMangoldtLineSeriesSwap)
- Smooth positive kernel 1/(|4 − z|² + cutoff(z − 4)) equals |4 − z|^{−2} on Re z ≤ 1 (whole zero strip); summable over Xi divisor; zeta source trace = S(4).
- Finite integer theta-prefix readings with compact cutoff R converge (n → ∞) to compact traces; R → ∞ gives S(4). xiResolventThetaSamePoint (double limit of finite theta readings) = S(4).
- D(4) = (7/2)·thetaSamePoint − Re(Γ-factor log-derivative)(4) + Σ Λ(n)n^{−4}; same for (7/2)S(4) − Re(ξ'/ξ)(4). Full depth at s = 4 as an explicit theta–prime expression.

## TheFiniteFieldCalibration (uses ArithmeticCastelnuovoSeveri TheFrobeniusSpanDefectCountsTheOuterEigenvalues)
- Line reflection in z is circle reflection in w = e^{iz}. Holomorphic weight on ℂ* equal to |f|² on unit circle ⇒ h(w) = f(w)·conj f(1/w̄) (Rosati weight); unitary-calibrated explicit sums on curve data = Rosati pairing Σ f(β_i) conj f(β_{refl i}).
- Curve ordinate β/|β| preserved by circle reflection; off-circle eigenvalue ≠ its reflection. Curve collision charge: 0 on unitary data, ≥ 2 otherwise, even; TFAE unitary/O = 0/O < 2.
- Lefschetz pencil (power sums Σβ_i^n) Cesàro-bounded ⇔ unitary ⇔ O < 2. Golden datum (q = 5, β = φ, φ^{−1}) has collision charge exactly 2.

## SamePointPositivityIsEffectivity
- Signed finite divisor: Σ m_ρ|P(ρ)|² ≥ 0 for all polynomial tests P ⇔ all m_ρ ≥ 0 (Lagrange isolating polynomial reads one multiplicity). Any pole (negative multiplicity) ⇒ some polynomial test negative. Hilbertian side exists exactly for effective divisors (excludes twins like ζ(2s)/ζ(s)).
