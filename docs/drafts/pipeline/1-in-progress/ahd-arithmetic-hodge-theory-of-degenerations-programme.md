# Arithmetic Hodge Theory of Degenerations (AHD) — programme card

- **ID:** AHD
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7
- **Statement:** RH as a structure theorem for the degeneration of the scaling surface along the
  resolution axis; positivity carried through the critical curve by a count, an inherited
  polarization or an integer with a structural bound; one global gluing; calibrations.

## Goal
Develop the field of §2.7: answer its questions by Lean theorems, build its tools. Folder
`formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/`, umbrella
`ArithmeticHodgeTheoryOfDegenerations.lean`, README there.

## Lean modules
TheHorizonTermOfAConductor, TheZeroLedgerOfTheBulk, TheHorizonLayerReadsWeilSummands,
TheCriticalMultiple, TheLedgerOfAWindowOfZeros, TheJordanLimitCountsProjectiveSpace,
TheHorizonBlockIsQuietBelowTheGrid, TheAliasingTailOfAHorizonBlock,
TheHorizonBlockOnTheArithmeticSide, TheHorizonLayerBecomesWeilsForm, TheHorizonCriterion,
TheCriticalMultipleOfAWindow, TheAliasingIsCoercive, TheEnergyOfAHorizonBlock,
TheHorizonBlockBelowTheGridIsSharp, TheSecondOrderTermOfAHorizonBlock,
TheAliasingIsTheDilationDerivativeOfTheBulk, TheAliasingConstantOfTheTiltedSpline,
ThePrimesOfAHorizonWindow, TheBulkDeterminesTheSecondOrderTerm, TheWindowIndex,
TheCountLawOverEveryFiniteRing, TheTwistedHorizonLayerIsZeroBlind, TheWindowIndexCountsTheRightZeros,
TheTwistedHorizonLayerIsPositive, TheAlternatingWindowCountsTheConductorTwoPoints,
ThePrimeWindowCountsTheProjectivePoints, TheHorizonLayerIsGradedByConductor,
TheWindowIndexCountsTheJumpMultiples, TheEnergyOfAPeriodicTwist,
TheRamanujanWindowCountsEveryConductor, TheSecondOrderTermIsDiagonalInTheRamanujanBasis,
TheHorizonLayerIsGradedByEveryConductor, TheWindowIndexResolvesTheZerosOfItsLength,
TheSecondOrderTermOfAPeriodicTwist, TheTwistedDirectionsCarryNoNegativeSquares,
TheTwistedSectorInheritsThePolarization, TheEnergyOfATwistIsItsSpectrum,
TheSecondOrderTermOfEveryPeriodicTwist, TheBulkIsBlindToTheLowZeros,
TheBulkAtThePoleReadsTheArchimedeanGenus, TheBulkIsBlindBelowTheResolutionHeight,
TheFrobeniusAnglesDiagonalizeTheCurveFamily, TheShortWindowsInheritThePolarization,
TheSecondOrderTermIsTheDirichletSeriesOfTheSpectrum,
TheRescaledLimitOfACurveIsTheHurwitzFormOfItsAngles, TheSpectrumOfARamanujanSumIsTheUnitGroup,
DegenerationSelectsThePureCurves, TheGoldenFakeIsSelfSimilarUnderDilation,
TheCoshHyperplaneInheritsThePolarization, TheCountPaysTheSecondOrderBelowAUniformMultiple,
TheSecondOrderOfACharacterWindowReadsAnLValue, TheCharacterWindowsAreGradedByParity,
TheFrequencyOfATwistActsAsAFrobeniusAngle, EveryPeriodicTwistedSectorInheritsThePolarization,
TheFrequencyTwistIsQuietBelowItsResonance, TheEnergyOfAFrequencyTwist, EveryFrequencyActsAsAFrobeniusAngle,
TheHorizonLayerIsGradedByFrequency, EveryFrequencySectorInheritsThePolarization,
TheMonodromyRateOfACurveIsItsZeroWidth.

## Status
- First order = count: `J(m) = J(1) #ℙ⁷(ℤ/m)`; count law over every finite ring (𝔽_q[T] calibration) [L].
- Zero ledgers: bulk (pole only, positive), horizon (Weil summands), twisted horizon (none), window exhaustion [L].
- Horizon theorem: past the critical curve `c⁻¹⟨Wx,x⟩ → κ Q(H)`; RH ⇔ horizon blocks
  nonnegative past the critical curve [L].
- Second order exact: `c⁻¹⟨Wx,x⟩ = κQ(H) − log N·N⁻¹Σ h_n² E₁'(cn/N) + o(1)`; aliasing density
  `= −(∫φ²/2)E₁'`; tilted spline at `c⁸/log N → K`: `→ κQ(H) + (7J(1)/K)∫e^{−8y}H²`; exact
  critical multiple `7J(1)‖H‖²_{−8}/(κ|Q|)` [L].
- General: `s^βE₁(s) → J` ⇒ at `c^{β+1}/log N → K`: `→ κQ(H) + (βJ/K)‖H‖²_{−(β+1)}` [L].
- Primes of a window: departing jumps pay their creation; Markov form at level `⌊e^A⌋` [L].
- Window index: horizon Gram → pencil `κQ + (βJ/K)⟨,⟩`; ind₋(pencil) ≤ eventual ind₋(G_N) [L].
- Window index law: `P_K = κW(H) + (βJ/K)A(H)`, `A ⪰ 0`; monotone in K; = ind₋W(H) for large K;
  some family has index ≥ n iff ≥ n right zeros (cubic-spline translates moved into a window);
  RH iff the window index vanishes; windows of length A: index ≤ 1 + 2A T(A/2)/π (Shannon) [L].
- Twisted horizon windows (mean-zero periodic twist) see no zero: twisted Riemann sums `O(1/N)` [L].
- Twisted horizon windows are positive at every resolution: `c⁻¹⟨Wx,x⟩/∫g² ≥ −C₀(L+B)²/N²`
  (symbol ≥ 0 beyond the archimedean horizon; low frequencies and pole values `O(1/N)`); coercive:
  at the critical curve eventually `≥ a/K − ε` (tilted spline; MVT from below, `Σx² → μ_χ∫h²`) [L].

- Conductor-two window `(−1)^n h/√n`: `c⁻¹⟨Wx,x⟩ − (log N/∫φ²)(𝒜(c/2) − 𝒜(c)) → 0`; at the critical
  curve `→ (2^{β+1}−1)βJ/K‖H‖²`, tilted spline `7J(2)/K‖H‖²_{−8}`, `J(2) = 255 J(1)` [L].

- Prime conductor window c_p = p·1_{p|n} − 1: second order `(p^{β+1}−1)βJ/K‖H‖²`, tilted
  `7(p−1)J(p)/K‖H‖²_{−8}`, `(p−1)J(p) = J(1)φ(p)#ℙ⁷(𝔽_p)`, every prime [L].
- Divisor twists `d·1_{d|n} − 1`: second order `(7/K)Σ_{e|d,e>1} φ(e)J(e)‖H‖²_{−8}` [L].
- Conductor grading: untwisted `x` and prime `y` windows orthogonal at second order
  (`c⁻¹(Q(x+y) − Q(x−y))/∫g² → 0`); `x + y → κQ(H) + βJ/K‖H‖² + (p^{β+1}−1)βJ/K‖G‖²` [L].
- Periodic twists: `E_N = (2π/c) Σ_n y_n² Σ_{|δ|≤⌈c⌉} C_χ(δ) G(δ/a_n) + O(c/N)` [L].
- Ramanujan windows, every `m ≥ 2`: autocorrelation of `c_m` is `c_m`; energy
  `2π Σ_{de=m} μ(d) 𝒜_N(c/e)`; second order `J_{β+1}(m)βJ/K‖H‖²`, tilted `7φ(m)J(m)/K` [L].
- Parseval for the count: Ramanujan expansion `Σ a_m c_m` → `(Σ a_m² J_{β+1}(m))βJ/K‖H‖²`;
  distinct conductors orthogonal at every offset [L].
- Conductor decomposition: untwisted ⊥ every mean-zero quiet twist; `h/√n + Σa_m c_m g/√n` →
  `κQ(H) + βJ/K‖H‖² + (Σa_m²J_{β+1}(m))βJ/K‖G‖²` [L].
- Window length: windows of length `2a` have window index ≥ #right zeros resolved at level `a`
  (finite-level inertia of ζ), ≤ Shannon number [L].
- Periodic twists: quiet region for every mean-zero periodic twist (KL on residue classes);
  even autocorrelation `Σ b_m c_m` ⇒ second order `(Σ b_m J_{β+1}(m))βJ/K‖H‖²`; Legendre symbol:
  `(p^{β+1}−1)/p` [L].
- Mixed families: Gram → `fromBlocks P_K 0 0 (ΛA(G))`; index = ind₋(P_K): twisted windows add no
  negative squares [L].
- Every mean-zero periodic twist: energy = spectrum (DFT of `C_χ`, Poisson on `ℤ + k/M`); second
  order `(βA_φ/(K∫φ²)) Σ_k |χ̂(k)|² (ζ(β+1,k/M) + ζ(β+1,1−k/M)) ‖H‖²`, `≥ 2M⁻¹Σχ²` factor [L];
  counting form `2M^{β+1} Σ_j |χ̂(j)|² j^{−(β+1)}` [L]; for `c_m` spectrum = units, sum
  `2ζ(s)J_s(m)`, agreeing with the energy law [L]; `Re(cψ)`, `ψ` primitive mod `q`: spectral sum
  `|c|²ζ(s)J_s(q)/q + q^{s−2}Re(c²ψ̄(−1)τ(ψ)²L(s,ψ̄²))`, on `|c| = 1` exactly
  `ζJ_s(q)/q ± q^{s−1}‖L(s,ψ̄²)‖` [L]; two characters: opposite parity orthogonal, equal parity
  coupled by `L(s,ψ̄₁ψ₂)`, `L(s,ψ̄₁ψ̄₂)` [L]; `cos(2πan/M)`: `½(ζ(s,u)+ζ(s,1−u))`, `u = a/M`, the
  Hurwitz form of a Frobenius angle [L]; every real frequency `α` (`2α ∉ ℤ`): same form at `u = {α}`
  (bounded-primitive sharp form, Kuzmin–Landau with rotation, discrepancy energy law) [L];
  trigonometric twists: `Σ a_k²` times the Hurwitz forms, graded by frequency [L].
- Uniform bulk ledger: pole-free packets receive `o(c/log N)` from all zeros of height `≤ N^θ`,
  `θ < 2/3` (second-order EM at zeros + zero count) [L]; with the pole the low zeros give exactly
  `κ y_1² (2 + γ − log 4π)` (archimedean genus) [L]; both up to every height `N^θ`, `θ < 1`
  (Euler–Maclaurin of order `m ≥ 1/(1−θ)`) [L].
- Curves: lattice tests of a pure curve, any atom width: `W = w² Σ_i S_{θ_i}(w/log q)|Σ x_k β_i^k|²`
  (Frobenius angles = twist frequencies); positive at every resolution [L]; rescaled limit under
  dilation = Hurwitz form of the fractional angles [L]; selection: pure without eigenvalue `1` ⇒
  `W → 0` on every lattice test; golden fake ⇒ `W(g_w) ≥ c w e^{εw}` (exponential monodromy) [L];
  one orbit `β, β⁻¹` (elliptic, golden): lattice Gram at every width `= E(w)/2 · spanGram` [L];
  exponential rate of every curve = zero width `δ = log max|β|/log q`: `|W| ≤ (2ℓ + L)N e^{δℓ}‖f‖²`
  on tests of length `ℓ`, attained up to `e^{−εℓ}` in both signs (Turán) [L].
- Inheritance on short windows: independent untwisted horizon families of length `≤ 3/5` are
  eventually positive definite (CWS window positivity + pencil) [L]; up to `log 2 + 1/50` on the
  cosh hyperplane (CWS coercivity), so the window index is `≤ 1` there [L]; every length `A` below
  the uniform multiple `K₀(A) = βJ/(κ(10 + 72e^{A/2}))` (ACS Weil floor) [L].
- Inheritance on the twisted sector: independent Ramanujan-twisted families are eventually positive
  definite along the critical curve (mechanism B, unconditional there) [L]; for every nonzero
  mean-zero periodic twist (spectral constant) [L]; every twist with a positive scalar second order,
  in particular trigonometric twists with distinct frequencies [L].
- Jump multiples: independent family ⇒ `A(H)` posdef and `ind₋(P_K) = #{λ_i < 0, βJ/(−λ_i) < K}`,
  `λ_i` relative eigenvalues of `κW(H)` against `A(H)` [L].

## Open
Gap between resolved zeros and Shannon number; bulk ledger at the resolution height `N/c`; count
of the second order; integer; `𝔽_q(T)` complete family. See README §9.
