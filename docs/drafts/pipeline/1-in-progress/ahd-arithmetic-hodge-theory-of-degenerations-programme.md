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
TheWindowIndexCountsTheJumpMultiples.

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
- Jump multiples: independent family ⇒ `A(H)` posdef and `ind₋(P_K) = #{λ_i < 0, βJ/(−λ_i) < K}`,
  `λ_i` relative eigenvalues of `κW(H)` against `A(H)` [L].

## In progress: Ramanujan windows of every conductor
Claim: for the Ramanujan window `c_m(n) h/√n`, `m ≥ 2`, the energy is
`2π Σ_{q|m} μ(m/q) 𝒜_N(c/q) + O(c/N)`, so at `c^{β+1}/log N → K` the second order is
`J_{β+1}(m) βJ/K ‖H‖²` (tilted: `7 φ(m) J(m)/K ‖H‖²_{−8}`).
Paper proof (δ-route, no shifted-lattice Poisson):
1. Rows: `Σ_m c_m(m) x_m G_{mn} = x_n Σ_{|δ|<a_n} c_m(n+δ) G(δ/a_n) + O(c²N^{−3/2})` (entrywise
   linearization, `|c_m| ≤ σ(m)`).
2. Swap: `Σ_n c_m(n) x_n row_n = Σ_δ Σ_n c_m(n)c_m(n+δ) x_n² G(δ/a_n)`; for each `|δ| ≤ c+1`,
   `n ↦ c_m(n)c_m(n+δ)` is `m`-periodic with mean `c_m(δ)` (roots of unity:
   `m⁻¹Σ_r c_m(r)c_m(r+δ) = Σ_{ξ prim} ξ^δ`), and `x ↦ h(log x)²/x · G(δ/(cx))` is Lipschitz uniformly
   in `δ`; periodic equidistribution, error `O(1/N)` per `δ`, `O(c/N)` total.
3. `Σ_δ c_m(δ)G(δ/a) = Σ_{q|m} qμ(m/q) Σ_j G(qj/a) = a Σ_q μ(m/q)(I² + 2a_φ(a/q))`; `Σμ = 0` removes
   `I²`: energy `2π Σ_q μ(m/q) 𝒜_N(c/q)`.
4. Pole (mean-zero twist) `O(N^{−2})`; remainder uniform; quiet region `|τ| ≤ N e^{−A}/m`:
   `c_m = Σ_q qμ(m/q) 1_{q|n}`, Kuzmin–Landau on each cofactor, twisted Riemann sums below `√N`.
5. Critical curve: `log N 𝒜_N(c/q) → q^{β+1} βJ/K ‖H‖²`, `Σ_q μ(m/q) q^{β+1} = J_{β+1}(m)`.

## Open
Window index vs width (Landau–Widom); bulk second order; uniform bulk
ledger to `N^{1/2−ε}`; count of the second order; integer; `𝔽_q(T)` complete family. See README §9.
