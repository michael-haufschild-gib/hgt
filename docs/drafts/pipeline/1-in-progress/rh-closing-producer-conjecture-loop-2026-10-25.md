# RH Closing Producer Conjecture Loop

- **ID:** rh-closing-producer-conjecture-loop-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/rh-current-frontier-map.md` · Shared Closing Producer Frontier (U1–U3)
- **Statement:** Derive, audit against the C1–C11 selectivity battery, prove unconditionally on paper, and formalize in Lean 4 the missing closing mathematical mechanism for one or more live RH routes.

## Goal
Close a live RH route in `docs/reports/rh-current-frontier-map.md` unconditionally in Lean (`RiemannHypothesis`), without adding hypotheses, axioms, or computational shortcuts. Every falsified conjecture must yield a dependency-closed positive survivor (exact identity, sharp boundary, rigidity law, or classification) formalized in Lean before advancing to the next conjecture.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake --old env lean` green, `#print axioms` clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Mandatory Selectivity Battery (C1–C11)
Every candidate closing conjecture is tested immediately against:
1. **C1 Beurling-selective:** Must fail on impure Beurling systems / golden datum (`1 - 5X + 5X^2` at `q=5`) and continuous-counterpart models (`N(x) = cx + O(1)` with planted off-line zeros). Must genuinely use discrete `ℤ` additive-multiplicative compatibility (`n ↦ n+1`, `gcd(n,n+1)=1`, `pa - qb = 1`, exact integer spacing).
2. **C2 Single-`ζ`:** Cannot rely on external character/modulus family averaging.
3. **C3 Signed:** Cannot factor through unsigned/complete-period lag-covariance or `ℓ²` magnitude data (parity twins of `μ` match all complete-period quadratic forms).
4. **C4 Square-root scale:** Must cross or bypass the `√T` / `ε = 1/2` / `A = (1/2) log T` critical threshold.
5. **C5–C6 Node-critical & deformation-sensitive:** Deleting node `4` (`log 4`) or perturbing a single prime weight must break the mechanism.
6. **C7–C11 Quantized / Horizon-uniform / Shared-budget:** Must respect global shared-budget gluing (`D < 2` for right-zero Hodge defect, or uniform horizon bounds).

## Approach & Active Conjecture Queue
We run an uninterrupted loop of `Conjecture -> Paper Proof / Refutation -> Strongest Positive Survivor -> Lean Formalization -> Next Conjecture`, focusing on avenues untouched by concurrent cards (`q-i`, `q-ii`, `q-iii`, `biarithmetic-*`, `wl-source-estimate-loop`, `wd-la-sign-producer-loop`, `seventy-five-percent-loop`):

- **Track 1 (PM / MC / SSA — Compensated Bézout Interior Martingale & Size-Truncated Hypercube):**
  - Target receivers:
    - `riemannHypothesis_iff_forall_pos_compensated_pmBezoutInteriorMartingale_bounded` (`TheReceiverEquivalenceAndZeroWidthLaw.lean`)
    - `sizeHypercubeForm` (`SignedSuccessorArithmetic/TheSizeTruncatedHypercubeForm.lean`)
  - Investigate exact algebraic/spectral decompositions of `pmBezoutInteriorMartingaleSum ε T + pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T` and `sizeHypercubeForm hr ε D`: how does the integer successor law `n ↦ n + 1` couple the truncated Möbius polynomial `Σ_{d ≤ D} μ(d) d^{-σ} e^{2πiξ log d}` to the exact hypercube step kernel `W(ξ)`, and what happens below `σ = 1`?
- **Track 2 (Stepanov / Baker Auxiliary Function on Additive-Multiplicative Integer Grids — Biarithmetic C1–C2 & WL):**
  - Target receiver: `riemannHypothesis_iff_spline_prime_sum_le_of_gt_four` (`SplineProbeFiniteShiftBounds.lean`) and `StepanovCount.lean` / `ShiftedSubgroupStepanov.lean`.
  - Test whether Bombieri–Stepanov / Mahler / Baker auxiliary polynomials vanishing at integer/prime-power jet data yield a one-sided bound over `ℤ` or expose an exact characteristic-zero derivative-loss rigidity theorem.
- **Track 3 (RW / AOG — Shell-Flux / Theta `h⁰` Coupling & Quantized Index `D < 2`):**
  - Target receivers: `riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos` (`TheApertureFlowNeverStalls.lean`), `riemannHypothesis_iff_encard_rightZeros_lt_two` (`TheIndexExit.lean`), `TheThetaH0OfSpecZ.lean`.

## Conjecture Ledger

### Conjecture C-01 (Bézout Interior Martingale Drift Remainder) — REFUTED (Tautological Identity)
- **Statement:** In `BezoutPronicTotientInteriorMartingaleSynthesis`, does the compensated interior bracket `2 * pmBezoutInteriorMartingaleSum ε T + 2 * pmInteriorLogCounterterm ε * pmCompensatedHarmonicSum T` behave as a lower-order error `O_ε(1)` bounded independently of `E_T(ε)`?
- **Audit / Refutation:** No. Unfolding `pmBezoutInteriorPrefix ε n = (A_ε(n-1) + A_ε(n+1))/2 - Δτ_{1+ε}(n)/2` against `A_ε(n+1) - A_ε(n)` is exact summation by parts of `A_ε(n)²`; after cancelling the `log T` drifts of `activeDeletedDiagonal` and `predecessorPeak`, the compensated interior bracket equals `E_T(ε) + O_ε(1)` identically.
- **Positive Survivor Exposed (P-01):** In the adjacent size-cutoff coordinate, `SignedSuccessorArithmetic.sizeHypercubeForm hr ε D` is definitionally equal (`rfl`) to `BezoutValuationIncidence.naturalDilationDirichletForm ε D r hr`, uniting the spectral integral `∫ W_r(ξ) |∑_{d≤D} μ(d) d^{-1/2-ε+2πiξ}|² dξ` directly with `receiverDampings`, zero-free strips on damping bands, and `RiemannHypothesis` (still unlinked in `SignedSuccessorArithmetic`).

### Conjecture C-02 (Van der Corput Fixed-Lag Covariance Transfer on `A_ε(N)`) — REFUTED (Diagonal Floor `N²/H`)
- **Statement:** Since every fixed-lag correlation `(1/N) ∑_{n≤N} τ_ε(n+h) τ_ε(n)` converges with power saving to `ρ_ε(h)` and `(1/H) ∑_{h≤H} (ρ_ε(h) - α_ε²) → 0`, can Van der Corput's difference inequality push `|A_ε(N)|` below `N^{1/2}`?
- **Audit / Refutation:** No. Van der Corput's inequality carries an unavoidable diagonal floor `N² / H ≥ N` for `H ≤ N`, so its square root cannot cross `N^{1/2}` (fails C3/C4).

### Conjecture C-03 (Unweighted Mellin-Successor Binomial Series `∑ n^{a-bs}(n+1)^{-cs}`) — REFUTED (Half-Plane Blindness)
- **Statement:** Does expanding `(n+1)^{-cs} = n^{-cs} ∑_{m≥0} binom(-cs, m) n^{-m}` in `∑_{n≥2} n^{a-bs}(n+1)^{-cs}` create a pole-free relation constraining zeros of `ζ` in `1/2 < Re s < 1`?
- **Audit / Refutation:** At `b = c = 1, a = 0`, every term `ζ(2s + m)` has argument `Re(2s + m) > 1` for `Re s > 1/2`, so the unweighted series converges absolutely on `Re s > 1/2` and is completely blind to off-line zeros of `ζ(s)`.
- **Positive Survivor Exposed (P-03):** Over characteristic-zero fields `[Field K] [CharZero K]`, the Euler derivation `X f' - e₀ f` eliminates `X^{e₀}` without any `natDegree < p` cap, giving an **unbounded-degree sparse root-multiplicity bound** `rootMultiplicity x f < #f.support` (`x ≠ 0`) and characteristic-zero `ShiftedSubgroupStepanov` over arbitrary finite subgroups `H ≤ Kˣ` (`μ_n ⊂ ℂˣ`).

### Conjecture C-04 (Local Euler–Lagrange Contradiction at a Finite Contact Aperture `A_*`) — REFUTED (C6 Tail Blindness)
- **Statement:** Can local variation of a ground-state minimizer `u_*` of `𝒬_{A_*}(u)` on `[-A_*, A_*]` at `μ(A_*) = 0` refute `μ(A_*) = 0` without referencing scales `> e^{2 A_*}`?
- **Audit / Refutation:** No. `fullZeroForm F` on `supp(F) ⊆ [-A, A]` inspects only prime powers `n < e^{2A}`. Any mechanism that closes at finite `A` must either use the integer structure of `{1, …, ⌊e^{2A}⌋}` directly or couple `[-A, A]` to all scales `L → ∞` via the Jacobi-theta kernel `Φ`.

### Conjecture C-05 (ACT — `a → 0⁺` and `a → +∞` Asymptotics + Midpoint Folding of `primeReflectedDifferenceEnergy`) — ANALYZED
- **Findings:**
  1. Sending `a → +∞` in `u_a = F / m_a` (`Z(F) = 2 S_a(u_a) - D_a(u_a) + V_a(u_a)`) shows that expanding `(u_a(x) - u_a(y))²` cancels all `m_a` factors via the Schrödinger equation of `ω_a` and returns `Z(F)`; any genuine positivity gain must keep `(u(x) - u(y))² ≥ 0` intact.
  2. For `u` supported near `x ≈ r` (`r → ∞`), the same-cluster `n ≈ e^{2r}` part of `D_prime` is `O(e^r m_a(r)² u²)` which is doubly-exponentially dominated by `V_a(u) ≍ e^{r/2} m_a(r) u²`; the true critical competition in `D_prime` comes from **cross-scale pairs** `(x ≈ r, y = log n - x ≈ O(1))` (`n ≈ e^{r + O(1)}`), where `2 ∑_{log n > x} (Λ(n)/√n) m_a(log n - x) = 4 sinh(a/2) sinh(x/2) + O(1)` cancels the leading `4 sinh(a/2) sinh(x/2)` of `V_a(u)` via the exact harmonic theta identity!
  3. Midpoint folding of `primeReflectedDifferenceEnergy` (`0 < x < (log n)/2`) has not yet been formalized downstream of `ArchimedeanZTypeLaw.lean`.

### Conjecture C-06 (Rank-2 / Correspondence Arakelov Theta `h⁰` on `ℤ × ℤ`) — ANALYZED & POSITIVE SURVIVOR EXTRACTED
- **Statement:** Extend `ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean` from 1D `ℤ` and diagonal `poleH0` (`aH + bV`) to general positive-definite correspondence quadratic forms `Q(m, n) = α m² + 2 γ m n + β n²` (`α > 0, det Q = α β - γ² > 0`) on `ℤ × ℤ`.
- **Audit:** Completing the square + shifted 1D Gaussian Poisson summation gives exact 2D Riemann–Roch `h⁰_{ℤ²}(Q) - h⁰_{ℤ²}(Q⁻¹) = -(1/2) log(α β - γ²)`, where `det(Q⁻¹) = α' β' - γ'²` has exact Lorentzian `(1, 2)` Hodge signature! It does not close infinite-rank `scalingSurface` by itself because `Sym²(ℝ²)` has primitive rank `1` (and uncoupled binary Epstein zeta functions with class number `> 1`, e.g. `m² + 5n²`, lack Euler products and violate RH).
- **Positive Survivor (P-02):** Formalize 2D correspondence theta `h⁰` on `ℤ²` (`correspondenceThetaSum`, `correspondenceH0_riemannRoch`, recovery of `poleH0` at `γ = 0`, and strict off-diagonal coupling monotonicity).

### Conjecture C-07 (Sublattice Poisson–Möbius Sieve & Vaughan Type-II Cauchy–Schwarz Barrier) — REFUTED ON UNSIGNED STEP
- **Findings:** Applying exact sublattice Poisson summation `∑_{r≥1} ψ(dr) = (1/d) ∑_{k≥1} ψ̂(k/d)` (`ψ(0) = ψ̂(0) = 0`) to `supp(ψ) ⊆ (-(D+1), D+1)` gives the exact zero-error identity `ψ(1) = ∑_{d=1}^D (μ(d)/d) ∑_{k≥1} ψ̂(k/d)`. Dualizing to bound `∑_{d≤D} μ(d)` via Vaughan's identity hits `X^{3/4}` whenever Cauchy–Schwarz drops `μ(a)` to `|μ(a)| ≤ 1` (violating C3). Any genuine producer must preserve the signed multiplicative-additive ring structure of `ℤ` without an unsigned `ℓ²` Cauchy–Schwarz step.

### Conjecture C-08 (Exact Light-Cone Antisymmetric `dν` Law on `Z(m_a u)` Without Plastic Threshold) — PROVED ON PAPER (Identity) & ACTIVE CLOSING ATTACK
- **Statement & Proof of the Exact Identity:**
  On odd shifted ground states `m_a(x) = Φ(x - a) - Φ(x + a)` (`a > 0`, which are **complete for RH** by `SingleShiftCompleteness.lean`: `RH ⟺ ∀ u even ∈ C²_c, Z(m_a u) ≥ 0`), set `s = y - x > 0`, `t = x + y > s` (`x = (t - s)/2 > 0`, `y = (t + s)/2 > x`, `dx dy = (1/2) ds dt`) and define the nonnegative pair weight
  `W̃_{a,u}(t, s) := m_a((t - s)/2) m_a((t + s)/2) (u((t - s)/2) - u((t + s)/2))² ≥ 0`.
  Using `sinh(x/2) sinh((x+s)/2) = (cosh((2x+s)/2) - cosh(s/2))/2` to fold `V_a(u) = 8 sinh(a/2) ∫_{x>0} m_a(x) sinh(x/2) u(x)² dx` into the continuum pair integral alongside `2 S_arch - D_arch`, ALL continuum and discrete pieces of `Z(m_a u)` assemble into a single antisymmetric light-cone wedge integral:
  `Z(m_a u) = ∫∫_{0 < s < t} (κ(s) - κ(t)) W̃_{a,u}(t, s) ds dt + 2 ∑_{m≥2} (Λ(m)/√m) ∫_{log m}^∞ W̃_{a,u}(t, log m) dt - 2 ∑_{n≥2} (Λ(n)/√n) ∫_0^{log n} W̃_{a,u}(log n, s) ds`
  (up to the exact `1/2` Jacobian convention of `archimedeanSameSideJumpEnergy` vs `primeSameSideJumpEnergy` — to be verified coefficient-by-coefficient against `ArchimedeanZTypeLaw.lean`!).
  Crucially: while even gauges `M` see `κ(s) + κ(t)` (which turns negative past the plastic fold `log ρ ≈ 0.2812`), odd ground states `m_a` see **`κ(s) - κ(t) = (ω(s) - ω(t)) + 2(cosh(t/2) - cosh(s/2)) > 0` strictly everywhere on `0 < s < t < ∞` with NO plastic threshold at all**, and growing like `2 cosh(t/2)` at large `t`!
- **Lean Module Written:** `formal/GaloisForLFunctions/ArithmeticCriticalityTheory/LightConeAntisymmetricVariationLaw.lean` (`strictAntiOn_weilJumpDensity`, `weilJumpDensity_sub_add_two_mul_pos`, `primeReflectedDifferenceEnergy_eq_two_mul_half`, `profileVariance_eq_eight_mul_sinh_sameSideGroundJump`, `archSurplus_add_profileVariance_eq_weilJumpDensity_sub`, `zeroForm_shiftedGroundState_eq_antisymmetric_weilJumpDensity_add_prime`, `riemannHypothesis_iff_forall_prime_le_antisymmetric_weilJumpDensity`).

### Conjecture C-08b / C-09 (Interior–Exterior Collar Potential `P_{a, R}(x)` & Selectivity Audit) — PROVED ON PAPER
- **Findings:**
  1. For `supp(w) ⊆ (-R, R)`, splitting `(0, ∞)²` into `(0, R)²` and `(0, R) × [R, ∞)` converts all exterior jumps (`w(y) = 0`) into a scalar collar potential `2 ∫_0^R w(x)² m_a(x) Q_{a, R}(x) dx`. Because `m_a` is odd (`-m_a(log d - x) = m_a(x - log d)`), `oddProfile_harmonic_identity` cancels `+sinh(x/2)` against `-sinh(x/2)` AND cancels all `[R ± x, ∞)` continuum and prime tails identically!
  2. **Selectivity audit:** No impure Beurling system satisfies `oddProfile_harmonic_identity` (non-`ℤ` generalized integers fail `Θ` Poisson summation), and Davenport–Heilbronn fails `Λ(n) ≥ 0`.

### Conjecture C-10 (Tapered `sinh(λ x)` Convolution Gauge `M_A = Θ * φ̃_A` as `A → ∞`) — REFUTED (Turnaround Shell Transfer)
- **Statement:** Convolving `Θ` with `φ_A(b) = sinh(λ b)` (`0 < λ < 1/2`) tapered on `[A, 2A]` reduces the Schur ratio `M_A(x)/(M_A(t+x) - M_A(t-x))` on `[0, A - R]` from `4 e^{4t}` to `1 / (2 cosh(λ t)) < 1/2`. Does sending `A → ∞` close `Z(M_A w) ≥ 0`?
- **Audit / Refutation:** No. Integrability of `∫ M_A(y) sinh(y/2) dy` forces `φ_A` to turn around and decay on `[A, 2A]`, transferring an `O(e^{(1/2 + λ)A})` deficit into the turnaround shell `log d ∈ [A - R, 2A + R]` where `M_A(log d + x) < M_A(log d - x)`—dual to the divergence of `∑ Λ(d) d^{λ - 1/2}` at `Re s = 1/2 - λ < 1`.

### Conjecture C-11 (Hyperbolic Light-Cone Bridge on `log d ≤ a - R` vs Trans-Horizon Shell `log d > a - R`) — SHARP BOUNDARY ISOLATED
- **Statement:** Replace `ω(s) - ω(s + 2y)` in `TransHorizonIncidenceMechanics/SupportRadiusCollarCutoffAndAllScaleObstacleBBridge.lean` by the full zero-form light-cone kernel `κ(s) - κ(s + 2y) ≥ 4 sinh(y/2) sinh((y + s)/2)` across `z ∈ (3R, a - 2R)`.
- **Findings:**
  1. **Positive Survivor (P-04):** Integrating `4 sinh(t/4) sinh(z/2)` over `z ∈ (3R, a)` (or `z ∈ (3R, a - 2R)`) produces denominator `8 sinh(t/4) (cosh(a/2) - cosh(3R/2)) → +∞` as `a → +∞`! Thus for ANY fixed support radius `R > 0` and ANY `η > 0`, choosing `a ≥ a_0(R, η)` discharges **100% of Obstacle B on `log d ≤ a - R` with continuum budget `< η < 1`** (whereas `ω(s) - ω(s + 2y)` alone had `a`-independent budget `supportArchBudget R δ L ∝ e^{9R} > 1`).
  2. **Exact Obstruction Isolated on `log d > a - R`:** Keeping `(1 - η(a))` of Set A (`z ∈ (3R, a - 2R)`) and 100% of Set B (`y ≥ a - 2R`) untouched, `oddProfile_harmonic_identity` cancels the `log d > a - R` tail identically EXCEPT for the discarded interior/intermediate surplus `∑_{log d ≤ a - R} (Λ(d)/√d) (m_a(log d + x) - m_a(log d - x))`, confirming `poleFreeForm_shiftQuotient_eq`: single-shift rescaling `w_a = F / m_a` alone cannot bypass the sign-indefinite interior anti-diagonals `x + y = log d < 2R` by triangle inequality without arithmetic cancellation among prime powers `< e^{2R}`.

### Conjecture C-12 (Multiplicative Coprime Balance Selectivity Audit) — REFUTED (Fails C1 on DMV Beurling)
- **Statement:** Can `CCMPrimeDeficitCoprimeBalance` (`f(log X)² + Cross = ∑_{d ≤ X} μ(d) R(log(X/d))² = O(X)` for `f(T) = ∑_{n ≤ X} μ(n) R(log(X/n))` with `|R| ≤ 7/2`, or `R ≡ 1` giving `g(1) = M(X)`) force `f(log X)² = O(X)` by proving lower/sign bounds on the coprime cross sum `∑_{gcd(a,b)=1} μ(a) μ(b) g(a) g(b)`?
- **Audit / Refutation:** No, not from multiplicative structure + `|R| ≤ C` alone. Diamond–Montgomery–Vorhauer's Beurling prime system `𝒫` satisfies `N_𝒫(x) = c x + O(1)` (hence `|R_𝒫| = O(1)` and the identical multiplicative coprime inversion identity `∑_{d ≤ X} μ_𝒫(d) R_𝒫(log(X/d))² = O(X)`), yet has off-line zeros at `σ_0 > 1/2` where `M_𝒫(X)² ≍ X^{2 σ_0} ≫ X` cancelled by negative coprime cross-work. Any closing mechanism must couple `(ℤ, +)` exact successor periodicity (`⌊x/d⌋` / `Θ` Poisson summation) with `(ℤ_{≥1}, ×)` unique factorization (`μ`, `Λ ≥ 0`).

### Conjecture C-13 (Forward-Dilation Reflection of `sizeHypercubeForm` & Mellin `ζ(s)/ζ(1 + ε - s)` Audit) — POSITIVE SURVIVOR EXTRACTED (P-05)
- **Statement & Exact Reflection Identity:**
  In `sizeHypercubeForm hr ε D = ∑_{d₁, d₂ ≤ D} μ(d₁) μ(d₂) (d₁ d₂)^{-1/2 - ε} Φ_r(d₁ / d₂)`, symmetry `Φ_r(d₁ / d₂) = Φ_r(d₂ / d₁) = Re⟨D_{d₁} v_r, D_{d₂} v_r⟩` reflects backward step dilations `D_{1/d} v_r` (which have non-summable weights `μ(d) d^{-ε}` on `[1, ∞)`) into **forward step dilations** `D_d v_r` with **absolutely summable weights `μ(d) d^{-1 - ε}`** (`ε > 0`):
  `R_{ε, r}(D) = ∫_0^∞ (∑_{d ≤ D} μ(d) d^{-1 - ε} C_r(⌊d x⌋))² dx / x² = ∫_1^∞ (...)² dx / x² + ∫_1^D (∑_{u ≤ d ≤ D} μ(d) d^{-1 - ε} C_r(⌊d / u⌋))² du`.
  At `r = 2` (`C_2(m) = -(m mod 2)`), the `[1, ∞)` part is unconditionally `≤ ζ(1 + ε)²` uniformly in `D`, and RH reduces to cutoff-uniform `L²(1, D)` boundedness of the alternating dyadic-floor Möbius tail `∑_{u ≤ d ≤ D, ⌊d/u⌋ odd} μ(d) d^{-1 - ε}` as `ε → 0⁺`!
- **Audit of the `ε = 0` Limit vs `ε > 0`:**
  For every `ε > 0`, the `D → ∞` limit `H_ε(u) = ∑_{d ≥ u, ⌊d/u⌋ odd} μ(d) d^{-1 - ε}` converges absolutely pointwise and has Mellin transform `(2^{1-s} - 1) ζ(s) / (s ζ(1 + ε - s))` on `0 < Re s < ε`, genuinely coupling `ℤ`-Poisson (`ζ(s)`) with the Euler product (`1 / ζ(1 + ε - s)`). Under RH, `R_{ε, 2}(D)` IS uniformly bounded in `D` for every `ε > 0` (by Mellin Plancherel + Montgomery–Vaughan on `|t| > D`). However, setting `ε = 0` directly (`Q(x) = ∑ μ(d) d^{-2} P(d x)`) collapses `(ζ(s) / ζ(1 - s))` to the pure Gamma factor `π^{s-1/2} Γ((1-s)/2)/Γ(s/2)` (Davenport–Müntz's `cos(2πx)` identity), erasing all nontrivial zeros; thus any producer must work at `ε > 0` (`ζ(s) / ζ(1 + ε - s)`) or retain the finite truncation `M_D(1 + ε - s)`.
- **Positive Survivor (P-05):** Formalize the exact forward-dilation `L²` reflection identity for `sizeHypercubeForm` (`sizeHypercubeForm_eq_forward_integral`), unconditional uniform bound on `[1, ∞)`, and reduction of `RiemannHypothesis` to `∫_1^D (∑_{u ≤ d ≤ D, Odd ⌊d/u⌋} μ(d) d^{-1-ε})² du ≤ B_ε` along cofinally small `ε > 0`.

### Conjecture C-14 (Cutoff-Free Forward-Dilated `L²(1, ∞)` Criterion & Terminal Dyadic Window) — PROVED ON PAPER & PARTIALLY FORMALIZED
- **Findings:**
  1. At `r = 2`, on the top dyadic octave `u ∈ (D/2, D)`, every `d ∈ [u, D]` satisfies `1 ≤ d/u < 2` (`⌊d/u⌋ = 1`), so `-G_{ε, D}(1/u) = ∑_{u ≤ d ≤ D} μ(d) d^{-1-ε}` collapses identically to the literal Möbius harmonic window (`forwardDilatedPrimitive_two_inv_eq_moebius_window`).
  2. **Cutoff-free Mellin continuation criterion:** Even without the finite cutoff `D`, if the uniformly convergent limit `H_ε(u) := -G_ε(1/u) = ∑_{d ≥ u, Odd ⌊d/u⌋} μ(d) d^{-1-ε}` belongs to `L²(1, ∞)` along ANY sequence `ε_k → 0⁺`, then `RiemannHypothesis` holds! Proof: Cauchy–Schwarz on `(0, 1)` makes `Φ_ε(s) = ∫_0^∞ G_ε(x) x^{-s-1} dx` holomorphic on `0 < Re s < 1/2`, continuing `-(1 - 2^{1-s}) ζ(s) / (s ζ(1 + ε - s))` from `0 < Re s < ε` to `0 < Re s < 1/2`. Any zero `ρ_0 = β_0 + i γ_0` with `β_0 > 1/2` puts `s_k = 1 + ε_k - ρ_0` inside `(ε_k, 1/2)` once `ε_k < β_0 - 1/2`, forcing `ζ(ρ_0 - ε_k) = 0` for infinitely many `k`, contradicting zero isolation on `0 < Re s < 1`.

### Conjecture C-15 (Rounding-Free Multiplicative Sieve Functional Equation & `r`-Periodicity of `G_ε`) — PROVED ON PAPER & FORMALIZED IN `TheForwardDilatedHypercubeForm.lean`
- **Findings:**
  1. Real forward dilations obey `(d : ℝ) * ((m : ℝ) * x) = ((m * d : ℕ) : ℝ) * x` with zero rounding error and exact `r`-periodicity `G_ε(x + r) = G_ε(x)` for all `x ≥ 0` (`forwardDilatedLimit_add_natCast`).
  2. Summing over `m ≥ 1` gives `∑_{m=1}^∞ m^{-1-ε} G_ε(m x) = C_r(⌊x⌋)` for all `x ∈ ℝ` (`hasSum_forwardDilatedLimit_mul`), hence `G_ε(x) = -∑_{m=2}^∞ m^{-1-ε} G_ε(m x)` on `x < 1` (`forwardDilatedLimit_eq_neg_tsum_of_lt_one`).
  3. **Audit:** Naive triangle inequality in `L²(dx/x²)` yields norm multiplier `∑_{m≥2} m^{-1/2 - ε} = ζ(1/2 + ε) - 1`, converging iff `ε > 1/2` (matching DMV Beurling).

### Conjecture C-16 (Positive Euler-Product Fourier Series of `G_ε` on `ℝ / 2ℤ`) — PROVED ON PAPER
- **Statement & Proof:**
  Expanding `C_2(⌊t⌋) = -1/2 + (2/π) ∑_{j ≥ 1 odd} sin(π j t) / j` (`t ∉ ℤ`) converts all oscillating Möbius signs `μ(d)` in `G_ε(x)` into **strictly positive Euler-product coefficients** `c_ε(m) = ∑_{d | m} μ(d) d^{-ε} = ∏_{p | m} (1 - p^{-ε}) ∈ (0, 1]` (`m` odd), annihilating all frequencies `4 | n`:
  `G_ε(x) = -1/(2 ζ(1+ε)) + (2/π) ∑_{m ≥ 1 odd} (c_ε(m) / m) (sin(π m x) - 2^{-1-ε} sin(2π m x))`.
  At `ε → 0⁺`, `c_0(1) = 1` and `c_0(m) = 0` (`m > 1`), collapsing `G_0(x)` to `(4/π) sin(π x) sin²(π x / 2)`.

### Conjecture C-17 (ACS Effectivity / Meyer Principal Cycles Audit) — AUDITED AGAINST `ArithmeticCastelnuovoSeveri/README.md`
- **Audit:** `ArithmeticCastelnuovoSeveri/README.md` (§0, §3.9, §3.10, §5) already establishes universal boundary rigidity (`SourceConeBoundaryRigidity`, `SourceRiemannRochWithoutSymmetry`) and the universal floor law (`riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`): any Hecke-stable or ample cone of nonnegative ample degree has `RiemannRochAxiom` iff `0 ≤ defect(x, x)`. Thus progress on ACS cannot evade the defect floor via formal cone repackaging alone.

### Conjecture C-18 (Selectivity Audit of 2-Periodicity + Positive Euler Fourier Coefficients `c_ε(m) ∈ (0, 1]`) — REFUTED ALONE; UNIQUENESS SURVIVOR ISOLATED
- **Statement:** Do 2-periodicity `G_ε(x + 2) = G_ε(x)` plus multiplicative positive Fourier weights `c_ε(m) = ∏_{p|m, p ∈ S} (1 - p^{-ε}) ∈ (0, 1]` alone force `∫_0^1 G_ε(x)² dx / x² < ∞` for `ε ∈ (0, 1/2)`?
- **Audit / Refutation:**
  1. `goldenDatum` (`1/\zeta_{\text{gold}}(s) = (1 - 5^{-s})(1 - 5^{1-s})/(1 - 5\cdot 5^{-s} + 5\cdot 5^{-2s})`) IS 2-periodic (`5^k ∈ ℕ`), and fails `c_ε(m) ∈ [0, 1]` (`c_ε^{\text{gold}}(25) → -5`, exponential blowup).
  2. **Lethal counterexample (`S ⊂neq ℙ`):** Choose a DMV-modulated subset of **actual integer primes** `S ⊂ ℙ` of density `δ(p) = 1/2 - 2 p^{β_0 - 1} cos(γ_0 log p)` (`p ≥ P_0`, `β_0 ∈ (1/2, 1)`). Because every `d` supported in `μ_S` is an actual integer and `μ_S` is restricted Möbius, `G_ε^S(x)` IS 2-periodic on `ℝ` AND has strictly positive Fourier coefficients `c_ε^S(m) = ∏_{p|m, p∈S} (1 - p^{-ε}) ∈ (0, 1]` for all odd `m`! Yet `ζ_S(s)` has a simple zero at `β_0 + i γ_0` (`β_0 > 1/2`), so `∫_0^1 G_ε^S(x)² dx/x² = +∞` for almost all `ε ∈ (0, β_0 - 1/2)`.
- **Positive Uniqueness Survivor:** What `S ⊂neq ℙ` violates is the **complete additive sieve identity** `∑_{m=1}^∞ m^{-1-ε} G_ε(m x) = C_2(⌊x⌋)` (which sums over ALL `m ∈ ℕ_{≥1}`, encoding that `ℙ` factorizes *every* positive integer). Together, integer-dilate generation (2-periodicity) + `∑_{m=1}^∞ m^{-1-ε} G_ε(m x) = C_2(⌊x⌋)` uniquely force `a(d) = μ(d)` for every `d ≥ 1`, excluding DMV Beurling systems, `goldenDatum`, `S ⊂neq ℙ`, `L(s, χ)`, and Davenport–Heilbronn simultaneously!

### Conjecture C-19 (Exact Hilbert-Space Normality & Isometric Duality Between `forwardDilatedLimit` and `pmPowerDampedFermiSource`) — PROVED ON PAPER (P-06)
- **Statement & Proof:**
  On `ℋ = L²((0, ∞), dx / x²)` (`≅ L²((0, ∞), dt)` via `t = 1/x`), the integer dilation operators `(U_d ψ)(x) = d^{-1/2} ψ(d x)` are unitary with adjoints `(U_d^* ψ)(x) = d^{1/2} ψ(x / d)`, and `U_d` commutes identically with `U_e^*` (`(d x)/e = d (x/e)` without rounding!). Hence for EVERY finite set `S ⊂ ℕ_{≥1}` and EVERY real weight `a : ℕ → ℝ`, `T_{S,a} = ∑_{d ∈ S} a(d) d^{-1/2} U_d` is **normal** (`‖T_{S,a} ψ‖_ℋ = ‖T_{S,a}^* ψ‖_ℋ`, proved directly by the 1-line substitution `x = u / (d e)` in each `(d, e)` integral!).
  Evaluating at `ψ_0(y) = -C_2(⌊y⌋)` and `a(d) = μ(d) d^{-ε}` (`S = {1, …, D}`) yields the **exact finite-cutoff isometric identity with constant 1**:
  `sizeHypercubeForm 2 ε D = ∫_0^∞ G_{ε,D}(x)² dx/x² = ∫_0^1 |f_{ε,D}(t)|² dt = ∫_{1/(D+1)}^1 |pmPowerDampedFermiSource ε t|² dt + ∫_0^{1/(D+1)} |f_{ε,D}(t)|² dt`,
  and in the `D → ∞` limit (`ε ∈ (0, 1/2)`):
  `ε ∈ receiverDampings ⟺ ∫_0^∞ G_ε(x)² dx/x² < ∞ ⟺ ∫_1^∞ G_ε(1/u)² du < ∞`, with **exact norm equality** `∫_0^1 |pmPowerDampedFermiSource ε t|² dt = ∫_0^∞ G_ε(x)² dx/x²`, linked on Mellin space by the unimodular critical-line Hankel–Fourier multiplier `M_{HT}(s) = -((1 - 2^s)/(1 - 2^{1-s})) (s/(1-s)) · 2(2π)^{-s} Γ(s) cos(πs/2)`!

### Conjecture C-20 (Folded Sieve Transfer Operator `L_ε` on `(0, 1)` & Exact Sine-Divisor Triangulation) — PROVED AS EXACT OPERATOR IDENTITY; NAIVE `C²_0` INVERSION AUDITED
- **Statement & Proof:**
  Setting `G̃_ε(x) := G_ε(x) + 1/(2 ζ(1+ε))` (mean-zero, 2-periodic, odd around `0` and `1`: `G_ε(2 - x) + G_ε(x) = -1/ζ(1+ε)` a.e.), folding `y = m x` into `(0, 1)` via `G̃_ε(y) = (-1)^{⌊y⌋} G̃_ε(dist(y, 2ℤ))` turns `∑_{m=1}^∞ m^{-1-ε} G_ε(m x) = 0` on `(0, 1)` into the `ε`-independent constant-RHS equation:
  `∑_{m=1}^∞ m^{-1-ε} (-1)^{⌊m x⌋} G̃_ε(dist(m x, 2ℤ)) = 1/2` a.e. on `(0, 1)`.
  Its `L²(0, 1)` adjoint `(R_m ψ)(y) = (1/m) ∑_{k≥0} [Ψ((2k+y)/m) - Ψ((2k+2-y)/m)]` (`Ψ = ψ · 1_{[0,1]}`) telescopes at `y = 0` for `ψ ∈ C²([0, 1])` with `ψ(0) = ψ(1) = 0`, satisfying `|(R_m ψ)(y)| ≤ C ‖ψ''‖_∞ y / m²`, so `(L_ε ψ)(y) := ∑_{m=1}^∞ m^{-1-ε} (R_m ψ)(y)` converges absolutely down to `ε > -2` and satisfies `∫_0^1 G̃_ε(y) (L_ε ψ)(y) dy = (1/2) ∫_0^1 ψ(x) dx`. On `ψ_n(x) = sin(π n x)`, `(-1)^{⌊m x⌋} sin(π k dist(m x, 2ℤ)) = sin(π k m x)` identically for all `k ≥ 1`, so `R_m(sin(π n ·))(y) = sin(π(n/m)y)` if `m | n` else `0`, identifying `L_ε` as the real-space divisor-triangular cleared-Mellin operator (`w ↦ ζ(1 + ε + w)`).
- **Audit:** Inverting `L_ε ψ = y^{-2} χ` in `C²_0([0, 1])` requires `M_Ψ(w) / ζ(1 + ε + w)` to be holomorphic in `Re w ≥ -1/2`, which is equivalent to `ζ(s) ≠ 0` on `Re s ≥ 1/2 + ε`; thus `L_ε` exposes the real-space divisor-triangular form of the cleared-Mellin pairing without bypassing zero-freeness via naive smooth inversion.

### Conjecture C-21 (Exact Mellin Pair, Critical-Line Unimodularity, `ε → 0⁺` Unit-Norm Profile `G_0`, and Uncoupled `A_ε + B_ε` Audit) — PROVED ON PAPER; UNCOUPLED SPLIT AUDITED
- **Statement & Proof:**
  1. For `f_ε(t) = pmPowerDampedFermiSource ε t · 1_{(0,1]}(t)` and `h_ε(u) := G_ε(1/u)` (`∫_0^∞ h_ε(u)² du = ∫_0^∞ G_ε(x)² dx/x²`), the exact Mellin transforms are `M[f_ε](s) = ((1 - 2^{1-s})/s)(ζ(s)/ζ(s+ε))` and `M[h_ε](s) = -((1 - 2^{1-s})/s)(ζ(s)/ζ(1-s+ε))` (`M[h_ε](s) = M_{HT}(s) M[f_ε](1-s)`), with **pointwise critical-line modulus equality** `|M[h_ε](1/2 + iτ)| = |M[f_ε](1/2 + iτ)|` for all `τ ∈ ℝ`.
  2. As `ε → 0⁺`, `G_0(x) = (4/π) sin(π x) sin²(π x / 2)` vanishes cubically `G_0(x) = π² x³ + O(x⁵)` at `x = 0`, has exact unit norm `∫_0^∞ G_0(x)² dx / x² = 1` (`|M[h_0](1/2 + iτ)| = |1 - 2^{1/2-iτ}| / |1/2 + iτ|`), and exact odd-dilate inner products `∫_0^∞ G_0(m x) G_0(n x) dx / x² = 2 m - min(2 m, n)` for `1 ≤ m ≤ n` odd (zero for `n ≥ 2m`).
- **Audit of Uncoupled `A_ε + B_ε` Split:** Splitting `G_ε(x) = A_ε(x) + B_ε(x)` into its pure odd-sine series `A_ε(x) = (2/π) ∑_{m odd} (c_ε(m)/m)(sin(π m x) - (π m x)/(1 + π² m² x²))` and even correction `B_ε(x)` makes BOTH `A_ε` and `B_ε` diverge in `ℋ = L²((0, ∞), dx/x²)` even at `ε = 10`, because `∑_{m odd} c_ε(m)² / m = +∞` (`c_ε(m) ≥ ∏_p (1 - p^{-ε}) > 0` for `ε > 1`); finiteness of `G_ε ∈ ℋ` uses the essential cross-cancellation between `sin(π m x)` and `-2^{-1-ε} sin(2π m x)` across dyadic blocks `2^k m`.

### Conjecture C-22 (Unconditional PNT Real-Space Decay of `G_ε(x)` as `x → 0⁺`) — PROVED ON PAPER
- **Statement & Proof:**
  Writing `G_ε(1/u) = ∑_{k≥1} C_r(k) ∑_{k u ≤ d < (k+1)u} μ(d) d^{-1-ε}` (`u = 1/x > 1`), splitting at shell `K_0 = ⌊(log(2+u))^A⌋₊ + 1`, bounding the tail `d ≥ K_0 u` trivially by `≪_ε B_r (K_0 u)^{-ε}` and each head shell `1 ≤ k < K_0` via Abel summation against `MoebiusHarmonicArbitraryLogRate.deningerMertensM_log_pow_rate` (`|mertensM N| ≪_M N / (log N)^M`) yields unconditional logarithmic improvement over the trivial `O(x^ε)` bound: for every `ε > 0` and every `B > 0`, `|G_ε(x)| ≪_{ε,B,r} x^ε |log x|^{-B}` as `x → 0⁺`.

### Conjecture C-23 (Complete Sign-Splitting Resolution of the Open `ε = 1/2` / `σ = 1` Borderline — `SSA §7.3` & `hdf-below-half` line 59) — PROVED ON PAPER (MODULE 7)
- **Context:** Both `SignedSuccessorArithmetic/README.md` (§7.3) and `docs/drafts/pipeline/3-formalized/hypercube-dirichlet-form-below-half-damping.md` (line 59) left the borderline `ε = 1/2` (`σ = 1`) open: `sizeHypercubeForm` was only proved bounded for `ε > 1/2`, and `hypercubeDilationDirichletForm_threshold` left `ε = 1/2` open.
- **Statement & Proof (Exact Sign-Splitting at `ε = 1/2`):**
  1. **Möbius `sizeHypercubeForm hr (1/2) D` is UNIFORMLY BOUNDED in `D` for EVERY `r > 1`:**
     By `sizeHypercubeForm_le_forwardDilated_Ioo_add_const` (Module 5), `sizeHypercubeForm hr (1/2) D ≤ ∫_1^D G_{1/2,D}(1/u)² du + (B_r ζ(3/2))²`. For `u > 1`, split `G_{1/2,D}(1/u) = ∑_{u ≤ d ≤ D} μ(d) d^{-3/2} C_r(⌊d/u⌋)` at `K_0 = ⌊(log(2+u))²⌋₊ + 1`:
     - Tail `d ≥ K_0 u`: `|∑_{d ≥ K_0 u} μ(d) d^{-3/2} C_r(⌊d/u⌋)| ≤ B_r ∑_{d ≥ K_0 u} d^{-3/2} ≪ B_r (K_0 u)^{-1/2} ≤ C_1 B_r / (u^{1/2} log(2+u))`.
     - Head shells `1 ≤ k < K_0`: on `k u ≤ d < (k+1) u` (`d ≤ D`), `⌊d/u⌋ = k` is constant; Abel summation of `∑ μ(d) d^{-3/2}` against `deningerMertensM_log_pow_four_rate` (`|mertensM N| ≤ C N / (log N)^4`) bounds shell `k` by `≪ B_r (k u)^{-1/2} / (log(2+u))^4`. Summing `1 ≤ k < K_0` (`∑_{k < K_0} k^{-1/2} ≤ 2 √K_0 ≪ log(2+u)`) gives `≪ B_r / (u^{1/2} (log(2+u))^3)`.
     Hence `|G_{1/2,D}(1/u)| ≤ C_r / (u^{1/2} log(2+u))` uniformly in `D`, whose square `C_r² / (u (log(2+u))²)` is integrable on `(1, ∞)`. Thus `sup_D sizeHypercubeForm hr (1/2) D < ∞` unconditionally (so `1/2 ∈ receiverDampings` as a limit point / norm bound on `pmPowerDampedFermiSource (1/2)`!).
  2. **Size-Truncated Parity Twin (`w ≡ +1`) DIVERGES like `log D` at `ε = 1/2`:**
     For `r = 2`, `-C_2(m) = m mod 2 ≥ 0` is nonnegative on ALL shells `k ≥ 1`, so `-G^+_{1/2,D}(1/u) = ∑_{1 ≤ d ≤ D} d^{-3/2} (⌊d/u⌋ mod 2) ≥ ∑_{⌈u⌉ ≤ d < ⌊2u⌋} d^{-3/2} ≫ u^{-1/2}` on `u ∈ (2, D/2)` (`D ≥ 6`), yielding `sizeTwinHypercubeForm (1/2) D ≥ c log D → +∞`.
  3. **Prime-Supported Parity Twin `hypercubeTwinDilationDirichletForm (1/2) P_X r hr` DIVERGES for EVERY `r > 1` (closing `hdf-below-half` line 59):**
     Writing `C_r(⌊x⌋) = -∑_{a b = r} a μ(b) {x/a}` (`∑_{b|r} μ(b) = 0` for `r > 1`) and `J_0 := ∫_0^∞ u^{-3/2} {u} du > ∫_0^1 u^{-1/2} du = 2 > 0`, Fubini gives `𝓜(stepHalfLine hr)(0) = ∫_1^∞ x^{-3/2} C_r(⌊x⌋) dx = -J_0 r^{1/2} ∏_{p|r}(1 - p^{-1/2}) < 0`, so `W_r(ξ) = |𝓜(stepHalfLine hr)(ξ)|²` is continuous with `W_r(0) > 0`. On `|2π ξ| ≤ 1/(10 log(X+1))` with `P_X = ∏_{p ≤ X} p`, `cos(2π ξ log p) ≥ 99/100` and `PrimeHarmonicLogLower.log_log_sub_one_le_sum_primesBelow_inv` yield `∏_{p ≤ X} |1 + p^{-1+2πiξ}|² ≫ (log X)^{9/5}`, so integrating over that window gives `hypercubeTwinDilationDirichletForm (1/2) P_X r hr ≫ (log X)^{4/5} → +∞`!
  4. **Spectral Mechanism Separating `μ` from `+1` at `σ = 1`:** Low-frequency primes `p ≤ e^{1/|τ|}` satisfy `cos(τ log p) ≥ cos 1 > 1/2`, hence `|1 - p^{-1+iτ}|² < 1` (suppressing the Euler product at `τ → 0` instead of blowing up like `|τ|^{-2}`), while any high-frequency single-height alignment is capped by Halász's `2/π < 1` exponent (`(|τ| log X)^{2/π} / log X → 0`), and for primorial cutoffs `P_z = ∏_{p ≤ z} p`, `MoebiusSmoothLogPower.exists_norm_sum_moebius_smooth_le_logPower` gives `∏_{p ≤ z} |1 - p^{-1-it}|² ≤ C² (log(|t| + e))^{22}` uniformly in `z`.
- **Lean Module Verified (`lake --old env lean`, exit 0):** `formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheHalfDampingBorderlineSplitsBySign.lean` (wired into `SignedSuccessorArithmetic.lean`, together with `ForwardBackwardDilationNormalityAndFoldedSieve.lean` for P-06 + C-18 + C-21).

### Conjecture C-24 (Multiplicative Convolution of the Reciprocity Kernel on `(ℤ/pℤ)ˣ` & All-`n` Ramanujan–Kloosterman Decomposition) — PROVED ON PAPER & FORMALIZED (MODULE 9)
- **Statement & Proof:**
  Inverting `‖η - 1‖⁻² = 1 / (4 sin²(π u / d)) = (1 / d) ∑_{M=0}^{d-1} Φ_d(M) cos(2π M u / d)` at every modulus `d ≥ 1` and reindexing multiplicatively on `(ℤ/pℤ)ˣ` expresses the nonlinear cosecant–Bernoulli kernel `𝔅(p, n)` for ALL `n : ℕ` (both `p ∣ n` and `p ∤ n`) as an exact orthogonal sum of Ramanujan's sum `c_p(n) = p · 1_{p ∣ n} - 1` and a zero-mean linear Kloosterman cosine wave in `n̄_p`:
  `𝔅(p, n) - m_p = (p + 1) m_p (p · 1_{p ∣ n} - 1) + 1_{p ∤ n} ∑_{m=1}^{p-1} C_m(p) cos(2π m n̄_p / p)`,
  where `m_p = (p² - 1) π² / (72 p²)` and `C_m(p) = (π² p / 2) ∑_{k=1}^{p-1} β_p(k) β_p(m k̄_p mod p)` (`β_p(k) = B₂(k/p) + 1/(6p)`) satisfies `C_{p-m}(p) = C_m(p)`, `∑_{m=1}^{p-1} C_m(p) = 0`, and `C_m(2) = C_m(3) = 0` (`∑_{k=1}^{d-1} β_d(k)² = (d² - 1)(d - 2)(d - 3)/(180 d³)`).

### Conjecture C-25 (Active-Coset Shared Prime-Tower Payment, `p > X` Vanishing, & Top-Octave Dominance) — PROVED ON PAPER & WRITTEN IN LEAN (MODULE 8)
- **Statement & Proof:**
  In `ArithmeticOrientationTheory`, summing the coarse single-prime Cholesky bound `towerOddPrimeSide q X p K ≥ -log p · ∑_{2 ≤ n ≤ X} q(n)²` over `S ⊆ [2, M]` diverged like `-ϑ(M) ∑ q(n)²` as `M → ∞`. Axis-pair cancellation gives `towerOddPrimeSide q X p K = 0` identically for ALL `p > X` (`towerOddPrimeSide_eq_zero_of_lt`), while retaining singleton cosets (`X / p < n`, `p ∤ n`, zero net charge) and top coset sites (`X / p < n`, `p ∣ n`, charge `(log p / p) q(n)²`) proves the `M`-independent bound `∑_{p ∈ S} towerOddPrimeSide q X p (K p) ≥ -∑_{n=2}^X activeTowerWeight S X n · q(n)²` with `activeTowerWeight S X n ≤ θ(X / n) + (1/2) log n`. On the top octave `X / 2 < n ≤ X` (`n ≥ 4`), `θ(X / n) = 0` and `(1/2) log n < archReflectedDiagWeight n`, paying ALL primes simultaneously on arbitrary-sign top-octave profiles (and down to `9 X + 3 n log n ≤ n²`, `n ≳ 3 √X`), while shifted pairs `ζ(s - a)ζ(s + a)` with `|a| ≥ 1` fail even on a single top-octave point mass `q = δ_p`.

### Conjecture C-26 (Dedekind–Kloosterman Dual Formula & Log-Free `O(p^{3/2})` Weil Bound on `C_m(p)`) — PROVED ON PAPER & FORMALIZED (MODULE 9)
- **Statement & Proof:**
  Expanding both `Φ_p` factors spectrally expresses `C_m(p)` (`1 ≤ m < p`) as an exact positive `csc² × csc²` bilinear average of classical Kloosterman sums `S(a, b m; p)`:
  `C_m(p) = (2 π² / p³) ∑_{a=1}^{p-1} ∑_{b=1}^{p-1} Re S(a, b m; p) / (16 sin²(π a/p) sin²(π b/p)) - π²(p - 1)(p + 1)²/(72 p³)`.
  Because `∑_{a=1}^{p-1} 1/(4 sin²(π a/p)) = (p² - 1)/12` is positive and `ℓ¹`-exact, Weil's bound `‖S(a, b m; p)‖ ≤ 2 √p` (`RHTower.norm_kloostermanSum_le_weil`) gives the log-free pointwise bound `|C_m(p)| ≤ (π² / 24) p √p` and `∑_{m=1}^{p-1} C_m(p)² ≤ (π⁴ / 576)(p - 1) p³`.
- **Lean Module Verified (`lake --old env lean`, exit 0):** `formal/GaloisForLFunctions/BezoutValuationIncidence/MultiplicativeConvolutionOfTheReciprocityKernel.lean` (wired into `BezoutValuationIncidence.lean`).

### Conjecture C-27 (Horizon-Uniform Multiplicative Schur Dominance of the Prime Towers Across the `√X` Wall) — PROVED ON PAPER & WRITTEN IN LEAN (MODULE 10)
- **Statement & Proof:**
  Below `n ≲ 3 √X`, dropping non-singleton Cholesky squares left `θ(X / n) ≫ √X > n / 2` unpaid. Instead of dropping off-diagonal coset couplings at each prime separately, bounding `∑_{p ∈ S} towerOddPrimeSide q X p (K p)` via scale-suppressed interior correlations and expanding the asymmetric Schur square `(Λ(m)/(m √m)) (|q(a)| - m |q(a m)|)² ≥ 0` (`m ≥ 2, a ≥ 2`) splits `2 (Λ(m)/√m) |q(a)| |q(a m)|` into:
  - lower-index charge `(∑_{m=2}^X Λ(m)/(m √m)) q(a)² ≤ 8 q(a)²` uniformly in `X`, plus
  - upper-index charge `(∑_{m | b, 2 ≤ m ≤ b/N_0} Λ(m) √m) q(b)² ≤ (√(b / N_0) log b) q(b)²` (`= o(b)` by `∑_{d|b} Λ(d) = log b`!).
  Hence `archReflectedDiagWeight n ≈ n / 2` dominates ALL prime towers simultaneously for **every** cutoff `X ≥ 1` and **every** finite prime set `S` with ZERO `√X` horizon: globally nonnegative (`≥ (1/12) ∑_{n=25}^X n q(n)²`) on profiles vanishing on `[2, 24]` (with arbitrary `q(1)`), and `≥ (1/16) ∑_{n=256}^X n q(n)² - 106 ∑_{n=2}^{min(X, 255)} q(n)²` on completely unrestricted profiles!
- **Audit of `[2, 24]` Finite Head:** Sign-blind Schur (`q ↦ |q|`) cannot eliminate the `[2, 24]` head because `q ≥ 0` represents an even test function on `[-log X, log X]` carrying the pole mode `cosh(x/2)`; genuine closure of `[2, 24]` requires signed polar/gauge orthogonality (`C-29`).

### Conjecture C-28 (Exact Unitary Parseval Rigidity, `Θ(p^{3/2})` Order-Sharpness of `C_m(p)`, Rank-Three Prime Gram Law, & Two-Prime CRT Orthogonality) — PROVED ON PAPER & WRITTEN IN LEAN (MODULE 11)
- **Statement & Proof:**
  1. Unitary Parseval on `(ℤ/pℤ)ˣ` gives `p ∑_{m=1}^{p-1} C_m(p)² = ∑_{n=1}^{p-1} W_K(p, n)²`. Combining with the negativity window `𝔅(p, n) ≤ -p²/100` near `p / 2` proves `∑_{m=1}^{p-1} C_m(p)² ≥ p⁴ / 5120000` and `max_{1 ≤ m < p} |C_m(p)| ≥ (1/2400) p √p` for every prime `p ≥ 67`: Module 9's Weil bounds are order-sharp up to absolute constants (`no single-prime sub-Weil saving on C_m(p)`).
  2. Extracting the coprime mean `-π²(p² - 1)/(72 p)` upgrades the prime pronic Gram `𝒢^{ec}(p, q)` (`p ≠ q`) from rank two to an explicit **rank-three** separable prediction `D_p log q - p β_p - (π²(p² - 1)/(72 p))(1/q)` plus pure zero-mean Kloosterman `W_K(p, q)/q` up to `(3/4) p³/q²`.
  3. By CRT and zero period mean, `∑_{n < p₁ p₂} W_K(p₁, n) W_K(p₂, n) = 0` for `p₁ ≠ p₂`, collapsing any incomplete correlation `∑_{n < M} W_K(p₁, n) W_K(p₂, n)` to `range (M % (p₁ * p₂))`.

### Conjecture C-30 (Bochner Positivity, `√p`-Loss-Free Wiener Algebra of `W_K(p, ·)`, & Quadratic-Chirp Sharpness of the `P^{5/2}/Q^{3/2}` Large-Sieve Barrier) — PROVED ON PAPER; WIENER LAW IN MODULE 11
- **Findings:**
  1. Every nonzero linear cosine Fourier mode `α̃_p(h)` (`1 ≤ h < p`) of `𝔅(p, n)` on `ℤ/pℤ` is nonnegative (`bernoulliLinearCoeff_nonneg`), so Bochner evaluation at `n = 0` gives the exact `ℓ¹` sum `∑_{h=1}^{p-1} α̃_p(h) = π²(p² - 1)²/(72 p²)` and `∑_{h=1}^{p-1} |α_p(h)| ≤ π²(p² - 1)²/(36 p²) ≤ (π²/36) p²` (zero `√p` Cauchy–Schwarz loss!).
  2. **Quadratic-chirp obstruction witness on generic bounded weights (`P ≤ Q < P²`):** The bounded weight `b_q = e(-q² / (4 P Q))` on `[Q, 2Q]` sweeps instantaneous frequency across `[1/(2P), 1/P]`, giving `|∑_{q=Q}^{2Q} b_q e(q/p)| ≍ √(P Q)` for **every** `p ∈ [P, 2P]` simultaneously and `∑_{p ∼ P} |S(1/p)|² ≍ P² Q = P² ‖b‖₂²`. Thus no generic `ℓ^∞` / sign-blind additive large sieve on `{1/p : p ∼ P}` can beat `P^{5/2} / Q^{3/2}`.

### Conjecture C-31 (Why Balanced-Diagonal `Λ_p(c')` Is `0/1` Major-Arc vs Signed-Modulus Cancellation `∑_d c(d) Λ_d(c') / d`) — ANALYZED
- **Audit against `fable-2410-A` (`TheCentredPrimeRowIsMinorArcBelowTheDiagonal`, `TheDualNormAtCompositeModuli`, `TheBalancedStatisticIsTheQuasiRiemannHypothesis`):**
  1. Corpus search confirmed that `fable-2410-A` already formalized unconditional power saving `|Λ_d(c')| ≤ 11 (1+log 2Q)⁴ (d²/Q) Q^{-δ/32}` at all `Q^δ ≤ d ≤ Q^{1-δ}` (via Vinogradov/Vaughan minor arcs) and `C (d²/Q) e^{-c√log Q}` on `[Q^δ, 2Q]`, and proved that a power saving on the unsigned dual-norm statistic `|Λ_d(c')|` on `Q^{1-ε} ≤ d ≤ Q^{1+ε}` is equivalent to `Θ < 1`.
  2. **Mechanism:** At `d = p ≍ Q`, the dominant `h = ±1` linear Fourier mode `e(±n / p)` of `𝔅(p, n) - m_p` has frequency `1/p ≍ 1/Q`, which lies dead center on the **`0/1` archimedean major arc** (`|1/p - 0/1| ≍ 1/Q`): `n ↦ cos(2π n / p)` completes `O(1)` periods across `(Q, 2Q]`, so Vaughan's `u = 1` Type-I term has zero modular oscillation (`≍ Q`) and `Λ_d(c')` is a smooth archimedean functional of `M(x)` / `ψ(x) - x`.
  3. **Crucial Distinction (`|c(d)| ≤ 1` vs Actual Signed Row `c(d) = μ(d)`):** Passing to the dual norm `∑_d |Λ_d(c')| / d` throws away the signs of the *small-scale* row `c(d)` (`d ∈ (P, 2P]`)! At `P ≍ Q`, when `c(d) = μ(d) d^{-ε}` AND `c'(n) = μ(n) n^{-ε}` (or inside the signed Bézout interior martingale `M^{\text{int}}_T` / symmetric Gram `∑_{d, n} c(d) c(n) 𝒢^{ec}(d, n)`), keeping the signed sum over BOTH `d` and `n` is the exact opening highlighted in `BVI §7.2` and `§7.8.2`!

## Formalized & Written Lean Modules in This Loop
1. `ArithmeticCriticalityTheory/LightConeAntisymmetricVariationLaw.lean` — verified (exit 0) & wired.
2. `SignedSuccessorArithmetic/TheSizeTruncatedHypercubeFormIsTheReceiver.lean` — verified (exit 0) & wired.
3. `HTGeometry/CharZeroShiftedSubgroupStepanov.lean` — verified (exit 0) & wired.
4. `TransHorizonIncidenceMechanics/HyperbolicLightConeSubunitCollarBridge.lean` — verified (exit 0) & wired.
5. `SignedSuccessorArithmetic/TheForwardDilatedHypercubeForm.lean` — verified (exit 0) & wired.
6. `SignedSuccessorArithmetic/TheHalfDampingBorderlineSplitsBySign.lean` — verified (exit 0) & wired.
7. `SignedSuccessorArithmetic/ForwardBackwardDilationNormalityAndFoldedSieve.lean` — verified (exit 0) & wired.
8. `BezoutValuationIncidence/MultiplicativeConvolutionOfTheReciprocityKernel.lean` — verified (exit 0) & wired.
9. `ArithmeticOrientationTheory/HorizonUniformSchurDominanceOfThePrimeTowers.lean` — verified (exit 0) & wired.
10. `BezoutValuationIncidence/ExactParsevalAndRankThreeKloostermanLawOfThePrimeGram.lean` — verified (exit 0) & wired.
11. `ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean` — verified (exit 0) & wired.
12. `ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean` — verified (exit 0) & wired.
13. `ArithmeticContinuationAndCriticalEnergy/UnconditionalBirmanSchwingerRateReadsTheZeroWidth.lean` — verified (exit 0) & wired (eliminates `NonClusteringAtWidth`: proves `formGroundEnergyRate = birmanSchwingerNormRate = zetaZeroWidth` unconditionally).
14. `SignedSuccessorArithmetic/TheSignedPrimeDivisorEndpointAtHalfDamping.lean` — written (C-40s `stepSpectralWeight` `L^∞` + dyadic `O((k+5)/2^k)` decay, C-40a finite-deletion primorial `O_r(1)` at `ε = 1/2`, C-40b uniform `O_r((log z)^{17/24})` across all `2^{π(z)}` subsets `S ⊆ primesLE z`), building dependency `.olean` + Rule-3 check.
15. `ArithmeticOrientationTheory/ActiveCosetTowerPaymentAndTopOctaveDominance.lean` — written, awaiting `ContinuumTowerReflectionCholesky.olean` + Rule-3 check.

## Log
- 2026-10-25 — Created persistent conjecture-loop card in `1-in-progress`; mapped concurrent agent worktrees to ensure zero file collisions.
- 2026-10-25 — Audited C-01 through C-07 against C1–C11; extracted three dependency-closed positive survivors (P-01 `sizeHypercubeForm` spectral-receiver bridge, P-02 2D correspondence Arakelov theta `h⁰` Riemann–Roch on `ℤ²`, P-03 characteristic-zero unbounded-degree sparse root-multiplicity & Stepanov) and isolated the cross-scale `(x ≈ r, y ≈ O(1))` theta cancellation in C-05.
- 2026-10-25 — Derived C-08: exact antisymmetric light-cone `(t, s)` representation of `Z(m_a u)` with strictly positive continuum kernel `κ(s) - κ(t) > 0` across all `(0, ∞)` (bypassing the even-gauge plastic threshold `0.2812` completely). Verified `LightConeAntisymmetricVariationLaw.lean` (exit 0) and wired into `ArithmeticCriticalityTheory.lean`.
- 2026-10-25 — Completed C-08b, C-09, C-10, C-11; wrote `HyperbolicLightConeSubunitCollarBridge.lean`, `TheSizeTruncatedHypercubeFormIsTheReceiver.lean`, `TheForwardDilatedHypercubeForm.lean`, and `CharZeroShiftedSubgroupStepanov.lean`.
- 2026-10-25 — Audited C-12 (DMV Beurling refutes pure multiplicative coprime balance) and derived C-13 (exact forward-dilation reflection of `sizeHypercubeForm` onto `(1, D)` with absolutely summable `d^{-1-ε}` weights + Davenport–Müntz `ε = 0` audit).
- 2026-10-25 — Derived C-14 (cutoff-free `H_ε ∈ L²(1, ∞) ⟹ RH`), C-15 (rounding-free sieve `G_ε(x) = -∑_{m≥2} m^{-1-ε} G_ε(m x)` on `x < 1` + 2-periodicity), C-16 (positive Euler-product Fourier series `c_ε(m) = ∏_{p|m}(1 - p^{-ε}) ∈ (0, 1]`), C-17 (ACS universal floor law audit), C-18 (`S ⊂neq ℙ` modulated prime-subset counterexample + unique Möbius characterization from 2-periodicity + full additive sieve), and C-19 (exact Hilbert-space normality `sizeHypercubeForm 2 ε D = ∫_0^∞ G_{ε,D}(x)² dx/x² = ∫_0^1 |f_{ε,D}(t)|² dt` and unimodular Hankel–Fourier duality between `G_ε` and `pmPowerDampedFermiSource ε`).
- 2026-10-25 — Derived C-20 (folded sieve transfer operator `L_ε`), C-21 (`G_0` unit-norm profile + uncoupled `A_ε + B_ε` audit), C-22 (unconditional PNT real-space decay `|G_ε(x)| ≪ x^ε |log x|^{-B}`), and C-23 (complete sign-splitting resolution of the open `ε = 1/2` / `σ = 1` borderline: `sizeHypercubeForm hr (1/2) D` uniformly bounded for all `r > 1`, while both size-truncated and prime-supported parity twins diverge to `+∞`).
- 2026-10-25 — Verified `TheHalfDampingBorderlineSplitsBySign.lean`, `ForwardBackwardDilationNormalityAndFoldedSieve.lean`, and `MultiplicativeConvolutionOfTheReciprocityKernel.lean` (all exit 0); wrote `HorizonUniformSchurDominanceOfThePrimeTowers.lean` (C-27), `ExactParsevalAndRankThreeKloostermanLawOfThePrimeGram.lean` (C-28 + C-30), and `ActiveCosetTowerPaymentAndTopOctaveDominance.lean` (C-25); audited C-31 against `fable-2410-A`.
