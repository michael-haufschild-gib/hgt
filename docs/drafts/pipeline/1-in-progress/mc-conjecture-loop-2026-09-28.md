# MC conjecture loop (2026-09-28)

- **ID:** `MC-LOOP-2026-09-28`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP (working log)
- **Route:** MC (frontier map §MC). Target: RH ⇔ |D(X)| ≤ B√X, D(X)=X−1−Σ_{n≤X}Λ(n)log(X/n); one side suffices.
- **Rule:** one row per cycle; verdict ∈ {FALSE, CIRCULAR, REDISCOVERED, BRIDGE, INSIGNIFICANT, SURVIVES}; learning → next cycle.

## Corpus facts used (do not rediscover)
- Short quadratic work B(T), W(T); Euler completion renewal D−A_P = ρ_P⋆ρ_P⋆D (positive kernel, supercritical at ½).
- Beurling firewall: continuous systems with N=ρx+O(x^θ) and off-line zeros (3-formalized/regular-beurling-integers-do-not-constrain-the-zeros.md); rational Beurling classification; H1–H4 independence + rigidity of summable deformations (4-publication-ready/euler-functional-equation-independence.md); Theorem N (linear Λ-positivity caps at PNT).
- Route E receiver: Γ–Hankel covariance Σμ(m)μ(n)(m+n)^{-r}; edge-pair sign sections ≤0 (RouteEAllQuotientPowerEdgeDominance).

## Cycles
| # | Conjecture | Verdict | Learning |
|---|---|---|---|
| 1 | Hyperbola kernel K_X=[L(X/ab)]_{a,b≤√X} is Lorentzian ⇒ reverse Cauchy–Schwarz gives one-sided D bound | FALSE (as producer) | Linear term λ=⟨μ_U,s_X⟩≈(1+γ)X·m(U) is X^{3/4} individually; cancellation needs 1+ℓ(U)=O(U^{-1/2}) (RH at √X). Hyperbola carrier is exponent-covariant: normalized error at X is quadratic in normalized errors at √X; off-line β is a fixed point of squaring — no contraction. |
| 2 | ω-partition polynomial N_x(t)=Σ_{n≤x}μ²(n)t^{ω(n)} is real-rooted; M(x)=N_x(−1) controlled by root near −1 | INSIGNIFICANT for MC | ω-statistics are Beurling-deformable; Selberg–Delange main term F(1,t)/Γ(t) is real-rooted but the √x scale is invisible to it. |
| 3 | Interpolate N_x at zero-blind nodes t=0..K: M(x)=Σ_k(−1)^kC(K+1,k+1)Σμ²(n)k^{ω(n)} (exact) and bound each node | FALSE | Nodes k≲log x/loglog x leave Selberg–Delange uniformity; high-k 'main terms' are x^{1+o(1)} and must cancel against errors. RH content sits in the ω large-deviation regime. |
| 4 | Discrete Beurling integers with N=Ax+O(x^θ), θ<½ force RH_B | FALSE (would imply RH via ℤ; case split ¬RH⇒ℤ, RH⇒perturbed primes gives a countermodel sketch) | Integer-count regularity is not the MC mechanism; firewall already exists in continuous form. Not MC-forward. |
| 5 | Euler/sieve completion a with subcritical signed renewal symbol sup_{Re s=½}|Aζ−1|<1 | FALSE | |Aζ−1|=1 at every critical-line zero: every renewal completion is exactly critical; on Re s=½+δ sup=∞ for Dirichlet polynomials (ζ unbounded, A almost periodic). |
| 6 | LP/SDP "bootstrap" certificate (crossing = FE, unitarity = Weil) for one-sided D | CIRCULAR | Linear positivity capped at PNT (Theorem N); Λ-positivity not SDP-representable (Theorem X). |
| 7 | Selberg Λ² square Σ_{n≤X}(Σ_{d\|n,d≤√X}μ(d))²≥0 minus hyperbola (lcm vs product) gives one-sided M bound | FALSE (trivial size) | H−S = −XΣ_g μ²(g)(g−1)/g²·(coprime reciprocal Möbius sums at U/g)² with mixed μ(h) signs; bound ~X (large g terms). Positivity again caps. |
| 8 | Log-Riesz divisor kernel: L(y)=y(A log y+B)+C log y+C'+O(y^{-1/4}) (Voronoi) makes D(X) = quadratic in 4 moments at √X + small | FALSE as reduction | Voronoi remainder bilinear form Σμ(a)μ(b)R(X/ab) has flat phase at the corner a,b~√X; trivial bound X. FE enters D only at the corner, where it is phase-flat. |
| 9 | Lorentzian collapse: s=1 pole core 2Xm(1+ℓ)−X log X m² ≤ X(1+ℓ(√X))²/log X (AM-GM) ⇒ one-sided MC from one statistic | CIRCULAR | Correct identity, but |1+ℓ(U)|≲U^{-1/2+ε} ⇔ RH at √X; μ-statistics carry 1/ζ'(ρ) weights, Λ-target carries 1/ρ²; renormalization never closes (μ/Λ asymmetry). |
| 10 | Sign-reversing involution on squarefrees ≤x with O(x^{½+ε}) fixed points (toggle smallest prime) | REDISCOVERED/FALSE | Iterated toggles leave x/log y unmatched (Björner slab); Route E matching closed (CANNOT-346/349/351–353). |
| 11 | Zaslavsky: realize knapsack poset as real arrangement so |M(x)| counts regions | FALSE | Knapsack complex is not a matroid complex (exchange fails for p>x/2); face lattice not geometric. |
| 12 | Horocycle (Zagier) / Eisenstein Maass–Selberg positivity | REDISCOVERED | Rate y^{3/4} ⇔ poles of φ(s)=ξ(2s−1)/ξ(2s) at Re s=ρ/2, outside the spectral-positivity region; HB retired. |
| 13 | Transfer operator (Mayer) positivity for Selberg zeta zeros at ρ/2 | FALSE | Needed strip 1/4<Re s<1/2 has spectral radius λ₁(σ)>1; complex Ruelle operators give no contraction there. |
| 14 | Prime-free test-function windows give archimedean-only zero sums | REDISCOVERED | Support ⊂(−log2,log2) is the RW small-aperture regime (corpus Weil positivity past √2). |
| 15 | Jentzsch-type: zeros of Möbius partial sums M_N(s) accumulate only at Re s=½ ⇔ RH | BRIDGE | Receiver only; zero-freeness of M_N needs |1/ζ|−|tail| lower bounds = RH. |
| 16 | Laguerre coefficients of D(e^T)e^{-T/2} bounded | REDISCOVERED | c_k = Σ_ρ ρ^{-2}(1−ρ)^{-1}(ρ/(ρ−1))^k — Keiper–Li for D (LI route). |
| 17 | Twist-generic MC: set B of unimodular twists χ with MC failing for μχ | SURVIVES (structural) | B is Kronecker-flow invariant, Haar-null (Wintner/Helson), and comeagre (set χ(p)=−1 on a long prime range ⇒ partial sums ≫x/log y). Category and measure disagree; RH asks about one special point. Candidate positive survivor, low RH-significance. |
| 18 | Γ–Hankel covariance gcd factorization E_r=Γ(r)(ζ(r)/ζ(2r))Σ_{(a,b)=1}ν(a)ν(b)(a+b)^{-r} = Möbius vs central divisor density n^{-r/2}Σ_{d\|n}(2cosh log(d/√n))^{-r} | REDISCOVERED (primitive-ratio decomposition in corpus) | Entire expected (r−1)^{-1} divergence sits in ζ(r)/ζ(2r); RH ⇔ coprime covariance bounded as r↓1. |
| 19 | Möbius graph closure over Γ-Laplace atoms is all of H×H (Müntz: Σ1/p=∞) | SURVIVES (no-go strengthening) | Resolves recorded open question; kills operator-closure producers maximally; low RH-significance. |
| 20 | Real-rootedness of N_x(t) for every x | UNDECIDED / likely INSIGNIFICANT | Truncated-Poisson model has Szegő complex zeros; actual top coefficients decay faster. MC needs root within x^{-1/2} of −1, which real-rootedness does not give. |
| 21 | Discrete Beurling perturbation p↦pe^{η_p} moving a zero to β' keeps N-error below √x (under RH) ⇒ discrete firewall | FAILED (beyond reach) | Crossing counts inherit RH-level prime-count errors in short intervals (√x log x); proving sub-√x integer error needs Montgomery–Soundararajan-type variance. Heuristic cost: integer exponent ≈ 1/(2(2−β')) ≥ 1/3. |
| 22 | **Discrete multiplicative uncertainty (DMU)**: for discrete Beurling systems with HN exponents [α,β,γ] (primes, integers, Möbius), Θ=max ≤ max(½, 2β) — i.e. integer regularity below a threshold β₀ forces RH_B | OPEN CONJECTURE (new field) | Implies RH (ℤ: β=0) and, if β₀>0.315, GRH for L(χ₋₄) (ℤ[i] ideal count, circle exponent). Continuous systems violate it maximally (ζ=(s−1+ρ)/(s−1): N exactly linear, Θ=1−ρ) — explains every corpus Beurling firewall: the √x barrier is a discreteness phenomenon (Hilberdink–Neamah lower relation Θ≥½). |
| 23 | Sub-orthogonality (SO): O_r(N) ≤ 0 ∀N, r∈(1,2σ₀) — Γ-smoothed Mertens conjecture | SURVIVES (plausible under RH+simple zeros, margin ~10^{17} at r↓1); implications FORMALIZED | Lean: SO ⇒ RH ∧ all strip zeros simple; multiplicity law: energy ceiling C/(2σ−1)^k ⇒ 2·order ≤ k+1. Card 3-formalized/mobius-gamma-hankel-sub-orthogonality.md. |
| 24 | Prove SO via a graph Poincaré inequality: −O = ½Σ_{m≠n}K(μ_m−μ_n)² − Σμ_m²deg(m) ≥ 0 | CIRCULAR | SO ⇔ Rayleigh quotient of μ for the Γ–Hankel Laplacian ≥ 1 ⇔ weighted L² bound for M_N on Re s = r/2 (Plancherel). |
| 25 | SO holds for Haar-generic multiplicative twists | FALSE | For Rademacher twists E[O_r(N)] = 0 with positive variance, so SO fails with positive probability. SO is non-generic: μ is antiferromagnetic on the Γ–Hankel graph. Its energy is O(1) at low height, while a random twist's is ~D ~ 0.3/(r−1), because 1/ζ is a fixed analytic function near ½ and random L_f⁻¹ is log-normal. |
| 26 | SO fails only at astronomically large N if ¬RH | SURVIVES (heuristic) | An off-line zero at height γ₀ with β>½ enters M_N(r/2+it), |t|≲10, only once N^{β−r/2} ≳ γ₀|ζ'(ρ₀)|. SO is a low-height phenomenon at every finite N and RH-strength only cofinally. That matches the gate: the cofinal source law carries RH. |

## Next cycle plan
- Attack SO on a cofinal structured family: extend RouteEAllQuotientPowerEdgeDominance (edge sections ≤0) to all divisor-comparable pairs (m | n), then to fixed-gcd strata; find the first section whose sign law fails and extract the survivor.
- DMU: look for a rigorous instance (quadratic-field systems: β ≈ circle exponent) or a counter-construction with β < 1/3 and Θ > ½.
