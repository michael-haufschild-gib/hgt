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
