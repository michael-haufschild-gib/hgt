# Exact ordinate coincidence fact log (own research; facts and no-gos only)

| id | fact | status |
|-|-|-|
| EOC-F1 | Two-prime Cesàro excess is zero-indexed; limit = K(T); unconditional bound only Cauchy density ≍ log t | L (corpus) |
| EOC-F2 | Prime-side two-prime pencil exists: lag_explicit_formula at X=4^a9^b | L (corpus) |
| EOC-F3 | χ_p(ρ)χ_p(1−ρ̄)=χ_p(ρ)·conj χ_p(1−ρ): hol×antihol at one point ⇒ not explicit-formula-able | P |
| EOC-F4 | Holomorphic clock unimodular on line ⇒ log|λ(1−s̄)|=−log|λ(s)| ⇒ one growing mode per free orbit | P |
| EOC-F5 | Holomorphic two-prime excess: 0 if window critical, unbounded otherwise ("∞·K") | P |
| EOC-F6 | Collisions under FE are codim 0 and Hurwitz-stable; CANNOT-402 transversality premise void | P |
| EOC-F7 | One prime clock suffices for growth detection (positive multiplicities forbid alias cancellation) | P |
| EOC-F8 | Lean: xiTwoPrimePencil_reflected_holomorphic_exchange (reflected excess → K(T); holomorphic excess bounded ⟺ K(T)=0); RH ⟺ ∀T holomorphic excess bounded; collision stability (Hurwitz) | L |
| EOC-F9 | Cross-route pattern: route 1 (chiral passage) also dies on holomorphy; quantized invariants are zero-indexed, source realizations are holomorphic and unquantized | P (meta) |
| EOC-F10 | Lean `XiHorizontalSingletonFiberHalfDensity`: liminf singleton-fibre ratio ≥ 1/2 (from 2/3 simple-critical) and ≥ (3·HD 1 − 1)/2 ≈ 0.5087 (Montgomery–Taylor); corpus had 0.116 | L |
| EOC-F11 | Stepanov/Chebyshev auxiliary integer over ℤ: log F = Σ Λ(n) g(X/n), g sawtooth; √X precision = one-sided Nyman–Beurling (CANNOT-LIN1); Stepanov's gain needs x^q−x, whose ℤ-analog lcm(1..N) has size ψ(N) | P (no-go) |
| EOC-F12 | Zeta23 inertia method is density-only: an off-line pair's block 2m(aaᵀ−bbᵀ) has negative eigenvalue O(δ²), maskable; route to exactness closed by resolution | P |
| EOC-F13 | Lean `XiLineUnimodularClockExcessCriterion`: every entire line-unimodular clock obeys Λ(s)·conj Λ(1−s̄)=1; window excess unbounded iff a zero leaves {|Λ|=1}, else → aliasing charge ≥ 2 per off-line zero; sub-quantum bound ⇒ window critical for every clock | L |
| EOC-F14 | Singleton bound 1/2 is sharp for inputs (κ_s=2/3): adversary = singletons + fibres (1 simple critical + 1 simple off-line pair), A = S/3; Zeta23 posIndex cannot separate collided fibres (posIndex ≤ 2 for 3 copies) | P |
| EOC-F15 | Zeta23 Fejér window κ(λ)=2/λ−2/(3λ²)+(2/λ)∫_1^λ F(α)(1−α/λ)dα for λ≥1 (=1/λ+λ/3 for λ≤1); dκ/dλ at λ=1 is −2/3, so any F=O(1) on [1,1+ε] beats 2/3 | P |
| EOC-F16 | NO-GO: sieve upper bounds for Σ Λ(n)Λ(n+h) cannot supply that O(1): the h²x main term must cancel to leave h log(x/h); factor-c sieve loss gives F(α) ≳ T^{α−1}/log T; averaged ∫_b^{b+1}F bounds allow a spike at 1⁺ (need average <1/3, truth ≈1). Exact missing input: optimal-order variance of primes in intervals of length x^ε (Goldston–Montgomery) — RH-level. Under RH this route gave only 0.6727 (Cheer–Goldston) | P (no-go) |
