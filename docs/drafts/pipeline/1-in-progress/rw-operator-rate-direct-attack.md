# Direct attack on the rate of the pole-compressed prime translation operator

Status: FAILED. No estimate below the trivial rate is obtained. No Lean claimed.

Target (RW/WL open core, MUST-250/255): `limsup_A (1/A) log ‖P_{V₀} C_A P_{V₀}‖ < 1` for
`C_A = Σ_{n<e^{2A}} Λ(n) n^{−1/2} (τ_{log n} + τ_{−log n})` on `L²(−A,A)`, `V₀ = {f : ∫f e^{±x/2} = 0}`.
Rate `c < 1` ⟺ zero-free strip `β ≤ ½ + c/2`; sub-exponential ⟺ RH.

## Attempt 1: Fourier multiplier with the pole removed
`C_A` is convolution by `μ_A = Σ_{n<e^{2A}} Λ(n)n^{−1/2}(δ_{log n}+δ_{−log n})`; on long intervals its norm is
`sup_ξ |μ̂_A(ξ)| = sup_ξ |2Re Σ_{n<X} Λ(n) n^{−1/2−iξ}|`, `X = e^{2A}`. The trivial rate `2√X` sits at `ξ = 0`
and is the main term `∫_1^X x^{−1/2}dx` of the pole of `ζ'/ζ` at `s = 1`. Projecting out `e^{±x/2}` removes
exactly this main term, leaving `Σ_{n<X}(Λ(n)−1)n^{−1/2−iξ}`. By the explicit formula this is
`−Σ_ρ X^{ρ−½−iξ}/(ρ−½−iξ) + O(log² X)`, whose size is `X^{Θ−½+o(1)}`.
**Fails:** a bound `≪ X^{c/2}` with `c < 1`, uniformly in `ξ`, is a uniform power saving for twisted
Chebyshev remainders, i.e. quasi-RH itself (Ingham). The strongest unconditional saving is
`exp(−c(log X)^{3/5}(log log X)^{−1/5})` (Vinogradov–Korobov), which gives rate exactly 1.

## Attempt 2: arithmetic Gram positivity on `ℚ_{>0}^×` (WL's "archimedean Hodge index")
`RH ⟺ (Φ(log(n/m)))` PSD (`riemannHypothesis_iff_arithmeticGramForm_nonneg`). Indices `log(n/m)` form the free
group `⊕_p ℤ`; by Bochner, PSD ⟺ a positive spectral measure on the torus of unimodular completely
multiplicative functions. Via the explicit formula this measure is the push-forward of the zero distribution
along `t ↦ (p^{it})_p`. **Fails:** the "Hodge index" is the zero measure seen through the Bohr compactification;
every finite prime set `S` gives a subgroup `ℤ^S` on which positivity is structurally non-forcing
(`RingRecursionWitness`); the full group is RH verbatim. CIRCULAR.

## Attempt 3: witness rigidity at a positive exponent (PM ladder)
`zetaZeroFreeStrip_iff_mellinFermiWitness_selfSimilar` [L]: rigidity at Mellin exponent `a` ⟺ no zero in
`1−a < Re s < 1`. The only analytic input that makes the Liouville argument work is pole-freeness of
`V_w` on `Re z < a`, i.e. the conclusion. Mellin multipliers cannot move poles, and dilations preserve the
exponent. **Fails:** CIRCULAR.

## Positive survivor
The three attempts reduce to one uniform statement: `Σ_{n<X}(Λ(n)−1) n^{−σ−iξ} ≪ X^{1−σ−δ}` uniformly in `ξ`,
for some fixed `δ > 0`. It is already recorded as MUST-250/255 and CANNOT-466.
NO POSITIVE SALVAGE FOUND beyond these existing entries.
