# Distributional laws for the mollified deviation `ζΨ − 1`

- **ID:** MOLL-DEV-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (law) with THEOREM (Lean) components
- **Source:** `3-formalized/zeta-off-line-first-moment-mollified-ceiling.md` §(ii) (the `(L)` residue
  is distributional); user directive 2026-09-05 "research, identify, formalize the distributional
  laws for ζΨ − 1"
- **Statement:** For the linear mollifier `Ψ_M(s) = ∑_{m≤M} μ(m)(log(M/m)/log M) m^{-s}`,
  `M = T^θ`, the deviation `W_M(t) := ζΨ_M(1/2+it) − 1`, `t` uniform on `[T, 2T]`, converges in
  law to the circular complex Gaussian `CN(0, 1/θ)`; its *head* — the truncated logarithmic
  derivative `H_M = −(1/log M)(ζ'/ζ)_{≤M}` — carries variance exactly `1/2` and is Gaussian to
  every accessible order.

## 1. Exact structure (Lean)

`MollifiedDeviationHeadVariance` (wired, axiom-clean):

1. **Head identification.** `mollifiedProductDirichletCoeff_eq_vonMangoldt`: for `1 ≤ k ≤ M` the
   Dirichlet coefficient of `ζ·Ψ_M` is `[k = 1] + Λ(k)/log M` (Barban–Vehov/Möbius inversion,
   corpus `barbanVehovCoeff_eq_vonMangoldt`). Hence
   `W_M = H_M + (tail supported on k > M)`, `H_M(s) = (1/log M) ∑_{1<k≤M} Λ(k) k^{-s}`.
2. **Chebyshev square-weight law.** `tendsto_sum_vonMangoldt_sq_div_div_log_sq`:
   `∑_{k≤N} Λ(k)²/k / (log N)² → 1/2` (higher-order Mertens `∑_{p≤x} log²p/p = ½log²x + C + o(1)`
   plus the `O(log N)` prime-power part).
3. **Head variance law.** `exists_mollifiedDeviationHead_meanSquare_close`: for every `ε > 0` there
   is `M₀` such that for all `M ≥ M₀` and every window `[T₁,T₂]` of length `≥ M²`,
   `|(1/(T₂−T₁)) ∫ |H_M(1/2+it)|² dt − 1/2| < ε` (corpus Dirichlet mean value theorem, error
   `8M(1+log M)`). The head's variance is `1/2`, independent of `θ`.

## 2. Known inputs (literature, not Lean)

- `E[ζΨ_M] → 1` (mollified first moment); `E|ζΨ_M|² → 1 + 1/θ` for `θ < 1/2` (Levinson 1974) and
  `θ < 4/7` (Conrey 1989). Hence `E W → 0`, `E|W|² → 1/θ`, and the tail plus cross term carries
  `1/θ − 1/2`.
- Non-absolute second moment: the CFKRS-type recipe gives `E[(ζΨ)²] → 1`, hence `E W² → 0`
  (circularity at second order).
- Twisted fourth moment: Hughes–Young (`θ < 1/11`), Bettin–Bui–Li–Radziwiłł (`θ < 1/4`); the explicit
  mollified constant `c₄(θ) = lim E|ζΨ|⁴` is derivable from their main terms (not extracted here).

## 3. The conjectured law and its exact consequence (Lean)

**Conjecture (MOLL-DEV).** `W_M → CN(0, 1/θ)` in law as `T → ∞`, for every fixed `θ` in the
mean-value range, with uniform integrability of `log|1 + W_M|²`.

Consequence formalized: `ComplexGaussianLogMeanExponentialIntegral`
(`complexGaussianLogMeanRadial_eq_expIntegralE1`): for `W ~ CN(0, σ²)`,
`E log|1 + W|² = E₁(1/σ²)`, `E₁(x) = ∫_x^∞ e^{-u}/u du` (polar coordinates, Jensen's circle
identity `⨍ log|1 + r e^{iφ}| = log max(r,1)` from `RiemannSiegelPhaseTorusLogMean`, one
integration by parts, the substitution `u = r²/σ²`).

Therefore the law predicts, with `σ² = 1/θ`:

```text
E log|ζΨ|² → E₁(θ):   E₁(4/7) ≈ 0.482,  E₁(1/2) ≈ 0.560,
(1/T)∫_0^T log|ζ(1/2+it)| dt ≤ ½ E₁(θ) + o(1) ≈ 0.241   (θ = 4/7),
```

replacing the unconditional Jensen ceiling `½ log(1+1/θ) = 0.506`. Under RH (`E log|ζ|² = 0`) the
same law forces the mollifier's own log-mean `E log|Ψ_M(1/2+it)|² → E₁(θ)`: the Möbius
mollifier has a positive `O(1)` log-mean although its mean square is `≍ log M`.

## 4. Why the head is Gaussian (paper sketch, not yet Lean)

`H_M(1/2+it) = ∑_{k≤M} a_k k^{-it}`, `a_k = Λ(k)/(log M √k)`, supported on prime powers. For
`kθ < 1` the `2k`-th moment is the diagonal of a Dirichlet polynomial of length `M^k < T`, and by
unique factorization the only solutions of `k₁⋯k_k = l₁⋯l_k` with prime-power entries are
permutations, apart from same-prime coincidences of relative size `O(1/log² M)`; so
`E|H_M|^{2k} → k! (1/2)^k`, the moments of `CN(0, 1/2)`. Mixed moments `E H^a H̄^b`, `a ≠ b`,
vanish. This is the standard prime-sum computation (Radziwiłł–Soundararajan style); it is rigorous
only for `k < 1/θ` because the variance of `H_M` is carried by the *large* primes `p ≈ M`.

## 5. Falsifiers

- `c₄(θ) ≠ 1 + 4/θ + 2/θ²` (the `CN(0,1/θ)` fourth moment) — computable from Hughes–Young /
  Bettin–Bui–Li–Radziwiłł; if it fails, the tail is non-Gaussian and the law must be replaced by
  `H_M + (non-Gaussian tail)` with the head still `CN(0,1/2)`.
- Any proof that `E log|ζΨ|² > E₁(θ) + δ` unconditionally would contradict the law; Jensen only
  gives `≤ log(1+1/θ)`.
- The two-point construction of `JensenGapSecondMomentNoGo` shows second and fourth moments alone
  cannot pin `E log|1+W|²`; a proof of the law's log-moment consequence needs a small-ball/tail law.

## 6. Open core `[OPEN CORE]`

The Gaussian law for the *tail* (frequencies `> M`, length up to `√T·M`) is a statement about a
long Dirichlet polynomial with Selberg-sieve-type coefficients `∑_{d|n, d≤M} μ(d)log(M/d)/log M`;
no mean-value technology controls its moments beyond the fourth. The head's Gaussianity is provable
to order `2⌊1/θ⌋` and is the next Lean target (`E|H_M|⁴ → 1/2` for `θ < 1/2`).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (the law is conjectural; components 1–3 and the `E₁` identity are proven)
- [x] 2 → 3  formalized components: `MollifiedDeviationHeadVariance`,
  `ComplexGaussianLogMeanExponentialIntegral` (axioms `propext, Classical.choice, Quot.sound`)
- [ ] 3 → 4

## Log
- 2026-09-05 — created; head identification, Chebyshev square-weight law, head variance law, and
  the Gaussian `E₁` identity in Lean; conjecture, consequences, falsifiers, open core recorded.

## 2026-09-05 (ii) — the head's fourth moment is Lean; the full Gaussian law is refuted numerically

**Theorem (Lean, `MollifiedDeviationHeadFourthMoment`, axiom-clean, wired).**
`exists_head_fourthMoment_close`: for every `ε > 0` there is `M₀` such that for `M ≥ M₀` and every
window with `8M²(1 + log M²) ≤ (ε/4)(T₂ − T₁)` — in particular `[T, 2T]` with `M = T^θ`, `θ < 1/2` —

```text
| (1/(T₂−T₁)) ∫_{T₁}^{T₂} |H_M(1/2+it)|⁴ dt − 1/2 | < ε,        1/2 = 2 · (1/2)² = E|CN(0,1/2)|⁴.
```

Route: `|H_M|⁴ = |H_M²|²` with `H_M²` the Dirichlet polynomial of the self-convolution (corpus
`dirPoly_mul_eq_dirPoly`); the Dirichlet mean value theorem on `[T₁,T₂]` reduces to the energy
`S₄(M) = ∑_r |(a∗a)_r|²`; the fibre expansion writes `S₄ = ∑_{k₁k₂ = l₁l₂} a a a a`; unique
factorization (`primePow_quad_classification`: an orientation, or all four powers of one prime)
gives `S₄ = 2S₂² − ∑a_k⁴ + E` with `0 ≤ E ≤ ∑_p (∑_{p^e≤M} a_{p^e})⁴ ≤ 2²⁰ C/log⁴M`,
`∑ a_k⁴ ≤ 2¹² C/log⁴ M`, `C = ∑ n^{-3/2}` (`tendsto_headFourthEnergy`). With `S₂ → 1/2`
(head variance law) this is the first rigorous Gaussian-moment law for `ζΨ − 1`.

**Numerical test of the full law (runpod, `T = 10⁶`, `4·10⁵` random heights in `[T,2T]`,
Riemann–Siegel with the `C₀` term; linear mollifier of length `y = T^θ`).**

| θ | y | E|ζΨ|² (1+1/θ) | E|W|² | kurt E|W|⁴/(E|W|²)² | E log|ζΨ|² | E₁(1/E|W|²) | head E|H|², kurt | tail E|Tail|², kurt |
|---|---|---|---|---|---|---|---|---|
| 0.3 | 63 | 3.60 (4.33) | 2.60 | 2.55 | −0.002 | 0.729 | 0.444, 1.96 | 2.16, 2.10 |
| 0.4 | 251 | 3.02 (3.50) | 2.02 | 2.04 | −0.002 | 0.565 | 0.460, 1.98 | 1.56, 1.68 |
| 0.5 | 1000 | 2.64 (3.00) | 1.65 | 1.77 | −0.002 | 0.447 | 0.470, 1.99 | 1.18, 1.51 |

Also `E W ≈ 0`, `E W² ≈ 0`, `E H² ≈ 0`, `E[H·conj(Tail)] ≈ 0`, `E log|ζ|² ≈ −0.001`,
`E log|Ψ|² ≈ −0.001`, and the finite-`T` deficit of `E|ζΨ|²` against `1 + 1/θ` is `12–17%`
(`log T ≈ 14`).

**Verdict on the conjecture of §3.** The head is Gaussian (kurtosis `1.96–1.99`, variance `→ 1/2`,
circular), exactly as the Lean theorem says. The *full* deviation is **not** `CN(0,1/θ)`: its
kurtosis crosses `2` near `θ ≈ 0.4` (`2.55`, `2.04`, `1.77`) and, decisively, its logarithmic mean
is `E log|1 + W|² ≈ 0`, not `E₁(1/σ²) ≈ 0.45–0.73`. The Gaussian `E₁` prediction of §3 is
therefore refuted; the observed value `E log|ζΨ|² ≈ 0` is the **outer-function law**: by
Littlewood, `E log|ζΨ|² = (4π/T)∑_{ζΨ(ρ)=0, β>1/2}(β − 1/2) + o(1)`, so `E log|ζΨ|² → 0` is
equivalent to `(L)` for `ζ` *together with* vanishing right-zero mass for the mollifier `Ψ`. The
numerics say both hold at `T = 10⁶`: the mollified product is asymptotically outer.

**Corrected conjecture (MOLL-DEV′).** `W_M = H_M + Tail_M` with `H_M → CN(0, 1/2)` (proven to
fourth order), `Tail_M` non-Gaussian and orthogonal to `H_M` with variance `1/θ − 1/2`, and the
joint law constrained by the outer identity `E log|1 + H_M + Tail_M| → 0`. The `(L)` ceiling is
therefore not `½E₁(θ)` but `0`: proving the outer law for the mollified product would prove `(L)`.
The Jensen gap `log E|ζΨ|² − E log|ζΨ|² → log(1 + 1/θ)` is total.

## 2026-09-05 (iii) — `c₄(θ)` from the ratios recipe (paper + symbolic residues)

**Setup.** `P(x) = x` gives the Mellin representation
`Ψ(s) = (1/log y)·(1/2πi)∫_{(c)} y^w ζ(s+w)^{-1} dw/w²`, so
`|ζΨ|⁴ = ζ(s)²ζ(1−s)² Ψ(s)²Ψ(1−s)²` is a four-fold Mellin integral of the ratio
`ζ(s+α₁)ζ(s+α₂)ζ(1−s+β₁)ζ(1−s+β₂) / [ζ(s+w₁)ζ(s+w₂)ζ(1−s+w₃)ζ(1−s+w₄)]`, `α,β → 0`.
The CFZ ratios conjecture evaluates the `t`-average as the six-term sum over swaps
`S ⊆ {α}, U ⊆ {β}, |S| = |U|`:
`∑ (t/2π)^{−∑_S α − ∑_U β} · Y(α_S ↔ −β_U; γ = w₁,w₂; δ = w₃,w₄)`, with
`Y(α;β;γ;δ) = ∏ζ(1+α_k+β_l) ∏ζ(1+γ_q+δ_r) / [∏ζ(1+α_k+δ_r) ∏ζ(1+γ_q+β_l)]`.
At leading order in `L = log T` (`ζ(1+x) → 1/x`, arithmetic factor `→ 1`, shifts scaled by `L`,
`y^w → e^{θw}`, `T^{−x} → e^{−x}`) the moment is
`c₄(θ) = θ^{−4}·(2πi)^{−4}∮⁴ e^{θ(w₁+w₂+w₃+w₄)} R₀(w) ∏ dw_i/w_i²`, `R₀ = lim_{α,β→0}` of the six-term
sum (holomorphic), contours `Re w₁ > Re w₂ > Re w₃ > Re w₄ > 0`, closed to the left; the poles
are at `w_i = 0` and `w_i = −w_j` (opposite side).

**Validation (sympy, runpod, `scratchpad/moll/c4_recipe.py`).** `(K,L,Q,R) = (1,1,0,0)` gives `1`
(`∫|ζ|² ~ L`); `(2,2,0,0)` gives `1/12` (the fourth moment `L⁴/12` before the arithmetic factor
`1/ζ(2)`, i.e. `L⁴/(2π²)`); `(1,1,1,1)` gives `1 + 1/θ` (Levinson/Conrey) — reproduced by
`R = 1 + Lγδ/(γ+δ)` and the two residues `w₂ = 0, −w₁`, as in the hand computation.

**Result.** For `(2,2,2,2)` the residues (kept: `w₄ ∈ {0,−w₁,−w₂}`, `w₃ ∈ {0,−w₁,−w₂}`,
`w₂ = 0` — the pole at `w₂ = +w₁` lies to the right and, in any case, carries zero residue —
`w₁ = 0`) give

```text
c₄(θ) = 1 + 2/θ + 1/θ² = (1 + 1/θ)².
```

So at leading order the recipe's mollified fourth moment is the **square of the mollified second
moment**: `E|ζΨ|⁴ = (E|ζΨ|²)²`, i.e. `Var(|ζΨ|²) = 0` to leading order. Compared with the Gaussian
value `1 + 4/θ + 2/θ²` this is far smaller (`9` versus `17` at `θ = 1/2`), confirming the refutation
of `CN(0,1/θ)` for the full deviation, but the numerics at `T = 10⁶` (`E|ζΨ|⁴/(E|ζΨ|²)² ≈ 2.05` at
`θ = 1/2`) are far *above* `1`. Either the leading-order recipe misses the true limit of the
mollified fourth moment (cancellation among the leading terms promoting lower-order pieces — the
same phenomenon that makes `E log|ζΨ|²` invisible to mean values), or the approach to the limit is
extremely slow. This is being tested by the `T`-scaling run (§(iv)).
