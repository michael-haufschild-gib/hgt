# Matomäki–Teräväinen all-interval `E₃` — Lean programme

- **ID:** `MT-E3-ALL-INTERVALS-LEAN-001`
- **Stage:** 1-in-progress
- **Type:** FORMALISATION PROGRAMME (shared input card)
- **Serves:** `../2-fully-proven/route-e-forbidden-support-e3-stability.md` (its `(FS4)`) and
  `../2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md` (its `(6)`)
- **RH used:** no
- **Computation used:** no

## Why this card exists

Both Route E `E₃` cards quote one external theorem and nothing else:

> **Matomäki–Teräväinen, "Almost primes in almost all short intervals II", Theorem 1.2.**
> For all large `x`, the interval `(x, x + √x(log x)^{1.55}]` contains `E₃` numbers.

Everything the two cards *prove* is already Lean (see their "Lean progress" sections, and the
`(FS7)`/`(7)`/`(9)` closures of 2026-08-18).  This card holds the formalisation of the quoted
theorem, so that the two cards have a single named dependency.

**The paper's text was retrieved and read** (arXiv:2207.05038, 26 pp.).  What follows is taken from
it, not reconstructed; the earlier guesswork recorded on the stability card — in particular an
alleged `log log x` deficit and an alleged constant-factor no-go — was based on a *different*
construction and does not apply.  Read this card, not that analysis, before working the lane.

## The actual construction (paper §7)

`a = 1.1`, `c = 1 + a/2 = 1.55`, `h = √x(log x)^c`, `P₁ = (log x)^a`.  The count is over
`p₁p₂n ∈ (x, x+h]` with

- `p₁ ∼ P₁` — a **short prime** variable;
- `p₂ ∼ √(x/P₁)/2` — a **long prime** variable;
- `n` weighted by **Harman's minorant `ρ⁻`**, the same one as in the paper's Theorem 2.1 but with
  `√(xP₁)` in place of `X` and `z = (xP₁)^{1/11}`, supported on `(√(x/P₁)/2, 4√(x/P₁)]`.

So the third factor is *not* a third prime variable: it is a sieve minorant that detects primes from
below.  This is the point I had wrong.  Target:

```text
∑_{x < p₁p₂n ≤ x+h} ρ⁻(n)  ≫  h/((log P₁)(log x)²) .
```

## The reduction chain, exactly as in §7

1. **Window comparison** (a slight variant of the paper's Theorem 2.1(ii)): reduce to
   ```text
   (1/h)∑_{x<p₁p₂n≤x+h} ρ⁻(n) = (1/h₁)∑_{x<p₁p₂n≤x+h₁} ρ⁻(n) + o(1/((log P₁)(log x)²)),
   h₁ = x^{99/100}.
   ```
2. **Perron** (Montgomery–Vaughan Cor. 5.3; the `[-T₀,T₀]` part as in Harman's book, Lemma 7.2),
   with `T₀ = x^{1/1000}`, reduces to
   ```text
   (1/h)∫_{T₀}^{x(log x)^{10}} |P₁(1+it)||P₂(1+it)||P(1+it)|·min(x/|t|, h) dt ≪ (log x)^{-2-ε/2}.
   ```
3. **Dyadic split** of `(x/h, x(log x)^{10}]` into `≪ log log x` pieces; it suffices that for every
   `T ∈ [x/h, x(log x)^{10}]`
   ```text
   (7.1)   ∫_{T₀}^{T}|P₁||P₂||P| dt ≪ (T/(x/h))·(log x)^{-2-ε}.
   ```
4. **The long prime variable is handled by the improved mean value theorem** (paper Lemma 3.3):
   for `T ≥ x/h`,
   ```text
   ∫_{T₀}^{T}|P₂(1+it)|²dt ≪ T/(√(x/P₁) log x) + (log x)^{-2} ≪ (T/(x/h))·(log x)^{-2},
   ```
   the last step being an *identity* of exponents because `h = √(xP₁)·log x`.
   **This is the card `(FS7)`, and it is already an unconditional corpus theorem**
   (`Sieve/DyadicPrimeMeanSquare.integral_normSq_dyadicPrimePoly_le`, proved through the
   shifted-pair Selberg sieve `Sieve/PrimePair*`).
5. **Cauchy–Schwarz** on `(7.1)`, pairing `|P₁P|` against `|P₂|`, reduces everything to
   ```text
   (5.2)   ∫_{T₀}^{T}|P₁(1+it)|²|P(1+it)|²dt ≪ (T/(x/h))·(log x)^{-2-2ε} ,
   ```
   which is proved in the paper's §5 (with `X` replaced by `√(xP₁)`).

So `(5.2)` is the single remaining core, exactly as the stability card says — but the second factor
is the **minorant polynomial `P`**, not a prime polynomial, and the prime polynomial `P₂` is the one
`(FS7)` disposes of.

## What §5 needs, and what the corpus already owns

| paper input | content | corpus status |
|-|-|-|
| Lemma 3.1 | reduction of the variance to `(5.2)` | to build (elementary, Perron bookkeeping) |
| Lemma 3.2 | mean value theorem `∫_{-T}^{T}|A|² = (2T+O(N))∑|a_n|²` | **owned** (`Sieve/DirichletMVT`, `Sieve/GallagherAlmostDiagonal`) |
| **Lemma 3.3** | improved MVT: `∫_{-T}^{T}|A(it)|²dt ≪ T∑|a_n|² + T∑_{0<|k|≤N/T}∑_n|a_n||a_{n+k}|` | **essentially owned** — this is exactly the shape `(FS7)` was proved with; needs stating in general form |
| Lemma 3.4 | Heath-Brown's *sparse* mean value estimate (from Heath-Brown, *Differences between consecutive smooth numbers*, Thm 4) | **not owned** — hard |
| Lemma 3.5 | (i) Watt's bound, (ii) Deshouillers–Iwaniec power mean values | **not owned** — these rest on Kuznetsov/automorphic input |
| Prop 2.2 | decomposition of `ρ⁻·1_{(Y/2,4Y]}` into `(log X)^{O(1)}` Type I/II pieces | to build (Harman sieve combinatorics) |
| §5.1–§5.3 | the three cases | to build |
| §7 | the assembly above | to build |

## The strategic choice: §6.1, not §5

The paper's §6.1 gives the **same theorems by Heath-Brown's identity instead of Harman's sieve**, at
the cost of a slightly larger exponent: `c = 2 + 3/13 + ε` for Theorem 1.1, hence
`a = 1 + 3/13` and `c = 1 + a/2 = 1.5 + 3/26 ≈ 1.615` for the all-interval `E₃` statement.  It
replaces Watt and Deshouillers–Iwaniec by **Bourgain's zero-density/large-values estimate**
([2, Lemma 4.60]) — hard, but purely analytic, with no automorphic input.

**For the two Route E cards the exponent `1.55` is not load-bearing.**  They use it only inside the
displacement `(1)`/`(FS14)` `0 < q − u ≪ U^{1/2+η}(log U)^{1.55}`, and their Route E consequence
depends only on `θ = 1/2 + η`; any fixed power of `log U` gives the same `θ`.  So the programme
should target the **§6.1 route**, i.e.

```text
Theorem 1.2′ (target).  For all large x, (x, x + √x(log x)^{1.615}] contains E₃ numbers,
```

and the two cards get retuned from `1.55` to `1.615` when it lands.  This removes Kuznetsov from the
dependency graph.  §6.1 needs: Heath-Brown's identity (**owned**,
`Sieve/HeathBrownIdentity.heathBrown_monomial_identity_of_lt_pow` and its compressed form), the
Type I treatment of §5.1, and a variant of Lemma 4.1 in the range `T^{1-ε/5} ≥ N ≥ T^{2/3}`,
`5ε ≤ σ ≤ 7/32 − 10ε`, from Bourgain's estimate.

The corpus's 163-module `Sieve/Maynard*` layer is built on Heath-Brown's identity and already
carries Huxley/Heath-Brown grouped large values, dyadic boxes, Perron packets and large-value
selection.  **Audit that layer against §6.1's requirements before building anything new.**

### M4 audit — what the large-values layer already gives, and what Lemma 4.1 needs (2026-08-18)

The paper's §4 is short and its only external input is **Jutila's large values estimate**
([10, Theorem 9.10]) applied with `k = 7`:

```text
Lemma 4.1 ("density hypothesis" for Dirichlet polynomials).  a_n divisor-bounded,
   T^{1-ε/10} ≥ N ≥ T^{9/11-10ε},  5ε ≤ σ ≤ 49/206 − 5ε   ⟹
   |{t ∈ [−T,T] : |N(1+it)| > N^{-σ}}| ≪ T^{2σ−ε²/5} .
```

and §6.1 needs the same statement in the range `T^{1-ε/5} ≥ N ≥ T^{2/3}`, `5ε ≤ σ ≤ 7/32 − 10ε`,
from Bourgain's zero-density estimate.  **No automorphic input appears anywhere in §4 or §6.1.**

Corpus inventory for Jutila:

| ingredient | corpus status |
|-|-|
| Halász–Montgomery / Montgomery large-values count `R·V² ≤ (T + N log N)(1/δ + log N)·G` | **owned** — `Sieve/MaynardMontgomeryFiniteSet.montgomery_heathBrown_grouped_large_values_finset` |
| Huxley's local large-values estimate, single and multi-block | **owned** — `Sieve/HuxleyLargeValues.huxley_multiblock_large_values` |
| the `k`-th power of a Dirichlet polynomial and its coefficient energy, **with a general support and a general fibre bound** | **owned** — `Sieve/PrimePowerSupport.sum_normSq_convPow_le_of_support` (the prime-support case is the specialisation `sum_normSq_convPow_le_of_prime_support`) |
| the fibre bound for *divisor-bounded* coefficients, i.e. `d_k(m) ≪_ε m^ε` | **was missing — now landed**, see below |

So Jutila's estimate is *assemblable* from corpus parts: apply the Montgomery count to `N(s)^k`,
whose length is `N^k` and whose coefficient energy is controlled by the general fibre lemma with the
divisor bound supplying the fibre cardinality.  That is milestone **M4a**.

### The divisor bound — `Sieve/DivisorBound` (2026-08-18)

Absent from mathlib, and the atom Jutila needs.

```text
card_divisors_le_rpow (hε : 0 < ε) (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ≤ divisorBoundConst ε * (n : ℝ) ^ ε ,
divisorBoundConst ε = (1 + 1/(ε log 2)) ^ #(primesBelow (⌈2^{1/ε}⌉ + 1)) .
```

The constant is explicit, not an `∃`.  Mechanism: `d(n)/n^ε = ∏_{p ∣ n}(a_p+1)/p^{a_p ε}`; above the
threshold `2^{1/ε}` each factor is `≤ 1` because `p^{aε} ≥ 2^a ≥ a+1` (`local_factor_le_one`), below
it each factor is `≤ 1 + 1/(ε log 2)` because `2^{aε} ≥ 1 + aε log 2` (`local_factor_le_small`).
Axiom-clean, wired.

### M4a landed — `Sieve/PowerFibreDivisorBound` (2026-08-18)

The prime-support fibre bound `ℓ^ℓ` of `Sieve/PrimePowerSupport` has no analogue for
divisor-bounded coefficients; the unrestricted fibre is the set of ordered `ℓ`-factorisations of the
anchored product, so it injects into the `ℓ`-fold product of the divisor set:

```text
powFibreOn_univ_card_le_divisors : #(powFibreOn N ℓ univ j) ≤ (d(j+1))^ℓ
powFibreOn_univ_card_le_rpow     : #(powFibreOn N ℓ univ j) ≤ (C_ε · (N^ℓ)^ε)^ℓ
sum_normSq_convPow_le_divisorBounded :
    ∑_j ‖convPow N ℓ a j‖² ≤ (C_ε (N^ℓ)^ε)^ℓ · (∑_n ‖a n‖²)^ℓ
volume_largeValues_pow_symm_le_divisorBounded :
    V^{2ℓ}·|{t ∈ [−T,T] : V ≤ ‖dirPoly N a t‖}|
        ≤ 2(T + 4N^ℓ(1+log N^ℓ))·(C_ε (N^ℓ)^ε)^ℓ·(∑_n‖a n‖²)^ℓ
volume_largeValues_le_divisorBounded : the same, solved for the measure.
```

**This is Matomäki–Teräväinen's Lemma 4.1 in measure form**, with the only arithmetic input being
the divisor bound.  Five theorems, axiom-clean, wired.  The general convolution-power energy lemma
`Sieve/PrimePowerSupport.sum_normSq_convPow_le_of_support` did all the analytic work; what was
missing was purely the fibre count, and only for the unrestricted support.

**Remaining for Lemma 4.1 as the paper states it:** Jutila's estimate is the *minimum* of this
moment bound and Montgomery's `GN/V²`; combining the two and checking the parameter arithmetic in
`T^{1-ε/10} ≥ N ≥ T^{9/11-10ε}`, `5ε ≤ σ ≤ 49/206−5ε` is **M4b**.

### The exponent is a free parameter — Remark 5.2 (2026-08-18)

The paper's Remark 5.2 states the dependence explicitly: **if Proposition 4.2 holds with any `σ` in
place of `49/206` and any `θ` in place of `2/11`, subject only to**

```text
1/5 + 2ε ≤ σ ≤ 1/2 ,        c = 1 + 1/(1 − θ(1 − 2σ) − ε) ,
```

then Theorem 2.1 holds with that `c` (and `a ∈ [c−1−ε², c−1]`).  Since `θ ≤ 1/2` and `1−2σ ≤ 1`,
`c ∈ [2,3]` always.  **For the two Route E cards any finite `c` is as good as `2.1`**, because the
all-interval exponent `1 + a/2` enters them only through a polylogarithmic factor in the
displacement.  So the lane does not need Jutila's sharp `σ = 49/206`; it needs *some* unconditional
Proposition 4.2 with `σ > 1/5`.

**But `σ > 1/5` is a real threshold, and neither corpus tool alone reaches it.**  With
`G = ∑_{n∼N}|a_n|²/n² ≍ (log N)^{O(1)}/N` and `V = N^{-σ}`, in the range `N ≥ T^{2/3}`:

| tool | gives | needs |
|-|-|-|
| Montgomery (`ℓ = 1`) | `T·N^{2σ−1}`, worst at `N = T^{2/3}`: `T^{(1+4σ)/3}` | `σ ≥ 1/2` |
| pure `ℓ`-th moment (`Sieve/PowerFibreDivisorBound`) | `N^{2σℓ+ℓ²ε}`, and `N^{2σℓ} ≥ T^{4σ(1−ε/5)}` for `ℓ ≥ 2` | `ℓ = 1` |

So the two endpoints fail and Jutila's *interpolation* between them is exactly what is required.

### All of Jutila's ingredients are corpus-owned

| Jutila ingredient | corpus status |
|-|-|
| Halász–Montgomery / Schur duality | **owned** — `Sieve/AlmostOrthogonality.sum_norm_inner_sq_le_of_schur`, `Sieve/LargeSieveDuality` |
| `k`-th power energy with general support + fibre bound | **owned** — `Sieve/PrimePowerSupport.sum_normSq_convPow_le_of_support` |
| divisor bound `d(n) ≪_ε n^ε` for the fibre count | **owned** — `Sieve/DivisorBound` (landed here) |
| Kuzmin–Landau and second-derivative bounds for the Gram entries `∑_{n∼N}n^{iτ}` | **owned** — `Sieve/HuxleyLargeValues`, `Sieve/MaynardKuzminLandauFactor.norm_LSeries_zetaDyadicBlock_le_over_height` |
| **the fourth moment of `ζ` on the critical line** | **owned** — `RHTower.exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog`, packaged as `Sieve/SmoothAFEZetaSquareInghamCriticalMomentPolylog.exists_inghamCriticalZetaFourthMoment_dyadic_le_polylog`: `∫_{Icc N (2N)}‖ζ(1/2+it)‖⁴dt ≤ C·N(1+log N)⁴` |

The last atom — the passage from the Gram entry to zeta — is now **landed** as
`Sieve/CriticalTruncationZeta` (2026-08-18).  It needed no approximate functional equation: PNT+
already carries the sharp Euler–Maclaurin representation `Zeta0EqZeta` together with the integral
bound `ZetaBnd_aux1`, and specialising them to `s = 1/2 + it` gives

```text
norm_sum_range_criticalPt_le (hN : 1 ≤ N) (ht : 2 ≤ |t|) :
  ‖∑_{n ≤ N} n^{-1/2-it}‖ ≤ ‖ζ(1/2+it)‖ + N^{1/2}/|t| + N^{-1/2}/2 + 4|t|·N^{-1/2} .
```

Every term but `‖ζ‖` is elementary, so partial summation turns the Gram entry `∑_{n∼N}n^{iτ}` into
`N^{1/2}‖ζ(1/2+iτ)‖` plus elementary error, which the fourth moment then averages.  Axiom-clean,
wired.

**Revised M4b:** Jutila's estimate = Halász–Montgomery on the `k`-th power, with the off-diagonal
Gram entries paid by the fourth moment of `ζ` through Cauchy–Schwarz, and the fibre count paid by
the divisor bound.  Every input above is unconditional and in the tree.

### The two endpoints of Jutila, in count form — `Sieve/JutilaLargeValues` (2026-08-18)

```text
card_largeValues_pow_div_le_divisorBounded (hε : 0 < ε) (N k) (hNk : 2 ≤ N^k) (a) … :
  R + 1 ≤ (T + 4N^k(1+log N^k))·(1/δ + 2 log N^k)
            · ((C_ε (N^k)^ε)^k · (∑_m‖a m‖²)^k) / V^{2k}
```

for every `k`, obtained by applying the corpus's Montgomery count
(`Sieve/DirichletLargeValuesL1.card_largeValues_div_le`) to the `k`-fold convolution
`convPow N k a` — length `N^k`, energy paid by the divisor bound through
`Sieve/PowerFibreDivisorBound`.  At `k = 1` this *is* the Montgomery endpoint, so the single
statement carries both ends of Jutila's interpolation with `k` free.  Axiom-clean, wired.

**What remains of M4b is exactly the interpolation**: the middle term of Jutila's estimate, obtained
by paying the off-diagonal Gram entries with the fourth moment of `ζ` through
`Sieve/CriticalTruncationZeta` rather than by the trivial diagonal.  Both of its inputs are now
corpus theorems.

## Milestones

- [x] **M1** Lemma 3.3 in general form (improved MVT) — **landed**, `Sieve/ImprovedMeanValue`.
- [ ] **M2** Lemma 3.1: the Perron/variance reduction to `(5.2)`, with explicit constants.
- [~] **M3** §7 assembly: **steps 3+5 landed** (`Sieve/MixedMomentAssembly`); step 1–2 (window comparison + Perron) open.
- [x] **M4** Audit done (below).  Jutila is assemblable from corpus parts; the missing atom was the divisor bound, now **landed**.
- [ ] **M5** Prop 2.2 for the Λ-version of §6.1 (Heath-Brown identity + dyadic splitting).
- [ ] **M6** §6.1 Type I case.
- [x] **M4a** the adapted-moment (Jutila) level-set bound for divisor-bounded coefficients — **landed**, `Sieve/PowerFibreDivisorBound`.
- [ ] **M4b** Jutila's estimate: Halász–Montgomery on the `k`-th power + fourth moment of `ζ` + divisor bound.  Needs the exponential-sum/zeta passage.
- [ ] **M4c** Proposition 4.2 for *some* `σ > 1/5` (the sharp `49/206` is not needed).
- [ ] **M7** §6.1 Type II case (the Bourgain input).
- [ ] **M8** `(5.2)′` and the retuned Theorem 1.2′; retune both Route E cards `1.55 → 1.615`.

## Lean progress

### M1 landed — `Sieve/ImprovedMeanValue` (2026-08-18)

The paper's Lemma 3.3, in the corpus's Gallagher form and fully general:

```text
integral_Icc_normSq_logPoly_le_shift :
  ∫_{Icc (-W) W} ‖logPoly a s w‖² dw
    ≤ (5/(4δ)) · ( ∑_{n∈s}‖a n‖²
                 + ∑_{k=1}^{K} ∑_{n ∈ s, n+k ∈ s} (‖a n‖² + ‖a (n+k)‖²) )
```

for any support `s ⊆ [1, N]`, any `0 < δ ≤ 1` with `2πδW ≤ 1`, and any `K ≥ 3Nδ`.  Supporting
theorems: `sum_biUnion_le_of_nonneg'` (a nonnegative sum over a union of fibres, any value type),
**`sum_weighted_neighbour_le`** (the weighted companion of `sum_card_neighbour_le`: a symmetric
near-diagonal relation whose pairs differ by at most `K` has weighted pair count
`≤ ∑ w + ∑_{k≤K}∑_{n,n+k ∈ s}(w n + w (n+k))`, by splitting the pair set into diagonal and the two
shifted copies), and **`le_add_of_log_close_range`** (a multiplicative window of ratio `e^δ` on
`[1,N]` is an additive window of length `3Nδ`).

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]`.  Wired into the
`GaloisForLFunctions.RHTower` umbrella.

This is the general instrument behind `(FS7)`, which is now visibly its instance at
`s = {p : R < p ≤ 2R}`, `a_p = 1/p`.

### M3 steps 3+5 landed — `Sieve/MixedMomentAssembly` (2026-08-18)

Cauchy–Schwarz and the dyadic split were already corpus theorems
(`HTGeometry.IntervalMeanSquareMoment.integral_norm_mul_norm_mul_kernel_le`); what was missing was
the Perron kernel in a globally continuous form and the specialisation to a *linear* majorant for
the first factor — the shape `(5.2)` supplies, its right side `(T/(x/h))(log x)^{-2-2ε}` being
proportional to the height with no constant term.

```text
perronKernel x h t₀ t := min (x / max t t₀) h          -- continuous, = min(x/t,h) on [t₀,∞)

integral_mixed_moment_perron_le :
  (∀ U ≥ t₀, ∫_{Icc(-U)U}‖A‖² ≤ κ_A·U)  →  (∀ U ≥ t₀, ∫_{Icc(-U)U}‖B‖² ≤ Q_B + κ_B·U)  →
  ∫_{t₀}^{t₀·2^M} ‖A‖‖B‖·perronKernel x h t₀
      ≤ (x·√κ_A·√Q_B·√2/√t₀)(1−√2/2)^{-1} + 2x·√κ_A·√κ_B·M
```

Substituting the programme's parameters (`A = P₁P`, `B = P₂`, `C = x`, `t₀ = x/h`, `κ_A` from
`(5.2)`, `Q_B, κ_B` from `(FS7)`) the first term is `≍ h(log x)^{-3-ε}` and the second
`≍ h·M·(log x)^{-2-ε}`, so after dividing by `h` the whole moment is `≪ (log x)^{-2-ε/2}` exactly
when the dyadic block count is `M ≪ (log x)^{ε/2}` — which is the paper's `M ≍ log log x`.

`#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Wired.

### `(FS7)` put in the affine shape the assembly consumes — `Sieve/DyadicPrimeMeanSquareAffine` (2026-08-18)

`Sieve/DyadicPrimeMeanSquare` carries a free smoothing parameter `δ`; the assembly needs
`Q + κ·W`.  Eliminating `δ = 1/(2πW)` and `K = ⌈6Rδ⌉` gives

```text
integral_normSq_dyadicPrimePoly_affine :
  ∫_{Icc(-W)W} ‖∑_{R<p≤2R} p^{-1+2πiw}‖² dw  ≤  fs7Const R h P₁ z  +  fs7Slope R h P₁ z · W ,
fs7Const  = 60e/E² + 15·Rem/R ,
fs7Slope  = (5π/2)(π(2R)−π(R))/R² + 20πe/(R E²) + 5π·Rem/R² ,     E = exp(mertensS h − mertensS P₁).
```

The shift range `K ≍ R/W` shrinks exactly as the height grows, which is why the prime pairs
contribute both a constant and a linear part rather than a term growing with `W`.  Axiom-clean,
wired.  This is the paper's step 4 in the shape its step 3 uses.

## Log

- 2026-08-18 — card opened.  Source located and read; construction corrected (the third factor is
  Harman's minorant, not a third prime); `(FS7)` confirmed to be exactly the paper's step 4;
  §6.1 selected as the Kuznetsov-free route; the exponent shown to be non-load-bearing for both
  Route E cards.
