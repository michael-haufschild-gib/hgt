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

### The Gram entry against `ζ` — `Sieve/AbelIncreasingWeight`, `Sieve/GramEntryZetaBound` (2026-08-18)

```text
norm_sum_mul_le_of_bounded_partial_mono :
  ‖∑_{i<n} (w i : ℂ)·g i‖ ≤ 2·B·w(n−1)      (w ≥ 0 nondecreasing, all prefixes of g ≤ B)

norm_sum_expSum_le_zeta (M) (ht : 2 ≤ |t|) :
  ‖∑_{n<M} n^{-it}‖ ≤ 2·(‖ζ(1/2+it)‖ + M^{1/2}/|t| + 1/2 + 4|t|)·(M−1)^{1/2}
```

The corpus's `Sieve/AbelInequality` had Dirichlet's test only for a *nonincreasing* weight; the
Gram entry needs the opposite monotonicity, since `n^{-it} = n^{1/2}·n^{-1/2-it}`.  Summing by
parts against the increasing `n^{1/2}` reduces the entry to the critical-line prefixes, which
`Sieve/CriticalTruncationZeta` compares with `ζ`.  Supporting: `criticalPrefixBound`,
`norm_sum_range_criticalPt_prefix_le` (uniform over all prefixes, with the `n = 0` and `n = 1`
degeneracies handled through `0^s = 0`), `weighted_criticalPt_eq`.  Axiom-clean, wired.

**This is the analytic heart of Jutila's interpolation**: every term but `‖ζ‖` is elementary, and
`‖ζ‖` is exactly what the corpus's fourth moment averages.

### The discrete-to-integral transfer, generalised — `Sieve/GallagherSumGeneral` (2026-08-18)

```text
sum_abs_le_gallagher_general (hδ : 0 < δ) (hderiv : ∀ x, HasDerivAt f (f' x) x) (hcont' : Continuous f')
    (hgap : ∀ i, lam i + δ ≤ lam (i+1)) (hA : A ≤ lam 0 − δ/2) (R) :
  ∑_{r ≤ R} |f(λ_r)| ≤ δ^{-1}∫_A^{λ_R+δ/2}|f| + ∫_A^{λ_R+δ/2}|f'|
```

`Sieve/GallagherSum` had this only for an exponential sum; the averaging step of Jutila needs it for
`‖ζ(1/2+i·)‖`-type functions.  Both ingredients were already corpus theorems — the pointwise Sobolev
bound `Sieve/GallagherSobolev.gallagher_sobolev` and the window disjointness
`Sieve/WindowDisjointness.sum_window_le` — so only the composition was missing.  Axiom-clean, wired.

Applying it to `f = ‖ζ(1/2+i·)‖⁴` and integrating against
`exists_inghamCriticalZetaFourthMoment_dyadic_le_polylog` is the averaging step; the one input still
to be supplied there is a derivative bound for `‖ζ‖⁴` on the critical line.

**What remains of M4b is the averaging step**: the middle term of Jutila's estimate, obtained
by paying the off-diagonal Gram entries with the fourth moment of `ζ` through
`Sieve/CriticalTruncationZeta` rather than by the trivial diagonal. The zeta Gram bridge and general
Gallagher transfer are corpus theorems; derivative control for `‖ζ‖⁴` and the assembled averaging
estimate remain.

### Both Perron branches and the merged window integral (2026-08-18)

```text
norm_perron_kernel_le_div (hx : 0 < x) (hh : 0 < h) (ht : t ≠ 0) :
  ‖((x+h)^{1+it} − x^{1+it})/(1+it)‖ ≤ 2(x+h)/|t|
norm_perron_kernel_le_length (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
  ‖((x+h)^{1+it} − x^{1+it})/(1+it)‖ ≤ h
perronPrefixIntegral_sub :
  prefixIntegral(B) - prefixIntegral(A) = integral(perronPoly * windowKernel(A,B))
```

`Sieve/PerronKernelBound` proves the decay branch, the integral-representation length branch, and
their `min` combination. `Sieve/PerronWindowKernel` merges the two prefix integrals from
`PerronShortInterval` into one integral against the window kernel. Full variance reduction and the
paper's short/long-window comparison still remain. Axiom-clean, wired.

## Milestones

- [x] **M1** Lemma 3.3 in general form (improved MVT) — **landed**, `Sieve/ImprovedMeanValue`.
- [ ] **M2** Lemma 3.1: the Perron/variance reduction to `(5.2)`, with explicit constants.
- [~] **M3** §7 assembly: **steps 3+5 landed** (`Sieve/MixedMomentAssembly`); both Perron kernel branches and the merged-window integral landed (`Sieve/PerronKernelBound`, `Sieve/PerronWindowKernel`); the full window comparison remains.
- [x] **M4** Audit done (below).  Jutila is assemblable from corpus parts; the missing atom was the divisor bound, now **landed**.
- [ ] **M5** Prop 2.2 for the Λ-version of §6.1 (Heath-Brown identity + dyadic splitting).
- [ ] **M6** §6.1 Type I case.
- [x] **M4a** the adapted-moment (Jutila) level-set bound for divisor-bounded coefficients — **landed**, `Sieve/PowerFibreDivisorBound`.
- [~] **M4b** Jutila's estimate: exponential-sum/zeta Gram passage and general Gallagher transfer landed; derivative control and fourth-moment averaging assembly remain.
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

## MAJOR REDIRECTION — Jutila and Bourgain are both removable (2026-08-18)

**Everything above about needing Jutila's `[10, Theorem 9.10]` (or, on the §6.1 route, Bourgain's
zero-density estimate) is superseded.  Huxley's large-values theorem alone suffices.**

### What the paper actually uses

The paper's proof of Lemma 4.1 is three lines; its content is Jutila's estimate at `k = 7`,

```text
|T| ≪ (NT)^{ε²/500} ( GN/V²  +  (GN/V²)^{-1/k}·G³NT/V⁶  +  (GN/V²)^{4k}·T/N^{2k} ) ,
       G = ∑_{n∼N}|a_n|²/n² ,  V = N^{-σ} .
```

With `G = N^{-1+o(1)}`, `V = N^{-σ}` the three terms are `N^{2σ}`, `T N^{(6−2/k)σ−2}`,
`T N^{(8σ−2)k}`, matching the paper's display exactly (this is how the transcription above was
verified).  Jutila's **middle term has base `G³NT/V⁶`, which is precisely Huxley's second term**;
the factor `(GN/V²)^{-1/k}` is Jutila's refinement of it.  Setting the base against the target
`T^{2σ−ε²/5}` with `N ≥ T^{1−θ}`:

```text
1 + (1−θ)(6σ−2) ≤ 2σ   ⟺   σ ≤ (2θ−1)/(6θ−4) .
```

At the Harman-route value `θ = 2/11` this is **`σ ≤ 7/32 = 0.21875`**, and Jutila's extra factor
buys only `49/206 = 0.23786`.  **Remark 5.2 needs merely `σ > 1/5 + 2ε`.**  So Huxley alone clears
the threshold with room to spare, and the whole `k = 7` apparatus is unnecessary.

### The cost, computed exactly

Re-running §5.3 with `7/32` in place of `49/206`:

| constraint | with `σ = 49/206` | with `σ = 7/32` |
|-|-|-|
| second bound `a > 6/(5+2σ)` | `103/94 = 1.0957` | `32/29 = 1.10345` |
| first bound `a > 1/(1 − θ(1−2σ))`, `θ = 2/11` | `1/(1 − 108/1133) = 1.1053` | `88/79 = 1.11392` |
| binding value of `a` | `1.1` | `88/79 ≈ 1.11392` |
| `c = 1 + a` | `2.1` | `≈ 2.114` |
| **all-interval `E₃` exponent `1 + a/2`** | **`1.55`** | **`≈ 1.557`** |

So the two Route E cards retune `1.55 → 1.557`, not `1.55 → 1.615`.  **The §6.1 (Heath-Brown
identity + Bourgain) detour is abandoned**: it was adopted only to avoid Jutila's dependency chain,
and Jutila is no longer in the chain.  §6.1 does not even avoid Watt/Deshouillers–Iwaniec, because
its Type I sums are "handled as before", i.e. by §5.1.

### Huxley's theorem, and why the corpus was one lemma away

Huxley's estimate in Kerr's normalisation (arXiv:1909.12075, Lemma 15, attributed to Huxley,
*Large values of Dirichlet polynomials III*):

```text
|a_n| ≤ 1,  A ⊂ [0,T] well spaced,  |∑_{N≤n≤2N} a_n n^{it}| ≥ V on A,  V ≥ N^{3/4+o(1)}
  ⟹  |A| ≪ N^{2+o(1)}/V² + T·N^{4+o(1)}/V⁶ .
```

Its proof is **exactly the corpus's local Huxley theorem plus a subdivision**:

1. `Sieve/HuxleyLargeValues.huxley_local_large_values` gives, on a window of diameter `W`,
   `K V² ≤ 2G(N + (12πN/δ)(1+log K))` **provided `G·B(N,U,W) ≤ V²/2`**, where
   `B ≤ 214√W + 1536 N/√U` and `3U ≤ 4πN`.
2. Taking `U = 4πN/3` makes `N/√U = √(3N/4π)`, so the `U`-endpoint of the envelope is absorbable
   exactly when `G√N ≲ V²` — **this is Huxley's hypothesis `V ≥ N^{3/4}`** (with `G ≍ N`).
3. The `√W` endpoint is then absorbable for `W ≍ V⁴/G²`, and the number of windows is `Ttot/W`,
   producing `Ttot G³N/V⁶ + GN/V²` — Huxley's two terms.

The corpus already owned step 1 (Kuzmin–Landau kernel + second-derivative envelope, both
unconditional).  Only the subdivision was missing.

### Landed — `Sieve/HuxleySubdivision`, `Sieve/HuxleyClosedLargeValues` (2026-08-18)

```text
card_le_of_window_bound (hmono : Monotone lam) (hW : 0 < W)
    (hspread : ∀ r ≤ R, lam r − lam 0 ≤ Ttot)
    (hlocal : ∀ j m, j+m ≤ R → lam (j+m) − lam j ≤ W → (m+1 : ℝ) ≤ C) :
  (R+1 : ℝ) ≤ (⌊Ttot/W⌋₊ + 1)·C

huxley_global_large_values … (hlamW : logDyadicLambda N W ≤ 1)
    (hB : logDyadicSecondEnvelope N U W ≤ B) (habsorb : G·B ≤ V²/2) … :
  (R+1)·V² ≤ (⌊Ttot/W⌋₊ + 1)·(2G(N + (12πN/δ)·∑_{i≤R} 1/(i+1)))

huxley_large_values_closed (hthresh : G(1 + 1536√(3N/4π)) ≤ V²/3) … :
  (R+1)·V² ≤ (Ttot·(1284G)²/V⁴ + 1)·(2G(N + (12πN/δ)·∑_{i≤R} 1/(i+1)))
```

plus `norm_dyadicDirRow : ‖dyadicDirRow N t‖ = √N` and `sq_le_of_large_value : V² ≤ N·G` (the
Cauchy–Schwarz ceiling that makes the window automatically legal for the phase test, so no extra
hypothesis is needed).  The subdivision lemma is purely combinatorial — fibres of
`r ↦ ⌊(λ_r − λ_0)/W⌋` are index intervals of frequency spread `< W`, and there are `⌊Ttot/W⌋+1`
of them.  All five `#print axioms` clean; both modules wired into the `RHTower` umbrella.

`huxley_large_values_closed` **is Huxley's Lemma 15 with explicit constants**: dividing by `V²`,

```text
R + 1 ≤ 2G·N·(1 + 12π(1+log(R+1))/δ)·(1/V² + Ttot·(1284G)²/V⁶) ,
```

i.e. `R ≪ GN/V² + Ttot·G³N/V⁶` up to logarithms, with the threshold `G√N ≲ V²` as the only side
condition.  This is the single large-values input the whole `E₃` programme needs.

### Revised milestone list

- **M4b′** — Huxley's global estimate: **landed** (above).  Jutila's `k`-th power interpolation,
  the Gram/ζ bridge (`Sieve/CriticalTruncationZeta`, `Sieve/GramEntryZetaBound`), the fourth-moment
  averaging and `Sieve/JutilaLargeValues` are **no longer on the critical path**; they remain as
  unconditional corpus assets in case a sharper `σ` is ever wanted.
- **M4c** — Lemma 4.1 at `σ = 7/32 − 10ε`: plumbing from `huxley_large_values_closed`
  (measure→well-spaced-count, the `lam : ℕ → ℝ` global-gap interface, divisor-bounded coefficient
  energy) plus the exponent arithmetic.  This is now the next Lean target.
- The remaining genuinely hard external inputs are unchanged and unavoidable on either route:
  **Lemma 3.4** (Heath-Brown's sparse mean value estimate) and **Lemma 3.5** (Watt /
  Deshouillers–Iwaniec twisted fourth moments — the only place automorphic input enters), together
  with **Prop 2.2** (Harman's sieve decomposition).

### The Dirichlet-block interface — `Sieve/HuxleyFinsetLargeValues`,
### `Sieve/HuxleyDirichletLargeValues`, `Sieve/HuxleyExplicitLargeValues` (2026-08-18)

Three further modules turn the abstract count into the object Lemma 4.1 quantifies over.

```text
sepEnum S hcard delta           -- monotone enumeration of a finite set of reals, continued past
                                -- the last point by an arithmetic progression of step delta
sepEnum_of_le, sepEnum_mem, sepEnum_gap
huxley_large_values_finset      -- the count for a finite delta-separated `S : Finset ℝ`

blockCoeff N c sigma            -- the coefficient vector of the block, weighted by n^{-sigma}
blockPoly  N c sigma t = ∑_{N ≤ n < 2N} c n · n^{-sigma} · e^{-i t log n}
inner_dyadicDirRow_blockCoeff : ⟪dyadicDirRow N t, blockCoeff N c sigma⟫ = blockPoly N c sigma t
norm_blockCoeff_sq            : ‖blockCoeff N c sigma‖² = ∑_{N ≤ n < 2N} ‖c n‖²(n^{-sigma})²
norm_blockCoeff_one_sq_le     : ‖blockCoeff N c 1‖² ≤ D²/N       (for ‖c n‖ ≤ D)

huxley_block_large_values (hthresh : (D²/N)(1 + 1536√(3N/4π)) ≤ V²/3) … :
  |S|·V² ≤ (1648656·Ttot·D⁴/(N²V⁴) + 1)·(2D²(1 + 12π(1 + log|S|)/delta))

card_le_of_separated : |S| ≤ Ttot/delta + 1
huxley_block_large_values_explicit : the same with `log|S|` replaced by `log (Ttot/delta + 1)`
```

The last statement is **Lemma 4.1's engine, fully explicit**: dividing by `V²`, with `G = D²/N`,

```text
|S| ≤ 2D²·L·(1/V² + 1648656·Ttot·D⁴/(N²V⁶)) ,   L = 1 + 12π(1 + log(Ttot/delta + 1))/delta ,
```

which at `D = N^{o(1)}`, `delta = 1`, `Ttot = 2T`, `V = N^{-σ}` reads `N^{2σ} + T N^{6σ−2}` — the two
Huxley terms.  Ten new theorems, all `#print axioms` clean, all wired.

**What is left for Lemma 4.1 is exponent arithmetic only**, with no further analytic input:

1. threshold: `(D²/N)(1 + 1536√(3N/4π)) ≤ N^{-2σ}/3` holds once `2256 D² ≤ N^{1/2−2σ}`, and
   `1/2 − 2σ ≥ 1/16` for `σ ≤ 7/32`;
2. second term: `2D²N^{2σ}L ≤ T^{2σ}·T^{−2σε}·(…)`, using `N ≤ T^{1−ε}` and `σ ≥ 5ε`;
3. first term: `T·N^{6σ−2} ≤ T^{1+(9/11)(6σ−2)}` using `N ≥ T^{9/11}` and `6σ − 2 < 0`, and
   `1 + (9/11)(6σ−2) − 2σ = (32/11)(σ − 7/32)`, so at `σ ≤ 7/32 − 5ε` the exponent is
   `2σ − (160/11)ε`, leaving `≈ 14.5 ε` of room for `D⁶`, `L`, and the constants.

## Open question: can Watt / Deshouillers–Iwaniec be removed from §5.1–§5.2? (2026-08-18)

With Jutila and Bourgain gone, **Lemma 3.5 (Watt's and Deshouillers–Iwaniec's twisted fourth
moments) is the only remaining automorphic input** — and §6.1 does *not* avoid it, since its Type I
sums are "handled as before".  So this is now the decisive fork for the whole programme.

Where it is used (§5.1, Type I).  After Cauchy–Schwarz against the amplifier `M = P₁^k`,

```text
∫_U |M₁|²|M₂|² ≤ M^{ε/10}(∫_U |M₂|⁴|M|²)^{1/2}(∫_U |M₁|⁴)^{1/2} ,
```

with `M₂` the long coefficient-`1` variable (`M₂ ≍ X/(P₁M₁)`, so `M₂ ≍ X^{1/2}` at the extreme
`M₁ ≍ X^{1/2}`) and `M ≍ T^{1/10}` the `P₁`-smooth amplifier, whose sparsity
`|supp M| ≤ M^{1−1/a+o(1)}` gives `∑|b_m|² ≪ M^{1+1/a}` — this is the *only* source of saving in the
whole Type I estimate, and it is a saving of just `M^{−(1−1/a)/2} ≈ X^{−0.0045}`.

**The plain mean value theorem is not merely lossy here, it fails by a full power of the amplifier.**
Writing `∫_{−T}^{T}|M₂²M|² ≪ (T + M₂²M)·∑|c_ℓ|²` and `∑|c_ℓ|² ≈ M₂^{−2}M^{1/a−1}X^{o(1)}` gives

```text
MVT :  (T/M₂² + M)·M^{1/a−1}X^{o(1)} ,        DI :  (T/M₂²)·M^{1/a−1}X^{ε} ,
```

so the MVT carries the extra additive `M·M^{1/a−1} = M^{1/a}` — at `T = X`, `M₁ = 1` this turns the
final Type I bound from `P₁·M^{(1/a−1)/2}` into `X^{1/2}M^{1/(2a)}`.  The reason is structural: at
`T ≍ X` and length `M₂² ≍ X` the diagonal is the whole MVT, and only reflection (functional
equation) beats it.  Shrinking `M` does not help — the loss term dominates for every `M > T/M₂²`,
and `T/M₂² ≍ 1` at the extreme `M₁ ≍ X^{1/2}`.

Two escapes to test, in order of promise:

1. **Restrict the Type I range and pay the sieve.**  For `T ≤ M₂` the pointwise bound (3.2),
   `|∑_{N<n≤N′}n^{−1−it}| ≪ 1/|t|`, already gives `∫_T^{2T}|M₁|²|M₂|² ≪ X^{o(1)}/T ≤ X^{−1/1000}` —
   no moment estimate at all.  The hard range is only `T > M₂ ≍ X/(P₁M₁)`.  Since the two Route E
   cards accept **any** fixed exponent, a Type I range much smaller than `M₁ ≤ X^{1/2+ε}` is
   affordable; the cost is that Harman's sieve then leaves more Type II, i.e. a larger `θ` in
   Remark 5.2, i.e. a larger `c`.  Quantifying that trade is the concrete next question.
2. **Use Lemma 3.4 in place of Lemma 3.5.**  The paper itself notes (Remark 5.3) that Heath-Brown's
   sparse mean value estimate can substitute for Deshouillers–Iwaniec in a related place.  Lemma 3.4
   is stated for a *sparse* `M(s) = ∑_{m ∈ M}ε_m m^{−s}` against a dyadic `A(s)`, which is exactly
   the shape here (`M` = the `P₁`-smooth amplifier, `A` = `M₂²`).  Its third term is deletable when
   `N ≥ T^{2/3}` or `|M| ≤ T^{1/3}`, both satisfiable.  Heath-Brown's Theorem 4 rests on the double
   large sieve and the divisor switching — hard, but **not automorphic**.

Neither escape is settled; the analysis above of the MVT failure is, and it rules out the naive
route.

## M4c CLOSED — Lemma 4.1 is Lean-proved unconditionally (2026-08-18)

Two more modules complete the chain from Huxley's estimate to the paper's Lemma 4.1.

### `Sieve/HuxleyDensityBound`

```text
huxley_threshold_of_rpow (h : 2400·D² ≤ N^{1/2−2σ}) :
  (D²/N)(1 + 1536√(3N/4π)) ≤ (N^{−σ})²/3
```
— Huxley's `V ≥ N^{3/4+o(1)}` in the divisor-bounded normalisation.  Mechanism: `√(3/4π) ≤ 1/2`
(only `π > 3` is needed), so the envelope is `≤ 800√N`, and `(D²/N)·800√N = 800D²N^{−1/2}`.

```text
huxley_block_two_term :
  |S| ≤ (6594624·T·D⁶·N^{6σ−2} + 2·D²·N^{2σ})·(1 + 12π(1 + log(2T+1)))
```
— **Huxley's `T G³NV^{−6} + GNV^{−2}` with every constant explicit and no asymptotic notation**, for
a one-separated `S` inside a range of length `2T` on which the block reaches `N^{−σ}`.  The proof is
pure `rpow` bookkeeping against `A = N^{2σ}`: `V²A = 1`, `V⁴A² = 1`, `N^{6σ−2} = A³/N²`.

### `Sieve/HuxleyDensityHypothesis`, `Sieve/HuxleyDensityThreshold`

```text
lemma41_huxley (heps : 0 < ε) (hepss : ε ≤ 1/1000) (hT1 : 1 ≤ T)
    (hE : 6594624 ≤ T^{ε²}) (hL : 1 + 12π(1+log(2T+1)) ≤ T^{ε²})
    (hD1 : 1 ≤ D) (hD6 : D⁶ ≤ T^{ε²})
    (hNlo : T^{9/11} ≤ N) (hNhi : N ≤ T^{1−ε})
    (hsl : 5ε ≤ σ) (hsh : σ ≤ 7/32 − 5ε)
    (hthr : 2400 D² ≤ N^{1/2−2σ}) … :
  |S| ≤ T^{2σ − ε²/5}

exists_lemma41_largeness : ∃ T₀ ≥ 1, ∀ T ≥ T₀, the three largeness hypotheses hold
exists_lemma41_huxley    : the same statement with `hE`, `hL`, `hD6` discharged
```

The exponent arithmetic is exactly as predicted:

* `N^{6σ−2} ≤ T^{(9/11)(6σ−2)}` (antitone `rpow` in the base, `6σ−2 ≤ 0`), so the first term is
  `≤ T^{3ε² + 1 + (9/11)(6σ−2)}`, and
  `2σ − ε²/5 − (3ε² + 1 + (9/11)(6σ−2)) = (7 − 32σ)/11 − 3.2ε² ≥ 160ε/11 − 3.2ε² ≥ ε²`;
* `N^{2σ} ≤ T^{(1−ε)2σ}`, so the second term is `≤ 2T^{2ε² + (1−ε)2σ}`, and
  `2σ − ε²/5 − (2ε² + (1−ε)2σ) = 2σε − 2.2ε² ≥ 7.8ε² ≥ ε²`;
* in both cases `T^{ε²} ≥ 6594624 ≥ 4` absorbs the factor `2` and the constants.

`exists_lemma41_largeness` builds the threshold explicitly: with `z = ε²/2` and
`C = 6594624 + D⁶ + 1 + 12π + 12π·3^z/z`, take `T₀ = max 1 (C^{1/z})`; then `T^z ≥ C` and
`log(2T+1) ≤ 3^z T^z/z` (mathlib's `Real.log_le_rpow_div`) give all three.

**Six theorems, all `#print axioms` clean, all wired.  Milestone M4c is closed** — with `σ = 7/32`
in place of the paper's `49/206`, which Remark 5.2 permits.

### Milestones after this session

- [x] **M4** audit; **M4a** adapted-moment level set; **M4b′** Huxley's global estimate;
      **M4c** Lemma 4.1 at `σ = 7/32 − 5ε`.
- [ ] **M4d** *(new)* Proposition 4.2 (Type II estimate): the `T₁/T₂/T₃` partition, the discrete
      mean value theorem for `M_j(1+it)^{ℓ_j}`, and Halász–Montgomery on `T₁`.  All three
      ingredients are corpus-owned; this is assembly.
- [ ] **M2** Lemma 3.1 (Perron/variance reduction).
- [ ] **M3** §7 assembly (window comparison remains).
- [ ] **M5** Prop 2.2 (Harman's sieve decomposition).
- [ ] **M6/M7** Type I and Type I/II — **blocked on the Watt/Deshouillers–Iwaniec fork above**.
- [ ] **M8** Theorem 1.2′ at exponent `≈ 1.557`; retune both Route E cards.

### Deduplication (2026-08-18)

`Sieve/SeparatedCount` already owned the counting core `card_le_of_separated` (a cell-index
injection, more general than the ordering argument: any finite family in an interval of length `L`
with pairwise separation `g` has at most `L/g + 1` members).  The version first written here was a
name collision in `RHTower.Sieve` that would have broken the umbrella; it is now
`card_le_of_pairwise_spread`, a three-line wrapper anchoring the corpus lemma at `S.min'`.
A collision scan over all twenty-three new declarations found no other clash.

## The general-range Huxley estimate — `Sieve/HuxleyRangeLargeValues` (2026-08-18)

Proposition 4.2 applies Lemma 4.1 to `M₁(1+it)^ℓ`, whose support is `[M₁^ℓ, (2M₁)^ℓ)` — a range of
multiplicative width `2^ℓ`, not a dyadic block.  The corpus's Huxley layer is dyadic-only
(`dyadicDirRow`), so the estimate has to be extended.  The extension is a pigeonhole, not new
analysis:

```text
rangeTerm c σ t n                 -- one term of a Dirichlet polynomial on the line σ
sum_blockPoly_eq_range :
  ∑_{j<J} blockPoly (A·2^j) c σ t = ∑_{n ∈ [A, A·2^J)} rangeTerm c σ t n
exists_block_large (hJ : 1 ≤ J) :
  V ≤ ‖∑_{n ∈ [A, A·2^J)} rangeTerm c σ t n‖ → ∃ j < J, V/J ≤ ‖blockPoly (A·2^j) c σ t‖
huxley_range_large_values :
  |S|·(V/J)² ≤ ∑_{j<J} (the dyadic bound at length A·2^j, threshold V/J)
huxley_range_large_values_uniform :
  |S|·(V/J)² ≤ J·(the dyadic bound at length A, threshold V/J)
```

The whole cost of a range of width `2^J` is therefore a factor `J` in the count and `J²` in the
threshold — negligible against the `T^{ε²/5}` slack whenever `J ≪ 1`, which is exactly the regime
Proposition 4.2 uses (`ℓ ≪ 1` there).  The last statement holds because every block bound is largest
at the shortest block, so the sum is at most `J` copies of the bound at length `A`.

Five theorems, all `#print axioms` clean, wired.

### Next: M4d, Proposition 4.2

Ingredients and their status:

| Prop 4.2 step | tool | status |
|-|-|-|
| reduce to a one-spaced `T ⊆ U` | — | elementary |
| `T₃` (both polynomials `< T^{-1}`) | trivial bound | elementary |
| `T₁` (either polynomial `≥ M_j^{-10ε}`) | discrete mean value theorem for `M_j^{ℓ_j}` | **owned** — `Sieve/DirichletFiniteSetLargeValues.largeValues_dirPoly_finset` is Ivić's Theorem 9.4 |
| `T₁` second half | Halász–Montgomery | **owned** — `Sieve/HalaszMontgomeryDyadic`, `Sieve/HuxleyLargeValues` |
| `T₂` dyadic `(σ₁,σ₂)` partition | Lemma 4.1 | **owned** — `exists_lemma41_huxley`, and now its range form |

The one interface still to build is the bridge from `blockPoly`/`rangeTerm` to the corpus's
`dirPoly` (indices `Fin N`, phase `+it`), which `largeValues_dirPoly_finset` is stated over:
`blockPoly N c σ t = dirPoly (2N−1) a (−t)` with `a n = c(n+1)·(n+1)^{−σ}` supported on
`[N, 2N)`.  Everything else is assembly.

## Prop 4.2's `T₂` case is ALREADY in the corpus (2026-08-18, 21:40)

Found with `scripts/formal_tools.py research` — **`Sieve/MatomakiTeravainenTypeIIAmplitudeCells`**
formalizes the amplitude-cell cancellation of Proposition 4.2's `T₂` case, abstractly and
unconditionally:

```text
matomakiTeravainen_typeII_covered_amplitude_cells_energy
    (hS : S ⊆ I.biUnion cells) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hT : T = M₁M₂) (hC : 0 ≤ C)
    (hcount : ∀ i ∈ I, #(cells i) ≤ C·T^{2 min (σ₁ i) (σ₂ i) − δ})
    (hF₁ : ∀ i ∈ I, ∀ q ∈ cells i, F₁ q ≤ 2M₁^{−σ₁ i})
    (hF₂ : ∀ i ∈ I, ∀ q ∈ cells i, F₂ q ≤ 2M₂^{−σ₂ i}) :
  ∑_{q ∈ S} F₁ q² F₂ q² ≤ #I · (16 C T^{−δ})
```

with `matomakiTeravainen_typeII_amplitude_cell_scale`, `…_cell_energy`,
`…_cells_energy_comparable`, `…_comparable_uniform` and the covered-set variants — ten declarations,
no disjointness of the cells required, so the `≪ (log T)²` cell count of the paper enters as `#I`.

**Its `hcount` hypothesis is exactly Lemma 4.1's conclusion**, which this session closed as
`Sieve/HuxleyDensityThreshold.exists_lemma41_huxley` (`|S| ≤ T^{2σ − ε²/5}`, i.e. `C = 1`,
`δ = ε²/5`).  So the two halves of Prop 4.2's `T₂` case are both in the tree and only need joining.

### The join, precisely

Instantiate the cell lemma at `α := ℝ` (ordinates), `F_j t := ‖blockPoly M_j c_j 1 t‖`, and `cells i`
the dyadic amplitude cells `T₂,σ₁,σ₂`.  For each cell:

* `hF₁`, `hF₂` hold by the definition of the cell;
* `hcount` comes from `exists_lemma41_huxley` applied to **whichever of the two polynomials realises
  `min(σ₁,σ₂)`** — the paper's case split.  For `σ₁ ≤ σ₂` it is applied to `M₁(1+it)^ℓ` with `ℓ`
  chosen so that `M₁^ℓ` lands in the admissible length window; that is a polynomial over a range of
  multiplicative width `2^ℓ`, which is exactly what
  `Sieve/HuxleyRangeLargeValues.huxley_range_large_values_uniform` was built for.  For `σ₂ < σ₁` it is
  applied to `M₂` directly, whose support is already dyadic.

So the remaining work in `T₂` is the case split plus the `ℓ`-selection arithmetic
(`M₁^ℓ ∈ [T^{5/6−ε}, T^{1−ε/2}]`, possible because `M₁ ≤ T^{2/11+ε}` and consecutive powers of `M₁`
cannot skip a window of multiplicative width `T^{1/6+ε/2}`).

### Revised milestone list for Theorem 1.2

- [x] **M4** Lemma 4.1 at `σ = 7/32 − 5ε` (`exists_lemma41_huxley`), and its general-range form.
- [~] **M4d** Prop 4.2: the `T₂` cell cancellation is **owned**
      (`MatomakiTeravainenTypeIIAmplitudeCells`); the `T₁` step has its discrete mean value theorem
      (`DirichletFiniteSetLargeValues.largeValues_dirPoly_finset`, Ivić Thm 9.4) and
      Halász–Montgomery; `T₃` is trivial.  **Remaining: the case split and the `ℓ`-selection.**
- [ ] **M2** Lemma 3.1 (Perron/variance reduction) — `Sieve/PerronShortInterval` and
      `Sieve/PerronWindowKernel` are the primitives.
- [ ] **M5** Prop 2.2 (Harman sieve decomposition).
- [ ] **M6/M7** Type I and Type I/II — the Watt/Deshouillers–Iwaniec fork.
- [ ] **M8** Theorem 1.2′ at exponent `≈ 1.557`; retune both Route E cards.

Nothing in the `T₂` half needs a new analytic estimate.

## The `T₂` join: every piece is now named (2026-08-18, 22:00)

### Landed — `Sieve/PowerWindowSelect`

```text
exists_pow_mem_window (hM : 1 < M) (hA : 1 < A) (hAB : A * M ≤ B) :
  ∃ ℓ, 1 ≤ ℓ ∧ A ≤ M ^ ℓ ∧ M ^ ℓ ≤ B
```

This is the `ℓ`-selection of Proposition 4.2 — `M₁^ℓ ∈ [T^{5/6−ε}, T^{1−ε/2}]` — and it is exactly the
statement that consecutive powers cannot skip a window whose multiplicative width is at least the
base.  Proof: take the least `ℓ` with `A ≤ M^ℓ`; then `M^{ℓ−1} < A`, so `M^ℓ < A·M ≤ B`.  The
hypothesis `A·M ≤ B` is the paper's `M₁ ≤ T^{1/6+ε/2}` in disguise; at `M₁ ≤ T^{2/11+ε}` it needs the
window `[T^{5/6−ε}, T^{1−ε/2}]`, whose width `T^{1/6+ε/2}` **does** exceed `T^{2/11+ε}` only when
`1/6 > 2/11`, which is false — so at the Harman value the paper's own window is used with the
*sharper* `M₁ ≤ T^{2/11+ε/2}` bound, and the check is `2/11 + ε ≤ 1/6 + ε/2`… **this inequality is
false (`2/11 = 0.1818 > 1/6 = 0.1667`)**, which is why the paper writes `1 ≤ ℓ ≪ 1` rather than
claiming a single window: for `M₁` in the top part of its range one takes `ℓ = 1` and the polynomial
`M₁` itself, and the window is entered by *choosing which of `M₁`, `M₁²` to use*.  The selection lemma
above is the tool for that once the sub-window is fixed; the case analysis over `M₁`'s range is the
remaining arithmetic.

### The power of a block is a Dirichlet polynomial — already owned

`Sieve/PrimePowerSupport.dirPoly_convPow`:

```text
dirPoly (N ^ ℓ) (convPow N ℓ a) t = (dirPoly N a t) ^ ℓ
```

So `M₁(1+it)^ℓ` **is** a Dirichlet polynomial with the convolution-power coefficients, and if `a` is
supported on the dyadic block `(M₁, 2M₁]` then `convPow` is supported on `(M₁^ℓ, (2M₁)^ℓ]` — a range of
multiplicative width `2^ℓ`, which is precisely the shape
`Sieve/HuxleyRangeLargeValues.huxley_range_large_values_uniform` handles.

### The one bridge still to build

`dirPoly N a t = ∑_{n : Fin N} a n·exp(i t log(n+1))` is indexed by `1..N` with phase `+it`, while
`blockPoly N c σ t = ∑_{n ∈ [N,2N)} c n·n^{−σ}·exp(−i t log n)` is `Ico`-indexed with phase `−it` and
carries the `n^{−σ}` weight explicitly.  The bridge is

```text
blockPoly N c σ t = dirPoly (2N−1) a (−t) ,   a n = c (n+1)·(n+1)^{−σ}·1_{[N,2N)}(n+1)
```

which lets `dirPoly_convPow` produce the `ℓ`-th power and `huxley_range_large_values_uniform` bound
its large values.  **That bridge plus the `M₁`-range case analysis is the whole of the `T₂` join**;
`Sieve/MatomakiTeravainenTypeIIAmplitudeCells` then closes the case, and `T₁`/`T₃` are the discrete
mean value theorem and the trivial bound.
