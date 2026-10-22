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
- [x] **M4d** Prop 4.2, finite one-spaced form (brick 25) and **integral form** (brick 28,
      `exists_matomakiTeravainen_typeII_proposition42_integral`), at Huxley strength.
- [x] **M2** Lemma 3.1's pointwise comparison (bricks 26, 29, 30, 31) — assembled in
      `norm_realWindowSum_compare_le`, with the mixed-moment integral as its only analytic input.
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

## M2 groundwork: the two-window comparison kernel — `Sieve/PerronCompareKernel` (2026-08-18, 22:20)

Lemma 3.1 and the §7 window comparison both integrate the *difference* of two Perron kernels, the
short window against the long one renormalised.  Nothing in the corpus owned that object (searched:
`MaynardMultiscaleReferenceTelescope.routeTNormalizedWidthPerronIntegral_sub_eq_kernelDefect` is a
different, one-width defect), so it is now defined with its two branches:

```text
perronCompareKernel x h h₁ t
  := ((x+h)^{1+it} − x^{1+it})/(1+it) − (h/h₁)·((x+h₁)^{1+it} − x^{1+it})/(1+it)

norm_perronCompareKernel_le_length : ‖·‖ ≤ 2h
norm_perronCompareKernel_le_div (hle : h ≤ h₁) (ht : t ≠ 0) : ‖·‖ ≤ 4(x+h₁)/|t|
norm_perronCompareKernel_le_min : ‖·‖ ≤ min (2h) (4(x+h₁)/|t|)
```

Both branches come from `Sieve/PerronKernelBound`'s two bounds by the triangle inequality, the long
branch using `h/h₁ ≤ 1`.  Three theorems, axiom-clean, wired.

**What this does and does not give.**  It is the crude pair of bounds — enough to run the dyadic
assembly of `Sieve/MixedMomentAssembly` on the *comparison* integral rather than on a single window,
which is what Lemma 3.1 needs.  It does **not** yet capture the first-order cancellation
`‖·‖ ≪ min(h, x/|t|)·min(1, h₁|t|/x)` that makes only the top of the `t`-range contribute; that
sharper bound is the next step, and it is a Taylor-with-remainder estimate on `u ↦ u^{1+it}`.

### Concurrency note

`Sieve/MatomakiTeravainenTypeIIAmplitudeCells` (19:43) and
`Sieve/MatomakiTeravainenTypeIISparseHalaszMontgomery` (19:47, containing
`halaszMontgomery_blockPoly_finset_explicit` and `matomakiTeravainen_typeII_T1_sparse_energy`) are
being written by **another session, building Prop 4.2's `T₁` and `T₂` on top of this session's
`blockPoly`**.  To avoid collision this session has moved to the Perron/variance side (M2) and left
the Type-II join to that lane.  Whoever resumes should check
`grep -c matomakiTeravainen` before touching Prop 4.2.

## `Sieve/PerronKernelIntegralForm`, and the sharp comparison bound's proof plan (2026-08-18, 22:40)

```text
perron_kernel_eq_intervalIntegral (x h t : ℝ) :
  ((x+h)^{1+it} − x^{1+it})/(1+it) = ∫_x^{x+h} u^{it} du
```

extracted from the inline `integral_cpow` step of `norm_perron_kernel_le_length`, with no positivity
hypotheses needed (`integral_cpow` at `r.re = 0` covers the whole interval).  Axiom-clean, wired.

### The sharp comparison bound, and why it needs one more brick

The first-order cancellation the window comparison needs is

```text
‖perronCompareKernel x h h₁ t‖ ≤ |t|·h·h₁ / x .
```

Its proof is the observation that **the comparison kernel annihilates every constant**: for any `c`,

```text
∫_x^{x+h}(u^{it} − c) du − (h/h₁)∫_x^{x+h₁}(u^{it} − c) du
  = K(x,h,t) − c·h − (h/h₁)K(x,h₁,t) + (h/h₁)·c·h₁
  = perronCompareKernel x h h₁ t ,
```

because `(h/h₁)·h₁ = h`.  Taking `c = x^{it}` and using `‖u^{it} − x^{it}‖ ≤ |t|(u−x)/x` for `u ≥ x`
gives `‖·‖ ≤ |t|h²/(2x) + |t|hh₁/(2x) ≤ |t|hh₁/x` when `h ≤ h₁`.

Two bricks are needed for this and neither is in the corpus (searched):

1. **`intervalIntegrable` for `u ↦ u^{it}` on `[x, x+H]`**, so that `intervalIntegral.integral_sub`
   can split off the constant.  A first attempt at this from `Complex.continuousAt_ofReal_cpow_const`
   did not go through and was discarded rather than left as a `sorry`.
2. **The Lipschitz estimate `‖u^{it} − x^{it}‖ ≤ |t|(u−x)/x` for `0 < x ≤ u`** — a mean-value bound on
   `u ↦ u^{it}`, whose derivative has modulus `|t|/u ≤ |t|/x`.

With those two, the sharp bound and hence `‖·‖ ≤ h·min(2, |t|h₁/x)` follow, and the `t`-integral of
the comparison is concentrated on `|t| ≳ x/h₁` — which is exactly what makes Lemma 3.1's right-hand
side `(log X)^{-2-ε}` rather than `O(1)`.

## `Sieve/CpowMulILipschitz` — the Lipschitz brick for the sharp comparison bound (2026-08-18, 23:00)

```text
norm_cpow_mul_I_sub_le (hx : 0 < x) (hu : x ≤ u) :
  ‖u^{it} − x^{it}‖ ≤ |t|(u − x)/x
```

Chord below arc, then `log(u/x) ≤ (u−x)/x`.  Built by reusing
`HTGeometry.HalfPlaneMellinRepresentation.cpow_ofReal_mul_I` for the `cpow → exp` passage and
mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le` for the chord.  Axiom-clean, wired.  **Build cost
219 s** — the `HTGeometry` import chain is heavy; a lighter route would inline the three-line
`cpow_def_of_ne_zero`/`ofReal_log` unfolding instead.

Three near-duplications were avoided here by searching first:
`QuantumAlg.Util.Complex.norm_exp_ofReal_mul_I_sub_one_le` (one-point chord),
`HTGeometry.TorsionPolygonRecurrenceShadowing.norm_exp_ofReal_mul_I_sub_le` (two-point chord, too
heavy to import), and `HTGeometry.HalfPlaneMellinRepresentation.cpow_ofReal_mul_I`.  A from-scratch
FTC proof of the chord bound had already been written and checked before the search found these; it
was discarded.

### What is left for the sharp comparison bound

Only **interval-integrability of `u ↦ u^{it}` on `[x, x+H]` for `0 < x`**, so that
`intervalIntegral.integral_sub` can split off the constant in

```text
∫_x^{x+h}(u^{it} − c)du − (h/h₁)∫_x^{x+h₁}(u^{it} − c)du = perronCompareKernel x h h₁ t ,
```

the identity holding for every `c` because `(h/h₁)·h₁ = h`.  With `c = x^{it}` and
`norm_cpow_mul_I_sub_le` this yields

```text
‖perronCompareKernel x h h₁ t‖ ≤ |t|h²/(2x) + |t|hh₁/(2x) ≤ |t|·h·h₁/x    (h ≤ h₁),
```

hence `‖·‖ ≤ h·min(2, |t|h₁/x)`, which concentrates Lemma 3.1's `t`-integral on `|t| ≳ x/h₁`.
Integrability follows from continuity of `u ↦ u^{it}` on `(0,∞)` via `cpow_ofReal_mul_I` and
`Complex.continuous_exp`; it is the single remaining step of this brick.

## The sharp comparison bound is CLOSED — `Sieve/PerronCompareSharp` (2026-08-18, 23:20)

```text
intervalIntegrable_cpow_mul_I (hx : 0 < x) (hH : 0 ≤ H) :
  IntervalIntegrable (fun u => u^{it}) volume x (x+H)

perron_kernel_sub_const (hx : 0 < x) (hH : 0 ≤ H) :
  ((x+H)^{1+it} − x^{1+it})/(1+it) = ∫_x^{x+H}(u^{it} − x^{it}) du + x^{it}·H

norm_perronCompareKernel_le_sharp (hx : 0 < x) (hh : 0 < h) (hh₁ : 0 < h₁) (hle : h ≤ h₁) :
  ‖perronCompareKernel x h h₁ t‖ ≤ 2·|t|·h·h₁ / x
```

The mechanism is the constant annihilation: `perron_kernel_sub_const` writes each kernel as
"variation + `x^{it}`·length", and the renormalisation `(h/h₁)·h₁ = h` makes the two `x^{it}` terms
cancel exactly.  What survives is the variation of `u^{it}` across each window, bounded by
`Sieve/CpowMulILipschitz.norm_cpow_mul_I_sub_le`.  Integrability comes from
`Complex.continuousAt_ofReal_cpow_const` at `Or.inr (u ≠ 0)` — the `Or.inl` branch is `0 < (t·I).re`,
which is false here, and that mis-step cost one build cycle.

Combined with `norm_perronCompareKernel_le_length` this gives

```text
‖perronCompareKernel x h h₁ t‖ ≤ min (2h) (2|t|hh₁/x) ,
```

so the comparison integral is concentrated on `|t| ≳ x/h₁`: below that height the two windows agree
to first order and cancel.  **This is the analytic heart of Lemma 3.1 and of §7's window comparison,
and it is now unconditional.**

### What M2 (Lemma 3.1) still needs

Only the bookkeeping: Perron with the comparison kernel (`Sieve/PerronWindowKernel.perronPrefixIntegral_sub`
merges the two prefix integrals), then the dyadic split of `Sieve/MixedMomentAssembly` run on the
`min(2h, 2|t|hh₁/x)` weight instead of `min(x/t, h)`.  No further analytic input.

## `Sieve/PerronCompareLowFreq` — the transition height is explicit (2026-08-18, 23:35)

```text
norm_perronCompareKernel_le_min3 (hle : h ≤ h₁) (ht : t ≠ 0) :
  ‖perronCompareKernel x h h₁ t‖ ≤ min (min (2h) (2|t|hh₁/x)) (4(x+h₁)/|t|)

norm_perronCompareKernel_le_of_low (hle : h ≤ h₁) (hlow : |t| ≤ δ·x/h₁) :
  ‖perronCompareKernel x h h₁ t‖ ≤ 2·h·δ
```

The second is the statement that **the window comparison sees nothing below height `x/h₁`**: taking
`δ` small makes the kernel uniformly `≤ 2hδ` there, so the whole `t`-integral of Lemma 3.1 is carried
by `|t| ≳ x/h₁`, where the third branch `4(x+h₁)/|t|` then supplies the decay.  Two theorems,
axiom-clean, wired.

### Lemma 3.1's remaining step, in one line

Feed the weight `min(min(2h, 2|t|hh₁/x), 4(x+h₁)/|t|)` into
`Sieve/MixedMomentAssembly.integral_mixed_moment_perron_le` in place of `perronKernel`.  The
assembly's dyadic split is already written and its hypotheses are the two affine mean-square
majorants `(FS7)` supplies; only the weight changes, and the low-frequency branch removes the blocks
below `x/h₁` that the old `min(x/t, h)` weight had to pay for.

## `Sieve/MixedMomentWindowCompare` — Lemma 3.1's weight is now the comparison kernel (2026-08-18)

The substitution flagged as the last step of M2 is done. The new module defines

```
windowCompareKernel x h h₁ t₀ t = min (min (2h) (2|t|hh₁/x)) (4(x+h₁)/max |t| t₀)
```

— the three-branch majorant of `perronCompareKernel`, with the decaying branch's denominator floored
at `t₀` so the weight is globally continuous (`continuous_windowCompareKernel`). Four structural
facts and two moment bounds:

- `norm_perronCompareKernel_le_windowCompareKernel` — it majorizes the Perron window difference for
  `|t| ≥ t₀`, so it is a legitimate replacement for `perronKernel` in the assembly;
- `windowCompareKernel_le_div` — above `t₀` it decays like `4(x+h₁)/t`, which is exactly the
  hypothesis `G t ≤ C/t` of `HTGeometry.integral_norm_mul_norm_mul_kernel_le` at `C = 4(x+h₁)`;
- `windowCompareKernel_le_of_low` — below `δx/h₁` it never exceeds `2hδ`;
- `integral_lowRange_windowCompare_le`, `integral_dyadicRange_windowCompare_le`, and the total
  `integral_mixed_moment_windowCompare_le` over `[0, t₀2^M]`.

What changed mathematically. The single-window kernel `min(x/t, h)` equals `h` at `t = 0`, so the
low range had to be handled by subtracting the main term by hand. The comparison kernel vanishes
linearly at `t = 0` — the two windows' main terms cancel identically — so the low range is bounded
by `2hδ` times a Cauchy–Schwarz product of the two mean-square majorants at height `t₀`, with
`δ = t₀h₁/x`. No main-term subtraction appears anywhere in the chain. The dyadic range is unchanged
apart from the constant `x → 4(x+h₁)`.

M2 (Lemma 3.1) is closed as far as the analytic weight is concerned: every hypothesis of
`integral_mixed_moment_windowCompare_le` is one of the two affine mean-square majorants, and `(FS7)`
supplies both.

## M5 groundwork: Buchstab's identity and Harman's minorant are Lean-proved (2026-08-19)

The minorant `ρ⁻` of `(2.3)` — the object every later section refers to — is now a definition in the
tree, together with the three-fold Buchstab expansion that produces it and the elementary majorant
`(2.4)`.  Two modules, both axiom-clean (`[propext, Classical.choice, Quot.sound]`), both wired.

### `Sieve/BuchstabIdentity`

```text
rho (n z : ℕ) : ℕ := if 0 < n ∧ ∀ p ∈ n.primeFactors, z ≤ p then 1 else 0    -- 1_{(n,P(z))=1}

buchstab {n w z : ℕ} (hn : 0 < n) (hwz : w ≤ z) :
  rho n z + ∑ q ∈ (Ico w z).filter (fun q => q.Prime ∧ q ∣ n), rho (n / q) q = rho n w
```

This is `(1.2)`.  The proof is the three-case split on `rho n w` and `rho n z`; in the only
non-degenerate case the sum collapses to the single term `q = n.minFac`, because every other prime
`q ∣ n` in the window leaves `minFac n` behind in `n/q`.  Also `rho_le_one`, `rho_antitone`
(raising the sifting level can only remove integers) and `dvd_div_of_ne`.

### `Sieve/HarmanMinorant`

```text
primeWindow n a b   = (Ico a b).filter (fun q => q.Prime ∧ q ∣ n)
harmanPairs z E n q₁ = (primeWindow (n/q₁) z q₁).filter (fun q => q₁ * q^4 < E)

harmanS1 z Q n   = ∑_{q ∈ primeWindow n z Q} rho (n/q) z
harmanS2 z D E n = ∑_{q₁ ∈ primeWindow n z D} ∑_{q₂ ∈ harmanPairs z E n q₁} rho (n/q₁/q₂) z
harmanS3 z D E n = ∑_{q₁} ∑_{q₂} ∑_{q₃ ∈ primeWindow (n/q₁/q₂) z q₂} rho (n/q₁/q₂/q₃) z

rhoMinus z Q D E n : ℤ = rho n z − harmanS1 + harmanS2 − harmanS3
```

- **`rhoMinus_le_rho`** (`0 < n`, `z ≤ Q`, `D ≤ Q`): `rhoMinus z Q D E n ≤ rho n Q`.
- **`rho_eq_prime_indicator`** (`2 ≤ Q ≤ n < Q²`): `rho n Q = 1_{n prime}`.
- **`rhoMinus_le_primeIndicator`**: the two combined — `ρ⁻(n) ≤ 1_P(n)` on `[Q, Q²)`.
  At the paper's parameters `Q = 2X^{1/2}`, `D = X^{1/4−2ε}`, `E = X^{1−2ε}` the range `[2X^{1/2}, 3X]`
  sits inside `[Q, Q²) = [2X^{1/2}, 4X)`.

The proof is exactly the paper's: `harman_step_one` is Buchstab at `(z, Q)`; `harman_step_two`
expands each level-`q` term as `rho (n/q) z` minus a double sum; `harmanR2adm_le` discards the
inadmissible pairs (the second term of `(2.1)`); `harman_step_three` expands the admissible pairs;
and `harmanR3_le` — `rho_antitone` — discards the fourth Buchstab tail (the last term of `(2.2)`)
**without needing a fourth expansion**: raising the innermost level from `q₃` to `z` already
dominates it.  That is a genuine simplification of the paper's bookkeeping.

### The majorant `(2.4)`

```text
largePrimeCount n z = #(n.primeFactors.filter (z ≤ ·))

abs_rhoMinus_le (hn : 0 < n) : |rhoMinus z Q D E n| ≤ 1 + K + K² + K³,   K = largePrimeCount n z
pow_largePrimeCount_le (hn : 0 < n) : z ^ largePrimeCount n z ≤ n
```

Together these give `|ρ⁻(n)| ≤ 4(log n / log z)³` for `K ≥ 1`, which is `(2.4)` with the paper's
`log(3X)` replaced by the sharper `log n`.  `harmanS1_le`, `harmanS2_le`, `harmanS3_le` bound the
three corrections by `K`, `K²`, `K³` — each summand is at most one and the index sets inject into
the large prime factors of `n`, which only shrink under division.

### Milestone status

- [x] **M5a** the minorant itself: definition, `ρ⁻ ≤ 1_P`, and the majorant `(2.4)`.
- [ ] **M5b** Prop 2.2: the decomposition of `ρ⁻·1_{(Y/2,4Y]}` into Type I / Type I/II / Type II
      pieces (Lemma 2.3 plus the §2.2 bookkeeping).
- [ ] **M5c** Theorem 2.1(ii): the positive average, `∫` of the Buchstab function.

## M5b groundwork: Legendre, `(1+δ)`-adic blocks, and Lemma 2.3(i) (2026-08-19)

Three further modules, all axiom-clean and wired.

### `Sieve/BuchstabIdentity`, second half — Legendre's identity

```text
siftModulus z = ∏_{p ∈ primesBelow z} p                                  -- P(z)
rho_eq_one_iff_coprime (hn : 0 < n) : rho n z = 1 ↔ Nat.Coprime n (siftModulus z)
rho_eq_sum_divisors_moebius (hn : 0 < n) :
  (rho n z : ℤ) = ∑ e ∈ (gcd n (siftModulus z)).divisors, μ e
abs_rho_sub_truncated_moebius_le (hn : 0 < n) :
  |rho n z − ∑_{e ∣ gcd(n,P(z)), e ≤ D} μ e| ≤ #{e ∣ gcd(n,P(z)) : e > D}
```

The last is the term `c₁,n` of Lemma 2.3, bounded pointwise: cutting the Legendre expansion at `D`
costs at most one unit per discarded divisor.  This also connects the new `rho` to the corpus's
existing Brun layer (`Sieve/BrunPure`, `Sieve/TruncatedMoebius`), which truncates by `ω(e) ≤ r`
instead.

### `Sieve/AdicBlocks` — the `δ_A`-adic subdivision

```text
adicIndex δ z₀ q = ⌊log(q/z₀)/log(1+δ)⌋

adicIndex_block  (0<δ, 0<z₀, z₀≤q) : z₀(1+δ)^j ≤ q < z₀(1+δ)^{j+1},  j = adicIndex δ z₀ q
adicIndex_le_of_le                 : monotone in q
adicIndex_le_div (0<δ≤1, z₀≤z₁)    : adicIndex δ z₀ z₁ ≤ 2·log(z₁/z₀)/δ
sum_adic_blocks                    : ∑_{j<J} ∑_{q : adicIndex q = j} f q = ∑_q f q
adicIndex_mem_range                : every q ∈ [z₀,z₁] indexes below adicIndex δ z₀ z₁ + 1
```

`adicIndex_le_div` uses `log(1+δ) ≥ δ/(1+δ) ≥ δ/2`.  At the paper's `δ_A = (log X)^{-10A}` and
`z₁/z₀ ≤ X` this gives at most `2(log X)^{10A+1}` blocks, which is the counting behind Prop 2.2's
`O(exp((log log X)^5))` — `R ≤ log z/log z₀ ≍ (log log X)³` nested blocks raise it to
`exp(O((log log X)^4))`.

### `Sieve/MinorantDecomposition` — Lemma 2.3(i) as an exact identity

```text
truncLegendre k z D = ∑_{e ∣ gcd(k,P(z)), e ≤ D} μ e
truncTail    k z D  = #{e ∣ gcd(k,P(z)) : e > D}

rho_sub_rho_eq_sum (0<k, Q≤q) : rho k Q − rho k q = ∑_{p ∈ primeWindow k Q q} rho (k/p) p
rho_sub_rho_le_card           : ... ≤ #(primeWindow k Q q)

divisor_sum_rho_decomp (α : ℕ → ℤ) (0<n) (z₀ ≤ z₁) :
  | ∑_{m ∣ n} α_m ρ(n/m, z₁)
      − ( ∑_{m ∣ n} α_m·truncLegendre(n/m, z₀, D)
          − ∑_{m ∣ n} ∑_{q ∈ primeWindow (n/m) z₀ z₁} α_m ρ(n/m/q, q) ) |
    ≤ ∑_{m ∣ n} |α_m|·truncTail(n/m, z₀, D)
```

This is the displayed identity in the proof of Lemma 2.3, with `c₁,n` named and bounded.
`rho_sub_rho_eq_sum` is the exact cost of replacing the sieve level `q` by the bottom `Q` of its
`δ_A`-adic block — the term `c₂,n` — and it is nothing but Buchstab over the block, so no new
estimate is needed for it either.

### What M5b still needs

Only the **mean-square** bounds: `∑_{n ∼ Y} |c_{i,n}|² ≪_A Y/(log X)^{3A}` for the three error
terms.  Each is a divisor-type second moment over a sparse set (`c₁`: integers with a divisor
`> D` composed of primes `< z₀`; `c₂`: integers with a prime factor in a `δ_A`-short interval;
`c₃`: the boundary of the last block).  The algebra of Lemma 2.3 is finished.

### M5b, brick 1 — the Rankin atom for `c₁,n` (2026-08-19)

Added to `Sieve/MinorantDecomposition.lean`, axiom-clean:

```text
card_large_divisors_le_rankin (hα : 0 < α) (hD : 0 < D) :
  #{e ∣ m : e > D}  ≤  D^{-α} · ∑_{e ∣ m} e^α

truncTail_le_rankin (hα : 0 < α) (hD : 0 < D) :
  truncTail k z D  ≤  D^{-α} · ∑_{e ∣ gcd(k, P(z))} e^α
```

This is the standard Rankin trick — each divisor above `D` contributes at least `D^{-α}e^α ≥ 1` —
and it is the atom of the first of the three mean-square bounds M5b still needs.  With it, the
`c₁,n` estimate reduces to the Euler product

```text
   ∑_{n ∼ Y} (truncTail n z₀ D)²  ≤  D^{-2α}·∑_{n ∼ Y} (∑_{e ∣ gcd(n,P(z₀))} e^α)²
     ≤ D^{-2α}·Y·∑_{e₁,e₂ ∣ P(z₀)} (e₁e₂)^α / lcm(e₁,e₂) ,
```

which at `α = 1/log z₀` and `D = exp((log X)/(log log X))` is the paper's `Y/(log X)^{3A}`.  The
`lcm` pair sum is the same shape as `Sieve/JointTuranKubilius.sum_inv_lcmPair_le`, built this
session for the other lane.

Remaining for M5b: that Euler product, and the corresponding mean squares for `c₂,n` (integers with
a prime factor in a `δ_A`-short interval — the cost of replacing the sieve level `q` by the bottom
of its block, whose exact value is `Sieve/MinorantDecomposition.rho_sub_rho_eq_sum`) and `c₃,n`.

### M5b, brick 2 — the mean square of the divisor moment (2026-08-19)

`Sieve/DivisorMomentMeanSquare.lean`, axiom-clean, wired.

```text
divisors_gcd_eq (hn : 0 < n) (hP : 0 < P) :
  (gcd n P).divisors = P.divisors.filter (· ∣ n)

sum_sq_divisor_moment_le (hP : 0 < P) (α : ℝ) :
  ∑_{n ≤ Y} (∑_{e ∣ gcd(n,P)} e^α)²  ≤  Y · ∑_{e₁,e₂ ∣ P} (e₁e₂)^α / lcm(e₁,e₂)
```

Composed with brick 1 this reduces the `c₁,n` mean square of Lemma 2.3 to a **pure Euler product**:

```text
   ∑_{n ≤ Y} (truncTail n z₀ D)²  ≤  D^{-2α} · Y · ∑_{e₁,e₂ ∣ P(z₀)} (e₁e₂)^α / lcm(e₁,e₂) ,
```

with no arithmetic left — the remaining step is to evaluate the pair sum as
`∏_{p < z₀} (1 + 2p^{α−1} + p^{2α−1})` and choose `α = 1/log z₀`, `D = exp((log X)/(log log X))`.

The proof is the same skeleton as `Sieve/JointTuranKubilius`: the square of a divisor sum is a pair
sum of indicator products, a product of two divisibility indicators is the indicator of the lcm, and
`sum_indicator_dvd_le` counts its multiples.  That lemma was built for the other lane and is reused
verbatim here — the two gates share machinery.

Remaining for M5b: the Euler-product evaluation above, and the mean squares of `c₂,n` (integers with
a prime factor in a `δ_A`-short interval; its exact value is
`Sieve/MinorantDecomposition.rho_sub_rho_eq_sum`) and `c₃,n`.

### M5b: what the `c₁,n` Euler product needs, exactly (2026-08-19)

The pair sum left by brick 2 is, for `P = P(z₀)` squarefree with prime support `S`,

```text
   ∑_{e₁,e₂ ∣ P} (e₁e₂)^α / lcm(e₁,e₂)  =  ∏_{p ∈ S} (1 + 2p^{α−1} + p^{2α−1}) ,
```

because each prime contributes `1`, `p^α/p`, `p^α/p` or `p^{2α}/p` according to whether it divides
neither, only `e₁`, only `e₂`, or both.

The **one-variable** squarefree divisor/powerset transfer is corpus-owned —
`Sieve/MainTerm.sum_divisors_eq_sum_powerset` ("summing any function over the divisors of a
squarefree number is summing over the subsets of its prime support") and
`Sieve/SquarefreeDivisorProduct.sum_divisors_prod_primes_eq_prod`.  What is missing is the
**two-variable** version: after applying the transfer twice one has `∑_{A ⊆ S}∑_{B ⊆ S}`, and
turning that into `∏_{p ∈ S}` needs the four-way distributivity (`p` in neither, `A` only, `B` only,
both), i.e. `Finset.prod_sum` with a four-element fibre — equivalently a bijection
`S → Fin 4  ≃  {(A,B) : A, B ⊆ S}`.

A crude substitute does **not** work: bounding `1/lcm(e₁,e₂) ≤ 1/√(e₁e₂)` replaces the off-diagonal
`(e₁e₂)^{α−1}` by `(e₁e₂)^{α−1/2}`, and `∏_{p<z₀}(1 + p^{α−1/2})` is of size
`exp(c·z₀^{1/2}/log z₀)` — the whole saving is lost.  The diagonal is fine either way; it is the
off-diagonal that forces the exact product.

### CORRECTION: the two-variable Euler product is avoidable (2026-08-19)

The entry above says the `c₁,n` pair sum needs a **two-variable** powerset factorization.  It does
not.  Using `1/lcm(e₁,e₂) = gcd(e₁,e₂)/(e₁e₂)` and Gauss's identity
`gcd(e₁,e₂) = ∑_{d ∣ e₁, d ∣ e₂} φ(d)` (mathlib: `Nat.sum_totient`),

```text
   ∑_{e₁,e₂ ∣ P} (e₁e₂)^α/lcm(e₁,e₂)
     = ∑_{e₁,e₂ ∣ P} (e₁e₂)^{α−1}·gcd(e₁,e₂)
     = ∑_{d ∣ P} φ(d) · ( ∑_{e ∣ P, d ∣ e} e^{α−1} )²
     ≤ ( ∑_{e ∣ P} e^{α−1} )² · ∑_{d ∣ P} φ(d)·d^{2α−2} ,
```

the last step because for squarefree `P` the inner sum is `d^{α−1}∑_{f ∣ P/d} f^{α−1}` and every
term is positive, so it is at most `d^{α−1}·∑_{f ∣ P} f^{α−1}`.

Both remaining sums are **one-variable** Euler products, which
`Sieve/SquarefreeDivisorProduct.sum_divisors_prod_primes_eq_prod` already evaluates:

```text
   ∑_{e ∣ P} e^{α−1} = ∏_{p < z₀}(1 + p^{α−1}) ,
   ∑_{d ∣ P} φ(d)d^{2α−2} = ∏_{p < z₀}(1 + (p−1)p^{2α−2}) .
```

### The numbers, and why the route closes

At `α = 1/log z₀` one has `p^α ≤ e` for `p < z₀`, so `p^{α−1} ≤ e/p` and

```text
   ∏_{p<z₀}(1 + p^{α−1}) ≪ (log z₀)^e ,      ∏_{p<z₀}(1 + (p−1)p^{2α−2}) ≪ (log z₀)^{e²} ,
```

both polylogarithmic.  With `z₀ = exp((log X)/(log log X)³)` and `D = exp((log X)/(log log X))`,

```text
   D^{-2α} = exp(−2·(log X/log log X)·(log log X)³/log X) = exp(−2(log log X)²) ,
```

which beats every power of `log X`.  So `∑_{n ∼ Y}|c₁,n|² ≪ Y·exp(−2(log log X)²)·(log z₀)^{O(1)}`,
comfortably inside the required `Y/(log X)^{3A}` — the paper's `(2.9)` slack is enormous here.

**What to build**: the three displayed reductions (Gauss's identity, the `d ∣ e` reindexing for
squarefree `P`, and the positivity step), then the two Euler products from the corpus lemma, then
the numeric comparison.  No two-variable combinatorics.

### M5b, brick 3 — the pair term in gcd form (2026-08-19)

Added to `Sieve/DivisorMomentMeanSquare.lean`, axiom-clean:

```text
pair_term_eq (h₁ : 0 < e₁) (h₂ : 0 < e₂) (α : ℝ) :
  (e₁^α · e₂^α) / lcm(e₁,e₂)  =  (e₁·e₂)^{α−1} · gcd(e₁,e₂)
```

the first of the three reductions of the entry above.  `gcd·lcm = e₁e₂` turns the `lcm` denominator
into a `gcd` numerator, and `Real.rpow_sub` absorbs the extra `e₁e₂`.  Gauss's identity
`∑_{d ∣ n} φ(d) = n` (`Nat.sum_totient`) then expands the `gcd`, after which the pair sum splits as

```text
   ∑_{d ∣ P} φ(d) · ( ∑_{e ∣ P, d ∣ e} e^{α−1} )² ,
```

and the remaining two steps — the `d ∣ e` reindexing for squarefree `P` and the positivity
comparison — leave only one-variable Euler products.

### M5b, brick 4 — Gauss's identity applied to the pair sum (2026-08-19)

`Sieve/DivisorMomentMeanSquare.lean`, axiom-clean:

```text
divisors_gcd_pair_eq       (gcd e₁ e₂).divisors = P.divisors.filter (d ∣ e₁ ∧ d ∣ e₂)
gcd_eq_sum_totient_filter  gcd e₁ e₂ = ∑_{d ∣ P} [d ∣ e₁][d ∣ e₂]·φ(d)
sum_pair_gcd_eq            ∑_{e₁,e₂ ∣ P} (e₁e₂)^{α−1}·gcd(e₁,e₂)
                             = ∑_{d ∣ P} φ(d)·(∑_{e ∣ P, d ∣ e} e^{α−1})²
```

The second of the three reductions.  With brick 3 (`pair_term_eq`) the whole pair sum of the `c₁,n`
mean square is now the **single-variable** expression on the right; only the `d ∣ e` reindexing
`{e ∣ P : d ∣ e} ↔ {d·f : f ∣ P/d}` for squarefree `P` and the positivity comparison remain before
the two corpus Euler products.

The proof is Gauss's `∑_{d ∣ n} φ(d) = n` (`Nat.sum_totient`) restricted to the divisors of `P`,
then two `Finset.sum_comm` swaps to bring `d` outside and `Finset.sum_mul_sum` to factor the two
inner sums.

### M5b, brick 5 — divisor pair reduced to Euler products (2026-08-27)

Added to `Sieve/DivisorMomentMeanSquare.lean`, axiom-clean:

```text
sum_filter_dvd_rpow_le:
  ∑_{e ∣ P, d ∣ e} e^β ≤ d^β · ∑_{f ∣ P} f^β

sum_divisors_rpow_eq_prod (Squarefree P):
  ∑_{d ∣ P} d^β = ∏_{p ∣ P} (1 + p^β)

sum_pair_gcd_le_eulerProducts (0 < P) (Squarefree P):
  ∑_{e₁,e₂ ∣ P} (e₁e₂)^{α−1} gcd(e₁,e₂)
    ≤ (∏_{p ∣ P} (1 + p^{α−1}))² · ∏_{p ∣ P} (1 + p^{2α−1})
```

This closes the exact quotient-reindexing and positivity comparison left by brick 4.  The first
bound uses the injection `e ↦ e/d` from divisors of `P` divisible by `d` into all divisors of `P`;
no squarefree assumption is needed.  Gauss's identity, `φ(d) ≤ d`, rpow positivity, and square
monotonicity then reduce the pair sum to two divisor power sums.  Squarefreeness evaluates those
sums with the existing corpus Euler-product theorem.

Direct Lean check and targeted module build passed.  New declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Remaining `c₁,n` work is the parameter-specific
Euler-product estimate and its insertion into the divisor mean-square bound; no pair-sum or
two-variable divisor combinatorics remain.

### M5b, brick 6 — explicit `c₁,n` mean square (2026-08-27)

Added two axiom-clean modules:

- `Sieve/DivisorMomentEulerBound.lean` proves `siftModulus_squarefree`, identifies its prime factors
  with the primes below `z`, and shows

  ```text
  sum_pair_gcd_siftModulus_invLog_le_logLog (2 ≤ z):
    ∑_{e₁,e₂ ∣ P(z)} (e₁e₂)^{1/log z−1} gcd(e₁,e₂)
      ≤ exp((2e + e²) · (log log z + mertensSecondUpperConst)).
  ```

- `Sieve/MinorantTruncTailMeanSquare.lean` rewrites this in the original lcm form, squares the
  pointwise Rankin bound, applies `sum_sq_divisor_moment_le`, and proves

  ```text
  sum_sq_truncTail_invLog_le_logLog (2 ≤ z) (0 < D):
    ∑_{1≤n≤Y} truncTail(n,z,D)²
      ≤ D^{−2/log z} · Y ·
          exp((2e + e²) · (log log z + mertensSecondUpperConst)).
  ```

Thus the `c₁,n` analytic estimate is dependency-closed through the exact Rankin parameter.  Only
the paper's external scale substitution
`z₀ = exp(log X/(log log X)³)`, `D = exp(log X/log log X)` and the resulting absorption into
`Y/(log X)^{3A}` remain for this term.  Both modules passed direct Lean checks, targeted module
builds, new-declaration axiom audits (`propext`, `Classical.choice`, `Quot.sound` only), umbrella
reachability, and formal lint.

### M5b, brick 7 — `c₂,n` prime-window mean square (2026-08-27)

Added `Sieve/PrimeWindowMeanSquare.lean`, axiom-clean and umbrella-wired.  It defines the prime set
of a half-open block and proves the exact identification

```text
primeWindow n a b = primeFactorsIn (primesIco a b) n.
```

The existing Turán second moment for designated prime factors then gives, with
`A(a,b) = ∑_{a≤p<b} 1/p`,

```text
sum_sq_card_primeWindow_le:
  ∑_{1≤n≤Y} #primeWindow(n,a,b)² ≤ Y·A(a,b) + Y·A(a,b)²

sum_sq_card_primeWindow_le_of_mass (A(a,b) ≤ η):
  ∑_{1≤n≤Y} #primeWindow(n,a,b)² ≤ Y·(η + η²).
```

This closes the `c₂,n` divisor-count combinatorics.  Remaining analytic step is a uniform
reciprocal-mass estimate for the paper's `(1+δ_A)`-adic blocks.  The corpus already contains
Mertens' second theorem with exponential error, strong enough because the block bottom is at least
`z₀ = exp(log X/(log log X)³)` while `δ_A = (log X)^{-10A}`.  Direct Lean, targeted build, and
new-declaration axiom audit passed.

### M5b, brick 8 — uniform Mertens mass for `c₂,n` blocks (2026-08-27)

Added `Sieve/PrimeWindowMertensMass.lean`, axiom-clean and umbrella-wired.  The endpoint identity

```text
primesIco a b = primesRange (a−1) (b−1)
```

allows direct use of the corpus's exponential-error Mertens theorem.  Unconditionally there are
fixed `B ≥ 0`, `c > 0`, and `N₀ ≥ 3` such that every `N₀ ≤ u ≤ v` satisfies

```text
∑_{u<p≤v} 1/p
  ≤ log log v − log log u + 2B exp(−c sqrt(log u)).
```

The module combines this with brick 7 and obtains the same bound for the full second moment of
`#primeWindow(n,a,b)`, with `η` equal to the displayed mass majorant:

```text
∑_{1≤n≤Y} #primeWindow(n,a,b)² ≤ Y(η + η²).
```

This is uniform across all sufficiently high blocks, so block count does not spend a separate
Mertens error.  Remaining `c₂,n` step is pure scale calculus: for
`b/a ≤ 1 + δ_A`, bound the log-log increment by `O(δ_A)` and absorb
`exp(−c sqrt(log z₀))` into the same logarithmic power.  Direct Lean, targeted build,
new-declaration axiom audit, umbrella reachability, and formal lint passed.

### M5b, brick 9 — linear `δ` bound on one adic block (2026-08-27)

Added `Sieve/PrimeWindowAdicMeanSquare.lean`, axiom-clean and umbrella-wired.  Elementary scale
calculus gives

```text
logLog_sub_le_delta_div_log
  (v ≤ (1+δ)u) : log log v − log log u ≤ δ / log u.
```

Combining this with brick 8 yields fixed `B ≥ 0`, `c > 0`, `N₀ ≥ 3` for which every sufficiently
high half-open block `[a,b)` obeys

```text
exists_sum_sq_card_primeWindow_le_six_mul_delta:
  b−1 ≤ (1+δ)(a−1),  0≤δ≤1,
  2B exp(−c sqrt(log(a−1))) ≤ δ
  ----------------------------------------------------------------
  ∑_{1≤n≤Y} #primeWindow(n,a,b)² ≤ 6Yδ.
```

Thus only one scalar schedule comparison remains for the `c₂,n` mean square: the PNT error at
`a ≥ z₀` is eventually below `δ_A = (log X)^{-10A}`.  Direct Lean, targeted build, and
new-declaration axiom audit passed.

### M5b, brick 10 — log-power schedule for `c₂,n` blocks (2026-08-27)

Added `Sieve/PrimeWindowLogPowerSchedule.lean`, axiom-clean and umbrella-wired.  The module proves
the unconditional scalar comparison

```text
2B exp(−c sqrt(log x)) ≤ (log x)^(−K)
```

eventually for arbitrary fixed `B ≥ 0`, `c > 0`, and `K > 0`.  Substitution into brick 9 gives a
single uniform threshold after which every half-open block `[a,b)` satisfying

```text
b−1 ≤ (1 + (log(a−1))^(−K))(a−1)
```

has exact second-moment bound

```text
∑_{1≤n≤Y} #primeWindow(n,a,b)² ≤ 6Y(log(a−1))^(−K).
```

Remaining paper-scale translation is explicit: at the paper's lower cutoff
`z₀ = exp(log X/(log log X)³)`, choose a fixed exponent stronger than `10A` and prove the resulting
lower-end log power is at most `δ_A = (log X)^(−10A)`.  After that, only `c₃,n` boundary handling
and Proposition 2.2 bookkeeping remain in this branch.  Direct Lean, targeted build,
new-declaration axiom audit, umbrella reachability, and formal lint passed.

### M5b, brick 11 — exact paper-scale `c₂,n` mean square (2026-08-27)

Added `Sieve/PrimeWindowPaperScale.lean`, axiom-clean and umbrella-wired.  It names the literal
paper schedules

```text
mtLowerCutoff X = exp(log X/(log log X)³),
mtPaperWidth A X = (log X)^(−10A),
```

proves `log X/(log log X)³ → ∞`, and uses the spare exponent `10A+1` to establish

```text
(log X/(log log X)³)^(−(10A+1)) ≤ (log X)^(−10A)
```

eventually.  Therefore the exponential Mertens error at every block bottom `a−1 ≥ z₀` is at most
the paper width `δ_A`.  Substitution into brick 9 gives the exact unconditional capstone

```text
eventually_primeWindow_paperLogWidth:
  z₀ ≤ a−1,
  b−1 ≤ (1+δ_A)(a−1)
  ------------------------------------------------
  ∑_{1≤n≤Y} #primeWindow(n,a,b)² ≤ 6Yδ_A.
```

This closes the analytic estimate for each `c₂,n` adic block at the literal source scale.  Remaining
work in M5b is `c₃,n` last-block boundary handling and Proposition 2.2's finite block/type
bookkeeping.  Direct Lean, targeted module build, new-declaration axiom audit, umbrella
reachability, and formal lint passed.

### M5b, brick 12 — exact prime-pair factorial mean (2026-08-27)

Source re-audit corrects the earlier shorthand “last-block boundary”: `c₃,n` is the replacement
error `ρ(k,Q)−ρ(k,q)`.  Buchstab forces a second prime factor in the same
`(Q,Q(1+δ_A)]` block.  Added `Sieve/PrimePairDivisorMean.lean`, defining the literal product-
divisibility pair count and proving

```text
∑_{1≤n≤Y} primePairDivisorCount S T n
  ≤ Y ∑_{p∈S} (1/p) ∑_{q∈T(p)} 1/q.
```

If every fibre has reciprocal mass at most `η`, this is at most
`Y η ∑_{p∈S}1/p`.  Equal pairs are handled separately and exactly by `p² ∣ n`, with mean
`≤ Y∑_{p∈S}p⁻²`.  This removes the diagonal term that made an ordinary card-square moment too
large after summing all adic blocks.  Direct Lean, targeted build, new-declaration axiom audit,
umbrella reachability, and formal lint passed.

### M5b, brick 13 — `c₃,n` collision envelope at paper scales (2026-08-27)

Added `Sieve/PrimePairPaperScale.lean`, axiom-clean and umbrella-wired.  Every distinct-prime fibre
above `z₀` has reciprocal mass at most `2δ_A`.  Also

```text
z₀⁻¹ ≤ δ_A
```

eventually, so repeated-prime square divisors fit the same scale.  For arbitrary finite outer
prime family `S` above `z₀` and endpoints `b(p)` satisfying
`b(p)−1 ≤ (1+δ_A)p`, the combined collision count obeys

```text
∑_{1≤n≤Y} primeBlockCollisionCount S b n
  ≤ 3Y δ_A ∑_{p∈S} 1/p.
```

This closes exact same-block pair geometry and its unweighted first moment.  Remaining `c₃,n`
work is the source's divisor-weighted lift
`∑_{n∼Y} d₃(n)|c₃,n|`, the outer reciprocal-mass bound over
`z₀/(1+δ_A) ≤ p < z₁(1+δ_A)`, and final polylog absorption into `(log X)^(−3A)`.
Direct Lean, targeted build, new-declaration axiom audit, umbrella reachability, and formal lint
passed.

### M5b, brick 14 — divisor-weighted `c₃,n` collision mean (2026-08-27)

Added `Sieve/PrimePairDivisorWeightedMean.lean` and
`Sieve/PrimePairWeightedPaperScale.lean`, both axiom-clean and umbrella-wired.  Multiplication by
one prime at most doubles divisor count, hence multiplication by two primes at most quadruples it.
Reindexing multiples of each prime pair and applying the unconditional fixed divisor-moment bound
gives, for every fixed `K`,

```text
∑_{1≤n≤Y} d(n)^K primeBlockCollisionCount(S,b,n)
  ≤ 4^K Y (1+log Y)^(2^K−1) · 3δ_A · ∑_{p∈S} 1/p.
```

The proof packages the distinct- and repeated-prime cases as one inclusive fibre
`{p} ∪ primesIco(p+1,b(p))`; its reciprocal mass is at most `δ_A+2δ_A=3δ_A`.
This retains the decisive pair-reciprocal saving under divisor weights without a Hölder loss.
Remaining `c₃,n` work: formalize the literal source coefficient and its domination by a fixed
power of `d(n)`, bound outer reciprocal mass on the source range, and absorb the resulting fixed
polylogarithm into `(log X)^(−3A)`.  Direct Lean, targeted module builds, and batched
new-declaration axiom audit passed.

### M5b, brick 15 — literal `c₃,n` coefficient and source-scale bound (2026-08-27)

Added `Sieve/MatomakiTeravainenC3Coefficient.lean`,
`Sieve/PrimeWindowRelaxedPaperScale.lean`, and
`Sieve/MatomakiTeravainenC3PaperScale.lean`, all axiom-clean and umbrella-wired.  The first module
defines the source coefficient over each outer prime's assigned adic block bottom `Q`:

```text
∑_q ∑_{m∣n/q} α_m (ρ((n/q)/m,Q) − ρ((n/q)/m,q)).
```

Its exact Buchstab expansion proves internally that every new prime `p` satisfies `qp ∣ n`; no
support premise replaces this arithmetic step.  Expansion multiplicity is bounded by `d(n)` and
the source ternary divisor weight satisfies `d₃(n) ≤ d(n)²`, reducing the weighted coefficient to
the already-proved `d(n)³` prime-pair mean.

The first source block may start at `z₀/(1+δ_A)`, below the earlier clean cutoff.  The relaxed
window theorem proves its reciprocal prime mass is still at most `2δ_A`.  The outer prime sum is
bounded by `1+log N`; the resulting fixed `log⁸` loss is absorbed by the spare powers in
`δ_A=(log X)^(−10A)`.  For `A ≥ 2` (hence the paper's `A ≥ 5`), the unconditional capstone is

```text
∑_{1≤n≤Y} d₃(n) |c₃,n| ≤ B Y (log X)^(−3A),
```

uniformly for `Y ≤ 4X`, `N ≤ X`, bounded coefficients `|α_m| ≤ B`, and the literal source block
endpoint conditions.  Direct Lean, targeted module builds, and batched new-declaration axiom audit
passed.  Remaining work: combine the exact `c₁,n`, `c₂,n`, and `c₃,n` estimates into Lemma 2.3,
then discharge Proposition 2.2's finite block/type bookkeeping.

### M5b, brick 16 — literal `c₂,n` coefficient and source-scale bound (2026-08-27)

Added `Sieve/PrimeDivisorWeightedMean.lean`,
`Sieve/MatomakiTeravainenC2Coefficient.lean`, and
`Sieve/MatomakiTeravainenC2PaperScale.lean`, all umbrella-wired.  The exact coefficient is the
source's upper block spill minus lower clipped spill.  Divisor reindexing gives its unconditional
one-prime weighted mean, and the paper-width prime-window estimate plus fixed polylogarithmic
absorption proves

```text
∑_{1≤n≤Y} d₃(n) |c₂,n| ≤ B Y (log X)^(−3A).
```

No analytic estimate is assumed as a premise.  Direct Lean, targeted module builds, and batched
new-declaration axiom audit passed.

### M5b, brick 17 — literal `c₁,n` smooth-tail coefficient (2026-08-27)

Added `Sieve/DivisorSubmultiplicative.lean`, `Sieve/SiftTailDivisorWeightedMean.lean`,
`Sieve/SiftTailDivisorEulerBound.lean`, `Sieve/MatomakiTeravainenC1Coefficient.lean`,
`Sieve/MatomakiTeravainenC1Schedule.lean`, and
`Sieve/MatomakiTeravainenC1PaperScale.lean`, all umbrella-wired.  The schedule uses the literal
rounded source parameters

```text
z₀ = ⌈exp(log X/(log log X)³)⌉,
D  = ⌊exp(log X/log log X)⌋.
```

The composite smooth truncation tail is controlled by an Euler-product/Rankin bound, then its
fixed polylogarithmic factors are absorbed at the source scale.  This proves unconditionally

```text
∑_{1≤n≤Y} d₃(n) |c₁,n| ≤ B Y (log X)^(−3A).
```

Direct Lean, targeted module builds, and batched new-declaration axiom audit passed.

### M5b, brick 18 — exact Lemma 2.3(i) and mean-square capstone (2026-08-27)

Added `Sieve/MatomakiTeravainenLemma23I.lean` and
`Sieve/MatomakiTeravainenLemma23IPaperScale.lean`, both umbrella-wired.  Exact finite divisor
reindexing, Buchstab decomposition, and the literal signs of `c₁,n`, `c₂,n`, and `c₃,n` prove the
source identity.  With

```text
e_n = c₁,n + c₂,n + c₃,n,
```

the formal pointwise estimate is `|e_n| ≤ 5B d₃(n)`.  The three source-scale first moments give

```text
∑_{1≤n≤Y} d₃(n) |e_n| ≤ 3B Y (log X)^(−3A),
∑_{1≤n≤Y} |e_n|²       ≤ 15B² Y (log X)^(−3A).
```

Thus Lemma 2.3(i), including equation (2.13) and its stated mean-square consequence, is now an
unconditional Lean theorem.  Direct Lean, targeted module builds, and batched new-declaration
axiom audit passed.  Remaining source obligations: Lemma 2.3(ii)'s finite Buchstab iteration and
Proposition 2.2's finite block/type bookkeeping.

### M5b, brick 19 — exact Lemma 2.3(ii) survivors and published absorption no-go (2026-08-27)

Added exact finite operator iteration, literal source-error identification, adjacent and real
geometric block schedules (with separate floor/ceiling endpoints), large-prime-count terminal
argument, explicit signed main/error layers, and sharp recursive coefficient bound

```text
|α_r^(d)| ≤ B K^d.
```

Finite `L²` accumulator proves source exponent exactly:

```text
K^(sum_{0≤j≤J} 2j),
```

with one depth-independent constant. Source re-audit then found a fatal final-step mismatch. At
paper's literal

```text
z₀ = exp(log X/(log log X)^3),
L  = floor(log(4X)/log z₀) ≍ (log log X)^3,
```

claimed factor `((log(4X)/log z₀)+1)^(2L²)` has logarithm
`Θ((log log X)^6 log log log X)`, whereas any fixed power of `log X` has logarithm only
`Θ(log log X)`. Therefore it is not `(log X)^o(1)` and cannot convert equation-(2.16)
`(log X)^(-3A)` bound to stated `(log X)^(-2A)` bound. Same line appears in arXiv v2 and 2023
accepted manuscript. Recorded
`5-failed/matomaki-teravainen-lemma23ii-log-absorption-no-go.md`.

Strong positive survivor: equation (2.15)'s exact algebra, literal `c₁+c₂+c₃` provenance,
source-faithful block schedule, correct coefficient growth, cumulative exponent, and terminal
remainder vanishing are formal. Open core is a genuinely stronger analytic layer estimate or a
different stopping/schedule argument. Proposition 2.2 cannot be promoted from this published
Lemma 2.3(ii) proof until that core is repaired.

### M5b, brick 20 — divisor-bounded repair candidate for Lemma 2.3(ii) (2026-08-27)

The false factor in the published proof comes from bounding the depth-`d` coefficient by
`B K^d`, where `K` counts prime divisors at least `z₀`. This loses strict block ordering. For fixed
`r`, every representation

```text
r = m q₁ ... q_d,   j_d < ... < j₁,   q_u in block j_u
```

maps injectively to divisor `q₁ ... q_d | r`: pairwise-disjoint prime blocks recover each `q_u`
and its unique block, then `m` is forced. Hence iterated coefficient is bounded by

```text
|alpha'_r| <= B d(r),
```

uniformly in `d`, not by `B K^d`.

This suggests an exact repair. Extend Lemma 2.3(i) from bounded coefficients to fixed
divisor-bounded envelope `|alpha_m| <= B d(m)`. Its proof already uses fixed divisor moments;
submultiplicativity changes only fixed log powers. Each depth layer then retains a
`Y (log X)^(-3A)` mean square after reserving those powers. Finite Hilbert-space accumulation
costs at most `(L+1)^2`, and

```text
L = floor(log(4X)/log z₀) = O((log log X)^3),
(L+1)^2 = (log X)^o(1).
```

Thus repaired route can absorb from `-3A` to `-2A` without false `L^(2L²)` step.

Status: paper mechanism identified, not yet dependency-closed. Required Lean bricks are
(i) exact depth-uniform divisor bound for iterated coefficient, (ii) literal divisor-bounded
Lemma 2.3(i) at paper scale, (iii) layer accumulation with only polynomial `L` loss, and
(iv) final source-scale absorption. No repaired Lemma 2.3(ii) theorem is claimed before all four
close.

### M5b, brick 21 — dependency-closed aligned repair of Lemma 2.3(ii) (2026-08-27)

All four repair obligations from brick 20 are now closed. Strictly ordered disjoint prime blocks
give a depth-uniform divisor envelope for terminal coefficients. A grid-free aggregation of all
terminal cutoffs keeps one global `c₁`, endpoint-spill, and same-block collision family rather than
paying the false grid factor. Fixed divisor moments give every depth layer the source
`Y(log X)^(-3A)` saving, finite Hilbert-space accumulation costs only `(L+1)^2`, and the cubic
source depth absorbs this into `(log X)^(-2A)`.

The repaired schedule uses natural aligned endpoints whose nonempty prime blocks satisfy the exact
source-width condition `(Q,(1+δ_A)Q]`; empty padded blocks are removed. Added exact chain-product,
terminal-coefficient, grid-free error, paper-scale accumulation, and aligned-schedule modules. The
unconditional capstone is

```text
eventually_exists_matomakiTeravainen_lemma23ii_repaired:
  A ≥ 5, z₀ ≤ z₁ ≤ X, Y ≤ 4X, |α_m| ≤ B
  ---------------------------------------------------
  ∃ aligned source data,
    exact terminal expansion at depth floor(log Y/log z₀),
    ∑_{1≤n≤Y}|accumulated error(n)|²
      ≤ 15 B²Y(log X)^(-2A).
```

This is a mathematically repaired variant, not a proof of the published literal power-grid final
line ruled out in brick 19.

### M5b, brick 22 — Proposition 2.2 count and scale classification (2026-08-27)

Added exact active-chain indexing and proved that every signed main layer is the sum over strictly
descending nonempty block chains. Active aligned blocks are bounded by
`6(log X)^(10A+1)`, source depth by `2(log log X)^3`, and the exact sum of chain cardinalities over
all depths by `exp((log log X)^5/2)`. Any fixed number of outer `δ_A`-adic grid choices is a fixed
power of `log X`, so chain count times every outer partition is at most the proposition's literal
`exp((log log X)^5)` budget.

The source's final subset choice is now exact: if the full iterated block product reaches
`X^(ε/2)`, a nonempty subset product lies in `[X^(ε/2),X^(2/11)]`; the proof splits off a single
large factor or greedily accumulates logarithms and uses `ε ≤ 2/11`. The complementary small
branch gives the exact Type-I scale for the pair term. For the triple term, the source grouping

```text
M₁ = E Q₂ Q₃,     M₂ = Q₁ ∏Qᵢ′
```

satisfies `M₁²M₂ ≤ X^(1-ε)` and `M₂ ≤ X^(1/4-ε)`. Literal Type I, Type I/II, and Type II
arithmetic-function types are defined, including equation (2.11)'s ordered prime-block tuple
coefficient and its unconditional divisor bound.

Open Proposition 2.2 core: rectangularize the fourth Harman term without hiding its coupled
conditions. Exact adic cells create (i) same-block `q₂,q₃` order collisions and (ii) the narrow
boundary where `q₁q₂⁴ < X^(1-2ε)` changes inside one cell. Both must be source-identified and
discharged with the existing divisor-weighted prime-pair/window bounds before assembling the full
minorant decomposition and its supported `L²` error. Count, subset selection, and all scale
inequalities are closed.

### M5b, brick 23 — exact Harman rectangularization and literal error bounds (2026-08-27)

The fourth-term rectangularization core is closed without weakening source predicates. Exact
active pair and triple cells partition the uniformly good source tuples; disjoint prime blocks make
every pair/triple cell coefficient unique and uniformly bounded by one. Applying the repaired
Lemma 2.3(ii) cellwise gives an exact terminal expansion with per-cell mean square
`15Y(log X)^(-2A)`.

The exposed source sums are definitionally reindexed back to Harman's original terms:

```text
mtHarmanAdmissiblePairSiftSum (primesIco z D) E z n = harmanS2 z D E n,
mtHarmanAdmissibleTripleSiftSum (primesIco z D) E z n = harmanS3 z D E n.
```

Every excluded pair is either a strict same-cell collision or lies in the exact threshold-boundary
fibre. Every excluded triple is one of the two strict same-cell collisions or lies in the same
pair-threshold fibre. Literal complex errors are bounded by their exact bad-tuple counts. Bad pairs
inject into `divisors(n)^2`; bad triples inject into `divisors(n)^3`, while the extra prime above a
counted obstruction costs at most one further divisor. Consequently the pointwise squared errors
are absorbed by the existing weighted majorants at `K=2` and `K=4`. Their paper-aligned means are
therefore bounded by the already-proved exact costs

```text
4^2 Y (1+log Y)^3  (66 δ_A) ∑_{p in P} 1/p,
4^4 Y (1+log Y)^15 (68 δ_A) ∑_{p in P} 1/p.
```

New compiled leaves are `MatomakiTeravainenHarmanCellIteration.lean`,
`MatomakiTeravainenHarmanRectangularSums.lean`, and
`MatomakiTeravainenHarmanNonrectangularErrors.lean`.

Open Proposition 2.2 core: exact outer adic partition of the base, one-prime, pair, and triple
terms; package all terminal expansions as literal Type I, Type I/II, and Type II pieces; aggregate
the finite family errors inside the proposition's `exp((log log X)^5)` count budget; prove final
support `(Y/4,8Y]` and `Y(log X)^(-A)` mean square; wire the capstone and promote only after this
dependency closes.

### M5b, brick 24 — unconditional literal Proposition 2.2 assembly (2026-08-28)

The remaining Proposition 2.2 obligations are closed. Exact outer adic partitions for the base,
one-prime, pair, and triple terms feed the repaired grid-free terminal expansion. Compression
removes only padded empty one-prime blocks and preserves the retained main exactly. Every retained
index is classified at the literal real thresholds as Type I, Type I/II, or Type II; the Type-II
chain-length obligation now follows intrinsically from its selected prime product rather than an
impossible global recursion-depth bound.

Added the paper-parameter side-condition package and capstone in
`Sieve/MatomakiTeravainenProposition22PaperConditions.lean` and
`Sieve/MatomakiTeravainenProposition22PaperAssembly.lean`. For `A ≥ 5`,
`0 < epsilon ≤ 1/100`, all sufficiently large `X`, and every natural `Y` with

```text
X^(1-epsilon/100) < Y ≤ X/2,
```

`eventually_nonempty_mtProposition22Decomposition` constructs an exact finite decomposition with

```text
rhoMinus-source = sum of Proposition-2.2 pieces + c,
#pieces ≤ exp((log log X)^5),
support(c) ⊆ (Y/4,8Y],
sum_{1≤n≤8Y} |c(n)|^2
  ≤ (92224 * 5^35 + 7232) Y (log X)^(-A).
```

Natural cutoffs are the ceilings of the paper's literal real powers; no open input, added premise,
axiom, `sorry`, or computational certificate is used. Proposition 2.2 bookkeeping is therefore
dependency-closed in Lean. Programme remains in progress because the later analytic route from
Proposition 2.2 to the all-interval `E3` theorem still has separate obligations.

### M6, brick 25 — finite one-spaced Type-II assembly (2026-08-28)

The three Proposition 4.2 amplitude regimes now assemble unconditionally for every finite
one-spaced frequency set. The new capstone
`exists_matomakiTeravainen_typeII_proposition42_huxley` combines the exact large-amplitude `T1`
energy bound, Huxley's middle-amplitude `T2` saving, and the tiny-amplitude `T3` saving through the
overlap-safe partition theorem. Under the explicit dyadic product window and
`sigma0 + eta + epsilon^2/20 <= 7/32 - 5 epsilon`, it proves

```text
sum_{t in S} |M1(1+it)|^2 |M2(1+it)|^2
  <= 16384 B1^2 (1+|log T|) C2^2
       (2(1+|log T|))^(2^(2(w2+1))-1)
     + T^(-epsilon^2/20) + T^(-1/2).
```

This is the dependency-closed finite Huxley-strength core, not the paper's literal measurable-set
Proposition 4.2. Two obligations remain distinct: the paper uses Jutila's sharper large-values
input, and its reduction from an arbitrary measurable `U subset [0,T]` to one-spaced samples needs
a restricted-set discretisation theorem. Corpus `exists_spaced_families_integral_le` applies only
to a continuous integrand on a full interval, so it cannot be used on `U.indicator F` without a
new measurable-set argument. No measurable conclusion is claimed.

### M2, brick 26 — exact pointwise two-window Perron comparison (2026-08-28)

Added `Sieve/MatomakiTeravainenLemma31PerronComparison.lean`. For natural left endpoint `A`, short
width `H`, reference width `H1`, coefficient cutoff `M`, and Perron height `T`, the theorem
`norm_perronWindowSum_compare_sub_integral_le` proves exactly

```text
windowSum(A,H) - (H/H1) windowSum(A,H1)
  = (1/(2*pi)) integral_{-T}^{T}
      perronPoly(1+it) perronCompareKernel(A+1/2,H,H1,t) dt
    + endpoint error,
```

with the endpoint error bounded by the sum of the two short-window Perron errors plus `H/H1`
times the two long-window Perron errors. The kernel identity is literal at base `A+1/2`; no
asymptotic notation, floor suppression, or cancellation premise is hidden. Existing
`norm_perronCompareKernel_le_min3` and `integral_mixed_moment_windowCompare_le` can now consume the
integral without another algebraic bridge.

This closes the pointwise Perron bookkeeping seam, not all of Lemma 3.1. Remaining work is the
continuous `x`-variance integration: align real window endpoints with the natural half-integer
windows, identify the coefficient polynomial with `P1(s)P(s)`, integrate the explicit endpoint
errors, and insert the assumed mixed mean-square bound. No variance conclusion is claimed yet.

### M6, brick 27 — cell-max discretisation *restricted to a closed set* (2026-08-29)

Brick 25 left `exists_matomakiTeravainen_typeII_proposition42_huxley` stated for finite one-spaced
frequency **sets**, and recorded that the passage to the paper's measurable `U ⊆ [0,T]` was blocked:
the corpus's `HTGeometry/CellMaxDiscretisation.exists_spaced_families_integral_le` discretises a
continuous integrand over a *full* interval, and its sample points are unconstrained, whereas the
Proposition 4.2 hypotheses require every sample point to satisfy the amplitude threshold — i.e. to
lie in `U`.

That gap is now closed, in the form the application actually needs.  `U` is not an arbitrary
measurable set: it is the set where a Dirichlet-polynomial amplitude exceeds a threshold, i.e. the
preimage of a closed half-line under a continuous function, hence **closed**.  For a closed
restricting set the cell-max argument runs verbatim, because each closed cell meets `U` in a
*compact* set and a continuous integrand attains its maximum there at a point of `U`.

`formal/GaloisForLFunctions/HTGeometry/CellMaxSetDiscretisation.lean`, unconditional and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), wired into `GaloisForLFunctions.HTGeometry`:

```text
iUnion_Ioc_cells                  the half-open cells of length Δ tile `Ioc a (a+mΔ)`
exists_cell_max_setIntegral_le    ∃ K ⊆ range m and maximisers c k ∈ U ∩ cell k with
                                    ∫_{U ∩ Ioc a (a+mΔ)} F ≤ ∑_{k ∈ K} Δ · F (c k)
exists_spaced_families_setIntegral_le
    ∃ S₁ S₂ ⊆ U ∩ Icc a (a+mΔ), both Δ-spaced, with
      ∫_{U ∩ Ioc a (a+mΔ)} F ≤ Δ · ( ∑_{S₁} F + ∑_{S₂} F )
```

The conclusion also records `S₁, S₂ ⊆ Icc a (a+mΔ)`, which discharges Proposition 4.2's diameter
hypothesis `∀ x y ∈ S, |x − y| ≤ 2T` at `a = -T`, `Δ = 1`, `m = 2T`.

Only cells that actually meet `U` enter the sum (the index set `K`), so no sample point is
manufactured outside the level set; cells missing `U` contribute a vanishing integral.  Splitting
`K` by parity gives the two `Δ`-spaced families.

**What this unblocks.** With the amplitude's continuity, the level set
`{t : A₁^{-σ₀} ≤ amp₁ t ∨ A₂^{-σ₀} ≤ amp₂ t}` is closed, and
`exists_spaced_families_setIntegral_le` converts the finite-set bound of brick 25 into a bound on
`∫_U amp₁² amp₂²` at the cost of a factor two.  That is the paper's Proposition 4.2 in integral
form, the shape §5's Cauchy–Schwarz consumes.

### M4d, brick 28 — Proposition 4.2 in integral form (2026-08-29)

`Sieve/MatomakiTeravainenProposition42Integral.lean`, unconditional and axiom-clean, wired into
`GaloisForLFunctions.RHTower`:

```text
continuous_matomakiTeravainenDirichletAmplitude
    the Dirichlet amplitude is continuous in the ordinate (from the corpus's `continuous_dirPoly`)
matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ σ₀ B₁
    = Icc (−T) T ∩ {amp₁ ≤ 1} ∩ {amp₂ ≤ 1} ∩ {amp₁ ≤ B₁}
        ∩ ({A₁^{−σ₀} ≤ amp₁} ∪ {A₂^{−σ₀} ≤ amp₂})
isClosed_matomakiTeravainenTypeIIRegion       — every constraint is a closed condition
matomakiTeravainenTypeIIRegion_subset_Icc
exists_matomakiTeravainen_typeII_proposition42_integral
    ∫_{region} amp₁² amp₂²
      ≤ 2 · ( 16384 B₁² (1+|log T|) C₂² (2(1+|log T|))^{2^{2(w₂+1)}−1}
              + T^{−ε²/20} + T^{−1/2} )
```

The factor two is the parity split of the unit cells; nothing else is lost.  The diameter
hypothesis `|x − y| ≤ 2T` of the finite form is discharged from `region ⊆ Icc (−T) T`, and the
one-spacing from `Δ = 1`.

**M4d is therefore complete in the Huxley-strength form**: the paper's Proposition 4.2 as an
integral over the amplitude region, with no measurable-set hypothesis left open, and with the
factor-two loss made explicit.  What separates it from the paper's literal statement is only the
strength of the large-values input (Huxley in place of Jutila), which the programme deliberately
chose.

Remaining milestones: **M2** (Lemma 3.1's continuous variance integration), **M6/M7** (Type I and
Type I/II), **M8** (the assembly at exponent `1 + 44/79`).

### M2, brick 29 — real windows aligned with the natural Perron windows (2026-08-29)

Brick 26 left the pointwise two-window Perron comparison stated for a *natural* left endpoint
`A : ℕ`, while Lemma 3.1's variance runs over a **real** centre `x`.  The alignment is now closed,
and it is exact.

`Sieve/RealWindowAlignment.lean`, unconditional, axiom-clean, umbrella-wired:

```text
natWindow_eq_realWindow            the naturals in (x, x+h] are exactly Ioc ⌊x⌋ ⌊x+h⌋
sum_realWindow_eq_perronWindowSum  **the real window sum IS a natural window sum**, with no error,
                                   at A = ⌊x⌋, H = ⌊x+h⌋ − ⌊x⌋
abs_natWidth_sub_le_one            |(⌊x+h⌋ − ⌊x⌋) − h| ≤ 1
norm_realWindowSum_compare_sub_integral_le
    brick 26's identity transported verbatim to the real windows (x, x+h] and (x, x+h₁]
```

The point worth recording: **there is no truncation error in the alignment**.  The only inexactness
is that the integer width `⌊x+h⌋ − ⌊x⌋` replaces `h`, and it does so within one — which is a
relative error `O(1/h)`, negligible at the paper's `h = √x(log x)^c`.

What M2 still needs is the `x`-integration itself: square the pointwise bound, integrate over
`x ∈ [X, 2X]`, and exploit the orthogonality of `x^{i(t−t')}` (the corpus's
`Sieve/LogWindowPlancherel` is the sharp form of that step) to convert the squared Perron integral
into the mixed mean square that `integral_mixed_moment_windowCompare_le` bounds.

### M2, brick 30 — the comparison kernel is dominated at *every* height (2026-08-29)

`Sieve/MixedMomentWindowCompare.norm_perronCompareKernel_le_windowCompareKernel` compares the
analytic kernel with the mixed-moment kernel only **above** the transition height `t₀`, where the
two visibly agree.  The Perron integral of Lemma 3.1 runs over the whole range, and below `t₀` the
mixed-moment kernel's third component is the *constant* `4(x+h₁)/t₀`, which is smaller than the
analytic kernel's `4(x+h₁)/|t|` — so the comparison is not free there.

`Sieve/PerronWindowKernelCompareAll.lean`, unconditional, axiom-clean, umbrella-wired:

```text
perronCompareKernel_zero              the analytic kernel vanishes at t = 0
windowCompareKernel_zero              so does the mixed-moment kernel
norm_perronCompareKernel_le_windowCompareKernel_all
    **domination below the transition height too**, under `t₀ ≤ x/h₁`
norm_perronCompareKernel_le_windowCompareKernel_all'
    …including the origin
continuous_perronCompareKernel'       continuity in the ordinate (a corpus gap)
norm_integral_perronPoly_compareKernel_le
    ‖∫_{-T}^{T} perronPoly · perronCompareKernel‖ ≤ ∫_{-T}^{T} ‖perronPoly‖ · windowCompareKernel
```

Below `t₀` the *first two* components already beat the constant: `t₀ ≤ x/h₁` gives
`2|t|hh₁/x ≤ 2t₀hh₁/x`, and `(t₀h₁)(t₀h) ≤ x·x` then gives `2t₀hh₁/x ≤ 4(x+h₁)/t₀`.

**M2's pointwise chain is now complete as a sequence of owned theorems**: alignment (brick 29) →
two-window Perron identity with explicit endpoint errors (brick 26) → kernel domination at every
height (brick 30) → `integral_mixed_moment_windowCompare_le`.  What remains is the bookkeeping that
factors `perronPoly` as `P₁P · P₂` and inserts the two mean-square hypotheses, plus the arithmetic
of the endpoint errors at the paper's parameters.

### M2, brick 31 — Lemma 3.1's pointwise comparison, ASSEMBLED (2026-08-29)

`Sieve/RealWindowCompareBound.lean`, unconditional, axiom-clean, umbrella-wired:

```text
norm_realWindowSum_compare_le
   ‖ ∑_{x < n ≤ x+h} c n  −  (H/H₁) ∑_{x < n ≤ x+h₁} c n ‖
     ≤ (1/2π) ∫_{-T}^{T} ‖perronPoly c M 1 t‖ · windowCompareKernel (⌊x⌋+½) H H₁ t₀ t  dt
       + [ perronNearError K M ⌊x+h⌋ 1 T + perronNearError K M ⌊x⌋ 1 T
           + (H/H₁)( perronNearError K M ⌊x+h₁⌋ 1 T + perronNearError K M ⌊x⌋ 1 T ) ]
```

with `H = ⌊x+h⌋ − ⌊x⌋`, `H₁ = ⌊x+h₁⌋ − ⌊x⌋`, under `0 < H ≤ H₁`, `0 < t₀ ≤ (⌊x⌋+½)/H₁`, and
`‖c n‖ ≤ K`.  **No asymptotic notation, no hidden cancellation, every error term explicit.**

This is Lemma 3.1's pointwise content.  The only analytic input left in it is the mixed-moment
integral on the right, and that is exactly what
`Sieve/MixedMomentWindowCompare.integral_mixed_moment_windowCompare_le` bounds from the two mean
squares — one of which, the large prime variable, is the corpus theorem `(FS7)`
(`Sieve/DyadicPrimeMeanSquare`).

**M2 is therefore complete as a chain of owned theorems.**  What remains to state the paper's
Lemma 3.1 verbatim is the factorisation of `perronPoly` as `P₁P · P₂` at the paper's parameters and
the arithmetic of the endpoint errors — bookkeeping, with no analytic content left.

Remaining milestones for Theorem 1.2: **M6/M7** (Type I and Type I/II) and **M8** (the assembly at
exponent `1 + 44/79`).

### M2, brick 32 — Proposition-2.2 Perron factorization (2026-08-29)

`Sieve/MatomakiTeravainenPerronFactorization.lean`, unconditional, axiom-clean, umbrella-wired:

```text
arithmeticFunction_mul_eq_lseriesConvolution
    arithmetic-function multiplication is literal `LSeries.convolution` on coefficients
perronPoly_eq_LSeries_of_support
    a Perron cutoff containing the full support is the corresponding finite `LSeries`
mtRealIntervalAF_support_nat
    the canonical cutoff `⌈U⌉₊` contains every interval-supported coefficient
perronPoly_arithmeticFunction_mul
    exact two-factor Perron factorization at the product cutoff
MTTypeIPieceData.perronPoly_factorization
MTTypeI_II_PieceData.perronPoly_factorization
MTTypeIIPieceData.perronPoly_factorization
    exact factorization of every Proposition-2.2 piece into its source Dirichlet factors
```

All cutoffs are explicit ceilings of the actual real support endpoints.  The Type-I/II identity
retains all three factors and the left-associated convolution/product structure; no factor is
absorbed or simplified away.  Thus brick 31's `perronPoly` is now connected exactly to the
Dirichlet factors used by the mean-value estimates.

Remaining milestones for Theorem 1.2: the analytic **M6/M7** Type-I and Type-I/II estimates, then
the **M8** all-interval E3 assembly.  The two Route-E cards stay in Stage 2 until that final theorem
is instantiated with every scale and support condition discharged.

### M6/M7, brick 33 — Watt--Deshouillers--Iwaniec over-height branch (2026-08-29)

Source audit of §§5.1--5.2 isolates the remaining common input as Lemma 3.5: Watt's and
Deshouillers--Iwaniec's twisted fourth moments.  The paper itself splits their proof at the length
`N` of the unit-coefficient factor.  The entire branch `T ≤ N` is now closed in
`Sieve/MatomakiTeravainenWattDIOverHeight.lean`, unconditional, axiom-clean, umbrella-wired:

```text
mtWattUnitBlock, mtWattCoefficientBlock
    exact Perron-line carriers on `(N,N']` and `(A,2A]`
mtWattUnitBlock_eq_sum_Ico
    literal finite Dirichlet-block identity
norm_mtWattUnitBlock_le_over_height
    ‖N(1+it)‖ ≤ 2(6π+1)/T for T/2 ≤ t ≤ T ≤ N
integral_Icc_normSq_mtWattCoefficientBlock_le_general_affine
    arbitrary coefficient block paid by its exact affine masses
integral_mtWatt_overHeight_le_generalAffine
    ∫_{T/2}^{T} |N|⁴|A|²
      ≤ (2(6π+1)/T)⁴ · (generalMeanSquareConst + T·generalMeanSquareRate)
mtWatt_weightedMass_term_le, mtWatt_plainMass_term_le
    exact pointwise A⁻¹ and A⁻² costs on the dyadic coefficient support
sum_normSq_mtWattCoefficientBlock_eq
    the restricted block energy is exactly ∑_{A<n≤2A} |aₙ|²
generalMeanSquareConst_mtWattCoefficientBlock_le_energy
    generalMeanSquareConst ≤ (5πe/A) ∑_{A<n≤2A} |aₙ|²
generalMeanSquareRate_mtWattCoefficientBlock_le_energy
    generalMeanSquareRate ≤ (5π/(2A²)) ∑_{A<n≤2A} |aₙ|²
integral_mtWatt_overHeight_le_energy
    ∫_{T/2}^{T} |N|⁴|A|²
      ≤ (2(6π+1)/T)⁴ · (5πe/A + 5πT/(2A²)) · ∑_{A<n≤2A} |aₙ|²
```

This derives the source's `T⁻⁴` residual branch directly from corpus Kuzmin--Landau and the affine
mean-square theorem, including the literal coefficient-energy normalization used in the
Deshouillers--Iwaniec form.  Every declaration has only `propext`, `Classical.choice`, and
`Quot.sound` in its axiom audit.  No Watt, Deshouillers--Iwaniec, spectral, or large-value premise
remains when the factor exceeds the height.  Remaining M6/M7 core is now precisely the
complementary sub-height regime `N ≤ T`, where the published argument uses the deep twisted
moments.  Final card closure still requires that regime plus the source amplification and exponent
arithmetic; no card is promoted by this brick alone.

### M6/M7, brick 34 — full-product long-height branch (2026-08-29)

`Sieve/MatomakiTeravainenWattProductMeanSquare.lean`, unconditional, axiom-clean,
umbrella-wired:

```text
perronPoly_eq_dirPoly_twistedTruncCoeff
    exact Perron-polynomial / finite-dirPoly bridge
sum_norm_mtWattUnitCoeff_le_one
    reciprocal ℓ¹ mass on (N,N'] is at most one when N' ≤ 2N
sum_norm_sq_mtWattDataCoeff_le_energy
    data block has ℓ² mass at most A⁻² ∑_{A<n≤2A}|aₙ|²
sum_norm_sq_mtWattProductDirCoeff_le_energy
    multiplicative Young transports that energy through both unit blocks without divisor loss
mtWattProduct_eq_dirPoly
    exact three-factor Watt product as Young-compatible Dirichlet polynomial
integral_mtWatt_longHeight_le_energy
    2AN'² ≤ T implies
    ∫_{T/2}^{T}|N(1+it)|⁴|A(1+it)|²dt
      ≤ (5πe+5π/2)(T/A²)∑_{A<n≤2A}|aₙ|²
```

Thus ordinary affine mean square closes the second elementary side of Lemma 3.5 whenever the
*complete product length* lies below the height.  Together with brick 33, the genuine
Watt--Deshouillers--Iwaniec core is narrowed to the intermediate range
`N < T < 2AN'²`.  All new declarations audit to `propext`, `Classical.choice`, and
`Quot.sound` only.  M6/M7 and both Route-E cards remain open until that intermediate range and
the final amplification/exponent assembly are formalized.

### M6/M7, brick 35 — exact Lemma 3.5 over-height envelopes (2026-08-29)

`Sieve/MatomakiTeravainenLemma35OverHeight.lean`, unconditional, axiom-clean,
umbrella-wired, upgrades brick 33 from a matching residual estimate to both literal source
envelopes in Lemma 3.5(i)--(ii):

```text
mtLemma35OverHeightConst
    explicit absolute constant
integral_mtLemma35_overHeight_le_residualEnergy
    shared explicit residual estimate, with exact coefficient-energy normalization
mtWattCoefficientMaxSq
    genuine finite maximum of |aₙ|² on `(A,2A]`
sum_normSq_mtWattCoefficientBlock_le_max
    ∑_{A<n≤2A}|aₙ|² ≤ A max_{A<n≤2A}|aₙ|²
integral_mtWatt_lemma35_overHeight
    T ≤ N and ε > 0 imply the Lemma 3.5(i) Watt envelope
integral_mtDI_lemma35_overHeight
    T ≤ N and ε > 0 imply
    ∫_{T/2}^{T}|N(1+it)|⁴|A(1+it)|²dt
      ≤ C T^ε
        ((T + A²T^(1/2) + A^(5/4)T^(3/4))/(N²A)
          + (T+A)/(T⁴A))
        (1/A)∑_{A<n≤2A}|aₙ|²
```

The proofs algebraically embed brick 33's explicit `T⁻⁴` estimate into the source residual,
use the exact dyadic-cardinality maximum bound for Watt, add each nonnegative main term, and use
`T^ε ≥ 1`; they introduce no analytic premise.  All new declarations audit to `propext`,
`Classical.choice`, and `Quot.sound` only.  This discharges both exact source statements throughout
`T ≤ N`.  Remaining deep range stays exactly
`N < T < 2AN'²`, followed by source amplification and exponent assembly; no Route-E card is yet
eligible for Stage 3.

### M6/M7, brick 36 — divisor-energy recovery in the intermediate range (2026-08-30)

`Sieve/MatomakiTeravainenWattDivisorEnergy.lean` is unconditional, axiom-clean, and
umbrella-wired.  It replaces brick 34's lossy reciprocal `ℓ¹` transport by two applications of
the divisor-fibre convolution-energy theorem:

```text
sum_norm_sq_mtWattUnitCoeff_le_inv
    ∑_{N<n≤N'} |1/n|² ≤ 1/N
exists_sum_norm_sq_mtWattProductDirCoeff_le_divisor
    full triple-convolution energy
      ≪ε (2AN'²)^(ε/2)(N'²)^(ε/2) A⁻²N⁻²
         ∑_{A<n≤2A}|aₙ|²
exists_integral_mtWatt_divisorEnergy
    ∫_{T/2}^{T}|N(1+it)|⁴|A(1+it)|²dt
      ≪ε (2AN'²)^(ε/2)(N'²)^(ε/2)
         (T+2AN'²) A⁻²N⁻² ∑_{A<n≤2A}|aₙ|²
```

This is the strongest ordinary affine-mean-square estimate available after retaining both
reciprocal unit-block energies.  It supplies a new elementary envelope inside
`N < T < 2AN'²`; comparison with the literal Watt/Deshouillers--Iwaniec right-hand side now
isolates only parameter configurations where the product-length term exceeds the source main
terms.  Direct check, targeted module build, and `#print axioms` all pass; the three declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.  Full Lemma 3.5 still requires the
genuine twisted fourth-moment bound on that residual configuration, then amplification and
Theorem 1.2 exponent assembly.

### M6/M7, brick 37 — divisor energy reaches the literal Watt/DI envelopes (2026-08-30)

`Sieve/MatomakiTeravainenWattDivisorRange.lean` compares brick 36 directly with both right-hand
sides of Matomäki--Teräväinen Lemma 3.5:

```text
exists_integral_mtDI_lemma35_divisorRange
    divisor energy implies the literal DI envelope when 2AN'² ≤ A^(5/4)T^(3/4)

exists_integral_mtWatt_lemma35_divisorRange
    divisor energy implies the literal Watt envelope when 2AN'² ≤ A²√T
```

The strengthened capstones
`exists_integral_mtDI_lemma35_divisorRange_of_le_height` and
`exists_integral_mtWatt_lemma35_divisorRange_of_le_height` choose divisor exponent `ε/5` and
prove its absorption into `T^ε` from `T ≥ 2`, `A ≤ T`, `N ≤ T`, and `N' ≤ 2N`. No
twisted-moment, spectral, large-value, coefficient-boundedness, or divisor-power premise remains
in these regions. Direct source check and targeted leaf build pass. All six declarations audit to
`[propext, Classical.choice, Quot.sound]`, and the leaf is umbrella-wired without an umbrella
build.

This is not final Lemma 3.5: next arithmetic step must derive `A ≤ T`, `N ≤ T`, and the applicable
displayed product-length inequality from each actual Proposition-2.2 parameter case. Only the
complementary scale region may still require a genuine twisted fourth moment; neither Route-E
card is promoted yet.

### M6/M7, brick 38 — over-height/divisor-range union assembled (2026-08-31)

`Sieve/MatomakiTeravainenLemma35CoveredRange.lean` combines brick 35 with brick 37.  Its two
capstones

```text
exists_integral_mtDI_lemma35_coveredRange
exists_integral_mtWatt_lemma35_coveredRange
```

perform the `T ≤ N` versus `N < T` split internally.  In the first branch they use the elementary
over-height estimate and require no `A ≤ T` or product-length comparison; in the second they derive
`N ≤ T` and use reciprocal divisor energy when `A ≤ T` and the corresponding DI/Watt
product-length inequality holds.  Thus neither theorem retains a supplied comparison between `N`
and `T`, and the coverage condition is the exact union of the two proved regions.

Direct check and targeted leaf build pass.  Both declarations audit to
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.
Residual Lemma 3.5 configuration is now exactly `N < T` together with either `A > T` or failure of
the applicable product-length comparison.  Proposition-2.2 scale arithmetic must eliminate or
route those cases before amplification and Theorem 1.2 assembly.

### M6/M7, brick 39 — full-numerator and internal height routing (2026-08-31)

`Sieve/MatomakiTeravainenLemma35NumeratorRange.lean` charges the complete affine-mean-square
product length to the entire literal Watt/Deshouillers--Iwaniec numerator, rather than demanding
that one summand dominate. Its capstones

```text
exists_integral_mtDI_lemma35_numeratorRange
exists_integral_mtWatt_lemma35_numeratorRange
```

split internally between over-height, large-`A`, and full-numerator branches. No comparison between
`A`, `N`, and `T` remains except the exact numerator inequality itself. Direct source check,
targeted leaf build, and new-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`.

### M6/M7, brick 40 — third-derivative reciprocal-block range (2026-08-31)

`Sieve/MatomakiTeravainenLemma35ThirdDerivative.lean` specializes the general logarithmic
third-derivative test to the exact reciprocal unit block and proves

```text
norm_mtWattUnitBlock_le_thirdDerivativeWindow :
  |N(1+it)| ≤ 4096 (T^(1/6)N^(-1/2) + N^(1/4)T^(-1/4))
```

on `T/2 ≤ t ≤ T ≤ N^3`. Abel transport and the one-unit-factor mean square then give
`exists_integral_mtDI_lemma35_thirdDerivativeRange`, which proves the literal DI envelope wherever
its resulting scalar comparison holds. All applicability and divisor-power conditions are
discharged internally from the displayed source scales. Direct source check and new-declaration
axiom audit pass with only `[propext, Classical.choice, Quot.sound]`.

### DI spectral bridge, brick 41 — integrated Kloosterman/residue Parseval (2026-08-31)

`Sieve/KloostermanHybridResidueParseval.lean` now carries both pointwise and integrated exact
energy laws. The new theorem

```text
sum_integral_normSq_kloostermanHybridTransform_eq_unitResidueEnergy
```

identifies the Kloosterman-transform energy over every symmetric physical-height window with
`(q+1)^3` times the integrated Dirichlet energy on unit physical residue classes. Finite summation
and integration commute exactly; no inequality, modulus average, spectral estimate, or new premise
is hidden. Direct check and targeted leaf build pass; the two new declarations audit to
`[propext, Classical.choice, Quot.sound]`.

This is the finite local bridge needed before modulus averaging. It does not prove the residual
Deshouillers--Iwaniec estimate: the remaining core is still the genuine spectral cancellation in
the Proposition-2.2 scale region not covered by bricks 33--40, followed by amplification and the
Theorem 1.2 assembly.

### DI spectral bridge, brick 42 — normalized finite-modulus direct sum (2026-08-31)

`Sieve/KloostermanHybridModulusEnergy.lean` packages arbitrary finite modulus families with
coefficient data allowed to depend on the modulus. Its exact theorem

```text
normalizedKloostermanHybridModulusEnergy_eq_unitResidue
```

divides each Kloosterman output energy by its cubic local Plancherel factor and identifies the
whole direct sum with unit-residue physical energy. The companion
`normalizedKloostermanHybridModulusEnergy_le_baseline` proves the explicit pre-spectral bound

```text
sum_q [5*pi*e*N/(q+1) + 5*pi*T] * coefficientEnergy(q).
```

This cleanly identifies the scale a cross-modulus spectral theorem must improve. Direct check,
targeted leaf build, umbrella wiring, and all-new-declaration axiom audit pass; only
`[propext, Classical.choice, Quot.sound]` occur.

### Sparse large values, brick 43 — Heath--Brown basic collision reduction (2026-08-31)

`Sieve/HeathBrownSparseMeanValueBasic.lean` proves the unconditional basic sparse mean-value
inequality behind Heath--Brown Theorem 4(i). Its generic theorem

```text
integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
```

keeps repeated frequencies as separate finite indices and bounds their symmetric-window mean
square by the literal weighted near-collision sum. Positive integer supports, unit phases, positive
height, and `[0,1]` dense coefficients are encoded in types; no side premise supplies any analytic
estimate. The source-facing capstone

```text
integral_Icc_normSq_heathBrown_factors_le_collision
```

first identifies the indexed polynomial exactly with `M(it)Q(it)`, then proves the explicit bound

```text
integral_{-T}^{T} |M(it) Q(it)|^2 dt
  <= (5*pi/2) T * #{(m1,n1,m2,n2) : |log(m1*n1)-log(m2*n2)| < 1/T}.
```

Direct check and targeted leaf build (`3378/3378`) pass. All 18 public declarations audit to
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.
This closes only Theorem 4(i), the collision reduction. Heath--Brown Theorem 4(iii), its deep
collision/lattice estimate, and the residual Deshouillers--Iwaniec spectral cancellation remain
separate open inputs; no Route-E card is promoted on this brick alone.

### Sparse large values, brick 44 — weighted reverse collision comparison (2026-08-31)

`Sieve/HeathBrownSparseMeanValueReverse.lean` closes the converse comparison for nonnegative
coefficients. It proves the compact-triangle Parseval identity for arbitrary finite real
frequencies, then derives

```text
finiteFrequencyCollisionWeight_le_integral_Icc_nnreal
```

without a positivity premise by encoding coefficients in `NNReal`. For positive integer supports
the exact weighted collision mass is

```text
heathBrownPositiveWeightedCollision
  = sum_{m1,n1,m2,n2; |log(m1*n1)-log(m2*n2)|<1/T} q(n1)q(n2).
```

The two source-facing capstones prove the forward comparison for arbitrary unit sparse phases and
the reverse comparison when every sparse phase is `1`:

```text
integral_Icc_normSq_heathBrown_factors_le_weightedCollision
heathBrownPositiveWeightedCollision_le_integral_Icc_factors
```

Thus the normalized symmetric-window version of Heath--Brown Theorem 4(i) is two-sided with
explicit constants. Direct check and targeted leaf build (`3380/3380`) pass. All six public
declarations audit to `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without
an umbrella build. Theorem 4(iii) still requires Lemma 6's good/bad two-dimensional lattice
classification, divisor-coefficient control, and the final two-scale iteration.

### Sparse large values, brick 45 — exact bad-ray rescaling (2026-08-31)

`Sieve/HeathBrownSparseRayScaling.lean` formalizes the one-dimensional branch on pages 12--13 of
Heath--Brown's Lemma 6.  For a positive primitive direction `(u₁,u₂)`, it proves:

```text
card_heathBrownRayScales
    # {lambda > 0 : lambda*u₁ ≤ N and lambda*u₂ ≤ N}
      = floor(N / max(u₁,u₂))
abs_log_mul_rayScale_sub_log_mul_rayScale
    common positive scaling preserves the logarithmic collision displacement exactly
card_heathBrownRayScales_le_mul_succ
    #ray(N) ≤ (N/N₀) * (1 + #ray(N₀))
```

The endpoint loss is derived from Euclidean division; no real-interval counting premise remains.
Direct source check and targeted leaf build pass. All six public declarations audit to
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.
This closes the rescaling half of Lemma 6's bad-pair case.  Remaining work is the unconditional
two-dimensional good/bad classification and good-pair `O(N²/T)` count, then summation over sparse
pairs and the two-scale Theorem 4(iii) iteration.

### Sparse large values, brick 46 — primitive-direction Farey packing (2026-08-31)

`Sieve/HeathBrownFareyWindow.lean` replaces the reduced-basis counting part of Heath--Brown Lemma 6
by an exact reduced-direction formulation.  Primitive positive directions are Farey fractions;
the corpus's circle separation implies ordinary real separation, giving

```text
card_heathBrownFareyWindow_le
  # {a/q reduced : 1 ≤ a ≤ q ≤ Q, alpha ≤ a/q ≤ beta}
    ≤ (beta - alpha) Q² + 1.
```

No lattice basis or packing hypothesis remains.  Direct check, targeted leaf build, umbrella
wiring, and all-three-theorem axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`.  Together with brick 45 this closes the two elementary
components of Lemma 6: quadratic packing of nonexceptional primitive directions and exact
rescaling on one primitive ray.  Remaining work is their weighted exceptional-direction assembly
at the logarithmic collision window, followed by the two-scale Theorem 4(iii) iteration.

### Sparse large values, brick 47 — full primitive-square packing (2026-08-31)

`Sieve/HeathBrownPrimitiveWindow.lean` removes the artificial slope-at-most-one restriction from
brick 46.  A nonzero integral cross determinant separates two distinct positive primitive
directions of height at most `Q` by `Q⁻²`; consequently every real slope interval satisfies

```text
card_heathBrownPrimitiveWindow_le
  # {primitive (u₁,u₂) : max(u₁,u₂) ≤ Q, a ≤ u₁/u₂ ≤ b}
    ≤ (b-a)Q²+1.
```

Proof reuses corpus reduced-fraction uniqueness theorem.  No reduced-basis, orientation, or
packing premise remains.  Direct check, targeted leaf build, umbrella wiring, and four-theorem
axiom audit pass with only `[propext, Classical.choice, Quot.sound]`.

### Sparse large values, brick 48 — logarithmic collision-window count (2026-08-31)

`Sieve/HeathBrownPrimitiveLogWindow.lean` converts
`|log((m₁u₁)/(m₂u₂))| ≤ delta` into its exact exponential slope interval.  For
`0 < m₂ ≤ m₁` and `0 < delta ≤ 1`, corpus exponential-width estimate and brick 47 give

```text
card_heathBrownPrimitiveLogWindow_le
  # {primitive u : height(u) ≤ Q,
       |log((m₁u₁)/(m₂u₂))| ≤ delta}
    ≤ 4 delta Q²+1.
```

No logarithmic-window counting premise remains.  Direct check, targeted leaf build, umbrella
wiring, and four-theorem axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`.

### Sparse large values, brick 49 — weighted primitive-ray two-scale assembly (2026-08-31)

`Sieve/HeathBrownPrimitiveRayMass.lean` counts every positive multiple on every primitive
logarithmic collision ray.  Exact finite layer cake, low/high direction partition, Euclidean
quotient transport, brick 48, and corpus finite inverse-square bound yield

```text
cast_heathBrownPrimitiveLogRayMass_le_twoScale
  rayMass N ≤ 15 delta N²
    + (floor(N/N₀)+1) rayMass N₀
    + 2 floor(N/N₀)+1.
```

Exceptional-direction multiplicity is assembled with required `N/N₀` endpoint scale; `+1`
packing loss does not accumulate to `N`.  No exceptional direction, lattice basis, layer-cake,
or inverse-square premise is retained.  Direct source check, targeted leaf build (`9097/9097`),
umbrella wiring, and all-eleven-theorem axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`.

Remaining work: source-level reindexing of Heath--Brown's full sparse collision sum by these
primitive ray masses, summation over cofactor pairs with divisor coefficients, and Theorem
4(iii)'s iteration.  Proposition-2.2 routing, amplification, and Matomäki--Teräväinen Theorem 1.2
assembly remain downstream.

### Sparse large values, brick 50 — literal collision-square ray reindexing (2026-08-31)

`Sieve/HeathBrownPositiveCollisionRayReindex.lean` constructs the positive-pair/coprime-direction
gcd equivalence and restricts it to the literal bounded collision square.  It proves exactly

```text
# {(n₁,n₂) ∈ [1,N]² :
     |log(m₁n₁)-log(m₂n₂)| ≤ delta}
  = heathBrownPrimitiveLogRayMass N m₁ m₂ delta.
```

Combining this identity with brick 49 gives, for arbitrary positive cofactors `m₁,m₂`,

```text
collisionCount N ≤ 15 delta N²
  + (floor(N/N₀)+1) collisionCount N₀
  + 2 floor(N/N₀)+1.
```

Cofactor ordering is discharged internally by swapping dense coordinates.  No gcd decomposition,
primitive-ray partition, cofactor-ordering, or source-to-ratio conversion premise remains.  Direct
source check, targeted leaf build (`9098/9098`), umbrella wiring, and all-nineteen-theorem axiom
audit pass with only `[propext, Classical.choice, Quot.sound]` (two arithmetic inverse laws need
only `[propext, Quot.sound]`).

This closes source-level reindexing for unweighted full positive squares.  Remaining Theorem
4(iii) work is coefficient-weighted summation over actual dense supports and sparse cofactor pairs,
followed by iteration.  Proposition-2.2 routing, amplification, and Theorem 1.2 assembly remain.

### Sparse large values, brick 51 — aggregate and weighted two-scale mean value (2026-08-31)

`Sieve/HeathBrownSparseCollisionTwoScale.lean` sums brick 50 over every ordered sparse cofactor
pair and embeds arbitrary bounded positive dense supports into the closed full-square aggregate
`J(A,N,T)`.  It proves

```text
J(A,N,T) ≤ 15 N²|A|²/T
  + (floor(N/N₀)+1) J(A,N₀,T)
  + (2 floor(N/N₀)+1)|A|².
```

The corpus's existing `[0,1]`-weighted strict collision mass is at most `J(A,N,T)`.  Composing with
the exact sparse mean-value collision reduction gives a source-facing integral theorem for
`M(it)Q(it)` with the same two-scale aggregate.  Dense-support boundedness, `1 ≤ T`, and
`1 ≤ N₀ ≤ N` are the literal finite-range data; coefficient domination, strict-to-closed passage,
cofactor summation, gcd/ray decomposition, and all analytic estimates are discharged.

Direct source check and final targeted leaf build (`9101/9101`) pass.  All nine new public
theorems audit to only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without
an umbrella build.  This closes the finite Heath--Brown Lemma 6/Theorem 4(iii) comparison core.
Remaining Route-E work is its paper-specific iterative parameter substitution into Proposition
2.2, residual Watt/DI scale routing, amplification, and Matomäki--Teräväinen Theorem 1.2 assembly.

### Sparse large values, brick 52 — integral two-scale recurrence (2026-08-31)

`Sieve/HeathBrownSparseMeanValueTwoScale.lean` closes the smaller aggregate in brick 51 by the
same physical mean square at half-height.  The full positive interval `[1,N₀]` with unit weights
contains every closed collision of logarithmic width `1/T` as a strict collision of width `2/T`.
The existing reverse finite-frequency theorem therefore gives

```text
J(A,N₀,T) ≤ (5/(2T)) I(T/2; A, [1,N₀]).
```

Substitution into brick 51 produces the fully integral recurrence

```text
I(T; A,B) ≤ (5π/2)T * (
    15 N²|A|²/T
  + (floor(N/N₀)+1) (5/(2T)) I(T/2; A,[1,N₀])
  + (2 floor(N/N₀)+1)|A|²).
```

The natural-to-positive lift, full positive interval, unit-coefficient cardinality identity,
closed-to-strict half-height embedding, reverse mean-value comparison, and recurrence composition
are all discharged in Lean.  No smaller-scale collision aggregate, positivity conversion, or
analytic premise remains.  Direct source check and targeted leaf build (`9102/9102`) pass; all
seven new theorem declarations audit to only `[propext, Classical.choice, Quot.sound]`.  Module is
umbrella-wired without an umbrella build.

Remaining Route-E work is paper-specific iteration/parameter substitution into Proposition 2.2,
residual Watt/DI scale routing, amplification, and Matomäki--Teräväinen Theorem 1.2 assembly.

### Sparse large values, brick 53 — Cauchy/divisor square lift (2026-08-31)

`Sieve/HeathBrownSparseMeanValueSquareLift.lean` formalises the square-lift step used in
Heath--Brown's Theorem 4(iii).  It constructs the natural-number sparse factor, proves its
ordinary mean-square bound with support height and integration height kept separate, identifies
the square of the full unit interval with divisor-fibre coefficients, and normalises those
coefficients by the corpus divisor bound.  For arbitrary dense coefficients in `[0,1]`, it also
proves domination by unit coefficients on the same support.  The capstone is the squared Cauchy
estimate

```text
I(T; A,[1,N])²
  ≤ MS(T; A) · divisorScale(N,η)² · (25π/8) · I(T; A,[1,N²]),
```

with coefficient bounds, divisor-fibre counting, reconstruction, continuity, integrability, and
Cauchy--Schwarz discharged internally.  No supplied coefficient, divisor, continuity, or analytic
premise remains.  Direct source check and targeted leaf build (`9107/9107`) pass; all thirty new
declarations audit to only `[propext, Classical.choice, Quot.sound]`.  Module is umbrella-wired
without an umbrella build.

Remaining Heath--Brown work is exact one/two-step recurrence iteration, integer parameter choice
and exponent absorption yielding Theorem 4(iii), then Proposition-2.2 routing, amplification, and
Matomäki--Teräväinen Theorem 1.2 assembly.

### Sparse large values, brick 54 — closed one-step self-bound (2026-08-31)

`Sieve/HeathBrownSparseMeanValueSelfBound.lean` combines bricks 52 and 53 into a closed estimate.
It constructs zero coefficients embedding `[1,K²]` into `[1,N]`, proves symmetric height-window
monotonicity, proves nonnegativity of the explicit sparse mean-square envelope, and solves the
resulting scalar system

```text
I ≤ a + bJ,     J² ≤ kI
```

as `I ≤ 2a+b²k`.  Its capstone instantiates `a`, `b`, and `k` with the exact recurrence,
half-height, divisor scale, and explicit constants from the preceding modules whenever `K²≤N`.
All coefficient, analytic, interval-extension, positivity, and quadratic-solver premises are
discharged.  Direct source check and targeted leaf build (`9108/9108`) pass; all nine declarations
audit to only `[propext, Classical.choice, Quot.sound]`.  Module is umbrella-wired without an
umbrella build.

Remaining Heath--Brown work is integer scale selection and exponent simplification for the first
branch, the paper's second recurrence branch, and their exact Theorem 4(iii) union.  Proposition-
2.2 routing, amplification, and Matomäki--Teräväinen Theorem 1.2 assembly then remain.

### Sparse large values, brick 55 — exact natural square-root scale (2026-08-31)

`Sieve/HeathBrownSparseMeanValueSqrtScale.lean` selects `K=Nat.sqrt N` inside brick 54, proving
internally that `K²≤N` and `N/K≤K+2`.  It simplifies the closed one-step bound to the three exact
terms

```text
75π N²R²
+ 5π T (2⌊√N⌋+5) R²
+ ((25π/4)(⌊√N⌋+3))² · k,
```

where `k` is the explicit half-height sparse envelope times the squared divisor scale and the two
comparison constants.  No integer-rounding or quotient estimate remains as a hypothesis.  Direct
source check, targeted leaf build (`9109/9109`), and three-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

### Sparse large values, brick 56 — coefficient-faithful two-step closure (2026-08-31)

`Sieve/HeathBrownSparseMeanValueIteration.lean` closes the paper's second recurrence iteration
without duplicating brick 54.  For arbitrary sparse phases and arbitrary dense `[0,1]`
coefficients, the outer recurrence lands at the half-height unit interval of length `N₀`; its
divisor square lift lands at `N₀²`, where brick 54's existing self-bound closes the inner mean
square.  The resulting theorem

```text
integral_Icc_normSq_heathBrown_factors_le_twoStepSelfBound
```

has no analytic, coefficient, support, rounding, or inner-integral premise.  Direct source check
and targeted leaf build (`9109/9109`) pass; the declaration audits to only
`[propext, Classical.choice, Quot.sound]`.  Module is umbrella-wired without an umbrella build.

Remaining Heath--Brown work is divisor-scale/rpow absorption, exact integer regime parameters,
and the Theorem 4(iii) branch union.  Proposition-2.2 routing and amplification remain downstream.

### Sparse large values, brick 57 — first-branch divisor/rpow absorption (2026-08-31)

`Sieve/HeathBrownSparseMeanValueFirstBranch.lean` proves the cast natural root lies below the real
root and bounds the square-root divisor scale by `divisorBoundConst η · N^η`.  Substitution into
brick 55 removes every floor and divisor-normalizer artifact, giving

```text
I ≤ 75π N²R² + 35π T√N R²
  + (25π)² N · ((5πe+5π/4)TR)
      · ((divisorBoundConst η·N^η)²(25π/8)²).
```

The support condition is the source theorem's literal `m≤T`; no auxiliary analytic or rounding
premise remains.  Direct check, targeted leaf build (`9110/9110`), and three-declaration axiom
audit pass with only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without
an umbrella build.

Remaining Heath--Brown work is regime absorption for this branch and exact integer parameter
algebra for brick 56's coefficient-faithful two-step branch, followed by Theorem 4(iii) union.

### Sparse large values, brick 58 — explicit first-regime absorption (2026-08-31)

`Sieve/HeathBrownSparseMeanValueFirstBranchRegime.lean` consumes brick 57 and proves the exact
first-branch estimate under `T√N≤N²`.  Its only new step absorbs the residual `35πT√N R²` into
the diagonal budget, yielding

```text
I ≤ 110π N²R²
  + (25π)² N · ((5πe+5π/4)TR)
      · ((divisorBoundConst η·N^η)²(25π/8)²).
```

Direct source check and targeted leaf build (`9111/9111`) pass; the declaration audits to only
`[propext, Classical.choice, Quot.sound]`.  Module is umbrella-wired without an umbrella build.

Remaining Heath--Brown work is deriving this explicit branch condition from the paper's published
regime, exact integer parameter algebra for brick 56's two-step branch, and Theorem 4(iii) union.

### Sparse large values, brick 59 — arbitrary positive recurrence scale (2026-08-31)

`Sieve/HeathBrownSparseMeanValueArbitraryScale.lean` removes the accidental formal restriction
`N₀≤N` from bricks 51--52.  The source's Lemma 6 allows every positive `N₀`: when `N₀≤N` the
existing primitive-ray decomposition applies, while for `N<N₀` the closed collision support at
length `N` embeds directly into the support at length `N₀`.  The resulting aggregate and integral
recurrences therefore require only `1≤N₀`.  Brick 56 now consumes this unrestricted recurrence,
so its coefficient-faithful two-step bound also accepts every positive auxiliary scale.

Direct source checks and targeted leaf builds (`9103/9103`, `9110/9110`) pass.  Five new
declarations and the generalized brick-56 theorem audit to only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

Remaining Heath--Brown work is exact integer realization of
`max(T^(1/3),(RT)^(1/4))`, exponent absorption in the second branch, and Theorem 4(iii) union.

### Sparse large values, brick 60 — published first-regime bridge (2026-08-31)

`Sieve/HeathBrownSparseMeanValueFirstBranchPublishedRegime.lean` proves directly that
`T^(2/3)≤N` implies the exact brick-58 condition `T√N≤N²`.  Cubing the published inequality gives
`T²≤N³`; squaring both nonnegative sides then closes the square-root comparison.  Its capstone
instantiates brick 58, removing the explicit algebraic regime hypothesis from the first branch.

Direct source check and targeted leaf build (`9112/9112`) pass; both declarations audit to only
`[propext, Classical.choice, Quot.sound]`.  Module is umbrella-wired without an umbrella build.

Remaining Heath--Brown work is exact integer realization and exponent absorption for the
coefficient-faithful two-step branch, followed by Theorem 4(iii) union.

### Sparse large values, brick 61 — real-ratio recurrence and canonical second scale (2026-08-31)

`Sieve/HeathBrownPrimitiveRayMassRealScale.lean` proves the source-faithful primitive-ray
coefficient `2N/N₀`, including the previously missing case `N<N₀`.  Its aggregate and integral
lifts in `HeathBrownSparseMeanValueRealScale.lean`, followed by
`HeathBrownSparseMeanValueRealIteration.lean`, give the exact real-ratio two-step recurrence for
every positive auxiliary scale.  `HeathBrownSecondScaleParameters.lean` constructs
`⌈max(T^(1/3),(RT)^(1/4))⌉₊`, proves its rounding bounds, proves its square reaches `T^(2/3)`, and
derives `R≤T` from positive-natural support.  `HeathBrownSparseMeanValueSecondScale.lean`
instantiates the recurrence at this canonical scale, discharging all selection premises.

Direct source checks and targeted leaf builds (`9098/9098`, `9104/9104`, `9111/9111`,
`9111/9111`, `9115/9115`) pass.  All eighteen new declarations audit to only
`[propext, Classical.choice, Quot.sound]`; all modules are umbrella-wired without an umbrella
build.

Remaining Heath--Brown work is explicit constant/rpow absorption for this selected-scale bound
and union with brick 60 into exact Theorem 4(iii).

### Sparse large values, brick 62 — exact Heath--Brown Theorem 4(iii) (2026-08-31)

`Sieve/HeathBrownSecondScaleAlgebra.lean` proves the canonical-scale cube, inverse-quarter-power,
cardinality crossover, height ceiling, and quartered divisor-loss inequalities.
`HeathBrownSparseMeanValueTheoremFourAlgebra.lean` absorbs the complete two-step square-root
expression into the published monomials.  `HeathBrownSparseMeanValueTheoremFour.lean` then proves,
for arbitrary sparse circle phases and arbitrary dense coefficients in `[0,1]`,

```text
I ≤ (95π/2) N²R²
  + Cη (NT)^η (NRT + N R^(7/4) T^(3/4)),
```

with explicit `Cη`.  Empty support and `N=0`, canonical scale selection, all rounding, divisor
loss, and exponent algebra are discharged internally.  Second-scale estimate works in all
regimes, so no branch hypothesis survives.

Direct source checks and targeted leaf builds (`9116/9116`, `9117/9117`, `9118/9118`) pass.  All
ten declarations audit to only `[propext, Classical.choice, Quot.sound]`; capstone is
umbrella-wired without an umbrella build.

Remaining programme gate is Proposition-2.2 scale routing, amplification, and final
Matomäki--Teräväinen Theorem 1.2 assembly.

### Sparse large values, brick 63 — literal Matomäki--Teräväinen Lemma 3.4 (2026-08-31)

`Sieve/HeathBrownSparseMeanValueBounded.lean` extends Theorem 4(iii) from circle-valued sparse
phases to arbitrary complex coefficients of modulus at most one and discharges the compact range
`1 ≤ T < 2`.  `HeathBrownSparseMeanValueBoundedRefined.lean` proves the published deletion of the
mixed `R^(7/4)T^(3/4)` term under either `T^(2/3) ≤ N` or `R ≤ T^(1/3)`: the first regime uses
Heath--Brown's independent square-root branch, while the second absorbs the mixed term directly.

`Sieve/HeathBrownSparseMeanValueLemma34.lean` performs the exact one-line normalization.  It keeps
both reciprocal weights, arbitrary real dense coefficients, the dyadic support `N < n ≤ 2N`, and
the source support `M ≤ m ≤ T`; constructs `max_n |a_n|` internally; discharges empty support,
zero maximum, sign splitting, continuity, and the range `1 ≤ T < 2`; and proves both (3.1) and its
published mixed-term deletion refinement with explicit constants.  No coefficient-sign,
nonemptiness, height-two, normalization, or analytic premise survives.

Direct source checks and targeted leaf builds (`9124/9124`, `9125/9125`) pass.  The focused
seventeen-declaration axiom audit reports only `[propext, Classical.choice, Quot.sound]`; the
capstone is umbrella-wired without an umbrella build.

Heath--Brown/Matomäki--Teräväinen Lemma 3.4 is therefore closed.  Remaining Theorem 1.2 work is
the genuine Lemma 3.5 Type I and Type I/II analytic cancellation, its routing/amplification, and
the final all-interval assembly; Proposition 2.2 bookkeeping and Type II are already closed.

### Lemma 3.5 support and energy sharpening, bricks 64--66 (2026-09-02)

`Sieve/MatomakiTeravainenLemma35ConstructedRange.lean` unions every already constructive
Deshouillers--Iwaniec regime and discharges the height comparisons internally.  It makes the
remaining uncovered small-`A`, product-long Type I / Type I--II region exact rather than hiding it
behind a generic envelope hypothesis.

`Sieve/MatomakiTeravainenPrimeAmplifierSupport.lean` proves the literal powered-prime amplifier's
support law.  Every nonzero coefficient has an ordered prime tuple; unique factorization sends it
injectively to an unordered multiset.  Consequently the raised support has at most
`choose(P + ell - 1, ell)` elements, with zero and empty cases discharged.

`Sieve/PrimePowerFactorialEnergy.lean` strengthens the generic prime-supported convolution fibre
bound from `ell ^ ell` to `ell!`: a product fibre consists only of permutations of one certified
prime multiset.  `Sieve/MatomakiTeravainenPrimeAmplifierFactorialEnergy.lean` specializes this to
the complete amplifier and every literal Watt block,

```text
sum |a_ell(m)|^2 <= ell! * P^ell,
```

and recovers the existing source-scale `rpow` estimate through `ell! <= ell^ell`.  Direct checks
pass; targeted leaf build (`11129/11129`) passes.  All new public endpoints audit to only
`[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired without an umbrella build.

These bricks optimize and close exact combinatorial support/energy infrastructure.  They do not
close Lemma 3.5: the paper's small-`A`, product-long Type I and Type I--II ranges still require
genuine spectral twisted-moment cancellation absent from the current corpus.  Therefore the
cofactor-amplified `E_3` card remains in stage 2; no conditional endpoint or hypothesis-bearing
substitute is promoted.

### Lemma 3.5 Heath--Brown specialization, bricks 67--69 (2026-09-02)

`Sieve/MatomakiTeravainenPrimeAmplifierSparseMass.lean` and
`Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownSupport.lean` package every literal powered-prime
Watt block as a positive-integer sparse support.  The coefficient normalization is exactly
`1/ell!`, its norm is at most one, and its one-line Heath--Brown factor is exactly `1/ell!` times
the literal Watt coefficient block.  The support satisfies both the sharp stars-and-bars law and
the Brun--Titchmarsh envelope for `ell! * card support`.

`Sieve/MatomakiTeravainenWattUnitSquareHeathBrown.lean` identifies every coefficient of the
squared reciprocal unit block with an ordered supported factor-pair count divided by its anchor.
The raw count is divisor-bounded.  Since products from `(N,N']^2` occupy `(N^2,4N^2]` when
`N'<=2N`, the module proves an exact, disjoint two-dyadic decomposition; coefficients below
`N^2` and above `N'^2` vanish internally.  Thus no false one-dyadic support premise is retained.

`Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownMoment.lean` applies the already-closed literal
Lemma 3.4 to both dyadic pieces, recombines them with the sharp two-term norm-square inequality,
undoes the factorial normalization, replaces both dense maxima by the divisor scale, and converts
the symmetric set integral to the literal positive interval.  Its source-facing endpoint is

```text
intervalIntegral_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_divisorScale
```

for the exact powered-prime amplifier, with no analytic, coefficient, support, continuity,
integrability, or dyadic-decomposition premise.  Direct checks and targeted leaf builds
(`11172/11172`, `11176/11176`) pass.  A focused 41-declaration audit across bricks 64--69 reports
only `[propext, Classical.choice, Quot.sound]`; all new leaves are umbrella-wired without an
umbrella build.

This constructs the proposed non-automorphic Lemma 3.4 replacement at the literal Watt moment.
Remaining work is exact scalar absorption of the factorial-weighted sparse-card and divisor
envelopes into the Lemma 3.5 Type-I/Type-I--II budgets, then Proposition-2.2 routing,
amplification, and Theorem 1.2 assembly.  Card remains stage 2 until those comparisons are closed.

### Energy-faithful Type-I replacement, bricks 70--73 (2026-09-02)

`Sieve/MatomakiTeravainenPrimeAmplifierIntegralEnergy.lean` proves the exact multiplicity law

```text
convPow primeIndicator j = #(supported ordered prime-product fibre over j).
```

Hence every nonzero raised coefficient is a positive natural number, each supported anchor
contributes at least one unit of squared energy, and every literal block satisfies both
`card support <= exact block energy` and `card support <= B`.  This is the missing direction that
allows a sparse-cardinality mean value to retain the coefficient energy required by Lemma 3.5.

`Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownEnergyMoment.lean` uses those inequalities to
linearize all three Heath--Brown support monomials.  Its capstone bounds the literal mixed Watt
moment by an explicit scalar times the exact block energy; no support statistic sits outside that
energy factor.

`Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownBTMoment.lean` replaces the remaining support
statistics by the factorial Brun--Titchmarsh envelope and `R <= B`.
`Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownSqrtBTMoment.lean` selects the canonical sieve
level `sqrt P`, using `bt_error_le_main` to obtain the source-only base

```text
292 P / log P + 1 + ell.
```

Thus the mixed-moment coefficient now contains only `P, ell, B, N, N', T, eta` and explicit
constants.

Finally, `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownMoment.lean` inserts this moment
into the restricted Type-I Cauchy receiver.  It constructs the fixed-block cover and amplifier
lower bounds internally and reduces every block-height clause to the single complete-support
condition

```text
((2 * P)^ell : R) <= T.
```

Direct source checks and targeted leaf builds (`11172/11172`, `11178/11178`, `11179/11179`,
`11181/11181`, `11179/11179`) pass.  A focused audit of all 27 public declarations reports only
`[propext, Classical.choice, Quot.sound]`; leaves are umbrella-wired without an umbrella build.

Remaining gate is now explicit exponent arithmetic: discharge `((2P)^ell)<=T` from the Section
5.1 schedule and absorb the canonical `292P/log P + 1 + ell`, factorial, divisor, and small-power
terms into the published Type-I budget.  Proposition-2.2 routing, amplification, and Theorem 1.2
assembly remain downstream.  No spectral, automorphic, coefficient, support, or analytic premise
has been introduced.

### Source-scale Type-I absorption and height dichotomy, bricks 74--80 (2026-09-02)

Seven unconditional leaves discharge that explicit schedule and coefficient debt:

- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSourceScale.lean` proves uniformly on the
  paper exponent interval that the rounded prime scale satisfies `P <= X^(1/10)` and hence
  `P <= T^(2/5)` from `X^(1/4) <= T`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownCanonicalMoment.lean` repairs the receiver
  linkage to the square-root Brun--Titchmarsh coefficient.  Its source-degree reserve absorbs
  `ell!`, `(ell!)^2`, and the complete canonical base `292P/log P + 1 + ell` on every literal
  powered-prime block once `294 ell <= P`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownDegreeDeficit.lean` proves that reserve
  eventually and uniformly from the actual lower exponent `10999/10000`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownAbsorbedSourceMoment.lean` combines those
  facts with the source schedule, so prime rounding, degree, complete-support height, factorial,
  exact sparse support, and Brun--Titchmarsh hypotheses are constructed internally;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerMoment.lean` charges the remaining
  square-divisor and dyadic-product losses to a fixed coefficient times `T^(12 eta)`.  Choosing
  `eta = epsilon/24` gives the exact published power `T^(epsilon/2)`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerSourceMoment.lean` installs that
  epsilon coefficient in the source-scale receiver;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeightDichotomy.lean` removes the last caller-supplied
  comparison between unit-block length and height: `N <= T` selects the new Heath--Brown bound,
  while its complement supplies `T <= N` to the existing elementary affine receiver.

Direct checks pass.  Targeted final leaf build
`GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeightDichotomy`
passes (`11192/11192`).  Focused audit of the 27 new theorem declarations reports only
`[propext, Classical.choice, Quot.sound]`; every leaf is umbrella-wired without an umbrella build.

Card remains stage 2.  Type-I source-scale schedule and height routing are now closed, but the
literal Section-5.1 scalar comparison with the amplifier threshold and long-factor energy,
Proposition-2.2 Type-I routing, amplification, and final all-interval Theorem 1.2 assembly remain.

### Exact threshold-layer Type-I replacement, bricks 81--85 (2026-09-02)

The prior coefficient-energy collapse was too coarse: it erased the powered-block denominator and
therefore could not retain the small source saving used in Section 5.1. Seven unconditional
modules replace that step without changing the amplifier:

- `Sieve/MatomakiTeravainenPrimeAmplifierLayerCake.lean` writes every positive integral raised
  coefficient as sum of unit threshold layers, proves exact coefficient identity, and bounds total
  layer mass by `P^ell`;
- `MatomakiTeravainenPrimeAmplifierHeathBrownLayerMoment.lean` applies literal Lemma 3.4 to each
  layer and recombines them by finite `L²` Minkowski, retaining both `B²` denominators;
- `MatomakiTeravainenPrimeAmplifierHeathBrownLayerScalar.lean` uses finite Jensen at exponents
  `1/2` and `7/8` to collapse layers to exact factorial powers;
- `MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerReceiver.lean` inserts that sharp symmetric
  mixed moment into restricted Type-I Cauchy receiver;
- `MatomakiTeravainenPrimeAmplifierHeathBrownLayerCanonical.lean` proves canonical block
  cancellation from `ell! <= P^ell <= B`;
- `MatomakiTeravainenPrimeAmplifierHeathBrownLayerSourceScalar.lean` keeps sharper source law
  `ell! <= (P^ell)^(1/alpha)`, recovering exact negative powers
  `(P^ell)^(-(1-1/alpha)/2)` and `(P^ell)^(-(1-1/alpha)/8)`;
- `MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceReceiver.lean` constructs source base,
  degree, powered threshold, complete-support height, and source-large-set identity internally.

Direct checks and targeted leaf builds pass. Focused axiom audit of all 26 new theorem
declarations reports only `[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired
without umbrella build.

Remaining Type-I work is height/exponent comparison of this now-sharp source root with long-factor
energy and Proposition-2.2 piece scales, followed by amplification and final Theorem 1.2 assembly.
No hypothesis-bearing endpoint has been promoted.

### Exact source density and uniform amplifier decay, bricks 86--94 (2026-09-02)

The sharp threshold-layer chain now reaches a source-only power envelope without losing the
prime-tuple density:

- `MatomakiTeravainenPrimeAmplifierHeathBrownLayerSourceHeight.lean` and its receiver pay both
  square-product roots and the square-divisor scale by the literal height while retaining the
  exact ordered-prime mass divided by `P^ell`;
- the long-energy, divisor-energy, and long-power leaves replace the remaining fourth moment by
  the unconditional affine envelope, the literal fixed divisor majorant, and finally an arbitrary
  fixed positive height power;
- the layer scalar was corrected to retain
  `card(mtTypeIPrimeCoeffSupport P)^ell / P^ell`, rather than the coarse leading constant `1`;
- `MatomakiTeravainenPrimeAmplifierLayerPrimeDensity.lean` applies the literal square-root
  Brun--Titchmarsh bound to prove this ratio is at most `2^(-ell)`, then uses the exact source
  degree and `log log(X)^7 / log(X) -> 0` to obtain

  ```text
  card(mtTypeIPrimeCoeffSupport P)^ell / P^ell
    <= exp(-(log(log X))^6).
  ```

- `MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceDensity.lean` inserts that density
  into the full long-power receiver;
- `MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourcePowerDecay.lean` discharges the
  variable exponents uniformly.  From `alpha >= 10999/10000` it proves
  `9/100 <= 1 - 1/alpha`; the exact power window `T^(1/10) <= P^ell` then gives the two literal
  bounds `T^(-9/2000)` and `T^(-9/8000)`.

Direct checks pass. Targeted leaf builds through the power-decay receiver pass (`11274/11274`).
Focused audits of all new and strengthened declarations report only
`[propext, Classical.choice, Quot.sound]`; leaves are umbrella-wired without an umbrella build.

Card remains stage 2. Remaining Type-I debt is now the exact Proposition-2.2 product-scale
substitution for the long/unit factors and absorption of the resulting fixed constants and powers
into the paper's `exp(-(log log X)^6)` budget. Type-I/II routing, amplification, and all-interval
Theorem 1.2 assembly remain downstream.

### One-unit coefficient-faithful Type-I lane, bricks 95--98 (2026-09-02)

Four unconditional leaves build the complementary one-unit route:

- `MatomakiTeravainenTypeIPrimeAmplifierOneUnitMoment.lean` inserts the existing unconditional
  one-unit second-derivative moment into the exact powered-prime amplifier cover, retaining literal
  coefficient energy and avoiding factorial normalization;
- `MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceMoment.lean` constructs prime scale, raising
  degree, every block-height comparison, and equation `(5.4)` energy on the source schedule;
- `MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceLongEnergy.lean` reduces the long fourth
  moment to exact dyadic coefficient energy;
- `MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceLongPower.lean` installs the fixed divisor
  envelope and absorbs its polylogarithm into `T^(epsilon/100)`.

Direct checks pass. Targeted final leaf build passes (`11211/11211`). Focused audit of all eight
new theorem declarations reports only `[propext, Classical.choice, Quot.sound]`; final leaf is
umbrella-wired without an umbrella build.

Exponent audit changes the frontier. Threshold-layer density is subpower and cannot offset the
long fourth-moment root on the middle Type-I product scales. The one-unit lane likewise does not
recover the `T/N^2`-strength saving in the paper's Deshouillers--Iwaniec Lemma 3.5(ii). Thus exact
Proposition-2.2 substitution cannot close from current elementary moments. Remaining primitive is
genuine modulus-average spectral cancellation, or a source-specific theorem of equal strength;
only after it is closed can Type-I routing, amplification, and Theorem 1.2 assembly proceed. No
analytic premise has been added.

### Signed modulus-average spectral carrier, bricks 99--101 (2026-09-02)

The cancellation-bearing object is now explicit and unconditional:

- `KloostermanModulusBilinear.lean` retains complex relative phases by summing complete
  Kloosterman bilinear forms over moduli before taking norms. Its expansion and sharp elementary
  fixed-modulus/direct-sum baselines are proved;
- `KloostermanHybridModulusBilinear.lean` inserts two physical-height additive Dirichlet vectors,
  with continuity and pointwise baselines;
- `KloostermanHybridModulusLinear.lean` inserts one physical-height vector against a fixed residue
  vector and proves the exact integrated non-spectral baseline from the existing hybrid large
  sieve.

Direct checks and targeted builds pass (`8941/8941`, `9229/9229`, `9230/9230`). Focused axiom
audit of all 12 new declarations reports only `[propext, Classical.choice, Quot.sound]`; final leaf
is umbrella-wired without an umbrella build.

This closes representation and baseline infrastructure, not spectral saving. The next primitive
must improve the signed modulus sum itself via genuine Kuznetsov--Deshouillers--Iwaniec
cancellation. Positive per-modulus square energy cannot supply that theorem because it discards
cross-modulus phases. No interface premise or conditional endpoint has been introduced.

### Shared-coefficient adjoint carrier, brick 102 (2026-09-02)

`KloostermanHybridModulusAdjoint.lean` proves additive-hybrid height/frequency conjugation,
Kloosterman bilinear symmetry, exact adjoints before and after the signed modulus sum, and the
time-reflection adjoint of the shared-coefficient hybrid amplitude. The source sequence is now
literally common across every modulus rather than hidden in an arbitrary modulus-indexed family.

Direct check and targeted build pass (`9231/9231`). All eight theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.
This prepares an exact orthogonality audit of the shared specialization. No analytic premise has
been introduced.

### Two-sided additive-hybrid collapse, brick 103 (2026-09-02)

`KloostermanSharedHybridCollapse.lean` proves that feeding additive Fourier transforms into both
legs of the complete Kloosterman bilinear form removes the Kloosterman kernel exactly. The result
is modulus squared times an inverse-residue correlation, and the signed modulus family is the sum
of those correlations.

Direct check and targeted build pass (`9233/9233`). All five theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

This closes a false spectral direction. Two-sided shared additive-hybrid input cannot supply the
missing Kuznetsov saving. The correct remaining carrier must keep one residue leg non-Fourier (or
return to the generic signed Kloosterman bilinear form) while sharing the physical arithmetic
coefficients across moduli. No conditional estimate has been introduced.

### Physical-residue carrier and integer modulus kernel, bricks 104--105 (2026-09-02)

`KloostermanPhysicalResidueModulusBilinear.lean` uses shared physical residue fibres rather than
additive Fourier vectors. Fibrewise expansion recovers the literal classical Kloosterman bilinear
sum on ordinary Dirichlet indices, so the complete kernel survives. Continuity and the exact
fixed-modulus operator baseline are closed.

`KloostermanIntegerModulusKernel.lean` then moves the signed modulus sum inside both coefficient
sums. It defines the ordinary-integer kernel `sum_q w_q S(m,n;q)`, proves its symmetry,
conjugation, and totient baseline, and identifies the full physical-height carrier as its finite
bilinear form.

Direct checks and targeted builds pass (`9234/9234`, `9235/9235`). All nine theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; final leaf is umbrella-wired without
umbrella build.

Remaining primitive is now exact: prove a Kuznetsov--Deshouillers--Iwaniec operator bound for this
signed integer-index kernel with the paper's modulus weights and ranges, then route it into the
source Type-I moment. No arbitrary modulus-indexed coefficient family and no conditional spectral
interface remains.

### Finite signed-kernel operator receiver, brick 106 (2026-09-02)

`KloostermanIntegerKernelOperator.lean` defines the finite transform and bilinear form of the
ordinary-index signed modulus kernel. Cauchy--Schwarz reduces the bilinear square to transform
output energy; a second Cauchy step gives the exact Hilbert--Schmidt energy, and the totient bound
exposes the complete elementary cardinality loss. The literal physical-height carrier is proved
equal to this operator on `Icc 1 N` and `Icc 1 M`.

Direct check and targeted build pass (`9236/9236`). All seven theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Remaining primitive is no longer representational: replace this proved Hilbert--Schmidt/totient
baseline by the quantitative Kuznetsov--Deshouillers--Iwaniec output-energy bound required by
Lemma 3.5(ii), with all ranges discharged internally.

### Exact Gram and off-diagonal frontier, brick 107 (2026-09-02)

`KloostermanIntegerKernelGram.lean` proves the Hermitian Gram expansion of signed-kernel transform
energy and splits it exactly into diagonal plus erased-index off-diagonal. The diagonal is proved
equal to a nonnegative weighted sum of literal kernel row energies.

Direct check and targeted build pass (`9237/9237`). All five theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

The remaining Kuznetsov input is precisely a bound for
`kloostermanIntegerKernelGramOffDiagonal` on the paper's supports and modulus weights. Everything
needed to turn such a proved bound into output energy and the Type-I receiver is already closed;
no hypothesis-bearing interface has been added.

### Cross-modulus correlation expansion, brick 108 (2026-09-02)

`KloostermanCrossModulusCorrelation.lean` expands a Gram entry as a weighted double modulus sum of
literal incomplete correlations
`sum_m conj(S(m,n;q)) S(m,k;r)`. It proves Hermitian symmetry and the exact equal/distinct-modulus
split.

Direct check and targeted build pass (`9238/9238`). All three theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Next analytic layer is completion and cancellation for these explicit correlations. Distinct
moduli and off-diagonal input indices are now separate finite objects; neither estimate is encoded
as a premise.

### Complete equal-modulus correlation, brick 109 (2026-09-02)

`KloostermanCompleteColumnCorrelation.lean` proves

```text
sum_m conj(S(m,n;q)) S(m,k;q) = q S(0,k-n;q),
```

and hence diagonal energy `q phi(q)`, using only finite additive-character orthogonality.

Direct check and targeted build pass (`9239/9239`). Both theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Remaining correlation problem is now incomplete-window completion plus distinct moduli. The full
equal-modulus period no longer belongs to the analytic frontier.

### Complete-column Ramanujan arithmetic, brick 110 (2026-09-02)

`KloostermanCompleteColumnRamanujan.lean` proves the exact identities

```text
complete column correlation = q * CGL Ramanujan coefficient
                            = q * gcd--Möbius divisor sum,
```

then bounds its norm unconditionally by `q` times the corresponding positive divisor sum.

Direct check and targeted build pass (`12570/12570`). All three public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Next analytic layer remains completion of finite output windows and distinct-modulus correlation
cancellation. No hypothesis-bearing large-sieve or Kuznetsov interface has been introduced.

### Same-modulus interval completion, brick 111 (2026-09-02)

`KloostermanSameModulusIntervalCompletion.lean` proves exact residue grouping on `[1,M]`, splits
each multiplicity as `M/q` plus a discrepancy of absolute value at most one, and obtains

```text
interval column correlation
  = (M/q) * complete Ramanujan column correlation + remainder,
norm remainder <= q * phi(q).
```

The remainder bound uses the exact Kloosterman second moment twice and finite Cauchy--Schwarz, not
the pointwise totient bound. It is instantiated directly for the existing stored-modulus Gram
correlation. Direct check and targeted build pass (`12571/12571`). All nine public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Equal-modulus incomplete-window arithmetic is now closed. Distinct-modulus completion and
cancellation are the remaining Kloosterman core before source Lemma 3.5(ii) routing.

### Distinct-modulus complete correlation and interval remainder, brick 112 (2026-09-02)

`KloostermanDistinctModulusCompleteCorrelation.lean` proves that the complete product-period
correlation of Kloosterman columns at two distinct positive moduli vanishes exactly. It groups the
literal interval `[1,M]` by product-period residues, deletes this zero complete main term, and
identifies the entire distinct-modulus correlation with an explicit boundary-discrepancy remainder.
Finite Cauchy--Schwarz and the exact complete Kloosterman second moment then give

```text
norm remainder <= q*r*(phi(q)+phi(r))/2,
```

together with a weaker elementary totient-product bound and direct instantiations for the stored
`q+1`, `r+1` Gram correlation.

Direct check and targeted build pass (`12572/12572`). All thirteen public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

The complete-period distinct-modulus main is closed unconditionally. Remaining genuine core is
quantitative cancellation for the incomplete discrepancy remainder at the source ranges, then
Lemma 3.5(ii) routing; no correlation estimate is assumed.

### Least-common-multiple completion, brick 113 (2026-09-02)

`KloostermanDistinctModulusLcmCompletion.lean` proves that the product-period correlation consists
of exactly `gcd(q,r)` repeated least-common-multiple periods. Since the former vanishes for unequal
positive moduli, the complete correlation already vanishes on the sharp common period
`lcm(q,r)`. The literal interval correlation is therefore an exact lcm-residue discrepancy, and
the exact lcm-period column energies give

```text
norm remainder <= lcm(q,r)*(phi(q)+phi(r))/2.
```

This improves brick 112 by the full common-divisor factor and is instantiated directly for the
stored `q+1`, `r+1` Gram correlation. Direct check and targeted build pass (`12573/12573`). All
nine public theorem declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf
is umbrella-wired without umbrella build.

Remaining analytic core is cancellation inside the incomplete lcm-period boundary at the source
ranges, followed by Lemma 3.5(ii) routing; no estimate is assumed.

### Exact terminal common-period block, brick 114 (2026-09-02)

`KloostermanDistinctModulusTerminalBlock.lean` proves the exact periodic division law behind the
sharp completion. For unequal positive moduli, every full lcm block in `[1,M]` erases and

```text
cross correlation on [1,M]
  = sum_{0 <= i < M mod lcm(q,r)} conj(S(i+1,n;q)) S(i+1,k;r).
```

Thus the analytic survivor is a literal consecutive terminal block of exact length
`M mod lcm(q,r)`, not an opaque discrepancy vector. The module also proves the corresponding
exact-length totient bound and stored `q+1`, `r+1` Gram identities.

Direct check and targeted build pass (`12736/12736`). Its five public results and the newly public
lcm-periodicity theorem audit with only `[propext, Classical.choice, Quot.sound]`; leaf is
umbrella-wired without umbrella build.

Remaining core is collective cancellation of these explicit terminal blocks after the source
modulus weights are restored, then Lemma 3.5(ii) routing; no cancellation estimate is assumed.

### Weighted terminal-block Gram, brick 115 (2026-09-02)

`KloostermanDistinctModulusTerminalGram.lean` restores the original signed modulus weights around
every literal terminal block. It proves the existing distinct-modulus Gram on `[1,M]` is exactly
this weighted terminal carrier, and hence the full signed-kernel Gram is

```text
same-modulus Gram + weighted terminal distinct-modulus Gram.
```

It also proves the unconditional weighted residual budget with each pair retaining its exact
`M mod lcm(q+1,r+1)` length and both totient factors.

Direct check and targeted build pass (`12737/12737`). All four public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

The remaining analytic primitive is now collective cancellation of this exact weighted terminal
Gram inside the source-index quadratic form at the paper ranges; no operator or correlation bound
is assumed.

### Source-weighted terminal quadratic receiver, brick 116 (2026-09-02)

`KloostermanDistinctModulusTerminalQuadratic.lean` composes modulus equality with the existing
source-index Gram split. It proves exact decompositions of both the full transform-output energy
and the erased source off-diagonal into equal-modulus and terminal distinct-modulus quadratic
forms. Its unconditional terminal off-diagonal bound retains every source coefficient, modulus
weight, erased diagonal, and exact `M mod lcm(q+1,r+1)` residual length.

Direct check and targeted build pass (`12738/12738`). All four public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

The remaining analytic estimate is now attached to the literal source-weighted terminal
off-diagonal carrier at the paper ranges. Equal-modulus Ramanujan main/remainder routing is the
remaining elementary complement; no estimate is assumed.

### Three-way Ramanujan and terminal quadratic frontier, brick 117 (2026-09-02)

`KloostermanSameModulusRamanujanQuadratic.lean` lifts exact equal-modulus completion through the
modulus weights and source quadratic forms. Transform energy and the erased source off-diagonal now
decompose exactly into

```text
equal-modulus Ramanujan main
  + bounded equal-modulus completion remainder
  + terminal distinct-modulus carrier.
```

The completion-remainder bounds retain every source coefficient and the exact weighted sum
`sum_q |w_q|^2 (q+1) phi(q+1)`.

Direct check and targeted build pass (`12739/12739`). All seven public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Elementary completion bookkeeping is now closed on both modulus sectors. Remaining work is to
identify/control the Ramanujan main square energy and prove collective cancellation for the
terminal distinct-modulus carrier at the paper ranges; no estimate is assumed.

### Ramanujan main as complete-column square energy, brick 118 (2026-09-02)

`KloostermanSameModulusRamanujanEnergy.lean` identifies every complete-column correlation
quadratic with the literal square energy of the complete Kloosterman column transform. After
restoring interval density and all modulus weights, it proves

```text
Ramanujan main quadratic
  = sum_q |w_q|^2 * M/(q+1) * sum_m |sum_n b_n S(m,n;q+1)|^2.
```

The module proves this carrier is real with nonnegative real part. Thus the Ramanujan main is not a
cancellation-bearing residual term.

Direct check and targeted build pass (`12740/12740`). All six public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Equal-modulus main and completion remainder are now classified completely: positive square energy
plus a closed remainder budget. Remaining genuine analytic primitive is collective control of the
source-weighted terminal distinct-modulus carrier at the paper ranges; no estimate is assumed.

### Exact scalar analytic frontier, brick 119 (2026-09-02)

`KloostermanAnalyticFrontier.lean` packages the exact transform-output energy into three named
quantities: nonnegative Ramanujan main energy, full-source same-modulus remainder budget, and
full-source terminal distinct-modulus budget. It proves the exact complex identity, cancellation
of the combined remainder's imaginary part, the combined norm bound, and the unconditional scalar
energy upper bound without an analytic premise.

Direct check and targeted build pass (`12741/12741`). All six public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

This closes the exact elementary scalar baseline, not the paper-range saving. Remaining genuine
primitive is collective spectral cancellation beyond the terminal-carrier absolute-value budget,
followed by source routing into Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is
assumed.

### Unequal-modulus phase nonresonance, brick 120 (2026-09-02)

`KloostermanCrossPhaseGeometric.lean` proves the standard additive character on every positive
cyclic group is faithful and has the expected natural-multiple power law. For units `x mod q` and
`y mod r`, equality of the cross-phase ratio to one would force both `q ∣ r` and `r ∣ q`; hence
unequal moduli give a nontrivial unit-circle ratio. Every finite orbit therefore satisfies the
reciprocal-chord geometric bound independently of orbit length.

Direct check and targeted build pass (`12746/12746`). Its five public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

### Terminal geometric-orbit expansion, brick 121 (2026-09-02)

`KloostermanTerminalGeometricCancellation.lean` expands every literal terminal cross-column block
coefficient-faithfully into a double sum over unit pairs. Each inner sum is exactly one nontrivial
geometric orbit from brick 120. It proves a terminal-length-independent reciprocal-chord bound and
combines it with the prior exact-length totient bound as their pointwise minimum, including the
stored ordinary-index Gram correlation.

Direct check and targeted build pass (`12747/12747`). All six public theorem declarations, plus
brick 120's newly public natural-multiple law, audit with only
`[propext, Classical.choice, Quot.sound]`; leaves are umbrella-wired without umbrella build.

This is genuine finite phase cancellation, but not yet the paper-range spectral estimate. The
remaining primitive is a collective bound for the reciprocal chord denominators and their signed
modulus/source aggregation strong enough for Lemma 3.5(ii), followed by amplification and Theorem
1.2; no estimate is assumed.

### Coprime cross-frequency CRT compression, brick 122 (2026-09-02)

`KloostermanCoprimeCrossPhaseFrequency.lean` identifies the arithmetic structure of every coprime
unit-pair denominator from bricks 120--121.  The pair `(x mod q, y mod r)` maps by CRT to the
product-period frequency with coordinates `-r*x mod q` and `q*y mod r`.  Complement multiplication
is invertible, so this map is an explicit equivalence

```text
(ZMod q)ˣ × (ZMod r)ˣ  ≃  (ZMod (q*r))ˣ.
```

Its product-level standard additive character is exactly the original cross-phase ratio.  The
terminal double reciprocal-chord sum therefore reindexes, with no loss and no multiplicity, as one
sum over product-modulus units.  The terminal geometric bound is restated in this compressed form.

Direct check and targeted leaf build pass (`12749/12749`).  All eight public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

This removes the apparent `phi(q) * phi(r)` independent-denominator loss for coprime pairs.  The
next arithmetic primitive is a harmonic bound for the single product-period reciprocal-chord sum,
then noncoprime gcd stratification and signed modulus/source aggregation at the paper ranges.
Lemma 3.5(ii), amplification, and Theorem 1.2 remain open; no estimate is assumed.

### Product-period reciprocal-chord harmonic bound, brick 123 (2026-09-02)

`KloostermanProductUnitChordSum.lean` proves the missing collective estimate from brick 122.  For
each nonzero product frequency with canonical representative `j`, two-sided Jordan separation gives

```text
2 / ||1 - e_N(j)|| ≤ (N/2) * (1/j + 1/(N-j)).
```

Unit representatives and their complements are injective positive families bounded by `N`, so the
existing harmonic finite-family theorem bounds each side.  Hence

```text
sum_{z in (ZMod N)ˣ} 2 / ||1 - e_N(z)|| ≤ N * (1 + log N).
```

After brick 122's lossless CRT reindexing, every coprime terminal block satisfies the unconditional,
interval-length-independent bound `q*r*(1+log(q*r))`; the stored ordinary-index Gram correlation
has the corresponding `(q+1)(r+1)` statement.

Direct check and targeted leaf build pass (`13483/13483`).  All eight public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Coprime reciprocal-denominator aggregation is now closed.  Remaining primitive is noncoprime gcd
stratification and signed modulus/source aggregation at paper ranges, followed by Lemma 3.5(ii),
amplification, and Theorem 1.2; no estimate is assumed.

### Product-period frequency slices without coprimality, brick 124 (2026-09-02)

`KloostermanProductFrequencySliceBound.lean` removes the coprimality restriction from the
reciprocal-denominator stage.  For arbitrary positive unequal `q,r`, it realizes each cross phase
as the standard additive character of `q*val(y)-r*val(x)` modulo `q*r`.  With either unit
coordinate fixed this frequency map is injective, and unequal moduli force all slice frequencies
to be nonzero.

The module generalizes the two-sided chord estimate from units to every nonzero cyclic frequency
and proves a harmonic bound for any injective nonzero finite frequency family.  Slicing in either
coordinate gives the shared-gcd-safe bound

```text
sum_x sum_y 2 / ||1 - crossPhase(q,r,x,y)||
  <= min (phi(q) * q*r*(1+log(q*r)))
         (phi(r) * q*r*(1+log(q*r))).
```

This transports directly to the literal terminal block and stored ordinary-index correlation.
Direct check and targeted leaf build pass (`13484/13484`).  All sixteen new theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Noncoprime reciprocal-denominator aggregation is now closed without gcd assumptions.  Remaining
primitive is signed modulus/source aggregation at paper ranges and cancellation beyond this
absolute harmonic budget, followed by Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate
is assumed.

### Source/modulus product-harmonic aggregation, brick 125 (2026-09-02)

`KloostermanProductHarmonicQuadratic.lean` restores brick 124 through every signed modulus weight
and source coefficient.  It defines the explicit weighted pair budget and proves both the literal
terminal Gram and existing stored distinct-modulus Gram are bounded by it.  Since this budget is
independent of source indices, the full source quadratic and erased off-diagonal satisfy

```text
norm terminalQuadratic <= (sum_n |b_n|)^2 * productHarmonicModulusBudget.
```

Direct check and targeted leaf build pass (`13485/13485`).  All six theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Absolute signed modulus/source aggregation is now closed.  Remaining analytic primitive is
cancellation beyond this ℓ¹/product-harmonic baseline at the paper ranges, followed by Lemma
3.5(ii), amplification, and Theorem 1.2; no estimate is assumed.

### Literal source-interval residue multiplicity, brick 131 (2026-09-02)

`KloostermanSourceResidueMultiplicity.lean` replaces the exact but potentially inflated residue
energy by the literal interval geometry used in the paper.  Every fibre of
`n : Finset.Icc 1 N` modulo `q+1` injects, for `N>0`, under
`n ↦ (n-1)/(q+1)` into a range of cardinality `(N-1)/(q+1)+1`.  Fibrewise Cauchy--Schwarz and
exact residue reassembly give

```text
SourceResidueEnergy(q,[1,N],b)
  <= (q+1) * ((N-1)/(q+1)+1) * sum_{1 <= n <= N} |b_n|².
```

The terminal theorem substitutes this budget for both source legs in the full weighted
interpolated Gram receiver.  All statements are no-premise and unconditional.  Direct source check
and targeted leaf build pass (`13490/13490`); all three public theorems audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

This closes source-residue inflation on the literal interval.  It is a bridge, not the missing
collective signed spectral cancellation.  Lemma 3.5(ii), amplification, and Theorem 1.2 remain
open; no estimate is assumed.

### Exact shared-gcd product-frequency multiplicity, brick 135 (2026-09-02)

`KloostermanProductFrequencyGcdBound.lean` closes the noncoprime arithmetic stratification left by
bricks 123–125.  If two product-period frequencies agree, cancellation of the common gcd shows
their first representatives agree modulo `q/gcd(q,r)`.  The remaining quotient is a label in
`Fin (gcd(q,r))`, and the fixed-label frequency map is injective.  Consequently every frequency
fibre has at most `gcd(q,r)` elements.

Fibrewise summation and the existing injective nonzero-frequency harmonic theorem give

```text
sum_x sum_y 2 / ||1-crossPhase(q,r,x,y)||
  <= gcd(q,r) * q*r * (1+log(q*r)).
```

This alternative shared-gcd budget is propagated to terminal/stored correlations, weighted Gram
entries, full source quadratics, and erased off-diagonal quadratics.  Direct source check and
targeted leaf build pass (`13494/13494`).  Eight principal theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Noncoprime product-frequency multiplicity is now dependency-closed.  This is still an
absolute-value receiver: it does not yield the signed spectral/Kuznetsov saving needed for
Lemma 3.5(ii), amplification, and Theorem 1.2.  No such estimate is assumed.

### Exact lcm-period terminal Parseval energy, brick 136 (2026-09-02)

`KloostermanTerminalOrbitParseval.lean` replaces product-period pointwise chord summation by exact
orthogonality on the true cross-phase period `lcm(q,r)`.  The exact frequency map has fibres of
cardinality at most `gcd(q,r)`, and consecutive additive-character Parseval gives energy
`lcm(q,r) * (M % lcm(q,r))`.  The gcd-lcm product identity cancels the fibre multiplicity exactly:

```text
sum_x sum_y ‖kloostermanTerminalOrbit(M,q,r,x,y)‖²
  <= q*r*(M % lcm(q,r)).
```

This eliminates both the harmonic logarithm and the shared-gcd overcount.  The same exact budget is
transported through source residues, weighted terminal Gram pairs, full signed modulus/source
quadratics, and the literal interval receiver.  All results are dependency-closed and introduce no
support, range, coprimality, or analytic cancellation axiom.

Direct source check and targeted leaf build pass (`13500/13500`).  Nine public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

This is genuine finite phase cancellation, but remains pairwise in the moduli.  Collective signed
spectral/Kuznetsov saving at paper ranges, Lemma 3.5(ii), amplification, and Theorem 1.2 remain open;
no such estimate is assumed.

### Row-by-row lcm-Parseval terminal receiver, brick 137 (2026-09-02)

`KloostermanTerminalOrbitParsevalSchur.lean` composes brick 136 with the exact symmetric Schur-row
architecture.  Its pair kernel is the square root of the two source-residue energies times the
exact lcm-period orbit budget; the diagonal is zero.  Lean proves

```text
‖terminalGram(M,Q,w,B,b)‖
  <= sum_{q in Q} ‖w_q‖² * sum_{r in Q} LcmParsevalSchurKernel(M,B,b,q,r).
```

This removes the global modulus-pair Cauchy factor while retaining the log-free, gcd-free orbit
budget.  The literal source-interval capstone substitutes the exact residue multiplicity row by
row.  All statements are unconditional and add no support, coprimality, modulus-size, or analytic
cancellation premise.

Direct source check and targeted leaf build pass (`13501/13501`).  Three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

This closes the strongest absolute-value receiver exposed by the terminal factorization.  It still
takes norms before summing moduli, so collective signed spectral/Kuznetsov saving at paper ranges,
Lemma 3.5(ii), amplification, and Theorem 1.2 remain open; no such estimate is assumed.

### Lossless common-period frequency carrier, brick 138 (2026-09-02)

`KloostermanGlobalPeriodFrequency.lean` defines the minimal common period
`P(Q)=lcm_{q in Q}(q+1)`.  Every stored modulus divides `P(Q)`, hence every pairwise lcm does.
For each erased-diagonal tuple `(q,r,x,y)`, Lean constructs an explicit frequency in
`ZMod P(Q)`, proves its additive character equals the original Kloosterman cross phase, and proves
the frequency is nonzero.  Faithfulness of the standard additive character also proves the exact
collision classification: equality of global frequencies is equivalent to equality of the
original complex cross-phase ratios.

A general finite-order orbit lemma then shows that a nontrivial phase sum depends only on its
length modulo any period.  Consequently the original pairwise-lcm terminal orbit equals exactly
the global-period orbit of length `M % P(Q)`.

No norm or absolute value appears in this transport.  It therefore retains all signed modulus and
source-Fourier coefficients for one global frequency-fibre grouping—the first carrier in this
chain that can express cross-modulus cancellation rather than only majorize it.

Direct source check and targeted leaf build pass (`13502/13502`).  Nine public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Remaining next obligation is exact grouping of the full terminal Gram by these global frequencies,
then a bound for the resulting signed collision energy.  The latter is the genuine
spectral/Kuznetsov core; Lemma 3.5(ii), amplification, and Theorem 1.2 remain open and unassumed.

### Signed global-frequency Parseval receiver, brick 139 (2026-09-02)

`KloostermanGlobalFrequencyParseval.lean` closes the exact grouping obligation left by brick 138.
It defines `A_z` as the complete signed sum of modulus weights and source-Fourier products from
every erased-diagonal `(q,r,x,y)` tuple with global frequency `z`, and defines the collision energy
`E_global = sum_z ‖A_z‖²`.  Lean proves

```text
terminalGram(M,Q,w,B,b) = sum_z A_z * globalOrbit_z,
A_0 = 0,
‖terminalGram(M,Q,w,B,b)‖²
  <= E_global * P(Q) * (M % P(Q)).
```

The first line is an exact finite reindexing, not a bound.  The second uses off-diagonal
nontriviality.  The third is finite Cauchy--Schwarz plus the exact Parseval identity
`sum_z ‖globalOrbit_z‖² = P(Q)*(M % P(Q))`.

Unlike every preceding pairwise or Schur receiver, this formulation keeps all cross-modulus signs
inside a common frequency fibre until after aggregation.  It introduces no analytic premise and
isolates one scalar target: bound `E_global` at the paper's modulus/source ranges.

Direct source check and targeted leaf build pass (`13503/13503`).  Four public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

The remaining analytic theorem is exactly the signed global collision-energy estimate—a concrete
finite Kuznetsov target—followed by Lemma 3.5(ii), amplification, and Theorem 1.2.  None is assumed.

### Exact collision time-frequency Parseval, brick 140 (2026-09-02)

`KloostermanGlobalCollisionParseval.lean` applies corpus-owned cyclic DFT Parseval to the signed
coefficients `A_z`.  It also expands each transform value into the literal erased-diagonal
`(q,r,x,y)` sum with its global additive phase.  Lean proves

```text
sum_k ‖timeTransform_k‖² = P(Q) * E_global,
E_global = P(Q)⁻¹ * sum_k ‖timeTransform_k‖².
```

This is an exact equality and introduces no estimate.  It converts the remaining signed collision
energy into one explicit time-domain Kloosterman second moment, ready for an unconditional
large-sieve/Kuznetsov bound.

Direct source check and targeted leaf build pass (`13504/13504`).  Three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

The paper-scale bound for that explicit time-domain moment, Lemma 3.5(ii), amplification, and
Theorem 1.2 remain open and unassumed.

### Complete-transform Gram and fourth-moment normal form, brick 141 (2026-09-02)

`KloostermanGlobalCollisionGram.lean` proves that the explicit time slice from brick 140 factors
through the existing complete Kloosterman transform.  Writing `R_q(k)` for that local transform,
Lean proves

```text
timeTransform_k = sum_{q != r} star(w_q R_q(k)) * (w_r R_r(k))
                = (‖sum_q w_q R_q(k)‖² - sum_q ‖w_q R_q(k)‖² : R),
E_global = P(Q)⁻¹ * sum_k
  (‖sum_q w_q R_q(k)‖² - sum_q ‖w_q R_q(k)‖²)².
```

The generic common-period lift is exact: a statistic modulo `q+1` repeats
`P(Q)/(q+1)` times.  Applying the corpus's sharp finite complete-Kloosterman `L²` theorem yields

```text
P(Q)⁻¹ * sum_k ‖R_q(k)‖²
  <= (q+1) * sum_z ‖sourceResidue_q(z)‖².
```

Thus no product/LCM loss remains in local second moments.  Remaining target is genuinely the
cross-modulus fourth moment of the total-mass-minus-diagonal defect.

Direct source check and targeted leaf build pass (`13505/13505`).  Thirteen newly exposed or
created theorem declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is
umbrella-wired without umbrella build.

The cross-modulus fourth-moment/Kuznetsov bound, Lemma 3.5(ii), amplification, and Theorem 1.2
remain open and unassumed.

## Brick 142 — exact elementary cross-modulus fourth-moment envelope (2026-09-02)

`Sieve/KloostermanGlobalCollisionElementary.lean` supplies the unconditional comparison point
for the exact fourth-moment normal form.  It proves pointwise complete-response control,
the ordered-pair mixed second moment

```text
P(Q)^(-1) * sum_k normSq(R_q(k)) * normSq(R_r(k))
  <= (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r),
```

and the exact erased-diagonal cardinality `#Q * (#Q - 1)`.  The resulting global theorem is

```text
E_global
  <= #Q * (#Q - 1) *
       sum_(q != r) normSq(w_q) * normSq(w_r) *
         (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r).
```

This is a closed theorem, not a hypothesis and not a spectral claim.  Direct check and targeted
leaf build pass (`13506/13506`); all four public declarations have only standard Lean quotient
and choice axioms.  Module is umbrella-wired; umbrella was not built.

The remaining analytic target is now quantitative and comparative: replace the exact
`#Q * (#Q - 1)` finite-Cauchy baseline and pointwise local charge by the paper-scale collective
Kuznetsov saving, then discharge Lemma 3.5(ii), amplification, and Theorem 1.2.

## Brick 143 — literal-source elementary collision envelope (2026-09-02)

`Sieve/KloostermanGlobalCollisionInterval.lean` composes brick 142 with the exact residue-fibre
occupancy for `Finset.Icc 1 N`.  Removing the common positive `q+1` factor from the existing
source-energy theorem yields

```text
sum_z normSq(sourceResidue_q([1,N],b,z))
  <= residueMultiplicity(q,N) * SourceL2([1,N]),
```

with no size premise and exact occupancy
`if N=0 then 0 else (N-1)/(q+1)+1`.  Substitution on both legs gives

```text
E_global([1,N])
  <= #Q * (#Q - 1) *
       sum_(q != r) normSq(w_q) * normSq(w_r) * (q+1)^2 * (r+1)
         * residueMultiplicity(q,N) * SourceL2([1,N])
         * residueMultiplicity(r,N) * SourceL2([1,N]).
```

Direct check and targeted leaf build pass (`13507/13507`); both public theorems use only
`[propext, Classical.choice, Quot.sound]`.  Leaf is umbrella-wired; umbrella was not built.

The source side of the elementary cross-modulus fourth moment is now literal and fully explicit.
Remaining analytic target is collective Kuznetsov saving over this baseline, then Lemma 3.5(ii),
amplification, and Theorem 1.2.

## Brick 144 — weight-separated global collision receiver (2026-09-02)

`Sieve/KloostermanGlobalCollisionWeighted.lean` performs dependent erased-pair
Cauchy--Schwarz before the common-period average.  It proves

```text
normSq(timeTransform_k)
  <= WeightPairEnergy(Q,w) *
       sum_(q != r) normSq(R_q(k)) * normSq(R_r(k))
```

and consequently

```text
E_global
  <= WeightPairEnergy(Q,w) *
       sum_(q != r) (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r),
```

with `WeightPairEnergy = sum_(q != r) normSq(w_q) * normSq(w_r)`.  A literal
`Finset.Icc 1 N` capstone substitutes both exact residue multiplicities from brick 143.
This receiver is complementary to brick 142 and keeps amplifier normalization separate from the
response/source sum.

Direct source check and targeted leaf build pass (`13508/13508`); all three public declarations
use only `[propext, Classical.choice, Quot.sound]`.  Leaf is umbrella-wired; umbrella was not
built.

Remaining analytic target is still a collective signed Kuznetsov saving over these exact
elementary receivers, then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Brick 145 — bidirectional minimum collision receiver (2026-09-02)

`Sieve/KloostermanGlobalCollisionSymmetric.lean` exposes the exact pre-estimate receiver

```text
E_global
  <= WeightPairEnergy(Q,w) *
       sum_(q != r) Avg_k[normSq(R_q(k)) * normSq(R_r(k))]
```

and proves both elementary orientations of every pair average.  The resulting pair kernel is

```text
min(
  (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r),
  (r+1)^2 * (q+1) * SourceEnergy(r) * SourceEnergy(q)).
```

Thus the global capstone retains the better pointwise/average assignment for every ordered pair.
The literal-source version propagates exact residue occupancies through both minimum branches.

Direct source check and targeted leaf build pass (`13509/13509`).  All five created theorem
declarations use only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired and the
umbrella was not built.

All loss still visible after brick 145 is collective: local L2, pointwise control, pairwise
orientation, weight separation, and literal source collisions are closed.  Remaining target is a
cross-modulus Kuznetsov fourth-moment saving, then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Brick 146 — exact amplifier-weight diagonal deficit (2026-09-02)

`Sieve/KloostermanGlobalCollisionWeightIdentity.lean` closes the exact algebra of brick 145's
weight-pair factor:

```text
WeightPairEnergy(Q,w)
  = (sum_(q in Q) normSq(w_q))^2
      - sum_(q in Q) normSq(w_q)^2.
```

Both the general symmetric collision envelope and literal `Finset.Icc 1 N` envelope are rewritten
with this exact diagonal saving exposed.  No weight normalization, positivity premise, or
cardinality relaxation is needed.

Direct source check and targeted leaf build pass (`13510/13510`).  All three created theorems use
only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired and umbrella was not built.

After brick 146, amplifier normalization contributes exactly total squared mass minus diagonal
fourth moment.  Remaining obstruction is unchanged and genuinely analytic: collective
cross-modulus Kuznetsov fourth-moment saving, then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Brick 147 — pair-local Minkowski collision receiver (2026-09-02)

`Sieve/KloostermanGlobalCollisionMinkowski.lean` applies finite `ell^2` Minkowski before the
global modulus-pair Cauchy step.  The exact receiver is

```text
E_global
  <= (sum_(q != r) |w_q| * |w_r| * sqrt(Avg_k[|R_q(k)|^2 |R_r(k)|^2]))^2.
```

Brick 145's bidirectional minimum bounds each pair average inside its own square root.  The
literal `Finset.Icc 1 N` theorem then inserts both exact residue occupancies at that same
pair-local level.  A comparison theorem proves

```text
MinkowskiElementaryBudget
  <= WeightPairEnergy(Q,w) * sum_(q != r) PairElementaryBudget(q,r),
```

so brick 147 uniformly strengthens the prior elementary receiver.

Direct source check and targeted leaf build pass (`13513/13513`).  All five created theorem
declarations use only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired and
umbrella was not built.

After brick 147, all elementary aggregation loss has been reduced to pair-local mixed response
averages.  Remaining obstruction is collective cross-modulus Kuznetsov cancellation beyond those
elementary pair bounds, then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Brick 149 — centered collective collision receiver (2026-09-02)

`Sieve/KloostermanGlobalCollisionCentered.lean` uses the already proved vanishing of the zero
global-frequency coefficient before taking a fourth-moment bound.  The common-period collision
transform has exact mean zero:

```text
sum_k collisionTimeTransform(k) = 0.
```

Writing `D(k)` for the diagonal response mass and `S(k)` for the squared total response, the exact
Gram identity gives `collisionTimeTransform(k) = S(k) - D(k)`.  Finite Cauchy gives
`S(k) <= #Q * D(k)`, while exact centering gives `sum_k S(k) = sum_k D(k)`.  Combining these before
summation, and retaining the exact square expansion, proves the unconditional collective receiver

```text
E_global
  <= (#Q + 1) * PointwiseDiagonalBudget * AverageDiagonalBudget.
```

The two aggregate budgets retain every squared modulus weight and every exact source-residue
energy.  At comparable modulus/source weights this replaces brick 142's direct
`#Q * (#Q - 1)` finite-Cauchy multiplier by one `#Q + 1` factor, a full family-cardinality gain.
The literal `Finset.Icc 1 N` capstone inserts exact residue multiplicities independently in both
aggregate budgets.

Direct source check and targeted leaf build pass (`13508/13508`).  The three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired and
the umbrella was not built.

This is genuine collective cancellation but not yet the paper-scale Kuznetsov saving: it uses
only exact zero-mode removal plus local complete-transform bounds.  Remaining obstruction is a
further cross-modulus fourth-moment saving strong enough for Lemma 3.5(ii), followed by
amplification and Theorem 1.2.

## Brick 150 — sharp centered collective constant (2026-09-02)

The centered receiver in `Sieve/KloostermanGlobalCollisionCentered.lean` has been sharpened by a
factor two with no new premise.  If `S(k)` is total squared response, `D(k)` is diagonal response,
and `U` bounds `D(k)`, then

```text
(S(k)-D(k))^2 <= S(k)^2 + D(k)^2
S(k)^2 <= #Q * U * S(k)
D(k)^2 <= U * D(k).
```

Exact zero-mode cancellation gives `sum S = sum D`, hence

```text
E_global <= (#Q + 1) * U * AverageDiagonalBudget.
```

The literal `Finset.Icc 1 N` specialization inherits the same sharp factor and keeps exact residue
multiplicities.  Direct source check and targeted leaf build pass; both changed theorem
declarations use only `[propext, Classical.choice, Quot.sound]`.  No umbrella build was run.

The remaining analytic target is unchanged: a paper-scale collective cross-modulus Kuznetsov
saving, then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Brick 151 — zero-mode-exact terminal Gram bridge (2026-09-02)

`Sieve/KloostermanGlobalFrequencyParseval.lean` now deletes the global zero frequency on both
sides of the terminal Parseval receiver.  If `P = kloostermanGlobalPeriod Q` and `r = M % P`, the
zero terminal orbit equals `r`, so Lean proves the exact nonzero-frequency identity

```text
sum_(z != 0) normSq(GlobalTerminalOrbit(M,Q,z)) = P*r - r^2.
```

Because the signed global frequency coefficient already vanishes at zero, the terminal quadratic
therefore satisfies

```text
norm(TerminalGram)^2 <= GlobalCollisionEnergy * (P*r - r^2).
```

`Sieve/KloostermanGlobalCollisionCentered.lean` composes this exact receiver with brick 150.  The
general and literal-source capstones are

```text
norm(TerminalGram)^2
  <= ((#Q + 1) * PointwiseDiagonalBudget * AverageDiagonalBudget) * (P*r - r^2),
```

with exact `Finset.Icc 1 N` residue multiplicities in the literal version.  This closes the bridge
from the centered collision normal form back to the actual terminal distinct-modulus Gram in the
integer-kernel decomposition; no full-period zero-mode charge survives.

Both changed sources pass direct `lake env lean` checks and targeted leaf builds.  The five new
declarations audit with only `[propext, Classical.choice, Quot.sound]`; no umbrella build was run.

Remaining analytic obstruction is now entirely inside the nonzero-frequency global collision
energy: a paper-scale cross-modulus Kuznetsov saving strong enough for Lemma 3.5(ii), followed by
amplification and Theorem 1.2.

## Brick 152 — full constructed-range Type-I consumer (2026-09-02)

`Sieve/MatomakiTeravainenTypeIConstructedRange.lean` propagates the complete unconditional
five-region union from the constructed-range form of Matomäki–Teräväinen Lemma 3.5(ii) through
restricted Cauchy–Schwarz and the literal powered-prime amplifier cover.  For a measurable
`E ⊆ Set.Icc (T / 2) T`, the analytic input is selected internally whenever one of the following
closed alternatives holds:

```text
T <= N,
sqrt T <= B,
2*B*N'^2 <= T + B^2*sqrt T + B^(5/4)*T^(3/4),
or the complete third-derivative region
  T <= N^3,
  T^(5/6) <= B^2,
  N^(3/2) <= B^2,
  N <= B*T^(1/6),
  N^(5/2) <= B*T.
```

The first capstone proves the constructed-range restricted Type-I integral bound at an arbitrary
block length `B`.  The second specializes `B` to every literal powered-prime block
`mtTypeIPrimeBlockLength P ell r`, constructs the amplifier lower bound and finite block cover
internally, and concludes the existing exact `mtTypeIPrimeBlockMomentBound`.  Neither theorem
exposes an analytic-estimate, coefficient-energy, amplifier-lower-bound, or cover premise.

Direct source check and targeted leaf build pass.  Both new public declarations audit with only
`[propext, Classical.choice, Quot.sound]`; the new leaf is umbrella-wired and the umbrella was not
built.

This closes the stale two-region consumer gap.  It does not yet prove that every block generated
by the source schedule lies in the five-region union, so it shrinks but does not close the numeric
frontier toward Matomäki–Teräväinen Theorem 1.2.

## Brick 153 — lossless real-to-natural Type-I blocks (2026-09-02)

`Sieve/MatomakiTeravainenRealNaturalBlocks.lean` closes the endpoint-type mismatch between the
real-scale factors stored by Proposition 2.2 and the exact natural Watt blocks consumed by the
Type-I moment machinery.

For every real dyadic coefficient interval `(M,2M]` with `M ≥ 1`, writing `A = floor M`, Lean
proves the exact Perron-polynomial identity

```text
RealDyadicBlock(M)
  = WattBlock(A) + WattBlockTail(2*A).
```

The first term carries every coefficient through `2*A`; the second carries only coefficients
strictly above `2*A`.  Since `2*M < 2*A+2`, that tail lies inside `(2*A,4*A]` and contains at most
the rounding boundary.  No coefficient is duplicated, deleted, or replaced by a majorant.

For the unit factor Lean also proves the exact identity

```text
RealUnitBlock(L,U) = WattUnitBlock(floor L, floor U).
```

Finally, the scalar source conditions `1 ≤ delta*M ≤ floor M` imply the precise moment-admission
window

```text
floor M < floor((1+delta)*M) ≤ 2*floor M.
```

Direct source check and targeted leaf build pass (`11124/11124`).  All five new theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; the leaf is umbrella-wired
and the umbrella was not built.

This removes rounding as a hidden source hypothesis.  Remaining assembly must prove the displayed
scalar window conditions from the actual geometric schedule, then apply the Type-I and Type-II
receivers to every Proposition-2.2 piece before the Perron comparison.

## Brick 154 — actual-source real-to-natural Watt windows (2026-09-03)

`Sieve/MatomakiTeravainenRealNaturalSourceSchedule.lean` discharges brick 153's scalar window
conditions on the literal rooted geometric schedule.  At successor paper width
`delta = mtPaperWidth (A+1) X`, the existing aligned-schedule progress theorem and width reserve
give, eventually and uniformly in every geometric level `j`,

```text
1 <= delta*M <= floor M,
floor M < floor((1+delta)*M) <= 2*floor M.
```

The source-facing capstone then identifies the real unit-factor Perron polynomial exactly with
`mtWattUnitBlock (floor M) (floor((1+delta)*M))`; no rounding majorant, scale premise, or analytic
estimate remains.  Direct source check and targeted leaf build pass (`11149/11149`).  All three
new declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
and umbrella was not built.

This closes actual-source unit-factor admission.  Remaining assembly must route every full
Proposition-2.2 piece into the Type-I/Type-II receivers, including the genuinely collective
cross-modulus estimate needed by the residual Lemma 3.5(ii) range, before Perron comparison and
Theorem 1.2.

## Brick 155 — retained-piece real-to-natural Watt windows (2026-09-03)

`Sieve/MatomakiTeravainenRealNaturalPieceSchedule.lean` closes the unit-factor handoff for the
actual Type-I and Type-I/II data produced by Proposition 2.2.  An arbitrary upper-adic block can
be too small, so no false all-index statement is used.  Instead Lean derives the required room
from the source's own retained-product lower bound and built-in scale caps.

At successor width `delta = mtPaperWidth (A+1) X`, uniformly over the literal paper range

```text
0 < epsilon <= 1/100,
X^(1-epsilon/100) < Y,
```

every Type-I datum satisfies `delta*M2 >= 1`.  Every Type-I/II datum first satisfies the exact
consequence

```text
M1*M2 <= X^(5/8),
```

from `M1^2*M2 <= X^(1-epsilon)` and `M2 <= X^(1/4-epsilon)`; its retained product then forces
`delta*M3 >= 1`.  Eventual half-width gives the matching upper floor bound in both cases.

The two source-facing capstones identify each real terminal factor exactly with
`mtWattUnitBlock (floor M) (floor ((1+delta)M))` and prove

```text
floor M < floor ((1+delta)M) <= 2*floor M.
```

All paper restrictions occur inside the eventual conclusions; neither theorem has a hypothesis.
Direct source check and targeted leaf build pass (`11141/11141`).  All five new declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired and umbrella was
not built.

This removes the false need for a lower bound on every adic index and closes natural unit-block
admission for every retained Type-I and Type-I/II piece.  The remaining analytic core is still the
collective signed cross-modulus estimate on the residual Lemma 3.5(ii) Type-I range.
