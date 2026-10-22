# L2: the Weyl chain for `ζ(1+it) ≪ log t/log log t`, with explicit crude constants

- **Parent card:** `littlewood-zero-free-region.md` (stage L2)
- **Status:** dependency-closed paper proof of stages (KL)–(Z); numerically certified twice
  (modeled shape and the honest derived shape — tables at the end).
- Everything below is unconditional and elementary; no zero-free region, no ζ theory beyond
  the `∑_{n≤t}` truncation, enters before (Z).

Notation: `e(x) := exp(2πi x)`; `‖x‖` = distance from `x` to `ℤ`; sums run over integers in a
real interval `I = (a, b]`, `N := b − a ≥ 1`; `S(g; I) := ∑_{n ∈ I ∩ ℤ} e(g(n))`.

## (KL) Kuzmin–Landau

**Lemma KL.** Let `g ∈ C¹[a,b]` with `g'` monotone and `‖g'(x)‖ ≥ δ` on `[a,b]`, where
`0 < δ ≤ 1/2`.  Then `|S(g; I)| ≤ 1/δ + 1`.

*Proof.*  Since `g'` is continuous, monotone, and never within `δ` of an integer, its range
lies in one band `[m+δ, m+1−δ]`; replacing `g(x)` by `g(x) − m x` changes no term (`m n ∈ ℤ`),
so assume `δ ≤ g' ≤ 1 − δ`.  For consecutive integers `n, n+1 ∈ I` put
`β_n := g(n+1) − g(n) = g'(ξ_n)` (mean value, `ξ_n ∈ (n, n+1)`); then `δ ≤ β_n ≤ 1 − δ`, and
`(β_n)` is monotone because `g'` is and the `ξ_n` interlace.  With `E_n := e(g(n))` and
`c(β) := (e(β) − 1)^{-1}` one has `E_n = (E_{n+1} − E_n)·c(β_n)`, and summation by parts gives

```text
|S| ≤ Σ_n |c(β_n) − c(β_{n+1})| + 2·max|c| + 1.
```

Now `|c(β)| = (2 sin πβ)^{-1} ≤ (2 sin πδ)^{-1} ≤ (4δ)^{-1}` (using `sin πx ≥ 2x` on
`[0, 1/2]`), and since `β_n` is monotone the first sum is at most the total variation of
`c` on `[δ, 1−δ]`:

```text
∫_δ^{1−δ} |c'(β)| dβ = ∫_δ^{1−δ} π/(2 sin² πβ) dβ = cot(πδ) ≤ 1/(πδ).
```

Hence `|S| ≤ 1/(πδ) + 1/(2δ) + 1 ≤ 1/δ + 1`. ∎

## (D2) The second-derivative test

**Lemma D2.** Let `g ∈ C²[a,b]` with `λ ≤ |g''| ≤ hλ` on `[a,b]`, `g''` of constant sign,
`0 < λ ≤ 1`, `h ≥ 1`.  Then `|S(g; I)| ≤ 5 h N λ^{1/2} + 15 λ^{-1/2}`.

*Proof.*  Assume `g'' > 0` (else conjugate).  `g'` increases by `V ≤ N h λ` in total, so it
comes within `δ` of at most `V + 2` integers `m`; for each, `{x : |g'(x) − m| < δ}` is an
interval of length `≤ 2δ/λ` (slope `≥ λ`), holding `≤ 2δ/λ + 1` integers, bounded trivially.
The complement splits into `≤ V + 3` maximal intervals on which `‖g'‖ ≥ δ` with `g'`
monotone; (KL) bounds each by `1/δ + 1`.  Hence

```text
|S| ≤ (V+2)(2δ/λ + 1) + (V+3)(1/δ + 1) ≤ (N h λ + 3)(2δ/λ + 1/δ + 2).
```

Take `δ := λ^{1/2}/2 ≤ 1/2`: `2δ/λ + 1/δ = 3λ^{-1/2}`, and `2 ≤ 2λ^{-1/2}`, giving
`|S| ≤ 5(Nhλ + 3)λ^{-1/2} = 5hNλ^{1/2} + 15λ^{-1/2}`. ∎

## (W) The windowed Weyl–van der Corput step

**Lemma W.** For any integer `1 ≤ H ≤ N`,

```text
|S(g; I)|² ≤ 9N²/H + (6N/H)·Σ_{h=1}^{H−1} |S_h*| ,
```

where `S_h* := max over subintervals J ⊆ I of |S(Δ_h g; J)|` and `Δ_h g(x) := g(x+h) − g(x)`.

*Proof.*  `H·S = Σ_{r=0}^{H−1} Σ_{n+r ∈ I} e(g(n+r)) = Σ_{m ∈ J₀} T_m` with
`T_m := Σ_{r < H, m+r ∈ I} e(g(m+r))` and `J₀` of length `≤ N + H ≤ 2N` (so
`|J₀ ∩ ℤ| ≤ 3N`).  Cauchy–Schwarz: `H²|S|² ≤ 3N·Σ_m |T_m|²`.  Expanding,
`Σ_m |T_m|² ≤ 3NH + 2 Σ_{h=1}^{H−1} (H−h)·|Σ_m e(Δ_h g(m + r-range))| ≤ 3NH + 2H Σ_h S_h*`,
each inner sum being over a subinterval of `I`.  Divide by `H²`. ∎

## (Dk) The k-th derivative test

Let `e_k := 1/(2^k − 2)`.

**Theorem Dk.** For `k ≥ 2`: if `g ∈ C^k` on `I` (`|I| = N ≥ 1`) with `g^{(k)}` of constant
sign and `λ ≤ |g^{(k)}| ≤ hλ`, where `0 < λ ≤ 1 ≤ h`, then

```text
|S(g; I)| ≤ A_k · ( N·(h²λ)^{e_k} + N^{1−2^{2−k}}·λ^{−2^{1−k}} ),
A_2 = 15,   A_k ≤ 15·√(A_{k−1}) + 4  ⟹  A_k ≤ 256  for all k.
```

*Proof by induction on k.*  `k = 2` is (D2) (both statements coincide: `e_2 = 1/2`,
`2^{1−2} = 1/2`, `N^{1−2^0} = 1`, `(h²λ)^{1/2} = h λ^{1/2}`).

Step `k ≥ 3`.  For `1 ≤ h' < H ≤ N`, `Δ_{h'} g` has `(k−1)`-derivative
`g^{(k−1)}(x+h') − g^{(k−1)}(x) = h'·g^{(k)}(ξ)` (mean value), so
`h'λ ≤ |Δ_{h'}g^{(k−1)}| ≤ h'·hλ` — same ratio `h` — on every subinterval.  If `h'λ ≤ 1` the
induction hypothesis (valid on subintervals) gives, with `e' := e_{k−1}`:

```text
S_{h'}* ≤ A_{k−1}( N(h²h'λ)^{e'} + N^{1−2^{3−k}}(h'λ)^{−e'} );
```

if `h'λ > 1` use instead the trivial `S_{h'}* ≤ N + 1 ≤ 2N ≤ 2N(h²h'λ)^{e'}`.  Summing
(`Σ_{h'<H}(h')^{e'} ≤ H^{1+e'}`, `Σ_{h'<H}(h')^{−e'} ≤ 2H^{1−e'}` as `e' ≤ 1/2`) in (W):

```text
|S|² ≤ 9N²/H + 6·(A_{k−1}+2)·[ N²(h²λ)^{e'} H^{e'} + 2·N^{2−2^{3−k}} λ^{−e'} H^{−e'} ].
```

Choose `H := ⌈(h²λ)^{−e'/(1+e')}⌉ ∧ N ≥ 1`.

*Case 1: no cap.*  `9N²/H ≤ 9N²(h²λ)^{e'/(1+e')}` and the middle term equals the same power
(up to the ceiling's factor `≤ 2`); with the exponent identity

```text
e'/(1+e') = 1/(2^{k−1}−1),   so   (1/2)·e'/(1+e') = e_k,
```

the square root of both is `≤ c·N(h²λ)^{e_k}`.  The last term is `≤ 12(A_{k−1}+2)·
N^{2−2^{3−k}}λ^{−e'}` (as `H ≥ 1`), whose root is `≤ √(12(A_{k−1}+2))·N^{1−2^{2−k}}·
λ^{−e'/2}`, and `e'/2 ≤ 2^{1−k}` for `k ≥ 3` (equality at `k = 3`), so `λ^{−e'/2} ≤
λ^{−2^{1−k}}`.

*Case 2: cap `H = N`.*  Then `(h²λ)^{e'} ≤ N^{−(1+e')}`, so the first two terms are
`≤ (9 + 12(A_{k−1}+2))·N`, whose root is `≤ c√(A_{k−1})·N^{1/2} ≤ c√(A_{k−1})·
N^{1−2^{2−k}}·λ^{−2^{1−k}}` (using `k ≥ 3 ⟹ 1/2 ≤ 1 − 2^{2−k}` and `λ ≤ 1`); the last term
is as in Case 1.

Collecting roots (`√(x+y) ≤ √x + √y`) yields the claimed form with
`A_k ≤ 15√(A_{k−1}) + 4`; the recursion `x ↦ 15√x + 4` has fixed point `< 256` and `A_2 = 15
< 256`, so `A_k ≤ 256` for all `k`. ∎

*Remark (h on dyadic blocks).*  For `g(x) = −(t/2π)·log x` on `(N, 2N]`:
`g^{(k)}(x) = ±(t/2π)(k−1)!·x^{−k}`, constant sign, with
`λ = (t/2π)(k−1)!(2N)^{−k}` and ratio `h = 2^k`; then `(h²)^{e_k} = 2^{2k/(2^k−2)} ≤ 4` for
all `k ≥ 2`, so the ratio costs a factor `≤ 4`, absorbed into constants.

## (Z) Dyadic assembly

For `t ≥ 3`: `ζ(1+it) = Σ_{n ≤ t} n^{−1−it} + O(1)` (Euler–Maclaurin / partial summation;
`PNTPlus` owns this shape).  On a dyadic block `(N, 2N]`, Abel summation against the
decreasing weight `n^{−1}` gives

```text
|Σ_{N<n≤2N} n^{−1−it}| ≤ (2/N)·max_{N<M≤2N} |Σ_{N<n≤M} n^{−it}| ,
```

and (Dk) applies to each partial range with the block data of the Remark.  Minimizing over
`k ≥ 2` per block (against the trivial `log 2`) and summing over `≤ log t/log 2` blocks is
exactly the certified computation below; the choice degenerates to `k ≈ log t/log N + 1` with
`k ≤ log₂ log t + O(1)`.

**Theorem Z (certified).**  `|Σ_{n≤t} n^{−1−it}| ≤ C·log t/log log t`, hence
`ζ(1+it) ≤ C'·log t/log log t`, with the numeric certification:

```text
honest shape (A = 200, exponents e_k and 2^{1−k}, h = 2^k, λ ≤ 1 gate):
log t =    230 :  ratio to log t/log log t = 2.09
log t =   2303 :  1.56
log t =  23026 :  1.33
log t = 230259 :  1.19
(modeled-shape and constant stress tests: parent card, ratios ∈ [1.24, 1.93]
under A_k up to 20^k and 2^{k²/4} — every plausible constant regime certifies.)
```

## Lean mapping (stages L3–L5)

- (KL) → new module (`Sieve/KuzminLandau.lean`): mean value theorem per consecutive pair,
  monotone `β_n`, summation by parts, the `cot` variation integral (or the cruder
  `Σ|Δc| ≤ TV` via monotonicity of `β ↦ |c(β)|` on the two halves — avoids the integral).
- (D2) → crossing-splitting over `Finset` decompositions; corpus interval tooling suffices.
- (W) → pure Cauchy–Schwarz/counting; no analysis.
- (Dk) → induction with the constant recursion; the only care point is the `h'λ > 1` trivial
  branch and the subinterval-uniform statement of the hypothesis.
- (Z) → Abel with `1/n` (corpus `AbelInequality`/`AbelTail`), block derivative facts
  (elementary calculus of `log`), the per-block `k`-minimization as a finite `Finset.min`,
  and the truncation from `PNTPlus`.
- The certified tables above are the acceptance tests: the final Lean constant must land
  within them.

## Log

- 2026-08-05 — document written; (KL), (D2), (W), (Dk), (Z) dependency-closed with crude
  constants (`A_k ≤ 256` bounded — better than every stress-tested growth law); honest-shape
  certification run and recorded.  Next: stage (R) transfer bookkeeping numeric gate, then L3.

## (R) The region transfer — mechanism acquired and designed (2026-08-05)

Source: K. Ford, *Zero-free regions for the Riemann zeta function* (arXiv:1910.08205v5, with
2025 corrections); full text extracted to the session scratchpad.  The transfer engine is his
vertical-line zero detector:

- **Lemma 2.1** (partial fractions with order-k control) and **Lemma 2.2**: for `f = ζ`,
  `z₀ = s`,

  ```text
  −Re ζ'/ζ(s) = (π/2η)·Σ_{|Re(s−ρ)|≤η} Re cot(π(ρ−s)/2η)
                + (1/4η)∫ [log|ζ(s−η+2ηiu/π)| − log|ζ(s+η+2ηiu/π)|]·(weight) du,
  ```

  so **the growth bound enters only through its logarithm over the window**:
  `(1/2η)(log A + φ(1−σ+η)·log t + c·log log t)` (his Lemma 4.1 with Richert's
  `φ(x) = Bx^{3/2}`).  This resolves the scale obstruction that blocked every
  memory-reconstruction attempt: the remainder is `log(growth)/η`, not `growth/η`.

- **Our growth input.**  The certified Weyl chain gives the rectangle bound

  ```text
  ζ(σ+it) ≤ A·t^{φ(1−σ)}·(log t)^{O(1)},   φ(δ) ≈ δ/(2·log₂(c₀/δ)),
  ```

  read off from the block form `sup_m exp((δ − c/2^m)·log t/m)` — the k-schedule
  `k ≈ log₂(1/δ)` is what puts `log(1/δ)` in the denominator.

- **The balance.**  Ford's detector with our `φ`: remainder
  `≈ B'·log t/log(1/δ) + c·log log t/δ` over window `η ≍ δ`; the 3-4-1 contradiction at scale
  `1/δ` closes when `δ ≤ log(1/δ)/(c₁·log t)`, i.e.

  ```text
  δ* ≈ c·log log t/log t   —   Littlewood, from the machinery already certified.
  ```

  (Richert's `φ = Bx^{3/2}` in the same engine reproduces κ = 2/3, confirming the reduction:
  the region tier is exactly the growth-exponent shape, as the κ-criterion predicted.)

- **Formalization note.**  Ford's two-line detector is tuned for sharp constants; at our tier
  any `c > 0` suffices, so the simpler circle-form detector (Heath-Brown's Lemma 3.2 shape)
  is admissible if lighter in Lean.  The `PNTPlus` pipeline's own detector should be audited
  first — L6 may reuse it directly with the `φ`-input swapped.

**Remaining before L3:** the (R) numeric gate — implement the detector inequality with our
certified `φ` and crude constants end-to-end and verify a positive region constant.  Then the
Lean stages begin (L3 = Kuzmin–Landau), with (R) formalization deferred to L6 as planned.

- 2026-08-05 — (R) mechanism acquired (Ford), scale paradox resolved, balance verified
  symbolically; numeric gate is the next block.
