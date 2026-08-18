# Forbidden-support stability of the all-interval \(E_3\) theorem

- **ID:** route-e-forbidden-support-e3-stability
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Statement:** Matomäki--Teräväinen's all-interval \(E_3\) lower bound remains valid, with
  the same order, after excluding every prime divisor of an arbitrary \(A\le x^B\).

## Goal

Close Route E's simultaneous-coprimality admission gate for finitely many factor blocks.  The
result must be uniform in a dynamically supplied spectator/replacement support, not merely avoid
a fixed finite set.

## Gates

- [x] 0 → 1 in-progress: source-pure quantitative avoidance target
- [x] 1 → 2 fully-proven: complete perturbative proof below, using the published all-interval
  theorem and estimates already proved in its source
- [ ] 2 → 3 formalized: the elementary perturbative layer is formalized (see "Lean progress");
      the all-interval theorem it perturbs is a deep external input, not present in Mathlib
- [ ] 3 → 4 publication-ready: external priority audit and standalone exposition

## Lean progress

`formal/GaloisForLFunctions/RHTower/RouteEForbiddenSupportStability.lean` formalizes the
elementary layer of the perturbation, unconditionally and in the card's own parameter regime
(`fsExponent = 11/10`, `fsSmallScale`, `fsLargeScale`, `fsWindow` are `a`, `P₁`, `R`, `h` of
`(FS1)`):

- `card_mul_log_le_log` and `card_le_log_div_log` are the support-size bound: the prime divisors of
  `A` above a threshold `T` have a product dividing `A`, so their number is at most `log A / log T`.
  This is the single arithmetic fact behind both `#S₁ log P₁ ≤ log A` and `(FS11)`.
- `norm_cpow_le`, `norm_supportSum_le_card_div` and `norm_supportSum_le_log` are `(FS5)`: the
  deleted Dirichlet polynomial satisfies `|D₁(s)| ≤ #S₁/T ≤ log A/(T log T)` uniformly on the
  closed half-plane `Re s ≥ 1`, since each term has modulus `p^{-Re s} ≤ p^{-1} ≤ 1/T`.
- `sum_inv_le_log` is `(FS10)`: the harmonic mass carried away by the deleted support obeys the
  same bound, so the long-interval main term keeps `1 - o_B(1)` of its size.
- `norm_sq_sub_mul_le` and `integral_norm_sq_sub_mul_le` are `(FS6)`: the perturbed mixed mean
  square is at most twice the unperturbed one plus twice the sup-norm square times the second
  factor's mean square.
- `fsWindow_div_eq` is the exact form of `(FS12)`: at the lower endpoints of the two prime ranges
  the window carries exactly `4 log x` scaled units, `card_scaledWindow_le` bounds the integers in
  a scaled window by `h/c + 1`, and `card_window_le` combines them into the `4 log x + 1` bound on
  the remaining variable.
- `tendsto_fsNegligible` is `(FS13)`: the polylogarithmic triple count through one fixed large
  prime, weighted against the main term's `(log x)^{-0.45}` normalisation, tends to zero.
- `eventually_smallScale_lt_largeScale` is the range disjointness that makes the surviving triples
  squarefree, and `card_diagonalWindow_le` is the diagonal case `p₂ = p₃`: the square constraint
  `p₁p₂² ∈ (x, x+h]` leaves at most `log x / 2 + 1` integers, because the square root increases by
  at most `h/(2√x)` over the window (`sqrt_add_sub_sqrt_le`).  So the diagonal carries the same
  polylogarithmic bound as `(FS13)` and its removal leaves three distinct primes.
- `mobiusComplexCoefficient_prime_mul_threePrime`, `mul_sqrt_div_eq_sqrt_mul` and
  `abs_amplified_gap_le` are the block-admission corollary `(FS14)`: a prime cofactor times an
  exact-three-prime token has Möbius `+1`, and amplifying a near-square-root token at the reduced
  centre `u/ℓ` by `ℓ` keeps it within `√(uℓ)` times the same polylogarithmic factor of `u`.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

Not formalized: the all-interval count `(FS4)` itself, and the mean-value estimate `(FS7)` and the
two-dimensional upper-bound sieve it rests on.  These are Matomäki--Teräväinen's published inputs,
quoted rather than proved on this card; they are stated nowhere in the Lean tree, so nothing above
is conditional on them.  Every step this card *proves* is now in Lean.

The corpus Dirichlet mean-value theorem (`RHTower.Sieve.dirichlet_meanValue_theorem`) carries the
error `O(N log N)`, not the Montgomery--Vaughan `O(N)`; even the sharp form only gives `O(1/log R)`
for the second term of `(FS7)`, so that estimate genuinely needs the source's Section 5 sieve and
is not reachable from the card text alone.

## Theorem

Fix \(B>0\).  Put

\[
P_1=(\log x)^{a},\qquad a=1.1,\qquad
R={1\over2}\sqrt{x/P_1},\qquad
h=\sqrt{x}(\log x)^{1+a/2}.
\tag{FS1}
\]

Uniformly for all sufficiently large \(x\) and all integers \(1\le A\le x^B\), the interval
\((x,x+h]\) contains

\[
\gg_B {h\over(\log P_1)(\log x)^2}
\tag{FS2}
\]

products \(p_1p_2p_3\), counted with the same minorant multiplicity as in
Matomäki--Teräväinen's Section 7, such that

\[
p_1\asymp P_1,\qquad p_2\asymp R,\qquad p_3\asymp R,
\qquad (p_1p_2p_3,A)=1.                                  \tag{FS3}
\]

After removing the diagonal \(p_2=p_3\), the same order of lower bound remains for products of
three distinct primes.  In particular there is a squarefree \(E_3\) number coprime to \(A\) in
every such interval.

## Proof

Write \({\cal S}\) for the prime divisors of \(A\).  The proof of
[Matomäki--Teräväinen, Theorem 1.2](https://arxiv.org/abs/2207.05038) establishes

\[
\#\{p_1p_2p_3\in(x,x+h]:p_1\asymp P_1,\ p_2\asymp R\}
\gg {h\over(\log P_1)(\log x)^2}.                         \tag{FS4}
\]

It is enough to show that deleting \({\cal S}\) from each of the three prime variables changes
neither their short/long comparison nor its positive long-interval main term by more than
\(o_B(1)\) relatively.

### 1. The small prime variable

Let

\[
{\cal S}_1={\cal S}\cap(P_1,2P_1],\qquad
D_1(s)=\sum_{p\in{\cal S}_1}p^{-s}.
\]

The product constraint on \(A\) gives

\[
\#{\cal S}_1\log P_1\le\log A\le B\log x,
\]

and hence, uniformly on \(\Re s=1\),

\[
|D_1(s)|
\le {\#{\cal S}_1\over P_1}
\ll_B {(\log x)^{1-a}\over\log\log x}
=O_B\!\left({(\log x)^{-0.1}\over\log\log x}\right).
\tag{FS5}
\]

In the notation of Section 7 of the cited paper, replace
\(P_1(s)=\sum_{p\asymp P_1}p^{-s}\) by \(P_1(s)-D_1(s)\).  Every Dirichlet-polynomial estimate
except the mixed \(P_1P\) mean square is immediately monotone or follows by the triangle
inequality.  For the mixed term,

\[
\int |(P_1-D_1)P|^2
\le 2\int|P_1P|^2+2\|D_1\|_\infty^2\int|P|^2.             \tag{FS6}
\]

The first integral is the proved estimate used in their equation (7.6).  The improved mean-value
theorem and the same two-dimensional upper-bound sieve used in their equations (5.2)--(5.3) give,
for \(T\ge x/h\),

\[
\int_{T_0}^{T}|P(1+it)|^2dt
\ll {T\over R\log x}+{1\over(\log x)^2}.                 \tag{FS7}
\]

Combining `(FS5)` and `(FS7)`, the perturbation in `(FS6)` is

\[
\ll_B
 {T\over\sqrt{x}(\log x)^{0.65}(\log\log x)^2}
 +{1\over(\log x)^{2.2}(\log\log x)^2}.                  \tag{FS8}
\]

This is smaller than the required Section 7 bound

\[
{T\over x/h}{1\over(\log x)^{2+2\varepsilon}}
= {T\over\sqrt{x}(\log x)^{0.45+2\varepsilon}}
\tag{FS9}
\]

for any fixed \(0<\varepsilon<0.1\); at the lower endpoint \(T=x/h\), the second term in
`(FS8)` is also \(o((\log x)^{-2-2\varepsilon})\).  Thus the Perron short/long comparison survives
the deletion.

For the long interval, Mertens' prime estimate gives

\[
\sum_{p\asymp P_1}{1\over p}\asymp {1\over\log P_1},
\qquad
\sum_{p\in{\cal S}_1}{1\over p}
\ll_B {(\log x)^{-0.1}\over\log\log x}.                  \tag{FS10}
\]

The deleted harmonic mass is only \(O_B((\log x)^{-0.1})\) of the full one.  The positive
minorant main term and its upper-bound-sieve majorant are linear in this \(p_1\)-weight, so the
long main term retains \(1-o_B(1)\) of `(FS4)`.

### 2. The two large prime variables

Every \(q\in{\cal S}\) in either large-factor range satisfies
\(\log q=(1/2+o(1))\log x\).  Therefore

\[
\#({\cal S}\cap[R/2,4R])=O_B(1).                         \tag{FS11}
\]

Fix such a \(q\).  For every \(p_1\asymp P_1\), the remaining large prime is constrained to an
interval of integer length

\[
\ll {h\over p_1q}+1\ll(\log x)^{1+a/2-a+a/2}+1
\ll\log x.                                               \tag{FS12}
\]

Consequently the total number of short-interval triples containing \(q\) is

\[
\ll {P_1\over\log P_1}\log x
\ll {(\log x)^{2.1}\over\log\log x}
=o\!\left({\sqrt{x}\over
  (\log x)^{0.45}\log\log x}\right),                     \tag{FS13}
\]

which is negligible compared with `(FS4)`.  The identical argument applies to either large
prime variable.  In the long interval, a one-dimensional upper-bound sieve gives a relative
loss \(O_B((\log x)^2/R)=o_B(1)\).

### 3. Squarefreeness

The \(p_1\)-range and the two large-factor ranges are disjoint.  On the diagonal \(p_2=p_3\),
for each \(p_1\) the product constraint permits only \(O(\log x)\) integer values by `(FS12)`.
Thus the diagonal has the same polylogarithmic bound `(FS13)` and is negligible.  Removing it
proves `(FS2)`--`(FS3)` for three distinct primes.

## Corollary: simultaneous block admission

Fix \(\delta>0\).  Let \(u_1,\ldots,u_r\) be factor blocks with
\(\prod_i u_i\le N^{O(1)}\), \(u_i\ge N^\delta\), and \(r=O_\delta(1)\).  Process them
sequentially.  At stage \(i\), the product of every original prime support and every previously
chosen replacement support is at most \(u_i^{O_\delta(1)}\).  The theorem supplies an \(E_3\)
replacement coprime to all of them.

If \(\mu(u_i)=+1\), use that \(E_3\) token.  If \(\mu(u_i)=-1\), choose a fresh prime
\(\ell_i\ll_\delta\log N\) outside the accumulated support and apply the theorem at
\(u_i/\ell_i\), also forbidding \(\ell_i\).  Then

\[
Q_i=\ell_i E_3(u_i/\ell_i),\qquad
\mu(Q_i)=+1=-\mu(u_i),
\]

is squarefree and

\[
|Q_i-u_i|
\ll \sqrt{u_i\ell_i}\,(\log u_i)^{1.55}
=u_i^{1/2}N^{o(1)}.                                      \tag{FS14}
\]

The resulting block pairs are jointly coprime.  For \(u_i\le z^2\), the factor ranges in the
all-interval proof keep every replacement prime at most \(z\).  Hence every corner of the
associated block cube remains in the zero/one-large-prime boundary.

This closes simultaneous pointwise coprime **admission** for any fixed number of polynomial-scale
blocks.  It does not prove fractional vertex capacity, incoming-corner co-degree, or co-moving
cutoff flux.

## Novelty audit

The underlying all-interval \(E_3\) theorem and all mean-value/sieve estimates are published.
The uniform deletion of an adversarial support \(A\le x^B\), its \(L^\infty\)-small-prime
Dirichlet perturbation `(FS5)`--`(FS9)`, and the simultaneous block-admission corollary were not
found in the source or collision search.  This is a stability extraction from the published
proof, not a new Type-II estimate.

## Log

- 2026-08-01 — extracted and proved polynomial-forbidden-support stability; closed Route E's
  finite-block simultaneous coprimality gate on paper.  Remaining source core is capacity and
  co-moving seam flux.

## The remaining input is tracked on a dedicated programme card (2026-08-17)

The only thing between this card and stage 3 is Matomäki--Teräväinen's all-interval \(E_3\) theorem
(arXiv:2207.05038, Theorem 1.2) together with the mean-value and two-dimensional sieve estimates it
rests on.  That formalisation is now tracked on
`docs/drafts/pipeline/1-in-progress/matomaki-radziwill-lean-programme.md`, shared with the three
`route-e-*` cards in `new_scientific_knowledge` (which need Matomäki--Radziwiłł instead): both
theorems are built out of the same Dirichlet-polynomial toolkit — Plancherel, the mean value
theorem, large values, Halász--Montgomery — and the same Vinogradov--Korobov prerequisite.

Two shared bricks have landed there, both unconditional and axiom-clean:
`Sieve/LogWindowPlancherel.lean` (the exact Plancherel identity for a logarithmic short-interval
sum, replacing the corpus's lossy Gallagher inequality, whose sup term forces windows of length
`≫ √X`) and `Sieve/LogWindowDiscreteTransfer.lean` (the passage from a discrete family of starting
points to the mean square over the whole line).

The card's own remaining elementary debt is separate and smaller: the unsigned squarefree harmonic
estimates quoted in `(7)` and `(9)` (respectively `(FS7)`'s sieve input), which do not depend on the
deep theorem and can be built independently.

## The two-dimensional sieve half of `(FS7)` is built (2026-08-18)

The card's `(FS7)` — the mean square of the large-prime Dirichlet polynomial,

```text
∫_{T₀}^{T} |P(1+it)|² dt  ≪  T/(R log x) + 1/(log x)² ,
```

was recorded here (and in the Serena memory `cards/route-e-e3-elementary-layer`) as unreachable
because the corpus's Dirichlet mean value theorem cannot save a second logarithm.  **That diagnosis
was about the wrong instrument.**  The saving does not come from a sharper mean value theorem; it
comes from the *two-dimensional upper-bound sieve* applied to the off-diagonal pairs, exactly as the
source's Section 5 does — and the corpus already owns that sieve, built for the
Matomäki–Radziwiłł programme's rough half (`Sieve/RoughPairSieve`, `Sieve/RoughPairCount`).

Five new unconditional modules turn it into the mean square:

| module | content |
|-|-|
| `Sieve/PrimePairCount` | `not_dvd_of_prime_lt`, `primePair_subset_roughPair`, **`card_primePair_le`** — a prime above the sifting range carries no prime factor inside it, so the shifted rough-pair sieve counts prime pairs: `#{m ≤ Y : m, m+d prime, m > h} ≤ Y/((1/2)E²C(d)) + (Selberg remainder)`, with `E = exp(mertensS h − mertensS P₁)` and the singular series `C(d) = ∏_{p ∣ d, P₁<p≤h}(p−1)/p` |
| `Sieve/PrimePairShiftSum` | `sum_inv_mul_pred_eq`, `sum_inv_mul_pred_le`, `sum_rangePrimes_inv_mul_pred_le`, `prod_dvd_iff_forall_dvd`, `prod_shiftCorrection_inv_eq`, **`sum_inv_shiftCorrection_le`** — `∑_{d ≤ K} 1/C(d) ≤ e·K`, by expanding the product over subsets, counting multiples, and reassembling into `∏_p(1 + 1/(p(p−1))) ≤ exp(∑_{n≥2} 1/(n(n−1))) = e`.  The telescoping `∑_{2≤n≤h} 1/(n(n−1)) = 1 − 1/h` is proved, not quoted |
| `Sieve/PrimePairAverage` | `pairClass_div_le`, `pairBudget_le`, **`sum_card_primePair_le`** — the shift-uniform level budget (the pair class count never exceeds two) plus the singular-series average: `∑_{d≤K} #{pairs at shift d} ≤ 2e·K·Y/E² + K·(remainder)` |
| `Sieve/PrimePairNeighbour` | **`sum_card_neighbour_le`** (a symmetric near-diagonal relation whose pairs differ by at most `K` has total count `≤ #s + 2∑_{d≤K}#{n ∈ s : n+d ∈ s}`), `exp_sub_one_le_three_mul`, `lt_mul_exp_of_log_sub_lt`, `le_add_of_log_close`, **`sum_logNeighbourCount_bigPrimeSet_le`** — the Gallagher neighbour count of a dyadic prime block is a shifted prime-pair count, because a multiplicative window of ratio `e^δ` at height `≤ 2R` has additive length `≤ 6Rδ` |
| `Sieve/DyadicPrimeMeanSquare` | `sum_logNeighbourCount_sieve_le`, **`integral_normSq_dyadicPrimePoly_le`** — the mean square itself: `∫_{-W}^{W}‖∑_{R<p≤2R} p^{-1+2πiw}‖²dw ≤ (5/(4δ))(1/R²)(π(2R)−π(R) + 2(8e·K·R/E² + K·(remainder)))` whenever `2πδW ≤ 1`, `K ≥ 6Rδ`, `δ ≤ 1` |

`#print axioms` on all seven named theorems: `[propext, Classical.choice, Quot.sound]`.  All five
modules are wired into the `GaloisForLFunctions.RHTower` umbrella.

Substituting `δ = 1/(2πW)` and `K = ⌈6Rδ⌉`, the first term is the diagonal `≍ W/(R log R)` and the
second is `≍ 1/E² ≍ (log P₁/log h)²`, which is the card's `1/(log x)²` up to the `(log log)²` the
Selberg level costs (the level constraint `h^{2k} ≤ z` with `k ≍ log log h` forces
`log h ≍ log Y/log log Y`, hence `(log log)²/(log)²` rather than `1/(log)²`).  That loss is
harmless: `(FS8)`'s second term becomes `(log x)^{-2.2}/log log x`, still `o((log x)^{-2-2ε})` for
every `ε < 0.1`, which is all `(FS9)` needs.

**So `(FS7)` is no longer a quoted external input.**  What remains between this card and stage 3 is
the all-interval count `(FS4)` itself — the Perron/minorant assembly of Matomäki–Teräväinen's
Theorem 1.2, whose Dirichlet-polynomial inputs are now the corpus's own.

### Correction to the recorded no-go

The line in "Lean progress" saying that `(FS7)` "genuinely needs the source's Section 5 sieve and is
not reachable from the card text alone" is now superseded in its operative half: the Section 5 sieve
is needed, and it is present.  The Serena memory `cards/route-e-e3-elementary-layer` carries a
matching "do not re-attempt" note that no longer applies to `(FS7)`.

## Source located, and the unique remaining core identified (2026-08-18)

`arXiv:2207.05038` is **Matomäki–Teräväinen, "Almost primes in almost all short intervals II"**.  Its
Theorem 1.1 is the `E₂`/almost-all statement at interval length `(log x)^{2.1}` with
`(log x)^{1.09} < p₁ ≤ (log x)^{1.1}`; **Theorem 1.2 is the bonus all-interval statement**

> for sufficiently large `x`, the interval `(x, x + √x(log x)^{1.55}]` contains `E₃` numbers,

proved (per the paper's own remark) "by following the proof of Theorem 1.1 very closely".  So the
card's `(FS4)` is quoted correctly, and both theorems rest on the *same* new estimate.

### The numerology, redone here

Write `A(s) = P₁(s)P(s)²` with `P₁(s) = ∑_{p ≍ P₁} p^{-s}`, `P(s) = ∑_{p ≍ R} p^{-s}`, and the
parameters of `(FS1)`.  The count's main term is `≍ h/((log P₁)(log x)²) ≍ √x(log x)^{-0.45}/log log x`.
Estimating the transform error by the trivial sup bound on the short polynomial,
`max_t |P₁(1+it)| ≤ ∑_{p ≍ P₁} 1/p ≍ 1/log P₁ ≍ 1/log log x`, together with the *proved* `(FS7)`
`∫_{|t| ≤ U}|P(1+it)|²dt ≪ U/(R log x) + 1/(log x)²`, gives for the sharp-cutoff kernel `≍ x/|t|`

```text
∑_{U dyadic ∈ [T₀,T]} (x/U)·max|P₁|·∫_{|t| ≍ U}|P|²
   ≍ (1/log log x)·[ (x/(R log x))·#{dyadic blocks} + x/(T₀(log x)²) ]
   ≍ (1/log log x)·[ 2√x(log x)^{-0.45}·log log x + h/(log x)² ] ,
```

because `T/T₀ = R/T₀ ≍ log x`, so there are `≍ log log x` dyadic blocks.  The first bracket term is
`≍ √x(log x)^{-0.45}`, i.e. **exactly `log log x` times the main term**.  So:

- the mean value theorem plus `(FS7)` leaves a deficit of precisely one `log log x`;
- `(5.2)`'s stated saving `∫_{T₀}^{T}|P₁P|²dt ≪ (T/(x/h))(log X)^{-2-ε/10}` supplies `(\log x)^{-ε/10}`,
  which covers that `log log x` with room to spare.

That is the whole role of the paper's new Type II estimate for this card, and it is **the unique
remaining analytic input**: `(FS7)` is now a corpus theorem, and the perturbative layer `(FS5)`,
`(FS6)`, `(FS8)`–`(FS14)` was already formalized.

### Why `(5.2)` cannot be cheapened

- No pointwise cancellation in `P₁`.  `log P₁ = 1.1 log log x`, so cancellation in `∑_{p ≍ P₁}p^{-it}`
  uniformly for `|t| ≤ T ≍ √x` is far outside every zero-free region (Vinogradov–Korobov needs
  `log P ≫ (log X)^{2/3+δ}`).
- No gain from the mean value theorem on the product.  `P₁P` has length `P₁R ≍ √x(log x)^{0.55} ≫ T`,
  so the mean value theorem is diagonal-dominated and returns `≍ 1/(log P₁ log R)`, which is *worse*
  than `max|P₁|²·∫|P|²`.
- Shrinking the dyadic range does not help: the mean value theorem's `N∑|a_n|²` term is independent
  of the block length once the block is shorter than the polynomial.

So `(5.2)` genuinely requires a mean value theorem with a saving beyond the diagonal — Watt's
theorem, Deshouillers–Iwaniec, or Heath-Brown's mean value theorem for *sparse* Dirichlet
polynomials, which is the tool the paper's abstract singles out as its innovation.

### Consequence for the Lean plan

The card's remaining gate is now a single named estimate rather than "the all-interval theorem":

```text
(5.2)   ∫_{T₀}^{T} |P₁(1+it)P(1+it)|² dt  ≪  (T h/x)·(log x)^{-2-ε/10} .
```

Everything else on the route — the Perron short-interval formula
(`Sieve/PerronShortInterval.norm_sum_Icc_sub_sum_Icc_sub_perronInterval_le`, already unconditional
and sharp), the mean value theorem (`Sieve/GallagherAlmostDiagonal`), and `(FS7)`
(`Sieve/DyadicPrimeMeanSquare`) — is corpus-owned.  The next milestone in this lane is therefore
Heath-Brown's sparse mean value theorem, not another perturbative layer.

This numerology is my own derivation from the card's parameters and the paper's stated `(5.2)`; the
paper's Section 7 was not retrievable, so the constant bookkeeping above should be re-derived
against the source before it is relied on in a write-up.
