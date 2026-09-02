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

## CORRECTION to the numerology above, and the exact obstruction (2026-08-18, later)

The entry above says the deficit is "exactly one `log log x`, produced by the `≍ log log x` dyadic
blocks".  **That is an artefact of the sharp-cutoff Perron kernel `≍ x/|t|` and is wrong for the
right architecture.**  Redone with a smooth window the block sum disappears, and the deficit becomes
a *bounded constant factor* — but an irreducible one.  Both halves of this correction matter, so
both are recorded.

### The right architecture: window comparison in the multiplicative variable

Let `φ₁` be smooth, supported in `[0, δ]` with `δ = h/x`, `∫φ₁ = 1`; let `φ₂` be the same at width
`Δ = 1/2`.  For a finite Dirichlet polynomial `A(s) = ∑ a_n n^{-s}` with `a_n ≥ 0`,

```text
∑_n (a_n/n) φ_i(log n − log x) = (1/2π) ∫_ℝ φ̂_i(t) x^{it} A(1+it) dt ,
```

so, since `φ̂₁(0) = φ̂₂(0) = 1`,

```text
(1/h)∑_{x<n≤x+h} a_n  ≥  ∑_n(a_n/n)φ₁(·)
                       =  ∑_n(a_n/n)φ₂(·)  −  (1/2π)∫(φ̂₂−φ̂₁)(t)x^{it}A(1+it)dt .
```

The first term is the **long-window count**, evaluated by the prime number theorem on intervals of
length `≍ x` — it is `≍ P₁(1)P(1)²`, the main term.  The difference `φ̂₂ − φ̂₁` vanishes at `t = 0`,
is `O(1)` on `1 ≲ |t| ≲ T₀ = x/h`, and decays faster than any power beyond `T₀`.  **There is no
dyadic-block accumulation**: the error is a single integral over `1 ≲ |t| ≲ T₀`.  So the whole
theorem reduces to the single inequality

```text
(★)   ∫_{1 ≤ |t| ≤ T₀} |P₁(1+it)| · |P(1+it)|² dt  <  (1/2)·P₁(1)·P(1)² .
```

That reduction uses no Type II input at all and is the correct target for formalisation.

### Why the available tools miss `(★)` by a bounded factor, and why it cannot be tuned away

Bounding `|P₁(1+it)| ≤ P₁(1)` reduces `(★)` to a statement about the *large* prime polynomial alone:

```text
(★★)   ∫_{1 ≤ |t| ≤ T₀} |P(1+it)|² dt  <  (1/2) P(1)² .
```

With `P(1) = ∑_{R<p≤2R}1/p ≈ log 2/log R`, the right side is `≈ 0.24/(log R)²`.  The left side is
the diagonal `2T₀/(R log R) = 2/(log R)²` (using `T₀/R = 1/log R`) **plus** the near-diagonal
prime-pair term

```text
2T₀·R^{-2}·#{(p,p') : 0 < |p−p'| ≤ R/T₀}  ≈  4/(log R)² ,
```

which is **independent of `h`**: shortening the window raises `T₀` and lowers the pair range `R/T₀`
in exact proportion.  So `(★★)` fails by a factor `≈ 25`, for *every* `h`, and no window, no
Beurling–Selberg majorant and no constant-chasing repairs it — a Selberg majorant with transform
supported in `[-δ,δ]` contributes `(1/δ)·(pair density 2δ/(log R)²) = 2/(log R)²`, the same
irreducible term.

### What is actually true, and the exact open core

`(★)` itself is true with an enormous margin.  On `|t| ≥ 1` the short polynomial has typical size
`(∑_{p≍P₁}p^{-2})^{1/2} = (P₁ log P₁)^{-1/2}`, not `P₁(1) ≍ 1/log P₁`; inserting the typical size
gives a left side smaller than the right by a factor `≍ (P₁/log P₁)^{1/2} = (log x)^{0.55+o(1)}`.
The loss is therefore entirely in replacing `|P₁|` by its supremum — equivalently, in Cauchy–Schwarz,
which is off by the same factor.

Splitting `(★)` at a level `V₀` (`Sieve/MeanSquareLevelSplit.integral_mul_le_levelSplit`, the `L¹`
companion added for this purpose) leaves exactly one quantity:

```text
[OPEN CORE]   ∫_{S_V} |P(1+it)|² dt  ≤  (small constant) · ∫_{1≤|t|≤T₀}|P(1+it)|² dt ,
              S_V := {t ∈ [1,T₀] : |P₁(1+it)| ≥ V} ,   V ≍ P₁(1).
```

`S_V` has relative measure `≍ log P₁/P₁ = (log x)^{-1.1+o(1)}` — provable from the spaced-point
large-values inequality (`RHTower.LargeValuesDpoly`, `RHTower.WellSpacedSubset`) — but small
*measure* does not bound the `|P|²`-mass, because `|P|²` is spiky: its whole mass `≍ 1/(log R)²`
sits on a set of measure `O(1)`, while `|S_V| ≍ T₀(log x)^{-1.1}` is far larger.  Nothing
measure-theoretic separates them; the separation is arithmetic.  **That is the Type II content, and
this is the precise form in which the two E3 cards still need it.**

Routes eliminated here, with reasons (do not re-attempt):
- adapted-moment/Heath-Brown level sets for `P₁` (`Sieve/PrimePowerSupport`): the constraint
  `P₁^ℓ ≤ T₀` caps the saving at `T₀^{-c}` with `c = 0.1/1.1`, a power saving where a *bounded*
  measure is required;
- the moment method on `P₁^k P^j`: `R > T₀`, so `P₁^kR^j > T₀` for every `j ≥ 1` and the mean value
  theorem's length term cancels the gain;
- Hölder with `∫|P|⁴`: `∫|P|⁴ ≍ 1/(log R)²` is `T₀`-independent while `|S_V| ∝ T₀`;
- expanding `∫|P₁P|²` into a shifted-pair count: the near-diagonal term is `T₀`-independent and of
  the same order as the trivial bound `max|P₁|²∫|P|²`, so the pair sieve gives nothing new here
  (it was decisive for `(FS7)` because there the competitor was the mean value theorem, not a sup).

## RETRACTION of both analyses above — the source was retrieved and read (2026-08-18, later still)

The paper's text was obtained and read in full (arXiv:2207.05038, 26 pp.).  **Both numerology
sections above analyse the wrong construction** and are superseded.

The paper's §7 does not use `p₁p₂p₃` with two large *primes*.  It counts `p₁p₂n` with
`p₁ ∼ P₁ = (log x)^{1.1}`, `p₂ ∼ √(x/P₁)/2`, and `n` weighted by **Harman's minorant `ρ⁻`** on
`(√(x/P₁)/2, 4√(x/P₁)]`.  With that construction:

- the window comparison is against `h₁ = x^{99/100}`, Perron is truncated at `T₀ = x^{1/1000}`, and
  the range `(x/h, x(log x)^{10}]` *is* split dyadically into `≍ log log x` pieces — so the
  dyadic-block count is real after all, and it is absorbed by the `(log x)^{-ε}` saving;
- the long prime variable `P₂` is handled by the improved mean value theorem, giving exactly
  `∫_{T₀}^{T}|P₂|² ≪ T/(√(x/P₁)log x) + (log x)^{-2} ≪ (T/(x/h))(log x)^{-2}` — **this is `(FS7)`,
  and the corpus proof of it is on the paper's own path**;
- Cauchy–Schwarz then pairs `|P₁P|` against `|P₂|` and leaves `(5.2)` for the pair
  `(P₁, P)` with `P` the *minorant* polynomial.

So the "irreducible factor ≈ 25" and the "`log log x` deficit" computed above both concern a
construction the paper does not use; neither is an obstruction to the real argument.  The
`(FS7)` closure and the `(7)`/`(9)` closure are unaffected — they are theorems.

The formalisation of the quoted theorem now has its own card:
`../1-in-progress/matomaki-teravainen-e3-lean-programme.md`, which carries the milestone list read
off the paper, the corpus inventory against each input, and the decision to target the paper's §6.1
(Heath-Brown's identity, exponent `1.615`) rather than §5 (Harman's sieve, exponent `1.55`), because
§6.1 replaces Watt and Deshouillers–Iwaniec — hence Kuznetsov — by Bourgain's zero-density estimate.
**The exponent is not load-bearing for this card**: it enters only through `(FS14)`'s
`|Q_i − u_i| ≪ √(u_iℓ_i)(log u_i)^{1.55}`, and the Route E consequence depends only on `θ = 1/2`,
so `1.55 → 1.615` costs nothing.

## Exponent retune `1.55 → 1.557`, and the removal of Jutila/Bourgain (2026-08-18)

The note above selecting Matomäki–Teräväinen's §6.1 (Heath-Brown identity, exponent `1.615`) over
§5 (Harman's sieve, exponent `1.55`) is **superseded**.  §6.1 was chosen only to avoid Jutila's
large-values estimate; that estimate turns out not to be needed at all.

Huxley's large-values theorem `R ≪ GNV^{-2} + T G³N V^{-6}` — now Lean-proved unconditionally, see
`../1-in-progress/matomaki-teravainen-e3-lean-programme.md` — already gives the paper's Lemma 4.1
with `σ = 7/32 = 0.21875` at `θ = 2/11`, and its Remark 5.2 needs only `σ > 1/5 + 2ε`.  Re-running
§5.3 with `7/32` in place of `49/206` gives `a > max(32/29, 88/79) = 88/79`, hence

```text
Theorem 1.2′ (target).  For all large x, (x, x + √x(log x)^{1+44/79}] contains E₃ numbers,
                        1 + 44/79 = 123/79 = 1.55696… .
```

So `(FS14)` reads `|Q_i − u_i| ≪ √(u_iℓ_i)(log u_i)^{1.557} = u_i^{1/2}N^{o(1)}` — the same
conclusion, since only the `u_i^{1/2}N^{o(1)}` form is used downstream.  Also note that §6.1 does
**not** avoid Watt/Deshouillers–Iwaniec: its Type I sums are handled by §5.1.  The Harman route (§5)
is therefore the one to formalise.

## Lean progress update (2026-08-29) — exact remaining Lemma 3.5 range

Two unconditional, axiom-clean modules now discharge both elementary sides of the Watt/DI hybrid
moment:

- `Sieve/MatomakiTeravainenWattDIOverHeight.lean`: `T ≤ N`;
- `Sieve/MatomakiTeravainenWattProductMeanSquare.lean`: `2AN'² ≤ T`, with
  `(5πe+5π/2)(T/A²)∑_{A<n≤2A}|aₙ|²`.

The latter uses an exact Perron-to-`dirPoly` factorization and multiplicative Young, so it retains
no Watt/DI, spectral, or large-value premise.  Axiom audit is only `propext`,
`Classical.choice`, and `Quot.sound`.

The shared analytic gap with the cofactor card is therefore no longer all of `N ≤ T`: it is
exactly the intermediate range `N < T < 2AN'²`, plus amplification and final exponent
bookkeeping for Matomäki--Teräväinen Theorem 1.2.  Card remains Stage 2.

## Lean progress update (2026-08-30) — reciprocal divisor-energy recovered

`Sieve/MatomakiTeravainenWattDivisorEnergy.lean` proves the unconditional affine envelope

```text
∫_{T/2}^{T}|N(1+it)|⁴|A(1+it)|²dt
  ≪ε (2AN'²)^(ε/2)(N'²)^(ε/2)(T+2AN'²)A⁻²N⁻²
      ∑_{A<n≤2A}|aₙ|².
```

It retains both reciprocal `ℓ²` savings through divisor-fibre convolution.  Direct check,
targeted module build, and axiom audit pass with only `propext`, `Classical.choice`, and
`Quot.sound`.  Remaining gate is the residual Watt/DI intermediate configuration plus
amplification and final Matomäki--Teräväinen Theorem 1.2 bookkeeping.

## Lean progress update (2026-08-30) — literal Watt/DI comparison regions

`Sieve/MatomakiTeravainenWattDivisorRange.lean` turns the divisor-energy envelope into the exact
Lemma 3.5 Watt bound under `2AN'² ≤ A²√T`, and into the exact DI bound under
`2AN'² ≤ A^(5/4)T^(3/4)`. Strengthened capstones choose divisor exponent `ε/5` and discharge its
power from `T ≥ 2`, `A ≤ T`, `N ≤ T`, and `N' ≤ 2N`. Direct check, targeted build, and
six-declaration axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; module is
umbrella-wired.

These are intermediate comparison theorems, not retained hypotheses of the card. Remaining work
must derive height bounds and scale partition from paper parameters, handle any complementary
configuration, and perform amplification plus Theorem 1.2 assembly.

## Lean progress update (2026-08-31) — height dichotomy discharged internally

`Sieve/MatomakiTeravainenLemma35CoveredRange.lean` combines the elementary `T ≤ N` branch with the
reciprocal-divisor `N < T` branch for both literal Watt and Deshouillers--Iwaniec envelopes.  The
new capstones retain no supplied comparison between `N` and `T`; `A ≤ T` and the product-length
condition are needed only on the sub-height branch where divisor energy consumes them.  Direct
check, targeted leaf build, and axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired.

Remaining shared gap is the actual Proposition-2.2 scale routing for the residual `N < T` cases
where `A > T` or the applicable product-length inequality fails, followed by amplification and
Theorem 1.2 assembly.  Card remains Stage 2.

## Lean progress update (2026-08-31) — Heath--Brown primitive-direction packing

`Sieve/HeathBrownFareyWindow.lean` proves the exact quadratic Farey-window count for primitive
positive collision directions.  Together with `Sieve/HeathBrownSparseRayScaling.lean`, this closes
the two elementary components of Heath--Brown Lemma 6 without retaining a lattice-basis premise:
quadratic packing of nonexceptional directions and exact transport of one exceptional ray.  Direct
check, targeted leaf build, and all-three-theorem axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.
Weighted exceptional-direction assembly, Theorem 4(iii)'s two-scale iteration, residual
Proposition-2.2 routing, amplification, and final Theorem 1.2 assembly remain.  Card stays Stage 2.

## Lean progress update (2026-08-31) — weighted primitive-ray assembly

`Sieve/HeathBrownPrimitiveWindow.lean`, `Sieve/HeathBrownPrimitiveLogWindow.lean`, and
`Sieve/HeathBrownPrimitiveRayMass.lean` now prove full positive-slope packing, exact logarithmic
collision-window count `≤ 4 delta Q²+1`, and multiplicity-weighted two-scale law

```text
rayMass N ≤ 15 delta N²
  + (floor(N/N₀)+1) rayMass N₀
  + 2 floor(N/N₀)+1.
```

Finite layer cake keeps endpoint loss at `N/N₀`.  No exceptional direction, lattice basis,
packing, layer-cake, or inverse-square premise remains.  Direct checks and targeted leaf builds
pass; all nineteen theorem declarations across three leaves audit to only
`[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired without an umbrella build.

Card remains Stage 2.  Source-level reindexing and coefficient-weighted summation of complete
Heath--Brown collision form, Theorem 4(iii)'s iteration, Proposition-2.2 routing, amplification,
and final Matomäki--Teräväinen all-interval supply theorem remain.

## Lean progress update (2026-08-31) — literal source collision reindexing

`Sieve/HeathBrownPositiveCollisionRayReindex.lean` identifies the literal closed
difference-of-logs collision square on `[1,N]²` exactly with primitive ray mass.  Its capstone
discharges cofactor ordering by coordinate swap and gives the direct two-scale collision-count
law with explicit constants.  No gcd decomposition, ray partition, source-log conversion, or
cofactor-ordering premise remains.  Direct check, targeted build (`9098/9098`), and nineteen-
theorem axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; module is
umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared gate is coefficient-weighted summation over actual dense
supports and sparse cofactor pairs, Theorem 4(iii)'s iteration, Proposition-2.2 routing,
amplification, and final all-interval theorem.

## Lean progress update (2026-08-31) — finite Heath--Brown two-scale mean value closed

`Sieve/HeathBrownSparseCollisionTwoScale.lean` proves the ordered-cofactor aggregate law

```text
J(A,N,T) ≤ 15 N²|A|²/T
  + (floor(N/N₀)+1)J(A,N₀,T)
  + (2 floor(N/N₀)+1)|A|²,
```

dominates existing `[0,1]`-weighted strict collision mass on arbitrary bounded dense supports,
and composes it with exact `M(it)Q(it)` mean-value reduction.  Coefficient bounds, strict-to-closed
passage, cofactor summation, ray decomposition, and analytic comparison are discharged.  Direct
check, final targeted build (`9101/9101`), and nine-theorem axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without umbrella build.

Card remains Stage 2.  Finite Heath--Brown Lemma 6/Theorem 4(iii) comparison core is closed.
Paper-specific iterative parameter substitution, Proposition-2.2 routing, amplification, and final
Matomäki--Teräväinen all-interval supply theorem remain.

## Lean progress update (2026-08-31) — fully integral Heath--Brown recurrence

`Sieve/HeathBrownSparseMeanValueTwoScale.lean` removes the smaller closed aggregate from the
brick-51 output.  Full unit-weight support `[1,N₀]` at height `T/2` strictly contains every closed
`1/T` product collision, and reverse finite-frequency mean value gives

```text
J(A,N₀,T) ≤ (5/(2T)) I(T/2; A,[1,N₀]).
```

The resulting capstone is an entirely integral two-scale recurrence for the original weighted
`M(it)Q(it)` mean square.  Positive-index conversion, support membership, strict endpoint slack,
unit-weight collision cardinality, reverse comparison, and recurrence substitution are proved
internally.  Direct source check, targeted leaf build (`9102/9102`), and all-seven-theorem axiom
audit pass with only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without
an umbrella build.

Card remains Stage 2.  Remaining shared gate is paper-specific iteration/parameter substitution,
residual Proposition-2.2 Watt/DI routing, amplification, and final Matomäki--Teräväinen all-interval
supply theorem.

## Lean progress update (2026-08-31) — Heath--Brown Cauchy/divisor square lift

`Sieve/HeathBrownSparseMeanValueSquareLift.lean` proves the exact divisor-normalised square
reconstruction and squared Cauchy lift from the unit interval through `N` to the interval through
`N²`.  Sparse-factor mean square, `[0,1]`-coefficient domination, divisor-fibre bounds,
continuity, and integrability are all internal Lean theorems, not hypotheses.  Direct check,
targeted leaf build (`9107/9107`), and all-thirty-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared gate is exact Theorem 4(iii) recurrence iteration and
integer parameter algebra, residual Proposition-2.2 Watt/DI routing, amplification, and final
Matomäki--Teräväinen all-interval supply theorem.

## Lean progress update (2026-08-31) — closed Heath--Brown one-step self-bound

`Sieve/HeathBrownSparseMeanValueSelfBound.lean` closes the exact finite system produced by the
two-scale recurrence and Cauchy/divisor lift.  Zero extension, symmetric height monotonicity,
explicit-envelope positivity, and the quadratic implication `I≤a+bJ`, `J²≤kI` implies
`I≤2a+b²k` are proved internally.  Direct check, targeted leaf build (`9108/9108`), and all-nine-
declaration axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; module is
umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared gate is integer scale selection, second-branch recurrence
and exponent algebra for exact Theorem 4(iii), then residual Proposition-2.2 routing,
amplification, and final all-interval supply theorem.

## Lean progress update (2026-08-31) — exact square-root branch selected

`Sieve/HeathBrownSparseMeanValueSqrtScale.lean` selects `K=Nat.sqrt N` in the closed self-bound and
proves `K²≤N` and `N/K≤K+2` internally.  Its explicit three-term inequality has no rounding,
quotient, or scale-selection premise.  Direct check, targeted leaf build (`9109/9109`), and all
three declaration axiom audits pass with only `[propext, Classical.choice, Quot.sound]`; module is
umbrella-wired without an umbrella build.

Card remains Stage 2.  Divisor/rpow absorption, second-branch recurrence, and exact Theorem 4(iii)
regime union remain before residual Proposition-2.2 routing, amplification, and all-interval
supply.

## Lean progress update (2026-08-31) — first branch fully de-rounded

`Sieve/HeathBrownSparseMeanValueFirstBranch.lean` proves the natural-to-real square-root transfer
and absorbs the exact divisor scale into `divisorBoundConst η·N^η`.  Its explicit first-branch
mean-value theorem has no floor, divisor, rpow, or positivity premise.  Direct check, targeted leaf
build (`9110/9110`), and all-three-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

Card remains Stage 2.  First-branch regime absorption and two-step parameter algebra remain before
exact Theorem 4(iii), residual Proposition-2.2 routing, amplification, and all-interval supply.

## Lean progress update (2026-08-31) — arbitrary-scale Heath--Brown recurrence

`Sieve/HeathBrownSparseMeanValueArbitraryScale.lean` proves collision-support monotonicity and
extends the exact recurrence to every positive auxiliary cutoff `N₀`, matching the unrestricted
scale in Heath--Brown's Lemma 6.  The coefficient-faithful two-step theorem now has no `N₀≤N`
premise.  Direct checks, targeted leaf builds (`9103/9103`, `9110/9110`), and the focused axiom
audit pass with only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without
an umbrella build.

Card remains Stage 2.  Exact second-scale selection and exponent absorption remain before the
Theorem 4(iii) union and downstream Route-E assembly.

## Lean progress update (2026-08-31) — source-faithful real-ratio second scale

`Sieve/HeathBrownPrimitiveRayMassRealScale.lean` proves Heath--Brown's exact `2N/N₀`
primitive-ray coefficient uniformly for positive `N₀`, including `N<N₀`.
`HeathBrownSparseMeanValueRealScale.lean` and `HeathBrownSparseMeanValueRealIteration.lean` lift
it through collision aggregation, integral recurrence, square lift, and quadratic closure.
`HeathBrownSecondScaleParameters.lean` supplies the fully proved natural scale
`⌈max(T^(1/3),(RT)^(1/4))⌉₊`; `HeathBrownSparseMeanValueSecondScale.lean` selects it and discharges
all scale premises.

Direct checks, targeted leaf builds (`9098/9098`, `9104/9104`, `9111/9111`, `9111/9111`,
`9115/9115`), and the eighteen-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired without an umbrella build.

Card remains Stage 2.  Explicit exponent absorption and Theorem 4(iii) union remain before
residual Proposition-2.2 routing, amplification, and final all-interval supply theorem.

## Lean progress update (2026-08-31) — exact Heath--Brown Theorem 4(iii)

`Sieve/HeathBrownSecondScaleAlgebra.lean`,
`HeathBrownSparseMeanValueTheoremFourAlgebra.lean`, and
`HeathBrownSparseMeanValueTheoremFour.lean` close the exact coefficient-faithful estimate

```text
I ≤ (95π/2) N²R² + Cη (NT)^η (NRT + N R^(7/4) T^(3/4))
```

with explicit `Cη`.  Arbitrary sparse phases and dense `[0,1]` coefficients are retained; empty
support, `N=0`, scale selection, rounding, divisor loss, crossover, and all exponent algebra are
discharged.  Direct checks, targeted leaf builds (`9116/9116`, `9117/9117`, `9118/9118`), and the
ten-declaration axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; capstone is
umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared analytic work is Proposition-2.2 routing,
amplification, and final Matomäki--Teräväinen Theorem 1.2 assembly.

## Lean progress update (2026-08-31) — literal Lemma 3.4 and published refinement

`Sieve/HeathBrownSparseMeanValueBounded.lean`,
`HeathBrownSparseMeanValueBoundedRefined.lean`, and
`HeathBrownSparseMeanValueLemma34.lean` close Matomäki--Teräväinen Lemma 3.4 with the published
quantifiers and coefficient classes.  The formal statements retain arbitrary bounded complex
sparse coefficients, arbitrary real dense coefficients, reciprocal weights, source/dyadic
supports, and the internally constructed coefficient maximum.  They include the exact refinement
deleting the mixed term under `N ≥ T^(2/3)` or sparse cardinality at most `T^(1/3)`.

No sign, nonemptiness, height-two, normalization, continuity, or analytic hypothesis remains.
Direct checks, targeted leaf builds (`9124/9124`, `9125/9125`), and the focused
seventeen-declaration axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; the
capstone is umbrella-wired without an umbrella build.

Card remains Stage 2.  Lemma 3.4 is closed.  Remaining shared work is Lemma 3.5's genuine Type I
and Type I/II analytic cancellation, routing/amplification, and final Theorem 1.2 assembly;
Proposition 2.2 bookkeeping and Type II are already closed.

## Lean progress update (2026-09-02) — distinct-modulus complete correlation

`Sieve/KloostermanDistinctModulusCompleteCorrelation.lean` closes the complete-period arithmetic
inside the remaining Type-I Kloosterman Gram problem: correlations at distinct positive moduli
vanish over a full product period. It decomposes the literal `[1,M]` correlation into this zero
main plus an explicit boundary-discrepancy remainder and proves the unconditional second-moment
bound `q*r*(phi(q)+phi(r))/2`, with direct stored-modulus instantiations.

Direct check and targeted build pass (`12572/12572`). All thirteen public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2. Remaining shared analytic core is quantitative cancellation for the
incomplete distinct-modulus remainder at source ranges, then Lemma 3.5(ii) routing,
amplification, and all-interval Matomäki--Teräväinen supply; no estimate is assumed.

## Lean progress update (2026-09-02) — least-common-multiple completion

`Sieve/KloostermanDistinctModulusLcmCompletion.lean` sharpens the shared Type-I Gram carrier from
product-period to least-common-multiple completion. Unequal-modulus complete correlation vanishes
on `lcm(q,r)`, arbitrary intervals are exact lcm-boundary remainders, and their unconditional
second-moment budget is `lcm(q,r)*(phi(q)+phi(r))/2`, a full `gcd(q,r)` gain over the previous
product-period bound.

Direct check and targeted build pass (`12573/12573`). All nine public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining shared analytic core is cancellation inside the sharp incomplete
common period at source ranges, then Lemma 3.5(ii) routing, amplification, and all-interval supply;
no estimate is assumed.

## Lean progress update (2026-09-02) — exact terminal common-period block

`Sieve/KloostermanDistinctModulusTerminalBlock.lean` proves that each unequal-modulus `[1,M]`
correlation in the shared Type-I Gram problem is exactly the shifted block of length
`M mod lcm(q,r)`. All full common-period blocks vanish; an exact-residual-length totient bound and
stored-modulus identities are included.

Direct check and targeted build pass (`12736/12736`). Its five public results and exposed
periodicity theorem audit with only `[propext, Classical.choice, Quot.sound]`; leaf is
umbrella-wired without umbrella build.

Card remains Stage 2. Remaining shared analytic core is collective weighted cancellation of these
literal terminal blocks, then Lemma 3.5(ii) routing, amplification, and all-interval supply; no
estimate is assumed.

## Lean progress update (2026-09-02) — weighted terminal-block Gram

`Sieve/KloostermanDistinctModulusTerminalGram.lean` restores the source modulus weights around the
literal terminal blocks and identifies the existing distinct-modulus Gram exactly with that
carrier. It yields the full Gram split into same-modulus plus weighted terminal pieces and proves
the closed pairwise residual-length budget.

Direct check and targeted build pass (`12737/12737`). All four public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining shared primitive is collective cancellation of this exact carrier
inside the source-index quadratic form at paper ranges, then Lemma 3.5(ii), amplification, and
all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — source-weighted terminal quadratic receiver

`Sieve/KloostermanDistinctModulusTerminalQuadratic.lean` lifts the exact terminal carrier into the
existing source-index quadratic and erased off-diagonal forms. It proves their exact
equal-modulus/terminal split and an unconditional bound retaining all source coefficients, modulus
weights, and pairwise residual lengths.

Direct check and targeted build pass (`12738/12738`). All four public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining shared estimate is collective cancellation of the literal
source-weighted terminal off-diagonal at paper ranges, plus equal-modulus Ramanujan routing, then
Lemma 3.5(ii), amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — three-way Ramanujan/terminal frontier

`Sieve/KloostermanSameModulusRamanujanQuadratic.lean` closes equal-modulus completion routing
through the weighted source quadratic. Transform energy and source off-diagonal decompose exactly
into Ramanujan main, bounded same-modulus remainder, and terminal distinct-modulus carrier, with a
closed source-weighted remainder budget.

Direct check and targeted build pass (`12739/12739`). All seven public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining shared work is Ramanujan-main square-energy control and collective
terminal-carrier cancellation at paper ranges, then Lemma 3.5(ii), amplification, and all-interval
supply; no estimate is assumed.

## Lean progress update (2026-09-02) — Ramanujan main square energy

`Sieve/KloostermanSameModulusRamanujanEnergy.lean` identifies the full weighted Ramanujan main with
a nonnegative real sum of complete Kloosterman column-transform square energies, retaining exact
interval density and modulus weights.

Direct check and targeted build pass (`12740/12740`). All six public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Equal-modulus main/remainder classification is closed. Remaining shared
primitive is collective control of the terminal distinct-modulus carrier at paper ranges, then
Lemma 3.5(ii), amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — exact scalar analytic frontier

`Sieve/KloostermanAnalyticFrontier.lean` gives the full transform-output energy a named exact
frontier: nonnegative Ramanujan main energy, same-modulus completion remainder, and terminal
distinct-modulus carrier. It proves closed full-source budgets, combined imaginary cancellation,
and an unconditional scalar energy bound with no analytic premise.

Direct check and targeted build pass (`12741/12741`). All six public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. This closes the elementary absolute-value baseline only. Remaining shared
primitive is collective spectral cancellation beyond the terminal-carrier budget, followed by
source routing into Lemma 3.5(ii), amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — terminal geometric cancellation

`Sieve/KloostermanCrossPhaseGeometric.lean` proves cross-unit phase nonresonance for unequal
positive moduli. `Sieve/KloostermanTerminalGeometricCancellation.lean` expands the literal
terminal block into nontrivial geometric orbits and proves a length-independent reciprocal-chord
bound, combined pointwise with the exact-length totient estimate.

Direct checks and targeted builds pass (`12746/12746`, `12747/12747`). Eleven public declarations
across both leaves audit with only `[propext, Classical.choice, Quot.sound]`; leaves are
umbrella-wired without umbrella build.

Card remains Stage 2. Remaining shared primitive is collective control of reciprocal chord
denominators and signed modulus/source aggregation at paper ranges, then Lemma 3.5(ii),
amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — coprime cross-frequency CRT compression

`Sieve/KloostermanCoprimeCrossPhaseFrequency.lean` proves an explicit equivalence between
coprime cross-unit pairs and units modulo the product period, with CRT coordinates `(-r*x, q*y)`.
Its standard additive character is the exact terminal cross-phase ratio.  Thus the double
reciprocal-chord carrier compresses losslessly to one product-unit sum, and the terminal bound is
available in that form.

Direct check and targeted leaf build pass (`12749/12749`).  All eight public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Remaining shared primitive is a harmonic product-period chord estimate,
then noncoprime gcd strata and signed modulus/source aggregation at paper ranges, Lemma 3.5(ii),
amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — product-unit harmonic chord bound

`Sieve/KloostermanProductUnitChordSum.lean` proves the collective bound
`sum_units 2/||1-e_N(z)|| <= N*(1+log N)` from two-sided Jordan separation and existing harmonic
finite-family control.  With brick 122, this gives every coprime terminal block and stored Gram
correlation an unconditional length-independent product-period harmonic bound.

Direct check and targeted leaf build pass (`13483/13483`).  All eight public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Coprime reciprocal-denominator aggregation is closed.  Remaining shared
primitive is noncoprime gcd stratification and signed modulus/source aggregation at paper ranges,
then Lemma 3.5(ii), amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — product-period slices without coprimality

`Sieve/KloostermanProductFrequencySliceBound.lean` proves that every unequal-modulus cross phase
has product-period frequency `q*val(y)-r*val(x)`, with no coprimality premise.  Fixing either unit
coordinate gives an injective nonzero frequency family.  General cyclic chord separation and
harmonic representative bounds therefore control the full double denominator carrier by the
better of its two totient-weighted product-period slice budgets, and the exact terminal/stored
correlations inherit that bound.

Direct check and targeted leaf build pass (`13484/13484`).  All sixteen new theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Noncoprime denominator aggregation is closed.  Remaining shared primitive
is signed modulus/source aggregation and cancellation beyond the absolute harmonic budget at paper
ranges, then Lemma 3.5(ii), amplification, and all-interval supply; no estimate is assumed.

## Lean progress update (2026-09-02) — source/modulus product-harmonic aggregation

`Sieve/KloostermanProductHarmonicQuadratic.lean` pushes the noncoprime product-period bound through
all signed modulus weights and source coefficients.  Both terminal/stored Gram entries and their
full or erased source quadratics receive explicit closed budgets; the quadratic factor is exactly
the square of source ℓ¹ mass times the weighted modulus-pair budget.

Direct check and targeted leaf build pass (`13485/13485`).  All six theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2.  Absolute signed source/modulus aggregation is closed.  Remaining shared
primitive is spectral cancellation beyond this product-harmonic ℓ¹ baseline at paper ranges, then
Lemma 3.5(ii), amplification, and all-interval supply; no estimate is assumed.
