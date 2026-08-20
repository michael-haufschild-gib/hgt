# Route E cofactor-amplified \(E_3\) token supply

- **ID:** `ROUTE-E-COFACTOR-AMPLIFIED-E3-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-CAPACITY SURVIVOR
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** the whole elementary layer is formalized — exact parity reversal, the
  \(s\leftrightarrow2s\) cofactor pairing and displacement scaling in
  `MobiusCofactorAmplifiedToken.lean`, the parity-balance inequality behind `(7)` and `(9)` and the
  dyadic slice count `(6a)` in `RouteECofactorParityBalance.lean`, and the amplified displacement
  `(5)` in `RouteEForbiddenSupportStability.lean`.  The analytic supply rests on the published
  Matomäki--Teräväinen all-interval theorem and is not formalized.  See "Lean progress".

## Lean progress

`formal/GaloisForLFunctions/RHTower/RouteECofactorParityBalance.lean` formalizes the card's key
elementary claim, that **parity balance needs no signed Möbius estimate**:

- `parityClass Band σ T` and `oddBase Band T` are the two cofactor sets of the construction: the
  band-avoiding integers below `T` of a prescribed Möbius parity, and the odd band-avoiding
  squarefree integers below `T/2`;
- `moebius_two_mul` is the sign reversal `μ(2s) = -μ(s)` for odd `s`, and `pairMap σ` is the
  pairing itself — keep `s` when it already carries the target parity, otherwise double it;
- `pairMap_mem` shows the pairing lands in the requested class: doubling preserves band-avoidance
  (because `2` lies below the band), preserves the bound `2s ≤ T`, and flips the sign, and a
  squarefree `s` has `μ(s) = ±1` so the flipped sign is the target one;
- `pairMap_injOn` is injectivity — an odd cofactor is never the double of another;
- `half_sum_oddBase_le_sum_parityClass` is the conclusion: **each** parity class carries at least
  half the harmonic mass of the odd squarefree band-avoiding source set.  This is the structural
  half of `(7)` and `(9)`; the classical unsigned squarefree estimate that turns it into `≍ √T`
  and `≍ log T` is a separate input.

The same file proves the slice bookkeeping `(6a)`: `dyadic_mem_iff` characterises the dyadic
powers inside `[A,B]` by their binary logarithms, and `le_card_dyadicSlices` bounds their number
below by `log(B/A)/log 2 - 1`, which at `A = L^{a₀}`, `B = 2L^{a₁}` is the `≍ (a₁-a₀) log log U`
slice count.

The displacement `(5)` is `ForbiddenSupport.abs_amplified_gap_le` together with
`ForbiddenSupport.mul_sqrt_div_eq_sqrt_mul`: a near-square-root token at the reduced centre `u/t`
amplified by `t` stays within `√(ut)` times the same polylogarithmic factor of `u`.  The parity
`(4)` is `mobiusCofactorToken_reverses`.

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

Not formalized: the quantitative all-interval supply `(6)`, which is the published
Matomäki--Teräväinen minorant, and the classical unsigned squarefree harmonic estimates quoted in
`(7)` and `(9)`.

## Statement

Fix \(0<\eta<1/6\), let \(U\) be large, and put \(T=U^{2\eta}\).  Uniformly for
\(u\in[U,2U]\) with \(\mu(u)\ne0\), there is a source-fixed family
\({\cal Q}_\eta(u)\) of squarefree integers \(q\) satisfying

\[
\mu(q)=-\mu(u),\qquad
0<q-u\ll U^{1/2+\eta}(\log U)^{1.55},
\tag{1}
\]

and

\[
\#{\cal Q}_\eta(u)
\gg_\eta
\frac{U^{1/2+\eta}}
     {(\log U)^{0.45}}.
\tag{2}
\]

The physical target union across one dyadic scale has the lower bound

\[
\#\bigcup_{u\in[U,2U]}{\cal Q}_\eta(u)
\gg_\eta \frac{U}{\log U}.
\tag{3}
\]

The targets in `(3)` are physical integers, not labeled representations.

## Construction

Put \(a_1=1.1\) and fix \(a_0<a_1\) inside the uniform
Matomäki--Teräväinen parameter interval
\([1.1-10^{-4},1.1]\).  For every squarefree \(t\le T\) with
\(\mu(t)=\mu(u)\), exclude from \(t\) the full polylogarithmic band
\[
(\log(U/t))^{a_0}\le p\le2(\log(U/t))^{a_1}.
\]
For each disjoint dyadic prime slice in that band, use a distinguished prime

\[
p_1\asymp(\log(U/t))^a,\qquad a_0\le a\le a_1.
\]

Apply the Matomäki--Teräväinen all-interval theorem at \(y=u/t\).  It supplies

\[
m=p_1p_2p_3\in
\left(y,y+\sqrt y(\log y)^{1.55}\right]
\]

with

\[
p_1\asymp(\log y)^a,
\qquad
p_2,p_3\asymp\frac12\sqrt{\frac{y}{p_1}}.
\]

Set \(q=tm\).  Since \(\eta<1/6\), for every \(t\le T\) and large \(U\),

\[
p_2,p_3>T.
\]

The excluded full \(p_1\)-band therefore makes \(t\) and \(m\) coprime.  It also makes \(t\)
recoverable from \(q\): it is exactly the product of the prime factors of \(q\) at most \(T\)
outside that full band.  The remaining small prime factor uniquely identifies its dyadic
\(p_1\)-slice.  Hence target families belonging to distinct \(t\)'s or distinct slices are
disjoint.

The parity is exact:

\[
\mu(q)=\mu(t)\mu(m)=-\mu(t)=-\mu(u).
\tag{4}
\]

The displacement is

\[
0<q-u
\ll t\sqrt{\frac ut}\left(\log\frac ut\right)^{1.55}
\ll\sqrt{Ut}(\log U)^{1.55},
\tag{5}
\]

which proves `(1)`.

## Row supply

For fixed \(t\) and one dyadic \(p_1\)-slice, the quantitative form of the published theorem gives

\[
\gg
\frac{\sqrt{U/t}(\log U)^{1.55}}
     {(\log\log U)(\log U)^2}
=
\frac{\sqrt{U/t}}
     {(\log U)^{0.45}\log\log U}
\tag{6}
\]

tokens in its natural interval.

There are
\[
K\asymp(a_1-a_0)\log\log U                              \tag{6a}
\]
disjoint dyadic slices between \((\log y)^{a_0}\) and \((\log y)^{a_1}\).
For a lower slice with natural interval
\(H_a=\sqrt y(\log y)^{1+a/2}\), partition the common interval
\[
H_*=\sqrt y(\log y)^{1+a_1/2}
\]
into \(H_*/H_a+O(1)\) natural subintervals.  The all-interval theorem applies in each.  Uniformity
of its minorant theorem for \(a\in[1.1-10^{-4},1.1]\) makes the lower-bound constant independent
of the slice.  Therefore every slice contributes
\[
\gg \frac{H_*}{(\log U)^2\log\log U}
\]
tokens to the common interval.  Distinct distinguished-prime slices give disjoint physical
integers, so `(6a)` cancels the single-slice \(\log\log U\) loss:
\[
\#\{m\text{ from all slices}\}
\gg \frac{\sqrt{U/t}}{(\log U)^{0.45}}.                 \tag{6b}
\]

Parity balance needs no signed Möbius estimate.  For large \(U\), the fixed prime \(2\) lies
below the excluded polylogarithmic band.  Pair every odd squarefree \(s\le T/2\) avoiding that
band with \(2s\).  Exactly one member of \(\{s,2s\}\) has each Möbius parity.  The classical
unsigned squarefree estimates therefore give, for either \(\sigma\in\{-1,+1\}\),

\[
\sum_{\substack{t\le T\\\mu(t)=\sigma\\
                 t\ {\rm avoids\ the\ full\ band}}}t^{-1/2}
\asymp_{a_0,a_1}\sqrt T
\tag{7}
\]

because removing the full band multiplies the unsigned squarefree main term by a fixed positive
Euler factor.  Mertens' prime reciprocal theorem gives
\[
\prod_{(\log U)^{a_0}\le p\le2(\log U)^{a_1}}
  (1+p^{-1})^{-1}\asymp_{a_0,a_1}1.
\]
Thus both allowed parity classes remain \(\asymp\sqrt T\).  Summing `(6b)` over the disjoint
\(t\)-families proves `(2)`.

## Physical target count

For fixed \(t\), select disjoint source intervals of length

\[
H_t\asymp\sqrt{Ut}(\log U)^{1.55}
\]

inside a fixed interior portion of \([U,2U]\).  There are \(\asymp U/H_t\) such intervals, and
`(6b)` applies to each.  Thus fixed \(t\) contributes

\[
\gg
\frac{U}{t(\log U)^2}
\tag{8}
\]

distinct targets.  The same elementary \(s\leftrightarrow2s\) pairing and unsigned squarefree
harmonic estimate give

\[
\sum_{\substack{t\le T\\ \mu(t)=\sigma}}
\frac1t
\asymp\log T
\tag{9}
\]

for either \(\sigma\in\{-1,+1\}\), also after the full-band exclusion.
Since \(\log T=2\eta\log U\), summing `(8)` and using unique \(t\)-decoding proves `(3)`.

## Route E consequence

Suppose an independent decomposition genuinely leaves
\(O(U^{1-\kappa+o(1)})\) unmatched exceptional block centers.
For any fixed \(0<\eta<\min\{\kappa,1/6\}\):

1. `(3)` is asymptotically larger than the total exceptional set;
2. exceptional fallback displacement has exponent
   \(\theta=\tfrac12+\eta\);
3. the exact threshold
   \(\kappa\ge\theta-\tfrac12\) is satisfied strictly.

Thus aggregate displacement and total physical cardinality pass for this fallback subproblem.
The remaining fallback gate is local: prove that every exceptional subset has enough nearby
targets, rather than merely comparing global cardinalities.

## Hostile audit

- Cofactors are physical factors of \(q\), not marker labels; disjoint factor ranges make them
  uniquely decodable.
- Pairing \(s\) with \(2s\) proves both parity lower bounds without importing cancellation of
  \(\mu(t)\); `mobiusCofactorPair_two_reverses` formalizes its exact sign law.  The parity
  restriction loses only a constant, not a power or logarithm.
- Summing the uniform disjoint \(p_1\)-slices first recovers the fixed-slice
  \(\log\log U\) loss; the \(t\)-sum then recovers one full \(\log U\).  The resulting
  \(U/\log U\) union is still a zero-density family and is smaller by \(\log\log U\) than the
  ordinary \(L^1\) defect mass obtained directly from Menon's sharp mean-square estimate.
- `(3)` is enough for a power-saving exceptional set but does not imply Hall expansion:
  exceptional centers may cluster.
- Published almost-all theorems produce exceptional windows plus a tolerated signed defect on
  every ordinary window; they do not by themselves produce the unmatched-center hypothesis in
  this section.
- Classical weighted squarefree sums and the published all-interval \(E_3\) theorem, including
  its stated uniform \(a\)-interval, are the external inputs.  No literature source was found
  for the disjoint multi-band aggregation, uniquely decoded cofactor amplification, or their
  Route E exceptional-capacity synthesis.

## Status

`[PROVED HERE; CANDIDATE NEW SCIENTIFIC KNOWLEDGE, NOVELTY UNVERIFIED]`.
Conditional global exceptional capacity and strict-half exponent both close, with the stronger
\(U/\log U\) physical union.  Local Hall anti-concentration remains open, and the parent card
separately retains the ordinary-window defect current.

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

## The mean-square input of the shared all-interval theorem is now Lean (2026-08-18)

This card's `(6)` is the quantitative form of Matomäki--Teräväinen's all-interval `E₃` theorem, the
same external input as the sibling card `route-e-forbidden-support-e3-stability`.  One of its two
Dirichlet-polynomial ingredients — the mean square of the large prime variable, `(FS7)` on the
sibling card — is now an unconditional corpus theorem rather than a quotation.  The route is the
*two-dimensional upper-bound sieve*, which the corpus already owned from the Matomäki--Radziwiłł
programme (`Sieve/RoughPairSieve`, `Sieve/RoughPairCount`), specialised to prime pairs:

`Sieve/PrimePairCount`, `Sieve/PrimePairShiftSum`, `Sieve/PrimePairAverage`,
`Sieve/PrimePairNeighbour`, `Sieve/DyadicPrimeMeanSquare` — see the sibling card for the
theorem-by-theorem table.  Capstone:

```text
integral_normSq_dyadicPrimePoly_le :
  ∫_{-W}^{W} ‖∑_{R<p≤2R} p^{-1+2πiw}‖² dw
    ≤ (5/(4δ))(1/R²)( π(2R)−π(R) + 2( 8e·K·R/E² + K·(Selberg remainder) ) )
```

for `2πδW ≤ 1`, `δ ≤ 1`, `K ≥ 6Rδ`, with `E = exp(mertensS h − mertensS P₁)`.  Axioms:
`[propext, Classical.choice, Quot.sound]`.

The card's own elementary debt — the unsigned squarefree harmonic estimates `(7)` and `(9)` — is
untouched by this and is still open.

## The elementary debt `(7)` and `(9)` is CLOSED (2026-08-18)

Both unsigned squarefree harmonic estimates are now unconditional Lean theorems, so the card's own
elementary layer is complete and nothing but the shared all-interval theorem remains.

`RHTower.sum_inv_parityClass_ge` — **`(9)`** — and `RHTower.sum_inv_sqrt_parityClass_ge` — **`(7)`**:
for a band `B` of primes with `2 ∉ B` and Mertens mass `∑_{p ∈ B} 1/p ≤ 1/8`, and either sign
`σ = ±1`,

```text
(1/16)·log⌊T/2⌋ − 7/16  ≤  ∑_{t ∈ parityClass B σ T} 1/t ,
(1/8)·√⌊T/2⌋   − 1      ≤  ∑_{t ∈ parityClass B σ T} 1/√t .
```

The card's band `(log U)^{a₀} ≤ p ≤ 2(log U)^{a₁}` with `a₁ = 1.1`, `a₀ ≥ 1.1 − 10⁻⁴` has Mertens
mass `log(a₁/a₀) + o(1) ≈ 9·10⁻⁵`, far below `1/8`, so the hypothesis is satisfied for large `U`.

### How it is proved

| module | content |
|-|-|
| `Sieve/ElementaryHarmonicBounds` | **`two_mul_sqrt_succ_sub_two_le_sum`** (`2√(M+1) − 2 ≤ ∑_{n≤M} n^{-1/2}`, telescoping; the matching upper bound `≤ 2√M` was already `RHTower.sum_one_div_sqrt_le`), `sum_filter_dvd_eq` (the multiples of `p` reindexed by their cofactor), **`sum_inv_sqrt_dvd_le`** (`≤ 2√M/p`), **`sum_inv_dvd_le`** (`≤ (1+log M)/p`), `sum_telescope_inv`, **`sum_inv_sq_odd_le`** (`∑ 1/d² ≤ 1/4` over any set of odd `d ≥ 3`, from `1/(2j+1)² ≤ (1/4)(1/j − 1/(j+1))`) |
| `Sieve/CoprimeSquarefreeHarmonic` | `sum_biUnion_le_of_nonneg`, `notCoprime_subset_biUnion`, **`sum_coprime_ge`**, `notSquarefree_subset_biUnion`, `sum_inv_sq_coveringPrimes_le`, `sum_notSquarefree_le`, **`sum_inv_coprime_squarefree_ge`** (`≥ (log M)/8 − 7/8`), **`sum_inv_sqrt_coprime_squarefree_ge`** (`≥ √M/4 − 2`), both under `∑_{p ∣ Q} 1/p ≤ 5/8` and `2 ∣ Q` |
| `RHTower/RouteECofactorUnsignedMass` | **`CofactorParity.sum_oddBase_two_mul_le_sum_parityClass`** — the parity balance generalised from the harmonic weight to an arbitrary weight antitone above `1`, which is what lets the same pairing serve `(7)`; `bandModulus`, `primeFactors_bandModulus_subset`, `sum_inv_primeFactors_bandModulus_le`, **`coprime_bandModulus_iff`**, **`oddBase_eq_coprime_squarefree`** (the pairing's source set *is* the squarefree set coprime to `2∏_{p∈B}p`), and the two capstones |

The mechanism is one inclusion–exclusion, used twice: an integer not coprime to `Q` is a multiple of
a prime factor of `Q`, and the multiples of `p` carry at most `1/p` of the mass; a non-squarefree
integer coprime to an even `Q` is a multiple of the square of an odd prime, and the odd reciprocal
squares sum to at most `1/4`.  With `1/2 + 1/8 + 1/4 < 1` both constants survive.  No sieve, no
prime number theorem, no Mertens estimate for the *sifted* set is used — only the hypothesis that
the band's own Mertens mass is small, which is the card's own `∏(1+p^{-1})^{-1} ≍ 1`.

`#print axioms` on all ten named theorems: `[propext, Classical.choice, Quot.sound]`.  All three
modules are wired into the `GaloisForLFunctions.RHTower` umbrella.

### What remains on this card

Only `(6)`, the quantitative all-interval `E₃` supply — the shared Matomäki--Teräväinen input, whose
large-prime mean square `(FS7)` is now also a corpus theorem (see the entry above).

## Exponent retune `1.55 → 1.557` (2026-08-18)

The all-interval `E₃` input is being formalised through Huxley's large-values theorem rather than
Jutila's; see `../1-in-progress/matomaki-teravainen-e3-lean-programme.md`.  The resulting exponent
is `1 + 44/79 = 1.55696…` instead of `1.55`, and the §6.1 (Heath-Brown identity + Bourgain) route at
`1.615` is abandoned.  Nothing on this card depends on the value: the exponent enters only through a
polylogarithmic factor in the displacement.

## Lean progress (2026-08-19): the weight-general parity balance and the band's Euler factor

`formal/GaloisForLFunctions/RHTower/RouteECofactorParityWeights.lean` closes the two pieces of
`(7)` and `(9)` that were listed as "not formalized" and are **not** the Matomäki–Teräväinen input.

- `half_sum_oddBase_le_sum_parityClass_weight` — the pairing `s ↔ 2s` costs a factor two in *any*
  weight `w ≥ 0` with `(1/2)·w(s) ≤ w(2s)`.  The previously formalized statement was the special
  case `w(t) = 1/t` of `(9)`; this is the general form.
- `half_sum_oddBase_le_sum_parityClass_sqrt` — the instance `w(t) = 1/√t` the card's `(7)` uses.
  Doubling costs only `√2` there, so the factor two is not even tight.
- `prod_one_add_inv_le_exp`, `exp_neg_le_prod_inv` — `∏_{p∈S}(1+1/p) ≤ exp(∑_{p∈S}1/p)`, hence a
  lower bound on the reciprocal Euler product of any finite prime set.
- `band_euler_factor_ge` — **the card's quoted Mertens estimate, explicitly**:

  ```
       (log P / log Q) · exp(−(mertensSecondLowerConst + mertensSecondUpperConst))
         ≤  ∏_{P < p ≤ Q} (1 + 1/p)^{-1}      for  2 ≤ P ≤ Q.
  ```

  At the card's band `P = (log U)^{a₀}`, `Q = 2(log U)^{a₁}` the ratio `log P/log Q → a₀/a₁`, so the
  excluded band multiplies the unsigned squarefree main term by a factor bounded below by a
  positive constant depending only on `a₀, a₁` — which is exactly the "`≍_{a₀,a₁} 1`" the card
  quotes.  Unconditional; `#print axioms` gives `propext, Classical.choice, Quot.sound`.

What is still not formalized in this card is only the quantitative all-interval supply `(6)`
(the published Matomäki–Teräväinen minorant) and the unsigned squarefree harmonic *main terms*
`∑_{t ≤ T} μ²(t) t^{-1/2} ≍ √T` and `∑_{t ≤ T} μ²(t)/t ≍ log T` restricted to band-avoiding `t`.

### The unsigned squarefree harmonic main term of `(7)`

`formal/GaloisForLFunctions/RHTower/RouteECofactorSquarefreeHarmonic.lean`, unconditional:

- `sum_sqrtInv_le` — `∑_{n=1}^{T} n^{-1/2} ≤ 2√T`, by the telescoping
  `n^{-1/2} ≤ 2(√n − √(n−1))`.
- `sum_sqrtInv_squarefree_le` — hence `∑_{n ≤ T} μ²(n) n^{-1/2} ≤ 2√T`.
- `sum_sqrtInv_squarefree_ge` — **the matching lower bound**, for any `R` with `T ≤ R²`:

  ```
        ϱ·√T − (R + T/R)/√T  ≤  ∑_{n ≤ T} μ²(n) n^{-1/2} ,      ϱ = squarefreeDensity.
  ```

  The proof is one comparison: every weight `n^{-1/2}` with `n ≤ T` is at least `T^{-1/2}`, so the
  sum is at least `Q(T)/√T`, and `Q(T) ≥ T·ϱ − (R + T/R)` is the corpus's own squarefree window
  count `Sieve/SquarefreeWindowCount.abs_window_squarefree_sub_le`.  At `R ≍ √T` the error is `O(1)`
  and the two bounds pin the sum to `≍ √T` — the card's `(7)` main term.

`#print axioms` on all three: `propext, Classical.choice, Quot.sound`.

Still open in this card: the all-interval supply `(6)` (Matomäki–Teräväinen), the corresponding
`∑_{n ≤ T} μ²(n)/n ≍ log T` main term of `(9)` (a dyadic-block sum of the same window count), and
the restriction of both main terms to *odd band-avoiding* `n`, for which
`RouteECofactorParityWeights.band_euler_factor_ge` supplies the Euler factor but the
coprime-squarefree count itself is not yet formalized.

### The unsigned squarefree harmonic main term of `(9)`

Same file, unconditional:

- `sum_inv_squarefree_block_ge` — one dyadic block: for `2^j + 2^j ≤ R²`,

  ```
        (2^j·ϱ − (R + 2^j/R)) / 2^{j+1}  ≤  ∑_{2^j < n ≤ 2^{j+1}} μ²(n)/n .
  ```

- `sum_inv_squarefree_block_ge_const` — at `R = 2^{⌊j/2⌋+1}` and `j ≥ 8` the error is at most
  `3·2^{⌊j/2⌋} ≤ (ϱ/2)·2^j`, so **every dyadic block above `2^8` carries `≥ ϱ/4`**.
- `sum_inv_squarefree_ge` — summing the blocks:

  ```
        (ϱ/4)·(J − 8)  ≤  ∑_{n ≤ 2^J} μ²(n)/n .
  ```

- `sum_inv_squarefree_le` — `∑_{n ≤ T} μ²(n)/n ≤ 1 + log T`, from the corpus's harmonic bound
  `Sieve/HarmonicLogBound.sum_Icc_one_div_le_one_add_log`.

The two together pin `∑_{n ≤ T} μ²(n)/n` to `≍ log T` — the card's `(9)` main term.  With the
`(7)` main term above and `RouteECofactorParityWeights`, **every ingredient of `(7)` and `(9)` is
now formalized except the restriction of the main terms to odd band-avoiding `n`**, i.e. the
coprime-squarefree count; the Euler factor that governs that restriction is `band_euler_factor_ge`.

### `(7)` is closed

`formal/GaloisForLFunctions/RHTower/RouteECofactorBandCount.lean` assembles the pieces into the
card's `(7)` itself, unconditionally:

- `excludedPrimes Band Y = insert 2 ((Icc 1 Y).filter (fun p => p.Prime ∧ Band p))` — the primes a
  cofactor must avoid: the prime `2` of the pairing together with the whole band.
- `card_oddBase_ge` — the odd band-avoiding squarefree cofactors below `T/2` number at least

  ```
        (T/2)·ϱ − (R + (T/2)/R) − ∑_{p ∈ excludedPrimes} (T/2)/p ,     any  T/2 ≤ R² .
  ```

  (The union bound `Sieve/RouteECofactorSquarefreeHarmonic.card_squarefree_avoid_ge_of_subset`.)
- `sum_sqrtInv_oddBase_ge` — dividing by `√(T/2)` gives the source sum of `(7)`.
- `sum_sqrtInv_parityClass_ge` — with the pairing, **each parity class**:

  ```
        (1/2)·[ (T/2)·ϱ − (R + (T/2)/R) − ∑_{p ∈ excludedPrimes} (T/2)/p ] / √(T/2)
          ≤  ∑_{t ≤ T, μ(t)=σ, band-avoiding} t^{-1/2} .
  ```

- `sum_sqrtInv_parityClass_le` — and `≤ 2√T` in the other direction.

At `R ≍ √T` the second error term is `O(1)`, and the third is `(T/2)·(1/2 + ∑_{band} 1/p)`, whose
band part is `log(a₁/a₀) + O(1/log P)` by `band_euler_factor_ge`'s Mertens input — at the card's
`a₀ ∈ [1.1−10⁻⁴, 1.1]`, `a₁ = 1.1` that is below `10⁻³`, so the bracket is at least
`(T/2)(ϱ − 1/2 − 10⁻³) > (T/2)/10` and the whole left side is `≥ √T/30`.  **Both sides of `(7)`
are therefore `≍ √T`, formalized.**

The only remaining unformalized input of this card is the quantitative all-interval supply `(6)`,
the published Matomäki–Teräväinen minorant.

## Lean progress update (2026-08-20) — `(7)` and `(9)` are now unconditional

The "Lean progress" section above is out of date on two counts.

**1. The unsigned squarefree estimates `(7)` and `(9)` were already formalized.**
`Sieve/CoprimeSquarefreeHarmonic` proves both lower bounds for the squarefree integers coprime to
an even modulus `Q`,

```text
   sum_inv_coprime_squarefree_ge      : (1/8)·log M − 7/8 ≤ ∑_{n ≤ M, (n,Q)=1, μ²(n)=1} 1/n
   sum_inv_sqrt_coprime_squarefree_ge : (1/4)·√M   − 2   ≤ ∑_{n ≤ M, (n,Q)=1, μ²(n)=1} 1/√n
```

whenever `∑_{p ∣ Q} 1/p ≤ 5/8`, and `RouteECofactorUnsignedMass` transports them across the
`s ↔ 2s` pairing (generalised there to an arbitrary antitone weight) to the parity classes:

```text
   sum_inv_sqrt_parityClass_ge : (1/8)·√(T/2) − 1        ≤ ∑_{t ∈ parityClass B σ T} 1/√t
   sum_inv_parityClass_ge      : (1/16)·log(T/2) − 7/16  ≤ ∑_{t ∈ parityClass B σ T} 1/t
```

for any band `B` of odd primes with `∑_{p ∈ B} 1/p ≤ 1/8`.

**2. The band hypothesis is now discharged for the card's own band.**  Two new modules:

- `Sieve/PrimeRangeMertensMass.sum_inv_primesRange_le` — the **sharp** Mertens mass of a prime
  range.  The corpus's Mertens second theorem carries different additive constants at the two ends,
  so its difference is useless for a narrow band; Mertens' *first* theorem gives the sharp bound
  directly, since `1/p ≤ (log p/p)/log z₀` for `p > z₀`:
  ```text
     ∑_{z₀ < p ≤ z} 1/p ≤ (𝔄(z) − 𝔄(z₀))/log z₀ ≤ (log z − log z₀ + 2c)/log z₀ ,
  ```
  with the single constant `c = mertensFirstConst` of `|𝔄(N) − log N| ≤ c`.
- `RouteECofactorBandMass` — the specialisation.  `eventually_sum_inv_primesRange_polylog_le` shows
  that for `V^{a₀} ≤ z₀ ≤ z ≤ 2V^{a₁}` the band mass is at most
  `(log 2 + (a₁ − a₀)log V + 2c)/(a₀ log V) → (a₁ − a₀)/a₀`, hence below any target `c > (a₁−a₀)/a₀`
  once `V` is large.  At the card's exponents `a₀ = 1.1 − 10⁻⁴`, `a₁ = 1.1` this ratio is
  `10⁻⁴/1.0999 ≈ 9.1·10⁻⁵ < 1/8`.

  `eventually_sum_inv_sqrt_parityClass_band_ge`, `eventually_sum_inv_parityClass_band_ge` and
  `eventually_routeE_band_parity_mass` are `(7)` and `(9)` with that hypothesis removed:

```text
   ∀ᶠ V in atTop, ∀ z₀ z, 2 ≤ z₀ → z₀ ≤ z → V^{1.1−10⁻⁴} ≤ z₀ → z ≤ 2V^{1.1} →
     ∀ σ ∈ {1,−1}, ∀ T,
       (1/8)·√(T/2) − 1        ≤ ∑_{t ∈ parityClass (primesRange z₀ z) σ T} 1/√t
     ∧ (1 ≤ T/2 → (1/16)·log(T/2) − 7/16 ≤ ∑_{t ∈ parityClass (primesRange z₀ z) σ T} 1/t) .
```

`#print axioms` on all of these: `propext`, `Classical.choice`, `Quot.sound` only.

**Remaining gap, now the only one:** the quantitative all-interval supply `(6)`, i.e.
Matomäki–Teräväinen Theorem 1.2 (`docs/drafts/pipeline/1-in-progress/matomaki-teravainen-e3-lean-programme.md`).
Both this card and `route-e-forbidden-support-e3-stability` are gated on exactly that one theorem;
nothing else in either card is unformalized.
