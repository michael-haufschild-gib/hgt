# Route E cofactor-amplified \(E_3\) token supply

- **ID:** `ROUTE-E-COFACTOR-AMPLIFIED-E3-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-CAPACITY SURVIVOR
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** the elementary layer is formalized — exact parity reversal, the
  \(s\leftrightarrow2s\) cofactor pairing and displacement scaling in
  `MobiusCofactorAmplifiedToken.lean`, the parity-balance inequality and dyadic slice count `(6a)`
  in `RouteECofactorParityBalance.lean`, the amplified displacement `(5)` in
  `RouteEForbiddenSupportStability.lean`, and the unsigned band-avoiding squarefree estimates
  `(7)` and `(9)` with the card's band hypothesis discharged in `RouteECofactorUnsignedMass.lean`
  and `RouteECofactorBandMass.lean`.  Analytic supply `(6)` still depends on the published
  Matomäki--Teräväinen all-interval theorem and is not yet formalized.  See "Lean progress".

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

Not formalized: quantitative all-interval supply `(6)`, which is the published
Matomäki--Teräväinen minorant.  The unsigned squarefree harmonic estimates `(7)` and `(9)` are now
closed by `RouteECofactorUnsignedMass.lean` and `RouteECofactorBandMass.lean`.

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

## Lean progress update (2026-08-29) — elementary Lemma 3.5 regimes closed

`Sieve/MatomakiTeravainenWattDIOverHeight.lean` closes the branch `T ≤ N`.
`Sieve/MatomakiTeravainenWattProductMeanSquare.lean` now closes the disjoint full-product
long-height branch `2AN'² ≤ T` with the exact source-energy estimate

```text
∫_{T/2}^{T}|N(1+it)|⁴|A(1+it)|²dt
  ≤ (5πe+5π/2)(T/A²)∑_{A<n≤2A}|aₙ|².
```

The proof factors the exact Watt product into a finite Dirichlet polynomial and applies the
lossless multiplicative Young inequality; no Watt/DI, spectral, or large-value hypothesis is
retained.  Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

Remaining shared analytic gap is now precisely the intermediate regime
`N < T < 2AN'²` of Matomäki--Teräväinen Lemma 3.5, followed by its amplification and
Theorem 1.2 exponent assembly.  Card remains Stage 2.

## Lean progress update (2026-08-30) — reciprocal divisor-energy recovered

`Sieve/MatomakiTeravainenWattDivisorEnergy.lean` now proves unconditionally

```text
∫_{T/2}^{T}|N(1+it)|⁴|A(1+it)|²dt
  ≪ε (2AN'²)^(ε/2)(N'²)^(ε/2)(T+2AN'²)A⁻²N⁻²
      ∑_{A<n≤2A}|aₙ|².
```

Two divisor-fibre convolution estimates preserve the `N⁻²` reciprocal energy discarded by the
earlier `ℓ¹` argument.  Direct check, targeted module build, and axiom audit pass; only `propext`,
`Classical.choice`, and `Quot.sound` occur.  This closes an additional elementary portion of
`N < T < 2AN'²`; residual Watt/DI configurations and Theorem 1.2 assembly still gate promotion.

## Lean progress update (2026-08-30) — literal Watt/DI comparison regions

`Sieve/MatomakiTeravainenWattDivisorRange.lean` embeds the reciprocal divisor-energy bound into
both literal Lemma 3.5 envelopes: the Watt bound under `2AN'² ≤ A²√T`, and the DI bound under
`2AN'² ≤ A^(5/4)T^(3/4)`. Its strengthened capstones choose divisor exponent `ε/5` and discharge
the small divisor power from `T ≥ 2`, `A ≤ T`, `N ≤ T`, and `N' ≤ 2N`. Direct check, targeted
build, and six-declaration axiom audit pass; only `[propext, Classical.choice, Quot.sound]` occur,
and the module is umbrella-wired.

Card remains Stage 2. `A ≤ T`, `N ≤ T`, and applicable product-length inequalities must be proved
from actual Proposition-2.2 parameters, followed by complementary-range analysis, amplification,
and final all-interval supply assembly; no such premise may remain in the card theorem.

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
positive collision directions.  Combined with `Sieve/HeathBrownSparseRayScaling.lean`, both
elementary inputs of Heath--Brown Lemma 6 are now axiom-clean: nonexceptional directions pack at
the `Q²/T` scale, while one exceptional ray rescales exactly.  Direct check, targeted leaf build,
and three-declaration axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; module
is umbrella-wired without an umbrella build.  Weighted exceptional-direction assembly, the
two-scale Theorem 4(iii) iteration, Proposition-2.2 routing, amplification, and final Theorem 1.2
assembly remain.  Card stays Stage 2.

## Lean progress update (2026-08-31) — weighted primitive-ray assembly

`Sieve/HeathBrownPrimitiveWindow.lean`, `Sieve/HeathBrownPrimitiveLogWindow.lean`, and
`Sieve/HeathBrownPrimitiveRayMass.lean` extend Farey packing to all positive primitive slopes,
place literal logarithmic product collision inside an interval of width at most `4 delta`, and
count every positive multiple on each surviving ray.  Resulting exact two-scale bound is

```text
rayMass N ≤ 15 delta N²
  + (floor(N/N₀)+1) rayMass N₀
  + 2 floor(N/N₀)+1.
```

Finite layer cake ensures packing endpoint loss contributes `N/N₀`, not `N`.  No exceptional
direction, reduced basis, packing, layer-cake, or inverse-square premise remains.  Direct checks
and targeted leaf builds pass; final leaf builds `9097/9097`.  All nineteen new theorem
declarations across three leaves audit to only `[propext, Classical.choice, Quot.sound]`; all
leaves are umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared gap: source-level reindexing and coefficient-weighted
summation of complete Heath--Brown sparse collision form, Theorem 4(iii)'s iteration, residual
Proposition-2.2 routing, amplification, and final Matomäki--Teräväinen Theorem 1.2 assembly.

## Lean progress update (2026-08-31) — literal source collision reindexing

`Sieve/HeathBrownPositiveCollisionRayReindex.lean` proves exact equality between the literal
difference-of-logs collision count on `[1,N]²` and the primitive ray mass, then derives the direct
two-scale collision-count inequality with constants `15`, `1`, and `2`.  Cofactor ordering is
discharged internally by coordinate swap; gcd decomposition and difference-of-logs/log-ratio
conversion are constructed in Lean.  Direct check and targeted leaf build (`9098/9098`) pass.
All nineteen theorem declarations audit to only `[propext, Classical.choice, Quot.sound]`; module
is umbrella-wired without an umbrella build.

Card remains Stage 2.  Unweighted full-square source reindexing is closed.  Remaining shared gate:
coefficient-weighted summation over actual dense supports and sparse cofactor pairs, Theorem
4(iii)'s iteration, Proposition-2.2 routing, amplification, and final all-interval theorem.

## Lean progress update (2026-08-31) — finite Heath--Brown two-scale mean value closed

`Sieve/HeathBrownSparseCollisionTwoScale.lean` sums the exact ray count over all ordered sparse
cofactor pairs, dominates the existing `[0,1]`-weighted strict collision mass on any bounded dense
support, and composes with the corpus's exact `M(it)Q(it)` collision reduction.  Its aggregate law
is

```text
J(A,N,T) ≤ 15 N²|A|²/T
  + (floor(N/N₀)+1)J(A,N₀,T)
  + (2 floor(N/N₀)+1)|A|².
```

No coefficient, exceptional-direction, lattice, gcd, cofactor-ordering, or analytic premise
remains.  Direct source check, final targeted build (`9101/9101`), and nine-theorem axiom audit
pass with only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an
umbrella build.

Card remains Stage 2.  Finite Heath--Brown Lemma 6/Theorem 4(iii) comparison core is closed.
Remaining shared gate is paper-specific iterative parameter substitution, Proposition-2.2
residual Watt/DI routing, amplification, and final Matomäki--Teräväinen all-interval theorem.

## Lean progress update (2026-08-31) — fully integral Heath--Brown recurrence

`Sieve/HeathBrownSparseMeanValueTwoScale.lean` embeds every closed `1/T` collision in the full
positive interval `[1,N₀]` into the strict unit-weight collision family at height `T/2`.  Existing
reverse finite-frequency mean value then proves

```text
J(A,N₀,T) ≤ (5/(2T)) I(T/2; A,[1,N₀]),
```

and substitution yields the complete integral two-scale recurrence with the existing explicit
constants `15`, `5/2`, and endpoint term `2 floor(N/N₀)+1`.  Natural/positive support conversion,
unit-weight cardinality, closed-to-strict passage, and smaller-scale analytic closure are all
discharged.  Direct source check, targeted leaf build (`9102/9102`), and seven-theorem axiom audit
pass with only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an
umbrella build.

Card remains Stage 2.  Remaining shared gate is paper-specific recurrence iteration and parameter
substitution, residual Watt/DI routing in Proposition 2.2, amplification, and final
Matomäki--Teräväinen all-interval theorem.

## Lean progress update (2026-08-31) — Heath--Brown Cauchy/divisor square lift

`Sieve/HeathBrownSparseMeanValueSquareLift.lean` constructs the divisor-normalised dense square
factor and proves the exact squared Cauchy lift from length `N` to length `N²`.  It also proves the
sparse-factor ordinary mean square with independent support/integration heights and domination of
arbitrary `[0,1]` dense coefficients by unit coefficients.  Divisor fibres, coefficient bounds,
square reconstruction, continuity, integrability, and Cauchy--Schwarz are discharged internally;
no corresponding premise remains.  Direct check, targeted leaf build (`9107/9107`), and
thirty-declaration axiom audit pass with only `[propext, Classical.choice, Quot.sound]`; module is
umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared gate is exact Theorem 4(iii) recurrence iteration and
integer parameter algebra, Proposition-2.2 residual routing, amplification, and final all-interval
supply theorem.

## Lean progress update (2026-08-31) — closed Heath--Brown one-step self-bound

`Sieve/HeathBrownSparseMeanValueSelfBound.lean` constructs zero extension from `[1,K²]` to
`[1,N]`, proves height-window monotonicity and envelope positivity, and combines the exact
two-scale recurrence with the divisor square lift.  The capstone closes `I≤a+bJ`, `J²≤kI` as
`I≤2a+b²k` with the paper's explicit finite constants whenever `K²≤N`; none of these steps remains
as a premise.  Direct check, targeted leaf build (`9108/9108`), and nine-declaration axiom audit
pass with only `[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an
umbrella build.

Card remains Stage 2.  Remaining shared gate is integer scale selection, second-branch recurrence
and exponent algebra for exact Theorem 4(iii), then Proposition-2.2 routing, amplification, and the
all-interval supply theorem.

## Lean progress update (2026-08-31) — exact square-root branch selected

`Sieve/HeathBrownSparseMeanValueSqrtScale.lean` instantiates the closed self-bound at
`K=Nat.sqrt N`, discharging `K²≤N`, positivity, and the rounding loss `N/K≤K+2`.  The resulting
three-term estimate retains all explicit constants and no integer-scale premise.  Direct check,
targeted leaf build (`9109/9109`), and three-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

Card remains Stage 2.  Divisor/rpow absorption, second-branch recurrence, and exact Theorem 4(iii)
regime union remain before Proposition-2.2 routing, amplification, and all-interval supply.

## Lean progress update (2026-08-31) — first branch fully de-rounded

`Sieve/HeathBrownSparseMeanValueFirstBranch.lean` replaces `Nat.sqrt N` by `√N` and the exact
divisor scale by `divisorBoundConst η·N^η`, yielding a fully explicit three-term first-branch
bound with source support `m≤T`.  No floor, divisor, rpow, or positivity premise remains.  Direct
check, targeted leaf build (`9110/9110`), and three-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

Card remains Stage 2.  First-branch regime absorption and two-step parameter algebra remain before
exact Theorem 4(iii), Proposition-2.2 routing, amplification, and all-interval supply.

## Lean progress update (2026-08-31) — arbitrary-scale Heath--Brown recurrence

`Sieve/HeathBrownSparseMeanValueArbitraryScale.lean` proves monotonicity of the closed collision
aggregate and uses it to extend the exact two-scale recurrence from `1≤N₀≤N` to every positive
`N₀`, as required by Heath--Brown's Lemma 6.  `HeathBrownSparseMeanValueIteration.lean` now uses
that unrestricted theorem, so no hidden `N₀≤N` side condition remains.  Direct checks, targeted
leaf builds (`9103/9103`, `9110/9110`), and the six-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; module is umbrella-wired without an umbrella build.

Card remains Stage 2.  Exact second-scale selection and exponent absorption remain before the
Theorem 4(iii) union, Proposition-2.2 routing, amplification, and all-interval supply.

## Lean progress update (2026-08-31) — source-faithful real-ratio second scale

`Sieve/HeathBrownPrimitiveRayMassRealScale.lean` proves the exact `2N/N₀` recurrence for every
positive `N₀`; the `N<N₀` case is closed ray by ray rather than weakened to a floor-plus-one
coefficient.  `HeathBrownSparseMeanValueRealScale.lean` and
`HeathBrownSparseMeanValueRealIteration.lean` lift this to the coefficient-faithful two-step
integral bound.  `HeathBrownSecondScaleParameters.lean` constructs and proves all rounding and
size properties of `⌈max(T^(1/3),(RT)^(1/4))⌉₊`, and
`HeathBrownSparseMeanValueSecondScale.lean` selects it without auxiliary hypotheses.

Direct checks, targeted leaf builds (`9098/9098`, `9104/9104`, `9111/9111`, `9111/9111`,
`9115/9115`), and the focused eighteen-declaration axiom audit pass with only
`[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired without an umbrella build.

Card remains Stage 2.  Explicit exponent absorption and the exact Theorem 4(iii) regime union
remain before Proposition-2.2 routing, amplification, and all-interval supply.

## Lean progress update (2026-08-31) — exact Heath--Brown Theorem 4(iii)

`Sieve/HeathBrownSecondScaleAlgebra.lean`,
`HeathBrownSparseMeanValueTheoremFourAlgebra.lean`, and
`HeathBrownSparseMeanValueTheoremFour.lean` now prove the coefficient-faithful published bound

```text
I ≤ (95π/2) N²R² + Cη (NT)^η (NRT + N R^(7/4) T^(3/4))
```

with explicit `Cη`, arbitrary sparse circle phases, and arbitrary dense coefficients in `[0,1]`.
No scale, rounding, divisor, crossover, or branch premise remains.  Direct checks, targeted leaf
builds (`9116/9116`, `9117/9117`, `9118/9118`), and all-ten-declaration axiom audits pass with only
`[propext, Classical.choice, Quot.sound]`; capstone is umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared analytic work is Proposition-2.2 scale routing,
amplification, and final all-interval Theorem 1.2 assembly.

## Lean progress update (2026-08-31) — literal Lemma 3.4 and published refinement

`Sieve/HeathBrownSparseMeanValueBounded.lean`,
`HeathBrownSparseMeanValueBoundedRefined.lean`, and
`HeathBrownSparseMeanValueLemma34.lean` now prove Matomäki--Teräväinen Lemma 3.4 in its literal
one-line form.  Arbitrary complex sparse coefficients of modulus at most one, arbitrary real dense
coefficients, reciprocal weights, `M ≤ m ≤ T`, `N < n ≤ 2N`, and the internally constructed
maximum `max_n |a_n|` are retained.  The second capstone also deletes the mixed term under exactly
the published alternative `N ≥ T^(2/3)` or `|M| ≤ T^(1/3)`; the first alternative uses the
independent Heath--Brown square-root branch rather than an invalid absorption from the full bound.

Empty supports, zero coefficient maximum, sign splitting, normalization, continuity, and
`1 ≤ T < 2` are discharged.  Direct checks, targeted leaf builds (`9124/9124`, `9125/9125`), and
the focused seventeen-declaration audit pass with only `[propext, Classical.choice, Quot.sound]`;
the capstone is umbrella-wired without an umbrella build.

Card remains Stage 2.  Heath--Brown/Matomäki--Teräväinen Lemma 3.4 is closed.  Remaining shared
work is Lemma 3.5's genuine Type I and Type I/II analytic cancellation, subsequent
routing/amplification, and final Theorem 1.2 assembly; Proposition 2.2 bookkeeping and Type II are
already closed.

## Lean progress update (2026-09-02) — literal Heath--Brown replacement Watt moment

`Sieve/MatomakiTeravainenPrimeAmplifierSparseMass.lean` and
`MatomakiTeravainenPrimeAmplifierHeathBrownSupport.lean` now package each literal powered-prime
amplifier block as a factorial-normalized Heath--Brown sparse factor, with exact factor identity,
unit coefficient bound, stars-and-bars support, and Brun--Titchmarsh support envelope.

`Sieve/MatomakiTeravainenWattUnitSquareHeathBrown.lean` identifies the squared reciprocal unit
block with raw ordered factor-pair coefficients, divisor-bounds those coefficients, and proves its
exact split across `(N^2,2N^2]` and `(2N^2,4N^2]`; zero coefficients discharge both outside-range
tails.  `Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownMoment.lean` applies literal Lemma 3.4 to
both pieces and proves the positive-height interval estimate for the actual powered-prime Watt
moment, with only the explicit `(ell!)^2`, sparse-card, and divisor-scale factors remaining on its
right side.

Direct checks and targeted builds (`11172/11172`, `11176/11176`) pass.  Focused axiom audit of 41
new declarations reports only `[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired
without an umbrella build.

Card remains Stage 2.  Remaining shared gate is now scalar: absorb the explicit factorial-weighted
sparse-card/divisor expression into the literal Lemma 3.5 budgets in every Proposition-2.2 scale,
then complete amplification and Theorem 1.2.  No spectral or automorphic premise has been added.

## Lean progress update (2026-09-02) — energy-faithful Type-I receiver

Five further unconditional leaves close the support/energy mismatch in the Heath--Brown
replacement:

- `Sieve/MatomakiTeravainenPrimeAmplifierIntegralEnergy.lean` identifies every raised coefficient
  with its ordered prime-product fibre cardinality and proves `card support <= block energy`;
- `Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownEnergyMoment.lean` factors the exact coefficient
  energy from the complete mixed moment;
- `Sieve/MatomakiTeravainenPrimeAmplifierHeathBrownBTMoment.lean` and
  `MatomakiTeravainenPrimeAmplifierHeathBrownSqrtBTMoment.lean` remove exact support statistics and
  select `sqrt P`, leaving the explicit support base `292 P/log P + 1 + ell`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownMoment.lean` feeds the result through the
  fixed amplifier-block cover and restricted Cauchy receiver, reducing all block-height clauses to
  `((2P)^ell:R) <= T`.

Targeted builds pass, and the focused 27-declaration audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  All leaves are umbrella-wired without an umbrella build.

Card remains Stage 2.  Remaining shared work is exact Section-5.1 schedule/exponent absorption of
the now source-only coefficient, followed by Proposition-2.2 routing, amplification, and the
all-interval theorem.  No hypothesis-bearing substitute has been promoted.

## Lean progress update (2026-09-02) — source-scale Type-I absorption and height closure

Seven new unconditional leaves close the Section-5.1 source schedule, canonical
Brun--Titchmarsh/factorial losses, and unit-length/height branch:

- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSourceScale.lean` derives
  `P <= T^(2/5)` from the paper's source range;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownCanonicalMoment.lean` connects the Type-I
  receiver to the square-root Brun--Titchmarsh coefficient and absorbs `ell!`, `(ell!)^2`, and
  `292P/log P + 1 + ell` under the exact reserve `294 ell <= P`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownDegreeDeficit.lean` constructs that reserve
  uniformly from the actual exponent interval;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownAbsorbedSourceMoment.lean` discharges prime
  scale, degree, height, factorial, support, and Brun--Titchmarsh side conditions internally;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerMoment.lean` and
  `MatomakiTeravainenTypeIPrimeAmplifierHeathBrownPowerSourceMoment.lean` absorb all remaining
  divisor/small-power losses into a fixed constant times `T^(epsilon/2)`;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeightDichotomy.lean` chooses internally between the
  new `N <= T` Heath--Brown receiver and the existing `T <= N` affine receiver.

Direct checks and the targeted height-dichotomy leaf build (`11192/11192`) pass.  A focused audit
of all 27 new theorem declarations reports only `[propext, Classical.choice, Quot.sound]`; modules
are umbrella-wired without an umbrella build.

Card remains Stage 2.  No caller-supplied `N/T` comparison or hidden schedule/factorial/support
hypothesis remains in this Type-I lane.  Still open: literal final scalar comparison with the
amplifier threshold and long-factor energy, Proposition-2.2 Type-I routing, amplification, and
all-interval Theorem 1.2 assembly.  No conditional endpoint has been promoted.

## Lean progress update (2026-09-02) — exact threshold-layer Type-I replacement

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

## Lean progress update (2026-09-02) — exact source density and fixed power decay

Nine further unconditional bricks carry the threshold-layer Type-I replacement through its
source scalar:

- height, height-receiver, long-energy, divisor-energy, and long-power modules discharge the
  square-product scale, divisor scale, literal long fourth moment, fixed divisor majorant, and
  residual long polylogarithm;
- the strengthened layer scalar keeps the exact diagonal mass
  `card(mtTypeIPrimeCoeffSupport P)^ell / P^ell`;
- `Sieve/MatomakiTeravainenPrimeAmplifierLayerPrimeDensity.lean` proves that mass is at most
  `2^(-ell)` by the literal Brun--Titchmarsh support count and then at most
  `exp(-(log(log X))^6)` on the complete source schedule;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourceDensity.lean` inserts the saving
  into the full long-power receiver;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierHeathBrownLayerSourcePowerDecay.lean` replaces the
  two residual variable amplifier powers by the uniform paper-range savings
  `T^(-9/2000)` and `T^(-9/8000)`.

Direct checks and targeted leaf builds pass, ending at `11274/11274`. Focused axiom audits report
only `[propext, Classical.choice, Quot.sound]`; modules are umbrella-wired without an umbrella
build.

Card remains Stage 2. Remaining shared Type-I gate is exact product-scale routing from the
Proposition-2.2 piece data into this fixed-power receiver and final scalar absorption. Type-I/II,
amplification, and the all-interval supply theorem remain downstream; no conditional or
hypothesis-bearing endpoint has been promoted.

## Lean progress update (2026-09-02) — one-unit coefficient-faithful Type-I lane

Four unconditional modules add the complementary one-unit receiver:

- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierOneUnitMoment.lean` applies the unconditional
  one-unit second-derivative moment to every powered-prime amplifier block while preserving its
  exact coefficient energy and introducing no factorial normalization;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceMoment.lean` constructs the paper's
  prime scale and raising degree, discharges every block-height condition, and inserts equation
  `(5.4)` on the complete source schedule;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceLongEnergy.lean` replaces the long
  fourth moment by literal dyadic coefficient energy;
- `Sieve/MatomakiTeravainenTypeIPrimeAmplifierOneUnitSourceLongPower.lean` applies the fixed
  divisor majorant and absorbs its polylogarithm into `T^(epsilon/100)`.

Direct checks pass. Targeted final leaf build passes (`11211/11211`). A focused audit of all eight
new theorem declarations reports only `[propext, Classical.choice, Quot.sound]`; final leaf is
umbrella-wired without an umbrella build.

This lane does not by itself close Section 5.1. Exact exponent comparison shows both available
elementary replacements stop short on the middle Type-I product scales: the threshold-layer
diagonal is only subpower after multiplication by long-factor fourth-moment energy, while the
one-unit bound also lacks the published Deshouillers--Iwaniec modulus-average saving. The remaining
analytic gate is therefore the genuine Lemma 3.5(ii) cancellation (or an equally strong
source-specific theorem), followed by Proposition-2.2 routing, amplification, and the all-interval
supply theorem. Card remains Stage 2; no premise-bearing endpoint has been promoted.

## Lean progress update (2026-09-02) — signed modulus-average spectral carrier

Three unconditional modules replace the positive modulus-energy object by the signed carrier on
which genuine spectral cancellation can act:

- `Sieve/KloostermanModulusBilinear.lean` forms the complex sum of complete Kloosterman bilinear
  amplitudes across moduli before taking a norm, proves its literal threefold expansion, and gives
  exact fixed-modulus and direct-sum baselines;
- `Sieve/KloostermanHybridModulusBilinear.lean` specializes both residue vectors to physical-height
  additive Dirichlet polynomials and proves continuity plus pointwise baselines;
- `Sieve/KloostermanHybridModulusLinear.lean` fixes one residue vector and integrates the signed
  one-sided form, closing the exact non-spectral baseline by the existing additive hybrid large
  sieve.

Direct checks pass. Targeted builds pass (`8941/8941`, `9229/9229`, `9230/9230`). Focused audit of
all 12 new theorem declarations reports only `[propext, Classical.choice, Quot.sound]`; final leaf
is umbrella-wired without an umbrella build.

Card remains Stage 2. Relative phases across distinct moduli are now retained in Lean, but the
proved right side still takes the fixed-modulus triangle/Cauchy baseline. Remaining primitive is
the genuine Kuznetsov--Deshouillers--Iwaniec modulus-average improvement for this signed carrier;
then source Type-I routing, amplification, and all-interval Theorem 1.2 assembly remain. No
spectral estimate has been assumed or exposed as a hypothesis.

## Lean progress update (2026-09-02) — shared-coefficient adjoint structure

`Sieve/KloostermanHybridModulusAdjoint.lean` proves exact conjugation of additive hybrid
polynomials, symmetry and adjoint laws for fixed-modulus and signed modulus-average Kloosterman
forms, and the time-reflection adjoint for the shared-arithmetic-coefficient hybrid carrier. This
removes arbitrary modulus-dependent source coefficients from the intended spectral input and
retains the common arithmetic sequence on which cross-modulus cancellation must act.

Direct check and targeted build pass (`9231/9231`). Focused audit of all eight new theorem
declarations reports only `[propext, Classical.choice, Quot.sound]`; final leaf is umbrella-wired
without an umbrella build. Card remains Stage 2: adjoint/representation structure is closed and
the next exact orthogonality audit determines which specialization can carry a spectral estimate.
No quantitative estimate is a hypothesis of any endpoint.

## Lean progress update (2026-09-02) — two-sided hybrid collapse classification

`Sieve/KloostermanSharedHybridCollapse.lean` proves the exact pointwise unit-residue Fourier
formula, a reusable reflected-frequency pairing identity, and the full collapse law

```text
two additive-hybrid legs + complete Kloosterman kernel
  = (modulus)^2 * inverse-residue correlation.
```

Thus the two-sided shared additive-Fourier specialization is not the missing Kuznetsov carrier:
finite orthogonality removes its Kloosterman kernel before any modulus average. Generic signed
modulus bilinear form remains valid, and the one-sided hybrid form remains the relevant candidate
because its second residue vector is not another additive Fourier transform.

Direct check and targeted build pass (`9233/9233`). All five theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; final leaf is umbrella-wired without umbrella build.
Card remains Stage 2. Remaining analytic primitive is a genuine one-sided/shared-arithmetic
Kuznetsov--Deshouillers--Iwaniec modulus estimate, followed by source Type-I routing. No false
two-sided spectral premise survives.

## Lean progress update (2026-09-02) — genuine ordinary-index Kloosterman carrier

Two unconditional modules install the nondegenerate replacement:

- `Sieve/KloostermanPhysicalResidueModulusBilinear.lean` groups the same ordinary Dirichlet
  coefficients into physical residue fibres at every modulus, without additive Fourier transforms,
  and expands the result back to the literal signed sums
  `sum_q w_q sum_m a_m(t) sum_n b_n(t) S(m,n;q)`;
- `Sieve/KloostermanIntegerModulusKernel.lean` isolates
  `sum_q w_q S(m,n;q)` as a kernel on ordinary integer indices, proves symmetry, conjugation, and
  the exact totient triangle baseline, and identifies the physical-residue carrier with its finite
  ordinary-index bilinear form.

Direct checks and targeted builds pass (`9234/9234`, `9235/9235`). Focused audit of all nine new
theorem declarations reports only `[propext, Classical.choice, Quot.sound]`; final leaf is
umbrella-wired without umbrella build.

Card remains Stage 2. Representation question is now closed precisely: this integer-index signed
kernel retains the complete Kloosterman sums and shared arithmetic coefficients, while the earlier
two-additive-leg specialization provably does not. Remaining primitive is a quantitative spectral
operator estimate for this kernel strong enough to imply Lemma 3.5(ii), then source Type-I routing,
amplification, and Theorem 1.2. No estimate is assumed.

## Lean progress update (2026-09-02) — finite kernel operator receiver

`Sieve/KloostermanIntegerKernelOperator.lean` defines the signed integer-kernel transform and its
finite bilinear form. It proves the exact Cauchy receiver, pointwise and summed Hilbert--Schmidt
bounds, the fully scalar cardinality/totient baseline, and the identity with the physical-height
carrier on the literal interval supports.

Direct check and targeted build pass (`9236/9236`). All seven theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; final leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Algebraic and Hilbert-space routing to the correct signed kernel is closed.
Remaining analytic theorem must improve the explicit Hilbert--Schmidt/cardinality/totient baseline
at the paper's modulus ranges; no caller-supplied operator hypothesis has been introduced.

## Lean progress update (2026-09-02) — exact Gram/off-diagonal frontier

`Sieve/KloostermanIntegerKernelGram.lean` expands transform output energy into its Hermitian
source-side Gram kernel, proves the exact quadratic identity, splits diagonal from a literal
erased-index off-diagonal, and identifies the diagonal as manifestly nonnegative row square energy.

Direct check and targeted build pass (`9237/9237`). All five theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining spectral content is now isolated in one explicit finite object:
`kloostermanIntegerKernelGramOffDiagonal`. Diagonal, adjoint, Cauchy, and all representation
bookkeeping are unconditional and closed; no off-diagonal estimate is assumed.

## Lean progress update (2026-09-02) — cross-modulus correlation expansion

`Sieve/KloostermanCrossModulusCorrelation.lean` expands each signed-kernel Gram entry into the
literal double modulus sum of incomplete Kloosterman correlations, proves Hermitian symmetry, and
splits equal from distinct moduli by erasing the diagonal modulus.

Direct check and targeted build pass (`9238/9238`). All three theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining spectral theorem is reduced further to quantitative control of
explicit incomplete cross-modulus correlations, especially the distinct-modulus part, on the
paper's output interval. No correlation bound has been assumed.

## Lean progress update (2026-09-02) — complete equal-modulus correlation

`Sieve/KloostermanCompleteColumnCorrelation.lean` evaluates the full equal-modulus column
correlation exactly as `q * S(0,k-n;q)` by additive-character orthogonality. Its diagonal is
therefore exactly `q * phi(q)`.

Direct check and targeted build pass (`9239/9239`). Both theorem declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Equal-modulus complete-period arithmetic is closed. Remaining work is
incomplete-window completion, bounds for the resulting zero-frequency/Ramanujan terms, and genuine
distinct-modulus cancellation strong enough for Lemma 3.5(ii).

## Lean progress update (2026-09-02) — complete-column Ramanujan arithmetic

`Sieve/KloostermanCompleteColumnRamanujan.lean` identifies the full equal-modulus correlation with
the modulus times the corpus's Chen--Gupta--Li Ramanujan coefficient, substitutes its exact
gcd--Möbius divisor formula, and proves an unconditional divisor-sum norm majorant.

Direct check and targeted build pass (`12570/12570`). All three public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Full-period equal-modulus arithmetic, including its gcd dependence, is now
closed. Remaining analytic work is incomplete-window completion and genuine distinct-modulus
cancellation strong enough for Lemma 3.5(ii); no estimate is assumed.

## Lean progress update (2026-09-02) — same-modulus interval completion

`Sieve/KloostermanSameModulusIntervalCompletion.lean` groups the actual `[1,M]` equal-modulus
Gram correlation by residue class. It proves the exact decomposition into a uniform complete-period
Ramanujan main term plus residue-count discrepancy, proves every discrepancy coefficient has
absolute value at most one, and bounds the whole remainder by the sharp complete second-moment
scale `q * phi(q)` using finite Cauchy--Schwarz.

The module bridges this result directly to the stored correlation whose index `q` represents
modulus `q+1`. Direct check and targeted build pass (`12571/12571`). All nine public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2. Equal-modulus incomplete-window completion is closed unconditionally.
Remaining spectral core is the distinct-modulus correlation estimate at the source ranges, then
its Type-I routing; no analytic bound is assumed.

## Lean progress update (2026-09-02) — distinct-modulus complete correlation

`Sieve/KloostermanDistinctModulusCompleteCorrelation.lean` proves exact vanishing of the complete
product-period correlation for distinct positive moduli. It groups the literal `[1,M]` correlation
by product-period residues, removes the vanishing complete main, identifies the result with an
explicit boundary-discrepancy remainder, and bounds that remainder by
`q*r*(phi(q)+phi(r))/2` using finite Cauchy--Schwarz and exact complete second moments. Direct
instantiations cover the existing stored-modulus Gram correlation.

Direct check and targeted build pass (`12572/12572`). All thirteen public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2. Complete-period distinct-modulus arithmetic is now closed. Remaining genuine
core is cancellation for the incomplete discrepancy remainder at the source ranges, followed by
Lemma 3.5(ii) routing, amplification, and Theorem 1.2 assembly; no estimate is assumed.

## Lean progress update (2026-09-02) — least-common-multiple completion

`Sieve/KloostermanDistinctModulusLcmCompletion.lean` proves that the earlier product period is
exactly `gcd(q,r)` copies of the sharp common period. Hence unequal-modulus correlation vanishes
already over `lcm(q,r)`, and the arbitrary `[1,M]` correlation is an exact lcm-residue remainder.
Exact lcm-period second moments improve the boundary bound to
`lcm(q,r)*(phi(q)+phi(r))/2`, including the stored-modulus Gram carrier.

Direct check and targeted build pass (`12573/12573`). All nine public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining genuine core is cancellation within this sharp incomplete common
period at source ranges, then Lemma 3.5(ii) routing, amplification, and Theorem 1.2 assembly; no
estimate is assumed.

## Lean progress update (2026-09-02) — exact terminal common-period block

`Sieve/KloostermanDistinctModulusTerminalBlock.lean` replaces the lcm discrepancy vector by its
exact surviving support. For unequal positive moduli, the `[1,M]` correlation is literally the
shifted sum over `0 <= i < M mod lcm(q,r)`; every complete common-period block vanishes. It also
proves the exact-residual-length totient bound and stored-modulus Gram identities.

Direct check and targeted build pass (`12736/12736`). Its five public results and exposed
periodicity theorem audit with only `[propext, Classical.choice, Quot.sound]`; leaf is
umbrella-wired without umbrella build.

Card remains Stage 2. Remaining genuine core is collective cancellation of these literal terminal
blocks with source modulus weights, then Lemma 3.5(ii) routing, amplification, and Theorem 1.2;
no estimate is assumed.

## Lean progress update (2026-09-02) — weighted terminal-block Gram

`Sieve/KloostermanDistinctModulusTerminalGram.lean` restores the original signed modulus weights
and proves that the existing distinct-modulus Gram on `[1,M]` is exactly the resulting terminal
carrier. The full kernel Gram is the existing same-modulus term plus this weighted terminal term;
an unconditional pairwise budget retains each exact `M mod lcm(q+1,r+1)` length.

Direct check and targeted build pass (`12737/12737`). All four public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining primitive is collective cancellation of this exact carrier inside
the source-index quadratic form at paper ranges, then Lemma 3.5(ii), amplification, and Theorem
1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — source-weighted terminal quadratic receiver

`Sieve/KloostermanDistinctModulusTerminalQuadratic.lean` composes the modulus split with the
existing source-index Gram receiver. Full transform energy and erased source off-diagonal now split
exactly into equal-modulus and terminal distinct-modulus quadratic forms. The closed terminal bound
retains every source coefficient, modulus weight, and exact residual length.

Direct check and targeted build pass (`12738/12738`). All four public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining analytic estimate is collective cancellation of this literal
source-weighted terminal off-diagonal at paper ranges, plus equal-modulus Ramanujan routing, then
Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — three-way Ramanujan/terminal frontier

`Sieve/KloostermanSameModulusRamanujanQuadratic.lean` lifts equal-modulus interval completion
through modulus weights and source quadratic forms. Transform energy and erased source
off-diagonal split exactly into Ramanujan main, bounded equal-modulus completion remainder, and
terminal distinct-modulus carrier. The remainder bound retains all source coefficients and the
weighted `sum_q |w_q|^2 (q+1) phi(q+1)` scale.

Direct check and targeted build pass (`12739/12739`). All seven public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Remaining work is Ramanujan-main square-energy control and collective
terminal-carrier cancellation at paper ranges, then Lemma 3.5(ii), amplification, and Theorem 1.2;
no estimate is assumed.

## Lean progress update (2026-09-02) — Ramanujan main square energy

`Sieve/KloostermanSameModulusRamanujanEnergy.lean` proves the weighted Ramanujan main quadratic is
exactly `sum_q |w_q|^2 M/(q+1)` times complete Kloosterman column-transform square energy. It is
therefore real and nonnegative, unconditionally.

Direct check and targeted build pass (`12740/12740`). All six public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. Equal-modulus main/remainder classification is closed. Remaining genuine
primitive is collective control of the source-weighted terminal distinct-modulus carrier at paper
ranges, then Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — exact scalar analytic frontier

`Sieve/KloostermanAnalyticFrontier.lean` packages the full transform-output energy as nonnegative
Ramanujan main energy plus the two exact completion carriers, supplies closed full-source budgets
for both residual terms, proves their combined imaginary part vanishes, and derives an
unconditional scalar energy bound. No analytic hypothesis is introduced.

Direct check and targeted build pass (`12741/12741`). All six public theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2. This is the exact absolute-value baseline, not the paper-range saving.
Remaining genuine primitive is collective spectral cancellation beyond the terminal-carrier
budget, then source routing into Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is
assumed.

## Lean progress update (2026-09-02) — terminal geometric cancellation

`Sieve/KloostermanCrossPhaseGeometric.lean` proves unequal positive moduli have no trivial
cross-unit additive phase. `Sieve/KloostermanTerminalGeometricCancellation.lean` then expands the
exact terminal carrier into those nontrivial geometric orbits and proves the hybrid minimum of
the old exact-length bound and a new terminal-length-independent reciprocal-chord bound, including
the stored Gram correlation.

Direct checks and targeted builds pass (`12746/12746`, `12747/12747`). Eleven public declarations
across the two leaves audit with only `[propext, Classical.choice, Quot.sound]`; both leaves are
umbrella-wired without umbrella build.

Card remains Stage 2. Remaining genuine primitive is collective control of the reciprocal chord
denominators and their signed modulus/source aggregation at the paper ranges, then Lemma 3.5(ii),
amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — coprime cross-frequency CRT compression

`Sieve/KloostermanCoprimeCrossPhaseFrequency.lean` proves that coprime cross-unit pairs are
equivalent to units modulo the product period through CRT coordinates `(-r*x, q*y)`.  It proves the
product-level standard additive character is exactly the terminal cross-phase ratio and reindexes
the entire double reciprocal-chord budget as one product-unit sum, without loss or multiplicity.
The terminal block bound is transported to that single-period carrier.

Direct check and targeted leaf build pass (`12749/12749`).  All eight public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Next shared primitive is a harmonic bound for the product-period chord sum,
then gcd stratification and signed modulus/source aggregation at paper ranges, Lemma 3.5(ii),
amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — product-unit harmonic chord bound

`Sieve/KloostermanProductUnitChordSum.lean` proves collectively that reciprocal chords of all
product-modulus unit frequencies have total at most `N*(1+log N)`.  It uses two-sided Jordan
separation and injective canonical/complementary representative families, then combines this with
the lossless coprime CRT compression.  The exact terminal block and stored Gram correlation now
have unconditional length-independent bounds of product-period times one harmonic logarithm.

Direct check and targeted leaf build pass (`13483/13483`).  All eight public theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Coprime reciprocal-denominator aggregation is closed.  Remaining shared
primitive is noncoprime gcd stratification and signed modulus/source aggregation at paper ranges,
then Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — product-period slices without coprimality

`Sieve/KloostermanProductFrequencySliceBound.lean` represents every unequal-modulus cross phase,
without a coprimality premise, by `q*val(y)-r*val(x)` modulo `q*r`.  Each fixed-coordinate slice is
an injective family of nonzero frequencies.  A generalized nonzero-frequency chord theorem and
injective-family harmonic estimate give the double reciprocal-chord budget as the minimum of the
two slice bounds `phi(q)*q*r*(1+log(q*r))` and `phi(r)*q*r*(1+log(q*r))`, with direct terminal-block
and stored-correlation consequences.

Direct check and targeted leaf build pass (`13484/13484`).  All sixteen new theorem declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Noncoprime denominator aggregation is closed.  Remaining shared primitive
is signed modulus/source aggregation and cancellation beyond the absolute harmonic budget at paper
ranges, then Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — source/modulus product-harmonic aggregation

`Sieve/KloostermanProductHarmonicQuadratic.lean` aggregates the shared-gcd-safe pair budget through
the card's signed modulus weights and source coefficients.  Terminal and stored Gram entries obey
one explicit modulus-pair budget; full and erased source quadratics are bounded by that budget times
the square of source ℓ¹ mass.

Direct check and targeted leaf build pass (`13485/13485`).  All six theorem declarations audit
with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2.  Absolute signed source/modulus aggregation is closed.  Remaining shared
primitive is spectral cancellation beyond this product-harmonic ℓ¹ baseline at paper ranges, then
Lemma 3.5(ii), amplification, and Theorem 1.2; no estimate is assumed.

## Lean progress update (2026-09-02) — exact `η<1/6` scale separation

`CofactorAmplifiedScaleSeparation.lean` formalizes the scale comparison used in the construction
to put both large `E₃` prime factors above every cofactor prime.  With

```text
T(U) = U^(2η),
Plarge(U) = sqrt((U/T(U)) / (log U)^a),
```

it proves the exact identity

```text
Plarge(U)/T(U) = U^(1/2-3η)/(log U)^(a/2)
```

for `U>1`, then proves this ratio tends to infinity whenever `η<1/6`.  Consequently every fixed
positive proportion of the large-prime scale eventually exceeds `T`, which is the precise
asymptotic content behind the card's `p₂,p₃>T` support-separation claim.  No prime-distribution
input is used.

Direct source check and targeted leaf build pass (`2009/2009`) after narrowing the import surface.
All three public theorem declarations audit with only `[propext, Classical.choice, Quot.sound]`;
leaf is umbrella-wired without umbrella build.

Card remains Stage 2.  Cofactor/large-prime scale separation is closed; the remaining shared core
is still the all-interval `E₃` spectral estimate, Lemma 3.5(ii) routing, amplification, and Theorem
1.2.

## Lean progress update (2026-09-02) — exact terminal source-Fourier factorization

`Sieve/KloostermanTerminalSourceFourier.lean` now preserves source cancellation through the exact
terminal carrier instead of taking source absolute values.  It defines the finite additive source
transform at inverse unit frequencies and the terminal geometric orbit, proves that one
cross-phase source quadratic is exactly a product of two source transforms, and then performs the
dependent finite Fubini reordering through `Q.erase q`.  The resulting no-premise theorem writes
the full weighted distinct-modulus terminal Gram quadratic exactly as

```text
sum_{q in Q} sum_{r in Q\{q}} conjugate(w_q) w_r
  sum_{x in (Z/q+1 Z)^*} sum_{y in (Z/r+1 Z)^*}
    conjugate(F_q(x)) F_r(y) Orbit_M(q,r;x,y).
```

Direct source check and targeted leaf build pass (`12748/12748`).  All four new public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Exact source Fourier/orbit interface is closed.  Remaining shared primitive
is a collective signed spectral estimate for this literal carrier at paper ranges, followed by
Lemma 3.5(ii), amplification, and Theorem 1.2; no cancellation estimate is assumed.

## Lean progress update (2026-09-02) — source Parseval with residue collisions

`Sieve/KloostermanSourceFourierParseval.lean` reuses the corpus's exact finite additive large-sieve
Parseval theorem.  Arbitrary natural source indices are first compressed by their residue modulo
`q`, so collisions are retained rather than hidden behind an injectivity assumption.  The module
proves the exact full-frequency identity

```text
sum_{t mod q} |F_q(t)|² = q * sum_{z mod q} |sum_{n in B, n=z mod q} b_n|²
```

and bounds the inverse-unit-frequency energy occurring in the terminal source-Fourier
factorization by this exact residue energy.  Both statements are unconditional and contain no
source-support premise.

Direct source check and targeted leaf build pass (`12749/12749`).  All four new public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Source-side finite Parseval control is closed.  Remaining shared primitive
is cancellation of the terminal orbit kernel across modulus/unit frequencies at paper ranges,
then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Lean progress update (2026-09-02) — terminal-orbit Hilbert--Schmidt receiver

`Sieve/KloostermanTerminalSourceFourierEnergy.lean` applies finite Cauchy--Schwarz twice to the
exact source-Fourier/orbit factorization.  For each modulus pair, the squared terminal source
quadratic is bounded by the product of its two source Fourier energies and the entrywise squared
energy of the terminal-orbit kernel.  Composing with source Parseval replaces both source factors
by exact residue-collision energies, leaving only the literal orbit-kernel Hilbert--Schmidt term.

Direct source check and targeted leaf build pass (`12750/12750`).  Both new public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Fixed-pair source energy reduction is closed.  Remaining shared primitive
is a saving for terminal-orbit kernel energy or stronger signed operator cancellation at paper
ranges, then Lemma 3.5(ii), amplification, and Theorem 1.2.

## Lean progress update (2026-09-02) — no-premise terminal-orbit hybrid energy

`Sieve/KloostermanTerminalOrbitEnergy.lean` closes the unconditional absolute energy evaluation
exposed by the preceding Hilbert--Schmidt receiver.  Every terminal orbit is bounded
simultaneously by its exact residual length and its reciprocal phase chord; after squaring, Lean
sums the pointwise minimum over every erased modulus pair.  A second no-premise theorem composes
that budget with exact source residue Parseval and bounds the sum of all erased-modulus terminal
source-quadratic energies by

```text
sum_{q in Q} sum_{r in Q\{q}}
  SourceResidueEnergy(q) * SourceResidueEnergy(r) * HybridOrbitEnergy(q,r).
```

Direct source check and targeted leaf build pass (`12751/12751`).  Both public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Absolute source and orbit-energy bookkeeping is now closed with no premises.
Remaining shared primitive is a genuine collective spectral saving beyond this pointwise hybrid
budget at paper ranges, followed by Lemma 3.5(ii), amplification, and Theorem 1.2.

## Lean progress update (2026-09-02) — full weighted hybrid/interpolated Gram receiver

`Sieve/KloostermanTerminalOrbitEnergy.lean` now carries the fixed-pair hybrid estimate through the
entire signed terminal Gram quadratic.  A dependent-pair Cauchy--Schwarz argument flattens
`Q.erase q` with `Finset.sigma`, so no artificial `#Q` factor is introduced.  The resulting
no-premise theorem bounds the squared full Gram norm by exact ordered modulus-weight energy times
the source-residue/hybrid-orbit receiver.

The same module then interpolates the pointwise bounds by

```text
min(length², chord⁻²) ≤ length * chord⁻¹
```

and discharges the summed reciprocal-chord factor with the existing shared-gcd-safe
product-harmonic theorem.  Thus a second no-premise theorem gives a fully explicit receiver whose
pair kernel is exact residual length times `kloostermanProductHarmonicPairBudget`.

Direct source check and targeted leaf build pass (`13489/13489`).  All three additional public
theorem declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf remains
umbrella-wired without umbrella build.

Card remains Stage 2.  Sharp unconditional absolute-value interpolation is closed, but it is not
the collective signed spectral saving required at paper ranges.  Remaining shared core is that
saving, Lemma 3.5(ii), amplification, and Theorem 1.2.

## Lean progress update (2026-09-02) — literal source-interval residue multiplicity

`Sieve/KloostermanSourceResidueMultiplicity.lean` removes the arbitrary-source residue-collision
budget from the literal interval `B = Finset.Icc 1 N`.  For `N>0`, shifted Euclidean quotient gives
an injection from each residue fibre modulo `q+1` into
`Finset.range ((N-1)/(q+1)+1)`, so Lean proves the exact maximum occupancy

```text
#{n in [1,N] : n = z mod (q+1)} <= (N-1)/(q+1)+1.
```

Fibrewise Cauchy--Schwarz and exact finite reassembly then bound source residue energy by

```text
(q+1) * ((N-1)/(q+1)+1) * sum_{1 <= n <= N} |b_n|^2.
```

The module inserts this no-premise bound for both source legs into the full weighted terminal Gram
receiver, retaining ordered modulus-weight energy and the residual-length/product-harmonic orbit
budget.  No source injectivity, size premise, or analytic cancellation estimate is assumed.

Direct source check and targeted leaf build pass (`13490/13490`).  All three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Literal interval source-collision bookkeeping is closed.  Remaining shared
core is genuine signed spectral saving at paper ranges, Lemma 3.5(ii), amplification, and Theorem
1.2.

## Lean progress update (2026-09-02) — exact literal-band dyadic slice asymptotic

`CofactorAmplifiedDyadicSliceCount.lean` strengthens the earlier lower bound for `(6a)` to the
exact floor-and-ceiling asymptotic at the card's literal exponent band.  It defines the dyadic
indices whose powers of two lie between

```text
(log U)^(10999/10000)  and  2 * (log U)^(11/10)
```

and proves, with no premise,

```text
#slices / log log U -> 1 / (10000 * log 2).
```

The proof retains both endpoint roundings and proves their combined normalized error vanishes; it
does not replace the stated `1.1 - 10^-4` range by a wider surrogate.

Direct source check and targeted leaf build pass (`8974/8974`).  The public theorem audits with
only `[propext, Classical.choice, Quot.sound]`; the leaf is umbrella-wired without an umbrella
build.

Card remains Stage 2.  Exact slice multiplicity and its leading constant are closed.  Remaining
shared core is genuine signed spectral saving at paper ranges, Lemma 3.5(ii), amplification, and
Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — exact terminal Schur-row receiver

`Sieve/KloostermanTerminalOrbitEnergy.lean` now strengthens the full distinct-modulus terminal
Gram estimate from a global pairwise Cauchy product to an exact symmetric Schur-row bound.  For
arbitrary finite modulus set `Q`, complex weights `w`, finite source set `B`, and coefficients `b`,
Lean proves with no premise

```text
‖terminalGram(M,Q,w,B,b)‖
  <= sum_{q in Q} ‖w_q‖^2 * sum_{r in Q} terminalSchurKernel(M,B,b,q,r).
```

The diagonal kernel is exactly zero.  Every off-diagonal row retains its own square-root
source-residue/orbit budget, so each squared modulus weight is charged only to its own terminal
kernel row.  No spectral cancellation, support injectivity, modulus-size condition, or analytic
hypothesis is introduced.

`Sieve/KloostermanSourceResidueMultiplicity.lean` inserts the literal interval multiplicity bound
for `B = Finset.Icc 1 N` before applying this Schur test, producing a second no-premise theorem with
fully explicit interval rows.

Direct checks pass.  Targeted leaf builds pass (`13497/13497` and `13498/13498`).  The four newly
exposed public theorems audit with only `[propext, Classical.choice, Quot.sound]`; both leaves were
already umbrella-wired, and no umbrella build was run.

Card remains Stage 2.  Exact absolute Schur-row control is closed, but it does not supply the
collective signed spectral/Kuznetsov saving required by Lemma 3.5(ii), amplification, and Theorem
1.2; none is assumed.

## Lean progress update (2026-09-02) — exact shared-gcd frequency multiplicity

`Sieve/KloostermanProductFrequencyGcdBound.lean` closes the remaining noncoprime arithmetic
classification behind the product-period reciprocal-chord carrier.  Equality of two cross
frequencies forces their first canonical unit representatives to agree modulo `q / gcd(q,r)`.
The quotient by this reduced modulus labels at most `gcd(q,r)` possibilities, and frequency is
injective on each fixed label.  Lean therefore proves the unconditional fibre bound

```text
#{(x,y) : q*val(y)-r*val(x) = z mod q*r} <= gcd(q,r).
```

Fibrewise summation over nonzero product frequencies gives the corresponding global bound

```text
sum_x sum_y 2 / ||1-crossPhase(q,r,x,y)||
  <= gcd(q,r) * q*r * (1+log(q*r)).
```

The module propagates this exact multiplicity through terminal and stored correlations, weighted
distinct-modulus Gram entries, full source quadratics, and erased off-diagonal quadratics.  The
final quadratic theorems have no premises; no support, modulus-size, coprimality, or analytic
cancellation hypothesis is added.

Direct source check passes.  Targeted leaf build passes (`13494/13494`).  Eight principal new
theorems audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired and no
umbrella build was run.

Card remains Stage 2.  Noncoprime frequency multiplicity is now classified by the shared gcd, but
the proof still takes absolute values frequency by frequency.  Remaining shared core is genuine
collective signed spectral/Kuznetsov saving at paper ranges, Lemma 3.5(ii), amplification, and
Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — exact lcm-period terminal Parseval energy

`Sieve/KloostermanTerminalOrbitParseval.lean` replaces the pointwise reciprocal-chord estimate by
exact finite Fourier orthogonality on the true cross-phase period `lcm(q,r)`.  Each exact-period
frequency fibre has cardinality at most `gcd(q,r)`, while Parseval contributes exactly
`lcm(q,r) * (M % lcm(q,r))`.  Using `gcd(q,r) * lcm(q,r) = q*r`, Lean proves

```text
sum_x sum_y ‖kloostermanTerminalOrbit(M,q,r,x,y)‖²
  <= q*r*(M % lcm(q,r)).
```

This removes both the harmonic logarithm and the shared-gcd overcount from squared terminal-orbit
energy.  The module propagates the exact budget through source residues, arbitrary signed modulus
weights, full distinct-modulus Gram quadratics, and the literal source interval `Finset.Icc 1 N`.
No support, coprimality, modulus-size, or analytic cancellation axiom is introduced.

Direct source check passes.  Targeted leaf build passes (`13500/13500`).  Nine public theorems
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without an
umbrella build.

Card remains Stage 2.  Exact finite phase cancellation is closed, but Parseval within each fixed
modulus pair is not the collective signed modulus-average Kuznetsov saving required by Lemma
3.5(ii), amplification, and Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — row-by-row lcm-Parseval receiver

`Sieve/KloostermanTerminalOrbitParsevalSchur.lean` composes brick 136's exact lcm-period orbit
energy with a symmetric Schur test.  For the explicit kernel

```text
K(q,r) = sqrt(SourceEnergy(q) * SourceEnergy(r)
                    * (q+1)*(r+1)*(M % lcm(q+1,r+1)))
```

with diagonal set to zero, Lean proves

```text
‖terminalGram(M,Q,w,B,b)‖
  <= sum_{q in Q} ‖w_q‖² * sum_{r in Q} K(q,r).
```

Thus each squared signed modulus weight is charged only against its own exact lcm-Parseval row;
the global modulus-pair Cauchy product from brick 136 disappears.  A second capstone inserts the
literal `Finset.Icc 1 N` source-residue multiplicity in every row.  No support, coprimality,
modulus-size, or spectral premise is added.

Direct source check and targeted leaf build pass (`13501/13501`).  All three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Exact absolute Schur aggregation is closed, but it still takes norms before
the modulus average and therefore does not supply Kuznetsov cancellation, Lemma 3.5(ii),
amplification, or Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — lossless global-period frequency carrier

`Sieve/KloostermanGlobalPeriodFrequency.lean` introduces one positive common period

```text
P(Q) = lcm_{q in Q} (q+1)
```

for the complete stored modulus family.  Each off-diagonal tuple `(q,r,x,y)` embeds into an
explicit frequency in `ZMod P(Q)` whose standard additive character is exactly its original cross
phase.  Lean proves this frequency is nonzero and that the pairwise `lcm(q+1,r+1)` terminal orbit
is exactly the orbit at the embedded global frequency with length `M % P(Q)`.

This is a lossless reindexing, not a majorant: all signed modulus and source-Fourier coefficients
can now be grouped in one cyclic frequency space before any norm is taken.  No support, range,
coprimality, or spectral premise is introduced.

The carrier is the least common multiple, not the larger raw product.  Lean also proves that the
standard additive character is injective and hence two stored tuples collide in `ZMod P(Q)` if
and only if their original complex cross-phase ratios agree.

Direct source check and targeted leaf build pass (`13502/13502`).  Nine public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Common-period embedding exposes the collective signed carrier but does not
bound its frequency-collision energy.  That global energy estimate, Lemma 3.5(ii), amplification,
and Theorem 1.2 remain open; none is assumed.

## Lean progress update (2026-09-02) — signed global-frequency Parseval receiver

`Sieve/KloostermanGlobalFrequencyParseval.lean` groups the full terminal Gram quadratic in the
common cyclic space from brick 138.  If `A_z` denotes the signed sum of every modulus-pair and
source-Fourier coefficient landing at global frequency `z`, and `O_z` its terminal orbit, Lean
proves the exact identity

```text
terminalGram(M,Q,w,B,b) = sum_z A_z * O_z,
A_0 = 0.
```

Finite Cauchy--Schwarz and exact additive-character Parseval then give

```text
‖terminalGram(M,Q,w,B,b)‖²
  <= (sum_z ‖A_z‖²) * P(Q) * (M % P(Q)),
P(Q) = lcm_{q in Q} (q+1).
```

All signed modulus and source coefficients sharing a frequency are summed inside `A_z` before its
norm is taken.  This is therefore the first collective receiver in the chain that preserves
cross-modulus cancellation; no collision estimate or spectral hypothesis is smuggled into it.

Direct source check and targeted leaf build pass (`13503/13503`).  Four public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Remaining analytic primitive is now sharply the paper-scale bound for the
signed collision energy `sum_z ‖A_z‖²`.  That Kuznetsov input, Lemma 3.5(ii), amplification, and
Theorem 1.2 remain open; none is assumed.

## Lean progress update (2026-09-02) — exact collision time-frequency Parseval

`Sieve/KloostermanGlobalCollisionParseval.lean` Fourier-transforms the signed global coefficients
`A_z` over the minimal period `P(Q)`.  Lean expands the transform into the literal erased-diagonal
modulus/unit/source sum, with additive phase
`stdAddChar (-(globalFrequency(q,r,x,y) * k))`; no fibre coefficient remains hidden.  Exact finite
Parseval gives

```text
sum_k ‖timeTransform_k‖² = P(Q) * sum_z ‖A_z‖²,
sum_z ‖A_z‖² = P(Q)⁻¹ * sum_k ‖timeTransform_k‖².
```

Thus the unresolved collision estimate is now equivalently one concrete time-domain Kloosterman
second moment.  Both equalities and the explicit expansion are unconditional.

Direct source check and targeted leaf build pass (`13504/13504`).  All three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  The exact receiver is closed, but the paper-scale bound for this time-domain
second moment, Lemma 3.5(ii), amplification, and Theorem 1.2 remain open; none is assumed.

## Lean progress update (2026-09-02) — complete-transform Gram and fourth-moment normal form

`Sieve/KloostermanGlobalCollisionGram.lean` splits the global additive phase into its two
single-modulus factors and defines the corresponding source response `R_q(k)`.  Lean identifies
this response exactly with the corpus-owned complete Kloosterman transform of the source compressed
by residue class.  Hence every collision time slice is the erased-diagonal Hermitian Gram form

```text
timeTransform_k = sum_{q != r} star(w_q R_q(k)) * (w_r R_r(k))
                = (‖sum_q w_q R_q(k)‖² - sum_q ‖w_q R_q(k)‖² : R).
```

Combining this with brick 140 gives the exact fourth-moment normal form

```text
E_global = P(Q)⁻¹ * sum_k
  (‖sum_q w_q R_q(k)‖² - sum_q ‖w_q R_q(k)‖²)².
```

Period lifting is also closed without loss: for every stored `q`, the local transform energy is
repeated exactly `P(Q)/(q+1)` times, and the normalized global average is at most
`(q+1)` times exact source residue energy.  Thus the LCM carrier cancels completely from each
single-modulus `L²` cost.

Direct source check and targeted leaf build pass (`13505/13505`).  All thirteen newly exposed or
created theorem declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is
umbrella-wired without umbrella build.

Card remains Stage 2.  Period bookkeeping, phase factorization, local complete-transform control,
and diagonal subtraction are closed.  Remaining analytic primitive is now precisely a
cross-modulus fourth-moment bound for the displayed mass defect, followed by Lemma 3.5(ii),
amplification, and Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — exact elementary collision-energy envelope

`Sieve/KloostermanGlobalCollisionElementary.lean` closes the unconditional baseline estimate for
brick 141's cross-modulus fourth-moment normal form.  A single complete response obeys the
pointwise consequence of the sharp transform `L²` theorem

```text
normSq(R_q(k)) <= (q+1)^2 * SourceEnergy(q).
```

Charging one factor pointwise and the other by its normalized global-period `L²` receiver gives,
for every ordered modulus pair,

```text
P(Q)^(-1) * sum_k normSq(R_q(k)) * normSq(R_r(k))
  <= (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r).
```

Lean also proves exactly that the erased diagonal contains `#Q * (#Q - 1)` ordered pairs.
Finite Cauchy--Schwarz therefore yields the fully explicit no-premise capstone

```text
E_global
  <= #Q * (#Q - 1) *
       sum_(q != r) normSq(w_q) * normSq(w_r) *
         (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r).
```

No modulus-size, support, coprimality, or analytic hypothesis occurs.  Direct source check and
targeted leaf build pass (`13506/13506`).  All four public declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2.  Elementary fourth-moment control is now closed at its exact finite
Cauchy cost.  What remains is a genuine collective Kuznetsov saving over this baseline, followed
by Lemma 3.5(ii), amplification, and Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — weight-separated global collision receiver

`Sieve/KloostermanGlobalCollisionWeighted.lean` applies dependent-pair Cauchy--Schwarz before
global-period averaging, separating signed modulus weights from response products exactly.
Pointwise, Lean proves

```text
normSq(timeTransform_k)
  <= WeightPairEnergy(Q,w) *
       sum_(q != r) normSq(R_q(k)) * normSq(R_r(k)),
```

where

```text
WeightPairEnergy(Q,w) = sum_(q != r) normSq(w_q) * normSq(w_r).
```

Using brick 142's ordered response-pair average then gives

```text
E_global
  <= WeightPairEnergy(Q,w) *
       sum_(q != r) (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r).
```

A second capstone inserts brick 143's exact literal-interval residue multiplicities on both source
legs.  This is an alternative exact receiver to the raw ordered-pair-cardinality estimate; it
preserves the amplifier weight normalization as a separate global factor.

Direct source check and targeted leaf build pass (`13508/13508`).  All three public declarations
audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella
build.

Card remains Stage 2.  Weight normalization is now preserved through the full elementary
fourth-moment bound.  Collective signed Kuznetsov saving, Lemma 3.5(ii), amplification, and
Theorem 1.2 remain open and unassumed.

## Lean progress update (2026-09-02) — bidirectional minimum collision receiver

`Sieve/KloostermanGlobalCollisionSymmetric.lean` strengthens brick 144 pair by pair.  The mixed
response average can charge either modulus pointwise, so Lean proves the minimum of both exact
orientations:

```text
Avg_k[normSq(R_q(k)) * normSq(R_r(k))]
  <= min(
       (q+1)^2 * (r+1) * SourceEnergy(q) * SourceEnergy(r),
       (r+1)^2 * (q+1) * SourceEnergy(r) * SourceEnergy(q)).
```

An intermediate theorem also exposes the exact structural receiver before either estimate:

```text
E_global
  <= WeightPairEnergy(Q,w) *
       sum_(q != r) Avg_k[normSq(R_q(k)) * normSq(R_r(k))].
```

Combining them gives a symmetric weight-separated capstone with the better orientation retained
for every ordered pair.  A literal `Finset.Icc 1 N` version propagates both exact residue
multiplicities through the minimum rather than selecting or weakening one branch.

Direct source check and targeted leaf build pass (`13509/13509`).  All five new public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Best elementary one-pointwise/one-average control is now symmetric and
literal-source exact.  The remaining gain must be genuinely collective across moduli, followed by
Lemma 3.5(ii), amplification, and Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — literal-interval elementary collision envelope

`Sieve/KloostermanGlobalCollisionInterval.lean` specializes brick 142 to the card's exact
positive source interval `Finset.Icc 1 N`.  Cancelling the common positive modulus factor from
the existing residue-energy theorem first exposes the raw bound

```text
sum_z normSq(sourceResidue_q([1,N],b,z))
  <= residueMultiplicity(q,N) * sum_(1 <= n <= N) normSq(b_n).
```

Both source legs are then substituted into the global collision theorem.  The capstone retains
the exact ordered-pair cost, weights, modulus powers, sharp occupancies
`if N=0 then 0 else (N-1)/(q+1)+1`, and two literal copies of source coefficient energy:

```text
E_global([1,N])
  <= #Q * (#Q - 1) *
       sum_(q != r) normSq(w_q) * normSq(w_r) * (q+1)^2 * (r+1)
         * residueMultiplicity(q,N) * SourceL2([1,N])
         * residueMultiplicity(r,N) * SourceL2([1,N]).
```

No injectivity, support, coprimality, modulus-size, or analytic hypothesis is used.  Direct source
check and targeted leaf build pass (`13507/13507`).  Both public declarations audit with only
`[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired without umbrella build.

Card remains Stage 2.  Literal-source elementary collision bookkeeping is closed in full.  The
remaining improvement is collective Kuznetsov cancellation beyond this exact baseline, followed
by Lemma 3.5(ii), amplification, and Theorem 1.2; none is assumed.

## Lean progress update (2026-09-02) — exact amplifier-weight diagonal deficit

`Sieve/KloostermanGlobalCollisionWeightIdentity.lean` identifies brick 145's separated weight
factor without a cardinal or normalization relaxation:

```text
WeightPairEnergy(Q,w)
  = (sum_(q in Q) normSq(w_q))^2
      - sum_(q in Q) normSq(w_q)^2.
```

The symmetric global collision theorem and its literal `Finset.Icc 1 N` form are both rewritten
through this equality.  Thus the complete amplifier weight mass and its exact diagonal fourth
moment remain visible in the final elementary receiver; no hypothesis on weights is introduced.

Direct source check and targeted leaf build pass (`13510/13510`).  All three public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Weight normalization bookkeeping is now exact through the literal-source
collision fourth moment.  Collective cross-modulus Kuznetsov saving, Lemma 3.5(ii), amplification,
and Theorem 1.2 remain open and unassumed.

## Lean progress update (2026-09-02) — pair-local Minkowski collision receiver

`Sieve/KloostermanGlobalCollisionMinkowski.lean` applies finite `ell^2` Minkowski to the exact
erased-diagonal response Gram before modulus-pair Cauchy--Schwarz.  Lean proves

```text
E_global
  <= (sum_(q != r) |w_q| * |w_r| * sqrt(Avg_k[|R_q(k)|^2 |R_r(k)|^2]))^2.
```

Inserting brick 145's symmetric pair estimate gives the same expression with
`sqrt(PairElementaryBudget(q,r))`.  A separate theorem proves this new budget is at most

```text
WeightPairEnergy(Q,w) * sum_(q != r) PairElementaryBudget(q,r),
```

so it is a certified strengthening of the prior global pairwise-Cauchy receiver, not an
alternative with an incomparable loss.  Literal interval residue multiplicities are also
inserted inside every pair-local square root.

Direct source check and targeted leaf build pass (`13513/13513`).  All five public theorem
declarations audit with only `[propext, Classical.choice, Quot.sound]`; leaf is umbrella-wired
without umbrella build.

Card remains Stage 2.  Elementary pair aggregation is now closed at the sharper Minkowski scale.
Collective signed Kuznetsov cancellation, Lemma 3.5(ii), amplification, and Theorem 1.2 remain
open and unassumed.
