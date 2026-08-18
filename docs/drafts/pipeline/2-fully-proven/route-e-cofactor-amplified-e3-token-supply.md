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
